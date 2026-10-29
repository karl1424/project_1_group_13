pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, ExprKind, Op, Range};
use slang_ui::prelude::{
    slang::{
        ast::{Case, Name, PrefixOp, Type},
        Span,
    },
    *,
};

pub struct App;

#[derive(Debug, Clone)]
struct Obligation {
    condition: Expr,
    span: Span,
    message: String,
}

impl Obligation {
    fn transform(self, f: impl Fn(&Expr) -> Expr) -> Obligation {
        Obligation {
            condition: f(&self.condition),
            ..self
        }
    }
}

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // get reference to z3 solver
        let mut solver = cx.solver()?;

        // iterate all methods
        for m in file.methods() {
            // convert all the preconditions into smt
            let pres: Vec<smtlib::Bool<'_>> = m
                .requires()
                .map(|pre| Ok(pre.smt(cx.smt_st())?.as_bool()?))
                .collect::<Result<_>>()?;

            let ensures: Vec<IVLCmd> = m
                .ensures()
                .map(|p| {
                    let q = match &m.return_ty {
                        Some(ty) => p.subst_result(&Expr::ident(&"result".to_string(), ty)),
                        None => p.clone(),
                    };
                    IVLCmd::assert(&q.with_span(p.span), "Postcondition might not hold")
                })
                .collect();

            // get method body, convert to IVL
            let cmd = &m.body.clone().unwrap().cmd;
            let body = cmd_to_ivlcmd(cmd)?;
            let ivl = body.seq(&IVLCmd::seqs(&ensures));

            let mut n = 0;

            // put all obligations into a list of oblications with span for error localication
            let obligations: Vec<_> = swp(&ivl, &vec![], &mut n)?
                .into_iter()
                .map(|o| Ok((o.condition.smt(cx.smt_st())?.as_bool()?, o.span, o.message)))
                .collect::<Result<_>>()?;

            // open a solver scope for this method
            solver.scope(|solver| {
                // assert all preconditions once per method
                for pre in pres {
                    solver.assert(pre)?;
                }

                for (soblig, span, msg) in obligations {
                    // open a solver scope for this obligation
                    solver.scope(|solver| {
                        // assert the negation of theobligation
                        solver.assert(!soblig)?;
                        // check sat of !obligation
                        match solver.check_sat()? {
                            smtlib::SatResult::Sat => {
                                cx.error(span, msg.to_string());
                            }
                            smtlib::SatResult::Unknown => {
                                cx.warning(span, format!("{msg}: unknown sat result"));
                            }
                            smtlib::SatResult::Unsat => (),
                        }

                        Ok(())
                    })?;
                }

                Ok(())
            })?;
        }

        Ok(())
    }
}

/// Encode a Cmd into IVL
fn cmd_to_ivlcmd(cmd: &Cmd) -> Result<IVLCmd> {
    match &cmd.kind {
        CmdKind::Assert { condition, message } => {
            Ok(guarded(condition, IVLCmd::assert(condition, message)))
        }
        CmdKind::Assume { condition } => Ok(guarded(condition, IVLCmd::assume(condition))),
        CmdKind::Assignment { name, expr } => Ok(guarded(expr, IVLCmd::assign(name, expr))),
        CmdKind::Seq(c1, c2) => Ok(IVLCmd::seq(&cmd_to_ivlcmd(c1)?, &cmd_to_ivlcmd(c2)?)),
        CmdKind::VarDefinition { name, ty, expr, .. } => match expr {
            Some(e) => Ok(guarded(e, IVLCmd::assign(name, e))),
            None => Ok(IVLCmd::havoc(name, ty)),
        },
        CmdKind::Match { body } => {
            let branches: Vec<IVLCmd> = body
                .cases
                .iter()
                .map(|case| {
                    Ok(IVLCmd::seq(
                        &IVLCmd::assume(&case.condition),
                        &cmd_to_ivlcmd(&case.cmd)?,
                    ))
                })
                .collect::<Result<_>>()?;

            let any = body
                .cases
                .iter()
                .map(|case| case.condition.clone())
                .reduce(|a, b| a.or(&b))
                .unwrap_or(Expr::bool(false));

            let checks: Vec<IVLCmd> = body
                .cases
                .iter()
                .flat_map(|c| div_checks(&c.condition))
                .collect();

            let assertion = IVLCmd::assert(&any, "No match case applies");

            Ok(IVLCmd::seqs(&checks)
                .seq(&assertion)
                .seq(&IVLCmd::nondets(&branches)))
        }
        CmdKind::Return { expr } => {
            if let Some(expr) = expr {
                return Ok(IVLCmd::assign(&Name::ident("result".to_string()), expr));
            }
            Ok(IVLCmd::nop())
        }
        CmdKind::Loop {
            invariants,
            variant: _,
            body,
        } => {
            let assert_inv = IVLCmd::seqs(
                &invariants
                    .iter()
                    .map(|i| {
                        guarded(
                            i,
                            IVLCmd::assert(i, "Loop invariant might not hold on entry"),
                        )
                    })
                    .collect::<Vec<_>>(),
            );

            let havoc_cmd = IVLCmd::seqs(
                &body
                    .cases
                    .iter()
                    .flat_map(|case| collect_assigned_vars(&case.cmd))
                    .map(|(name, ty)| IVLCmd::havoc(&name, &ty))
                    .collect::<Vec<_>>(),
            );

            let assume_inv =
                IVLCmd::seqs(&invariants.iter().map(IVLCmd::assume).collect::<Vec<_>>());

            let branches: Vec<IVLCmd> = body
                .cases
                .iter()
                .map(|case| Ok(IVLCmd::assume(&case.condition).seq(&cmd_to_ivlcmd(&case.cmd)?)))
                .collect::<Result<_>>()?;

            let guard_checks = IVLCmd::seqs(
                &body
                    .cases
                    .iter()
                    .flat_map(|c| div_checks(&c.condition))
                    .collect::<Vec<_>>(),
            );

            let loop_body = IVLCmd::nondets(&branches);

            let body_branch = loop_body
                .seq(&IVLCmd::seqs(
                    &invariants
                        .iter()
                        .map(|i| {
                            guarded(
                                i,
                                IVLCmd::assert(i, "Loop invariant might not be preserved"),
                            )
                        })
                        .collect::<Vec<_>>(),
                ))
                .seq(&IVLCmd::assume(&Expr::bool(false)));

            let b = body
                .cases
                .iter()
                .map(|c| c.condition.clone())
                .reduce(|a, b| a.or(&b))
                .unwrap_or(Expr::bool(false));

            let exit_branch = IVLCmd::assume(&b.prefix(PrefixOp::Not));

            Ok(assert_inv
                .seq(&havoc_cmd)
                .seq(&assume_inv)
                .seq(&guard_checks)
                .seq(&body_branch.nondet(&exit_branch)))
        }
        CmdKind::For {
            name,
            range,
            invariants,
            variant,
            body,
        } => {
            let Range::FromTo(from, to) = range;
            const MAX_UNROLL: i64 = 64;
            if invariants.is_empty() {
                if let (ExprKind::Num(a), ExprKind::Num(b)) = (&from.kind, &to.kind) {
                    if *b - *a <= MAX_UNROLL {
                        let mut cmds = vec![];
                        for k in *a..*b {
                            cmds.push(IVLCmd::assign(name, &Expr::num(k)));
                            cmds.push(cmd_to_ivlcmd(&body.cmd)?);
                        }
                        let last = if *a <= *b { *b } else { *a };
                        cmds.push(IVLCmd::assign(name, &Expr::num(last)));
                        return Ok(IVLCmd::seqs(&cmds));
                    }
                }
            }
            let init = guarded(from, IVLCmd::assign(name, from));
            let increment = Cmd::assign(
                name,
                &Expr::ident(&name.ident, &Type::Int).add(&Expr::num(1)),
            );
            let case = Case {
                condition: Expr::ident(&name.ident, &Type::Int).lt(&to),
                cmd: Cmd::seq(&body.cmd, &increment),
            };
            let loop_cmd = Cmd::_loop(invariants, variant.clone(), &[case]);
            Ok(init.seq(&cmd_to_ivlcmd(&loop_cmd)?))
        }
        c => bail!("not yet implemented: cmd_to_ivlcmd {c:?}"),
    }
}

/// Compute the weakest precondition set of IVL program
fn swp(ivl: &IVLCmd, post: &Vec<Obligation>, n: &mut usize) -> Result<Vec<Obligation>> {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => {
            let mut out: Vec<Obligation> = post
                .into_iter()
                .map(|o| o.clone().transform(|e| condition.clone().imp(e)))
                .collect();
            out.push(Obligation {
                condition: condition.clone(),
                span: condition.span,
                message: message.clone(),
            });
            Ok(out)
        }
        IVLCmdKind::Assume { condition } => Ok(post
            .into_iter()
            .map(|o| o.clone().transform(|e| condition.clone().imp(e)))
            .collect()),
        IVLCmdKind::Assignment { name, expr } => Ok(post
            .into_iter()
            .map(|o| o.clone().transform(|e| e.subst_ident(&name.ident, expr)))
            .collect()),
        IVLCmdKind::Havoc { name, ty } => {
            let fresh = Expr::ident(&format!("{}_havoc_{}", name, *n), ty);
            *n += 1;
            Ok(post
                .into_iter()
                .map(|o| o.clone().transform(|e| e.subst_ident(&name.ident, &fresh)))
                .collect())
        }
        IVLCmdKind::Seq(c1, c2) => {
            let q = swp(c2, post, n)?;
            swp(c1, &q, n)
        }
        IVLCmdKind::NonDet(c1, c2) => {
            let mut q = swp(c1, &post.clone(), n)?;
            q.extend(swp(c2, post, n)?);
            Ok(q)
        } //c => bail!("not yet implemented: wp of {:?}", c),
    }
}

fn collect_assigned_vars(cmd: &Cmd) -> Vec<(Name, Type)> {
    match &cmd.kind {
        CmdKind::Assignment { name, expr } => {
            vec![(name.clone(), expr.ty.clone())]
        }
        CmdKind::VarDefinition {
            name,
            ty,
            expr: Some(_),
            ..
        } => {
            vec![(name.clone(), ty.clone())]
        }
        CmdKind::Seq(c1, c2) => {
            let mut v = collect_assigned_vars(c1);
            v.extend(collect_assigned_vars(c2));
            v
        }
        CmdKind::Match { body } | CmdKind::Loop { body, .. } => body
            .cases
            .iter()
            .flat_map(|c| collect_assigned_vars(&c.cmd))
            .collect(),
        _ => vec![],
    }
}

fn div_checks(e: &Expr) -> Vec<IVLCmd> {
    let mut out = vec![];
    let _ = e.pre_order_map(|x| {
        if let ExprKind::Infix(_, Op::Div | Op::Mod, d) = &x.kind {
            let cond = Expr::ne(d, &Expr::num(0)).with_span(x.span);
            out.push(IVLCmd::assert(&cond, "Possible division by zero"));
        }
        None
    });
    out.reverse();
    out
}

fn guarded(e: &Expr, cmd: IVLCmd) -> IVLCmd {
    let mut cmds = div_checks(e);
    cmds.push(cmd);
    IVLCmd::seqs(&cmds)
}
