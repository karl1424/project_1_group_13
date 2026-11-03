method main(M: Int, N: Int, res: Int, m: Int)
    requires N >0 && M >= 0
    ensures M == res * N + m 
{
    res := 0; m := M;

    loop
        invariant M == res * N + m
        decreases m
    {
        m >= N => m := m - N; res := res + 1
    }
}