domain Pair {
  function pair(x: Int, y: Int): Pair
  function fst(x: Pair): Int
  function snd(x: Pair): Int

  axiom forall x: Int :: forall y: Int :: fst(pair(x,y)) == x
  axiom forall x: Int :: forall y: Int :: snd(pair(x,y)) == y
}

method client(x: Int, y: Int)
{
  var xy: Pair := pair(2,y);
  // @CheckError
  assert fst(xy) == 3;
  assert snd(xy) == y
}