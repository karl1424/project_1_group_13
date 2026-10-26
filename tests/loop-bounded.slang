method client()
{
    var acc: Int := 0;
    for i in 0..10
        invariant 0 <= i && i <= 10
        invariant 2 * acc == i * (i - 1)
    {
        acc := acc + i
    };
    assert acc == 45
}