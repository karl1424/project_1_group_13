method client(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1) / 2
{
    var acc: Int := 0;
    for i in 1..(n + 1)
        invariant 1 <= i && i <= n + 1
        invariant 2 * acc == (i - 1) * i
    {
        acc := acc + i
    };
    return acc
}