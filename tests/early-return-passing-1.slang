method f(n: Int): Int
    ensures result == 0
{
    match {
        true => return 0
    };
    assert false
} 