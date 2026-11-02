method f(n: Int): Int
    ensures result == 0
{
    match {
        true => 
            n := 1;
            n := 2
    };
    return 0
}