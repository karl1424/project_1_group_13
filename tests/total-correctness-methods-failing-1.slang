method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1)/2
    decreases n - 2
{
    var ret: Int;
    match {
        n == 0 => 
            ret := 0,
        n != 0 => 
            var res: Int;
            // @CheckError
            res := sumn(n - 1);
            ret := res + n
    };
    return ret
}