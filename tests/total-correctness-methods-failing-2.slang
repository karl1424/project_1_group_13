method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1)/2
    decreases n
{
    var ret: Int;
    match {
        n == 0 => 
            ret := 0,
        n != 0 => 
            var res: Int;
            // @CheckError
            res := sumn(n);
            ret := res + n
    };
    return ret
}