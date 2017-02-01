syn exp : * where
| lam : (exp -> exp) -> exp
| app : exp -> exp -> exp

def foo : 0 , x:exp -> exp, y : (exp , exp) -> exp |- x = * (*) need to put something better here
(*) hello