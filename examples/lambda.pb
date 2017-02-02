syn exp : * where
| lam : (exp ->> exp) ->> exp
| app : exp ->> exp ->> exp

def foo : (0 , x:exp ->> exp, y : (exp , exp) |- exp) = 0, x, y :> x ' y
(*) Mean comment at the end of the file
