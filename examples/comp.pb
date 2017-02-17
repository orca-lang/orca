data nat where
| z : nat
| s : nat -> nat

def 1 : nat = s z

data eq (A : *) : A -> A -> * where
| refl: (x : A) -> eq A x x


def test_1 : eq nat z z = refl z

def test_2 : eq nat (s z) (s z) = refl (s z)

(*) def test_3 : eq nat 1 (s z) = refl (s z) (*) The definition of one should compute to (s z)
