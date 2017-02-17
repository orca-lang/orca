data nat where
| z : nat
| s : nat -> nat

def 1 : nat = s z

data eq (A : *) : A -> A -> * where
| refl: (x : A) -> eq A x x


def test_1 : eq nat z z = refl z

def test_2 : eq nat (s z) (s z) = refl (s z)

def test_3 : eq nat 1 (s z) = refl (s z) (*) The definition of one should compute to (s z)


def id : nat -> nat = fn x => x

def another_1 : nat = id 1

def test_4 : eq nat 1 (id 1) = refl 1

def id' : nat -> nat = id


def test_5 : eq nat (id 1) (id (s (id z))) = refl (id 1)