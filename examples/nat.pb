data nat where
| zero: nat
| suc: nat -> nat

data big_nat : set_0 where
| big_zero : big_nat
| big_suc : big_nat -> big_nat

data fin : nat -> * where
| fZ : fin zero
| fS : (n : nat) -> fin n -> fin (suc n)

def Z : nat = zero
def 1 : nat = suc Z

def big_1 : big_nat = big_suc big_zero

data list (A : set) : * where
| nil: (A : set) -> list A
| cons: (A : set) -> A -> list A -> list A

data big_list (A : set) : * where
| big_nil: (A : set) -> big_list A
| big_cons: (A : set) -> A -> big_list A -> big_list A

def big_empty_nat_list : big_list big_nat = big_nil big_nat
def big_unary_nat_list : big_list big_nat = big_cons big_nat big_1 (big_nil big_nat)
