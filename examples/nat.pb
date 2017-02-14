data nat where
| zero: nat
| suc: nat -> nat

(*
def Z : nat = zero
def 1 : nat = suc Z

data list (A : set) : * where
| nil: (A : set) -> list A
| cons: (A : set) -> A -> list A -> list A


def empty_nat_list : list nat = nil nat

def unary_nat_list : list nat = cons nat 1 (nil nat)
*)