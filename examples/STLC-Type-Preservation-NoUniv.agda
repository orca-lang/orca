module STLC-Type-Preservation-NoUniv where
open import Data.Nat

data var : Set where
  top : var
  pop : var -> var

data tm : Set where
  ▹     : var -> tm
  ƛ     : tm -> tm
  _·_   : tm -> tm -> tm
  true  : tm
  false : tm

data tp : Set where
  arr  : tp -> tp -> tp
  bool : tp

infix 15 _,_

data ctx : Set where
  ⊡ : ctx
  _,_ : ctx -> tp -> ctx

infix 30 _∋_∶_ _⊢_∶_ _⊢r_∶_ _⟪_⇧_

data _∋_∶_ : ctx -> var -> tp -> Set where
  top : ∀ {Γ T} -> (Γ , T) ∋ top ∶ T
  pop : ∀ {Γ T x S} -> Γ ∋ x ∶ T -> (Γ , S) ∋  pop x ∶ T

data _⊢_∶_ (Γ : ctx) : tm -> tp -> Set where
  t-true : Γ ⊢ true ∶ bool
  t-false : Γ ⊢ false ∶ bool
  t-app : ∀ {M N T S} -> Γ ⊢ M ∶ arr S T -> Γ ⊢ N ∶ S -> Γ ⊢ M · N ∶ T
  t-lam : ∀ {M T S} -> (Γ , S) ⊢ M ∶ T -> Γ ⊢ ƛ M ∶ arr S T
  t-var : ∀ {x T} -> Γ ∋ x ∶ T -> Γ ⊢ ▹ x ∶ T

data _⟪_⇧_ : ctx → ℕ → ctx → Set where
  take-z : ∀ {Γ} → Γ ⟪ 0 ⇧ Γ
  take-s : ∀ {Γ n Γ' P} → Γ ⟪ n ⇧ Γ' → (Γ , P) ⟪ (suc n) ⇧ Γ'

shiftVar : var -> ℕ -> var
shiftVar x zero = x
shiftVar x (suc n) = pop (shiftVar x n)

data ren : Set where
  ↑  : (n : ℕ) -> ren
  _,_ : ren -> (y : var) -> ren

rshift : ren -> ren
rshift (↑ n) = ↑ (suc n)
rshift (π , y) = rshift π , pop y

[_]rv : ren -> var -> var
[ ↑ n ]rv x = shiftVar x n
[ π , y ]rv top = y
[ π , y ]rv (pop x) = [ π ]rv x

[_]r : ren -> tm -> tm
[ π ]r (▹ x) = ▹ ([ π ]rv x)
[ π ]r (ƛ e) = ƛ ([ rshift π , top ]r e)
[ π ]r (e · e₁) = [ π ]r e · [ π ]r e₁
[ π ]r true = true
[ π ]r false = false

_⊢r_∶_ : ctx -> ren -> ctx -> Set
Δ ⊢r π ∶ Γ = ∀ {x T} -> Γ ∋ x ∶ T -> Δ ∋ [ π ]rv x ∶ T

data sub : Set where
  ↑ : ℕ -> sub
  _,_ : sub -> tm -> sub

shift : sub -> sub
shift (↑ n) = ↑ (suc n)
shift (σ , e) =  shift σ , [ ↑ 1 ]r e

[_]v  : sub -> var -> tm
[ ↑ n ]v x = ▹ (shiftVar x n)
[ σ , x ]v top = x
[ σ , x ]v (pop x₁) = [ σ ]v x₁

[_] : sub -> tm -> tm
[ σ ] (▹ x) = [ σ ]v x
[ σ ] (ƛ e) = ƛ ([ shift σ , ▹ top ] e)
[ σ ] (e · e₁) = [ σ ] e · [ σ ] e₁
[ σ ] true = true
[ σ ] false = false

_⊢s_∶_ : ctx -> sub -> ctx -> Set
Δ ⊢s σ ∶ Γ = ∀ {x T} -> Γ ∋ x ∶ T -> Δ ⊢ [ σ ]v x ∶ T

infixr 4 _↪_
data _↪_ : tm -> tm -> Set where
 s-app-1 : ∀ {M M' N} -> M ↪ M' -> M · N ↪ M' · N
 s-app-2 : ∀ {M N} -> ƛ M · N ↪ [ ↑ 0 , N ] M

wkn-ren-lemma : ∀ {Δ S T} π x -> Δ ∋ [ π ]rv x ∶ T -> (Δ , S) ∋ [ rshift π ]rv x ∶ T
wkn-ren-lemma (↑ n) x x₁ = pop x₁
wkn-ren-lemma (d , y) top x₁ = pop x₁
wkn-ren-lemma (d , y) (pop x) x₁ = wkn-ren-lemma d x x₁

ext-ren-typ : ∀ {Δ Γ S} π -> Δ ⊢r π ∶ Γ -> (Δ , S) ⊢r rshift π , top ∶ (Γ , S)
ext-ren-typ π D top = top
ext-ren-typ π D (pop x₁) = wkn-ren-lemma π _ (D x₁)

ren-lemma : ∀ {Γ Δ T M} π -> Δ ⊢r π ∶ Γ  -> Γ ⊢ M ∶ T -> Δ ⊢ [ π ]r M ∶ T
ren-lemma π D t-true = t-true
ren-lemma π D t-false = t-false
ren-lemma π D (t-app e e₁) = t-app (ren-lemma π D e) (ren-lemma π D e₁)
ren-lemma π D (t-lam e) = t-lam (ren-lemma (rshift π , top) (ext-ren-typ π D) e)
ren-lemma π D (t-var x₁) = t-var (D x₁)

wkn-lemma : ∀ {Δ S T} σ x -> Δ ⊢ [ σ ]v x ∶ T -> (Δ , S) ⊢ [ shift σ ]v x ∶ T
wkn-lemma (↑ n) x (t-var x₁) = t-var (pop x₁)
wkn-lemma (σ , e) top d = ren-lemma (↑ 1) pop d
wkn-lemma (σ , e) (pop x) d = wkn-lemma σ x d

ext-sub-typ : ∀ {Δ Γ S} σ -> Δ ⊢s σ ∶ Γ -> (Δ , S) ⊢s shift σ , ▹ top ∶ (Γ , S)
ext-sub-typ σ D top = t-var top
ext-sub-typ σ D (pop E) = wkn-lemma σ _ (D E)

subst-lemma :  ∀ {Γ Δ T M} σ -> Δ ⊢s σ ∶ Γ  -> Γ ⊢ M ∶ T -> Δ ⊢ [ σ ] M ∶ T
subst-lemma σ D t-true = t-true
subst-lemma σ D t-false = t-false
subst-lemma σ D (t-app e e₁) = t-app (subst-lemma σ D e) (subst-lemma σ D e₁)
subst-lemma σ D (t-lam e) = t-lam (subst-lemma (shift σ , ▹ top) (ext-sub-typ σ D) e)
subst-lemma σ D (t-var x) = D x

subst-wkn-id : ∀ {Γ N S} -> Γ ⊢ N ∶ S -> Γ ⊢s ↑ 0 , N ∶ (Γ , S)
subst-wkn-id d top = d
subst-wkn-id d (pop x₁) = t-var x₁

pres : ∀ {Γ} M N T -> Γ ⊢ M ∶ T -> M ↪ N -> Γ ⊢ N ∶ T
pres (M · N) .(_ · _) t d1 (s-app-1 d2) = {!!}
pres (ƛ M · N) ._ t d1 s-app-2 = {!!}
-- pres (app M N) (app M' .N) (t-app d d₁) (s-app-1 e) = t-app (pres d e) d₁
-- pres (t-app (t-lam d) d₁) s-app-2 = subst-lemma (↑ 0 , _) (subst-wkn-id d₁) d
