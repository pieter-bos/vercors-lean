import .nonneg_rat

structure logic :=
  (loc : Type)
  (val : Type)
  (state : Type)
  (assn : Type)
  (conj : assn → assn → assn)
  (neg : assn → assn)
  (ex : (val → assn) → assn)
  (sat : assn → state → bool)

def heap (L : logic) := L.loc → (ℚ* × L.val)

inductive assn (L : logic)
| bool : L.assn → assn
| emp : assn
| heaplet : L.loc → ℚ* → assn
| conj : assn → assn → assn
| imp : assn → assn → assn

infixl `∧`:35 := λ(l r : assn), assn.conj l r
infixl `-*`:25 := λ(l r : assn), assn.imp l r

def assn.sat (L : logic) (h : heap L) (state : L.state) : (assn L) → bool
| (assn.bool p) := L.sat p state
| (assn.emp) := if ∀l : L.loc, (h l).fst = 0 then tt else ff