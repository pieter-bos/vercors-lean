import .lovelib

namespace simplify

structure O := (n : nat)
def Q : Type := {q : ℚ // q.nonneg}

#check ℚ
#check has_inv

lemma rat.nonneg_inv {a : ℚ} : a.nonneg → a⁻¹.nonneg :=
assume ha : a.nonneg,
show a⁻¹.nonneg, from or.elim (em (a = 0)) begin 
  intro zero,
  simp [zero],
end begin 
  intro nonzero,
  apply by_contradiction,
  intro invneg,
  have neginvnonneg: (-a⁻¹).nonneg,
  apply or.resolve_left (rat.nonneg_total a⁻¹), assumption,
  have mult : (a * -a⁻¹).nonneg, apply rat.nonneg_mul ha neginvnonneg,
  simp [mul_inv_cancel nonzero] at mult,
  have asdf : 0 ≤ (-1:ℚ), exact rat.nonneg_iff_zero_le.elim_left mult,
  linarith,
end


@[instance] def Q.has_add : has_add Q :=
{add := λq q', subtype.mk (q.val + q'.val) (by exact rat.nonneg_add q.property q'.property)}
@[instance] def Q.has_div : has_div Q :=
{div := λq q', subtype.mk (q.val / q'.val) (by exact rat.nonneg_mul q.property (rat.nonneg_inv q'.property))}

inductive X
| div : X
| null : X
| ass : X
| perm : X

inductive Nullable
| o : O → Nullable
| null : Nullable

def Nullable.eq : Nullable → Nullable → bool
| (Nullable.o o) (Nullable.o o') := if o == o' then tt else ff
| (Nullable.null) (Nullable.null) := tt
| _ _ := ff

inductive V
| b : bool → V
| z : ℤ → V
| q : Q → V
| o : Nullable → V

def V.eq : V → V → bool
| (V.b b) (V.b b') := if b = b' then tt else ff
| (V.z z) (V.z z') := if z = z' then tt else ff
| (V.q q) (V.q q') := if q = q' then tt else ff
| (V.o o) (V.o o') := Nullable.eq o o'
| _ _ := false


structure Var := (n : nat)
structure F := (n : nat)
structure Fun := (n : nat)
structure P := (n : nat)

inductive T
| B : T
| Z : T
| O : T
| Q : T

def H := O × F → V
def S := Var → V
def FieldPermMask := O × F → Q
def PredPermMask := P → Q

structure Configuration :=
(h : H)
(s : S)
(fieldPerm : FieldPermMask)
(predPerm : PredPermMask)

structure Defs :=
(var : Var → T) 
(field : F → T)
(func : Fun → (list T) × T)
(pred : P → (list T))

inductive E
| null : E
| b : bool → E
| n : ℤ → E
| x : Var → E
| deref : E → F → E
| negate : E → E
| add : E → E → E
| div : E → E → E
| not : E → E
| eq : E → E → E
| apply : Fun → list E → E
| unfolding : P → list E → E → E → E
| fieldPerm : E → F → E
| predPerm : P → list E → E

inductive A
| e : E → A
| fieldAcc : E → F → E → A
| predAcc : P → list E → E → A
| imp : E → A → A
| conj : A → A → A
| all : T → (E → A) → A
| ex : T → (E → A) → A
| forperm : F → E → A

def typ (d : Defs) : E → T
| (E.null) := T.O
| (E.b b) := T.B
| (E.n z) := T.Z
| (E.x x) := d.var x
| (E.deref o f) := d.field f
| (E.negate z) := (typ z)
| (E.add z z') := (typ z)
| (E.div z z') := (typ z)
| (E.not b) := T.B
| (E.eq v v') := T.B
| (E.apply f args) := (d.func f).snd
| (E.unfolding p args q e) := typ e
| (E.fieldPerm o f) := T.Q
| (E.predPerm p args) := T.Q

def allTyped (d : Defs) : list E → list T → Prop
| [] [] := true
| [] (_ :: _) := false
| (_ :: _) [] := false
| (e :: es) (t :: ts) := (typ d e) = t ∧ allTyped es ts

lemma allTypedLen (d: Defs) (es : list E) (ts : list T) 
  (typed : allTyped d es ts) : list.length es = list.length ts :=
begin
  induction' es,
  { cases' ts, 
    { refl, }, 
    { simp [allTyped] at typed, apply false.elim typed, }, 
  },
  { cases' ts, 
    { simp [allTyped] at typed, apply false.elim typed, }, 
    { simp [allTyped] at *, apply (ih d ts), apply and.elim_right typed, },
  },
end


mutual def allWellTyped, wellTyped (d : Defs)

with allWellTyped : list E → Prop
| [] := true
| (e :: es) := (wellTyped e ∧ allWellTyped es)

with wellTyped : E → Prop
| E.null := true
| (E.b b) := true
| (E.n z) := true
| (E.x x) := true
| (E.deref o f) := (typ d o) = T.O ∧ wellTyped o
| (E.negate z) := (typ d z) = T.Z ∧ wellTyped z
| (E.add z z') := (typ d z) = (typ d z') ∧ ((typ d z) = T.Z ∨ (typ d z) = T.Q) ∧ wellTyped z ∧ wellTyped z'
| (E.div z z') := (typ d z) = (typ d z') ∧ ((typ d z) = T.Z ∨ (typ d z) = T.Q) ∧ wellTyped z ∧ wellTyped z'
| (E.not b) := (typ d b) = T.B ∧ wellTyped b
| (E.eq v v') := (typ d v) = (typ d v') ∧ wellTyped v ∧ wellTyped v'
| (E.apply f args) := allTyped d args (d.func f).fst ∧ allWellTyped args
| (E.unfolding p args q e) := allTyped d args (d.pred p) ∧ allWellTyped args ∧ wellTyped q ∧ wellTyped e
| (E.fieldPerm o f) := typ d o = T.O ∧ wellTyped o
| (E.predPerm p args) := allTyped d args (d.pred p) ∧ allWellTyped args

def E' (d : Defs) : Type :=
  {e : E // wellTyped d e}

def value_t : V → T
| (V.b _) := T.B
| (V.z _) := T.Z
| (V.q _) := T.Q
| (V.o _) := T.O

def boolOf (v : V) (h : value_t v = T.B) : bool :=
begin
  cases v,
  case b { exact v, },
  repeat { simp [value_t] at h, exact false.elim h },
end

def zahlOf (v : V) (h : value_t v = T.Z) : ℤ :=
begin
  cases v,
  case z { exact v, },
  repeat { simp [value_t] at h, exact false.elim h },
end

def permOf (v : V) (h : value_t v = T.Q) : Q :=
begin
  cases v,
  case q { exact v, },
  repeat { simp [value_t] at h, exact false.elim h },
end


def objectOf (v : V) (h : value_t v = T.O) : Nullable :=
begin
  cases v,
  case o { exact v, },
  repeat { simp [value_t] at h, exact false.elim h },
end

def configurationMatchesDefs (d : Defs) (c : Configuration) : Prop :=
  (∀v, value_t (c.s v) = (d.var v)) ∧ 
  (∀o, ∀f, value_t (c.h (o, f)) = (d.field f))

def Configuration' (d : Defs) : Type :=
  {c : Configuration // configurationMatchesDefs d c}

-- D ?
inductive Eval
| err : X → Eval
| ok : V → Eval

def evalTypConsistent (d : Defs) (e : E) (res : Eval) : Prop := match res with
| (Eval.err _) := true
| (Eval.ok v) := value_t v = (typ d e)
end

def Eval' (d : Defs) (e : E) : Type :=
  {res : Eval // evalTypConsistent d e res}


def Eval'.x {d : Defs} {e : E} (x: X) : Eval' d e :=
  subtype.mk (Eval.err x) (by simp [evalTypConsistent])

def Eval'.v {d : Defs} {e : E} (v : V) (h : evalTypConsistent d e (Eval.ok v)): Eval' d e :=
  subtype.mk (Eval.ok v) h

def eval (d : Defs) (c : Configuration' d) (e : E' d) : Eval' d e.val :=
begin
  induction e, simp,
  rename e_val val,
  rename e_property wt_val,
  induction val,

  case null {
    exact Eval'.v (V.o (Nullable.null))
      (by simp [evalTypConsistent, typ, value_t])
  },

  case b : b {
    exact Eval'.v (V.b b)
      (by simp [evalTypConsistent, typ, value_t])
  },

  case n : z {
    exact Eval'.v (V.z z)
      (by simp [evalTypConsistent, typ, value_t])
  },

  case x : v {
    exact subtype.mk (Eval.ok (c.val.s v)) begin
      simp [evalTypConsistent, typ],
      apply and.elim_left c.property,
    end
  },

  case deref : o f ih {
    simp [wellTyped] at wt_val,
    have o' : Eval' d o, exact ih (and.elim_right wt_val),
    cases o' with o' wt_o', 
    cases o',
    case err { exact Eval'.x o', },
    -- ok
    simp [evalTypConsistent, and.elim_left wt_val] at wt_o',
    have o'_val : Nullable,
    exact objectOf o' wt_o',
    cases o'_val,
    case o { 
      exact Eval'.v (c.val.h (o'_val, f)) begin
        simp [evalTypConsistent, typ],
        apply and.elim_right c.property,
      end 
    },
    case null { 
      exact Eval'.x X.null,
    },
  },

  case negate : z ih {
    simp [wellTyped] at wt_val,
    have z' : Eval' d z, exact ih (and.elim_right wt_val),
    cases z' with z' wt_z',
    cases z',
    case err { exact Eval'.x z', },
    -- ok
    simp [evalTypConsistent, and.elim_left wt_val] at wt_z',
    have z'' : ℤ, exact zahlOf z' wt_z',
    exact Eval'.v (V.z (-z'')) (by simp [evalTypConsistent, value_t, typ, and.elim_left wt_val])
  },

  -- case add : z z' ih_z ih_z' {
  --   simp [wellTyped] at wt_val,
  --   have t_eq : (typ d z) = (typ d z'), cc,
  --   have t_numeric : (typ d z) = T.Z ∨ (typ d z) = T.Q, cc,
  --   have wt_z : wellTyped d z, cc,
  --   have wt_z' : wellTyped d z', cc,
  --   have z_eval : Eval' d z, exact ih_z wt_z,
  --   have z'_eval : Eval' d z', exact ih_z' wt_z',
  --   cases z_eval with z_eval wt_z_eval,
  --   cases z_eval,
  --   case err { exact Eval'.x z_eval, },
  --   -- ok
  --   cases z'_eval with z'_eval wt_z'_eval,
  --   cases z'_eval,
  --   case err { exact Eval'.x z'_eval },
  --   cases z_eval,
  --   case z {
  --     cases z'_eval, case z {
  --       exact Eval'.v (V.z (z_eval + z'_eval)) begin
  --         simp [evalTypConsistent, value_t, typ] at *,
  --         exact wt_z_eval,
  --       end
  --     },
  --     -- z'_eval does not match the type of z_eval, contradicting t_eq
  --     repeat {
  --       simp [evalTypConsistent, value_t, typ] at *,
  --       simp [t_eq] at wt_z_eval,
  --       cc,
  --     },
  --   },
  --   case q { 
  --     cases z'_eval, case q {
  --       exact Eval'.v (V.q (z_eval + z'_eval)) begin
  --         simp [evalTypConsistent, value_t, typ] at *,
  --         exact wt_z_eval,
  --       end
  --     },
  --     -- z'_eval does not match the type of z_eval, contradicting t_eq
  --     repeat {
  --       simp [evalTypConsistent, value_t, typ] at *,
  --       simp [t_eq] at wt_z_eval,
  --       cc,
  --     },
  --   },
  --   --z_eval does not have type Z or Q, contradicting t_numeric
  --   repeat {
  --     apply false.elim,
  --     apply or.elim t_numeric _ _,
  --     intro t_z, simp [t_z, evalTypConsistent, value_t] at wt_z_eval, assumption,
  --     intro t_q, simp [t_q, evalTypConsistent, value_t] at wt_z_eval, assumption,
  --   },
  -- },

  -- case div : z z' ih_z ih_z' {
  --   simp [wellTyped] at wt_val,
  --   have t_eq : (typ d z) = (typ d z'), cc,
  --   have t_numeric : (typ d z) = T.Z ∨ (typ d z) = T.Q, cc,
  --   have wt_z : wellTyped d z, cc,
  --   have wt_z' : wellTyped d z', cc,
  --   have z_eval : Eval' d z, exact ih_z wt_z,
  --   have z'_eval : Eval' d z', exact ih_z' wt_z',
  --   cases z_eval with z_eval wt_z_eval,
  --   cases z_eval,
  --   case err { exact Eval'.x z_eval, },
  --   -- ok
  --   cases z'_eval with z'_eval wt_z'_eval,
  --   cases z'_eval,
  --   case err { exact Eval'.x z'_eval },
  --   cases z_eval,
  --   case z {
  --     cases z'_eval, case z {
  --       exact Eval'.v (V.z (z_eval / z'_eval)) begin
  --         simp [evalTypConsistent, value_t, typ] at *,
  --         exact wt_z_eval,
  --       end
  --     },
  --     -- z'_eval does not match the type of z_eval, contradicting t_eq
  --     repeat {
  --       simp [evalTypConsistent, value_t, typ] at *,
  --       simp [t_eq] at wt_z_eval,
  --       cc,
  --     },
  --   },
  --   case q { 
  --     cases z'_eval, case q {
  --       exact Eval'.v (V.q (z_eval / z'_eval)) begin
  --         simp [evalTypConsistent, value_t, typ] at *,
  --         exact wt_z_eval,
  --       end
  --     },
  --     -- z'_eval does not match the type of z_eval, contradicting t_eq
  --     repeat {
  --       simp [evalTypConsistent, value_t, typ] at *,
  --       simp [t_eq] at wt_z_eval,
  --       cc,
  --     },
  --   },
  --   -- z_eval does not have type Z or Q, contradicting t_numeric
  --   repeat {
  --     apply false.elim,
  --     apply or.elim t_numeric _ _,
  --     intro t_z, simp [t_z, evalTypConsistent, value_t] at wt_z_eval, assumption,
  --     intro t_q, simp [t_q, evalTypConsistent, value_t] at wt_z_eval, assumption,
  --   },
  -- },

  case not : b ih {
    simp [wellTyped] at wt_val,
    have b_val : Eval' d b, exact ih (and.elim_right wt_val),
    cases b_val with b_val wt_b,
    cases b_val,
    case err { exact Eval'.x b_val, },
    simp [evalTypConsistent, and.elim_left wt_val] at wt_b,
    have b' : bool, exact boolOf b_val wt_b,
    exact Eval'.v (V.b (bnot b')) (by simp [evalTypConsistent, value_t, typ])
  },

  case eq : v v' ih ih' {
    simp [wellTyped] at wt_val,
    have v_val : Eval' d v, exact ih (and.elim_left (and.elim_right wt_val)),
    have v_val' : Eval' d v', exact ih' (and.elim_right (and.elim_right wt_val)),
    cases v_val with v_val wt_v_val,
    cases v_val' with v_val' wt_v_val',
    cases v_val, case err { exact Eval'.x v_val },
    cases v_val', case err { exact Eval'.x v_val' },
    exact Eval'.v (V.b (if v_val = v_val' then tt else ff)) begin
      
    end
  },

  repeat { sorry },
end

-- def empty_def : Defs := (Defs.mk (λ_, T.B) (λ_, T.B) (λ_, ([], T.B)) (λ_, []))
-- def empty_cfg : Configuration := Configuration.mk (λ_, V.b tt) (λ_, V.b tt) (λ_, subtype.mk 0 (by simp)) (λ_, subtype.mk 0 (by simp))
-- def empty_cfg' : Configuration' empty_def := subtype.mk empty_cfg begin
--   simp [empty_cfg, empty_def, configurationMatchesDefs],
--   apply and.intro,
--   intro _, simp [value_t],
--   intros _ _, simp [value_t],
-- end

end simplify