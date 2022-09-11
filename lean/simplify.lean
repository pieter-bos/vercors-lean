import .nonneg_rat
import .mask

namespace simplify

structure O := (n : nat)

instance dec_eq_o (o o' : O) [nat_dec : ∀n n' : nat, decidable (n = n')] : decidable (o = o') := begin
  induction o, induction o',
  rw O.mk.inj_eq,
  exact nat_dec o o',
end

inductive X
| div : X
| null : X
| ass : X
| perm : X

inductive Ref
| o : O → Ref
| null : Ref

instance dec_eq_ref (r r' : Ref) [o_dec : ∀o o' : O, decidable (o = o')] [f_dec : decidable false] [t_dec : decidable true] : decidable (r = r') := begin
  have ineq : ∀o : O, (Ref.null = Ref.o o) = false, cc,
  have ineq' : ∀o : O, (Ref.o o = Ref.null) = false, cc,

  induction r,

  induction r',
  rw Ref.o.inj_eq,
  exact o_dec r r',
  rw ineq' r,
  exact f_dec,

  induction r',
  rw ineq r',
  exact f_dec,
  rw Ref.null.inj_eq,
  exact t_dec,
end

inductive V
| b : bool → V
| z : ℤ → V
| q : ℚ* → V
| o : Ref → V

structure var := (n : nat)
structure field := (n : nat)
structure func := (n : nat)
structure pred := (n : nat)

inductive T
| B : T
| Z : T
| O : T
| Q : T

def V.typ : V → T
| (V.b _) := T.B
| (V.z _) := T.Z
| (V.o _) := T.O
| (V.q _) := T.Q

def H := field × O → V
def S := var → V
def FieldPermMask := mask (field × O)
def PredPermMask := mask (pred × list V)

structure conf :=
(h : H)
(s : S)
(fieldPerm : FieldPermMask)
(predPerm : PredPermMask)

inductive E
| null : E
| const_b : bool → E
| const_n : ℤ → E
| x : var → E
| deref : E → field → E
| negate : E → E
| add : E → E → E
| div : E → E → E
| not : E → E
| eq : E → E → E
| apply : func → list E → E
| unfolding : pred → list E → E → E → E
| fieldPerm : E → field → E
| predPerm : pred → list E → E

inductive A
| e : E → A
| fieldAcc : E → field → E → A
| predAcc : pred → list E → E → A
| imp : E → A → A
| conj : A → A → A
| all : T → (E → A) → A
| ex : T → (E → A) → A
| forperm : field → E → A

inductive Eval
| type_err : Eval
| err : X → Eval
| ok : V → Eval

def Eval.is_x : Eval → Prop
| Eval.type_err := false
| (Eval.err _) := true
| (Eval.ok _) := false

def Eval.is_v : Eval → Prop
| Eval.type_err := false
| (Eval.err _) := false
| (Eval.ok _) := true

def v_of_is_v {e : Eval} (h : e.is_v) : V := begin
  cases e,
  case ok { exact e, },
  repeat { simp [Eval.is_v] at h, apply false.elim, exact h, },
end

def Eval.is_t : Eval → T → Prop
| Eval.type_err _ := false
| (Eval.err _) _ := false
| (Eval.ok v) t := v.typ = t

structure defs :=
(var : var → T) 
(field : field → T)
(func : func → (list T) × T × (list V → Eval)) -- shamelessly shallowly embed lean functions, to not deal with termination.
(pred : pred → (list T))

def E.typ (d : defs) : E → T
| (E.null) := T.O
| (E.const_b b) := T.B
| (E.const_n z) := T.Z
| (E.x x) := d.var x
| (E.deref o f) := d.field f
| (E.negate z) := z.typ
| (E.add z z') := z.typ
| (E.div z z') := z.typ
| (E.not b) := T.B
| (E.eq v v') := T.B
| (E.apply f args) := (d.func f).snd.fst
| (E.unfolding p args q e) := e.typ
| (E.fieldPerm o f) := T.Q
| (E.predPerm p args) := T.Q

def all_typed (d : defs) : list E → list T → Prop
| [] [] := true
| [] (_ :: _) := false
| (_ :: _) [] := false
| (e :: es) (t :: ts) := e.typ d = t ∧ all_typed es ts

mutual def all_wt, wt (d : defs)
with all_wt : list E → Prop
| [] := true
| (e :: es) := (wt e ∧ all_wt es)

with wt : E → Prop
| E.null := true
| (E.const_b b) := true
| (E.const_n z) := true
| (E.x x) := true
| (E.deref o f) := o.typ d = T.O ∧ wt o
| (E.negate z) := z.typ d = T.Z ∧ wt z
| (E.add z z') := z.typ d = z'.typ d ∧ (z.typ d = T.Z ∨ z.typ d = T.Q) ∧ wt z ∧ wt z'
| (E.div z z') := z.typ d = z'.typ d ∧ (z.typ d = T.Z ∨ z.typ d = T.Q) ∧ wt z ∧ wt z'
| (E.not b) := b.typ d = T.B ∧ wt b
| (E.eq v v') := v.typ d = v'.typ d ∧ wt v ∧ wt v'
| (E.apply f args) := all_typed d args (d.func f).fst ∧ all_wt args
| (E.unfolding p args q e) := all_typed d args (d.pred p) ∧ all_wt args ∧ wt q ∧ wt e
| (E.fieldPerm o f) := o.typ d = T.O ∧ wt o
| (E.predPerm p args) := all_typed d args (d.pred p) ∧ all_wt args

def conf.wt (d : defs) (c : conf) : Prop :=
  (∀x, (c.s x).typ = d.var x)
  ∧ (∀f o, (c.h (f, o)).typ = d.field f)

def Eval.map_v (e : Eval) (f : V → Eval) : Eval := match e with
| Eval.type_err := Eval.type_err
| Eval.err x := Eval.err x
| Eval.ok v := f v
end

#print Eval.rec

lemma map_v_is_x_or_t 
  : ∀ {t t' : T} {f : V → Eval} (e : Eval),
    e.is_x ∨ e.is_t t' →
    (∀ (v : V) (h : e = Eval.ok v), (f v).is_x ∨ (f v).is_t t) → 
    (e.map_v f).is_x ∨ (e.map_v f).is_t t 
  := 
begin
  intros t t' f e,
  cases e,

  case type_err {
    intros e_x_or_t f_all_v,
    simp [Eval.is_x, Eval.is_v] at e_x_or_t, 
    apply false.elim, exact e_x_or_t,
  },

  case err {
    intros e_x_or_t v,
    simp [Eval.map_v, Eval.is_x],
  },

  case ok {
    intros e_x_or_t v,
    simp [Eval.map_v],
    exact v e rfl,
  },
end

lemma eval_ok_t {e : Eval} {t : T} {v : V} :
  (Eval.ok v).is_t t ↔ v.typ = t := by simp [Eval.is_t]

def Eval.cases_v (e : Eval) (f_b : bool → Eval) (f_z : ℤ → Eval) (f_q : ℚ* → Eval) (f_o : Ref → Eval) :=
  e.map_v $ λv, match v with
  | V.b b := f_b b
  | V.z z := f_z z
  | V.q q := f_q q
  | V.o o := f_o o
  end

def evals_map' : list V → (list V → Eval) → list Eval → Eval
| acc f [] := f acc
| acc f (e :: es) := e.map_v $ λv, evals_map' (acc ++ [v]) f es

def evals_map (es : list Eval) (f : list V → Eval) : Eval :=
  evals_map' [] f es

lemma evals_map_x_or_t : 
  ∀ {t  : T} (f : list V → Eval) (es : list Eval),
    (∀e : Eval, ∃t : T, e ∈ es → e.is_x ∨ e.is_t t) →
    (∀ (vs : list V) (h : es = vs.map Eval.ok), (f vs).is_x ∨ (f vs).is_t t) →
    (evals_map es f).is_x ∨ (evals_map es f).is_t t :=
begin
  intros t f es,
  intros no_type_err,
  intros ok_f_no_type_err,
  
  induction es,

  case nil {
    simp only [evals_map, evals_map'],
    apply ok_f_no_type_err list.nil,
    simp only [list.map],
  },

  case cons : e es ih {
    simp only [evals_map, evals_map'],
    apply map_v_is_x_or_t,
    apply exists.elim,
    exact no_type_err e,
    intro t_before,
    simp,
    intro e_ok,
    /-exact e_ok,-/ sorry,

    sorry,
    sorry,
  },
end

mutual def eval, evals (d : defs)
with eval : conf → E → Eval
| c (E.null) := Eval.ok (V.o Ref.null)
| c (E.const_b b) := Eval.ok (V.b b)
| c (E.const_n z) := Eval.ok (V.z z)
| c (E.x x) := Eval.ok (c.s x)
| c (E.deref o f) := (eval c o).map_v $ λv, 
  match v with
  | (V.o Ref.null) := Eval.err X.null
  | (V.o (Ref.o o)) := if c.fieldPerm (f, o) = 0 then Eval.err X.perm else Eval.ok $ c.h (f, o)
  | _ := Eval.type_err
  end
| c (E.negate z) := (eval c z).map_v $ λv,
  match v with
  | (V.z z) := Eval.ok $ V.z (-z)
  | _ := Eval.type_err
  end
| c (E.add z z') := (eval c z).map_v $ λz, (eval c z').map_v $ λz',
  match z, z' with
  | (V.z z), (V.z z') := Eval.ok $ V.z (z + z')
  | (V.q q), (V.q q') := Eval.ok $ V.q (q + q')
  | _, _ := Eval.type_err
  end
| c (E.div z z') := (eval c z).map_v $ λz, (eval c z').map_v $ λz',
  match z, z' with
  | (V.z z), (V.z z') := if z' = 0 then Eval.err X.div else Eval.ok $ V.z $ int.div /- or flooring, round to zero? -/ z z'
  | (V.q q), (V.q q') := if q' = 0 then Eval.err X.div else Eval.ok $ V.q (q / q')
  | _, _ := Eval.type_err
  end
| c (E.not b) := (eval c b).map_v $ λv,
  match v with
  | (V.b b) := Eval.ok $ V.b ¬b
  | _ := Eval.type_err
  end
| c (E.eq v v') := (eval c v).map_v $ λv, (eval c v').map_v $ λv',
  match v, v' with
  | (V.b b), (V.b b') := Eval.ok $ V.b $ if b = b' then tt else ff
  | (V.z z), (V.z z') := Eval.ok $ V.b $ if z = z' then tt else ff
  | (V.q q), (V.q q') := Eval.ok $ V.b $ if q = q' then tt else ff
  | (V.o o), (V.o o') := Eval.ok $ V.b $ if o = o' then tt else ff
  | _, _ := Eval.type_err
  end
| c (E.apply f args) := evals_map (evals c args) $ λargs, ((d.func f).snd.snd args)
| c (E.unfolding p args q e) := evals_map (evals c args) $
    λargs, if c.predPerm (p, args) < 1
      then Eval.err X.perm
      else (eval c e).map_v $ λbody, Eval.ok (V.b ff)
| c (E.fieldPerm o f) := (eval c o).map_v $ λo,
  match o with
  | (V.o Ref.null) := Eval.err X.null
  | (V.o (Ref.o o)) := Eval.ok $ V.q $ c.fieldPerm (f, o)
  | _ := Eval.type_err
  end
| c (E.predPerm p args) := evals_map (evals c args)$ λargs, 
    Eval.ok $ V.q $ c.predPerm (p, args)

with evals : conf → list E → list Eval
| c [] := []
| c (e :: es) := (eval c e) :: (evals c es)

#print decidable.rec

lemma x {α : Type} (c : Prop) [decidable c] (a a' : α) : (ite c a a') = (ite (¬c) a' a) := begin
  exact (ite_not c a' a).symm
end 

lemma ite_prop {α : Type} {prop : α → Prop} {c : Prop} [h : decidable c] {a a' : α} :
  (c → prop a) ∧ (¬c → prop a') ↔ prop (ite c a a') := begin
  apply iff.intro,
  intro props,
  rw ite,
  apply h.rec_on,

  intro not_c,
  simp [(is_false not_c).rec_on], exact props.elim_right not_c,
  intro c,
  simp [(is_true c).rec_on], exact props.elim_left c,

  rw ite,
  apply h.rec_on,
  intro not_c,
  simp [(is_false not_c).rec_on],
  intro prop_a', finish,
  intro c,
  simp [(is_true c).rec_on],
  intro prop_a, finish,
end

theorem wt_sufficient {c : conf} {d : defs} {e : E} (h : wt d e) (ch : c.wt d)
  : (eval d c e).is_x ∨ (eval d c e).is_t (e.typ d) := 
begin
  rw conf.wt at ch,
  have var_ok : ∀x, (c.s x).typ = d.var x, exact and.elim_left ch,
  have field_ok : ∀f o, (c.h (f,o)).typ = d.field f, exact and.elim_right ch,
  clear ch,

  induction e,
  repeat { simp only [eval, wt, Eval.is_t, E.typ, V.typ, Eval.is_x, Eval.is_t, false_or, rfl] at *, },

  -- case x : x { exact var_ok x, },

  -- case deref : o f ih {
  --   apply map_v_is_x_or_t,
  --   exact ih (and.elim_right h),
  --   intros v v_ok,
  --   rw v_ok at *,
  --   cases v,
  --   repeat { simp [eval, Eval.is_x, Eval.is_t, V.typ, h.elim_left] at *, exact ih h, },
  --   cases v,
  --   simp [eval],
  --   by_cases c.fieldPerm (f, v) = 0,
  --   simp [h, Eval.is_x, Eval.is_t],
  --   rw ←ite_not,
  --   simp at h,
  --   simp [h, Eval.is_x, Eval.is_t, field_ok f v],
  --   simp [eval, Eval.is_t, Eval.is_x],
  -- },

  -- case negate : z ih {
  --   apply map_v_is_x_or_t,
  --   exact ih h.elim_right,
  --   intros v v_ok,
  --   rw v_ok at *,
  --   cases v,
  --   repeat { simp [eval] at *, },

  --   repeat { simp [eval, Eval.is_x, Eval.is_t, h.elim_left, V.typ] at *, },
  --   repeat {  exact ih h, },
  -- },

  -- case add : z z' ih ih' {
  --   apply map_v_is_x_or_t,
  --   exact ih h.elim_right.elim_right.elim_left,
  --   intros v v_ok,
  --   rw v_ok at *,
  --   apply map_v_is_x_or_t,
  --   exact ih' h.elim_right.elim_right.elim_right,
  --   intros v' v_ok',
  --   rw v_ok' at *,
  --   by_cases is_t_z : (z.typ d) = T.Z,

  --   cases v,
  --   repeat { simp [is_t_z] at *, },
  --   repeat { simp [eval, Eval.is_x, Eval.is_t, V.typ] at ih, apply false.elim, exact ih h.elim_right.elim_left, },
  --   cases v',
  --   repeat { simp [eval, Eval.is_x, Eval.is_t, V.typ, ←h.elim_left] at ih', apply false.elim, exact ih' h.elim_right.elim_right, },

  --   simp [eval, Eval.is_t, Eval.is_x, V.typ],

  --   cases v,
  --   repeat { simp [eval, Eval.is_x, Eval.is_t, V.typ, h.elim_right.elim_left] at ih, apply false.elim, exact ih h.elim_right.elim_right.elim_left, },
  --   cases v',
  --   repeat { simp [eval, Eval.is_x, Eval.is_t, V.typ, h.elim_right.elim_left, ←h.elim_left] at ih', apply false.elim, exact ih' h.elim_right.elim_right.elim_right, },
    
  --   simp [eval, Eval.is_t, Eval.is_x, V.typ, h.elim_right.elim_left],
  -- },

  -- case div : z z' ih ih' {
  --   apply map_v_is_x_or_t,
  --   exact ih h.elim_right.elim_right.elim_left,
  --   intros v v_ok,
  --   rw v_ok at *,
  --   apply map_v_is_x_or_t,
  --   exact ih' h.elim_right.elim_right.elim_right,
  --   intros v' v_ok',
  --   rw v_ok' at *,
  --   by_cases is_t_z : (z.typ d) = T.Z,

  --   cases v,
  --   repeat { simp [is_t_z] at *, },
  --   repeat { simp [eval, Eval.is_x, Eval.is_t, V.typ] at ih, apply false.elim, exact ih h.elim_right.elim_left, },
  --   cases v',
  --   repeat { simp [eval, Eval.is_x, Eval.is_t, V.typ, ←h.elim_left] at ih', apply false.elim, exact ih' h.elim_right.elim_right, },

  --   rw eval,
  --   by_cases div_zero : v' = 0,
  --   simp [div_zero, Eval.is_x],
  --   rw ←ite_not,
  --   simp [div_zero, Eval.is_t, V.typ],

  --   cases v,
  --   repeat { simp [eval, Eval.is_x, Eval.is_t, V.typ, h.elim_right.elim_left] at ih, apply false.elim, exact ih h.elim_right.elim_right.elim_left, },
  --   cases v',
  --   repeat { simp [eval, Eval.is_x, Eval.is_t, V.typ, ←h.elim_left, h.elim_right.elim_left] at ih', apply false.elim, exact ih' h.elim_right.elim_right.elim_right, },

  --   rw eval,
  --   by_cases div_zero : v' = 0,
  --   simp [div_zero, Eval.is_x],
  --   rw ←ite_not,
  --   simp [div_zero, Eval.is_t, V.typ, h.elim_right.elim_left],
  -- },

  -- case not : b ih {
  --   apply map_v_is_x_or_t,
  --   exact ih h.elim_right,
  --   intros v v_ok,
  --   rw v_ok at *,
  --   cases v,
  --   repeat { simp only [eval, Eval.is_x, Eval.is_t, V.typ, false_or], },
  --   repeat { simp only [h.elim_left, Eval.is_x, Eval.is_t, V.typ, false_or] at ih, },
  --   repeat { exact ih h.elim_right },
  -- },

  -- case eq : l r ih ih' {
  --   have t_eq : l.typ d = r.typ d, from h.elim_left,
  --   have wt_l : wt d l, from h.elim_right.elim_left,
  --   have wt_r : wt d r, from h.elim_right.elim_right,
  --   clear h,

  --   apply map_v_is_x_or_t,
  --   exact ih wt_l,
  --   intros v v_ok,
  --   apply map_v_is_x_or_t,
  --   exact ih' wt_r,
  --   intros v' v_ok',
  --   rw v_ok at *, rw v_ok' at *,
    
  --   cases v,
  --   repeat {
  --     cases v',
  --     repeat {
  --       simp only [eval],
  --       simp only [Eval.is_t, V.typ], 
  --       apply or.intro_right, 
  --       refl,
  --     },
  --     repeat {
  --       simp only [eval], simp only [Eval.is_t, Eval.is_x, V.typ, or_false],
  --       simp only [Eval.is_x, Eval.is_t, V.typ, false_or] at ih,
  --       simp only [Eval.is_x, Eval.is_t, V.typ, false_or, ←t_eq, ←ih wt_l] at ih',
  --       exact ih' wt_r,
  --     },
  --   },
  -- },

  case apply : f args {
    apply map_v_is_x_or_t,
  },

  repeat { sorry, },
end

end simplify