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

def allTyped (d : defs) : list E → list T → Prop
| [] [] := true
| [] (_ :: _) := false
| (_ :: _) [] := false
| (e :: es) (t :: ts) := e.typ d = t ∧ allTyped es ts

mutual def allWellTyped, wellTyped (d : defs)
with allWellTyped : list E → Prop
| [] := true
| (e :: es) := (wellTyped e ∧ allWellTyped es)

with wellTyped : E → Prop
| E.null := true
| (E.const_b b) := true
| (E.const_n z) := true
| (E.x x) := true
| (E.deref o f) := o.typ d = T.O ∧ wellTyped o
| (E.negate z) := z.typ d = T.Z ∧ wellTyped z
| (E.add z z') := z.typ d = z'.typ d ∧ (z.typ d = T.Z ∨ z.typ d = T.Q) ∧ wellTyped z ∧ wellTyped z'
| (E.div z z') := z.typ d = z'.typ d ∧ (z.typ d = T.Z ∨ z.typ d = T.Q) ∧ wellTyped z ∧ wellTyped z'
| (E.not b) := b.typ d = T.B ∧ wellTyped b
| (E.eq v v') := v.typ d = v'.typ d ∧ wellTyped v ∧ wellTyped v'
| (E.apply f args) := allTyped d args (d.func f).fst ∧ allWellTyped args
| (E.unfolding p args q e) := allTyped d args (d.pred p) ∧ allWellTyped args ∧ wellTyped q ∧ wellTyped e
| (E.fieldPerm o f) := o.typ d = T.O ∧ wellTyped o
| (E.predPerm p args) := allTyped d args (d.pred p) ∧ allWellTyped args

def Eval.map_v (e : Eval) (f : V → Eval) : Eval := match e with
| Eval.type_err := Eval.type_err
| Eval.err x := Eval.err x
| Eval.ok v := f v
end

def Eval.cases_v (e : Eval) (f_b : bool → Eval) (f_z : ℤ → Eval) (f_q : ℚ* → Eval) (f_o : Ref → Eval) :=
  e.map_v $ λv, match v with
  | V.b b := f_b b
  | V.z z := f_z z
  | V.q q := f_q q
  | V.o o := f_o o
  end

def Eval.as_b (e : Eval) (f : bool → Eval) : Eval :=
  e.cases_v f (λ_, Eval.type_err) (λ_, Eval.type_err) (λ_, Eval.type_err)

def Eval.as_o (e : Eval) (f : Ref → Eval) : Eval := 
  e.cases_v (λ_, Eval.type_err) (λ_, Eval.type_err) (λ_, Eval.type_err) f

def Eval.as_numeric (e : Eval) (f_z : ℤ → Eval) (f_q : ℚ* → Eval) : Eval :=
  e.cases_v (λ_, Eval.type_err) f_z f_q (λ_, Eval.type_err)

def Eval.as_z (e : Eval) (f : ℤ → Eval) : Eval := e.as_numeric f (λ_, Eval.type_err)

inductive values_reduction
| err : Eval → values_reduction
| ok : list V → values_reduction

def values_reduction.append (v : values_reduction) (e : Eval) : values_reduction :=
  match v with
  | (values_reduction.err e) := values_reduction.err e
  | (values_reduction.ok vs) := 
    match e with
    | Eval.type_err := values_reduction.err Eval.type_err
    | Eval.err x := values_reduction.err $ Eval.err x
    | Eval.ok v := values_reduction.ok (vs ++ [v])
    end
  end

def values_reduction.of (es : list Eval) : values_reduction :=
  es.foldl values_reduction.append (values_reduction.ok [])

def evals_map (es : list Eval) (f : list V → Eval) : Eval :=
  match values_reduction.of es with
  | values_reduction.err e := e
  | values_reduction.ok vs := f vs
  end

mutual def evals, eval {d : defs} (c : conf)
with evals : list E → list Eval
| [] := []
| (e :: es) := (eval e) :: (evals es)

with eval : E → Eval
| E.null := Eval.ok (V.o Ref.null)
| (E.const_b b) := Eval.ok (V.b b)
| (E.const_n z) := Eval.ok (V.z z)
| (E.x x) := Eval.ok (c.s x)
| (E.deref o f) := (eval o).as_o $ λo, 
  match o with
  | Ref.null := Eval.err X.null
  | Ref.o o := if c.fieldPerm (f, o) = 0 then Eval.err X.perm else Eval.ok $ c.h (f, o)
  end
| (E.negate z) := (eval z).as_z $ λz, Eval.ok $ V.z (-z)
| (E.add z z') := (eval z).map_v $ λz, (eval z').map_v $ λz',
  match z, z' with
  | (V.z z), (V.z z') := Eval.ok $ V.z (z + z')
  | (V.q q), (V.q q') := Eval.ok $ V.q (q + q')
  | _, _ := Eval.type_err
  end
| (E.div z z') := (eval z).map_v $ λz, (eval z').map_v $ λz',
  match z, z' with
  | (V.z z), (V.z z') := if z' = 0 then Eval.err X.div else Eval.ok $ V.z $ int.div /- or flooring, round to zero? -/ z z'
  | (V.q q), (V.q q') := if q' = 0 then Eval.err X.div else Eval.ok $ V.q (q / q')
  | _, _ := Eval.type_err
  end
| (E.not b) := (eval b).as_b $ λb, Eval.ok $ V.b ¬b
| (E.eq v v') := (eval v).map_v $ λv, (eval v').map_v $ λv',
  match v, v' with
  | (V.b b), (V.b b') := Eval.ok $ V.b $ if b = b' then tt else ff
  | (V.z z), (V.z z') := Eval.ok $ V.b $ if z = z' then tt else ff
  | (V.q q), (V.q q') := Eval.ok $ V.b $ if q = q' then tt else ff
  | (V.o o), (V.o o') := Eval.ok $ V.b $ if o = o' then tt else ff
  | _, _ := Eval.type_err
  end
| (E.apply f args) := evals_map (evals args) $ 
    λargs, (d.func f).snd.snd args
| (E.unfolding p args q e) := evals_map (evals args) $ 
    λargs, if c.predPerm (p, args) < 1 -- FIXME
      then Eval.err X.perm 
      else (eval e).map_v $ λbody, Eval.ok (V.b ff)
| (E.fieldPerm o f) := (eval o).as_o $ λo,
  match o with
  | Ref.null := Eval.err X.null
  | (Ref.o o) := Eval.ok $ V.q $ c.fieldPerm (f, o)
  end
| (E.predPerm p args) := evals_map (evals args) $
    λargs, Eval.ok $ V.q $ c.predPerm (p, args)



end simplify