import data.fintype.basic
import tactic.derive_fintype
import tactic.linarith
import .finmap

namespace col

inductive ind_vec (σ : Type) : nat → Type
| nil : ind_vec 0
| cons : Π{n : nat}, σ → ind_vec n → ind_vec (n.succ)

def ind_vec.as_list {σ : Type} : ∀{n : nat}, ind_vec σ n → list σ
| _ ind_vec.nil := []
| _ (ind_vec.cons x xs) := x :: xs.as_list

lemma ind_vec.as_list_length {σ : Type} {n : nat} (v : ind_vec σ n) : v.as_list.length = n := begin
  induction v, 
  case nil { refl, },
  case cons { simp [ind_vec.as_list, v_ih], },
end

def ind_vec.as_vector {σ : Type} {n : nat} (v : ind_vec σ n) : vector σ n :=
  ⟨v.as_list, v.as_list_length⟩

def list.as_ind_vec {σ : Type} : Π(xs : list σ), ind_vec σ xs.length
| list.nil := ind_vec.nil
| (x :: xs) := ind_vec.cons x xs.as_ind_vec

def vector.as_ind_vec {σ : Type} {n : nat} : vector σ n → ind_vec σ n
| ⟨xs, h⟩ := eq.rec xs.as_ind_vec h

def ind_vec.map {σ τ : Type} : ∀{n : nat}, ind_vec σ n → (σ → τ) → ind_vec τ n
| _ ind_vec.nil _ := ind_vec.nil
| _ (ind_vec.cons x xs) f := ind_vec.cons (f x) (xs.map f)

structure domain :=
  (t_args : nat)

variable {domain_k : Type}
variable {domain_k_finite : fintype domain_k}
variable domains : finmap domain_k domain

inductive atyp (type_bindings : nat)
| binding : fin type_bindings → atyp
| bool : atyp
| int : atyp
| perm : atyp
| ref : atyp
| domain : Π(k : domain_k), ind_vec atyp (domains k).t_args → atyp

def typ := atyp domains 0

mutual def atyp.monomorphize, atyp.monomorphize_all {n : nat} (subs : vector (typ domains) n)

with atyp.monomorphize : atyp domains n → typ domains
| (atyp.binding i) := subs.nth i
| atyp.bool := atyp.bool
| atyp.int := atyp.int
| atyp.perm := atyp.perm
| atyp.ref := atyp.ref
| (atyp.domain k args) := atyp.domain k (atyp.monomorphize_all args)

with atyp.monomorphize_all : ∀{m : nat}, ind_vec (atyp domains n) m → ind_vec (typ domains) m
| 0 ind_vec.nil := ind_vec.nil
| (nat.succ i) (ind_vec.cons t ts) := ind_vec.cons (atyp.monomorphize t) (atyp.monomorphize_all ts)

structure domain_func :=
  (result : (typ domains))
  (args : list (typ domains))

structure function :=
  (result : typ domains)
  (args : list (typ domains))

structure field :=
  (t : typ domains)

structure predicate :=
  (args : list (typ domains))

structure method :=
  (args : list (typ domains))
  (locals : list (typ domains))
  (out_args : list (typ domains))

structure ctx_t 
  (domain_k : Type)
  (domain_func_k : Type)
  (func_k : Type)
  (field_k : Type)
  (predicate_k : Type)
  (method_k : Type)
  :=
  [domain_k_finite : fintype domain_k]
  (domains : finmap domain_k domain)
  [domain_func_k_finite : fintype domain_func_k]
  (domain_funcs : finmap domain_func_k (domain_func domains))
  [func_k_finite : fintype func_k]
  (funcs : finmap func_k (function domains))
  [field_k_finite : fintype field_k]
  (fields : finmap field_k (field domains))
  [predicate_k_finite : fintype predicate_k]
  (predicates : finmap predicate_k (predicate domains))
  [method_finite : fintype method_k]
  (methods : finmap method_k (method domains))

variable {domain_func_k : Type}
variable {func_k : Type}
variable {field_k : Type}
variable {predicate_k : Type}
variable {method_k : Type}

variable (ctx : ctx_t domain_k domain_func_k func_k field_k predicate_k method_k)

inductive want
| yes 
| no

def want.typ : want → Type
| want.yes := unit
| want.no := empty

structure exp_cfg :=
  (have_heap : want)
  (have_method : want)
  (have_assn : want)
  (have_result : want)
  (type_bindings : nat)

mutual inductive a_exp, domain_inv, func_inv, pred_inv
(ctx : ctx_t domain_k domain_func_k func_k field_k predicate_k method_k)
(cfg : exp_cfg)
(here : cfg.have_method.typ → method_k)

with a_exp : Type
-- pure, heap-independent
| const_bool : bool → a_exp
| const_int : ℤ → a_exp
| domain_apply_indirect : domain_inv → a_exp
| func_apply_indirect : func_inv → a_exp
| and : a_exp → a_exp → a_exp
| implies : a_exp → a_exp → a_exp
| binding : nat → a_exp
| all : (atyp ctx.domains cfg.type_bindings) → a_exp → a_exp
| ex : (atyp ctx.domains cfg.type_bindings) → a_exp → a_exp

-- normal, heap-dependent
| deref : cfg.have_heap.typ → a_exp → field_k → a_exp

-- local
| arg (m : cfg.have_method.typ) : fin (ctx.methods (here m)).args.length → a_exp
| out (m : cfg.have_method.typ) : fin (ctx.methods (here m)).out_args.length → a_exp
| loc (m : cfg.have_method.typ) : fin (ctx.methods (here m)).locals.length → a_exp

-- postcondition result
| result : cfg.have_result.typ → a_exp

-- assertions
| acc_field : cfg.have_assn.typ → a_exp → field_k → a_exp → a_exp
| acc_pred : cfg.have_assn.typ → pred_inv → a_exp → a_exp

with domain_inv : Type
| apply (k : domain_func_k) : ind_vec a_exp (ctx.domain_funcs k).args.length → domain_inv

with func_inv : Type
| apply (k : func_k) : ind_vec a_exp (ctx.funcs k).args.length → func_inv

with pred_inv : Type
| apply (k : predicate_k) : ind_vec a_exp (ctx.predicates k).args.length → pred_inv

def pure_exp (type_bindings : nat) : Type := 
  a_exp ctx { have_heap := want.no, have_method := want.no, have_assn := want.no, have_result := want.no, type_bindings := type_bindings }
    empty.elim

def exp : Type := 
  a_exp ctx { have_heap := want.yes, have_method := want.no, have_assn := want.no, have_result := want.no, type_bindings := 0 }
    empty.elim

def assn (have_result : want) : Type := 
  a_exp ctx { have_heap := want.yes, have_method := want.no, have_assn := want.yes, have_result := have_result, type_bindings := 0 }
    empty.elim

def local_exp (here : method_k) : Type :=
  a_exp ctx { have_heap := want.yes, have_method := want.yes, have_assn := want.no, have_result := want.no, type_bindings := 0 }
    (λ_, here)

def local_assn (here : method_k) : Type :=
  a_exp ctx { have_heap := want.yes, have_method := want.yes, have_assn := want.yes, have_result := want.no, type_bindings := 0 }
    (λ_, here)

structure domain_axiom :=
  (t_args : nat)
  (ax : pure_exp ctx t_args)

structure func_impl :=
  (requires : assn ctx want.no)
  (body : option $ exp ctx)
  (ensures : assn ctx want.yes)

structure predicate_impl :=
  (body : assn ctx want.no)

inductive stat (here : method_k)
| nop : stat
| seqn : list stat → stat
| cond : (local_exp ctx here) → stat → stat → stat
| assign : fin (ctx.methods here).locals.length → (local_exp ctx here) → stat

structure method_impl (here : method_k) :=
  (requires : local_assn ctx here)
  (body : option $ exp ctx)
  (ensures : local_assn ctx here)

structure verification :=
  {domain_k : Type}
  {domain_func_k : Type}
  {func_k : Type}
  {field_k : Type}
  {predicate_k : Type}
  {method_k : Type}

  [domain_k_finite : fintype domain_k]
  [domain_func_k_finite : fintype domain_func_k]
  [func_k_finite : fintype func_k]
  [field_k_finite : fintype field_k]
  [predicate_k_finite : fintype predicate_k]
  [method_finite : fintype method_k]
  
  (ctx : ctx_t domain_k domain_func_k func_k field_k predicate_k method_k)

  (domain_axioms : list (domain_axiom ctx))
  (func_impls : finmap func_k (func_impl ctx))
  (predicate_impls : finmap predicate_k (predicate_impl ctx))
  (method_impls : Π(k : method_k), method_impl ctx k)

-- typing rules
inductive a_exp.t 
(ctx : ctx_t domain_k domain_func_k func_k field_k predicate_k method_k)
(cfg : exp_cfg)
(here : cfg.have_method.typ → method_k)
: (list $ atyp ctx.domains cfg.type_bindings) → (a_exp ctx cfg here) → (atyp ctx.domains cfg.type_bindings) → Prop

| const_bool (vs : (list $ atyp ctx.domains cfg.type_bindings)) (b : bool) : a_exp.t vs (a_exp.const_bool b) atyp.bool
| const_int (vs : (list $ atyp ctx.domains cfg.type_bindings)) (i : ℤ) : a_exp.t vs (a_exp.const_int i) atyp.int
| domain_apply
    (vs : (list $ atyp ctx.domains cfg.type_bindings))
    (k : domain_func_k) 
    (args : ind_vec (a_exp ctx cfg here) (ctx.domain_funcs k).args.length)
    (args_ok : 
      ∀(i : fin (ctx.domain_funcs k).args.length), 
        a_exp.t vs (args.as_vector.nth i) 
          ((ctx.domain_funcs k).args.nth_le i i.property))
    : a_exp.t vs (a_exp.domain_apply_indirect (domain_inv.apply k args)) (ctx.domain_funcs k).result
| func_apply
    (vs : (list $ atyp ctx.domains cfg.type_bindings))
    (k : func_k)
    (args : ind_vec (a_exp ctx cfg here) (ctx.funcs k).args.length)
    (args_ok : 
      ∀(i : fin (ctx.funcs k).args.length),
        a_exp.t vs (args.as_vector.nth i)
          ((ctx.funcs k).args.nth_le i i.property))
    : a_exp.t vs (a_exp.func_apply_indirect (func_inv.apply k args)) (ctx.funcs k).result
| and (vs : (list $ atyp ctx.domains cfg.type_bindings)) : ∀l r, a_exp.t vs l atyp.bool → a_exp.t vs r atyp.bool → a_exp.t vs (a_exp.and l r) atyp.bool
| implies (vs : (list $ atyp ctx.domains cfg.type_bindings)) : ∀l r, a_exp.t vs l atyp.bool → a_exp.t vs r atyp.bool → a_exp.t vs (a_exp.implies l r) atyp.bool
| binding (vs : (list $ atyp ctx.domains cfg.type_bindings)) (i : nat) (h : i < vs.length) : a_exp.t vs (a_exp.binding i) $ vs.nth_le i h
| all 
    (vs : (list $ atyp ctx.domains cfg.type_bindings)) 
    (v : atyp ctx.domains cfg.type_bindings) 
    (e : a_exp ctx cfg here)
  : a_exp.t (v :: vs) e atyp.bool → a_exp.t vs (a_exp.all v e) atyp.bool
| ex
    (vs : (list $ atyp ctx.domains cfg.type_bindings)) 
    (v : atyp ctx.domains cfg.type_bindings) 
    (e : a_exp ctx cfg here)
  : a_exp.t (v :: vs) e atyp.bool → a_exp.t vs (a_exp.ex v e) atyp.bool
| deref
    (vs : (list $ atyp ctx.domains cfg.type_bindings)) 
    (have_heap : cfg.have_heap.typ)
    (obj : a_exp ctx cfg here)
    (k : field_k)
  : a_exp.t vs obj atyp.ref → a_exp.t vs (a_exp.deref have_heap obj k) (ctx.fields k).t

/-
-- semantics definitions
def objects := nat

structure location :=
  (obj : objects)
  (field : field)

inductive value
| int : ℤ → value
| rat : ℚ → value
| obj : objects → value

structure heap :=
  (mask : location → ℚ)
  (value : location → value)

structure state :=
  (heap : heap)
  (locals : nat → value)

-- semantics
def state.sat : state → exp → Prop := λ s e, match e with
| _ := sorry
end
-/

end col

namespace ex

@[derive fintype]
inductive domain_name
| option

open domain_name

def domains : finmap domain_name col.domain
| option := { t_args := 1 }

@[derive fintype]
inductive method_name
| test

open method_name

def methods : finmap method_name (col.method domains)
| test := { args := [col.atyp.domain option $ col.list.as_ind_vec [col.atyp.int]], locals := [], out_args := [] }

#check methods test

end ex