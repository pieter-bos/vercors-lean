import algebra
import tactic.linarith

-- set_option trace.simplify.rewrite true
-- set_option trace.simp_lemmas true
-- set_option trace.linarith true

def nonneg_rat : Type :=
  {q : ℚ // q.nonneg}

notation `ℚ*` := nonneg_rat

-- ℚ* is a comm-semi-ring with multiplicative inverse
-- Equivalent: a field without an additive inverse.
-- Additionally it has a decidable linear order matching the operations.

namespace nonneg_rat

instance : has_repr ℚ* := ⟨rat.repr ∘ subtype.val⟩
instance : has_to_string ℚ* := ⟨rat.repr ∘ subtype.val⟩

def of_rat (q : ℚ) (h : q.nonneg) : ℚ* := subtype.mk q h

lemma zero_def : (0:ℚ) = (rat.mk 0 1) := begin refl, end
lemma one_def : (1:ℚ) = (rat.mk 1 1) := begin refl, end
lemma unpack_rat (q : ℚ) : q = (rat.mk q.num q.denom) := rat.num_denom.symm

instance : has_zero ℚ* := ⟨of_rat 0 (refl 0)⟩
instance : has_one ℚ* := ⟨of_rat 1 (begin rw one_def, rw rat.mk_nonneg, exact int.one_nonneg, exact int.one_pos, end)⟩
instance : inhabited ℚ* := ⟨0⟩
-- instance : nontrivial ℚ* := ⟨⟨0, 1, begin exact ne_of_lt _ end⟩⟩

def add (q q' : ℚ*) : ℚ* := of_rat (q.val + q'.val) (rat.nonneg_add q.property q'.property)
instance : has_add ℚ* := ⟨add⟩

def mul (q q' : ℚ*) : ℚ* := of_rat (q.val * q'.val) (rat.nonneg_mul q.property q'.property)
instance : has_mul ℚ* := ⟨mul⟩

def inv (q : ℚ*) : ℚ* := of_rat (q.val⁻¹) begin
  by_cases zero : q.val = 0,
  rw [zero, zero_def, rat.inv_def, rat.mk_zero, zero_def, rat.mk_nonneg], exact int.one_pos,
  rw eq.symm (ne.def _ _) at zero,
  have h : 0 ≤ q.val, exact rat.nonneg_iff_zero_le.elim_left q.property,
  generalize val : q.val = q_val, rw val at *,
  
  have nonzero : q_val.num ≠ 0, exact by_contradiction begin
    intros n_zero,
    rw [ne.def, not_not] at n_zero, 
    rw [unpack_rat q_val, n_zero, rat.zero_mk] at zero,
    exact ne.irrefl zero,
  end,

  rw [unpack_rat q_val, rat.inv_def, rat.mk_nonneg],
  exact int.coe_nat_nonneg q_val.denom,
  exact rat.num_pos_iff_pos.elim_right (lt_of_le_of_ne h (ne.symm zero)),
end

instance : has_inv ℚ* := ⟨inv⟩

def div (q q' : ℚ*) : ℚ* := q * q'⁻¹
instance : has_div ℚ* := ⟨div⟩

def le (q q' : ℚ*) : Prop := q.val.le q'.val
instance : has_le ℚ* := ⟨le⟩

@[simp] lemma subtype_val (q : ℚ*) : (⟨q.val, q.property⟩ : ℚ*).val = q.val := begin exact rfl, end
lemma expand (q : ℚ*) : q = ⟨q.val, q.property⟩ := by exact subtype.eq rfl
@[simp] theorem eq_val (q q' : ℚ*) : q = q' ↔ q.val = q'.val := by rw [expand q, expand q']; exact subtype.mk_eq_mk
@[simp] theorem add_val (q q' : ℚ*) : (q + q').val = q.val + q'.val := by cc
@[simp] theorem mul_val (q q' : ℚ*) : (q * q').val = q.val * q'.val := by cc
@[simp] theorem inv_val (q : ℚ*) : (q⁻¹).val = q.val⁻¹ := by cc
theorem le_val (q q' : ℚ*) : q ≤ q' ↔ q.val ≤ q'.val := by simp

theorem add_assoc (a b c : ℚ*) : a + b + c = a + (b + c) := by simp; exact rat.add_assoc _ _ _
theorem add_comm (a b : ℚ*) : a + b = b + a := by simp; exact rat.add_comm _ _
theorem mul_assoc (a b c : ℚ*) : a * b * c = a * (b * c) := by simp; exact rat.mul_assoc _ _ _
theorem mul_comm (a b : ℚ*) : a * b = b * a := by simp; exact rat.mul_comm _ _

theorem zero_add (q : ℚ*) : 0 + q = q := by simp; refl
theorem add_zero (q : ℚ*) : q + 0 = q := by simp; refl

theorem one_mul (q : ℚ*) : 1 * q = q := by simp; exact rat.one_mul _
theorem mul_one (q : ℚ*) : q * 1 = q := by simp; exact rat.mul_one _

theorem left_distrib (a b c : ℚ*) : a * (b + c) = a*b + a*c := by simp; exact rat.mul_add _ _ _
theorem right_distrib (a b c : ℚ*) : (a + b) * c = a*c + b*c := by simp; exact rat.add_mul _ _ _

theorem mul_inv_cancel (a : ℚ*) : a ≠ 0 → a * a⁻¹ = 1 := by simp; exact rat.mul_inv_cancel _

theorem add_left_cancel (l a b : ℚ*) : l + a = l + b → a = b := by simp
theorem add_right_cancel (a r b : ℚ*) : a + r = b + r → a = b := by simp

theorem mul_zero (q : ℚ*) : q * 0 = 0 := 
  have q0 : q*0 + q*0 = q*0 + 0,
  by calc q*0 + q*0
      = q * (0+0) :
    by rw ←left_distrib
  ... = q * 0 :
    by rw zero_add
  ... = q*0 + 0 :
    by rw add_zero,
  
  show q * 0 = 0, from add_left_cancel _ _ _ q0

theorem zero_mul [mul_zero_class ℚ] (q : ℚ*) : 0 * q = 0 := 
  eq.trans (mul_comm 0 q) (mul_zero q)

theorem le_refl (q : ℚ*) : q ≤ q := by rw le_val
theorem le_trans (a b c : ℚ*) : a ≤ b → b ≤ c → a ≤ c := by simp only [le_val]; exact rat.le_trans
theorem le_antisymm (a b : ℚ*) : a ≤ b → b ≤ a → a = b := by simp only [le_val, eq_val]; exact rat.le_antisymm
theorem le_total (a b : ℚ*) : a ≤ b ∨ b ≤ a := by simp only [le_val]; exact rat.le_total _ _

theorem add_le_add_left (q q' : ℚ*) : q ≤ q' → ∀l, l + q ≤ l + q' := by simp only [le_val]; simp
theorem le_of_add_le_add_left (l a b : ℚ*) : l + a ≤ l + b → a ≤ b := by simp only [le_val]; simp

instance decidable_le : decidable_rel ((≤) : ℚ* → ℚ* → Prop)
| a b := show decidable (a.val ≤ b.val), by apply_instance

instance : comm_semiring ℚ* :=
{
  zero := 0,
  one := 1,
  add := add,
  mul := mul,

  add_assoc := add_assoc,
  add_comm := add_comm,
  mul_assoc := mul_assoc,
  mul_comm := mul_comm,

  zero_add := zero_add,
  add_zero := add_zero,
  
  one_mul := one_mul,
  mul_one := mul_one,
  
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  
  left_distrib := left_distrib,
  right_distrib := right_distrib,
  /-
  Missing, because it is not a field:
  - neg
  - add_left_neg
  - exists_pair_ne (to define)
  - inv (defined)
  - mul_inv_cancel (to define)
  -/
}

instance : add_left_cancel_semigroup ℚ* :=
{
  add_left_cancel := add_left_cancel,
  add := add,
  add_assoc := add_assoc,
}
instance : add_right_cancel_semigroup ℚ* :=
{
  add_right_cancel := add_right_cancel,
  add := add,
  add_assoc := add_assoc,
}

instance : decidable_linear_order ℚ* :=
{
  le := le,
  le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm,
  le_total := le_total,
  decidable_le := assume a b, rat.decidable_le a.val b.val,
}

instance : ordered_semiring ℚ* := 
{
  zero := 0,
  one := 1,
  add := add,
  mul := mul,

  add_assoc := add_assoc,
  add_comm := add_comm,
  mul_assoc := mul_assoc,

  zero_add := zero_add,
  add_zero := add_zero,
  
  one_mul := one_mul,
  mul_one := mul_one,
  
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  
  left_distrib := left_distrib,
  right_distrib := right_distrib,

  le := le,
  le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm,

  add_left_cancel := add_left_cancel,
  add_right_cancel := add_right_cancel,
  add_le_add_left := add_le_add_left,
  le_of_add_le_add_left := le_of_add_le_add_left,
  zero_lt_one := dec_trivial,
  mul_lt_mul_of_pos_left := begin  
    intros m m' l, 
    simp only [lt_iff_le_not_le, le_val], 
    simp only [←lt_iff_le_not_le],
    exact mul_lt_mul_of_pos_left,
  end,
  mul_lt_mul_of_pos_right := begin
    intros m m' l, 
    simp only [lt_iff_le_not_le, le_val], 
    simp only [←lt_iff_le_not_le],
    exact mul_lt_mul_of_pos_right,
  end,
}

end nonneg_rat