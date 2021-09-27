import algebra
import tactic.linarith

set_option trace.simplify.rewrite true
set_option trace.simp_lemmas true
set_option trace.linarith true

lemma x {β : Type} (p : β → Prop) {α : subtype p} (b₁ b₂ : β) (ok₁ : p b₁) (ok₂ : p b₂) :
  (subtype.mk b₁ ok₁).val = b₁ 
  :=
  begin
    exact rfl
  end

lemma y (q : ℚ) : 0 * q = q := begin library_search end

def nonneg_rat : Type :=
  {q : ℚ // q.nonneg}

notation `ℚ*` := nonneg_rat

-- ℚ* is a semi-ring of which multiplication is commutative, and has an inverse.
-- Equivalent: a field without an additive inverse.

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

def inv' (q : ℚ*) : ℚ* := of_rat (q.val⁻¹) begin
  have h : 0 ≤ q.val.num,
  exact rat.num_nonneg_iff_zero_le.elim_right 
    (rat.nonneg_iff_zero_le.elim_left q.property),
  rw [unpack_rat q.val, rat.inv_def, rat.nonneg_iff_zero_le, rat.num_nonneg_iff_zero_le.symm],
  sorry,
end

@[simp] lemma subtype_val (q : ℚ*) : (⟨q.val, q.property⟩ : ℚ*).val = q.val := begin exact rfl, end
lemma expand (q : ℚ*) : q = ⟨q.val, q.property⟩ := by exact subtype.eq rfl
@[simp] theorem eq_val (q q' : ℚ*) : q = q' ↔ q.val = q'.val := by rw [expand q, expand q']; exact subtype.mk_eq_mk
@[simp] theorem add_val (q q' : ℚ*) : (q + q').val = q.val + q'.val := by cc
@[simp] theorem mul_val (q q' : ℚ*) : (q * q').val = q.val * q'.val := by cc
@[simp] theorem inv_val (q : ℚ*) : (q⁻¹).val = q.val⁻¹ := by cc

#check add_left_cancel

theorem add_assoc (a b c : ℚ*) : a + b + c = a + (b + c) := by simp; exact rat.add_assoc _ _ _
theorem zero_add (q : ℚ*) : 0 + q = q := by simp; refl
theorem add_zero (q : ℚ*) : q + 0 = q := by simp; refl
theorem add_comm (a b : ℚ*) : a + b = b + a := by simp; exact rat.add_comm _ _
theorem mul_assoc (a b c : ℚ*) : a * b * c = a * (b * c) := by simp; exact rat.mul_assoc _ _ _
theorem one_mul (q : ℚ*) : 1 * q = q := by simp; exact rat.one_mul _
theorem mul_one (q : ℚ*) : q * 1 = q := by simp; exact rat.mul_one _
theorem left_distrib (a b c : ℚ*) : a * (b + c) = a*b + a*c := by simp; exact rat.mul_add _ _ _
theorem right_distrib (a b c : ℚ*) : (a + b) * c = a*c + b*c := by simp; exact rat.add_mul _ _ _
theorem zero_mul [mul_zero_class ℚ] (q : ℚ*) : 0 * q = 0 := begin
  simp,
  generalize : ↑q = q',
  exact zero_mul q',
end
theorem mul_zero (q : ℚ*) : q * 0 = 0 := sorry

instance : semiring ℚ* :=
{
  zero := 0,
  one := 1,
  add := add,
  mul := mul,
  add_assoc := add_assoc,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  left_distrib := left_distrib,
  right_distrib := right_distrib,
}

end nonneg_rat