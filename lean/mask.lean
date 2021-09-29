import .nonneg_rat

def mask (α : Type*) : Type := α → ℚ*

namespace mask

def of_func {α : Type} (f : α → ℚ*) : mask α := f
def func_of {α : Type} (m : mask α) : α → ℚ* := m

instance {α : Type} : has_zero (mask α) := ⟨λ_, 0⟩
instance {α : Type} : inhabited (mask α) := ⟨0⟩

lemma zero_def {α : Type} : (0 : mask α) = λ_ ,0 := by refl

def add {α : Type} (m m' : mask α) : mask α :=
  λa, m a + m' a

instance {α : Type} : has_add (mask α) := ⟨add⟩

lemma add_def {α : Type} (m m' : mask α) : m + m' = λa, m a + m' a := by refl

def le {α : Type} (m m' : mask α) : Prop :=
  ∀a, m a ≤ m' a

instance {α : Type} : has_le (mask α) := ⟨le⟩

lemma le_def {α : Type} (m m' : mask α) : m ≤ m' ↔ ∀a, m a ≤ m' a := by refl

theorem zero_add {α : Type} (m : mask α) : 0 + m = m := begin
  simp only [function.funext_iff],
  intro a,
  rw add_def,
  simp [zero_def],
end

theorem add_zero {α : Type} (m : mask α) : m + 0 = m := begin
  simp only [function.funext_iff],
  intro a,
  rw add_def,
  simp [zero_def],
end

theorem add_assoc {α : Type} (m₁ m₂ m₃ : mask α) : m₁ + m₂ + m₃ = m₁ + (m₂ + m₃) := begin
  simp only [add_def, function.funext_iff],
  intro a,
  exact nonneg_rat.add_assoc _ _ _,
end

theorem add_comm {α : Type} (m m' : mask α) : m + m' = m' + m := begin
  simp only [add_def, function.funext_iff],
  intro a,
  exact nonneg_rat.add_comm _ _,
end

theorem add_left_cancel {α : Type} (l m m' : mask α) : l + m = l + m' → m = m' := begin
  simp only [add_def, function.funext_iff],
  intros all_left a,
  exact nonneg_rat.add_left_cancel _ _ _ (all_left a),
end

theorem add_right_cancel {α : Type} (m r m' : mask α) : m + r = m' + r → m = m' := begin
  simp only [add_def, function.funext_iff],
  intros all_right a,
  exact nonneg_rat.add_right_cancel _ _ _ (all_right a),
end

theorem le_refl {α : Type} (m : mask α) : m ≤ m := by rw le_def; intro a; exact nonneg_rat.le_refl (m a)
theorem le_trans {α : Type} (a b c : mask α) : a ≤ b → b ≤ c → a ≤ c := begin
  simp only [le_def],
  intro h_ab,
  intro h_bc,
  intro x,
  exact nonneg_rat.le_trans (a x) (b x) (c x) (h_ab x) (h_bc x),
end
theorem le_antisymm {α : Type} (a b : mask α) : a ≤ b → b ≤ a → a = b := begin
  simp only [le_def],
  intro h_ab,
  intro h_ba,
  rw function.funext_iff,
  intro x,
  exact nonneg_rat.le_antisymm (a x) (b x) (h_ab x) (h_ba x),
end

theorem add_le_add_left {α : Type} (m m' : mask α) : m ≤ m' → ∀l, l + m ≤ l + m' := begin
  simp only [le_def, add_def],
  intros all_leq l a,
  apply nonneg_rat.add_le_add_left,
  exact all_leq a,
end

theorem le_of_add_le_add_left {α : Type} (l m m' : mask α) : l + m ≤ l + m' → m ≤ m' := begin
  simp only [le_def, add_def],
  intros all_left a,
  exact nonneg_rat.le_of_add_le_add_left _ _ _ (all_left a),
end

instance {α : Type} : ordered_cancel_add_comm_monoid (mask α) :=
{
  zero := 0,
  add := add,
  le := le,

  zero_add := zero_add,
  add_zero := add_zero,
  
  add_assoc := add_assoc,
  add_comm := add_comm,

  add_left_cancel := add_left_cancel,
  add_right_cancel := add_right_cancel,

  le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm,

  add_le_add_left := add_le_add_left,
  le_of_add_le_add_left := le_of_add_le_add_left,
}

end mask