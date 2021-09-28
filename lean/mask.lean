import .nonneg_rat

def mask (α : Type*) : Type := α → ℚ*

namespace mask

def of_func {α : Type} (f : α → ℚ*) : mask α := f
def func_of {α : Type} (m : mask α) : α → ℚ* := m

lemma x {α β : Type} (f g : α → β) : f = g ↔ ∀x, f x = g x := begin library_search end

instance {α : Type} : has_zero (mask α) := ⟨of_func (λ_, 0)⟩
instance {α : Type} : inhabited (mask α) := ⟨0⟩

def add {α : Type} (m m' : mask α) : mask α :=
  of_func $ λa, m a + m' a

instance {α : Type} : has_add (mask α) := ⟨add⟩

def le {α : Type} (m m' : mask α) : Prop :=
  ∀a, m a ≤ m' a

instance {α : Type} : has_le (mask α) := ⟨le⟩

lemma le_def {α : Type} (m m' : mask α) : m ≤ m' ↔ ∀a, m a ≤ m' a := by refl

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

instance {α : Type} : partial_order (mask α) :=
{
  le := le,
  le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm,
}

end mask