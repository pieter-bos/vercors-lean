#eval (0 : (ℕ : (Type : (Type 1 : (Type 2 : (Type 3 : (Type _ : Type*)))))))

namespace russell

def set (α : Type) := α → bool
def set.contains {α : Type} (s : set α) (v : α) := s v

constant val : Type

inductive val_unwrap
| emp : val_unwrap
| set : set val → val_unwrap

constant val.unwrap : val → val_unwrap

noncomputable def R : set val := 
  λv, match v.unwrap with
  | val_unwrap.emp := tt
  | (val_unwrap.set s) := ¬(s.contains v)
  end

end russell