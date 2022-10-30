import data.fintype.basic
import logic.is_empty

variables α β : Type

def finmap [fintype α] := α → β

namespace finmap

def empty (σ : Type) : finmap empty σ := empty.elim

def keys [inst : fintype α] (m : finmap α β) : finset α :=
  inst.elems

def values [inst : fintype α] (m : finmap α β) : multiset β :=
  inst.elems.1.map m

end finmap