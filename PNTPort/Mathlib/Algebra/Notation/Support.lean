module

/- Ported from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, commit e9906138410f, Apache-2.0) to the Mathlib pinned by grh-compact. Changes: blueprint attributes removed, module paths renamed, and API adaptations listed in PORTING.md. -/

public import Mathlib.Algebra.Notation.Support


public section

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
