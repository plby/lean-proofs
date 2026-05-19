import Mathlib.Algebra.Notation.Support

set_option linter.style.setOption false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.flexible false

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
