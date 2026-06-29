/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
import Mathlib

namespace List

abbrev Sorted {α : Type*} (r : α → α → Prop) (l : List α) : Prop :=
  l.Pairwise r

@[simp]
theorem sorted_nil {α : Type*} {r : α → α → Prop} : List.Sorted r [] := by
  simp [List.Sorted]

namespace Sorted

theorem tail {α : Type*} {r : α → α → Prop} {a : α} {l : List α}
    (h : List.Sorted r (a :: l)) : List.Sorted r l := by
  simpa [List.Sorted] using (List.pairwise_cons.mp h).2

theorem filter {α : Type*} {r : α → α → Prop} (p : α → Bool) {l : List α}
    (h : List.Sorted r l) : List.Sorted r (l.filter p) := by
  simpa [List.Sorted] using List.Pairwise.filter p h

end Sorted

end List
