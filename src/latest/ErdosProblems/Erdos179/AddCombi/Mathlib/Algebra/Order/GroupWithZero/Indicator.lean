module

public import ErdosProblems.Erdos179.AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Algebra.Order.ZeroLEOne

public section

open scoped Indicator

namespace Set
variable {α M : Type*} [Zero M] [One M]

section Preorder
variable [Preorder M] [ZeroLEOneClass M] {s : Set α}

@[simp] lemma indicator_one_nonneg : 0 ≤ s.indicator (fun _ ↦ (1 : M)) :=
  indicator_nonneg (by simp)

@[simp] lemma indicator_one_apply_nonneg {a : α} :
    0 ≤ s.indicator (fun _ ↦ (1 : M)) a := indicator_one_nonneg a

end Preorder

section PartialOrder
variable [PartialOrder M] [ZeroLEOneClass M] [NeZero (1 : M)] {s : Set α}

@[simp]
lemma indicator_one_pos [Nontrivial M] : 0 < s.indicator (fun _ ↦ (1 : M)) ↔ s.Nonempty := by
  classical
  simp [indicator_apply, lt_iff_le_not_ge, Pi.le_def, apply_ite, ite_apply, Set.Nonempty,
    zero_lt_one.not_ge]

end PartialOrder
end Set
