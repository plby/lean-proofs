/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsoluteKernel

/-!
# Injective coding of contributing pairs by common and moved assignments

A moved label remembers its ordered pair of coordinates. The code has a
left inverse on every same-support pair. Enlarging its image to the
whole product space is therefore a valid upper bound for nonnegative
weights and removes the common/moved disjointness constraint.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι]

def movedPairAssignment (r s : α → Option ι) : α → Option (ι × ι) :=
  fun q => if r q = s q then none else
    match r q, s q with
    | some i, some j => some (i, j)
    | _, _ => none

def assignmentPairCode (rs : (α → Option ι) × (α → Option ι)) :
    (α → Option ι) × (α → Option (ι × ι)) :=
  (commonAssignment rs.1 rs.2, movedPairAssignment rs.1 rs.2)

def restoreAssignmentPair (uv : (α → Option ι) × (α → Option (ι × ι))) :
    (α → Option ι) × (α → Option ι) :=
  (fun q => match uv.1 q with
    | some i => some i
    | none => (uv.2 q).map Prod.fst,
   fun q => match uv.1 q with
    | some i => some i
    | none => (uv.2 q).map Prod.snd)

omit [DecidableEq α] [Fintype α] [Fintype ι] in
theorem restoreAssignmentPair_code {r s : α → Option ι} (h : SamePrimeSupport r s) :
    restoreAssignmentPair (assignmentPairCode (r, s)) = (r, s) := by
  apply Prod.ext <;> funext q <;>
    have hq := h q
  all_goals
    cases hr : r q <;> cases hs : s q <;>
      simp_all [restoreAssignmentPair, assignmentPairCode, commonAssignment, movedPairAssignment]
  all_goals split_ifs <;> simp_all

omit [DecidableEq α] [Fintype α] [Fintype ι] in
theorem assignmentPairCode_injective_on_support
    {r s r' s' : α → Option ι} (h : SamePrimeSupport r s) (h' : SamePrimeSupport r' s')
    (heq : assignmentPairCode (r, s) = assignmentPairCode (r', s')) : (r, s) = (r', s') := by
  have hh := congrArg restoreAssignmentPair heq
  simpa only [restoreAssignmentPair_code h, restoreAssignmentPair_code h'] using hh

omit [DecidableEq α] [Fintype α] [Fintype ι] in
theorem movedPairAssignment_none_iff {r s : α → Option ι} (h : SamePrimeSupport r s)
    (q : α) : movedPairAssignment r s q = none ↔ movedAssignment r s q = none := by
  have hq := h q
  cases hr : r q <;> cases hs : s q <;> simp_all [movedPairAssignment, movedAssignment]

omit [DecidableEq α] [Fintype ι] in
theorem movedPairAssignment_scalarWeight (a : α → ℝ) {r s : α → Option ι}
    (h : SamePrimeSupport r s) :
    assignmentScalarWeight a (movedPairAssignment r s) =
      assignmentScalarWeight a (movedAssignment r s) := by
  apply Finset.prod_congr rfl
  intro q _hq
  simp only [movedPairAssignment_none_iff h q]

omit [DecidableEq α] [Fintype ι] in
theorem movedPairAssignment_primeProduct (p : α → ℕ) {r s : α → Option ι}
    (h : SamePrimeSupport r s) :
    assignmentPrimeProduct p (movedPairAssignment r s) =
      assignmentPrimeProduct p (movedAssignment r s) := by
  apply Finset.prod_congr rfl
  intro q _hq
  simp only [movedPairAssignment_none_iff h q]

open scoped Classical in
theorem sum_supported_pairCode_le
    (J : ((α → Option ι) × (α → Option (ι × ι))) → ℝ) (hJ : ∀ uv, 0 ≤ J uv) :
    (∑ r : α → Option ι, ∑ s : α → Option ι,
      if SamePrimeSupport r s then J (assignmentPairCode (r, s)) else 0) ≤
        ∑ u : α → Option ι, ∑ v : α → Option (ι × ι), J (u, v) := by
  classical
  let S : Finset ((α → Option ι) × (α → Option ι)) :=
    Finset.univ.filter (fun rs => SamePrimeSupport rs.1 rs.2)
  have hinj : Set.InjOn assignmentPairCode
      (↑S : Set ((α → Option ι) × (α → Option ι))) := by
    intro rs hrs tt htt heq
    exact assignmentPairCode_injective_on_support (Finset.mem_filter.mp hrs).2
      (Finset.mem_filter.mp htt).2 heq
  calc
    _ = ∑ rs ∈ S, J (assignmentPairCode rs) := by
      simp only [S, Finset.sum_filter, Fintype.sum_prod_type]
    _ = ∑ uv ∈ S.image assignmentPairCode, J uv := (Finset.sum_image hinj).symm
    _ ≤ ∑ uv, J uv := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun uv _huv _hnot => hJ uv)
    _ = _ := Fintype.sum_prod_type _

open scoped Classical in
theorem sum_common_moved_weight_le_product
    (H : (α → Option ι) → ℝ) (hH : ∀ u, 0 ≤ H u)
    (b : α → ℝ) (hb : ∀ q, 0 ≤ b q) (p : α → ℕ) :
    (∑ r : α → Option ι, ∑ s : α → Option ι,
      if SamePrimeSupport r s then
        H (commonAssignment r s) * assignmentScalarWeight b (movedAssignment r s) *
          Real.log (assignmentPrimeProduct p (movedAssignment r s)) else 0) ≤
      (∑ u, H u) * ∑ v : α → Option (ι × ι),
        assignmentScalarWeight b v * Real.log (assignmentPrimeProduct p v) := by
  classical
  let J := fun uv : (α → Option ι) × (α → Option (ι × ι)) =>
    H uv.1 * (assignmentScalarWeight b uv.2 * Real.log (assignmentPrimeProduct p uv.2))
  have hJ : ∀ uv, 0 ≤ J uv := fun uv =>
    mul_nonneg (hH uv.1) (mul_nonneg (assignmentScalarWeight_nonneg hb uv.2)
      (Real.log_natCast_nonneg _))
  calc
    _ = ∑ r : α → Option ι, ∑ s : α → Option ι,
        if SamePrimeSupport r s then J (assignmentPairCode (r, s)) else 0 := by
      apply Finset.sum_congr rfl
      intro r _hr
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases h : SamePrimeSupport r s
      · simp only [if_pos h, J, assignmentPairCode,
          movedPairAssignment_scalarWeight b h, movedPairAssignment_primeProduct p h, mul_assoc]
      · simp only [if_neg h]
    _ ≤ ∑ u : α → Option ι, ∑ v : α → Option (ι × ι), J (u, v) :=
      sum_supported_pairCode_le J hJ
    _ = _ := by
      simp only [J]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.restoreAssignmentPair_code
#print axioms Erdos4b.FGKMT.sum_common_moved_weight_le_product
