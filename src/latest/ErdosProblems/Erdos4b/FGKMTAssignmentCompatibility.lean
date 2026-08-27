/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentDivisibility

/-!
# Compatible prime assignments and their literal CRT density

For distinct roots, two divisor assignments can hold simultaneously
exactly when they never assign a prime to different coordinates.
Their merged assignment has density the reciprocal of its prime product.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α] [DecidableEq ι]

def AssignmentCompatible (d e : α → Option ι) : Prop :=
  ∀ q i j, d q = some i → e q = some j → i = j

def mergeAssignment (d e : α → Option ι) (q : α) : Option ι :=
  match d q with
  | none => e q
  | some i => some i

omit [Fintype α] [DecidableEq ι] in
theorem mergeAssignment_some_iff (d e : α → Option ι) (q : α) (i : ι) :
    mergeAssignment d e q = some i ↔ d q = some i ∨ (d q = none ∧ e q = some i) := by
  cases hd : d q <;> simp [mergeAssignment, hd]

omit [Fintype α] [DecidableEq ι] in
theorem mergeAssignment_of_left {d e : α → Option ι} {q : α} {i : ι}
    (hd : d q = some i) : mergeAssignment d e q = some i := by
  simp only [mergeAssignment, hd]

omit [Fintype α] [DecidableEq ι] in
theorem mergeAssignment_of_right {d e : α → Option ι}
    (hc : AssignmentCompatible d e) {q : α} {i : ι} (he : e q = some i) :
    mergeAssignment d e q = some i := by
  cases hd : d q with
  | none => simp only [mergeAssignment, hd, he]
  | some j => simp only [mergeAssignment, hd, hc q j i hd he]

theorem assignmentDivisorPair_iff_merged {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (a : ι → ℤ)
    (hroot : ∀ q i j, (p q : ℤ) ∣ a i - a j → i = j)
    (d e : α → Option ι) (n : ℤ) :
    ((∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ n + a i) ∧
      (∀ i, (assignmentPrimeTuple p e i : ℤ) ∣ n + a i)) ↔
      AssignmentCompatible d e ∧
        ∀ i, (assignmentPrimeTuple p (mergeAssignment d e) i : ℤ) ∣ n + a i := by
  simp only [assignmentDivisorCondition_iff_local hp hinj]
  constructor
  · rintro ⟨hd, he⟩
    refine ⟨?_, ?_⟩
    · intro q i j hdi hej
      apply hroot q i j
      have hh := dvd_sub (hd q i hdi) (he q j hej)
      simpa only [add_sub_add_left_eq_sub] using hh
    · intro q i hqi
      rcases (mergeAssignment_some_iff d e q i).mp hqi with hdi | ⟨_, hei⟩
      · exact hd q i hdi
      · exact he q i hei
  · rintro ⟨hc, hm⟩
    exact ⟨fun q i hdi => hm q i (mergeAssignment_of_left hdi),
      fun q i hei => hm q i (mergeAssignment_of_right hc hei)⟩

open scoped Classical in
theorem assignmentCrtKernel_eq_merged (p : α → ℕ) (d e : α → Option ι) :
    assignmentCrtKernel (fun q => (p q : ℝ)) d e =
      if AssignmentCompatible d e then
        1 / (assignmentPrimeProduct p (mergeAssignment d e) : ℝ) else 0 := by
  classical
  by_cases hc : AssignmentCompatible d e
  · rw [if_pos hc]
    unfold assignmentCrtKernel assignmentPrimeProduct
    rw [Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro q _hq
    cases hd : d q with
    | none => cases he : e q <;> simp [localCrtDensity, mergeAssignment, hd, he]
    | some i =>
      cases he : e q with
      | none => simp [localCrtDensity, mergeAssignment, hd]
      | some j => simp [localCrtDensity, mergeAssignment, hd, hc q i j hd he]
  · rw [if_neg hc]
    unfold AssignmentCompatible at hc
    push Not at hc
    obtain ⟨q, i, j, hd, he, hij⟩ := hc
    exact Finset.prod_eq_zero (Finset.mem_univ q)
      (by simp only [hd, he, localCrtDensity, if_neg hij])

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentDivisorPair_iff_merged
#print axioms Erdos4b.FGKMT.assignmentCrtKernel_eq_merged
