/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma612

/-!
# Residual matching allocation after an exceptional saving

This is the finite weight argument in ER-large and ER-small of the
mathematical writeup. It constructs the residual matchings rather than
assuming that their degree margins already give an embedding.
-/

open scoped BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoExceptionalResidualAllocation

open Finset

variable {E : Type*} [DecidableEq E]

/-- Order-free first crossing, including the zero target and empty set. -/
theorem exists_first_threshold_subset (M : Finset E) (w : E → ℝ)
    (target cap : ℝ) (htarget : 0 ≤ target) (hcap : 0 < cap)
    (hbound : ∀ e ∈ M, w e ≤ cap) (htotal : target ≤ ∑ e ∈ M, w e) :
    ∃ P ⊆ M, target ≤ ∑ e ∈ P, w e ∧ (∑ e ∈ P, w e) < target + cap := by
  induction M using Finset.induction_on generalizing target with
  | empty =>
      refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
      · exact htotal
      · simpa only [Finset.sum_empty] using (add_pos_of_nonneg_of_pos htarget hcap)
  | @insert e M he ih =>
      by_cases hzero : target ≤ 0
      · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
        · simpa only [Finset.sum_empty] using hzero
        · simpa only [Finset.sum_empty] using (add_pos_of_nonneg_of_pos htarget hcap)
      have htpos : 0 < target := lt_of_not_ge hzero
      by_cases hx : target ≤ w e
      · refine ⟨{e}, Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _), ?_, ?_⟩
        · simpa only [Finset.sum_singleton] using hx
        · simp only [Finset.sum_singleton]
          linarith only [hbound e (Finset.mem_insert_self _ _), htpos]
      have hremaining : target - w e ≤ ∑ x ∈ M, w x := by
        rw [Finset.sum_insert he] at htotal
        linarith only [htotal]
      obtain ⟨P, hPM, hlo, hup⟩ := ih (target - w e)
        (sub_nonneg.mpr (le_of_not_ge hx))
        (fun x hxM => hbound x (Finset.mem_insert_of_mem hxM)) hremaining
      have heP : e ∉ P := fun h => he (hPM h)
      refine ⟨insert e P, Finset.insert_subset_insert e hPM, ?_, ?_⟩
      · rw [Finset.sum_insert heP]
        linarith only [hlo]
      · rw [Finset.sum_insert heP]
        linarith only [hup]

/-- The source saving pays two residual reserves, one crossing overshoot,
the total degree defect, and the raw-row discrepancy. -/
theorem exists_large_residual_allocation
    (M E0 : Finset E) (a b : E → ℝ)
    (n delta saving f0 f1 fb reserve cap discrepancy : ℝ)
    (hE0 : E0 ⊆ M) (hcap : 0 < cap)
    (hbound : ∀ e ∈ M, a e ≤ cap)
    (hf1 : 0 ≤ f1) (hfb : 0 ≤ fb) (hreserve : 0 ≤ reserve)
    (hdiscrepancy : 0 ≤ discrepancy)
    (htotal : (1 - delta) * n ≤ ∑ e ∈ M, a e)
    (hforest : f0 + f1 + fb ≤ n)
    (hsaving : (∑ e ∈ E0, a e) + saving ≤ f0)
    (hmargin : delta * n + 2 * reserve + cap + discrepancy ≤ saving)
    (hrows : ∀ R ⊆ M, (∑ e ∈ R, a e) - (∑ e ∈ R, b e) ≤ discrepancy) :
    ∃ E1 Eb : Finset E,
      E1 ⊆ M \ E0 ∧ Eb ⊆ M \ E0 ∧ Disjoint E1 Eb ∧ E1 ∪ Eb = M \ E0 ∧
      f1 + reserve ≤ ∑ e ∈ E1, a e ∧ fb + reserve < ∑ e ∈ Eb, b e := by
  have hsum : (∑ e ∈ M \ E0, a e) + (∑ e ∈ E0, a e) = ∑ e ∈ M, a e :=
    Finset.sum_sdiff hE0
  have htarget : f1 + reserve ≤ ∑ e ∈ M \ E0, a e := by
    nlinarith only [hsum, htotal, hforest, hsaving, hmargin, hcap, hfb, hreserve, hdiscrepancy]
  obtain ⟨E1, hE1, hlo, hup⟩ := exists_first_threshold_subset (M \ E0) a (f1 + reserve) cap
    (add_nonneg hf1 hreserve) hcap (fun e he => hbound e (Finset.mem_sdiff.mp he).1) htarget
  let Eb := (M \ E0) \ E1
  have hEb : Eb ⊆ M \ E0 := Finset.sdiff_subset
  have hsplit : (∑ e ∈ Eb, a e) + (∑ e ∈ E1, a e) = ∑ e ∈ M \ E0, a e :=
    Finset.sum_sdiff hE1
  have hdisjoint : Disjoint E1 Eb := by
    rw [Finset.disjoint_left]
    intro e he1 heb
    exact (Finset.mem_sdiff.mp heb).2 he1
  refine ⟨E1, Eb, hE1, hEb, hdisjoint, ?_, hlo, ?_⟩
  · exact Finset.union_sdiff_of_subset hE1
  · have hrow := hrows Eb (hEb.trans Finset.sdiff_subset)
    nlinarith only [hrow, hsplit, hsum, htotal, hforest, hsaving, hmargin, hup]

/-- In the small opposite-family case the previously selected matching is
kept literally, and all other available edges serve the same-side residual. -/
theorem small_residual_budget
    (M E0 Eb : Finset E) (a : E → ℝ)
    (n delta saving f0 f1 fb reserve cost : ℝ)
    (hE0 : E0 ⊆ M) (hEb : Eb ⊆ M) (hdisjoint : Disjoint E0 Eb)
    (hfb : 0 ≤ fb)
    (htotal : (1 - delta) * n ≤ ∑ e ∈ M, a e)
    (hforest : f0 + f1 + fb ≤ n)
    (hsaving : (∑ e ∈ E0, a e) + saving ≤ f0)
    (hcost : (∑ e ∈ Eb, a e) ≤ cost)
    (hmargin : delta * n + cost + reserve ≤ saving) :
    f1 + reserve ≤ ∑ e ∈ M \ (E0 ∪ Eb), a e := by
  have hsum := Finset.sum_sdiff (Finset.union_subset hE0 hEb) (f := a)
  rw [Finset.sum_union hdisjoint] at hsum
  nlinarith only [hsum, htotal, hforest, hsaving, hcost, hmargin, hfb]

end Erdos547b.ZhaoExceptionalResidualAllocation

#print axioms Erdos547b.ZhaoExceptionalResidualAllocation.exists_first_threshold_subset
#print axioms Erdos547b.ZhaoExceptionalResidualAllocation.exists_large_residual_allocation
#print axioms Erdos547b.ZhaoExceptionalResidualAllocation.small_residual_budget
