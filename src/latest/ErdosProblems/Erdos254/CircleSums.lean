/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Basic

namespace Erdos254

open Filter Set
open scoped BigOperators Topology

/-- Stop a finite sum the first time it reaches a specified threshold. -/
lemma exists_subset_sum_between {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {t M : ℝ} (ht : 0 < t) (hM : ∀ i ∈ s, f i ≤ M) (hs : t ≤ ∑ i ∈ s, f i) :
    ∃ F ⊆ s, t ≤ ∑ i ∈ F, f i ∧ (∑ i ∈ F, f i) ≤ t + M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty] at hs; linarith
  | @insert a s ha ih =>
      by_cases htail : t ≤ ∑ i ∈ s, f i
      · obtain ⟨F, hF, hlo, hhi⟩ := ih
          (fun i hi ↦ hM i (Finset.mem_insert_of_mem hi)) htail
        exact ⟨F, hF.trans (Finset.subset_insert _ _), hlo, hhi⟩
      · refine ⟨insert a s, Finset.Subset.refl _, hs, ?_⟩
        rw [Finset.sum_insert ha]
        have := hM a (Finset.mem_insert_self _ _)
        linarith

lemma coe_sum_circle {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : UnitAddCircle) = ∑ i ∈ s, (f i : UnitAddCircle) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, AddCircle.coe_add, ih]

private lemma real_sum_lt_quarter {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, f i ≤ 1 / 4)
    (hsmall : ∀ F ⊆ s, distToNearestInt (∑ i ∈ F, f i) < 1 / 4) :
    (∑ i ∈ s, f i) < 1 / 4 := by
  by_contra h
  obtain ⟨F, hF, hlo, hhi⟩ := exists_subset_sum_between s f (by norm_num : (0 : ℝ) < 1 / 4)
    hf (le_of_not_gt h)
  have habs : |∑ i ∈ F, f i| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_of_nonneg (by linarith), abs_one]
    linarith
  have heq : distToNearestInt (∑ i ∈ F, f i) = ∑ i ∈ F, f i := by
    rw [distToNearestInt, (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr habs,
      abs_of_nonneg (by linarith)]
  have := hsmall F hF
  rw [heq] at this
  linarith

/-- If all subset sums stay within distance `1/4` of zero on the circle,
the sum of the individual distances is less than `1/2`. -/
theorem sum_norm_lt_half_of_subset_sums_small {ι : Type*} (s : Finset ι)
    (f : ι → UnitAddCircle)
    (hsmall : ∀ F ⊆ s, ‖∑ i ∈ F, f i‖ < 1 / 4) :
    (∑ i ∈ s, ‖f i‖) < 1 / 2 := by
  classical
  let r : ι → ℝ := fun i ↦ AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (f i)
  have hcoe : ∀ i, ((r i : ℝ) : UnitAddCircle) = f i := fun _ ↦ AddCircle.coe_equivIco
  have hnorm : ∀ i, ‖f i‖ = |r i| := by
    intro i
    have hb := (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (f i)).2
    have hr : |r i| ≤ |(1 : ℝ)| / 2 := by
      rw [abs_le, abs_one]
      dsimp [r]
      constructor <;> linarith [hb.1, hb.2]
    rw [← hcoe i]
    exact (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr hr
  have hterm : ∀ i ∈ s, |r i| < 1 / 4 := by
    intro i hi
    rw [← hnorm]
    simpa only [Finset.sum_singleton] using hsmall {i} (Finset.singleton_subset_iff.mpr hi)
  have hreal : ∀ F ⊆ s, distToNearestInt (∑ i ∈ F, r i) < 1 / 4 := by
    intro F hF
    simpa only [distToNearestInt, coe_sum_circle, hcoe] using hsmall F hF
  let P := s.filter (fun i ↦ 0 ≤ r i)
  let Q := s.filter (fun i ↦ ¬0 ≤ r i)
  have hP : (∑ i ∈ P, r i) < 1 / 4 := by
    apply real_sum_lt_quarter P r
    · intro i hi
      exact (le_abs_self _).trans (hterm i (Finset.mem_filter.mp hi).1).le
    · intro F hF
      exact hreal F (hF.trans (Finset.filter_subset _ _))
  have hQ : (∑ i ∈ Q, -r i) < 1 / 4 := by
    apply real_sum_lt_quarter Q (fun i ↦ -r i)
    · intro i hi
      exact (neg_le_abs _).trans (hterm i (Finset.mem_filter.mp hi).1).le
    · intro F hF
      have := hreal F (hF.trans (Finset.filter_subset _ _))
      simpa only [Finset.sum_neg_distrib, distToNearestInt, AddCircle.coe_neg, norm_neg] using this
  have hPsum : (∑ i ∈ P, |r i|) = ∑ i ∈ P, r i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_of_nonneg (Finset.mem_filter.mp hi).2
  have hQsum : (∑ i ∈ Q, |r i|) = ∑ i ∈ Q, -r i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hi).2)
  have hsplit : (∑ i ∈ P, |r i|) + (∑ i ∈ Q, |r i|) = ∑ i ∈ s, |r i| :=
    Finset.sum_filter_add_sum_filter_not s (fun i ↦ 0 ≤ r i) (fun i ↦ |r i|)
  simp_rw [hnorm]
  rw [hPsum, hQsum] at hsplit
  linarith

end Erdos254
