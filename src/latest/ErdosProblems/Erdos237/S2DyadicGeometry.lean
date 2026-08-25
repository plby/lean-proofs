import ErdosProblems.Erdos237.S2MixedDyadic
import ErdosProblems.Erdos237.DyadicSupport

/-! Geometry and disjointness of the extra-coordinate dyadic boxes. -/

namespace Erdos237

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def s2DyadicBoxes {H K : Finset ℕ} (q : K ≃ Option H) (m : H)
    (L k : ℕ) : Finset (K → Fin L) :=
  univ.filter fun x => (∑ i, s2MixedCost q m L k i (x i)) ≤ 1 / 2

def s2ConfigLeft {H K : Finset ℕ} (q : K ≃ Option H) {L : ℕ}
    (x : K → Fin L) : H → Fin L := fun h => x (q.symm (some h))

noncomputable def s2ConfigRight {H K : Finset ℕ} (q : K ≃ Option H) (m : H) {L : ℕ}
    (x : K → Fin L) : H → Fin L :=
  fun h => if h = m then x (q.symm none) else s2ConfigLeft q x h

theorem sum_s2Outer_value {H K : Finset ℕ} (q : K ≃ Option H) (m : H) (f : K → ℝ) :
    (∑ i : K, if s2IsInner q m i then 0 else f i) =
      ∑ h ∈ univ.erase m, f (q.symm (some h)) := by
  classical
  rw [sum_extraCoordinate q]
  simp only [s2IsInner, Equiv.apply_symm_apply, true_or, ↓reduceIte,
    Option.some_ne_none, false_or, Option.some.injEq, zero_add]
  rw [← sum_erase_add _ _ (mem_univ m)]
  simp only [↓reduceIte, add_zero]
  apply sum_congr rfl
  intro h hh
  exact if_neg (mem_erase.mp hh).1

theorem sum_s2MixedCost_eq {H K : Finset ℕ} (q : K ≃ Option H) (m : H)
    {L k : ℕ} (x : K → Fin L) :
    (∑ i, s2MixedCost q m L k i (x i)) =
      ∑ h ∈ univ.erase m, dyadicUpper L k (s2ConfigLeft q x h) :=
  sum_s2Outer_value q m (fun i => dyadicUpper L k (x i))

theorem sum_configLeft_upper {H K : Finset ℕ} (q : K ≃ Option H) (m : H)
    {L k : ℕ} (x : K → Fin L) :
    (∑ h, dyadicUpper L k (s2ConfigLeft q x h)) =
      dyadicUpper L k (x (q.symm (some m))) + ∑ i, s2MixedCost q m L k i (x i) := by
  rw [sum_s2MixedCost_eq]
  exact (add_sum_erase _ _ (mem_univ m)).symm

theorem sum_configRight_upper {H K : Finset ℕ} (q : K ≃ Option H) (m : H)
    {L k : ℕ} (x : K → Fin L) :
    (∑ h, dyadicUpper L k (s2ConfigRight q m x h)) =
      dyadicUpper L k (x (q.symm none)) + ∑ i, s2MixedCost q m L k i (x i) := by
  classical
  rw [sum_s2MixedCost_eq, ← add_sum_erase _ _ (mem_univ m)]
  simp only [s2ConfigRight, ↓reduceIte]
  congr 1
  apply sum_congr rfl
  intro h hh
  rw [if_neg (mem_erase.mp hh).1]

theorem s2DyadicBoxes_project_good {H K : Finset ℕ} {L k : ℕ}
    (q : K ≃ Option H) (m : H) (e : H ≃ Fin k) (hL : 0 < L) (hk : 2 ^ L ≤ k)
    {x : K → Fin L} (hx : x ∈ s2DyadicBoxes q m L k) :
    (s2ConfigLeft q x ∘ e.symm) ∈ dyadicGoodBoxes L k ∧
      (s2ConfigRight q m x ∘ e.symm) ∈ dyadicGoodBoxes L k := by
  have hc := (mem_filter.mp hx).2
  have hlo := dyadicUpper_le_half hL hk (x (q.symm (some m)))
  have hhi := dyadicUpper_le_half hL hk (x (q.symm none))
  constructor
  · rw [dyadicGoodBoxes, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    change (∑ i, (fun h => dyadicUpper L k (s2ConfigLeft q x h)) (e.symm i)) ≤ 1
    rw [e.symm.sum_comp (fun h => dyadicUpper L k (s2ConfigLeft q x h)),
      sum_configLeft_upper q m]
    linarith
  · rw [dyadicGoodBoxes, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    change (∑ i, (fun h => dyadicUpper L k (s2ConfigRight q m x h)) (e.symm i)) ≤ 1
    rw [e.symm.sum_comp (fun h => dyadicUpper L k (s2ConfigRight q m x h)),
      sum_configRight_upper q m]
    linarith

theorem s2DyadicBoxes_sum_upper_lt_one {H K : Finset ℕ} {L k : ℕ}
    (q : K ≃ Option H) (m : H) (hL : 0 < L) (hk : 2 ^ L ≤ k)
    {x : K → Fin L} (hx : x ∈ s2DyadicBoxes q m L k) :
    (∑ i : K, dyadicUpper L k (x i) / 2) < 1 := by
  rw [← sum_div, sum_extraCoordinate q]
  change (dyadicUpper L k (x (q.symm none)) +
    ∑ h, dyadicUpper L k (s2ConfigLeft q x h)) / 2 < 1
  rw [sum_configLeft_upper q m]
  have hc := (mem_filter.mp hx).2
  have hlo := dyadicUpper_le_half hL hk (x (q.symm (some m)))
  have hhi := dyadicUpper_le_half hL hk (x (q.symm none))
  linarith

theorem s2DyadicShells_disjoint {K : Finset ℕ} {L k N : ℕ}
    {alpha : ℝ} (halpha : 0 < alpha) (hN : 2 ≤ N) {x y : K → Fin L} (hxy : x ≠ y) :
    Disjoint
      (engelsmaFractionalTupleShell K alpha (fun i => dyadicLength L k (x i) / 2)
        (fun i => dyadicUpper L k (x i) / 2) N)
      (engelsmaFractionalTupleShell K alpha (fun i => dyadicLength L k (y i) / 2)
        (fun i => dyadicUpper L k (y i) / 2) N) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  unfold engelsmaFractionalTupleShell squarefreeCoprimeTupleShell
  apply Fintype.piFinset_disjoint_of_disjoint (a := i)
  rcases lt_or_gt_of_ne hi with hlt | hlt
  · apply coordinateShell_disjoint_of_le
    apply radius_mono_exponent_of_two_le ?_ hN
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (dyadicUpper_le_length_of_lt hlt) (by norm_num)) halpha.le
  · apply Disjoint.symm
    apply coordinateShell_disjoint_of_le
    apply radius_mono_exponent_of_two_le ?_ hN
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (dyadicUpper_le_length_of_lt hlt) (by norm_num)) halpha.le

theorem s2DyadicShell_projects {H K : Finset ℕ} {L k : ℕ}
    (q : K ≃ Option H) (m : H) (e : H ≃ Fin k) (alpha : ℝ) (N : ℕ)
    {x : K → Fin L} {z : K → ℕ}
    (hz : z ∈ engelsmaFractionalTupleShell K alpha
      (fun i => dyadicLength L k (x i) / 2) (fun i => dyadicUpper L k (x i) / 2) N) :
    s2LiftLeft q z ∈ dyadicTupleShell e alpha N (s2ConfigLeft q x ∘ e.symm) ∧
      s2LiftRight q m z ∈ dyadicTupleShell e alpha N (s2ConfigRight q m x ∘ e.symm) := by
  classical
  have hcoord := Fintype.mem_piFinset.mp hz
  have hm (t : ℝ) : alpha / 2 * t = alpha * (t / 2) := by ring
  constructor
  · rw [dyadicTupleShell, engelsmaFractionalTupleShell, squarefreeCoprimeTupleShell,
      Fintype.mem_piFinset]
    intro h
    simpa [Function.comp_apply, s2LiftLeft, s2ConfigLeft, hm] using hcoord (q.symm (some h))
  · rw [dyadicTupleShell, engelsmaFractionalTupleShell, squarefreeCoprimeTupleShell,
      Fintype.mem_piFinset]
    intro h
    by_cases hh : h = m
    · subst h
      simpa [Function.comp_apply, s2LiftRight, s2ConfigRight, hm] using hcoord (q.symm none)
    · simpa [Function.comp_apply, s2LiftRight, s2LiftLeft, s2ConfigRight, s2ConfigLeft, hh, hm]
        using hcoord (q.symm (some h))

end Erdos237
