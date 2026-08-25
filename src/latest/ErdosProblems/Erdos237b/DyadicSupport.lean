import ErdosProblems.Erdos237b.DyadicLattice
import ErdosProblems.Erdos237b.FiniteBoxWeights
import ErdosProblems.Erdos237b.SupportedWeights

/-!
# Supported dyadic Y-weights

The boxes use half the exponent of the divisor cutoff. This leaves strict
room in the product-support inequality while preserving an unbounded
variational ratio. Distinct dyadic configurations give disjoint shells.
-/

namespace Erdos237b

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

theorem radius_mono_exponent_of_two_le {a b : ℝ} (hab : a ≤ b) {N : ℕ} (hN : 2 ≤ N) :
    engelsmaMaynardRadius a N ≤ engelsmaMaynardRadius b N := by
  unfold engelsmaMaynardRadius maynardDivisorCutoff
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N - 1 by omega)) hab

theorem dyadicUpper_le_length_of_lt {L k : ℕ} {i j : Fin L} (hij : i < j) :
    dyadicUpper L k i ≤ dyadicLength L k j := by
  unfold dyadicUpper dyadicLength
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) hij

theorem coordinateShell_disjoint_of_le {W a b c d : ℕ} (hbc : b ≤ c) :
    Disjoint (squarefreeCoprimeCoordinateShell W a b)
      (squarefreeCoprimeCoordinateShell W c d) := by
  apply disjoint_left.mpr
  intro u hu hv
  exact (mem_sdiff.mp hv).2
    (squarefreeCoprimeCoordinateSupport_subset hbc (mem_sdiff.mp hu).1)

noncomputable def dyadicTupleShell {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (alpha : ℝ) (N : ℕ) (x : Fin k → Fin L) : Finset (H → ℕ) :=
  engelsmaFractionalTupleShell H (alpha / 2)
    (fun h => dyadicLength L k (x (e h)))
    (fun h => dyadicUpper L k (x (e h))) N

theorem dyadicTupleShell_disjoint {H : Finset ℕ} {L k N : ℕ}
    (e : H ≃ Fin k) {alpha : ℝ} (halpha : 0 < alpha) (hN : 2 ≤ N)
    {x y : Fin k → Fin L} (hxy : x ≠ y) :
    Disjoint (dyadicTupleShell e alpha N x) (dyadicTupleShell e alpha N y) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  let h : H := e.symm i
  have hh : x (e h) ≠ y (e h) := by simpa [h] using hi
  unfold dyadicTupleShell engelsmaFractionalTupleShell squarefreeCoprimeTupleShell
  apply Fintype.piFinset_disjoint_of_disjoint (a := h)
  rcases lt_or_gt_of_ne hh with hlt | hlt
  · apply coordinateShell_disjoint_of_le
    exact radius_mono_exponent_of_two_le
      (mul_le_mul_of_nonneg_left (dyadicUpper_le_length_of_lt hlt) (by positivity)) hN
  · apply Disjoint.symm
    apply coordinateShell_disjoint_of_le
    exact radius_mono_exponent_of_two_le
      (mul_le_mul_of_nonneg_left (dyadicUpper_le_length_of_lt hlt) (by positivity)) hN

theorem eventually_dyadicTupleShell_subset {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) {alpha : ℝ} (halpha : 0 < alpha)
    {x : Fin k → Fin L} (hx : x ∈ dyadicGoodBoxes L k) :
    ∀ᶠ N : ℕ in atTop, dyadicTupleShell e alpha N x ⊆
      preSievedSimplexTupleSupport H (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N) := by
  have hsum : (∑ h : H, dyadicUpper L k (x (e h)) / 2) < 1 := by
    rw [← sum_div, e.sum_comp (fun i => dyadicUpper L k (x i))]
    have hgood := (mem_filter.mp hx).2
    linarith
  have hsub := eventually_engelsmaFractionalTupleBox_subset_preSievedSimplexTupleSupport
    halpha (fun h => dyadicUpper L k (x (e h)) / 2)
    (fun h => div_nonneg (dyadicUpper_nonneg _ _ _) (by norm_num)) hsum
  filter_upwards [hsub] with N hsubN
  intro u hu
  apply hsubN
  rw [engelsmaFractionalTupleBox, squarefreeCoprimeTupleBox, Fintype.mem_piFinset]
  have hu' := Fintype.mem_piFinset.mp hu
  intro h
  have huh := (mem_sdiff.mp (hu' h)).1
  convert huh using 1
  congr 2
  ring

noncomputable def dyadicRawWeight {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (alpha : ℝ) (N : ℕ) : (H → ℕ) → ℝ :=
  finiteBoxWeight (dyadicGoodBoxes L k) (dyadicTupleShell e alpha N)
    (fun x => ∏ i, dyadicHeight L (x i))

noncomputable def dyadicWeightBound (L k : ℕ) : ℝ :=
  ∑ x ∈ dyadicGoodBoxes L k, |∏ i, dyadicHeight L (x i)|

theorem dyadicWeightBound_nonneg (L k : ℕ) : 0 ≤ dyadicWeightBound L k :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem abs_dyadicRawWeight_le {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (alpha : ℝ) (N : ℕ) (r : H → ℕ) :
    |dyadicRawWeight (L := L) e alpha N r| ≤ dyadicWeightBound L k :=
  abs_finiteBoxWeight_le _ _ _ _

noncomputable def dyadicY {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (alpha : ℝ) (N : ℕ) : (H → ℕ) → ℝ :=
  restrictToMaynardSupport H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
    (dyadicRawWeight (L := L) e alpha N)

theorem dyadicRawWeight_nonneg {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (alpha : ℝ) (N : ℕ) (r : H → ℕ) :
    0 ≤ dyadicRawWeight (L := L) e alpha N r := by
  apply finiteBoxWeight_nonneg
  intro x _
  unfold dyadicHeight
  positivity

theorem dyadicY_nonneg {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (alpha : ℝ) (N : ℕ) (r : H → ℕ) :
    0 ≤ dyadicY (L := L) e alpha N r := by
  unfold dyadicY restrictToMaynardSupport
  split_ifs
  · exact dyadicRawWeight_nonneg e alpha N r
  · rfl

theorem coefficient_le_dyadicRawWeight {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (alpha : ℝ) (N : ℕ) {x : Fin k → Fin L}
    (hx : x ∈ dyadicGoodBoxes L k) {r : H → ℕ} (hr : r ∈ dyadicTupleShell e alpha N x) :
    (∏ i, dyadicHeight L (x i)) ≤ dyadicRawWeight (L := L) e alpha N r := by
  classical
  have hp : ∀ x : Fin k → Fin L, 0 ≤ ∏ i, dyadicHeight L (x i) := by
    intro x
    unfold dyadicHeight
    positivity
  unfold dyadicRawWeight finiteBoxWeight
  have h := single_le_sum (s := dyadicGoodBoxes L k)
    (f := fun x => if r ∈ dyadicTupleShell e alpha N x then ∏ i, dyadicHeight L (x i) else 0)
    (fun x _ => by
      split_ifs
      · exact hp x
      · rfl) hx
  simpa only [if_pos hr] using h

theorem dyadicY_supported {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (alpha : ℝ) (N : ℕ) :
    IsSupportedMaynardY H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
      (dyadicY (L := L) e alpha N) :=
  restrictToMaynardSupport_supported _ _ _ _

theorem abs_dyadicY_le {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (alpha : ℝ) (N : ℕ) (r : H → ℕ) :
    |dyadicY (L := L) e alpha N r| ≤ dyadicWeightBound L k :=
  abs_restrictToMaynardSupport_le _ _ (dyadicWeightBound_nonneg L k)
    (abs_dyadicRawWeight_le e alpha N) r

end Erdos237b
