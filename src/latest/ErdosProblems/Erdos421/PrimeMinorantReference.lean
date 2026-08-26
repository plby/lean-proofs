import ErdosProblems.Erdos421.ReferenceRoughBounds
import ErdosProblems.Erdos421.PrimeMinorantTransfer

/-! # An unconditional positive lower bound for the actual reference prime minorant -/

namespace Erdos421

open Filter Topology

theorem intermediatePrimeMinorant_reference_lower {L : ℝ} (hL : 2 ≤ L) :
    ∀ᶠ X : ℕ in atTop, ∀ y ∈ Set.Icc (Real.log (X : ℝ)) (Real.log (2 * X : ℝ)),
      1 / (2000 * Real.log X) ≤ intermediatePrimeMinorant X ((Real.log X) ^ (-L)) y := by
  filter_upwards [reference_rough_window_bounds hL (by norm_num : (0 : ℝ) < 1 / 8000),
    eventually_outer_prime_reciprocal_small, eventually_reference_window_fits,
    eventually_intermediate_cutoff_large 2, eventually_ge_atTop 2]
    with X hrough hmass hfit hlarge hX
  intro y hy
  have hX1 : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hLX := Real.log_pos hX1
  have hZ1 : (1 : ℝ) < intermediatePrimeCutoff X := by linarith [hlarge.1]
  have hZp : (0 : ℝ) < intermediatePrimeCutoff X := by linarith
  have hLZ := Real.log_pos hZ1
  have hlogZX := Real.log_le_log hZp hfit.1
  have hinv : 1 / Real.log X ≤ 1 / Real.log (intermediatePrimeCutoff X) :=
    one_div_le_one_div_of_le hLZ hlogZX
  obtain ⟨hparent, hchildren⟩ := hrough y hy
  let P := sievePrimes (intermediatePrimeCutoff X) (outerPrimeCutoff X)
  let R : ℝ := ∑ p ∈ P, (p : ℝ)⁻¹
  have hR : R ≤ 191 / 200 := hmass
  have hR1 : R ≤ 1 := hR.trans (by norm_num)
  have hc : logarithmicPrimeCofactorWindow P (3 * X) (intermediatePrimeCutoff X)
      ((Real.log X) ^ (-L)) y ≤
      ((23 / 40 : ℝ) / Real.log (intermediatePrimeCutoff X)) * R +
        ((1 / 8000 : ℝ) / Real.log X) * R := by
    unfold logarithmicPrimeCofactorWindow
    calc
      _ ≤ ∑ p ∈ P, (p : ℝ)⁻¹ *
          ((23 / 40 : ℝ) / Real.log (intermediatePrimeCutoff X) + (1 / 8000 : ℝ) / Real.log X) :=
        Finset.sum_le_sum (fun p hp ↦ mul_le_mul_of_nonneg_left (hchildren p hp) (by positivity))
      _ = R * ((23 / 40 : ℝ) / Real.log (intermediatePrimeCutoff X) +
          (1 / 8000 : ℝ) / Real.log X) := (Finset.sum_mul _ _ _).symm
      _ = _ := by ring
  have hc' : logarithmicPrimeCofactorWindow P (3 * X) (intermediatePrimeCutoff X)
      ((Real.log X) ^ (-L)) y ≤
      ((23 / 40 : ℝ) / Real.log (intermediatePrimeCutoff X)) * (191 / 200) +
        (1 / 8000 : ℝ) / Real.log X :=
    hc.trans (add_le_add (mul_le_mul_of_nonneg_left hR (by positivity))
      (mul_le_of_le_one_right (by positivity) hR1))
  have hlower := sub_le_sub hparent hc'
  change (11 / 20 : ℝ) / Real.log (intermediatePrimeCutoff X) - (1 / 8000 : ℝ) / Real.log X -
      (((23 / 40 : ℝ) / Real.log (intermediatePrimeCutoff X)) * (191 / 200) +
        (1 / 8000 : ℝ) / Real.log X) ≤
      intermediatePrimeMinorant X ((Real.log X) ^ (-L)) y at hlower
  have hi0 : 0 ≤ 1 / Real.log X := by positivity
  have hnumeric : (1 / 2000 : ℝ) * (1 / Real.log X) ≤
      (7 / 8000 : ℝ) * (1 / Real.log (intermediatePrimeCutoff X)) -
        (2 / 8000 : ℝ) * (1 / Real.log X) := by nlinarith
  calc
    _ = (1 / 2000 : ℝ) * (1 / Real.log X) := by ring
    _ ≤ _ := hnumeric
    _ = (11 / 20 : ℝ) / Real.log (intermediatePrimeCutoff X) - (1 / 8000 : ℝ) / Real.log X -
        (((23 / 40 : ℝ) / Real.log (intermediatePrimeCutoff X)) * (191 / 200) +
          (1 / 8000 : ℝ) / Real.log X) := by ring
    _ ≤ _ := hlower

end Erdos421
