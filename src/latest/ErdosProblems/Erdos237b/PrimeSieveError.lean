import ErdosProblems.Erdos237b.PrimeErrorEnvelope
import ErdosProblems.Erdos237b.SieveS1Limit
import ErdosProblems.Erdos237b.YSharpBounds
import BoundedGaps.BombieriVinogradov.Proof.MainTheorem

/-! Unconditional vanishing of the actual prime-progression error for bounded supported weights. -/

namespace Erdos237b

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

noncomputable def admissibleResidue {H : Finset ℕ} (hH : BoundedGaps.IsAdmissible H)
    (N : ℕ) : ℕ :=
  Classical.choose (exists_preSieveResidueClass_primorial hH (tripleLogCutoff (N - 1)))

theorem admissibleResidue_coprime {H : Finset ℕ} (hH : BoundedGaps.IsAdmissible H)
    (N : ℕ) (h : ℕ) (hh : h ∈ H) :
    Nat.Coprime (admissibleResidue hH N + h) (engelsmaMaynardModulus N) :=
  (Classical.choose_spec (exists_preSieveResidueClass_primorial hH
    (tripleLogCutoff (N - 1)))).2 h hh

noncomputable def s2YError (H : Finset ℕ) (alpha : ℝ)
    (y : ℕ → (H → ℕ) → ℝ) (v : ℕ → ℕ) (N : ℕ) : ℝ :=
  compatiblePairRestrictedErrorOuter H
    (maynardDivisorTupleSupport H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N))
    (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) (v N) N
    (maynardCoefficientFromY H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) (y N))
    (fun _ hd => isMaynardDivisorTuple_of_mem_support hd)

theorem tendsto_normalized_s2YError {H : Finset ℕ} {theta delta B : ℝ}
    (hH : H.Nonempty) (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2) (hB : 0 ≤ B)
    (y : ℕ → (H → ℕ) → ℝ) (v : ℕ → ℕ)
    (hy : ∀ N, IsSupportedMaynardY H (engelsmaMaynardRadius (theta / 2 - delta) N)
      (engelsmaMaynardModulus N) (y N)) (hbound : ∀ N r, |y N r| ≤ B)
    (hv : ∀ N h, h ∈ H → Nat.Coprime (v N + h) (engelsmaMaynardModulus N)) :
    Tendsto (fun N : ℕ => s2YError H (theta / 2 - delta) y v N /
      sieveScale H (theta / 2 - delta) N) atTop (nhds 0) := by
  let alpha := theta / 2 - delta
  let A : ℝ := ((s2HalfLogExponent H * 2 : ℕ) : ℝ)
  have hA : 0 < A := by dsimp [A, s2HalfLogExponent]; positivity
  obtain ⟨C, X₀, hw⟩ := hasPrimeLevel_exists_witness
    (unconditional_bombieriVinogradov theta htheta hthetaHalf) hA
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have henv := tendsto_normalized_s2TauErrorEnvelope (H := H) (B := B)
    htheta hthetaHalf hdelta hdeltaTheta hw.1
  apply squeeze_zero_norm' ?_ henv
  filter_upwards [eventually_coversShiftDifferencePrimes H,
    eventually_engelsmaMaynard_modulus_radius_cutoff htheta.le hdelta,
    eventually_ge_atTop (X₀ + 1), eventually_sieveScale_pos H halpha]
    with N hcoverage hcut hN hS
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hS]
  apply div_le_div_of_nonneg_right ?_ hS.le
  let R := engelsmaMaynardRadius alpha N
  let W := engelsmaMaynardModulus N
  let D := maynardDivisorTupleSupport H R W
  let lambda := maynardCoefficientFromY H R W (y N)
  let L := B * (1 + Real.log R) ^ (2 * Fintype.card H ^ 2)
  have hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d :=
    fun _ hd => isMaynardDivisorTuple_of_mem_support hd
  have hupper (h : H) : X₀ ≤ 2 * N + h.val - 1 := by omega
  have hlower (h : H) : X₀ ≤ N + h.val - 1 := by omega
  have hcutUpper (h : H) : W * R * R ≤ modulusCutoff theta (2 * N + h.val - 1) := by
    simpa only [show N + (N + h.val) - 1 = 2 * N + h.val - 1 by omega]
      using hcut (N + h.val)
  have hcutLower (h : H) : W * R * R ≤ modulusCutoff theta (N + h.val - 1) := hcut h.val
  have hsizeUpper (h : H) : W * R * R ≤ (2 * N + h.val - 1) + 1 :=
    (hcutUpper h).trans ((modulusCutoff_le_self (by have := hw.2.1; omega)
      (by linarith : theta ≤ 1)).trans (Nat.le_succ _))
  have hsizeLower (h : H) : W * R * R ≤ (N + h.val - 1) + 1 :=
    (hcutLower h).trans ((modulusCutoff_le_self (by have := hw.2.1; omega)
      (by linarith : theta ≤ 1)).trans (Nat.le_succ _))
  have hb := hw.bound_abs_compatiblePairRestrictedErrorOuter_tau
    hH (BoundedGaps.Maynard.squarefree_primorial _) hD hcoverage (hv N) lambda L (by omega)
    (show 0 ≤ L by dsimp [L]; positivity)
    (fun d hd => abs_coefficientFromY_le_sharp_log (hy N) hB (hbound N) hH hd)
    hupper hlower hcutUpper hcutLower hsizeUpper hsizeLower
  exact hb

end Erdos237b
