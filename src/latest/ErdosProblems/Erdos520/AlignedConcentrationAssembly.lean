import ErdosProblems.Erdos520.AlignedGlobalTestAssembly
import ErdosProblems.Erdos520.CaichConcentration
import ErdosProblems.Erdos520.QuadraticVariationReduction
import ErdosProblems.Erdos520.TestPointAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Stopped concentration on the aligned test mesh

This file inserts the concrete root-exponential test points and Caich's
quadratic-variation scale into the exact stopped-Hoeffding theorem.  It
discharges the threshold-ratio calculation which produces the power
`K + 2 K eta - 10`.
-/

/-- Exact square of the repaired critical scale once `log₂ n` is positive. -/
theorem criticalScale_sq
    {η : ℝ} {n : ℕ} (hlog : 0 < log₂ n) :
    criticalScale η n ^ 2 =
      (n : ℝ) * log₂ n ^ (1 / 2 + 2 * η) := by
  unfold criticalScale
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hpow :
      (log₂ n ^ (1 / 4 + η)) ^ 2 =
        log₂ n ^ (1 / 2 + 2 * η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog.le]
    congr 1
    norm_num
    ring
  rw [hpow]

/-- Raising the aligned lower bound for `log₂ x` to the positive exponent
which occurs after squaring the critical threshold. -/
theorem aligned_log₂_rpow_lower
    {K m ell i : ℕ} {η : ℝ} (hK : 1 ≤ K) (hη : 0 < η)
    (hi : i ∈ alignedRootExpTests K m ell) :
    (1 / (3 * (2 : ℝ) ^ K)) ^ (1 / 2 + 2 * η) *
        (ell : ℝ) ^ ((K : ℝ) * (1 / 2 + 2 * η)) ≤
      log₂ (alignedRootExpTestPoint m i) ^ (1 / 2 + 2 * η) := by
  let c : ℝ := 1 / (3 * (2 : ℝ) ^ K)
  let β : ℝ := 1 / 2 + 2 * η
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hβ : 0 < β := by
    dsimp only [β]
    linarith
  have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
  have hellR : 0 < (ell : ℝ) := by positivity
  have hlower : c * (ell : ℝ) ^ (K : ℝ) ≤
      log₂ (alignedRootExpTestPoint m i) := by
    calc
      c * (ell : ℝ) ^ (K : ℝ) =
          c * (ell : ℝ) ^ K := by rw [Real.rpow_natCast]
      _ ≤ log₂ (alignedRootExpTestPoint m i) := by
        simpa only [c] using!
          alignedRootExpTestPoint_log₂_scale_lower hK hi
  have hraise := Real.rpow_le_rpow
    (mul_nonneg hc.le (Real.rpow_nonneg hellR.le _)) hlower hβ.le
  calc
    c ^ β * (ell : ℝ) ^ ((K : ℝ) * β) =
        (c * (ell : ℝ) ^ (K : ℝ)) ^ β := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hellR.le _),
        ← Real.rpow_mul hellR.le]
    _ ≤ log₂ (alignedRootExpTestPoint m i) ^ β := hraise

/-- Positive constant in the aligned stopped-Hoeffding exponent. -/
noncomputable def alignedConcentrationConstant
    (d C : ℝ) (K : ℕ) (η : ℝ) : ℝ :=
  d ^ 2 / (2 * C) *
    (1 / (3 * (2 : ℝ) ^ K)) ^ (1 / 2 + 2 * η)

theorem alignedConcentrationConstant_pos
    {d C η : ℝ} {K : ℕ} (hd : 0 < d) (hC : 0 < C) :
    0 < alignedConcentrationConstant d C K η := by
  unfold alignedConcentrationConstant
  positivity

/-- The squared critical threshold divided by Caich's repaired predictable
quadratic-variation bound has the required power of `ell`. -/
theorem aligned_criticalThreshold_ratio_lower
    {d C η : ℝ} {K m ell i : ℕ}
    (hd : 0 < d) (hC : 0 < C) (hη : 0 < η) (hK : 1 ≤ K)
    (hi : i ∈ alignedRootExpTests K m ell) :
    alignedConcentrationConstant d C K η *
        (ell : ℝ) ^
          ((K : ℝ) + 2 * (K : ℝ) * η - 10) ≤
      (d * criticalScale η (alignedRootExpTestPoint m i)) ^ 2 /
        (2 * caichQuadraticVariationThreshold C K
          (fun _ell r ↦ alignedRootExpTestPoint m r) ell i) := by
  let n : ℕ := alignedRootExpTestPoint m i
  let c : ℝ := 1 / (3 * (2 : ℝ) ^ K)
  let β : ℝ := 1 / 2 + 2 * η
  have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
  have hellR : 0 < (ell : ℝ) := by positivity
  have hn : 0 < n := by
    dsimp only [n]
    have hlt := alignedThinInitial_lt_testPoint_of_mem hi
    omega
  have hlogLower : c * (ell : ℝ) ^ (K : ℝ) ≤ log₂ n := by
    calc
      c * (ell : ℝ) ^ (K : ℝ) = c * (ell : ℝ) ^ K := by
        rw [Real.rpow_natCast]
      _ ≤ log₂ n := by
        simpa only [c, n] using!
          alignedRootExpTestPoint_log₂_scale_lower hK hi
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hlog : 0 < log₂ n :=
    (mul_pos hc (Real.rpow_pos_of_pos hellR _)).trans_le hlogLower
  have hβ : 0 < β := by
    dsimp only [β]
    linarith
  have hrpow := aligned_log₂_rpow_lower hK hη hi
  have hqv : 0 < caichQuadraticVariationThreshold C K
      (fun _ell r ↦ alignedRootExpTestPoint m r) ell i := by
    unfold caichQuadraticVariationThreshold
    positivity
  have hscaleSq := criticalScale_sq (η := η) hlog
  have hpower :
      (ell : ℝ) ^ ((K : ℝ) * β) *
          (ell : ℝ) ^ ((K : ℝ) / 2) /
          (ell : ℝ) ^ (10 : ℝ) =
        (ell : ℝ) ^ ((K : ℝ) + 2 * (K : ℝ) * η - 10) := by
    rw [← Real.rpow_add hellR, ← Real.rpow_sub hellR]
    congr 1
    dsimp only [β]
    ring
  have hmain :
      c ^ β *
          (ell : ℝ) ^ ((K : ℝ) + 2 * (K : ℝ) * η - 10) ≤
        log₂ n ^ β * (ell : ℝ) ^ ((K : ℝ) / 2) /
          (ell : ℝ) ^ (10 : ℝ) := by
    rw [← hpower]
    have hnonneg : 0 ≤
        (ell : ℝ) ^ ((K : ℝ) / 2) /
          (ell : ℝ) ^ (10 : ℝ) := by positivity
    simpa only [c, β, n, div_eq_mul_inv, mul_assoc] using!
      (mul_le_mul_of_nonneg_right hrpow hnonneg)
  unfold alignedConcentrationConstant caichQuadraticVariationThreshold
  dsimp only [n, c, β] at hmain hscaleSq ⊢
  rw [mul_pow, hscaleSq]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hCne : C ≠ 0 := hC.ne'
  have helldenom : (ell : ℝ) ^ ((K : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hellR _).ne'
  have hellten : (ell : ℝ) ^ 10 = (ell : ℝ) ^ (10 : ℝ) := by
    exact (Real.rpow_natCast (ell : ℝ) 10).symm
  rw [hellten]
  calc
    d ^ 2 / (2 * C) *
          (1 / (3 * (2 : ℝ) ^ K)) ^ (1 / 2 + 2 * η) *
          (ell : ℝ) ^ ((K : ℝ) + 2 * (K : ℝ) * η - 10) ≤
        d ^ 2 / (2 * C) *
          (log₂ n ^ (1 / 2 + 2 * η) *
            (ell : ℝ) ^ ((K : ℝ) / 2) /
              (ell : ℝ) ^ (10 : ℝ)) := by
      simpa only [mul_assoc] using!
        (mul_le_mul_of_nonneg_left hmain
          (show 0 ≤ d ^ 2 / (2 * C) by positivity))
    _ =
        (d ^ 2 * ((n : ℝ) * log₂ n ^ (1 / 2 + 2 * η))) /
          (2 * (C * (n : ℝ) * (ell : ℝ) ^ (10 : ℝ) /
            (ell : ℝ) ^ ((K : ℝ) / 2))) := by
      field_simp

/-! ## Exact stopped-Hoeffding assembly -/

/-- Test-point threshold used for the largest-prime martingale piece. -/
noncomputable def alignedLargestPrimeThreshold
    (d η : ℝ) (m _ell i : ℕ) : ℝ :=
  d * criticalScale η (alignedRootExpTestPoint m i)

/-- Repaired quadratic-variation threshold on the aligned mesh. -/
noncomputable def alignedLargestPrimeQvThreshold
    (C : ℝ) (K m ell i : ℕ) : ℝ :=
  caichQuadraticVariationThreshold C K
    (fun _ell r ↦ alignedRootExpTestPoint m r) ell i

/-- Once the repaired quadratic-variation estimate is available almost
surely eventually, stopped Hoeffding and the exact mesh entropy give the
`1/4 + eta` estimate for the largest-prime martingale at every selected test
point. -/
theorem ae_eventually_alignedLargestPrimeMain_lt_of_qv
    {d C η : ℝ} {K m : ℕ} (a : ℕ → ℕ)
    (hd : 0 < d) (hC : 0 < C) (hη : 0 < η) (hK : 1 ≤ K)
    (hgap : 10 < 2 * (K : ℝ) * η)
    (hqv : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        largestPrimeQuadraticVariation omega
            (alignedRootExpTestPoint m i) (a ell)
            (alignedRootExpTestPoint m i) ≤
          alignedLargestPrimeQvThreshold C K m ell i) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        |largestPrimeMain omega
          (alignedRootExpTestPoint m i) (a ell)
          (alignedRootExpTestPoint m i)| <
            alignedLargestPrimeThreshold d η m ell i := by
  let tests : ℕ → Finset ℕ := alignedRootExpTests K m
  let x : ℕ → ℕ → ℕ := fun _ell i ↦ alignedRootExpTestPoint m i
  let a' : ℕ → ℕ → ℕ := fun ell _i ↦ a ell
  let u : ℕ → ℕ → ℝ := alignedLargestPrimeThreshold d η m
  let T : ℕ → ℕ → ℝ := alignedLargestPrimeQvThreshold C K m
  have hu : ∀ ell i, i ∈ tests ell → 0 ≤ u ell i := by
    intro ell i hi
    have hlogLower := alignedRootExpTestPoint_log₂_scale_lower hK hi
    have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
    have hlog : 0 < log₂ (alignedRootExpTestPoint m i) := by
      have hc : 0 < (1 / (3 * (2 : ℝ) ^ K) : ℝ) := by positivity
      have hp : 0 < (ell : ℝ) ^ K := by positivity
      exact (mul_pos hc hp).trans_le hlogLower
    dsimp only [u, alignedLargestPrimeThreshold]
    unfold criticalScale
    exact mul_nonneg hd.le <| mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg hlog.le _)
  have hT : ∀ ell i, i ∈ tests ell → 0 < T ell i := by
    intro ell i hi
    have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
    have hxpos : 0 < alignedRootExpTestPoint m i := by
      have hlt := alignedThinInitial_lt_testPoint_of_mem hi
      omega
    dsimp only [T, alignedLargestPrimeQvThreshold]
    unfold caichQuadraticVariationThreshold
    positivity
  have hexponent : ∀ ell i, i ∈ tests ell →
      alignedConcentrationConstant d C K η *
          (ell : ℝ) ^
            ((K : ℝ) + 2 * (K : ℝ) * η - 10) ≤
        (u ell i) ^ 2 / (2 * T ell i) := by
    intro ell i hi
    simpa only [tests, u, T, alignedLargestPrimeThreshold,
      alignedLargestPrimeQvThreshold] using!
      aligned_criticalThreshold_ratio_lower hd hC hη hK hi
  have hbudget : Summable fun ell =>
      largestPrimeStoppedBudget tests u T ell := by
    apply summable_largestPrimeStoppedBudget_alignedRootExpTests_caich
      K m hK u T
      (alignedConcentrationConstant_pos hd hC) hgap
    exact hexponent
  have hmain := ae_eventually_largestPrimeMain_lt_of_qv_and_summable
    tests x a' x u T hu hT hbudget
  apply hmain
  simpa only [tests, x, a', T, alignedLargestPrimeQvThreshold] using! hqv

/-- Add the low-prime smooth contribution and pull the finite aligned test
families back to the single global root-exponential sequence. -/
theorem aeTestPointBound_partialSum_aligned_of_smooth_qv
    {d C η : ℝ} {K m : ℕ} (a : ℕ → ℕ)
    (hd : 0 < d) (hC : 0 < C) (hη : 0 < η)
    (hK : 1 ≤ K) (hm : 0 < m)
    (hgap : 10 < 2 * (K : ℝ) * η)
    (ha : ∀ᶠ ell : ℕ in atTop, ∀ i ∈ alignedRootExpTests K m ell,
      a ell ≤ alignedRootExpTestPoint m i)
    (hsmooth : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        |Ψ omega (alignedRootExpTestPoint m i) (a ell)| ≤
          alignedLargestPrimeThreshold d η m ell i)
    (hqv : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        largestPrimeQuadraticVariation omega
            (alignedRootExpTestPoint m i) (a ell)
            (alignedRootExpTestPoint m i) ≤
          alignedLargestPrimeQvThreshold C K m ell i) :
    AETestPointBound μ partialSum (criticalScale η)
      (alignedRootExpTestPoint m) := by
  let tests : ℕ → Finset ℕ := alignedRootExpTests K m
  let x : ℕ → ℕ → ℕ := fun _ell i ↦ alignedRootExpTestPoint m i
  let y₀ : ℕ → ℕ → ℕ := fun ell _i ↦ a ell
  let u : ℕ → ℕ → ℝ := alignedLargestPrimeThreshold d η m
  have hmain := ae_eventually_alignedLargestPrimeMain_lt_of_qv
    a hd hC hη hK hgap hqv
  have hpartial : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ tests ell,
        |partialSum omega (x ell i)| ≤ 2 * u ell i := by
    filter_upwards [hsmooth, hmain] with omega hsmoothOmega hmainOmega
    filter_upwards [hsmoothOmega, hmainOmega, ha]
      with ell hsmoothEll hmainEll haEll
    intro i hi
    exact abs_partialSum_le_two_mul_of_pieces omega (haEll i hi)
      (hsmoothEll i hi) (hmainEll i hi)
  apply aeTestPointBound_criticalScale_alignedRootExp_of_ae_scales
    hK hm (fun ell i ↦ 2 * u ell i) (2 * d) (by positivity)
  · filter_upwards with i
    unfold u alignedLargestPrimeThreshold
    ring_nf
    exact le_rfl
  · simpa only [tests, x, u] using! hpartial

/-- Fully granular aligned test-point theorem.  The repaired block maximum,
the five assembled auxiliary estimates, and the deterministic smoothing
inequality imply the quadratic-variation hypothesis above; no separate
"published completion" object is used. -/
theorem aeTestPointBound_partialSum_aligned_of_components
    {d D B η : ℝ} {K m : ℕ} (a : ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ)
    (hd : 0 < d) (hD : 0 < D) (hB : 0 < B) (hη : 0 < η)
    (hK : 1 ≤ K) (hm : 0 < m)
    (hgap : 10 < 2 * (K : ℝ) * η)
    (ha : ∀ᶠ ell : ℕ in atTop, ∀ i ∈ alignedRootExpTests K m ell,
      a ell ≤ alignedRootExpTestPoint m i)
    (hsmoothContribution : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        |Ψ omega (alignedRootExpTestPoint m i) (a ell)| ≤
          alignedLargestPrimeThreshold d η m ell i)
    (hsmoothing : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      qvSmoothingGoodAtScale
        (alignedRootExpTests K m)
        (fun _ell i ↦ alignedRootExpTestPoint m i)
        (fun ell _i ↦ a ell)
        (fun _ell i ↦ alignedRootExpTestPoint m i)
        J U E D ell omega)
    (hblock : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      blockEnergyMaxGoodAtScale J U B K ell omega)
    (haux : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale
        (alignedRootExpTests K m) E B K ell omega) :
    AETestPointBound μ partialSum (criticalScale η)
      (alignedRootExpTestPoint m) := by
  let tests : ℕ → Finset ℕ := alignedRootExpTests K m
  let x : ℕ → ℕ → ℕ := fun _ell i ↦ alignedRootExpTestPoint m i
  let a' : ℕ → ℕ → ℕ := fun ell _i ↦ a ell
  have hx : ∀ ell i, i ∈ tests ell → 0 < x ell i := by
    intro ell i hi
    have hlt := alignedThinInitial_lt_testPoint_of_mem hi
    exact Nat.zero_lt_of_lt hlt
  have hqvGeneric :=
    ae_eventually_testPointQuadraticVariationGood_of_reduction
      tests x a' x J U E hx hD.le hB.le hsmoothing hblock haux
  have hqv : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        largestPrimeQuadraticVariation omega
            (alignedRootExpTestPoint m i) (a ell)
            (alignedRootExpTestPoint m i) ≤
          alignedLargestPrimeQvThreshold (2 * D * B) K m ell i := by
    simpa only [tests, x, a', alignedLargestPrimeQvThreshold] using! hqvGeneric
  exact aeTestPointBound_partialSum_aligned_of_smooth_qv
    a hd (mul_pos (mul_pos (by norm_num) hD) hB) hη hK hm hgap
    ha hsmoothContribution hqv

end Problem520
end Erdos
