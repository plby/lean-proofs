import ErdosProblems.Erdos67b.MRLemma14TwoLengthHighAssembly

/-!
# Single-length Perron limit and frequency split

The source Lemma 14 comparison leaves one longer normalized short average.
This module gives that term the same endpoint-corrected, infinite-Perron
treatment as the two-length difference.  In particular, no pointwise
absolute Perron error (and hence no spurious logarithmic loss) remains.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

/-- Square mean of the endpoint-corrected single-length Perron model.  The
coefficient restriction scale `Y` is independent of the spatial scale `X`. -/
def dyadicSingleCorrectedPerronMeanSquareAt
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq
      (dyadicRestrictedCorrectedPerronAverage S f Y x H T)

/-- Vanishing square mass of the pure single-length Perron truncation
errors. -/
def dyadicSinglePerronTruncationErrorMeanSquareAt
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    (lemma14PerronTruncationError
      (dyadicRestrictedCoefficient S f Y) x H T) ^ 2

/-- Endpoint correction is an `H`-only cost.  This is the precise bridge
from the corrected central model to the raw Perron-kernel energy. -/
theorem dyadicSingleCorrectedPerronMeanSquareAt_le_raw_add_endpoint
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y X H : ℕ} (hH : 0 < H) (T : ℝ) :
    dyadicSingleCorrectedPerronMeanSquareAt S f Y X H T ≤
      2 * dyadicRestrictedPerronAverageMeanSquareAt S f Y X H T +
        2 * (X : ℝ) / (H : ℝ) ^ 2 := by
  classical
  have hHnonneg : 0 ≤ ((H : ℝ)⁻¹) := by positivity
  unfold dyadicSingleCorrectedPerronMeanSquareAt
    dyadicRestrictedPerronAverageMeanSquareAt
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (dyadicRestrictedCorrectedPerronAverage S f Y x H T)) ≤
      ∑ x ∈ Finset.Ioc X (2 * X),
        (2 * Complex.normSq (dyadicRestrictedPerronAverage S f Y x H T) +
          2 * ((H : ℝ)⁻¹) ^ 2) := by
      apply Finset.sum_le_sum
      intro x hx
      unfold dyadicRestrictedCorrectedPerronAverage
      have hsum := normSq_sub_le_two_mul_add
        (dyadicRestrictedPerronAverage S f Y x H T)
        (-dyadicRestrictedPerronEndpointCorrection S f Y x H)
      simp only [sub_neg_eq_add, Complex.normSq_neg] at hsum
      have hcorr := norm_dyadicRestrictedPerronEndpointCorrection_le
        S hf Y x hH
      have hcorrSq : Complex.normSq
          (dyadicRestrictedPerronEndpointCorrection S f Y x H) ≤
          ((H : ℝ)⁻¹) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        exact (sq_le_sq₀ (norm_nonneg _) hHnonneg).2 hcorr
      linarith
    _ = 2 * (∑ x ∈ Finset.Ioc X (2 * X),
          Complex.normSq (dyadicRestrictedPerronAverage S f Y x H T)) +
        2 * (X : ℝ) * ((H : ℝ)⁻¹) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul, card_Ioc_self_two_mul]
      ring
    _ = 2 * (∑ x ∈ Finset.Ioc X (2 * X),
          Complex.normSq (dyadicRestrictedPerronAverage S f Y x H T)) +
        2 * (X : ℝ) / (H : ℝ) ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]

theorem tendsto_dyadicSinglePerronTruncationErrorMeanSquareAt_atTop
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H : ℕ) :
    Filter.Tendsto (fun T : ℝ ↦
        dyadicSinglePerronTruncationErrorMeanSquareAt S f Y X H T)
      Filter.atTop (nhds 0) := by
  unfold dyadicSinglePerronTruncationErrorMeanSquareAt
  simpa using tendsto_finsetSum (Finset.Ioc X (2 * X)) (fun x hx ↦
    (tendsto_lemma14PerronTruncationError_atTop
      (dyadicRestrictedCoefficient S f Y) x H).pow 2)

theorem exists_dyadicSinglePerronTruncationErrorMeanSquareAt_lt
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H : ℕ)
    {e : ℝ} (he : 0 < e) :
    ∃ U₀ : ℝ, ∀ U ≥ U₀,
      dyadicSinglePerronTruncationErrorMeanSquareAt S f Y X H U < e := by
  obtain ⟨U₀, hU₀⟩ := Metric.tendsto_atTop.mp
    (tendsto_dyadicSinglePerronTruncationErrorMeanSquareAt_atTop
      S f Y X H) e he
  refine ⟨U₀, fun U hU ↦ ?_⟩
  have hnonneg : 0 ≤
      dyadicSinglePerronTruncationErrorMeanSquareAt S f Y X H U := by
    unfold dyadicSinglePerronTruncationErrorMeanSquareAt
    exact Finset.sum_nonneg (fun x hx ↦ sq_nonneg _)
  have h := hU₀ U hU
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at h

/-- The actual normalized single-length mean square is controlled by the
corrected finite Perron model and a genuinely vanishing error. -/
theorem dyadicRestrictedShortAverageMeanSquareAt_le_correctedPerron
    (S : Finset ℕ) (f : ℕ → ℂ) {Y X H : ℕ}
    (_hX : 0 < X) (hH : 0 < H) {T : ℝ} (hT : 0 < T) :
    dyadicRestrictedShortAverageMeanSquareAt S f Y X H ≤
      2 * dyadicSingleCorrectedPerronMeanSquareAt S f Y X H T +
        2 * dyadicSinglePerronTruncationErrorMeanSquareAt S f Y X H T := by
  classical
  unfold dyadicRestrictedShortAverageMeanSquareAt
    dyadicSingleCorrectedPerronMeanSquareAt
    dyadicSinglePerronTruncationErrorMeanSquareAt
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hxmem
  have hx : 0 < x := by
    have := Finset.mem_Ioc.mp hxmem
    omega
  let A : ℂ := dyadicRestrictedShortAverage S f Y x H
  let M : ℂ := dyadicRestrictedCorrectedPerronAverage S f Y x H T
  let E : ℝ := lemma14PerronTruncationError
    (dyadicRestrictedCoefficient S f Y) x H T
  have happrox : ‖A - M‖ ≤ E := by
    simpa only [A, M, E] using
      norm_dyadicShortAverage_sub_correctedPerron_le_truncationError
        S f Y hx hH hT
  have hsq : Complex.normSq (A - M) ≤ E ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (E - ‖A - M‖), norm_nonneg (A - M)]
  have hbasic : Complex.normSq A ≤
      2 * Complex.normSq M + 2 * Complex.normSq (A - M) := by
    have hnormA : ‖A‖ ≤ ‖M‖ + ‖A - M‖ := by
      calc
        ‖A‖ = ‖M + (A - M)‖ := by congr 1; abel
        _ ≤ ‖M‖ + ‖A - M‖ := norm_add_le _ _
    simp only [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖M‖ - ‖A - M‖), norm_nonneg A,
      norm_nonneg M, norm_nonneg (A - M)]
  exact hbasic.trans (by nlinarith)

/-- Exact decomposition of one corrected symmetric Perron model into its
central segment and the two high-frequency segments. -/
theorem dyadicRestrictedCorrectedPerronAverage_eq_low_add_high
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {x H : ℕ} (hx : 0 < x) (hH : 0 < H)
    {T U : ℝ} (_hTU : T ≤ U) :
    dyadicRestrictedCorrectedPerronAverage S f Y x H U =
      dyadicRestrictedCorrectedPerronAverage S f Y x H T +
        perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H (-U) (-T) +
        perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H T U := by
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  have hF : Continuous F := continuous_dyadicVerticalDirichletPolynomial S f Y
  have hG : Continuous (fun t ↦ F t * perronIncrementKernel x H t) :=
    continuous_mul_perronIncrementKernel_nat F hF hx hH
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ := MeasureTheory.volume) (-U) (-T))
    (hG.intervalIntegrable (μ := MeasureTheory.volume) (-T) T)
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ := MeasureTheory.volume) (-U) T)
    (hG.intervalIntegrable (μ := MeasureTheory.volume) T U)
  have hsplit :
      (∫ t in -U..U, F t * perronIncrementKernel x H t) =
        (∫ t in -T..T, F t * perronIncrementKernel x H t) +
          (∫ t in -U..-T, F t * perronIncrementKernel x H t) +
          ∫ t in T..U, F t * perronIncrementKernel x H t := by
    calc
      (∫ t in -U..U, F t * perronIncrementKernel x H t) =
          (∫ t in -U..T, F t * perronIncrementKernel x H t) +
            ∫ t in T..U, F t * perronIncrementKernel x H t := hright.symm
      _ = ((∫ t in -U..-T, F t * perronIncrementKernel x H t) +
            ∫ t in -T..T, F t * perronIncrementKernel x H t) +
            ∫ t in T..U, F t * perronIncrementKernel x H t := by
          rw [hleft]
      _ = _ := by ring
  unfold dyadicRestrictedCorrectedPerronAverage
    dyadicRestrictedPerronAverage perronKernelSegmentOn
  change (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t in -U..U, F t * perronIncrementKernel x H t)) + _ = _
  rw [hsplit]
  ring

/-- A corrected one-length model at outer height `U` is bounded by its
central model at `T` and the positive/negative high-frequency mass. -/
theorem dyadicSingleCorrectedPerronMeanSquareAt_le_low_add_high
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H : ℕ} (_hX : 0 < X) (hH : 0 < H)
    {T U : ℝ} (hTU : T ≤ U) :
    dyadicSingleCorrectedPerronMeanSquareAt S f Y X H U ≤
      2 * dyadicSingleCorrectedPerronMeanSquareAt S f Y X H T +
        4 * dyadicSinglePerronHighMeanSquare S f Y X H T U := by
  classical
  let L : ℕ → ℂ := fun x ↦
    dyadicRestrictedCorrectedPerronAverage S f Y x H T
  let N : ℕ → ℂ := fun x ↦
    perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
      x H (-U) (-T)
  let P : ℕ → ℂ := fun x ↦
    perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
      x H T U
  have hpoint (x : ℕ) (hxmem : x ∈ Finset.Ioc X (2 * X)) :
      Complex.normSq
          (dyadicRestrictedCorrectedPerronAverage S f Y x H U) ≤
        2 * Complex.normSq (L x) +
          4 * (Complex.normSq (N x) + Complex.normSq (P x)) := by
    have hx : 0 < x := by
      have := Finset.mem_Ioc.mp hxmem
      omega
    rw [dyadicRestrictedCorrectedPerronAverage_eq_low_add_high
      S f Y hx hH hTU]
    have houter := normSq_sub_le_two_mul_add (L x) (-(N x + P x))
    have hinner := normSq_sub_le_two_mul_add (N x) (-P x)
    simp only [sub_neg_eq_add, Complex.normSq_neg] at houter hinner
    dsimp [L, N, P] at houter hinner ⊢
    calc
      Complex.normSq (_ + _ + _) =
          Complex.normSq
            (dyadicRestrictedCorrectedPerronAverage S f Y x H T +
              (perronKernelSegmentOn
                  (dyadicVerticalDirichletPolynomial S f Y) x H (-U) (-T) +
                perronKernelSegmentOn
                  (dyadicVerticalDirichletPolynomial S f Y) x H T U)) := by
          congr 1
          abel
      _ ≤ 2 * (Complex.normSq
            (dyadicRestrictedCorrectedPerronAverage S f Y x H T) +
          Complex.normSq
            (perronKernelSegmentOn
                (dyadicVerticalDirichletPolynomial S f Y) x H (-U) (-T) +
              perronKernelSegmentOn
                (dyadicVerticalDirichletPolynomial S f Y) x H T U)) := houter
      _ ≤ _ := by linarith [hinner]
  unfold dyadicSingleCorrectedPerronMeanSquareAt
    dyadicSinglePerronHighMeanSquare
  calc
    _ ≤ ∑ x ∈ Finset.Ioc X (2 * X),
        (2 * Complex.normSq (L x) +
          4 * (Complex.normSq (N x) + Complex.normSq (P x))) :=
      Finset.sum_le_sum hpoint
    _ = 2 * (∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (L x)) +
        4 * ∑ x ∈ Finset.Ioc X (2 * X),
          (Complex.normSq (N x) + Complex.normSq (P x)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rfl

/-- Abstract single-length Perron-limit join.  A high-frequency estimate
uniform in the outer truncation height controls the actual longer average. -/
theorem dyadicRestrictedShortAverageMeanSquareAt_le_of_uniform_high
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H : ℕ} (hX : 0 < X) (hH : 0 < H)
    {T E : ℝ} (_hT : 0 < T)
    (hhigh : ∀ U : ℝ, T ≤ U →
      dyadicSinglePerronHighMeanSquare S f Y X H T U ≤ E) :
    dyadicRestrictedShortAverageMeanSquareAt S f Y X H ≤
      4 * dyadicSingleCorrectedPerronMeanSquareAt S f Y X H T +
        8 * E := by
  apply le_of_forall_pos_le_add
  intro e he
  obtain ⟨U₀, hU₀⟩ :=
    exists_dyadicSinglePerronTruncationErrorMeanSquareAt_lt
      S f Y X H (half_pos he)
  let U : ℝ := max U₀ (max T 1)
  have hU₀U : U₀ ≤ U := le_max_left _ _
  have hTU : T ≤ U := le_trans (le_max_left _ _) (le_max_right _ _)
  have hUpos : 0 < U := by
    exact lt_of_lt_of_le zero_lt_one
      (le_trans (le_max_right T 1) (le_max_right U₀ (max T 1)))
  have herr := hU₀ U hU₀U
  have hshort := dyadicRestrictedShortAverageMeanSquareAt_le_correctedPerron
    S f hX hH hUpos (Y := Y)
  have hsplit := dyadicSingleCorrectedPerronMeanSquareAt_le_low_add_high
    S f hX hH hTU (Y := Y)
  have henergy := hhigh U hTU
  linarith

end

end Erdos67b
