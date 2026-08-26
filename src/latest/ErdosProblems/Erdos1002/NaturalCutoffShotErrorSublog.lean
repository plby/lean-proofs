import ErdosProblems.Erdos1002.NaturalCutoffWindowCarrierBridge
import ErdosProblems.Erdos1002.NaturalCutoffShotFullCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sublogarithmic natural-cutoff shot error

This file closes the Fourier-window reconstruction estimate.  The exact
positive-frequency coefficient identity from
`NaturalCutoffWindowCarrierBridge` is summed first over the carrier variable
and then over a finite frequency interval.  Absolute carrier summability
justifies this interchange.  The uniform carrier estimate then bounds every
positive-frequency truncation; monotone exhaustion of the positive Parseval
energy and real Fourier conjugacy recover the full `L²` error.

The final theorem has exactly the normalization required by
`tendsto_rotation_reconstruction_of_windowError_sublog`.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- Positive-frequency Fourier truncation of the literal natural-cutoff
shot error. -/
def naturalCutoffShotErrorPositivePartialSum
    (N : ℕ+) (K : ℕ) : UnitCircleL2 :=
  ∑ n ∈ Finset.Icc 1 K,
    naturalCutoffShotErrorCoefficient N (n : ℤ) • fourierLp 2 (n : ℤ)

private theorem sum_range_succ_eq_sum_Icc_one
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (K : ℕ) :
    (∑ j ∈ Finset.range K, f (j + 1)) =
      ∑ n ∈ Finset.Icc 1 K, f n := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  omega

/-- Natural-scale specialization of the squared infinite-carrier estimate.
The bound is uniform in the positive-frequency cutoff `K`. -/
theorem uniform_norm_infiniteWindowFourierSeries_sq_small_natural_scale
    {eta : ℝ} (heta : 0 < eta) :
    ∃ N₀ : ℕ, ∀ (N K : ℕ), N₀ ≤ N →
      ‖infiniteWindowFourierSeries N N K‖ ^ 2 ≤
        eta * (Real.log (N : ℝ)) ^ 2 := by
  have hetaNine : 0 < eta / 9 := by positivity
  rcases uniform_norm_infiniteWindowFourierSeries_sq_small_above_scale
    hetaNine with ⟨H, _hH, hinfinite⟩
  have hlogNat :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop, H ≤ Real.log (N : ℝ) :=
    (tendsto_atTop.1 hlogNat) H
  rcases (eventually_atTop.1 hevent) with ⟨N₁, hN₁⟩
  refine ⟨max 3 N₁, ?_⟩
  intro N K hN
  have hNthree : 3 ≤ N := (le_max_left 3 N₁).trans hN
  have hNN₁ : N₁ ≤ N := (le_max_right 3 N₁).trans hN
  have hNpos : 0 < N := by omega
  have hNRpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hbase : H ≤ Real.log (windowCarrierBaseScale N) := by
    exact (hN₁ N hNN₁).trans (Real.log_le_log hNRpos (by
      unfold windowCarrierBaseScale
      have he : 0 < Real.exp 1 := Real.exp_pos 1
      linarith))
  have hraw := hinfinite N N K hNpos hbase
  have hglobalScale :
      windowCarrierGlobalScale N N ≤ (N : ℝ) ^ 3 := by
    unfold windowCarrierGlobalScale
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hNRthree : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNthree
    nlinarith [mul_nonneg (sub_nonneg.mpr hNRthree)
      (sq_nonneg (N : ℝ)), sq_nonneg ((N : ℝ) - 1)]
  have hglobalLog :
      Real.log (windowCarrierGlobalScale N N) ≤
        3 * Real.log (N : ℝ) := by
    calc
      Real.log (windowCarrierGlobalScale N N) ≤
          Real.log ((N : ℝ) ^ 3) := by
        apply Real.log_le_log
        · unfold windowCarrierGlobalScale
          positivity
        · exact hglobalScale
      _ = 3 * Real.log (N : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hglobalNonneg :
      0 ≤ Real.log (windowCarrierGlobalScale N N) :=
    le_trans (by norm_num) (one_le_log_windowCarrierGlobalScale N N)
  have hglobalSq :
      (Real.log (windowCarrierGlobalScale N N)) ^ 2 ≤
        (3 * Real.log (N : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hglobalNonneg hglobalLog 2
  calc
    ‖infiniteWindowFourierSeries N N K‖ ^ 2 ≤
        (eta / 9) *
          (Real.log (windowCarrierGlobalScale N N)) ^ 2 := hraw
    _ ≤ (eta / 9) * (3 * Real.log (N : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hglobalSq hetaNine.le
    _ = eta * (Real.log (N : ℝ)) ^ 2 := by ring

/-- Exact finite Parseval identity for the positive error truncation. -/
theorem norm_naturalCutoffShotErrorPositivePartialSum_sq
    (N : ℕ+) (K : ℕ) :
    ‖naturalCutoffShotErrorPositivePartialSum N K‖ ^ 2 =
      ∑ n ∈ Finset.Icc 1 K,
        ‖naturalCutoffShotErrorCoefficient N (n : ℤ)‖ ^ 2 := by
  unfold naturalCutoffShotErrorPositivePartialSum
  simpa using!
    (orthonormal_fourier.orthogonalFamily.norm_sum
      (fun n : ℤ ↦ naturalCutoffShotErrorCoefficient N n)
      ((Finset.Icc 1 K).map
        ⟨(fun n : ℕ ↦ (n : ℤ)), fun _ _ h ↦ Int.ofNat_inj.mp h⟩))

/-- The finite positive-frequency error polynomial is exactly the negative
of the full carrier series with the same frequency cutoff.  The carrier sum
is interchanged with the finite frequency sum only after proving the
required scalar and vector summability. -/
theorem naturalCutoffShotErrorPositivePartialSum_eq_neg_infiniteWindow
    (N : ℕ+) (K : ℕ) :
    naturalCutoffShotErrorPositivePartialSum N K =
      -infiniteWindowFourierSeries (N : ℕ) (N : ℕ) K := by
  have hscalar : ∀ n ∈ Finset.Icc 1 K,
      Summable fun ell : ℤ ↦
        bernoulliMarkFourierCoefficient ell *
          windowModeCoefficient (N : ℕ) (N : ℕ) ell n := by
    intro n _hn
    exact
      summable_bernoulliMarkFourierCoefficient_mul_windowModeCoefficient
        (N : ℕ) (N : ℕ) n
  unfold naturalCutoffShotErrorPositivePartialSum
    infiniteWindowFourierSeries
  rw [show (∑ n ∈ Finset.Icc 1 K,
      naturalCutoffShotErrorCoefficient N (n : ℤ) • fourierLp 2 (n : ℤ)) =
      -(∑ n ∈ Finset.Icc 1 K,
        (∑' ell : ℤ,
          bernoulliMarkFourierCoefficient ell *
            windowModeCoefficient (N : ℕ) (N : ℕ) ell n) •
              fourierLp 2 (n : ℤ)) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    rw [naturalCutoffShotErrorCoefficient_eq_neg_tsum_windowMode
      N n hnpos, neg_smul]]
  congr 1
  calc
    (∑ n ∈ Finset.Icc 1 K,
        (∑' ell : ℤ,
          bernoulliMarkFourierCoefficient ell *
            windowModeCoefficient (N : ℕ) (N : ℕ) ell n) •
              fourierLp 2 (n : ℤ)) =
      ∑' ell : ℤ, ∑ n ∈ Finset.Icc 1 K,
        (bernoulliMarkFourierCoefficient ell *
          windowModeCoefficient (N : ℕ) (N : ℕ) ell n) •
            fourierLp 2 (n : ℤ) := by
      calc
        (∑ n ∈ Finset.Icc 1 K,
            (∑' ell : ℤ,
              bernoulliMarkFourierCoefficient ell *
                windowModeCoefficient (N : ℕ) (N : ℕ) ell n) •
                  fourierLp 2 (n : ℤ)) =
          ∑ n ∈ Finset.Icc 1 K, ∑' ell : ℤ,
            (bernoulliMarkFourierCoefficient ell *
              windowModeCoefficient (N : ℕ) (N : ℕ) ell n) •
                fourierLp 2 (n : ℤ) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [(hscalar n hn).tsum_smul_const]
        _ = ∑' ell : ℤ, ∑ n ∈ Finset.Icc 1 K,
            (bernoulliMarkFourierCoefficient ell *
              windowModeCoefficient (N : ℕ) (N : ℕ) ell n) •
                fourierLp 2 (n : ℤ) := by
            symm
            apply Summable.tsum_finsetSum
            intro n hn
            exact (hscalar n hn).smul_const (fourierLp 2 (n : ℤ))
    _ = ∑' ell : ℤ, windowCarrierTerm (N : ℕ) (N : ℕ) K ell := by
      apply tsum_congr
      intro ell
      unfold windowCarrierTerm windowModeFourierPolynomial
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [mul_smul]

/-- Uniform squared `o(log² N)` bound for the actual literal natural-cutoff
shot error.  This includes both positive and negative frequencies; the
factor two is supplied by the exact real-Fourier conjugacy theorem. -/
theorem uniform_norm_naturalCutoffShotErrorL2_sq_small
    {eta : ℝ} (heta : 0 < eta) :
    ∃ N₀ : ℕ, ∀ N : ℕ+, N₀ ≤ (N : ℕ) →
      ‖naturalCutoffShotErrorL2 N‖ ^ 2 ≤
        eta * (Real.log (N : ℝ)) ^ 2 := by
  have hetaHalf : 0 < eta / 2 := by positivity
  rcases uniform_norm_infiniteWindowFourierSeries_sq_small_natural_scale
    hetaHalf with ⟨Nbound, hbound⟩
  refine ⟨Nbound, ?_⟩
  intro N hN
  let f : ℕ → ℝ := fun n ↦
    ‖naturalCutoffShotErrorCoefficient N (n : ℤ)‖ ^ 2
  have hsall : Summable fun z : ℤ ↦
      ‖naturalCutoffShotErrorCoefficient N z‖ ^ 2 := by
    have h := (hasSum_sq_fourierCoeff (naturalCutoffShotErrorL2 N)).summable
    simpa only [fourierCoeff_naturalCutoffShotErrorL2] using! h
  have hspnat : Summable fun n : ℕ+ ↦ f (n : ℕ) := by
    apply hsall.comp_injective
    intro a b hab
    exact Subtype.ext (Int.ofNat_inj.mp hab)
  have hsnat : Summable fun n : ℕ ↦ f (n + 1) :=
    summable_pnat_iff_summable_succ.mp hspnat
  have hpartial : ∀ K : ℕ,
      (∑ n ∈ Finset.Icc 1 K, f n) ≤
        (eta / 2) * (Real.log (N : ℝ)) ^ 2 := by
    intro K
    have heq :=
      naturalCutoffShotErrorPositivePartialSum_eq_neg_infiniteWindow
        N K
    have hnormEq : ‖naturalCutoffShotErrorPositivePartialSum N K‖ ^ 2 =
        ‖infiniteWindowFourierSeries (N : ℕ) (N : ℕ) K‖ ^ 2 := by
      rw [heq, norm_neg]
    calc
      (∑ n ∈ Finset.Icc 1 K, f n) =
          ‖naturalCutoffShotErrorPositivePartialSum N K‖ ^ 2 := by
        rw [norm_naturalCutoffShotErrorPositivePartialSum_sq]
      _ = ‖infiniteWindowFourierSeries (N : ℕ) (N : ℕ) K‖ ^ 2 :=
        hnormEq
      _ ≤ (eta / 2) * (Real.log (N : ℝ)) ^ 2 :=
        hbound (N : ℕ) K hN
  have hpositive :
      (∑' n : ℕ+, ‖naturalCutoffShotErrorCoefficient N (n : ℤ)‖ ^ 2) ≤
        (eta / 2) * (Real.log (N : ℝ)) ^ 2 := by
    change (∑' n : ℕ+, f (n : ℕ)) ≤ _
    rw [tsum_pnat_eq_tsum_succ]
    apply hsnat.tsum_le_of_sum_range_le
    intro K
    rw [sum_range_succ_eq_sum_Icc_one]
    exact hpartial K
  calc
    ‖naturalCutoffShotErrorL2 N‖ ^ 2 =
        ∑' z : ℤ, ‖naturalCutoffShotErrorCoefficient N z‖ ^ 2 :=
      (tsum_sq_naturalCutoffShotErrorCoefficient N).symm
    _ = 2 * ∑' n : ℕ+,
        ‖naturalCutoffShotErrorCoefficient N (n : ℤ)‖ ^ 2 :=
      tsum_sq_naturalCutoffShotErrorCoefficient_eq_two_mul_positive N
    _ ≤ 2 * ((eta / 2) * (Real.log (N : ℝ)) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hpositive (by norm_num)
    _ = eta * (Real.log (N : ℝ)) ^ 2 := by ring

/-- The actual natural-cutoff shot error is `o(log N)` in circle `L²`. -/
theorem tendsto_naturalCutoffShotErrorL2_div_log :
    Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 2, by omega⟩
        ‖naturalCutoffShotErrorL2 N‖ / Real.log (N : ℝ))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have heta : 0 < (ε / 2) ^ 2 := sq_pos_of_pos (half_pos hε)
  rcases uniform_norm_naturalCutoffShotErrorL2_sq_small heta with
    ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro m hm
  let N : ℕ+ := ⟨m + 2, by omega⟩
  have hNbound : N₀ ≤ (N : ℕ) := by
    dsimp [N]
    omega
  have hNtwo : 2 ≤ (N : ℕ) := by simp [N]
  have hNRone : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hNtwo)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNRone
  have hsquare := hN₀ N hNbound
  have hsquare' : ‖naturalCutoffShotErrorL2 N‖ ^ 2 ≤
      ((ε / 2) * Real.log (N : ℝ)) ^ 2 := by
    simpa only [mul_pow] using! hsquare
  have hlinear : ‖naturalCutoffShotErrorL2 N‖ ≤
      (ε / 2) * Real.log (N : ℝ) :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (half_pos hε).le hlog.le)).mp hsquare'
  have hstrict : (ε / 2) * Real.log (N : ℝ) <
      ε * Real.log (N : ℝ) :=
    mul_lt_mul_of_pos_right (half_lt_self hε) hlog
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg (norm_nonneg _) hlog.le)]
  exact (div_lt_iff₀ hlog).2 (hlinear.trans_lt hstrict)

/-- Closed reconstruction consequence: the normalized rotation sum and the
normalized literal primitive shot sum differ by `o(1)` in `L²`. -/
theorem tendsto_rotation_reconstruction_of_window_carrier_estimate :
    Tendsto
      (fun N : ℕ ↦
        eLpNorm
          (normalizedRotationSum N - normalizedReconstructedShotSum N)
          2 uniform01Measure)
      atTop (nhds 0) :=
  tendsto_rotation_reconstruction_of_windowError_sublog
    tendsto_naturalCutoffShotErrorL2_div_log

end

end Erdos1002
