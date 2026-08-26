import ErdosProblems.Erdos1002.FixedAwayPhysicalFourier
import ErdosProblems.Erdos1002.ChanKumchevElementaryLongRange

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The unshifted fixed-away carrier on one frequency shell

This file isolates the analytic part of the `ell = 0` argument.  It does
not assume the Chan--Kumchev estimate: the arithmetic partial sums and the
fixed-away multiplier are kept as separate inputs until the final shell
estimate.  In particular, every multiplier variation and every finite Abel
boundary below is an ordinary proved statement.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal Real Topology

namespace Erdos1002

noncomputable section

/-- The unshifted fixed-away multiplier sampled on `K < n <= 2K`. -/
def fixedAwayUnshiftedDyadicMultiplier
    (t δ : ℝ) (K : ℕ) (x : ℝ) : nearDyadicIndex K → ℂ :=
  fun n ↦ fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
    ((n : ℕ) / x ^ 2)

/-- The literal finite denominator block for the unshifted carrier, viewed
in the finite Euclidean frequency space. -/
def fixedAwayUnshiftedFiniteVector
    (t δ : ℝ) (K A U : ℕ) : NearDyadicEuclidean K :=
  ∑ p ∈ Finset.Icc A U,
    euclideanCoordinateMul (nearRamanujanVectorTerm K p)
      (fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))

/-- The Euclidean vector is exactly the restriction of the coefficient
formula `sum c_p(-n) p^{-2} R_chi(n/p^2)` to `K < n <= 2K`. -/
theorem fixedAwayUnshiftedFiniteVector_apply
    (t δ : ℝ) (K A U : ℕ) (n : nearDyadicIndex K) :
    fixedAwayUnshiftedFiniteVector t δ K A U n =
      ∑ p ∈ Finset.Icc A U,
        (ramanujanSum p (-((n : ℕ) : ℤ)) /
          (((p : ℕ) : ℝ) ^ 2 : ℝ)) *
        fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
          (((n : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2) := by
  simp only [fixedAwayUnshiftedFiniteVector, WithLp.ofLp_sum,
    Finset.sum_apply, euclideanCoordinateMul, nearRamanujanVectorTerm,
    fixedAwayUnshiftedDyadicMultiplier, WithLp.ofLp_toLp]

/-- Rewriting a denominator block over the natural half-open interval is
useful when two adjacent dyadic shells are joined. -/
theorem fixedAwayUnshiftedFiniteVector_eq_sum_Ioc
    (t δ : ℝ) (K Q U : ℕ) :
    fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U =
      ∑ p ∈ Finset.Ioc Q U,
        euclideanCoordinateMul (nearRamanujanVectorTerm K p)
          (fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ)) := by
  unfold fixedAwayUnshiftedFiniteVector
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · intro p _hp
    rfl

/-- The finite Euclidean vector is literally the restriction of the
`ell = 0` full carrier block from the physical Fourier expansion.  The
auxiliary parameter `N` disappears because the zero carrier has no
modulation. -/
theorem fixedAwayUnshiftedFiniteVector_one_apply_eq_fullCarrierBlock_zero
    (t δ : ℝ) (K P N : ℕ) (n : nearDyadicIndex K) :
    fixedAwayUnshiftedFiniteVector t δ K 1 P n =
      fixedAwayFullCarrierBlock P t δ N 0 ((n : ℕ) : ℤ) := by
  rw [fixedAwayUnshiftedFiniteVector_apply]
  unfold fixedAwayFullCarrierBlock fixedAwayRamanujanProfileBlock
    fixedAwayRamanujanProfileTerm fixedAwayShiftedProfile fixedAwayScaledPV
    nearBernoulliCarrierFrequency
  apply Finset.sum_congr rfl
  intro p _hp
  push_cast
  ring_nf

/-- Exact squared-norm identification with the positive-frequency dyadic
shell of the physical zero-carrier coefficients. -/
theorem norm_sq_fixedAwayUnshiftedFiniteVector_one_eq_fullCarrierBlock_zero
    (t δ : ℝ) (K P N : ℕ) :
    ‖fixedAwayUnshiftedFiniteVector t δ K 1 P‖ ^ 2 =
      ∑ n ∈ Finset.Ioc K (2 * K),
        ‖fixedAwayFullCarrierBlock P t δ N 0 (n : ℤ)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [← Finset.sum_coe_sort (Finset.Ioc K (2 * K))]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [fixedAwayUnshiftedFiniteVector_one_apply_eq_fullCarrierBlock_zero]

/-- Differentiation of the reciprocal-square sampled fixed-away multiplier.
The argument is always on the positive half-line, hence never crosses the
jump of `R_chi` at zero. -/
theorem hasDerivAt_fixedAwayUnshiftedReciprocalSquare
    {t δ n x : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hn : 0 < n) (hx : x ≠ 0) :
    HasDerivAt
      (fun y : ℝ ↦ fixedAwayPVTransform
        (fixedAwaySmoothCorrection t δ) t (n / y ^ 2))
      ((-2 * n / x ^ 3) •
        deriv (fixedAwayPVTransform
          (fixedAwaySmoothCorrection t δ) t) (n / x ^ 2)) x := by
  have harg : n / x ^ 2 ≠ 0 := div_ne_zero hn.ne' (pow_ne_zero 2 hx)
  have hout := (hasDerivAt_fixedAwayPVTransform_smooth_eq_fourier
    hδ hδt harg).differentiableAt.hasDerivAt
  have hinner := reciprocalSquareArgument_hasDerivAt n x hx
  simpa only [Function.comp_def] using! hout.scomp x hinner

/-- The sampled multiplier is differentiable on the positive half-line. -/
theorem differentiableAt_fixedAwayUnshiftedReciprocalSquare
    {t δ n x : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hn : 0 < n) (hx : 0 < x) :
    DifferentiableAt ℝ
      (fun y : ℝ ↦ fixedAwayPVTransform
        (fixedAwaySmoothCorrection t δ) t (n / y ^ 2)) x :=
  (hasDerivAt_fixedAwayUnshiftedReciprocalSquare hδ hδt hn hx.ne').differentiableAt

/-- Exact norm of the scalar derivative factor on the positive half-line. -/
theorem norm_neg_two_mul_div_cube
    {n x : ℝ} (hn : 0 ≤ n) (hx : 0 < x) :
    ‖(-2 * n / x ^ 3 : ℝ)‖ = 2 * n / x ^ 3 := by
  rw [Real.norm_eq_abs]
  have hnonpos : -2 * n / x ^ 3 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hn)
      (pow_pos hx 3).le
  rw [abs_of_nonpos hnonpos]
  ring

/-- A uniform low-denominator derivative bound on one dyadic denominator
shell.  The factor `Q/K` is what makes shells below `sqrt K` summable after
finite Abel summation. -/
theorem norm_deriv_fixedAwayUnshiftedReciprocalSquare_le_lowShell
    {t δ K Q n x : ℝ}
    (hδ : 0 < δ) (hδt : δ ≤ t)
    (hK : 0 < K) (hnK : K ≤ n)
    (hQ : 0 < Q) (hxQ : Q ≤ x) (hx2Q : x ≤ 2 * Q) :
    ‖deriv
      (fun y : ℝ ↦ fixedAwayPVTransform
        (fixedAwaySmoothCorrection t δ) t (n / y ^ 2)) x‖ ≤
      8 * fixedAwayDerivativeCauchyConstant t δ * Q / K := by
  have hn : 0 < n := hK.trans_le hnK
  have hx : 0 < x := hQ.trans_le hxQ
  have harg : n / x ^ 2 ≠ 0 := div_ne_zero hn.ne' (pow_ne_zero 2 hx.ne')
  have hcomp := hasDerivAt_fixedAwayUnshiftedReciprocalSquare
    hδ hδt hn hx.ne'
  rw [hcomp.deriv, norm_smul,
    norm_neg_two_mul_div_cube hn.le hx]
  have houter :=
    norm_deriv_fixedAwayPVTransform_smooth_le_cauchyEnvelope
      hδ hδt harg
  have hargNonneg : 0 ≤ n / x ^ 2 := by positivity
  have hinvSq : (1 + (n / x ^ 2) ^ 2)⁻¹ ≤ (x ^ 2 / n) ^ 2 := by
    have hpos : 0 < n / x ^ 2 := div_pos hn (sq_pos_of_pos hx)
    have hone : (n / x ^ 2) ^ 2 ≤ 1 + (n / x ^ 2) ^ 2 := by nlinarith
    have hinv : (1 + (n / x ^ 2) ^ 2)⁻¹ ≤
        ((n / x ^ 2) ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 hone
    calc
      (1 + (n / x ^ 2) ^ 2)⁻¹ ≤ ((n / x ^ 2) ^ 2)⁻¹ := hinv
      _ = (x ^ 2 / n) ^ 2 := by field_simp [hn.ne', hx.ne']
  have hC : 0 ≤ fixedAwayDerivativeCauchyConstant t δ :=
    fixedAwayDerivativeCauchyConstant_nonneg t δ
  have hderivOuter :
      ‖deriv (fixedAwayPVTransform
          (fixedAwaySmoothCorrection t δ) t) (n / x ^ 2)‖ ≤
        fixedAwayDerivativeCauchyConstant t δ * (x ^ 2 / n) ^ 2 :=
    houter.trans (mul_le_mul_of_nonneg_left hinvSq hC)
  calc
    (2 * n / x ^ 3) *
        ‖deriv (fixedAwayPVTransform
          (fixedAwaySmoothCorrection t δ) t) (n / x ^ 2)‖ ≤
      (2 * n / x ^ 3) *
        (fixedAwayDerivativeCauchyConstant t δ * (x ^ 2 / n) ^ 2) :=
      mul_le_mul_of_nonneg_left hderivOuter (by positivity)
    _ = 2 * fixedAwayDerivativeCauchyConstant t δ * x / n := by
      field_simp [hn.ne', hx.ne']
    _ ≤ 2 * fixedAwayDerivativeCauchyConstant t δ * (2 * Q) / K := by
      apply (div_le_div_iff₀ hn hK).2
      gcongr
    _ = 4 * fixedAwayDerivativeCauchyConstant t δ * Q / K := by ring
    _ ≤ 8 * fixedAwayDerivativeCauchyConstant t δ * Q / K := by
      gcongr
      norm_num

/-- The constant in the positive-half-line reciprocal bound for `R_chi`. -/
def fixedAwayPVInverseDecayConstant (t δ : ℝ) : ℝ :=
  fixedAwayDerivativeBound2 t δ / (2 * Real.pi) ^ 2

theorem fixedAwayPVInverseDecayConstant_nonneg (t δ : ℝ) :
    0 ≤ fixedAwayPVInverseDecayConstant t δ := by
  unfold fixedAwayPVInverseDecayConstant
  exact div_nonneg (fixedAwayDerivativeBound2_nonneg t δ) (sq_nonneg _)

/-- Below the transition `Q ≈ sqrt K`, the terminal sampled multiplier on
`Q < p <= 2Q` has the explicit gain `Q²/K`. -/
theorem norm_fixedAwayUnshiftedDyadicMultiplier_le_lowShell
    {t δ : ℝ} {K Q U : ℕ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hQ : 0 < Q)
    (hQU : Q < U) (hU2Q : U ≤ 2 * Q) :
    ‖fixedAwayUnshiftedDyadicMultiplier t δ K (U : ℝ)‖ ≤
      4 * fixedAwayPVInverseDecayConstant t δ * (Q : ℝ) ^ 2 /
        (K : ℝ) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hUR : (0 : ℝ) < U := by exact_mod_cast hQ.trans hQU
  have hC : 0 ≤ fixedAwayPVInverseDecayConstant t δ :=
    fixedAwayPVInverseDecayConstant_nonneg t δ
  have hright :
      0 ≤ 4 * fixedAwayPVInverseDecayConstant t δ * (Q : ℝ) ^ 2 /
        (K : ℝ) := by positivity
  apply (pi_norm_le_iff_of_nonneg hright).mpr
  intro n
  have hnBounds := Finset.mem_Ioc.mp n.property
  have hnR : (0 : ℝ) < (n : ℕ) := by exact_mod_cast hK.trans hnBounds.1
  have harg : 0 < ((n : ℕ) : ℝ) / (U : ℝ) ^ 2 := by positivity
  have hraw := norm_fixedAwayPVTransform_smooth_le_inv hδ hδt harg
  change ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
      (((n : ℕ) : ℝ) / (U : ℝ) ^ 2)‖ ≤ _
  calc
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
        (((n : ℕ) : ℝ) / (U : ℝ) ^ 2)‖ ≤
      fixedAwayDerivativeBound2 t δ /
        ((2 * Real.pi) ^ 2 *
          (((n : ℕ) : ℝ) / (U : ℝ) ^ 2)) := hraw
    _ = fixedAwayPVInverseDecayConstant t δ /
        (((n : ℕ) : ℝ) / (U : ℝ) ^ 2) := by
      unfold fixedAwayPVInverseDecayConstant
      ring
    _ = fixedAwayPVInverseDecayConstant t δ * (U : ℝ) ^ 2 /
        (n : ℕ) := by
      field_simp [hnR.ne', hUR.ne']
    _ ≤ fixedAwayPVInverseDecayConstant t δ * (2 * (Q : ℝ)) ^ 2 /
        (K : ℝ) := by
      apply (div_le_div_iff₀ hnR hKR).2
      have hUR2Q : (U : ℝ) ≤ 2 * (Q : ℝ) := by exact_mod_cast hU2Q
      have hKleN : (K : ℝ) ≤ (n : ℕ) := by
        exact_mod_cast hnBounds.1.le
      gcongr
    _ = 4 * fixedAwayPVInverseDecayConstant t δ * (Q : ℝ) ^ 2 /
        (K : ℝ) := by ring

/-- One discrete multiplier increment in a low denominator shell. -/
theorem norm_fixedAwayUnshiftedDyadicMultiplier_sub_succ_le_lowShell
    {t δ : ℝ} {K Q U p : ℕ}
    (hδ : 0 < δ) (hδt : δ ≤ t)
    (hK : 0 < K) (hQ : 0 < Q)
    (hQp : Q ≤ p) (hpU : p + 1 ≤ U) (hU2Q : U ≤ 2 * Q) :
    ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
        fixedAwayUnshiftedDyadicMultiplier t δ K ((p + 1 : ℕ) : ℝ)‖ ≤
      8 * fixedAwayDerivativeCauchyConstant t δ * (Q : ℝ) /
        (K : ℝ) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hpR : (0 : ℝ) < p := by exact_mod_cast hQ.trans_le hQp
  have hC : 0 ≤ fixedAwayDerivativeCauchyConstant t δ :=
    fixedAwayDerivativeCauchyConstant_nonneg t δ
  have hright :
      0 ≤ 8 * fixedAwayDerivativeCauchyConstant t δ * (Q : ℝ) /
        (K : ℝ) := by positivity
  apply (pi_norm_le_iff_of_nonneg hright).mpr
  intro n
  let f : ℝ → ℂ := fun x ↦ fixedAwayPVTransform
    (fixedAwaySmoothCorrection t δ) t (((n : ℕ) : ℝ) / x ^ 2)
  have hnBounds := Finset.mem_Ioc.mp n.property
  have hnR : (0 : ℝ) < (n : ℕ) := by exact_mod_cast hK.trans hnBounds.1
  have hdiff : ∀ x ∈ Set.Icc (p : ℝ) ((p + 1 : ℕ) : ℝ),
      DifferentiableAt ℝ f x := by
    intro x hx
    apply differentiableAt_fixedAwayUnshiftedReciprocalSquare hδ hδt hnR
    exact hpR.trans_le hx.1
  have hbound : ∀ x ∈ Set.Icc (p : ℝ) ((p + 1 : ℕ) : ℝ),
      ‖deriv f x‖ ≤
        8 * fixedAwayDerivativeCauchyConstant t δ * (Q : ℝ) /
          (K : ℝ) := by
    intro x hx
    apply norm_deriv_fixedAwayUnshiftedReciprocalSquare_le_lowShell
      hδ hδt hKR
    · exact_mod_cast hnBounds.1.le
    · exact hQR
    · have hQpR : (Q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hQp
      exact hQpR.trans hx.1
    · have hxU : x ≤ (U : ℝ) := by
        calc
          x ≤ ((p + 1 : ℕ) : ℝ) := hx.2
          _ ≤ (U : ℝ) := by exact_mod_cast hpU
      exact hxU.trans (by exact_mod_cast hU2Q)
  have hpMem : (p : ℝ) ∈ Set.Icc (p : ℝ) ((p + 1 : ℕ) : ℝ) := by
    constructor <;> norm_num
  have hpSuccMem : ((p + 1 : ℕ) : ℝ) ∈
      Set.Icc (p : ℝ) ((p + 1 : ℕ) : ℝ) := by
    constructor <;> norm_num
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (convex_Icc _ _) hpMem hpSuccMem
  change ‖f (p : ℝ) - f ((p + 1 : ℕ) : ℝ)‖ ≤ _
  calc
    ‖f (p : ℝ) - f ((p + 1 : ℕ) : ℝ)‖ =
        ‖f ((p + 1 : ℕ) : ℝ) - f (p : ℝ)‖ := norm_sub_rev _ _
    _ ≤ (8 * fixedAwayDerivativeCauchyConstant t δ * (Q : ℝ) /
        (K : ℝ)) *
          ‖(((p + 1 : ℕ) : ℝ) - (p : ℝ))‖ := hmv
    _ = 8 * fixedAwayDerivativeCauchyConstant t δ * (Q : ℝ) /
        (K : ℝ) := by norm_num

/-- The complete discrete variation on a low dyadic denominator shell. -/
theorem sum_norm_fixedAwayUnshiftedDyadicMultiplier_sub_succ_le_lowShell
    {t δ : ℝ} {K Q U : ℕ}
    (hδ : 0 < δ) (hδt : δ ≤ t)
    (hK : 0 < K) (hQ : 0 < Q)
    (hQU : Q + 1 ≤ U) (hU2Q : U ≤ 2 * Q) :
    (∑ p ∈ Finset.Ico (Q + 1) U,
      ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
        fixedAwayUnshiftedDyadicMultiplier t δ K ((p + 1 : ℕ) : ℝ)‖) ≤
      8 * fixedAwayDerivativeCauchyConstant t δ * (Q : ℝ) ^ 2 /
        (K : ℝ) := by
  let D : ℝ := 8 * fixedAwayDerivativeCauchyConstant t δ * (Q : ℝ) /
    (K : ℝ)
  have hpoint : ∀ p ∈ Finset.Ico (Q + 1) U,
      ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
        fixedAwayUnshiftedDyadicMultiplier t δ K ((p + 1 : ℕ) : ℝ)‖ ≤ D := by
    intro p hp
    have hpBounds := Finset.mem_Ico.mp hp
    apply norm_fixedAwayUnshiftedDyadicMultiplier_sub_succ_le_lowShell
      (U := U) (p := p) hδ hδt hK hQ
    · omega
    · omega
    · exact hU2Q
  have hcard : (Finset.Ico (Q + 1) U).card ≤ Q := by
    rw [Nat.card_Ico]
    omega
  calc
    (∑ p ∈ Finset.Ico (Q + 1) U,
        ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
          fixedAwayUnshiftedDyadicMultiplier t δ K ((p + 1 : ℕ) : ℝ)‖) ≤
      ∑ _p ∈ Finset.Ico (Q + 1) U, D := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpoint p hp
    _ = ((Finset.Ico (Q + 1) U).card : ℝ) * D := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * D := by
      have hD : 0 ≤ D := by
        dsimp [D]
        exact div_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num)
              (fixedAwayDerivativeCauchyConstant_nonneg t δ))
            (Nat.cast_nonneg Q))
          (Nat.cast_nonneg K)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hD
    _ = 8 * fixedAwayDerivativeCauchyConstant t δ * (Q : ℝ) ^ 2 /
        (K : ℝ) := by
      dsimp [D]
      ring

/-- Explicit constant for one complete or terminal denominator shell lying
below `sqrt K`. -/
def fixedAwayUnshiftedLowShellConstant (t δ : ℝ) : ℝ :=
  2 * Real.sqrt 42 *
    (4 * fixedAwayPVInverseDecayConstant t δ +
      8 * fixedAwayDerivativeCauchyConstant t δ)

theorem fixedAwayUnshiftedLowShellConstant_nonneg (t δ : ℝ) :
    0 ≤ fixedAwayUnshiftedLowShellConstant t δ := by
  unfold fixedAwayUnshiftedLowShellConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg 42))
    (add_nonneg
      (mul_nonneg (by norm_num) (fixedAwayPVInverseDecayConstant_nonneg t δ))
      (mul_nonneg (by norm_num)
        (fixedAwayDerivativeCauchyConstant_nonneg t δ)))

/-- Fully unconditional fixed-away Abel estimate below the square-root
transition.  The arithmetic input here is the already-proved elementary
finite Ramanujan tail, not Chan--Kumchev. -/
theorem norm_fixedAwayUnshiftedFiniteVector_le_lowShell
    {t δ : ℝ} {K Q U : ℕ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hQ : 0 < Q)
    (hQU : Q + 1 ≤ U) (hU2Q : U ≤ 2 * Q)
    (hUK : U ^ 2 ≤ K) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U‖ ≤
      fixedAwayUnshiftedLowShellConstant t δ *
        (Q : ℝ) / Real.sqrt (K : ℝ) := by
  let M : ℝ := 2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)
  have hpartial : ∀ R ∈ Finset.Icc (Q + 1) U,
      ‖euclideanIntervalPartialSum (nearRamanujanVectorTerm K) (Q + 1) R‖ ≤ M := by
    intro R hR
    dsimp [M]
    exact norm_euclideanIntervalPartialSum_nearRamanujan_tail_le_lowRange
      K Q U R hQ hUK hR
  have habel := norm_euclidean_vector_sum_coordinateMul_le
    (nearRamanujanVectorTerm K)
    (fun p ↦ fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))
    hQU M hpartial
  have hterminal := norm_fixedAwayUnshiftedDyadicMultiplier_le_lowShell
    hδ hδt hK hQ (by omega : Q < U) hU2Q
  have hvariation :=
    sum_norm_fixedAwayUnshiftedDyadicMultiplier_sub_succ_le_lowShell
      hδ hδt.le hK hQ hQU hU2Q
  have hsum :
      ‖fixedAwayUnshiftedDyadicMultiplier t δ K (U : ℝ)‖ +
          ∑ p ∈ Finset.Ico (Q + 1) U,
            ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
              fixedAwayUnshiftedDyadicMultiplier t δ K
                ((p + 1 : ℕ) : ℝ)‖ ≤
        (4 * fixedAwayPVInverseDecayConstant t δ +
          8 * fixedAwayDerivativeCauchyConstant t δ) *
            (Q : ℝ) ^ 2 / (K : ℝ) := by
    calc
      ‖fixedAwayUnshiftedDyadicMultiplier t δ K (U : ℝ)‖ +
          ∑ p ∈ Finset.Ico (Q + 1) U,
            ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
              fixedAwayUnshiftedDyadicMultiplier t δ K
                ((p + 1 : ℕ) : ℝ)‖ ≤
        4 * fixedAwayPVInverseDecayConstant t δ * (Q : ℝ) ^ 2 /
            (K : ℝ) +
          8 * fixedAwayDerivativeCauchyConstant t δ * (Q : ℝ) ^ 2 /
            (K : ℝ) := add_le_add hterminal hvariation
      _ = (4 * fixedAwayPVInverseDecayConstant t δ +
          8 * fixedAwayDerivativeCauchyConstant t δ) *
            (Q : ℝ) ^ 2 / (K : ℝ) := by ring
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hsqrtK : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.2 hKR
  change ‖∑ p ∈ Finset.Icc (Q + 1) U,
      euclideanCoordinateMul (nearRamanujanVectorTerm K p)
        (fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))‖ ≤ _
  calc
    ‖∑ p ∈ Finset.Icc (Q + 1) U,
        euclideanCoordinateMul (nearRamanujanVectorTerm K p)
          (fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))‖ ≤
      M *
        (‖fixedAwayUnshiftedDyadicMultiplier t δ K (U : ℝ)‖ +
          ∑ p ∈ Finset.Ico (Q + 1) U,
            ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
              fixedAwayUnshiftedDyadicMultiplier t δ K
                ((p + 1 : ℕ) : ℝ)‖) := habel
    _ ≤ M * ((4 * fixedAwayPVInverseDecayConstant t δ +
          8 * fixedAwayDerivativeCauchyConstant t δ) *
            (Q : ℝ) ^ 2 / (K : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hM
    _ = fixedAwayUnshiftedLowShellConstant t δ *
        (Q : ℝ) / Real.sqrt (K : ℝ) := by
      dsimp [M, fixedAwayUnshiftedLowShellConstant]
      have hQR0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
      have hKR0 : (K : ℝ) ≠ 0 := hKR.ne'
      field_simp [hsqrtK.ne', hQR0, hKR0]
      rw [Real.sq_sqrt hKR.le]
      ring

/-! ## Geometric aggregation below the square-root transition -/

/-- Complete dyadic denominator shells `1 < p ≤ 2^R` on one frequency
block.  The denominator `p = 1` is deliberately kept separate, since it is
a single explicit coefficient rather than a Ramanujan tail. -/
def fixedAwayUnshiftedLowDyadicVector
    (t δ : ℝ) (K R : ℕ) : NearDyadicEuclidean K :=
  ∑ r ∈ Finset.Ico 0 R,
    fixedAwayUnshiftedFiniteVector t δ K (2 ^ r + 1) (2 * 2 ^ r)

private theorem sum_pow_two_Ico_zero_le (R : ℕ) :
    (∑ r ∈ Finset.Ico 0 R, (2 : ℝ) ^ r) ≤ (2 : ℝ) ^ R := by
  rw [Finset.sum_Ico_eq_sub (fun r : ℕ ↦ (2 : ℝ) ^ r) (Nat.zero_le R)]
  rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1),
    geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
  norm_num

/-- All complete denominator shells below `sqrt K` have total norm at most
the last-shell scale.  This is the complementary geometric sum to the
inverse-geometric high-shell estimate. -/
theorem norm_fixedAwayUnshiftedLowDyadicVector_le
    {t δ : ℝ} {K R : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (hK : 0 < K)
    (hRK : (2 ^ R) ^ 2 ≤ K) :
    ‖fixedAwayUnshiftedLowDyadicVector t δ K R‖ ≤
      fixedAwayUnshiftedLowShellConstant t δ *
        ((2 ^ R : ℕ) : ℝ) / Real.sqrt (K : ℝ) := by
  have hC : 0 ≤ fixedAwayUnshiftedLowShellConstant t δ :=
    fixedAwayUnshiftedLowShellConstant_nonneg t δ
  have hshell : ∀ r ∈ Finset.Ico 0 R,
      ‖fixedAwayUnshiftedFiniteVector
          t δ K (2 ^ r + 1) (2 * 2 ^ r)‖ ≤
        fixedAwayUnshiftedLowShellConstant t δ *
          ((2 ^ r : ℕ) : ℝ) / Real.sqrt (K : ℝ) := by
    intro r hr
    have hrBounds := Finset.mem_Ico.mp hr
    have hrOne : r + 1 ≤ R := by omega
    have hUle : 2 * 2 ^ r ≤ 2 ^ R := by
      have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) hrOne
      simpa only [pow_succ, Nat.mul_comm] using! hpow
    have hUK : (2 * 2 ^ r) ^ 2 ≤ K :=
      (Nat.pow_le_pow_left hUle 2).trans hRK
    have hpowPos : 0 < 2 ^ r := by positivity
    exact norm_fixedAwayUnshiftedFiniteVector_le_lowShell
      hδ hδt hK hpowPos (by omega) le_rfl hUK
  unfold fixedAwayUnshiftedLowDyadicVector
  calc
    ‖∑ r ∈ Finset.Ico 0 R,
        fixedAwayUnshiftedFiniteVector
          t δ K (2 ^ r + 1) (2 * 2 ^ r)‖ ≤
      ∑ r ∈ Finset.Ico 0 R,
        ‖fixedAwayUnshiftedFiniteVector
          t δ K (2 ^ r + 1) (2 * 2 ^ r)‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.Ico 0 R,
        fixedAwayUnshiftedLowShellConstant t δ *
          ((2 ^ r : ℕ) : ℝ) / Real.sqrt (K : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hshell r hr
    _ = fixedAwayUnshiftedLowShellConstant t δ /
          Real.sqrt (K : ℝ) *
        (∑ r ∈ Finset.Ico 0 R, (2 : ℝ) ^ r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      ring
    _ ≤ fixedAwayUnshiftedLowShellConstant t δ /
          Real.sqrt (K : ℝ) * (2 : ℝ) ^ R := by
      apply mul_le_mul_of_nonneg_left (sum_pow_two_Ico_zero_le R)
      positivity
    _ = fixedAwayUnshiftedLowShellConstant t δ *
          ((2 ^ R : ℕ) : ℝ) / Real.sqrt (K : ℝ) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      ring

/-- The complete low dyadic sum is exactly the single denominator interval
`1 < p ≤ 2^R`; this records all shared endpoints explicitly. -/
theorem fixedAwayUnshiftedLowDyadicVector_eq_interval
    (t δ : ℝ) (K R : ℕ) :
    fixedAwayUnshiftedLowDyadicVector t δ K R =
      fixedAwayUnshiftedFiniteVector t δ K 2 (2 ^ R) := by
  induction R with
  | zero =>
      simp [fixedAwayUnshiftedLowDyadicVector,
        fixedAwayUnshiftedFiniteVector]
  | succ R ih =>
      let f : ℕ → NearDyadicEuclidean K := fun p ↦
        euclideanCoordinateMul (nearRamanujanVectorTerm K p)
          (fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))
      have hstep :
          fixedAwayUnshiftedLowDyadicVector t δ K (R + 1) =
            fixedAwayUnshiftedLowDyadicVector t δ K R +
              fixedAwayUnshiftedFiniteVector
                t δ K (2 ^ R + 1) (2 ^ (R + 1)) := by
        unfold fixedAwayUnshiftedLowDyadicVector
        rw [Finset.sum_Ico_succ_top (Nat.zero_le R)]
        congr 2
        simp only [pow_succ]
        ring
      rw [hstep, ih]
      rw [fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K 1,
        fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K (2 ^ R),
        fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K 1]
      exact Finset.sum_Ioc_consecutive f Nat.one_le_two_pow
        (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega))

/-- Endpoint-flexible aggregation of every denominator `1 < p ≤ U` below
the square-root transition.  A floor dyadic logarithm leaves at most one
partial final shell, and the factor two is displayed. -/
theorem norm_fixedAwayUnshiftedFiniteVector_two_le_lowRange
    {t δ : ℝ} (K U : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) (hK : 0 < K)
    (hU : 1 ≤ U) (hUK : U ^ 2 ≤ K) :
    ‖fixedAwayUnshiftedFiniteVector t δ K 2 U‖ ≤
      2 * fixedAwayUnshiftedLowShellConstant t δ *
        (U : ℝ) / Real.sqrt (K : ℝ) := by
  have hC : 0 ≤ fixedAwayUnshiftedLowShellConstant t δ :=
    fixedAwayUnshiftedLowShellConstant_nonneg t δ
  by_cases hUone : U = 1
  · subst U
    simp only [fixedAwayUnshiftedFiniteVector,
      Finset.Icc_eq_empty (by omega : ¬(2 : ℕ) ≤ 1),
      Finset.sum_empty, norm_zero, Nat.cast_one, mul_one]
    exact div_nonneg (mul_nonneg (by norm_num) hC) (Real.sqrt_nonneg _)
  · have hUtwo : 2 ≤ U := by omega
    let m : ℕ := Nat.log 2 U
    let Q : ℕ := 2 ^ m
    have hUne : U ≠ 0 := by omega
    have hm : 1 ≤ m := by
      dsimp [m]
      exact Nat.log_pos Nat.one_lt_two hUtwo
    have hQ : 0 < Q := by dsimp [Q]; positivity
    have hQU : Q ≤ U := by
      dsimp [Q, m]
      exact Nat.pow_log_le_self 2 hUne
    have hU2Q : U ≤ 2 * Q := by
      have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two U
      dsimp [Q, m]
      rw [pow_succ] at hlt
      omega
    have hQK : Q ^ 2 ≤ K :=
      (Nat.pow_le_pow_left hQU 2).trans hUK
    have hlow :
        ‖fixedAwayUnshiftedFiniteVector t δ K 2 Q‖ ≤
          fixedAwayUnshiftedLowShellConstant t δ *
            (Q : ℝ) / Real.sqrt (K : ℝ) := by
      have hraw := norm_fixedAwayUnshiftedLowDyadicVector_le
        hδ hδt hK (by simpa only [Q] using! hQK)
      rw [fixedAwayUnshiftedLowDyadicVector_eq_interval] at hraw
      simpa only [Q] using! hraw
    have hreplace :
        fixedAwayUnshiftedLowShellConstant t δ * (Q : ℝ) /
            Real.sqrt (K : ℝ) ≤
          fixedAwayUnshiftedLowShellConstant t δ * (U : ℝ) /
            Real.sqrt (K : ℝ) := by
      gcongr
    by_cases hQUeq : Q = U
    · rw [← hQUeq]
      calc
        ‖fixedAwayUnshiftedFiniteVector t δ K 2 Q‖ ≤
            fixedAwayUnshiftedLowShellConstant t δ * (Q : ℝ) /
              Real.sqrt (K : ℝ) := hlow
        _ ≤ 2 * fixedAwayUnshiftedLowShellConstant t δ * (Q : ℝ) /
              Real.sqrt (K : ℝ) := by
          have hnonneg : 0 ≤ fixedAwayUnshiftedLowShellConstant t δ *
              (Q : ℝ) / Real.sqrt (K : ℝ) := by positivity
          calc
            fixedAwayUnshiftedLowShellConstant t δ * (Q : ℝ) /
                Real.sqrt (K : ℝ) ≤
              2 * (fixedAwayUnshiftedLowShellConstant t δ * (Q : ℝ) /
                Real.sqrt (K : ℝ)) := by nlinarith
            _ = 2 * fixedAwayUnshiftedLowShellConstant t δ * (Q : ℝ) /
                Real.sqrt (K : ℝ) := by ring
    · have hQltU : Q < U := hQU.lt_of_ne hQUeq
      have hpartial := norm_fixedAwayUnshiftedFiniteVector_le_lowShell
        hδ hδt hK hQ (by omega) hU2Q hUK
      have hdisjoint : Disjoint (Finset.Ioc 1 Q) (Finset.Ioc Q U) := by
        rw [Finset.disjoint_left]
        intro p hpLeft hpRight
        have hl := Finset.mem_Ioc.mp hpLeft
        have hr := Finset.mem_Ioc.mp hpRight
        omega
      have hsplit :
          fixedAwayUnshiftedFiniteVector t δ K 2 U =
            fixedAwayUnshiftedFiniteVector t δ K 2 Q +
              fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U := by
        rw [fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K 1,
          fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K 1,
          fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K Q]
        rw [← Finset.sum_union hdisjoint]
        rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega : 1 ≤ Q) hQltU.le]
      rw [hsplit]
      calc
        ‖fixedAwayUnshiftedFiniteVector t δ K 2 Q +
            fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U‖ ≤
          ‖fixedAwayUnshiftedFiniteVector t δ K 2 Q‖ +
            ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U‖ :=
          norm_add_le _ _
        _ ≤ fixedAwayUnshiftedLowShellConstant t δ * (Q : ℝ) /
              Real.sqrt (K : ℝ) +
            fixedAwayUnshiftedLowShellConstant t δ * (Q : ℝ) /
              Real.sqrt (K : ℝ) := add_le_add hlow hpartial
        _ = 2 * (fixedAwayUnshiftedLowShellConstant t δ * (Q : ℝ) /
              Real.sqrt (K : ℝ)) := by ring
        _ ≤ 2 * (fixedAwayUnshiftedLowShellConstant t δ * (U : ℝ) /
              Real.sqrt (K : ℝ)) :=
          mul_le_mul_of_nonneg_left hreplace (by norm_num)
        _ = 2 * fixedAwayUnshiftedLowShellConstant t δ * (U : ℝ) /
              Real.sqrt (K : ℝ) := by ring

/-! ## Multiplier bounds above the square-root transition -/

/-- On `Q < x <= 2Q`, the elementary zeroth derivative bound gives a
uniform `K/Q³` estimate for the reciprocal-square composite. -/
theorem norm_deriv_fixedAwayUnshiftedReciprocalSquare_le_highShell
    {t δ K Q n x : ℝ}
    (hδ : 0 < δ) (hδt : δ ≤ t)
    (hK : 0 < K) (hn : 0 < n) (hnK : n ≤ 2 * K)
    (hQ : 0 < Q) (hxQ : Q ≤ x) :
    ‖deriv
      (fun y : ℝ ↦ fixedAwayPVTransform
        (fixedAwaySmoothCorrection t δ) t (n / y ^ 2)) x‖ ≤
      4 * fixedAwayDerivativeBound0 t δ * K / Q ^ 3 := by
  have hx : 0 < x := hQ.trans_le hxQ
  have harg : n / x ^ 2 ≠ 0 := div_ne_zero hn.ne' (pow_ne_zero 2 hx.ne')
  have hcomp := hasDerivAt_fixedAwayUnshiftedReciprocalSquare
    hδ hδt hn hx.ne'
  rw [hcomp.deriv, norm_smul,
    norm_neg_two_mul_div_cube hn.le hx]
  have houterRaw := fixedAwayPVTransform_smooth_deriv_polynomial
    hδ hδt 0 (n / x ^ 2) harg
  have houter :
      ‖deriv (fixedAwayPVTransform
          (fixedAwaySmoothCorrection t δ) t) (n / x ^ 2)‖ ≤
        fixedAwayDerivativeBound0 t δ := by
    simpa only [pow_zero, one_mul, fixedAwayDerivativeBound0] using! houterRaw
  have hfactor : 2 * n / x ^ 3 ≤ 4 * K / Q ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hx 3) (pow_pos hQ 3)).2
    have hxPow : Q ^ 3 ≤ x ^ 3 := by gcongr
    calc
      2 * n * Q ^ 3 ≤ 2 * (2 * K) * Q ^ 3 := by gcongr
      _ = 4 * K * Q ^ 3 := by ring
      _ ≤ 4 * K * x ^ 3 :=
        mul_le_mul_of_nonneg_left hxPow (by positivity)
  have hD0 : 0 ≤ fixedAwayDerivativeBound0 t δ :=
    fixedAwayDerivativeBound0_nonneg t δ
  calc
    (2 * n / x ^ 3) *
        ‖deriv (fixedAwayPVTransform
          (fixedAwaySmoothCorrection t δ) t) (n / x ^ 2)‖ ≤
      (2 * n / x ^ 3) * fixedAwayDerivativeBound0 t δ :=
        mul_le_mul_of_nonneg_left houter (by positivity)
    _ ≤ (4 * K / Q ^ 3) * fixedAwayDerivativeBound0 t δ :=
      mul_le_mul_of_nonneg_right hfactor hD0
    _ = 4 * fixedAwayDerivativeBound0 t δ * K / Q ^ 3 := by ring

/-- The sampled multiplier is globally bounded, uniformly in the frequency
shell and denominator. -/
theorem norm_fixedAwayUnshiftedDyadicMultiplier_le_global
    {t δ : ℝ} {K U : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) :
    ‖fixedAwayUnshiftedDyadicMultiplier t δ K (U : ℝ)‖ ≤
      fixedAwayPVGlobalDecayConstant t δ := by
  have hC : 0 ≤ fixedAwayPVGlobalDecayConstant t δ :=
    fixedAwayPVGlobalDecayConstant_nonneg t δ
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro n
  have hraw := norm_fixedAwayPVTransform_smooth_le_globalDecay
    hδ hδt (((n : ℕ) : ℝ) / (U : ℝ) ^ 2)
  have hinv : (1 + |((n : ℕ) : ℝ) / (U : ℝ) ^ 2|)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (le_add_of_nonneg_right (abs_nonneg _))
  exact hraw.trans (by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left hinv hC)

/-- One discrete multiplier increment in a high denominator shell. -/
theorem norm_fixedAwayUnshiftedDyadicMultiplier_sub_succ_le_highShell
    {t δ : ℝ} {K Q p : ℕ}
    (hδ : 0 < δ) (hδt : δ ≤ t)
    (hK : 0 < K) (hQ : 0 < Q)
    (hQp : Q ≤ p) :
    ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
        fixedAwayUnshiftedDyadicMultiplier t δ K ((p + 1 : ℕ) : ℝ)‖ ≤
      4 * fixedAwayDerivativeBound0 t δ * (K : ℝ) / (Q : ℝ) ^ 3 := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hpR : (0 : ℝ) < p := by exact_mod_cast hQ.trans_le hQp
  have hright :
      0 ≤ 4 * fixedAwayDerivativeBound0 t δ * (K : ℝ) /
        (Q : ℝ) ^ 3 := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (fixedAwayDerivativeBound0_nonneg t δ))
        (Nat.cast_nonneg K))
      (by positivity)
  apply (pi_norm_le_iff_of_nonneg hright).mpr
  intro n
  let f : ℝ → ℂ := fun x ↦ fixedAwayPVTransform
    (fixedAwaySmoothCorrection t δ) t (((n : ℕ) : ℝ) / x ^ 2)
  have hnBounds := Finset.mem_Ioc.mp n.property
  have hnR : (0 : ℝ) < (n : ℕ) := by exact_mod_cast hK.trans hnBounds.1
  have hdiff : ∀ x ∈ Set.Icc (p : ℝ) ((p + 1 : ℕ) : ℝ),
      DifferentiableAt ℝ f x := by
    intro x hx
    apply differentiableAt_fixedAwayUnshiftedReciprocalSquare hδ hδt hnR
    exact hpR.trans_le hx.1
  have hbound : ∀ x ∈ Set.Icc (p : ℝ) ((p + 1 : ℕ) : ℝ),
      ‖deriv f x‖ ≤
        4 * fixedAwayDerivativeBound0 t δ * (K : ℝ) / (Q : ℝ) ^ 3 := by
    intro x hx
    apply norm_deriv_fixedAwayUnshiftedReciprocalSquare_le_highShell
      hδ hδt hKR hnR
    · exact_mod_cast hnBounds.2
    · exact hQR
    · have hQpR : (Q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hQp
      exact hQpR.trans hx.1
  have hpMem : (p : ℝ) ∈ Set.Icc (p : ℝ) ((p + 1 : ℕ) : ℝ) := by
    constructor <;> norm_num
  have hpSuccMem : ((p + 1 : ℕ) : ℝ) ∈
      Set.Icc (p : ℝ) ((p + 1 : ℕ) : ℝ) := by
    constructor <;> norm_num
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (convex_Icc _ _) hpMem hpSuccMem
  change ‖f (p : ℝ) - f ((p + 1 : ℕ) : ℝ)‖ ≤ _
  calc
    ‖f (p : ℝ) - f ((p + 1 : ℕ) : ℝ)‖ =
        ‖f ((p + 1 : ℕ) : ℝ) - f (p : ℝ)‖ := norm_sub_rev _ _
    _ ≤ (4 * fixedAwayDerivativeBound0 t δ * (K : ℝ) /
        (Q : ℝ) ^ 3) *
          ‖(((p + 1 : ℕ) : ℝ) - (p : ℝ))‖ := hmv
    _ = 4 * fixedAwayDerivativeBound0 t δ * (K : ℝ) /
        (Q : ℝ) ^ 3 := by norm_num

/-- Total variation on a high dyadic denominator shell. -/
theorem sum_norm_fixedAwayUnshiftedDyadicMultiplier_sub_succ_le_highShell
    {t δ : ℝ} {K Q U : ℕ}
    (hδ : 0 < δ) (hδt : δ ≤ t)
    (hK : 0 < K) (hQ : 0 < Q)
    (hQU : Q + 1 ≤ U) (hU2Q : U ≤ 2 * Q) :
    (∑ p ∈ Finset.Ico (Q + 1) U,
      ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
        fixedAwayUnshiftedDyadicMultiplier t δ K ((p + 1 : ℕ) : ℝ)‖) ≤
      4 * fixedAwayDerivativeBound0 t δ * (K : ℝ) / (Q : ℝ) ^ 2 := by
  let D : ℝ := 4 * fixedAwayDerivativeBound0 t δ * (K : ℝ) /
    (Q : ℝ) ^ 3
  have hpoint : ∀ p ∈ Finset.Ico (Q + 1) U,
      ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
        fixedAwayUnshiftedDyadicMultiplier t δ K ((p + 1 : ℕ) : ℝ)‖ ≤ D := by
    intro p hp
    have hpBounds := Finset.mem_Ico.mp hp
    apply norm_fixedAwayUnshiftedDyadicMultiplier_sub_succ_le_highShell
      (p := p) hδ hδt hK hQ
    · omega
  have hcard : (Finset.Ico (Q + 1) U).card ≤ Q := by
    rw [Nat.card_Ico]
    omega
  have hD : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (fixedAwayDerivativeBound0_nonneg t δ))
        (Nat.cast_nonneg K))
      (by positivity)
  calc
    (∑ p ∈ Finset.Ico (Q + 1) U,
        ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
          fixedAwayUnshiftedDyadicMultiplier t δ K ((p + 1 : ℕ) : ℝ)‖) ≤
      ∑ _p ∈ Finset.Ico (Q + 1) U, D := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpoint p hp
    _ = ((Finset.Ico (Q + 1) U).card : ℝ) * D := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * D := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hD
    _ = 4 * fixedAwayDerivativeBound0 t δ * (K : ℝ) / (Q : ℝ) ^ 2 := by
      dsimp [D]
      have hQR0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
      field_simp [hQR0]

/-- Above `sqrt K`, terminal value plus total variation is bounded by one
constant independent of the shell. -/
theorem fixedAwayUnshiftedDyadicMultiplier_terminal_add_variation_le_highShell
    {t δ : ℝ} {K Q U : ℕ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hQ : 0 < Q) (hKQ : K ≤ Q ^ 2)
    (hQU : Q + 1 ≤ U) (hU2Q : U ≤ 2 * Q) :
    ‖fixedAwayUnshiftedDyadicMultiplier t δ K (U : ℝ)‖ +
        ∑ p ∈ Finset.Ico (Q + 1) U,
          ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
            fixedAwayUnshiftedDyadicMultiplier t δ K
              ((p + 1 : ℕ) : ℝ)‖ ≤
      fixedAwayPVGlobalDecayConstant t δ +
        4 * fixedAwayDerivativeBound0 t δ := by
  have hterminal := norm_fixedAwayUnshiftedDyadicMultiplier_le_global
    (K := K) (U := U) hδ hδt
  have hvariation :=
    sum_norm_fixedAwayUnshiftedDyadicMultiplier_sub_succ_le_highShell
      hδ hδt.le hK hQ hQU hU2Q
  have hKQReal : (K : ℝ) ≤ (Q : ℝ) ^ 2 := by exact_mod_cast hKQ
  have hQsqPos : 0 < (Q : ℝ) ^ 2 := by positivity
  have hD0 : 0 ≤ 4 * fixedAwayDerivativeBound0 t δ :=
    mul_nonneg (by norm_num) (fixedAwayDerivativeBound0_nonneg t δ)
  have hscaled :
      4 * fixedAwayDerivativeBound0 t δ * (K : ℝ) / (Q : ℝ) ^ 2 ≤
        4 * fixedAwayDerivativeBound0 t δ := by
    apply (div_le_iff₀ hQsqPos).2
    nlinarith
  exact (add_le_add hterminal hvariation).trans (add_le_add le_rfl hscaled)

def fixedAwayUnshiftedHighMultiplierConstant (t δ : ℝ) : ℝ :=
  fixedAwayPVGlobalDecayConstant t δ +
    4 * fixedAwayDerivativeBound0 t δ

theorem fixedAwayUnshiftedHighMultiplierConstant_nonneg (t δ : ℝ) :
    0 ≤ fixedAwayUnshiftedHighMultiplierConstant t δ := by
  unfold fixedAwayUnshiftedHighMultiplierConstant
  exact add_nonneg (fixedAwayPVGlobalDecayConstant_nonneg t δ)
    (mul_nonneg (by norm_num) (fixedAwayDerivativeBound0_nonneg t δ))

/-- Slightly enlarged multiplier constant at the unique square-root
transition shell.  The natural integer floor only gives `K ≤ 4 Q²`, and
this definition records the resulting factor four rather than silently
rounding `sqrt K`. -/
def fixedAwayUnshiftedTransitionMultiplierConstant (t δ : ℝ) : ℝ :=
  fixedAwayPVGlobalDecayConstant t δ +
    16 * fixedAwayDerivativeBound0 t δ

theorem fixedAwayUnshiftedTransitionMultiplierConstant_nonneg (t δ : ℝ) :
    0 ≤ fixedAwayUnshiftedTransitionMultiplierConstant t δ := by
  unfold fixedAwayUnshiftedTransitionMultiplierConstant
  exact add_nonneg (fixedAwayPVGlobalDecayConstant_nonneg t δ)
    (mul_nonneg (by norm_num) (fixedAwayDerivativeBound0_nonneg t δ))

/-- Terminal value plus variation on the square-root transition shell,
with the exact rounded inequality `K ≤ 4Q²`. -/
theorem
    fixedAwayUnshiftedDyadicMultiplier_terminal_add_variation_le_transitionShell
    {t δ : ℝ} {K Q U : ℕ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hQ : 0 < Q) (hKQ : K ≤ 4 * Q ^ 2)
    (hQU : Q + 1 ≤ U) (hU2Q : U ≤ 2 * Q) :
    ‖fixedAwayUnshiftedDyadicMultiplier t δ K (U : ℝ)‖ +
        ∑ p ∈ Finset.Ico (Q + 1) U,
          ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
            fixedAwayUnshiftedDyadicMultiplier t δ K
              ((p + 1 : ℕ) : ℝ)‖ ≤
      fixedAwayUnshiftedTransitionMultiplierConstant t δ := by
  have hterminal := norm_fixedAwayUnshiftedDyadicMultiplier_le_global
    (K := K) (U := U) hδ hδt
  have hvariation :=
    sum_norm_fixedAwayUnshiftedDyadicMultiplier_sub_succ_le_highShell
      hδ hδt.le hK hQ hQU hU2Q
  have hKQReal : (K : ℝ) ≤ 4 * (Q : ℝ) ^ 2 := by exact_mod_cast hKQ
  have hQsqPos : 0 < (Q : ℝ) ^ 2 := by positivity
  have hD0 : 0 ≤ 4 * fixedAwayDerivativeBound0 t δ :=
    mul_nonneg (by norm_num) (fixedAwayDerivativeBound0_nonneg t δ)
  have hscaled :
      4 * fixedAwayDerivativeBound0 t δ * (K : ℝ) / (Q : ℝ) ^ 2 ≤
        16 * fixedAwayDerivativeBound0 t δ := by
    apply (div_le_iff₀ hQsqPos).2
    nlinarith
  exact (add_le_add hterminal hvariation).trans (add_le_add le_rfl hscaled)

/-- Analytic consequence of a source-faithful Ramanujan prefix estimate on
one denominator shell above `sqrt K`.  This theorem proves all Abel and
multiplier work; the only argument not produced here is the named arithmetic
estimate `hCK`. -/
theorem norm_fixedAwayUnshiftedFiniteVector_le_highShell_of_prefixEstimate
    (C : ℝ) {t δ : ℝ} {K T Q U : ℕ}
    (hCK : RamanujanPrefixL2Estimate C K T)
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hQ : 0 < Q) (hKQ : K ≤ Q ^ 2)
    (hQU : Q + 1 ≤ U) (hU2Q : U ≤ 2 * Q) (hUT : U ≤ T) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U‖ ≤
      (6 * C * Real.sqrt (K : ℝ) / (Q : ℝ)) *
        fixedAwayUnshiftedHighMultiplierConstant t δ := by
  let M : ℝ := 6 * C * Real.sqrt (K : ℝ) / (Q : ℝ)
  have hpartial : ∀ R ∈ Finset.Icc (Q + 1) U,
      ‖euclideanIntervalPartialSum (nearRamanujanVectorTerm K) (Q + 1) R‖ ≤ M := by
    intro R hR
    have hRBounds := Finset.mem_Icc.mp hR
    have hQR : Q < R := by omega
    have hRT : R ≤ T := hRBounds.2.trans hUT
    dsimp [M]
    simpa only [euclideanIntervalPartialSum] using!
      norm_sum_nearRamanujanVectorTerm_tail_le_of_prefixEstimate
        C K T Q R hCK hQ hQR hRT
  have habel := norm_euclidean_vector_sum_coordinateMul_le
    (nearRamanujanVectorTerm K)
    (fun p ↦ fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))
    hQU M hpartial
  have hmult :=
    fixedAwayUnshiftedDyadicMultiplier_terminal_add_variation_le_highShell
      hδ hδt hK hQ hKQ hQU hU2Q
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCK.1) (Real.sqrt_nonneg _))
      (Nat.cast_nonneg Q)
  change ‖∑ p ∈ Finset.Icc (Q + 1) U,
      euclideanCoordinateMul (nearRamanujanVectorTerm K p)
        (fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))‖ ≤ _
  calc
    ‖∑ p ∈ Finset.Icc (Q + 1) U,
        euclideanCoordinateMul (nearRamanujanVectorTerm K p)
          (fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))‖ ≤
      M *
        (‖fixedAwayUnshiftedDyadicMultiplier t δ K (U : ℝ)‖ +
          ∑ p ∈ Finset.Ico (Q + 1) U,
            ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
              fixedAwayUnshiftedDyadicMultiplier t δ K
                ((p + 1 : ℕ) : ℝ)‖) := habel
    _ ≤ M * fixedAwayUnshiftedHighMultiplierConstant t δ := by
      exact mul_le_mul_of_nonneg_left hmult hM
    _ = (6 * C * Real.sqrt (K : ℝ) / (Q : ℝ)) *
        fixedAwayUnshiftedHighMultiplierConstant t δ := rfl

/-- One source-faithful shell starting at the rounded square-root
transition.  This differs from the preceding theorem only in the explicit
`K ≤ 4Q²` rounding constant. -/
theorem
    norm_fixedAwayUnshiftedFiniteVector_le_transitionShell_of_prefixEstimate
    (C : ℝ) {t δ : ℝ} {K T Q U : ℕ}
    (hCK : RamanujanPrefixL2Estimate C K T)
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hQ : 0 < Q) (hKQ : K ≤ 4 * Q ^ 2)
    (hQU : Q + 1 ≤ U) (hU2Q : U ≤ 2 * Q) (hUT : U ≤ T) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U‖ ≤
      (6 * C * Real.sqrt (K : ℝ) / (Q : ℝ)) *
        fixedAwayUnshiftedTransitionMultiplierConstant t δ := by
  let M : ℝ := 6 * C * Real.sqrt (K : ℝ) / (Q : ℝ)
  have hpartial : ∀ R ∈ Finset.Icc (Q + 1) U,
      ‖euclideanIntervalPartialSum (nearRamanujanVectorTerm K) (Q + 1) R‖ ≤ M := by
    intro R hR
    have hRBounds := Finset.mem_Icc.mp hR
    have hQR : Q < R := by omega
    have hRT : R ≤ T := hRBounds.2.trans hUT
    dsimp [M]
    simpa only [euclideanIntervalPartialSum] using!
      norm_sum_nearRamanujanVectorTerm_tail_le_of_prefixEstimate
        C K T Q R hCK hQ hQR hRT
  have habel := norm_euclidean_vector_sum_coordinateMul_le
    (nearRamanujanVectorTerm K)
    (fun p ↦ fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))
    hQU M hpartial
  have hmult :=
    fixedAwayUnshiftedDyadicMultiplier_terminal_add_variation_le_transitionShell
      hδ hδt hK hQ hKQ hQU hU2Q
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCK.1) (Real.sqrt_nonneg _))
      (Nat.cast_nonneg Q)
  change ‖∑ p ∈ Finset.Icc (Q + 1) U,
      euclideanCoordinateMul (nearRamanujanVectorTerm K p)
        (fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))‖ ≤ _
  calc
    ‖∑ p ∈ Finset.Icc (Q + 1) U,
        euclideanCoordinateMul (nearRamanujanVectorTerm K p)
          (fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))‖ ≤
      M *
        (‖fixedAwayUnshiftedDyadicMultiplier t δ K (U : ℝ)‖ +
          ∑ p ∈ Finset.Ico (Q + 1) U,
            ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
              fixedAwayUnshiftedDyadicMultiplier t δ K
                ((p + 1 : ℕ) : ℝ)‖) := habel
    _ ≤ M * fixedAwayUnshiftedTransitionMultiplierConstant t δ :=
      mul_le_mul_of_nonneg_left hmult hM
    _ = (6 * C * Real.sqrt (K : ℝ) / (Q : ℝ)) *
        fixedAwayUnshiftedTransitionMultiplierConstant t δ := rfl

/-- The completely proved divisor-square endpoint for terminal shells.  Its
explicit harmonic loss is retained and is later multiplied by the geometric
factor `sqrt K / Q`. -/
theorem norm_fixedAwayUnshiftedFiniteVector_le_highShell_divisorSquare
    {t δ : ℝ} {K Q U : ℕ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hQ : 0 < Q) (hKQ : K ≤ Q ^ 2)
    (hQU : Q + 1 ≤ U) (hU2Q : U ≤ 2 * Q) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U‖ ≤
      (6 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (Q : ℝ)) *
        fixedAwayUnshiftedHighMultiplierConstant t δ := by
  let hCK := (chanKumchevInitialSecondMomentEstimate_divisorSquare K U).toDyadic.toL2
  exact norm_fixedAwayUnshiftedFiniteVector_le_highShell_of_prefixEstimate
    (Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3)) hCK
      hδ hδt hK hQ hKQ hQU hU2Q le_rfl

/-! ## Geometric aggregation above the square-root transition -/

/-- If the source-faithful prefix estimate is available up to `T`, then all
denominator shells between `P` and an arbitrary `U ≤ T` are geometrically
summable.  The proof recursively exposes every finite Abel endpoint.  In
particular, there is no logarithmic loss from the number of denominator
shells. -/
theorem norm_fixedAwayUnshiftedFiniteVector_tail_le_highShell_of_prefixEstimate
    (C : ℝ) {t δ : ℝ} (K T P U : ℕ)
    (hCK : RamanujanPrefixL2Estimate C K T)
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hP : 0 < P) (hKP : K ≤ P ^ 2)
    (hPU : P < U) (hUT : U ≤ T) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) U‖ ≤
      (12 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
        fixedAwayUnshiftedHighMultiplierConstant t δ := by
  by_cases hU2P : U ≤ 2 * P
  · have hshell :=
      norm_fixedAwayUnshiftedFiniteVector_le_highShell_of_prefixEstimate
        C hCK hδ hδt hK hP hKP (by omega) hU2P hUT
    have hbase :
        0 ≤ (6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
          fixedAwayUnshiftedHighMultiplierConstant t δ := by
      exact mul_nonneg
        (div_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hCK.1)
            (Real.sqrt_nonneg _))
          (Nat.cast_nonneg P))
        (fixedAwayUnshiftedHighMultiplierConstant_nonneg t δ)
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) U‖ ≤
          (6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedHighMultiplierConstant t δ := hshell
      _ ≤ 2 * ((6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedHighMultiplierConstant t δ) := by
        nlinarith
      _ = (12 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedHighMultiplierConstant t δ := by ring
  · have h2PU : 2 * P < U := lt_of_not_ge hU2P
    have h2P : 0 < 2 * P := by positivity
    have hK2P : K ≤ (2 * P) ^ 2 := by nlinarith
    have h2PT : 2 * P ≤ T := h2PU.le.trans hUT
    have hleft :=
      norm_fixedAwayUnshiftedFiniteVector_le_highShell_of_prefixEstimate
        C hCK hδ hδt hK hP hKP (by omega) le_rfl h2PT
    have hright :=
      norm_fixedAwayUnshiftedFiniteVector_tail_le_highShell_of_prefixEstimate
        C K T (2 * P) U hCK hδ hδt hK h2P hK2P h2PU hUT
    have hdisjoint : Disjoint (Finset.Ioc P (2 * P))
        (Finset.Ioc (2 * P) U) := by
      rw [Finset.disjoint_left]
      intro p hpLeft hpRight
      have hl := Finset.mem_Ioc.mp hpLeft
      have hr := Finset.mem_Ioc.mp hpRight
      omega
    have hsplit :
        fixedAwayUnshiftedFiniteVector t δ K (P + 1) U =
          fixedAwayUnshiftedFiniteVector t δ K (P + 1) (2 * P) +
            fixedAwayUnshiftedFiniteVector t δ K (2 * P + 1) U := by
      rw [fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
        fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
        fixedAwayUnshiftedFiniteVector_eq_sum_Ioc]
      rw [← Finset.sum_union hdisjoint]
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) h2PU.le]
    rw [hsplit]
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) (2 * P) +
          fixedAwayUnshiftedFiniteVector t δ K (2 * P + 1) U‖ ≤
        ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) (2 * P)‖ +
          ‖fixedAwayUnshiftedFiniteVector t δ K (2 * P + 1) U‖ :=
        norm_add_le _ _
      _ ≤ (6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedHighMultiplierConstant t δ +
          (12 * C * Real.sqrt (K : ℝ) / ((2 * P : ℕ) : ℝ)) *
            fixedAwayUnshiftedHighMultiplierConstant t δ :=
        add_le_add hleft hright
      _ = (12 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedHighMultiplierConstant t δ := by
        push_cast
        field_simp
        ring
termination_by U - P
decreasing_by omega

/-- Geometric high tail beginning at the integer square-root floor.  Only
the first shell pays the rounded `K ≤ 4P²` constant; every subsequent shell
uses the sharper high-range theorem. -/
theorem
    norm_fixedAwayUnshiftedFiniteVector_tail_le_transition_of_prefixEstimate
    (C : ℝ) {t δ : ℝ} (K T P U : ℕ)
    (hCK : RamanujanPrefixL2Estimate C K T)
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hP : 0 < P) (hKP : K ≤ 4 * P ^ 2)
    (hPU : P < U) (hUT : U ≤ T) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) U‖ ≤
      (12 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
        fixedAwayUnshiftedTransitionMultiplierConstant t δ := by
  have hHighTrans : fixedAwayUnshiftedHighMultiplierConstant t δ ≤
      fixedAwayUnshiftedTransitionMultiplierConstant t δ := by
    unfold fixedAwayUnshiftedHighMultiplierConstant
      fixedAwayUnshiftedTransitionMultiplierConstant
    nlinarith [fixedAwayDerivativeBound0_nonneg t δ]
  have hfactor : 0 ≤ 6 * C * Real.sqrt (K : ℝ) / (P : ℝ) := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCK.1) (Real.sqrt_nonneg _))
      (Nat.cast_nonneg P)
  by_cases hU2P : U ≤ 2 * P
  · have hshell :=
      norm_fixedAwayUnshiftedFiniteVector_le_transitionShell_of_prefixEstimate
        C hCK hδ hδt hK hP hKP (by omega) hU2P hUT
    have hbase : 0 ≤ (6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
        fixedAwayUnshiftedTransitionMultiplierConstant t δ :=
      mul_nonneg hfactor
        (fixedAwayUnshiftedTransitionMultiplierConstant_nonneg t δ)
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) U‖ ≤
          (6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedTransitionMultiplierConstant t δ := hshell
      _ ≤ 2 * ((6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedTransitionMultiplierConstant t δ) := by
        nlinarith
      _ = (12 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedTransitionMultiplierConstant t δ := by ring

  · have h2PU : 2 * P < U := lt_of_not_ge hU2P
    have h2P : 0 < 2 * P := by positivity
    have hK2P : K ≤ (2 * P) ^ 2 := by
      calc
        K ≤ 4 * P ^ 2 := hKP
        _ = (2 * P) ^ 2 := by ring
    have h2PT : 2 * P ≤ T := h2PU.le.trans hUT
    have hleft :=
      norm_fixedAwayUnshiftedFiniteVector_le_transitionShell_of_prefixEstimate
        C hCK hδ hδt hK hP hKP (by omega) le_rfl h2PT
    have hrightRaw :=
      norm_fixedAwayUnshiftedFiniteVector_tail_le_highShell_of_prefixEstimate
        C K T (2 * P) U hCK hδ hδt hK h2P hK2P h2PU hUT
    have hright :
        ‖fixedAwayUnshiftedFiniteVector t δ K (2 * P + 1) U‖ ≤
          (6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedTransitionMultiplierConstant t δ := by
      calc
        ‖fixedAwayUnshiftedFiniteVector t δ K (2 * P + 1) U‖ ≤
            (12 * C * Real.sqrt (K : ℝ) / ((2 * P : ℕ) : ℝ)) *
              fixedAwayUnshiftedHighMultiplierConstant t δ := hrightRaw
        _ = (6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
              fixedAwayUnshiftedHighMultiplierConstant t δ := by
          push_cast
          field_simp
          ring
        _ ≤ (6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
              fixedAwayUnshiftedTransitionMultiplierConstant t δ :=
          mul_le_mul_of_nonneg_left hHighTrans hfactor
    have hdisjoint : Disjoint (Finset.Ioc P (2 * P))
        (Finset.Ioc (2 * P) U) := by
      rw [Finset.disjoint_left]
      intro p hpLeft hpRight
      have hl := Finset.mem_Ioc.mp hpLeft
      have hr := Finset.mem_Ioc.mp hpRight
      omega
    have hsplit :
        fixedAwayUnshiftedFiniteVector t δ K (P + 1) U =
          fixedAwayUnshiftedFiniteVector t δ K (P + 1) (2 * P) +
            fixedAwayUnshiftedFiniteVector t δ K (2 * P + 1) U := by
      rw [fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
        fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
        fixedAwayUnshiftedFiniteVector_eq_sum_Ioc]
      rw [← Finset.sum_union hdisjoint]
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) h2PU.le]
    rw [hsplit]
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) (2 * P) +
          fixedAwayUnshiftedFiniteVector t δ K (2 * P + 1) U‖ ≤
        ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) (2 * P)‖ +
          ‖fixedAwayUnshiftedFiniteVector t δ K (2 * P + 1) U‖ :=
        norm_add_le _ _
      _ ≤ (6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedTransitionMultiplierConstant t δ +
          (6 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedTransitionMultiplierConstant t δ :=
        add_le_add hleft hright
      _ = (12 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
            fixedAwayUnshiftedTransitionMultiplierConstant t δ := by ring

/-- The integer square-root floor lies below the real square root. -/
theorem natSqrt_cast_le_realSqrt (K : ℕ) :
    ((Nat.sqrt K : ℕ) : ℝ) ≤ Real.sqrt (K : ℝ) := by
  have hsq : (((Nat.sqrt K : ℕ) : ℝ)) ^ 2 ≤ (K : ℝ) := by
    exact_mod_cast Nat.sqrt_le' K
  have hroot := Real.sqrt_le_sqrt hsq
  simpa only [Real.sqrt_sq (Nat.cast_nonneg _)] using! hroot

/-- For positive `K`, the real square root is at most twice its integer
floor.  This is the exact rounding estimate used at the transition. -/
theorem realSqrt_le_two_natSqrt {K : ℕ} (hK : 0 < K) :
    Real.sqrt (K : ℝ) ≤ 2 * (Nat.sqrt K : ℝ) := by
  have hS : 1 ≤ Nat.sqrt K := Nat.sqrt_pos.2 hK
  have hlt : K < (Nat.sqrt K + 1) ^ 2 := by
    simpa only [Nat.succ_eq_add_one] using! Nat.lt_succ_sqrt' K
  have hfour : K ≤ 4 * (Nat.sqrt K) ^ 2 := by
    have hround : (Nat.sqrt K + 1) ^ 2 ≤ 4 * (Nat.sqrt K) ^ 2 := by
      nlinarith
    exact hlt.le.trans hround
  have hfourReal : (K : ℝ) ≤ 4 * (Nat.sqrt K : ℝ) ^ 2 := by
    exact_mod_cast hfour
  rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)]
  rw [Real.sq_sqrt (Nat.cast_nonneg K)]
  nlinarith

/-- On one frequency shell, every denominator `1 < p ≤ U` is uniformly
bounded once the source-faithful Ramanujan prefix estimate is available up
to `U`.  The proof splits exactly at `floor(sqrt K)` and displays the two
rounding constants. -/
theorem norm_fixedAwayUnshiftedFiniteVector_two_le_of_prefixEstimate
    (C : ℝ) {t δ : ℝ} (K T U : ℕ)
    (hCK : RamanujanPrefixL2Estimate C K T)
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hU : 1 ≤ U) (hUT : U ≤ T) :
    ‖fixedAwayUnshiftedFiniteVector t δ K 2 U‖ ≤
      2 * fixedAwayUnshiftedLowShellConstant t δ +
        24 * C * fixedAwayUnshiftedTransitionMultiplierConstant t δ := by
  let S : ℕ := Nat.sqrt K
  have hS : 0 < S := by dsimp [S]; exact Nat.sqrt_pos.2 hK
  have hSK : S ^ 2 ≤ K := by dsimp [S]; exact Nat.sqrt_le' K
  have hS4 : K ≤ 4 * S ^ 2 := by
    dsimp [S]
    have hSone : 1 ≤ Nat.sqrt K := Nat.sqrt_pos.2 hK
    have hlt : K < (Nat.sqrt K + 1) ^ 2 := by
      simpa only [Nat.succ_eq_add_one] using! Nat.lt_succ_sqrt' K
    have hround : (Nat.sqrt K + 1) ^ 2 ≤ 4 * (Nat.sqrt K) ^ 2 := by
      nlinarith
    exact hlt.le.trans hround
  have hLowNonneg : 0 ≤ 2 * fixedAwayUnshiftedLowShellConstant t δ :=
    mul_nonneg (by norm_num) (fixedAwayUnshiftedLowShellConstant_nonneg t δ)
  have hHighNonneg :
      0 ≤ 24 * C * fixedAwayUnshiftedTransitionMultiplierConstant t δ :=
    mul_nonneg (mul_nonneg (by norm_num) hCK.1)
      (fixedAwayUnshiftedTransitionMultiplierConstant_nonneg t δ)
  by_cases hUS : U ≤ S
  · have hUK : U ^ 2 ≤ K :=
      (Nat.pow_le_pow_left hUS 2).trans hSK
    have hlow := norm_fixedAwayUnshiftedFiniteVector_two_le_lowRange
      K U hδ hδt hK hU hUK
    have hratio : (U : ℝ) / Real.sqrt (K : ℝ) ≤ 1 := by
      apply (div_le_one₀ (Real.sqrt_pos.2 (by exact_mod_cast hK))).2
      exact (by exact_mod_cast hUS : (U : ℝ) ≤ (S : ℝ)).trans
        (by simpa only [S] using! natSqrt_cast_le_realSqrt K)
    have hC2 : 0 ≤ 2 * fixedAwayUnshiftedLowShellConstant t δ := hLowNonneg
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ K 2 U‖ ≤
          2 * fixedAwayUnshiftedLowShellConstant t δ * (U : ℝ) /
            Real.sqrt (K : ℝ) := hlow
      _ = (2 * fixedAwayUnshiftedLowShellConstant t δ) *
            ((U : ℝ) / Real.sqrt (K : ℝ)) := by ring
      _ ≤ 2 * fixedAwayUnshiftedLowShellConstant t δ := by
        simpa only [mul_one] using! mul_le_mul_of_nonneg_left hratio hC2
      _ ≤ 2 * fixedAwayUnshiftedLowShellConstant t δ +
          24 * C * fixedAwayUnshiftedTransitionMultiplierConstant t δ :=
        le_add_of_nonneg_right hHighNonneg
  · have hSU : S < U := lt_of_not_ge hUS
    have hST : S < T := hSU.trans_le hUT
    have hlow := norm_fixedAwayUnshiftedFiniteVector_two_le_lowRange
      K S hδ hδt hK (by omega) hSK
    have hhigh :=
      norm_fixedAwayUnshiftedFiniteVector_tail_le_transition_of_prefixEstimate
        C K T S U hCK hδ hδt hK hS hS4 hSU hUT
    have hsplit :
        fixedAwayUnshiftedFiniteVector t δ K 2 U =
          fixedAwayUnshiftedFiniteVector t δ K 2 S +
            fixedAwayUnshiftedFiniteVector t δ K (S + 1) U := by
      have hdisjoint : Disjoint (Finset.Ioc 1 S) (Finset.Ioc S U) := by
        rw [Finset.disjoint_left]
        intro p hpLeft hpRight
        have hl := Finset.mem_Ioc.mp hpLeft
        have hr := Finset.mem_Ioc.mp hpRight
        omega
      rw [fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K 1,
        fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K 1,
        fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K S]
      rw [← Finset.sum_union hdisjoint]
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega : 1 ≤ S) hSU.le]
    have hlow' :
        ‖fixedAwayUnshiftedFiniteVector t δ K 2 S‖ ≤
          2 * fixedAwayUnshiftedLowShellConstant t δ := by
      have hratio : (S : ℝ) / Real.sqrt (K : ℝ) ≤ 1 := by
        apply (div_le_one₀ (Real.sqrt_pos.2 (by exact_mod_cast hK))).2
        simpa only [S] using! natSqrt_cast_le_realSqrt K
      calc
        ‖fixedAwayUnshiftedFiniteVector t δ K 2 S‖ ≤
            2 * fixedAwayUnshiftedLowShellConstant t δ * (S : ℝ) /
              Real.sqrt (K : ℝ) := hlow
        _ = (2 * fixedAwayUnshiftedLowShellConstant t δ) *
              ((S : ℝ) / Real.sqrt (K : ℝ)) := by ring
        _ ≤ 2 * fixedAwayUnshiftedLowShellConstant t δ := by
          simpa only [mul_one] using!
            mul_le_mul_of_nonneg_left hratio hLowNonneg
    have hhigh' :
        ‖fixedAwayUnshiftedFiniteVector t δ K (S + 1) U‖ ≤
          24 * C * fixedAwayUnshiftedTransitionMultiplierConstant t δ := by
      have hratio : Real.sqrt (K : ℝ) / (S : ℝ) ≤ 2 := by
        apply (div_le_iff₀ (by exact_mod_cast hS)).2
        simpa only [S] using! realSqrt_le_two_natSqrt hK
      have hfactor : 0 ≤ 12 * C := mul_nonneg (by norm_num) hCK.1
      calc
        ‖fixedAwayUnshiftedFiniteVector t δ K (S + 1) U‖ ≤
            (12 * C * Real.sqrt (K : ℝ) / (S : ℝ)) *
              fixedAwayUnshiftedTransitionMultiplierConstant t δ := hhigh
        _ = (12 * C) * (Real.sqrt (K : ℝ) / (S : ℝ)) *
              fixedAwayUnshiftedTransitionMultiplierConstant t δ := by ring
        _ ≤ ((12 * C) * 2) *
              fixedAwayUnshiftedTransitionMultiplierConstant t δ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hratio hfactor)
            (fixedAwayUnshiftedTransitionMultiplierConstant_nonneg t δ)
        _ = 24 * C * fixedAwayUnshiftedTransitionMultiplierConstant t δ := by
          ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hlow' hhigh')

/-- Unconditional geometric terminal tail obtained from the proved
divisor-square prefix estimate.  The only loss is the displayed harmonic
factor; no shell-count factor is hidden. -/
theorem norm_fixedAwayUnshiftedFiniteVector_tail_le_highShell_divisorSquare
    {t δ : ℝ} (K P U : ℕ)
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hP : 0 < P) (hKP : K ≤ P ^ 2)
    (hPU : P < U) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) U‖ ≤
      (12 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (P : ℝ)) *
        fixedAwayUnshiftedHighMultiplierConstant t δ := by
  let hCK :=
    (chanKumchevInitialSecondMomentEstimate_divisorSquare K U).toDyadic.toL2
  exact norm_fixedAwayUnshiftedFiniteVector_tail_le_highShell_of_prefixEstimate
    (Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3)) K U P U hCK
      hδ hδt hK hP hKP hPU le_rfl

/-- Complete high-denominator decomposition at a terminal cutoff `T`.
The first term is the source-faithful Chan--Kumchev range and the second is
the fully proved divisor-square tail.  This formula makes the precise
arithmetic dependency and every endpoint visible. -/
theorem norm_fixedAwayUnshiftedFiniteVector_tail_le_prefixThenDivisor
    (C : ℝ) {t δ : ℝ} (K T P U : ℕ)
    (hCK : RamanujanPrefixL2Estimate C K T)
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hP : 0 < P) (hKP : K ≤ P ^ 2)
    (hPT : P < T) (hTU : T < U) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) U‖ ≤
      ((12 * C * Real.sqrt (K : ℝ) / (P : ℝ)) +
        (12 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (T : ℝ))) *
        fixedAwayUnshiftedHighMultiplierConstant t δ := by
  have hT : 0 < T := hP.trans hPT
  have hKT : K ≤ T ^ 2 := by
    have hsq : P ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hPT.le 2
    exact hKP.trans hsq
  have hmiddle :=
    norm_fixedAwayUnshiftedFiniteVector_tail_le_highShell_of_prefixEstimate
      C K T P T hCK hδ hδt hK hP hKP hPT le_rfl
  have hterminal :=
    norm_fixedAwayUnshiftedFiniteVector_tail_le_highShell_divisorSquare
      K T U hδ hδt hK hT hKT hTU
  have hdisjoint : Disjoint (Finset.Ioc P T) (Finset.Ioc T U) := by
    rw [Finset.disjoint_left]
    intro p hpLeft hpRight
    have hl := Finset.mem_Ioc.mp hpLeft
    have hr := Finset.mem_Ioc.mp hpRight
    omega
  have hsplit :
      fixedAwayUnshiftedFiniteVector t δ K (P + 1) U =
        fixedAwayUnshiftedFiniteVector t δ K (P + 1) T +
          fixedAwayUnshiftedFiniteVector t δ K (T + 1) U := by
    rw [fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
      fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
      fixedAwayUnshiftedFiniteVector_eq_sum_Ioc]
    rw [← Finset.sum_union hdisjoint]
    rw [Finset.Ioc_union_Ioc_eq_Ioc hPT.le hTU.le]
  rw [hsplit]
  calc
    ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) T +
        fixedAwayUnshiftedFiniteVector t δ K (T + 1) U‖ ≤
      ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) T‖ +
        ‖fixedAwayUnshiftedFiniteVector t δ K (T + 1) U‖ :=
      norm_add_le _ _
    _ ≤ (12 * C * Real.sqrt (K : ℝ) / (P : ℝ)) *
          fixedAwayUnshiftedHighMultiplierConstant t δ +
        (12 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (T : ℝ)) *
          fixedAwayUnshiftedHighMultiplierConstant t δ :=
      add_le_add hmiddle hterminal
    _ = ((12 * C * Real.sqrt (K : ℝ) / (P : ℝ)) +
        (12 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (T : ℝ))) *
        fixedAwayUnshiftedHighMultiplierConstant t δ := by ring

/-- Full one-frequency-shell estimate with a source-faithful prefix range
ending at `T` and the proved divisor-square tail after `T`.  This is the
finite, endpoint-explicit form used before choosing
`T = K / (log K)^B`. -/
theorem norm_fixedAwayUnshiftedFiniteVector_two_le_prefixThenDivisor
    (C : ℝ) {t δ : ℝ} (K T U : ℕ)
    (hCK : RamanujanPrefixL2Estimate C K T)
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hT : 1 ≤ T)
    (hSqrtT : Nat.sqrt K < T) (hTU : T < U) :
    ‖fixedAwayUnshiftedFiniteVector t δ K 2 U‖ ≤
      2 * fixedAwayUnshiftedLowShellConstant t δ +
        24 * C * fixedAwayUnshiftedTransitionMultiplierConstant t δ +
        (12 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (T : ℝ)) *
          fixedAwayUnshiftedHighMultiplierConstant t δ := by
  have hprefix := norm_fixedAwayUnshiftedFiniteVector_two_le_of_prefixEstimate
    C K T T hCK hδ hδt hK hT le_rfl
  have hKT : K ≤ T ^ 2 := by
    have hlt : K < (Nat.sqrt K + 1) ^ 2 := by
      simpa only [Nat.succ_eq_add_one] using! Nat.lt_succ_sqrt' K
    have hsuccT : Nat.sqrt K + 1 ≤ T := by omega
    exact hlt.le.trans (Nat.pow_le_pow_left hsuccT 2)
  have htail := norm_fixedAwayUnshiftedFiniteVector_tail_le_highShell_divisorSquare
    K T U hδ hδt hK (by omega) hKT hTU
  have hdisjoint : Disjoint (Finset.Ioc 1 T) (Finset.Ioc T U) := by
    rw [Finset.disjoint_left]
    intro p hpLeft hpRight
    have hl := Finset.mem_Ioc.mp hpLeft
    have hr := Finset.mem_Ioc.mp hpRight
    omega
  have hsplit :
      fixedAwayUnshiftedFiniteVector t δ K 2 U =
        fixedAwayUnshiftedFiniteVector t δ K 2 T +
          fixedAwayUnshiftedFiniteVector t δ K (T + 1) U := by
    rw [fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K 1,
      fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K 1,
      fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K T]
    rw [← Finset.sum_union hdisjoint]
    rw [Finset.Ioc_union_Ioc_eq_Ioc hT hTU.le]
  rw [hsplit]
  calc
    ‖fixedAwayUnshiftedFiniteVector t δ K 2 T +
        fixedAwayUnshiftedFiniteVector t δ K (T + 1) U‖ ≤
      ‖fixedAwayUnshiftedFiniteVector t δ K 2 T‖ +
        ‖fixedAwayUnshiftedFiniteVector t δ K (T + 1) U‖ :=
      norm_add_le _ _
    _ ≤ (2 * fixedAwayUnshiftedLowShellConstant t δ +
          24 * C * fixedAwayUnshiftedTransitionMultiplierConstant t δ) +
        (12 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (T : ℝ)) *
          fixedAwayUnshiftedHighMultiplierConstant t δ :=
      add_le_add hprefix htail
    _ = 2 * fixedAwayUnshiftedLowShellConstant t δ +
        24 * C * fixedAwayUnshiftedTransitionMultiplierConstant t δ +
        (12 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (T : ℝ)) *
          fixedAwayUnshiftedHighMultiplierConstant t δ := by ring

/-! ## Uniformity in the fixed-away threshold -/

def fixedAwayDerivativeCauchyUniformConstant (T δ : ℝ) : ℝ :=
  2 * (fixedAwayDerivativeUniformBound T δ 0 +
    fixedAwayDerivativeUniformBound T δ 2)

def fixedAwayPVInverseDecayUniformConstant (T δ : ℝ) : ℝ :=
  fixedAwayDerivativeUniformBound T δ 2 / (2 * Real.pi) ^ 2

def fixedAwayPVGlobalDecayUniformConstant (T δ : ℝ) : ℝ :=
  2 * (fixedAwayPVLocalUniformBound T +
    fixedAwayDerivativeUniformBound T δ 2 / (2 * Real.pi) ^ 2)

def fixedAwayUnshiftedLowShellUniformConstant (T δ : ℝ) : ℝ :=
  2 * Real.sqrt 42 *
    (4 * fixedAwayPVInverseDecayUniformConstant T δ +
      8 * fixedAwayDerivativeCauchyUniformConstant T δ)

def fixedAwayUnshiftedHighMultiplierUniformConstant (T δ : ℝ) : ℝ :=
  fixedAwayPVGlobalDecayUniformConstant T δ +
    4 * fixedAwayDerivativeUniformBound T δ 0

def fixedAwayUnshiftedTransitionMultiplierUniformConstant
    (T δ : ℝ) : ℝ :=
  fixedAwayPVGlobalDecayUniformConstant T δ +
    16 * fixedAwayDerivativeUniformBound T δ 0

theorem fixedAwayDerivativeCauchyConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (htT : t ≤ T) :
    fixedAwayDerivativeCauchyConstant t δ ≤
      fixedAwayDerivativeCauchyUniformConstant T δ := by
  unfold fixedAwayDerivativeCauchyConstant
    fixedAwayDerivativeCauchyUniformConstant fixedAwayDerivativeBound0
    fixedAwayDerivativeBound2
  gcongr
  · exact fixedAwayDerivativeBound_le_uniform hδ hδt htT 0
  · exact fixedAwayDerivativeBound_le_uniform hδ hδt htT 2

theorem fixedAwayPVInverseDecayConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (htT : t ≤ T) :
    fixedAwayPVInverseDecayConstant t δ ≤
      fixedAwayPVInverseDecayUniformConstant T δ := by
  unfold fixedAwayPVInverseDecayConstant
    fixedAwayPVInverseDecayUniformConstant fixedAwayDerivativeBound2
  gcongr
  exact fixedAwayDerivativeBound_le_uniform hδ hδt htT 2

theorem fixedAwayPVGlobalDecayConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (htT : t ≤ T) :
    fixedAwayPVGlobalDecayConstant t δ ≤
      fixedAwayPVGlobalDecayUniformConstant T δ := by
  have ht : 0 ≤ t := hδ.le.trans hδt
  unfold fixedAwayPVGlobalDecayConstant
    fixedAwayPVGlobalDecayUniformConstant fixedAwayDerivativeBound2
  gcongr
  · exact fixedAwayPVLocalBound_le_uniform ht htT
  · exact fixedAwayDerivativeBound_le_uniform hδ hδt htT 2

theorem fixedAwayUnshiftedLowShellConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (htT : t ≤ T) :
    fixedAwayUnshiftedLowShellConstant t δ ≤
      fixedAwayUnshiftedLowShellUniformConstant T δ := by
  unfold fixedAwayUnshiftedLowShellConstant
    fixedAwayUnshiftedLowShellUniformConstant
  gcongr
  · exact fixedAwayPVInverseDecayConstant_le_uniform hδ hδt htT
  · exact fixedAwayDerivativeCauchyConstant_le_uniform hδ hδt htT

theorem fixedAwayUnshiftedHighMultiplierConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (htT : t ≤ T) :
    fixedAwayUnshiftedHighMultiplierConstant t δ ≤
      fixedAwayUnshiftedHighMultiplierUniformConstant T δ := by
  unfold fixedAwayUnshiftedHighMultiplierConstant
    fixedAwayUnshiftedHighMultiplierUniformConstant fixedAwayDerivativeBound0
  gcongr
  · exact fixedAwayPVGlobalDecayConstant_le_uniform hδ hδt htT
  · exact fixedAwayDerivativeBound_le_uniform hδ hδt htT 0

theorem fixedAwayUnshiftedTransitionMultiplierConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (htT : t ≤ T) :
    fixedAwayUnshiftedTransitionMultiplierConstant t δ ≤
      fixedAwayUnshiftedTransitionMultiplierUniformConstant T δ := by
  unfold fixedAwayUnshiftedTransitionMultiplierConstant
    fixedAwayUnshiftedTransitionMultiplierUniformConstant
    fixedAwayDerivativeBound0
  gcongr
  · exact fixedAwayPVGlobalDecayConstant_le_uniform hδ hδt htT
  · exact fixedAwayDerivativeBound_le_uniform hδ hδt htT 0

/-- Uniform-threshold form of the one-shell prefix estimate.  The right
side depends only on the fixed upper threshold `T0` and smoothing width
`δ`, not on the varying threshold `t`. -/
theorem norm_fixedAwayUnshiftedFiniteVector_two_le_of_prefixEstimate_uniform
    (C : ℝ) {t δ T0 : ℝ} (K T U : ℕ)
    (hCK : RamanujanPrefixL2Estimate C K T)
    (hδ : 0 < δ) (hδt : δ < t) (htT0 : t ≤ T0)
    (hK : 0 < K) (hU : 1 ≤ U) (hUT : U ≤ T) :
    ‖fixedAwayUnshiftedFiniteVector t δ K 2 U‖ ≤
      2 * fixedAwayUnshiftedLowShellUniformConstant T0 δ +
        24 * C * fixedAwayUnshiftedTransitionMultiplierUniformConstant T0 δ := by
  have hraw := norm_fixedAwayUnshiftedFiniteVector_two_le_of_prefixEstimate
    C K T U hCK hδ hδt hK hU hUT
  have hLow := fixedAwayUnshiftedLowShellConstant_le_uniform
    hδ hδt.le htT0
  have hTransition :=
    fixedAwayUnshiftedTransitionMultiplierConstant_le_uniform
      hδ hδt.le htT0
  exact hraw.trans <| by
    gcongr
    exact mul_nonneg (by norm_num) hCK.1

/-- Uniform-threshold form including the explicit divisor-square terminal
tail.  This is the exact finite estimate needed before the asymptotic
choice of the Chan--Kumchev cutoff. -/
theorem
    norm_fixedAwayUnshiftedFiniteVector_two_le_prefixThenDivisor_uniform
    (C : ℝ) {t δ T0 : ℝ} (K T U : ℕ)
    (hCK : RamanujanPrefixL2Estimate C K T)
    (hδ : 0 < δ) (hδt : δ < t) (htT0 : t ≤ T0)
    (hK : 0 < K) (hT : 1 ≤ T)
    (hSqrtT : Nat.sqrt K < T) (hTU : T < U) :
    ‖fixedAwayUnshiftedFiniteVector t δ K 2 U‖ ≤
      2 * fixedAwayUnshiftedLowShellUniformConstant T0 δ +
        24 * C * fixedAwayUnshiftedTransitionMultiplierUniformConstant T0 δ +
        (12 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (T : ℝ)) *
          fixedAwayUnshiftedHighMultiplierUniformConstant T0 δ := by
  have hraw := norm_fixedAwayUnshiftedFiniteVector_two_le_prefixThenDivisor
    C K T U hCK hδ hδt hK hT hSqrtT hTU
  have hLow := fixedAwayUnshiftedLowShellConstant_le_uniform
    hδ hδt.le htT0
  have hTransition :=
    fixedAwayUnshiftedTransitionMultiplierConstant_le_uniform
      hδ hδt.le htT0
  have hHigh := fixedAwayUnshiftedHighMultiplierConstant_le_uniform
    hδ hδt.le htT0
  have hTailFactor :
      0 ≤ 12 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
        Real.sqrt (K : ℝ) / (T : ℝ) := by positivity
  exact hraw.trans <| by
    gcongr
    exact mul_nonneg (by norm_num) hCK.1

/-! ## Global high-frequency square tail -/

private theorem sum_inv_pow_two_Ico_zero_le_two (H : ℕ) :
    (∑ r ∈ Finset.Ico 0 H, 1 / (2 : ℝ) ^ r) ≤ 2 := by
  have h := geom_sum_Ico_le_of_lt_one
    (m := 0) (n := H) (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  calc
    (∑ r ∈ Finset.Ico 0 H, 1 / (2 : ℝ) ^ r) =
        ∑ r ∈ Finset.Ico 0 H, (1 / 2 : ℝ) ^ r := by
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [one_div]
      exact (inv_pow (2 : ℝ) r).symm
    _ ≤ (1 / 2 : ℝ) ^ 0 / (1 - (1 / 2 : ℝ)) := h
    _ = 2 := by norm_num

/-- Above the natural frequency `N²`, the full denominator range `p≤N`
lies below the reciprocal-square transition.  Its norm therefore decays
geometrically on the frequency blocks `K=2^rN²`. -/
theorem norm_fixedAwayUnshiftedFiniteVector_highFrequencyDyadic_le
    {t δ : ℝ} (N r : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) (hN : 0 < N) :
    ‖fixedAwayUnshiftedFiniteVector
        t δ (2 ^ r * N ^ 2) 2 N‖ ≤
      2 * fixedAwayUnshiftedLowShellConstant t δ /
        Real.sqrt ((2 : ℝ) ^ r) := by
  have hK : 0 < 2 ^ r * N ^ 2 := by positivity
  have hUK : N ^ 2 ≤ 2 ^ r * N ^ 2 := by
    have hone : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    nlinarith
  have hraw := norm_fixedAwayUnshiftedFiniteVector_two_le_lowRange
    (2 ^ r * N ^ 2) N hδ hδt hK hN hUK
  calc
    ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ r * N ^ 2) 2 N‖ ≤
        2 * fixedAwayUnshiftedLowShellConstant t δ * (N : ℝ) /
          Real.sqrt ((2 ^ r * N ^ 2 : ℕ) : ℝ) := hraw
    _ = 2 * fixedAwayUnshiftedLowShellConstant t δ /
          Real.sqrt ((2 : ℝ) ^ r) := by
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']

/-- The squared high-frequency tail is bounded uniformly in the number of
blocks.  This is the precise global summability statement replacing the
manuscript phrase “the high-frequency blocks form a geometric series”. -/
theorem sum_sq_norm_fixedAwayUnshiftedFiniteVector_highFrequencyDyadic_le
    {t δ : ℝ} (N H : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) (hN : 0 < N) :
    ∑ r ∈ Finset.Ico 0 H,
        ‖fixedAwayUnshiftedFiniteVector
          t δ (2 ^ r * N ^ 2) 2 N‖ ^ 2 ≤
      8 * fixedAwayUnshiftedLowShellConstant t δ ^ 2 := by
  have hC : 0 ≤ fixedAwayUnshiftedLowShellConstant t δ :=
    fixedAwayUnshiftedLowShellConstant_nonneg t δ
  have hpoint : ∀ r ∈ Finset.Ico 0 H,
      ‖fixedAwayUnshiftedFiniteVector
          t δ (2 ^ r * N ^ 2) 2 N‖ ^ 2 ≤
        4 * fixedAwayUnshiftedLowShellConstant t δ ^ 2 /
          (2 : ℝ) ^ r := by
    intro r _hr
    have hnorm := norm_fixedAwayUnshiftedFiniteVector_highFrequencyDyadic_le
      N r hδ hδt hN
    have hrSqrt : 0 < Real.sqrt ((2 : ℝ) ^ r) := by positivity
    have hrNonneg :
        0 ≤ 2 * fixedAwayUnshiftedLowShellConstant t δ /
          Real.sqrt ((2 : ℝ) ^ r) := by positivity
    calc
      ‖fixedAwayUnshiftedFiniteVector
          t δ (2 ^ r * N ^ 2) 2 N‖ ^ 2 ≤
        (2 * fixedAwayUnshiftedLowShellConstant t δ /
          Real.sqrt ((2 : ℝ) ^ r)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = 4 * fixedAwayUnshiftedLowShellConstant t δ ^ 2 /
          (2 : ℝ) ^ r := by
        rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
        ring
  calc
    ∑ r ∈ Finset.Ico 0 H,
        ‖fixedAwayUnshiftedFiniteVector
          t δ (2 ^ r * N ^ 2) 2 N‖ ^ 2 ≤
      ∑ r ∈ Finset.Ico 0 H,
        4 * fixedAwayUnshiftedLowShellConstant t δ ^ 2 /
          (2 : ℝ) ^ r := by
      apply Finset.sum_le_sum
      intro r hr
      exact hpoint r hr
    _ = 4 * fixedAwayUnshiftedLowShellConstant t δ ^ 2 *
        (∑ r ∈ Finset.Ico 0 H, 1 / (2 : ℝ) ^ r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ ≤ 4 * fixedAwayUnshiftedLowShellConstant t δ ^ 2 * 2 := by
      apply mul_le_mul_of_nonneg_left (sum_inv_pow_two_Ico_zero_le_two H)
      positivity
    _ = 8 * fixedAwayUnshiftedLowShellConstant t δ ^ 2 := by ring

end

end Erdos1002
