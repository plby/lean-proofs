/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos88.StructuredCountVectorLower
import ErdosProblems.Erdos88.StructuredUpperAsymptotic

/-!
# The structured bounded-window lower estimate

This module assembles the fixed-window lower half of Claim 12.1 with the
outer count-vector Berry--Esseen estimate.  The interval width is chosen
proportional to the zero-count conditional scale plus a linear cutoff.  The
same quantity occurs in the denominator of the conditional estimate, so it
cancels and leaves the sharp order `n⁻³ᐞ²`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Matrix.Norms.Frobenius

namespace Erdos88
namespace GaussianQuadratic

open BooleanSlices BoundedWindowAnalytic

attribute [local instance] Classical.propDecidable

/-- Passing from an ambient order at most twice `q` to the natural
three-halves scale costs only the harmless factor four. -/
lemma scale_three_halves_le_four_of_le_two
    {n q : ℕ} (hq : 1 ≤ q) (hnq : n ≤ 2 * q) :
    scale n (3 / 2 : ℝ) ≤ 4 * scale q (3 / 2 : ℝ) := by
  have hnqR : (n : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast hnq
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg n) hnqR
    (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have htwo : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    calc
      (2 : ℝ) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  calc
    scale n (3 / 2 : ℝ) ≤ (2 * (q : ℝ)) ^ (3 / 2 : ℝ) := by
      simpa only [scale, Real.rpow_eq_pow] using hpow
    _ = (2 : ℝ) ^ (3 / 2 : ℝ) * scale q (3 / 2 : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (Nat.cast_nonneg q)]
      rfl
    _ ≤ 4 * scale q (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right htwo (scale_nonneg q _)

/-- The edge-density lower bound gives the convenient square-root form of
the cubic lower bound for the first count-vector shift. -/
lemma countVectorLinearCoefficient_graph_sqrt_lower
    {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    {A : ℝ} (hA : 0 < A) (hc0 : ∀ i, 0 ≤ c i)
    (hedge : A * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ)) :
    (A / 2) * scale n (3 / 2 : ℝ) ≤
      Real.sqrt (vectorSqNorm (countVectorLinearCoefficient P hbucket
        (GraphQuadratic.graphEffectiveLinear G c))) := by
  let V := vectorSqNorm (countVectorLinearCoefficient P hbucket
    (GraphQuadratic.graphEffectiveLinear G c))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hVlower := countVectorLinearCoefficient_graph_sqNorm_lower
    hn P hbucket G c hA.le hc0 hedge
  have hleft : 0 ≤ (A / 2) * scale n (3 / 2 : ℝ) :=
    mul_nonneg (div_nonneg hA.le (by norm_num)) (scale_nonneg n _)
  have hV : 0 ≤ V := Structured.vectorSqNorm_nonneg _
  have hscaleSq : scale n (3 / 2 : ℝ) ^ 2 = (n : ℝ) ^ 3 := by
    simpa only [scale, Real.rpow_eq_pow] using
      GraphQuadratic.n_rpow_three_halves_sq n
  apply (sq_le_sq₀ hleft (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hV]
  calc
    ((A / 2) * scale n (3 / 2 : ℝ)) ^ 2 =
        (1 / 4 : ℝ) * (A ^ 2 * (n : ℝ) ^ 3) := by
      rw [mul_pow, hscaleSq]
      ring
    _ ≤ V := by simpa only [V] using hVlower

/-- Enlarging the physical window preserves a uniform conditional Claim
12.1 lower certificate. -/
lemma UniformConditionedClaim121Lower.mono_window
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    {D : RLCD.BucketDecomposition d0 k rho}
    {G : SimpleGraph (Fin n)}
    {hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket}
    {delta B B' M kappa s : ℝ}
    (h : UniformConditionedClaim121Lower
      D G hbucket delta B M kappa s) (hBB' : B ≤ B') :
    UniformConditionedClaim121Lower
      D G hbucket delta B' M kappa s := by
  intro ell f hbalanced hcoeff
  obtain ⟨hleft, hsigma, hlower⟩ := h ell f hbalanced hcoeff
  refine ⟨hleft, hsigma, ?_⟩
  intro z hz0 hzM
  exact (hlower z hz0 hzM).trans
    (Esseen.smallBall_mono_radius _ hBB' z)

/-- The elementary scale comparison behind the lower averaging.  If the
zero-count variance differs from the actual variance by a shift of size
`t`, and both the Frobenius scale and `t` are linear in `q`, then the sum of
the zero-count scale and `t` is bounded by a fixed multiple of the actual
conditional standard deviation. -/
lemma zero_add_linear_div_le_of_variance_comparison
    {rho q T sigma0 sigma W t : ℝ}
    (hrho : 0 < rho) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hsigma0 : 0 ≤ sigma0) (hsigma : 0 ≤ sigma) (hW : 0 ≤ W)
    (ht : t = T * q)
    (hlower : Real.sqrt rho * q ≤ sigma)
    (hcompare : sigma0 ^ 2 ≤ 2 * sigma ^ 2 + 2 * W)
    (hsmall : W < t ^ 2) :
    (sigma0 + t) / (2 + 3 * T / Real.sqrt rho) ≤ sigma := by
  have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hsigma0' : sigma0 ≤ 2 * (sigma + t) := by
    have hsq : sigma0 ^ 2 ≤ 2 * sigma ^ 2 + 2 * t ^ 2 := by
      exact hcompare.trans (by linarith)
    apply (sq_le_sq₀ hsigma0 (by positivity)).mp
    calc
      sigma0 ^ 2 ≤ 2 * sigma ^ 2 + 2 * t ^ 2 := hsq
      _ ≤ (2 * (sigma + t)) ^ 2 := by
        nlinarith [mul_nonneg hsigma ht0]
  have htSigma : t ≤ (T / Real.sqrt rho) * sigma := by
    rw [ht]
    calc
      T * q = (T / Real.sqrt rho) * (Real.sqrt rho * q) := by
        field_simp [hsqrt.ne']
      _ ≤ (T / Real.sqrt rho) * sigma :=
        mul_le_mul_of_nonneg_left hlower (div_nonneg hT hsqrt.le)
  have hden : 0 < 2 + 3 * T / Real.sqrt rho := by positivity
  apply (div_le_iff₀ hden).2
  calc
    sigma0 + t ≤ 2 * sigma + 3 * t := by linarith
    _ ≤ 2 * sigma + 3 * ((T / Real.sqrt rho) * sigma) := by
      gcongr
    _ = sigma * (2 + 3 * T / Real.sqrt rho) := by ring

/-- A subcritical power is eventually an arbitrarily small multiple of the
three-halves power.  This is the quantitative form used for the ratio
condition in the outer Berry--Esseen theorem. -/
lemma eventually_zeroScale_add_linear_le
    (gamma A T c : ℝ) (hgamma : 0 ≤ gamma)
    (hgammaSmall : gamma < 1 / 12) (hA : 0 < A)
    (hT : 0 ≤ T) (hc : 0 < c) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ∀ sigma0 : ℝ, 0 ≤ sigma0 →
        sigma0 ≤ 2 * scale q (1 + 6 * gamma) →
        sigma0 + T * (q : ℝ) ≤
          c * (A / 2) * scale q (3 / 2 : ℝ) := by
  let K : ℝ := (2 + T) / (c * (A / 2))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hexp : 1 + 6 * gamma < (3 / 2 : ℝ) := by linarith
  have hrate := QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    K (1 + 6 * gamma) (3 / 2 : ℝ) hK hexp
  filter_upwards [hrate, Filter.eventually_ge_atTop 1] with q hrateQ hq
  intro sigma0 hsigma0 hsigmaUpper
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlinear : (q : ℝ) ≤ scale q (1 + 6 * gamma) := by
    calc
      (q : ℝ) = scale q 1 := by
        unfold scale
        exact (Real.rpow_one (q : ℝ)).symm
      _ ≤ scale q (1 + 6 * gamma) :=
        scale_mono_exponent hq (by linarith)
  have hsum : sigma0 + T * (q : ℝ) ≤
      (2 + T) * scale q (1 + 6 * gamma) := by
    calc
      sigma0 + T * (q : ℝ) ≤
          2 * scale q (1 + 6 * gamma) +
            T * scale q (1 + 6 * gamma) :=
        add_le_add hsigmaUpper
          (mul_le_mul_of_nonneg_left hlinear hT)
      _ = (2 + T) * scale q (1 + 6 * gamma) := by ring
  have hden : 0 < c * (A / 2) := by positivity
  calc
    sigma0 + T * (q : ℝ) ≤
        (2 + T) * scale q (1 + 6 * gamma) := hsum
    _ = (c * (A / 2)) *
        (K * scale q (1 + 6 * gamma)) := by
      dsimp only [K]
      field_simp [hden.ne']
    _ ≤ (c * (A / 2)) * scale q (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hrateQ hden.le

/-- The fixed choices of the relative-Esseen smoothing radius and error
budget absorb at most one quarter of the Gaussian lower density. -/
lemma relativeEsseen_error_absorption (b : ℝ) (hb : 0 < b) :
    let C := Esseen.relativeEsseenConstant
    let eta := b / (8 * (C + 1))
    let R := 4 + 16 * (C + 1) / b
    3 * b / 4 ≤ b - C * (2 / R + eta) := by
  dsimp only
  have hC0 : 0 ≤ Esseen.relativeEsseenConstant :=
    Esseen.relativeEsseenConstant_nonneg
  have hCplus : 0 < Esseen.relativeEsseenConstant + 1 :=
    add_pos_of_nonneg_of_pos hC0 (show (0 : ℝ) < 1 by norm_num)
  have hRpos : 0 < 4 + 16 * (Esseen.relativeEsseenConstant + 1) / b :=
    add_pos_of_pos_of_nonneg (by norm_num)
      (div_nonneg (mul_nonneg (by norm_num) hCplus.le) hb.le)
  have hden : 0 < 8 * (Esseen.relativeEsseenConstant + 1) :=
    mul_pos (by norm_num) hCplus
  have htwo :
      2 / (4 + 16 * (Esseen.relativeEsseenConstant + 1) / b) ≤
        b / (8 * (Esseen.relativeEsseenConstant + 1)) := by
    apply (div_le_div_iff₀ hRpos hden).2
    field_simp [hb.ne']
    nlinarith
  have hsum :
      2 / (4 + 16 * (Esseen.relativeEsseenConstant + 1) / b) +
          b / (8 * (Esseen.relativeEsseenConstant + 1)) ≤
        b / (4 * (Esseen.relativeEsseenConstant + 1)) := by
    calc
      _ ≤ b / (8 * (Esseen.relativeEsseenConstant + 1)) +
            b / (8 * (Esseen.relativeEsseenConstant + 1)) :=
        add_le_add htwo (le_refl _)
      _ = b / (4 * (Esseen.relativeEsseenConstant + 1)) := by
        field_simp [hCplus.ne']
        ring
  have hfrac : Esseen.relativeEsseenConstant /
      (Esseen.relativeEsseenConstant + 1) ≤ 1 :=
    (div_le_one hCplus).2 (le_add_of_nonneg_right (by norm_num))
  have herror :
      Esseen.relativeEsseenConstant *
          (2 / (4 + 16 * (Esseen.relativeEsseenConstant + 1) / b) +
            b / (8 * (Esseen.relativeEsseenConstant + 1))) ≤ b / 4 := by
    calc
      _ ≤ Esseen.relativeEsseenConstant *
            (b / (4 * (Esseen.relativeEsseenConstant + 1))) :=
        mul_le_mul_of_nonneg_left hsum hC0
      _ = (b / 4) * (Esseen.relativeEsseenConstant /
            (Esseen.relativeEsseenConstant + 1)) := by
        field_simp [hCplus.ne']
      _ ≤ (b / 4) * 1 :=
        mul_le_mul_of_nonneg_left hfrac (div_nonneg hb.le (by norm_num))
      _ = b / 4 := by ring
  linarith

/-- The outer shift-error term is absorbed by its quadratic cutoff once the
conditional variance has the natural `q^(3/2)` upper bound. -/
lemma outer_shift_error_absorption
    (q : ℕ) {D eps t V C b T : ℝ}
    (hD : 0 ≤ D) (heps : 0 ≤ eps) (ht : 0 < t)
    (hsqrtV : 0 < Real.sqrt V) (hb : 0 < b)
    (hupper : Real.sqrt V ≤ C * (q : ℝ) * Real.sqrt q)
    (hcoef : 8 * D * 60000 * C / b ≤ T ^ 2)
    (htEq : t = T * (q : ℝ)) :
    (D * Real.sqrt q * (60000 * eps)) / t ^ 2 ≤
      (b / 8) * (eps / Real.sqrt V) := by
  have hsqrtQsq : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg q)
  have hDcoeff : D * 60000 * C ≤ b / 8 * T ^ 2 := by
    calc
      D * 60000 * C = (b / 8) * (8 * D * 60000 * C / b) := by
        field_simp [hb.ne']
      _ ≤ (b / 8) * T ^ 2 :=
        mul_le_mul_of_nonneg_left hcoef (div_nonneg hb.le (by norm_num))
  have hmul :
      (D * Real.sqrt q * (60000 * eps) / t ^ 2) * Real.sqrt V ≤
        (b / 8) * eps := by
    have htSq : 0 < t ^ 2 := sq_pos_of_pos ht
    calc
      (D * Real.sqrt q * (60000 * eps) / t ^ 2) * Real.sqrt V =
          (D * Real.sqrt q * (60000 * eps) * Real.sqrt V) / t ^ 2 := by ring
      _ ≤ (b / 8) * eps := (div_le_iff₀ htSq).2 (by
        calc
          D * Real.sqrt q * (60000 * eps) * Real.sqrt V ≤
              D * Real.sqrt q * (60000 * eps) *
                (C * (q : ℝ) * Real.sqrt q) := by
            exact mul_le_mul_of_nonneg_left hupper
              (mul_nonneg
                (mul_nonneg hD (Real.sqrt_nonneg _))
                (mul_nonneg (by norm_num) heps))
          _ = (D * 60000 * C) * eps * (q : ℝ) *
                Real.sqrt q ^ 2 := by ring
          _ = (D * 60000 * C) * eps * (q : ℝ) ^ 2 := by
            rw [hsqrtQsq]
            ring
          _ ≤ (b / 8 * T ^ 2) * eps * (q : ℝ) ^ 2 := by
            gcongr
          _ = (b / 8) * eps * t ^ 2 := by
            rw [htEq]
            ring)
  calc
    D * Real.sqrt q * (60000 * eps) / t ^ 2 ≤
        ((b / 8) * eps) / Real.sqrt V :=
      (le_div_iff₀ hsqrtV).2 hmul
    _ = (b / 8) * (eps / Real.sqrt V) := by ring

/-- A sufficiently large linear cutoff absorbs one inverse
three-halves-scale error against the conditional standard deviation. -/
lemma inverse_three_halves_scale_absorption
    (q : ℕ) {b T C sigma eps : ℝ}
    (hq : 0 < q) (hb : 0 < b) (hT : 0 < T) (hsigma : 0 < sigma)
    (hupper : sigma ≤ C * scale q (3 / 2 : ℝ))
    (hconst : 8 * C / (b * T) ≤ (q : ℝ))
    (heps : T * (q : ℝ) ≤ eps) :
    scale q (-(3 : ℝ) / 2) ≤ (b / 8) * (eps / sigma) := by
  have hcancel : scale q (-(3 : ℝ) / 2) *
      scale q (3 / 2 : ℝ) = 1 := by
    rw [scale_mul hq]
    norm_num [scale]
  have hcross : 8 * C ≤ (q : ℝ) * (b * T) :=
    (div_le_iff₀ (mul_pos hb hT)).mp hconst
  have hqbound : C ≤ (b / 8) * (T * (q : ℝ)) := by
    nlinarith [hcross]
  have hmul : scale q (-(3 : ℝ) / 2) * sigma ≤
      (b / 8) * eps := by
    calc
      scale q (-(3 : ℝ) / 2) * sigma ≤
          scale q (-(3 : ℝ) / 2) *
            (C * scale q (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hupper (scale_nonneg q _)
      _ = C * (scale q (-(3 : ℝ) / 2) * scale q (3 / 2 : ℝ)) := by ring
      _ = C := by rw [hcancel, mul_one]
      _ ≤ (b / 8) * (T * (q : ℝ)) := hqbound
      _ ≤ (b / 8) * eps :=
        mul_le_mul_of_nonneg_left heps (div_nonneg hb.le (by norm_num))
  calc
    scale q (-(3 : ℝ) / 2) ≤ ((b / 8) * eps) / sigma :=
      (le_div_iff₀ hsigma).2 hmul
    _ = (b / 8) * (eps / sigma) := by ring

/-- Combining a three-quarter main-term lower bound with a one-quarter
error budget leaves one half of the main scale. -/
lemma quarter_error_absorption
    {b x bracket err : ℝ} (hx : 0 ≤ x)
    (hbracket : 3 * b / 4 ≤ bracket)
    (herror : err ≤ (b / 4) * x) :
    (b / 2) * x ≤ x * bracket - err := by
  nlinarith [mul_le_mul_of_nonneg_left hbracket hx]

/-- The conditional interval scale `2 * eps` cancels from the final main
term without changing its inverse-standard-deviation normalization. -/
lemma half_scale_cancellation
    {b eps sigma k : ℝ} (heps : eps ≠ 0) (hsigma : sigma ≠ 0) :
    (b / 2) * (eps / sigma) * (k / (2 * eps)) =
      b * k / (4 * sigma) := by
  field_simp [heps, hsigma]
  ring

/-- A relative-width and center bound converts the quadratic smoothing
constraint to its dimensionless coefficient inequality. -/
lemma quadratic_ratio_bound
    {R eps c v M z : ℝ}
    (heps0 : 0 ≤ eps) (heps : eps ≤ c * v) (hcenter : |z| ≤ M * v)
    (hR : 0 ≤ R) (hc : 0 ≤ c) (hv : 0 ≤ v)
    (hcoeff : 2 * R * c * (M + R * c) ≤ 1) :
    2 * (R * eps) * (|z| + R * eps) ≤ v ^ 2 := by
  have hReps : R * eps ≤ R * (c * v) :=
    mul_le_mul_of_nonneg_left heps hR
  have hsumCenter : |z| + R * eps ≤ M * v + R * (c * v) :=
    add_le_add hcenter hReps
  have hleftFactor0 : 0 ≤ 2 * (R * (c * v)) :=
    mul_nonneg (by norm_num) (mul_nonneg hR (mul_nonneg hc hv))
  have hcenterFactor0 : 0 ≤ |z| + R * eps :=
    add_nonneg (abs_nonneg _) (mul_nonneg hR heps0)
  calc
    2 * (R * eps) * (|z| + R * eps) ≤
        2 * (R * (c * v)) * (|z| + R * eps) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hReps (by norm_num)) hcenterFactor0
    _ ≤ 2 * (R * (c * v)) * (M * v + R * (c * v)) :=
      mul_le_mul_of_nonneg_left hsumCenter hleftFactor0
    _ = (2 * R * c * (M + R * c)) * v ^ 2 := by ring
    _ ≤ v ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hcoeff

lemma two_mul_add_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 2 * a + b :=
  add_nonneg (mul_nonneg (by norm_num) ha) hb

lemma sqrt_sq_variance_comparison
    {a b W : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcompare : a ≤ 2 * b + 2 * W) :
    Real.sqrt a ^ 2 ≤ 2 * Real.sqrt b ^ 2 + 2 * W := by
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
  exact hcompare

/-- The zero-count scale plus a linear cutoff is controlled by every
count-vector conditional scale whose shift moment lies below that cutoff. -/
lemma countVectorClaim121Scale_lower_of_shiftMoment
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ) (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {rhoF T : ℝ} (hrhoF : 0 < rhoF) (hT : 0 ≤ T)
    (hq : 0 < Fintype.card D.Covered)
    (hFrob : Real.sqrt rhoF * (Fintype.card D.Covered : ℝ) ≤
      claim121FrobeniusBase
        (bucketCenteredAdjacency D.finCoveredPartition.bucket
          hbucket.choose (D.finCoveredGraph G)))
    (ell : BucketCountVector D.finCoveredPartition)
    (hell : countVectorShiftMoment D.finCoveredPartition hbucket
      (D.finCoveredGraph G) ell <
        (T * (Fintype.card D.Covered : ℝ)) ^ 2) :
    (zeroCountClaim121Scale D G c O hbucket +
        T * (Fintype.card D.Covered : ℝ)) /
        (2 + 3 * T / Real.sqrt rhoF) ≤
      countVectorClaim121Scale D G c O hbucket ell := by
  let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
    hbucket.choose (D.finCoveredGraph G)
  let y := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
    (D.conditionedCoveredCoefficient G c O)
  let f0 := Structured.wStar
    (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G)) y 0
  let f := Structured.wStar
    (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G)) y
    (productSliceDelta D.finCoveredPartition hbucket.choose
      (fun j ↦ (ell j).val))
  let sigma := countVectorClaim121Scale D G c O hbucket ell
  let sigma0 := zeroCountClaim121Scale D G c O hbucket
  let W := countVectorShiftMoment D.finCoveredPartition hbucket
    (D.finCoveredGraph G) ell
  let t := T * (Fintype.card D.Covered : ℝ)
  have hsigma0 : 0 ≤ sigma0 := by
    dsimp only [sigma0, zeroCountClaim121Scale]
    exact Real.sqrt_nonneg _
  have hsigma : 0 ≤ sigma := by
    dsimp only [sigma, countVectorClaim121Scale]
    exact Real.sqrt_nonneg _
  have hW : 0 ≤ W := countVectorShiftMoment_nonneg
    D.finCoveredPartition hbucket (D.finCoveredGraph G) ell
  have hcompare := baseScaleSq_le_claim121Scale_add_shiftMoment
    D.finCoveredPartition hbucket (D.finCoveredGraph G) y ell
  have hsigmaLower : Real.sqrt rhoF *
      (Fintype.card D.Covered : ℝ) ≤ sigma :=
    hFrob.trans (claim121FrobeniusBase_le_scale F f)
  have hF0 : 0 ≤ frobeniusSq F := RobustRank.frobeniusSq_nonneg F
  have hf00 : 0 ≤ vectorSqNorm f0 := Structured.vectorSqNorm_nonneg f0
  have hf0 : 0 ≤ vectorSqNorm f := Structured.vectorSqNorm_nonneg f
  have hbase0 : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f0 :=
    two_mul_add_nonneg hF0 hf00
  have htarget0 : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f :=
    two_mul_add_nonneg hF0 hf0
  have hcompare' : sigma0 ^ 2 ≤ 2 * sigma ^ 2 + 2 * W := by
    dsimp only [sigma0, zeroCountClaim121Scale, sigma,
      countVectorClaim121Scale]
    exact sqrt_sq_variance_comparison
      (a := 2 * frobeniusSq F + vectorSqNorm f0)
      (b := 2 * frobeniusSq F + vectorSqNorm f) (W := W)
      hbase0 htarget0 hcompare
  change (sigma0 + t) / (2 + 3 * T / Real.sqrt rhoF) ≤ sigma
  exact zero_add_linear_div_le_of_variance_comparison
    (rho := rhoF) (q := (Fintype.card D.Covered : ℝ)) (T := T)
    (sigma0 := sigma0) (sigma := sigma) (W := W) (t := t)
    hrhoF (Nat.cast_nonneg _) hT hsigma0 hsigma hW rfl
    hsigmaLower hcompare' hell

/-- Averaging a local structured lower bound over a seven-eighths set of
remainder conditionings preserves a fixed fraction of that bound. -/
lemma eventProbability_half_lower_of_structured_good
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    (B target klocal : ℝ)
    (Good : Finset (D.remainder : Set (Fin n)) → Prop)
    (hklocal : 0 ≤ klocal)
    (hbadGood : Concentration.uniformProbability (fun R0 ↦ ¬ Good R0) ≤
      1 / 8)
    (hlocal : ∀ R0 : Finset (D.remainder : Set (Fin n)), Good R0 →
      klocal * scale (Fintype.card D.Covered) (-(3 : ℝ) / 2) ≤
        ∑ ell : BucketCountVector D.finCoveredPartition,
          countVectorWeight D.finCoveredPartition ell *
            conditionedCountVectorWindowProbability D G e0 c
              (BoundedWindow.subtypeSubsetImage D.remainder R0)
              B target ell)
    (hqpos : 0 < Fintype.card D.Covered)
    (hqle : Fintype.card D.Covered ≤ n) :
    (klocal / 2) * scale n (-(3 : ℝ) / 2) ≤
      Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
        |Probability.perturbedEdgePolynomial G e0 c U - target| ≤ B) := by
  have hLnonneg : 0 ≤ klocal *
      scale (Fintype.card D.Covered) (-(3 : ℝ) / 2) :=
    mul_nonneg hklocal (scale_nonneg _ _)
  have hambient := eventProbability_half_structured_lower_of_good_remainders
    D G e0 c B target Good hLnonneg hbadGood hlocal
  have hscaleNleQ : scale n (-(3 : ℝ) / 2) ≤
      scale (Fintype.card D.Covered) (-(3 : ℝ) / 2) := by
    unfold scale
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast hqle) (by norm_num)
  calc
    (klocal / 2) * scale n (-(3 : ℝ) / 2) ≤
        (1 - 1 / 8) *
          (klocal * scale (Fintype.card D.Covered) (-(3 : ℝ) / 2)) := by
      have hmul := mul_le_mul_of_nonneg_left hscaleNleQ hklocal
      nlinarith [scale_nonneg (Fintype.card D.Covered) (-(3 : ℝ) / 2)]
    _ ≤ Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
        |Probability.perturbedEdgePolynomial G e0 c U - target| ≤ B) :=
      hambient

/-- Four natural center-error terms, each controlled at the covered
three-halves scale, give the linear standard-deviation bound used by the
outer count-vector estimate. -/
lemma center_bound_from_scale_components
    {n q : ℕ} {z targetError centralError U A K Abar Adens v : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hAbar : 0 ≤ Abar)
    (hraw : |z| ≤ |targetError| + |centralError| + (q : ℝ) + |U|)
    (htarget : |targetError| ≤ A * scale n (3 / 2 : ℝ))
    (hcentral : |centralError| ≤ K * Abar * scale n (3 / 2 : ℝ))
    (hscaleNQ : scale n (3 / 2 : ℝ) ≤ 4 * scale q (3 / 2 : ℝ))
    (hqScale : (q : ℝ) ≤ scale q (3 / 2 : ℝ))
    (hU0 : 0 ≤ U) (hU : U ≤ 30001 * v)
    (hscaleToV : scale q (3 / 2 : ℝ) ≤ (2 / Adens) * v) :
    |z| ≤
      (8 * (A + K * Abar) / Adens + 2 / Adens + 30001) * v := by
  have htarget' : |targetError| ≤
      4 * A * scale q (3 / 2 : ℝ) :=
    htarget.trans (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left hscaleNQ hA)
  have hcentral' : |centralError| ≤
      4 * K * Abar * scale q (3 / 2 : ℝ) := by
    calc
      |centralError| ≤ K * Abar * scale n (3 / 2 : ℝ) := hcentral
      _ ≤ (K * Abar) * (4 * scale q (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hscaleNQ (mul_nonneg hK hAbar)
      _ = 4 * K * Abar * scale q (3 / 2 : ℝ) := by ring
  have hUabs : |U| ≤ 30001 * v := by
    rw [abs_of_nonneg hU0]
    exact hU
  have htotal := add_le_add (add_le_add (add_le_add htarget' hcentral')
    hqScale) hUabs
  calc
    |z| ≤ (4 * A * scale q (3 / 2 : ℝ) +
        4 * K * Abar * scale q (3 / 2 : ℝ) +
        scale q (3 / 2 : ℝ)) + 30001 * v := hraw.trans htotal
    _ = (4 * (A + K * Abar) + 1) * scale q (3 / 2 : ℝ) +
          30001 * v := by ring
    _ ≤ (4 * (A + K * Abar) + 1) * ((2 / Adens) * v) +
          30001 * v := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hscaleToV (by positivity)) le_rfl
    _ = (8 * (A + K * Abar) / Adens + 2 / Adens + 30001) * v := by
      ring

/-- Two one-eighth error estimates leave one half of a main term whose
coefficient is at least three quarters of the reference density. -/
lemma outer_coefficient_after_two_errors
    {b x bracket shiftError nearError : ℝ}
    (hx : 0 ≤ x) (hbracket : 3 * b / 4 ≤ bracket)
    (hshift : shiftError ≤ (b / 8) * x)
    (hnear : nearError ≤ (b / 8) * x) :
    (b / 2) * x ≤ x * bracket - shiftError - nearError := by
  have herr : shiftError + nearError ≤ (b / 4) * x := by
    calc
      shiftError + nearError ≤ (b / 8) * x + (b / 8) * x :=
        add_le_add hshift hnear
      _ = (b / 4) * x := by ring
  calc
    (b / 2) * x ≤ x * bracket - (shiftError + nearError) :=
      quarter_error_absorption hx hbracket herr
    _ = x * bracket - shiftError - nearError := by ring

/-- The inverse covered scale converts a fixed coefficient based on a
variance upper constant into the actual inverse-standard-deviation bound. -/
lemma inverse_three_halves_local_to_variance
    (q : ℕ) {b k C sigma : ℝ}
    (hq : 0 < q) (hb : 0 ≤ b) (hk : 0 ≤ k) (hC : 0 < C)
    (hsigma : 0 < sigma)
    (hupper : sigma ≤ C * scale q (3 / 2 : ℝ)) :
    (b * k / (4 * C)) * scale q (-(3 : ℝ) / 2) ≤
      b * k / (4 * sigma) := by
  have hscaleInv : scale q (-(3 : ℝ) / 2) =
      1 / scale q (3 / 2 : ℝ) := by
    unfold scale
    rw [show (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) by ring]
    rw [one_div]
    change (q : ℝ) ^ (-(3 / 2 : ℝ)) = ((q : ℝ) ^ (3 / 2 : ℝ))⁻¹
    exact Real.rpow_neg (by positivity) (3 / 2 : ℝ)
  have hinv := one_div_le_one_div_of_le hsigma hupper
  rw [hscaleInv]
  calc
    (b * k / (4 * C)) * (1 / scale q (3 / 2 : ℝ)) =
        (b * k / 4) * (1 / (C * scale q (3 / 2 : ℝ))) := by ring
    _ ≤ (b * k / 4) * (1 / sigma) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = b * k / (4 * sigma) := by ring

/-- The chosen cutoff constant dominates the coefficient needed to absorb
the outer shift error. -/
lemma shift_cutoff_coefficient_bound
    {D C b H X T : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hb : 0 < b) (hH : 0 < H)
    (hX : X = 8 * D * 60000 * C / b)
    (hT : T = H + 2 + X) :
    8 * D * 60000 * C / b ≤ T ^ 2 := by
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hXT : X ≤ T := by rw [hT]; linarith
  have hTone : 1 ≤ T := by rw [hT]; linarith
  have hTsq : T ≤ T ^ 2 := by
    calc
      T = 1 * T := (one_mul T).symm
      _ ≤ T * T := mul_le_mul_of_nonneg_right hTone
        ((show (0 : ℝ) ≤ 1 by norm_num).trans hTone)
      _ = T ^ 2 := (pow_two T).symm
  rw [← hX]
  exact hXT.trans hTsq

/-- A small fraction of the density lower scale lies below the actual
conditional standard deviation. -/
lemma epsilon_le_sqrt_of_density_scale
    {q : ℕ} {eps c A V : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hA : 0 ≤ A)
    (hsmall : eps ≤ c * (A / 2) * scale q (3 / 2 : ℝ))
    (hlower : (A / 2) * scale q (3 / 2 : ℝ) ≤ Real.sqrt V) :
    eps ≤ Real.sqrt V := by
  calc
    eps ≤ c * (A / 2) * scale q (3 / 2 : ℝ) := hsmall
    _ = c * ((A / 2) * scale q (3 / 2 : ℝ)) := by ring
    _ ≤ (A / 2) * scale q (3 / 2 : ℝ) :=
      mul_le_of_le_one_left
        (mul_nonneg (div_nonneg hA (by norm_num)) (scale_nonneg q _)) hc1
    _ ≤ Real.sqrt V := hlower

/-- The reciprocal parameter used for the quadratic ratio constraint is at
most one under the coarse lower bounds on its factors. -/
lemma reciprocal_ratio_parameter_le_one
    {M R c : ℝ} (hM : 0 ≤ M) (hR : 4 ≤ R)
    (hc : c = 1 / (4 * R * (M + R + 1))) :
    c ≤ 1 := by
  have hden : 0 < 4 * R * (M + R + 1) := by positivity
  rw [hc]
  apply (div_le_one hden).2
  have hone : (1 : ℝ) ≤ M + R + 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 4)]

/-- The same reciprocal choice makes the dimensionless quadratic smoothing
coefficient at most one. -/
lemma reciprocal_ratio_coefficient_bound
    {M R c : ℝ} (hM : 0 ≤ M) (hR : 4 ≤ R)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hc : c = 1 / (4 * R * (M + R + 1))) :
    2 * R * c * (M + R * c) ≤ 1 := by
  have hR0 : 0 ≤ R := (show (0 : ℝ) ≤ 4 by norm_num).trans hR
  have hden : 0 < 4 * R * (M + R + 1) := by positivity
  have hRc : R * c ≤ R := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc1 hR0
  have hsum : M + R * c ≤ M + R + 1 := by linarith
  calc
    2 * R * c * (M + R * c) ≤
        2 * R * c * (M + R + 1) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 / 2 := by
      rw [hc]
      field_simp [hden.ne']
      ring
    _ ≤ 1 := by norm_num

/-- In the small-regularized-LCD branch, every target in the natural
`n^(3/2)` range has a fixed-window probability bounded below by a positive
multiple of `n⁻³ᐞ²`.  The physical window is selected before both coefficient
and target-range constants. -/
theorem exists_eventual_graphEffective_smallRLCD_window_lower_threshold
    (C gamma L : ℝ) (hC : 0 < C)
    (hgamma : 0 < gamma) (hgammaSmall : gamma < 3 / 800)
    (hL : 1 ≤ L) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ H Acenter : ℝ, 0 < H → 0 < Acenter →
      ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Fin n → ℝ),
          RamseyFree C G →
          (∀ i, 0 ≤ c i ∧ c i ≤ H * (n : ℝ)) →
          RLCD.regularizedLCD L gamma
              (GraphQuadratic.graphEffectiveLinear G c) ≤ Real.sqrt n →
          ∀ e0 target : ℝ,
            |target - Probability.expectation (1 / 2 : ℝ)
                (Probability.perturbedEdgePolynomial G e0 c)| ≤
                  Acenter * scale n (3 / 2 : ℝ) →
            kappa * scale n (-(3 : ℝ) / 2) ≤
              Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                |Probability.perturbedEdgePolynomial G e0 c U - target| ≤ B) := by
  obtain ⟨Bclaim, hBclaim, hfixedClaim⟩ :=
    exists_fixedWindow_eventual_productSlice_claim121_lower_uniform
      (2 * C) (2 * gamma) (mul_pos (by norm_num) hC)
      (mul_pos (by norm_num) hgamma) (by linarith)
  refine ⟨Bclaim, hBclaim, ?_⟩
  intro B hBclaimB H Acenter hH hAcenter
  obtain ⟨Bcommon, hBcommon, _etaCommon, _hetaCommon,
      _hetaCommonOne, hcommonAll⟩ :=
    exists_eventual_graphEffective_smallRLCD_common_claims_threshold
      C gamma hC hgamma hgammaSmall
  obtain ⟨_AdensCommon, _hAdensCommon, rhoF, hrhoF,
      Dshift, hDshift, hcommon⟩ := hcommonAll H L hH hL
  obtain ⟨Adens, hAdens, Nedge, hedgeDensity⟩ :=
    FiniteES.ramseyFree_edgeCount_density_lower
      (2 * C) (mul_pos (by norm_num) hC)
  let Hc : ℝ := 2 * H + 1
  let Abar : ℝ := max H 1
  let Kouter : ℝ := 4
  let Cvar : ℝ := (Hc + 1) / 2
  let Mlin : ℝ :=
    8 * (Acenter + Kouter * Abar) / Adens + 2 / Adens + 30001
  let base : ℝ := Real.exp (-((Mlin + 1) ^ 2) / 2) / 12
  let eta : ℝ := base / (8 * (Esseen.relativeEsseenConstant + 1))
  let R : ℝ := 4 + 16 * (Esseen.relativeEsseenConstant + 1) / base
  let X : ℝ := 8 * Dshift * 60000 * Cvar / base
  let T : ℝ := Hc + 2 + X
  let Cscale : ℝ := 2 + 3 * T / Real.sqrt rhoF
  let Mclaim : ℝ := 60002 * Cscale
  let csmall : ℝ := 1 / (4 * R * (Mlin + R + 1))
  have hHc : 0 < Hc := by dsimp only [Hc]; linarith
  have hAbar : 1 ≤ Abar := by dsimp only [Abar]; exact le_max_right _ _
  have hCvar : 0 < Cvar := by dsimp only [Cvar]; linarith
  have hMlin : 0 ≤ Mlin := by dsimp only [Mlin, Kouter, Abar]; positivity
  have hbase : 0 < base := by dsimp only [base]; positivity
  have hEsseen : 0 ≤ Esseen.relativeEsseenConstant :=
    Esseen.relativeEsseenConstant_nonneg
  have heta : 0 < eta := by
    dsimp only [eta]
    exact div_pos hbase (mul_pos (by norm_num) (by linarith))
  have hR : 4 ≤ R := by
    dsimp only [R]
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num)
      (by linarith)) hbase.le)
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hT : 0 < T := by dsimp only [T]; linarith
  have hCscale : 0 < Cscale := by dsimp only [Cscale]; positivity
  have hMclaim : 0 ≤ Mclaim := by dsimp only [Mclaim]; positivity
  have hcsmall : 0 < csmall := by
    dsimp only [csmall]
    positivity
  have hcsmallOne : csmall ≤ 1 := by
    exact reciprocal_ratio_parameter_le_one hMlin hR rfl
  have hRnonneg : 0 ≤ R := (show (0 : ℝ) ≤ 4 by norm_num).trans hR
  have hratioCoeff :
      2 * R * csmall * (Mlin + R * csmall) ≤ 1 := by
    exact reciprocal_ratio_coefficient_bound hMlin hR hcsmall.le
      hcsmallOne rfl
  obtain ⟨kclaim, hkclaim, hclaimEvent⟩ :=
    hfixedClaim Mclaim hMclaim
  let klocal : ℝ := base * kclaim / (4 * Cvar)
  let kappa : ℝ := klocal / 2
  have hklocal : 0 < klocal := by dsimp only [klocal]; positivity
  have hkappa : 0 < kappa := by dsimp only [kappa]; positivity
  refine ⟨kappa, hkappa, ?_⟩
  have hcommonB := hcommon Bcommon le_rfl
  have htypical :=
    eventually_conditionedCovered_hasKSSSBalancedCoefficients gamma hgamma
  have hzero := eventually_zeroCountClaim121Scale_le gamma hgamma
  have hdegreeBad :=
    RLCD.BucketDecomposition.eventually_uniformProbability_remainder_atypical_le
      gamma hgamma
  have hcountBad :=
    RLCD.BucketDecomposition.eventually_countVectorMass_not_nearBalanced_le
  have hgrowth := eventually_const_le_scale 2 gamma hgamma
  have hclaimN := eventually_of_le_two hclaimEvent
  have hcountBadN := eventually_of_le_two hcountBad
  have herrorN := eventually_of_le_two
    (eventually_countVectorLinearCoefficient_graph_error_le
      Hc Adens eta hHc.le hAdens heta)
  have hratioQ := eventually_zeroScale_add_linear_le
    gamma Adens T csmall hgamma.le (by linarith) hAdens hT.le hcsmall
  have hratioN := eventually_of_le_two hratioQ
  have hnearQ := eventually_const_le_scale
    (8 * Cvar / (base * T)) 1 (by norm_num)
  have hnearN := eventually_of_le_two hnearQ
  have hdegreeDecay : ∀ᶠ n : ℕ in Filter.atTop,
      scale n (-(3 : ℝ) / 2) ≤ 1 / 16 := by
    have hrate := QuadraticCancellation.eventually_const_mul_rpow_le_rpow
      16 (-(3 : ℝ) / 2) 0 (by norm_num) (by norm_num)
    filter_upwards [hrate] with n hn
    have : 16 * scale n (-(3 : ℝ) / 2) ≤ 1 := by
      simpa only [scale, Real.rpow_eq_pow, Real.rpow_zero] using hn
    linarith
  filter_upwards [hcommonB, htypical, hzero, hdegreeBad, hgrowth,
      hclaimN, hcountBadN, herrorN, hratioN, hnearN, hdegreeDecay,
      Filter.eventually_ge_atTop (max 2 (2 * Nedge))] with
      n hcommonN htypicalN hzeroN hdegreeBadN hgrowthN hclaimN'
        hcountBadN' herrorN' hratioN' hnearN' hdegreeDecayN hn
  intro G _instAdj c hRamsey hc hsmall e0 target htarget
  letI : DecidableRel G.Adj := _instAdj
  obtain ⟨D, hrem, hpart, hbucket, hcoveredRamsey, hFrob, hclaims⟩ :=
    hcommonN G c hRamsey hc hsmall
  have hnpos : 0 < n := by omega
  have hscaleHalf : scale n (1 - gamma) ≤ (n : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      scale n (1 - gamma) * 2 ≤
          scale n (1 - gamma) * scale n gamma :=
        mul_le_mul_of_nonneg_left hgrowthN (scale_nonneg n _)
      _ = scale n ((1 - gamma) + gamma) := scale_mul hnpos _ _
      _ = (n : ℝ) := by
        rw [show (1 - gamma) + gamma = (1 : ℝ) by ring]
        exact Real.rpow_one _
  have hremHalf : (D.remainder.card : ℝ) ≤ (n : ℝ) / 2 :=
    hrem.trans hscaleHalf
  let q := Fintype.card D.Covered
  have hcard : D.remainder.card + q = n := by
    simpa only [q, Fintype.card_fin] using D.remainder_card_add_card_covered
  have hqle : q ≤ n := by omega
  have hcardR : (D.remainder.card : ℝ) + (q : ℝ) = (n : ℝ) := by
    exact_mod_cast hcard
  have hnqR : (n : ℝ) ≤ 2 * (q : ℝ) := by linarith
  have hnq : n ≤ 2 * q := by exact_mod_cast hnqR
  have hqpos : 0 < q := by omega
  have hqOne : 1 ≤ q := hqpos
  have hscaleNQ := scale_three_halves_le_four_of_le_two hqOne hnq
  have hNedge : Nedge ≤ q := by
    have htwo : 2 * Nedge ≤ n :=
      (le_max_right 2 (2 * Nedge)).trans hn
    have htwoR : (Nedge : ℝ) ≤ (n : ℝ) / 2 := by
      have : ((2 * Nedge : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast htwo
      push_cast at this
      linarith
    exact_mod_cast htwoR.trans (by linarith : (n : ℝ) / 2 ≤ q)
  have hedge := hedgeDensity q hNedge (D.finCoveredGraph G) hcoveredRamsey
  have hmpos : 0 < Fintype.card D.BlockIndex := by
    change 0 < Fintype.card D.Covered at hqpos
    rw [D.card_covered] at hqpos
    have hblocks : 0 < D.blocks.card := Nat.pos_of_mul_pos_right hqpos
    simpa only [D.card_blockIndex] using hblocks
  let m := Fintype.card D.BlockIndex
  let K := m - 1
  have hmEq : m = K + 1 := by dsimp only [K]; omega
  have hmEq' : Fintype.card D.BlockIndex = K + 1 := by
    simpa only [m] using hmEq
  have hclaimAt := hclaimN' q hnq (K := K)
  let ClaimAt : ℕ → Prop := fun r ↦
      ∀ (P : BucketPartition (Fin q) (Fin r))
        (G : SimpleGraph (Fin q))
        (hbucket : RobustRank.HasEqualBuckets P.bucket),
        IsKSSSPartition (2 * gamma) P → RamseyFree (2 * C) G →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
          ∀ (ell : Fin r → ℕ) (f : Fin q → ℝ),
            IsNearBalanced (2 * gamma) P ell →
            HasKSSSBalancedCoefficients (2 * gamma) P f
              (bucketCenteredAdjacency P.bucket hbucket.choose G) →
            ∃ hleft : Nonempty (ProductSlicePoint P ell),
              letI := hleft
              let F := bucketCenteredAdjacency P.bucket hbucket.choose G
              let sigma := Real.sqrt
                (2 * frobeniusSq F + vectorSqNorm f)
              0 < sigma ∧ ∀ z : ℝ,
                0 ≤ s * z → s * z ≤ Mclaim * sigma →
                kclaim / sigma ≤
                  Esseen.smallBall
                    (Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                      (productSliceQuadratic P ell (-trace F) f F)) Bclaim z
  have hclaimAtK : ClaimAt (K + 1) := by
    simpa only [ClaimAt] using hclaimAt
  have hclaimAtD : ClaimAt (Fintype.card D.BlockIndex) :=
    Eq.mp (congrArg ClaimAt hmEq'.symm) hclaimAtK
  dsimp only [ClaimAt] at hclaimAtD
  obtain ⟨s, hs, hclaimRaw⟩ :=
    hclaimAtD D.finCoveredPartition (D.finCoveredGraph G) hbucket
      hpart hcoveredRamsey
  let Good : Finset (D.remainder : Set (Fin n)) → Prop := fun R0 ↦
    IsGoodLowerRemainder D G e0 c Abar Kouter R0
  have hdegreeOuter := hdegreeBadN D G hrem
  have hcAbs : ∀ v, |c v| ≤ Abar * (n : ℝ) := by
    intro v
    rw [abs_of_nonneg (hc v).1]
    exact (hc v).2.trans (mul_le_mul_of_nonneg_right
      (le_max_left H 1) (Nat.cast_nonneg n))
  have hcentralOuter := uniformProbability_remainderConditionalMean_far_scale_le
    D G e0 c hnpos hAbar (by norm_num : (0 : ℝ) < Kouter) hcAbs
  have hbadGood : Concentration.uniformProbability (fun R0 ↦ ¬ Good R0) ≤
      1 / 8 := by
    have hraw := uniformProbability_not_isGoodLowerRemainder_le
      D G e0 c Abar Kouter (scale n (-(3 : ℝ) / 2)) (1 / Kouter ^ 2)
      hdegreeOuter hcentralOuter
    calc
      Concentration.uniformProbability (fun R0 ↦ ¬ Good R0) ≤
          scale n (-(3 : ℝ) / 2) + 1 / Kouter ^ 2 := by
        simpa only [Good] using hraw
      _ ≤ 1 / 16 + 1 / 16 := by
        exact add_le_add hdegreeDecayN (by norm_num [Kouter])
      _ = 1 / 8 := by norm_num
  have hlocal (R0 : Finset (D.remainder : Set (Fin n)))
      (hR0 : Good R0) :
      klocal * scale q (-(3 : ℝ) / 2) ≤
        ∑ ell : BucketCountVector D.finCoveredPartition,
          countVectorWeight D.finCoveredPartition ell *
            conditionedCountVectorWindowProbability D G e0 c
              (BoundedWindow.subtypeSubsetImage D.remainder R0)
              B target ell := by
    let O := BoundedWindow.subtypeSubsetImage D.remainder R0
    have hO : O ⊆ D.remainder :=
      BoundedWindow.subtypeSubsetImage_subset D.remainder R0
    have hdegree : ∀ i : Fin q,
        |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
          (AKSGraph.degreeInto G (D.finCoveredEquiv i).1 D.remainder : ℝ) / 2| ≤
            Real.sqrt n := by
      intro i
      exact (hR0.1 i).le
    obtain ⟨hcoeffBounds, hclaim122, _hupper, _hmass⟩ := hclaims O hO
    let sigma0 := zeroCountClaim121Scale D G c O hbucket
    let t : ℝ := T * (q : ℝ)
    let eps : ℝ := sigma0 + t
    let U : ℝ := 30000 * eps + t
    let S : ℝ := 2 * eps
    let lowerScale : ℝ := eps / Cscale
    let y := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
      (D.conditionedCoveredCoefficient G c O)
    let V := vectorSqNorm
      (countVectorLinearCoefficient D.finCoveredPartition hbucket y)
    have hsigma0 : 0 ≤ sigma0 := by
      dsimp only [sigma0, zeroCountClaim121Scale]
      positivity
    have ht : 0 < t := by dsimp only [t]; positivity
    have heps : 0 < eps := by dsimp only [eps]; positivity
    have hS : 0 < S := by dsimp only [S]; positivity
    have hband0 : 0 ≤ U - 30000 * eps - t := by
      dsimp only [U]
      ring_nf
      norm_num
    have hbandM : U + 30000 * eps + t ≤ Mclaim * lowerScale := by
      have htEps : t ≤ eps := by
        dsimp only [eps]
        exact le_add_of_nonneg_left hsigma0
      dsimp only [U, Mclaim, lowerScale]
      have hrhs : 60002 * Cscale * (eps / Cscale) = 60002 * eps := by
        field_simp [hCscale.ne']
      rw [hrhs]
      linarith only [htEps]
    have hshiftScale : 2 * t ≤ S := by
      dsimp only [S, eps]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hsigma0)
        (by norm_num)
    have hzeroScale : 2 * zeroCountClaim121Scale D G c O hbucket ≤ S := by
      dsimp only [S, eps, sigma0]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ht.le)
        (by norm_num)
    have hcoeffScale : (Hc + 1) * (q : ℝ) ≤ eps := by
      have hTcoeff : Hc + 1 ≤ T := by
        dsimp only [T]
        linarith only [hX]
      calc
        (Hc + 1) * (q : ℝ) ≤ T * (q : ℝ) :=
          mul_le_mul_of_nonneg_right hTcoeff (Nat.cast_nonneg q)
        _ = t := rfl
        _ ≤ eps := by
          dsimp only [eps]
          exact le_add_of_nonneg_left hsigma0
    have hFnorm : ‖bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose (D.finCoveredGraph G)‖ ≤
        60000 * eps := by
      let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
        hbucket.choose (D.finCoveredGraph G)
      let f0 := Structured.wStar
        (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G)) y 0
      calc
        ‖bucketCenteredAdjacency D.finCoveredPartition.bucket
            hbucket.choose (D.finCoveredGraph G)‖ ≤
            claim121FrobeniusBase F := by
          simpa only [F] using frobenius_norm_le_claim121FrobeniusBase F
        _ ≤ sigma0 := by
          simpa only [F, f0, sigma0, zeroCountClaim121Scale, y] using
            claim121FrobeniusBase_le_scale F f0
        _ ≤ eps := by
          dsimp only [eps]
          exact le_add_of_nonneg_right ht.le
        _ = 1 * eps := by ring
        _ ≤ 60000 * eps :=
          mul_le_mul_of_nonneg_right (by norm_num) heps.le
    have hnearBad := (hcountBadN' q hnq)
      (Fintype.card D.BlockIndex) D.finCoveredPartition (2 * gamma) hpart
    have hclaim121 : UniformConditionedClaim121Lower
        D G hbucket (2 * gamma) B Mclaim kclaim s := by
      apply UniformConditionedClaim121Lower.mono_window
        (B := Bclaim) (B' := B) _ hBclaimB
      intro ell f hbalanced hcoeff
      exact hclaimRaw ell f hbalanced hcoeff
    have hcoeffNear (ell : BucketCountVector D.finCoveredPartition)
        (hell : IsNearBalanced (2 * gamma) D.finCoveredPartition
          (fun j ↦ (ell j).val)) :
        HasKSSSBalancedCoefficients (2 * gamma) D.finCoveredPartition
          (Structured.wStar
            (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
            (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G)) y
            (productSliceDelta D.finCoveredPartition hbucket.choose
              (fun j ↦ (ell j).val)))
          (bucketCenteredAdjacency D.finCoveredPartition.bucket
            hbucket.choose (D.finCoveredGraph G)) := by
      exact htypicalN G c D hremHalf hpart hbucket
        (fun j ↦ (ell j).val) hell O hdegree
    have hfixed := sqrt_mul_le_claim121_fixedScales_of_frobenius
      D G c O hbucket hrhoF.le hFrob
    have hsigma0Lower : Real.sqrt rhoF * (q : ℝ) ≤ sigma0 := by
      simpa only [q, sigma0] using hfixed.2
    have hsigma0Upper := hzeroN G c D hremHalf hpart hbucket O hdegree
    have hepsSmall := hratioN' q hnq sigma0 hsigma0
      (by simpa only [q, sigma0] using hsigma0Upper)
    have hepsSmallLocal : eps ≤
        csmall * ((Adens / 2) * scale q (3 / 2 : ℝ)) := by
      simpa only [eps, t, mul_assoc] using hepsSmall
    have hVlower := countVectorLinearCoefficient_graph_sqrt_lower
      hqpos D.finCoveredPartition hbucket (D.finCoveredGraph G)
      (D.conditionedCoveredCoefficient G c O) hAdens
      (fun i ↦ (hcoeffBounds i).1) hedge
    have hVlowerLocal : (Adens / 2) * scale q (3 / 2 : ℝ) ≤
        Real.sqrt V := by
      simpa only [V, y] using hVlower
    have hVupper := sqrt_countVectorLinearCoefficient_graph_sqNorm_le
      D.finCoveredPartition hbucket (D.finCoveredGraph G)
      (D.conditionedCoveredCoefficient G c O) Hc hHc.le
      (fun i ↦ (hcoeffBounds i).1) (fun i ↦ (hcoeffBounds i).2)
    have hV0 : 0 ≤ V := Structured.vectorSqNorm_nonneg _
    have hVpos : 0 < V := by
      have hleft : 0 < (Adens / 2) * scale q (3 / 2 : ℝ) :=
        mul_pos (div_pos hAdens (by norm_num)) (scale_pos hqpos _)
      have hsqrtPos : 0 < Real.sqrt V :=
        hleft.trans_le hVlowerLocal
      exact Real.sqrt_pos.mp hsqrtPos
    have hsqrtV : 0 < Real.sqrt V := Real.sqrt_pos.2 hVpos
    have hbracket : 3 * base / 4 ≤
        Real.exp (-((Mlin + 1) ^ 2) / 2) / 12 -
          Esseen.relativeEsseenConstant * (2 / R + eta) := by
      simpa only [R, eta, base] using
        relativeEsseen_error_absorption base hbase
    have hshiftAbsorb :
        (Dshift * Real.sqrt q * (60000 * eps)) / t ^ 2 ≤
          (base / 8) * (eps / Real.sqrt V) := by
      have hcoef : 8 * Dshift * 60000 * Cvar / base ≤ T ^ 2 := by
        exact shift_cutoff_coefficient_bound hDshift.le hCvar.le hbase hHc
          rfl rfl
      have hupperShift : Real.sqrt V ≤
          Cvar * (q : ℝ) * Real.sqrt q := by
        simpa only [V, y, Cvar, Hc] using hVupper
      exact outer_shift_error_absorption (q := q) (D := Dshift)
        (eps := eps) (t := t) (V := V) (C := Cvar) (b := base) (T := T)
        hDshift.le heps.le ht hsqrtV hbase hupperShift hcoef rfl
    have hnearAbsorb : scale q (-(3 : ℝ) / 2) ≤
        (base / 8) * (eps / Real.sqrt V) := by
      have hupper : Real.sqrt V ≤ Cvar * scale q (3 / 2 : ℝ) := by
        rw [GraphQuadratic.scale_three_halves_eq_mul_sqrt hqpos]
        simpa only [V, y, Cvar, Hc, mul_assoc] using hVupper
      have hconst : 8 * Cvar / (base * T) ≤ (q : ℝ) := by
        calc
          8 * Cvar / (base * T) ≤ scale q 1 := hnearN' q hnq
          _ = (q : ℝ) := by
            unfold scale
            exact Real.rpow_one _
      have hepsLinear : T * (q : ℝ) ≤ eps := by
        dsimp only [eps, t]
        exact le_add_of_nonneg_left hsigma0
      exact inverse_three_halves_scale_absorption (q := q) (b := base)
        (T := T) (C := Cvar) (sigma := Real.sqrt V) (eps := eps)
        hqpos hbase hT hsqrtV hupper hconst hepsLinear
    have houterCoefficient :
        (base / 2) * (eps / Real.sqrt V) ≤
          (eps / Real.sqrt V) *
            (Real.exp (-((Mlin + 1) ^ 2) / 2) / 12 -
              Esseen.relativeEsseenConstant * (2 / R + eta)) -
            (Dshift * Real.sqrt q * (60000 * eps)) / t ^ 2 -
              scale q (-(3 : ℝ) / 2) := by
      have hratio0 : 0 ≤ eps / Real.sqrt V := by positivity
      exact outer_coefficient_after_two_errors hratio0 hbracket
        hshiftAbsorb hnearAbsorb
    have hcancelMain :
        (base / 2) * (eps / Real.sqrt V) * (kclaim / S) =
          base * kclaim / (4 * Real.sqrt V) := by
      dsimp only [S]
      exact half_scale_cancellation heps.ne' hsqrtV.ne'
    have hlocalToMain : klocal * scale q (-(3 : ℝ) / 2) ≤
        base * kclaim / (4 * Real.sqrt V) := by
      have hupper : Real.sqrt V ≤ Cvar * scale q (3 / 2 : ℝ) := by
        rw [GraphQuadratic.scale_three_halves_eq_mul_sqrt hqpos]
        simpa only [V, y, Cvar, Hc, mul_assoc] using hVupper
      dsimp only [klocal]
      exact inverse_three_halves_local_to_variance q hqpos hbase.le hkclaim.le
        hCvar hsqrtV hupper
    have hepsSqrt : eps ≤ Real.sqrt V := by
      exact epsilon_le_sqrt_of_density_scale hcsmall.le hcsmallOne hAdens.le
        (by simpa only [eps, t] using hepsSmall) hVlowerLocal
    have hepsSqrtInput : eps ≤ Real.sqrt
        (vectorSqNorm (countVectorLinearCoefficient
          D.finCoveredPartition hbucket
          (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
            (D.conditionedCoveredCoefficient G c O)))) := by
      exact hepsSqrt
    have hqScale : (q : ℝ) ≤ scale q (3 / 2 : ℝ) := by
      calc
        (q : ℝ) = scale q 1 := by
          unfold scale
          exact (Real.rpow_one (q : ℝ)).symm
        _ ≤ scale q (3 / 2 : ℝ) := scale_mono_exponent hqOne (by norm_num)
    have hdec :
        (fun a b ↦ Classical.propDecidable (G.Adj a b)) = _instAdj :=
      Subsingleton.elim _ _
    have hcenterRaw := abs_conditionedCountVectorBaseCenter_sub_signed_le
      D G e0 c R0 hbucket target s U hs
    rw [hdec] at hcenterRaw
    have hR0' := hR0
    dsimp only [Good, IsGoodLowerRemainder] at hR0'
    rw [hdec] at hR0'
    have hcentralBase :
        |remainderConditionalMean D G e0 c R0 -
            Probability.expectation (1 / 2 : ℝ)
              (Probability.perturbedEdgePolynomial G e0 c)| ≤
          Kouter * Abar * scale n (3 / 2 : ℝ) := by
      exact hR0'.2.le
    have hscaleToV : scale q (3 / 2 : ℝ) ≤
        (2 / Adens) * Real.sqrt V := by
      calc
        scale q (3 / 2 : ℝ) =
            (2 / Adens) * ((Adens / 2) * scale q (3 / 2 : ℝ)) := by
          field_simp [hAdens.ne']
        _ ≤ (2 / Adens) * Real.sqrt V :=
          mul_le_mul_of_nonneg_left hVlowerLocal (by positivity)
    have hU : U ≤ 30001 * Real.sqrt V := by
      have htEps : t ≤ eps := by dsimp only [eps]; linarith
      calc
        U = 30000 * eps + t := rfl
        _ ≤ 30000 * eps + eps := by gcongr
        _ = 30001 * eps := by ring
        _ ≤ 30001 * Real.sqrt V := by gcongr
    have hcenter :
        |conditionedCountVectorBaseCenter D G e0 c O hbucket target - s * U| ≤
          Mlin * Real.sqrt V := by
      dsimp only [Mlin]
      exact center_bound_from_scale_components hAcenter.le
        (by dsimp only [Kouter]; norm_num) (by linarith) hcenterRaw htarget
        hcentralBase hscaleNQ hqScale (by dsimp only [U]; positivity) hU
        hscaleToV
    have hcenterInput :
        |conditionedCountVectorBaseCenter D G e0 c O hbucket target - s * U| ≤
          Mlin * Real.sqrt
            (vectorSqNorm (countVectorLinearCoefficient
              D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G c O)))) := by
      exact hcenter
    have hratioScale :
        2 * (R * eps) *
            (|conditionedCountVectorBaseCenter D G e0 c O hbucket target -
                s * U| + R * eps) ≤ V := by
      have hepsCSqrt : eps ≤ csmall * Real.sqrt V := by
        calc
          eps ≤ csmall * ((Adens / 2) * scale q (3 / 2 : ℝ)) :=
            hepsSmallLocal
          _ ≤ csmall * Real.sqrt V :=
            mul_le_mul_of_nonneg_left hVlowerLocal hcsmall.le
      calc
        2 * (R * eps) *
            (|conditionedCountVectorBaseCenter D G e0 c O hbucket target -
                s * U| + R * eps) ≤ (Real.sqrt V) ^ 2 :=
          quadratic_ratio_bound heps.le hepsCSqrt hcenter hRnonneg hcsmall.le
            (Real.sqrt_nonneg _) hratioCoeff
        _ = V := Real.sq_sqrt hV0
    have hratioScaleInput :
        2 * (R * eps) *
            (|conditionedCountVectorBaseCenter D G e0 c O hbucket target -
                s * U| + R * eps) ≤
          vectorSqNorm (countVectorLinearCoefficient
            D.finCoveredPartition hbucket
            (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
              (D.conditionedCoveredCoefficient G c O))) := by
      exact hratioScale
    have herror := herrorN' q hnq
    have hlowerScale (ell : BucketCountVector D.finCoveredPartition)
        (hell : countVectorShiftMoment D.finCoveredPartition hbucket
          (D.finCoveredGraph G) ell < t ^ 2) :
        lowerScale ≤ countVectorClaim121Scale D G c O hbucket ell := by
      dsimp only [lowerScale, eps, Cscale, sigma0, t]
      exact countVectorClaim121Scale_lower_of_shiftMoment
        D G c O hbucket hrhoF hT.le hqpos hfixed.1 ell hell
    have hraw :
        let y0 := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G c O)
        let V0 := vectorSqNorm
          (countVectorLinearCoefficient D.finCoveredPartition hbucket y0)
        (((eps / Real.sqrt V0) *
              (Real.exp (-((Mlin + 1) ^ 2) / 2) / 12 -
                Esseen.relativeEsseenConstant * (2 / R + eta)) -
            (Dshift * Real.sqrt (Fintype.card D.Covered) * (60000 * eps)) /
              t ^ 2) - scale q (-(3 : ℝ) / 2)) * (kclaim / S) ≤
          ∑ ell : BucketCountVector D.finCoveredPartition,
            countVectorWeight D.finCoveredPartition ell *
              conditionedCountVectorWindowProbability D G e0 c O
                B target ell := by
      apply conditionedCountVector_window_average_lower_explicit
        (D := D) (G := G) (e0 := e0) (c := c) (O := O)
        (K := Dshift) (H := Hc) (A := Adens) (eps := eps)
        (Mlin := Mlin) (R := R) (eta := eta) (delta := 2 * gamma)
        (B := B) (Mclaim := Mclaim) (kappa := kclaim) (s := s)
        (U := U) (t := t) (lowerScale := lowerScale) (S := S)
        (nearBad := scale q (-(3 : ℝ) / 2)) (target := target)
        (hO := hO) (hbucket := hbucket) (hclaim122 := hclaim122)
        (hq := hqpos) (hH := hHc.le) (hA := hAdens)
        (hc0 := fun i ↦ (hcoeffBounds i).1)
        (hcH := fun i ↦ (hcoeffBounds i).2) (hedge := hedge)
        (heps := heps) (hepssigma := hepsSqrtInput) (hMlin := hMlin)
        (hcenter := hcenterInput) (hcoeffScale := hcoeffScale) (hR := hR)
        (hratioScale := hratioScaleInput) (herror := herror) (ht := ht)
        (hFnorm := hFnorm) (hnearBad := hnearBad) (hMclaim := hMclaim)
        (hkappa := hkclaim) (hs := hs) (hS := hS) (hband0 := hband0)
        (hbandM := hbandM) (hshiftScale := hshiftScale)
        (hzeroScale := hzeroScale) (hclaim121 := hclaim121)
        (hlowerScale := hlowerScale) (hcoeffNear := hcoeffNear)
    have houterMain :
        (base / 2) * (eps / Real.sqrt V) * (kclaim / S) ≤
          ∑ ell : BucketCountVector D.finCoveredPartition,
            countVectorWeight D.finCoveredPartition ell *
              conditionedCountVectorWindowProbability D G e0 c O
                B target ell := by
      exact (mul_le_mul_of_nonneg_right houterCoefficient
        (by positivity : 0 ≤ kclaim / S)).trans
        (by simpa only [V, y] using hraw)
    exact hlocalToMain.trans (hcancelMain.symm.le.trans houterMain)
  dsimp only [kappa]
  have hfinal := eventProbability_half_lower_of_structured_good
    D G e0 c B target klocal Good hklocal.le hbadGood hlocal hqpos hqle
  have hdecFinal :
      (fun a b ↦ Classical.propDecidable (G.Adj a b)) = _instAdj :=
    Subsingleton.elim _ _
  rw [hdecFinal] at hfinal
  exact hfinal

end GaussianQuadratic
end Erdos88
