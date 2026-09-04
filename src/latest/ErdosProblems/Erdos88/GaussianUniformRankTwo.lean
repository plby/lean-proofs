import ErdosProblems.Erdos88.GaussianThreeSpectral

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal NNReal BigOperators

namespace Erdos88.GaussianQuadratic

open BooleanSlices

noncomputable def coordinateLinearDecay (a lam t : ℝ) : ℝ :=
  Real.exp (-(a ^ 2 * t ^ 2) / (2 + 8 * lam ^ 2 * t ^ 2))

lemma coordinateLinearDecay_nonneg (a lam t : ℝ) :
    0 ≤ coordinateLinearDecay a lam t := by
  exact Real.exp_nonneg _

lemma coordinateLinearDecay_le_one (a lam t : ℝ) :
    coordinateLinearDecay a lam t ≤ 1 := by
  unfold coordinateLinearDecay
  rw [Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (mul_nonneg (sq_nonneg a) (sq_nonneg t))) (by positivity)

lemma coordinate_charFactor_norm_eq_linearDecay_mul_zero
    (a lam t : ℝ) :
    ‖∫ x : ℝ, cexp ((((t * coordinatePolynomial a lam x : ℝ) : ℂ) * I))
        ∂standardGaussian‖ =
      coordinateLinearDecay a lam t *
        ‖∫ x : ℝ,
          cexp ((((t * coordinatePolynomial 0 lam x : ℝ) : ℂ) * I))
            ∂standardGaussian‖ := by
  rw [coordinate_charFactor_norm, coordinate_charFactor_norm]
  simp [coordinateLinearDecay, div_eq_mul_inv]

lemma diagonalCharModulus_eq_decayProd_mul_zero
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ) (t : ℝ) :
    diagonalCharModulus a lam t =
      (∏ i, coordinateLinearDecay (a i) (lam i) t) *
        diagonalCharModulus (fun _ ↦ 0) lam t := by
  classical
  unfold diagonalCharModulus
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact coordinate_charFactor_norm_eq_linearDecay_mul_zero (a i) (lam i) t

lemma decayProd_le_coordinate
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ) (j : ι) (t : ℝ) :
    (∏ i, coordinateLinearDecay (a i) (lam i) t) ≤
      coordinateLinearDecay (a j) (lam j) t := by
  classical
  calc
    (∏ i, coordinateLinearDecay (a i) (lam i) t) ≤
        ∏ i ∈ ({j} : Finset ι), coordinateLinearDecay (a i) (lam i) t :=
      Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ {j})
        (fun i hi ↦ coordinateLinearDecay_nonneg (a i) (lam i) t)
        (fun i hi hnot ↦ coordinateLinearDecay_le_one (a i) (lam i) t)
    _ = coordinateLinearDecay (a j) (lam j) t := by simp

lemma diagonalCharModulus_le_linearDecay_mul_threeSpectralEnvelope
    {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (j : ι)
    (B : Fin 3 → Finset ι)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin 3)) B)
    {s : ℝ} (hs : 0 ≤ s)
    (hblock : ∀ k, s ≤ ∑ i ∈ B k, (lam i) ^ 2) (t : ℝ) :
    diagonalCharModulus a lam t ≤
      coordinateLinearDecay (a j) (lam j) t * threeSpectralEnvelope s t := by
  rw [diagonalCharModulus_eq_decayProd_mul_zero]
  calc
    (∏ i, coordinateLinearDecay (a i) (lam i) t) *
          diagonalCharModulus (fun _ ↦ 0) lam t ≤
        coordinateLinearDecay (a j) (lam j) t *
          diagonalCharModulus (fun _ ↦ 0) lam t := by
      exact mul_le_mul_of_nonneg_right (decayProd_le_coordinate a lam j t)
        (by unfold diagonalCharModulus; positivity)
    _ ≤ coordinateLinearDecay (a j) (lam j) t *
          threeSpectralEnvelope s t := by
      exact mul_le_mul_of_nonneg_left
        (diagonalCharModulus_le_threeSpectralEnvelope
          (fun _ ↦ 0) lam B (by norm_num)
          (by simpa only [Finset.coe_univ] using hdisj) hs hblock t)
        (coordinateLinearDecay_nonneg _ _ _)

lemma diagonalCharModulus_le_linearDecay
    {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (j : ι) (t : ℝ) :
    diagonalCharModulus a lam t ≤ coordinateLinearDecay (a j) (lam j) t := by
  rw [diagonalCharModulus_eq_decayProd_mul_zero]
  calc
    (∏ i, coordinateLinearDecay (a i) (lam i) t) *
          diagonalCharModulus (fun _ ↦ 0) lam t ≤
        coordinateLinearDecay (a j) (lam j) t *
          diagonalCharModulus (fun _ ↦ 0) lam t :=
      mul_le_mul_of_nonneg_right (decayProd_le_coordinate a lam j t)
        (by unfold diagonalCharModulus; positivity)
    _ ≤ coordinateLinearDecay (a j) (lam j) t * 1 := by
      apply mul_le_mul_of_nonneg_left _ (coordinateLinearDecay_nonneg _ _ _)
      exact (diagonalCharModulus_le (fun _ ↦ 0) lam t).trans (by
        apply Finset.prod_le_one
        · intro i hi
          positivity
        · intro i hi
          apply (inv_le_one₀ (by positivity)).2
          apply Real.one_le_rpow
          · nlinarith [mul_nonneg
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg (lam i)))
              (sq_nonneg t)]
          · norm_num)
    _ = coordinateLinearDecay (a j) (lam j) t := mul_one _

lemma exp_neg_le_one_add_rpow_neg_three_fourths {A : ℝ} (hA : 0 ≤ A) :
    Real.exp (-A) ≤ (1 + A) ^ (-3 / 4 : ℝ) := by
  calc
    Real.exp (-A) = (Real.exp A)⁻¹ := Real.exp_neg A
    _ ≤ (A + 1)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 (Real.add_one_le_exp A)
    _ = (1 + A) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
      congr 1
      ring
    _ ≤ (1 + A) ^ (-3 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · linarith
      · norm_num

lemma linearDecay_mul_threeSpectralEnvelope_le
    (a lam t theta s : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hs : theta * lam ^ 2 / 6 ≤ s) :
    coordinateLinearDecay a lam t * threeSpectralEnvelope s t ≤
      threeSpectralEnvelope
        (theta * coordinateVariance a lam / 48) t := by
  let A : ℝ := a ^ 2 * t ^ 2 / (2 + 8 * lam ^ 2 * t ^ 2)
  let B : ℝ := 4 * s * t ^ 2
  have hD : 0 < 2 + 8 * lam ^ 2 * t ^ 2 := by positivity
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hs0 : 0 ≤ s := by
      have : 0 ≤ theta * lam ^ 2 / 6 := by positivity
      linarith
    positivity
  have hBlarge : (2 * theta / 3) * lam ^ 2 * t ^ 2 ≤ B := by
    dsimp only [B]
    have := mul_le_mul_of_nonneg_right hs (sq_nonneg t)
    nlinarith
  have hdenom :
      theta / 12 * (2 + 8 * lam ^ 2 * t ^ 2) ≤ 1 + B := by
    nlinarith
  have hAterm :
      theta / 12 * (a ^ 2 * t ^ 2) ≤ A * (1 + B) := by
    have hq : 0 ≤ a ^ 2 * t ^ 2 / (2 + 8 * lam ^ 2 * t ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hdenom hq
    dsimp only [A]
    calc
      theta / 12 * (a ^ 2 * t ^ 2) =
          (a ^ 2 * t ^ 2 / (2 + 8 * lam ^ 2 * t ^ 2)) *
            (theta / 12 * (2 + 8 * lam ^ 2 * t ^ 2)) := by
        field_simp [hD.ne']
      _ ≤ (a ^ 2 * t ^ 2 / (2 + 8 * lam ^ 2 * t ^ 2)) * (1 + B) := hmul
  have hlower :
      1 + theta * coordinateVariance a lam * t ^ 2 / 12 ≤
        (1 + A) * (1 + B) := by
    unfold coordinateVariance
    nlinarith
  have htarget :
      0 < 1 + theta * coordinateVariance a lam * t ^ 2 / 12 := by
    have hv := coordinateVariance_nonneg a lam
    positivity
  rw [show coordinateLinearDecay a lam t = Real.exp (-A) by
    unfold coordinateLinearDecay
    congr 1
    dsimp only [A]
    ring]
  unfold threeSpectralEnvelope
  change Real.exp (-A) * (1 + B) ^ (-3 / 4 : ℝ) ≤ _
  calc
    Real.exp (-A) * (1 + B) ^ (-3 / 4 : ℝ) ≤
        (1 + A) ^ (-3 / 4 : ℝ) * (1 + B) ^ (-3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (exp_neg_le_one_add_rpow_neg_three_fourths hA)
        (Real.rpow_nonneg (by positivity) _)
    _ = ((1 + A) * (1 + B)) ^ (-3 / 4 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ (1 + theta * coordinateVariance a lam * t ^ 2 / 12) ^
          (-3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos htarget hlower (by norm_num)
    _ = (1 + 4 * (theta * coordinateVariance a lam / 48) * t ^ 2) ^
          (-3 / 4 : ℝ) := by
      congr 1
      ring

theorem diagonalCharModulus_le_influential_rankTwoEnvelope
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (j : ι) {rho : ℝ} (hrho : 0 < rho)
    (htail : ∀ S : Finset ι, S.card ≤ 2 →
      rho * (∑ i, (lam i) ^ 2) ≤ ∑ i with i ∉ S, (lam i) ^ 2)
    (t : ℝ) :
    diagonalCharModulus a lam t ≤
      threeSpectralEnvelope
        (min rho 1 * coordinateVariance (a j) (lam j) / 48) t := by
  let theta : ℝ := min rho 1
  let q : ℝ := ∑ i, (lam i) ^ 2
  have htheta : 0 < theta := by
    exact lt_min hrho zero_lt_one
  have htheta1 : theta ≤ 1 := min_le_right _ _
  have hthetaRho : theta ≤ rho := min_le_left _ _
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hlamq : (lam j) ^ 2 ≤ q := by
    dsimp only [q]
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (lam i)) (Finset.mem_univ j)
  by_cases hq : q = 0
  · have hlam : (lam j) ^ 2 = 0 := by nlinarith
    calc
      diagonalCharModulus a lam t ≤ coordinateLinearDecay (a j) (lam j) t :=
        diagonalCharModulus_le_linearDecay a lam j t
      _ = coordinateLinearDecay (a j) (lam j) t * threeSpectralEnvelope 0 t := by
        simp [threeSpectralEnvelope]
      _ ≤ threeSpectralEnvelope
          (theta * coordinateVariance (a j) (lam j) / 48) t := by
        apply linearDecay_mul_threeSpectralEnvelope_le
          (a j) (lam j) t theta 0 htheta.le htheta1
        rw [hlam]
        norm_num
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have htailTheta : ∀ S : Finset ι, S.card ≤ 2 →
        theta * q ≤ ∑ i with i ∉ S, (lam i) ^ 2 := by
      intro S hS
      exact (mul_le_mul_of_nonneg_right hthetaRho hq0).trans (htail S hS)
    obtain ⟨B, hdisj, hblock⟩ :=
      exists_three_disjoint_blocks_of_rankTwo_tail
        (fun i ↦ (lam i) ^ 2) (mul_pos htheta hqpos) htailTheta
    have hsLam : theta * (lam j) ^ 2 / 6 ≤ theta * q / 6 := by
      gcongr
    calc
      diagonalCharModulus a lam t ≤
          coordinateLinearDecay (a j) (lam j) t *
            threeSpectralEnvelope (theta * q / 6) t :=
        diagonalCharModulus_le_linearDecay_mul_threeSpectralEnvelope
          a lam j B (by simpa only [Finset.coe_univ] using hdisj)
          (by positivity) hblock t
      _ ≤ threeSpectralEnvelope
          (theta * coordinateVariance (a j) (lam j) / 48) t :=
        linearDecay_mul_threeSpectralEnvelope_le
          (a j) (lam j) t theta (theta * q / 6)
          htheta.le htheta1 hsLam

lemma diagonalCenteredCharProduct_integrable_of_modulus_le_threeEnvelope
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    {s : ℝ} (hs : 0 < s)
    (hmod : ∀ t, diagonalCharModulus a lam t ≤ threeSpectralEnvelope s t) :
    Integrable (diagonalCenteredCharProduct a lam) := by
  apply (threeSpectralEnvelope_integrable hs).mono
  · exact (continuous_diagonalCenteredCharProduct a lam).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_diagonalCenteredCharProduct, Real.norm_eq_abs,
      abs_of_nonneg (threeSpectralEnvelope_nonneg hs.le t)]
    exact hmod t

lemma abs_inverseFourierDensityCandidate_le_of_modulus_le_threeEnvelope
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    {s : ℝ} (hs : 0 < s)
    (hmod : ∀ t, diagonalCharModulus a lam t ≤ threeSpectralEnvelope s t)
    (u : ℝ) :
    |inverseFourierDensityCandidate (diagonalCenteredCharProduct a lam) u| ≤
      threeSpectralMass / (4 * Real.pi * Real.sqrt s) := by
  let phi := diagonalCenteredCharProduct a lam
  let p := inverseFourierDensityCandidate phi
  have hchar : Integrable phi :=
    diagonalCenteredCharProduct_integrable_of_modulus_le_threeEnvelope
      a lam hs hmod
  have hInv : HasInverseFourierDensity p phi :=
    inverseFourierDensityCandidate_hasInverse
      (diagonalCenteredCharProduct_neg a lam)
  have hphase (t : ℝ) :
      ‖phi t * Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I))‖ =
        ‖phi t‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have hnormInt : (∫ t : ℝ, ‖phi t‖) ≤
      threeSpectralMass / (2 * Real.sqrt s) := by
    calc
      (∫ t : ℝ, ‖phi t‖) ≤ ∫ t : ℝ, threeSpectralEnvelope s t := by
        apply integral_mono hchar.norm (threeSpectralEnvelope_integrable hs)
        intro t
        dsimp only [phi]
        rw [norm_diagonalCenteredCharProduct]
        exact hmod t
      _ = threeSpectralMass / (2 * Real.sqrt s) :=
        integral_threeSpectralEnvelope hs
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hInv u, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  calc
    (2 * Real.pi)⁻¹ *
        ‖∫ t : ℝ, phi t * Complex.exp
          (-(((t * u : ℝ) : ℂ) * Complex.I))‖ ≤
        (2 * Real.pi)⁻¹ *
          ∫ t : ℝ, ‖phi t * Complex.exp
            (-(((t * u : ℝ) : ℂ) * Complex.I))‖ := by
      gcongr
      exact norm_integral_le_integral_norm _
    _ = (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖phi t‖ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hphase
    _ ≤ (2 * Real.pi)⁻¹ *
        (threeSpectralMass / (2 * Real.sqrt s)) := by gcongr
    _ = threeSpectralMass / (4 * Real.pi * Real.sqrt s) := by
      field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hs).ne']
      ring

theorem smallBall_diagonalCenteredLaw_le_of_modulus_le_threeEnvelope
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    {s : ℝ} (hs : 0 < s)
    (hmod : ∀ t, diagonalCharModulus a lam t ≤ threeSpectralEnvelope s t)
    {eps : ℝ} (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall (diagonalCenteredLaw a lam) eps x ≤
      eps * threeSpectralMass / (2 * Real.pi * Real.sqrt s) := by
  let : IsProbabilityMeasure (diagonalCenteredLaw a lam) :=
    diagonalCenteredLaw_isProbabilityMeasure a lam
  let phi := diagonalCenteredCharProduct a lam
  let p := inverseFourierDensityCandidate (charFun (diagonalCenteredLaw a lam))
  have hchar : Integrable phi :=
    diagonalCenteredCharProduct_integrable_of_modulus_le_threeEnvelope
      a lam hs hmod
  have hlawChar : Integrable (charFun (diagonalCenteredLaw a lam)) := by
    rw [charFun_diagonalCenteredLaw]
    exact hchar
  have hdens : Erdos88.Esseen.HasContinuousDensity
      (diagonalCenteredLaw a lam) p :=
    hasContinuousDensity_inverseFourierDensityCandidate
      (diagonalCenteredLaw a lam) hlawChar
  rw [hdens.smallBall_eq_integral eps x heps]
  calc
    (∫ y in (x - eps)..(x + eps), p y) ≤
        ∫ _y in (x - eps)..(x + eps),
          (threeSpectralMass / (4 * Real.pi * Real.sqrt s) : ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (hdens.continuous.intervalIntegrable _ _) intervalIntegrable_const
      intro y hy
      exact (le_abs_self (p y)).trans (by
        dsimp only [p]
        rw [charFun_diagonalCenteredLaw]
        exact abs_inverseFourierDensityCandidate_le_of_modulus_le_threeEnvelope
          a lam hs hmod y)
    _ = eps * threeSpectralMass / (2 * Real.pi * Real.sqrt s) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hs).ne']
      ring

theorem smallBall_diagonalCenteredLaw_le_of_influential_rankTwo_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (j : ι) {rho : ℝ} (hrho : 0 < rho)
    (htail : ∀ S : Finset ι, S.card ≤ 2 →
      rho * (∑ i, (lam i) ^ 2) ≤ ∑ i with i ∉ S, (lam i) ^ 2)
    (hj : 1 / 4 < coordinateVariance (a j) (lam j))
    {eps : ℝ} (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall (diagonalCenteredLaw a lam) eps x ≤
      eps * threeSpectralMass /
        (2 * Real.pi * Real.sqrt
          (min rho 1 * coordinateVariance (a j) (lam j) / 48)) := by
  have hs : 0 < min rho 1 * coordinateVariance (a j) (lam j) / 48 := by
    have htheta : 0 < min rho 1 := lt_min hrho zero_lt_one
    positivity
  apply smallBall_diagonalCenteredLaw_le_of_modulus_le_threeEnvelope
    a lam hs _ heps x
  intro t
  exact diagonalCharModulus_le_influential_rankTwoEnvelope a lam j hrho htail t

theorem smallBall_diagonalCenteredLaw_le_of_relative_rankTwo_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (hsum : totalVariance a lam = 1)
    {rho : ℝ} (hrho : 0 < rho)
    (htail : ∀ S : Finset ι, S.card ≤ 2 →
      rho * (∑ i, (lam i) ^ 2) ≤ ∑ i with i ∉ S, (lam i) ^ 2)
    {eps : ℝ} (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall (diagonalCenteredLaw a lam) eps x ≤
      2 * eps + eps * threeSpectralMass /
        (2 * Real.pi * Real.sqrt (min rho 1 / 192)) := by
  have htheta : 0 < min rho 1 := lt_min hrho zero_lt_one
  have hs0 : 0 < min rho 1 / 192 := by positivity
  have hden0 : 0 < 2 * Real.pi * Real.sqrt (min rho 1 / 192) := by
    positivity
  have htailTerm0 :
      0 ≤ eps * threeSpectralMass /
        (2 * Real.pi * Real.sqrt (min rho 1 / 192)) :=
    div_nonneg (mul_nonneg heps threeSpectralMass_nonneg) hden0.le
  by_cases hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 4
  · have hraw := smallBall_diagonalCenteredLaw_le_two_mul_of_small_coordinates
      a lam hsum hsmall heps x
    linarith
  · push_neg at hsmall
    obtain ⟨j, hj⟩ := hsmall
    have hraw := smallBall_diagonalCenteredLaw_le_of_influential_rankTwo_tail
      a lam j hrho htail hj heps x
    have hscale : min rho 1 / 192 ≤
        min rho 1 * coordinateVariance (a j) (lam j) / 48 := by
      have := mul_lt_mul_of_pos_left hj htheta
      nlinarith
    have hsqrt : Real.sqrt (min rho 1 / 192) ≤
        Real.sqrt (min rho 1 * coordinateVariance (a j) (lam j) / 48) :=
      Real.sqrt_le_sqrt hscale
    have hden :
        2 * Real.pi * Real.sqrt (min rho 1 / 192) ≤
          2 * Real.pi *
            Real.sqrt (min rho 1 * coordinateVariance (a j) (lam j) / 48) := by
      gcongr
    have hscaled :
        eps * threeSpectralMass /
            (2 * Real.pi *
              Real.sqrt (min rho 1 * coordinateVariance (a j) (lam j) / 48)) ≤
          eps * threeSpectralMass /
            (2 * Real.pi * Real.sqrt (min rho 1 / 192)) := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg heps threeSpectralMass_nonneg) hden0 hden
    exact hraw.trans (hscaled.trans (by linarith))

theorem smallBall_gaussianQuadraticCenteredLaw_map_div_le_of_relative_robustRankTwo
    {n : ℕ} (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {sigma rho eps : ℝ} (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f)
    (hrho : 0 < rho)
    (hrob : RobustRankAt 2 (rho * frobeniusSq F) F)
    (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall
        ((gaussianQuadraticCenteredLaw f F).map (fun y ↦ y / sigma)) eps x ≤
      2 * eps + eps * threeSpectralMass /
        (2 * Real.pi * Real.sqrt (min rho 1 / 192)) := by
  let a : Fin n → ℝ := fun i ↦ eigenLinearCoefficient hF f i / sigma
  let lam : Fin n → ℝ := fun i ↦ hF.eigenvalues i / sigma
  have hsum : totalVariance a lam = 1 := by
    exact totalVariance_normalized_eigenbasis hF f hsigma hsigmaSq
  have htail : ∀ S : Finset (Fin n), S.card ≤ 2 →
      rho * (∑ i, (lam i) ^ 2) ≤ ∑ i with i ∉ S, (lam i) ^ 2 := by
    intro S hS
    have hraw := robustRankAt_eigenvalue_tail hF hrob S hS
    have hsigmaSqPos : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
    have htotal : (∑ i, (lam i) ^ 2) = frobeniusSq F / sigma ^ 2 := by
      dsimp only [lam]
      simp_rw [div_pow]
      rw [← Finset.sum_div, sum_sq_eigenvalues_eq_frobeniusSq]
    have hout : (∑ i with i ∉ S, (lam i) ^ 2) =
        (∑ i with i ∉ S, (hF.eigenvalues i) ^ 2) / sigma ^ 2 := by
      dsimp only [lam]
      simp_rw [div_pow]
      rw [← Finset.sum_div]
    rw [htotal, hout]
    calc
      rho * (frobeniusSq F / sigma ^ 2) =
          (rho * frobeniusSq F) / sigma ^ 2 := by rw [mul_div_assoc]
      _ ≤ (∑ i with i ∉ S, (hF.eigenvalues i) ^ 2) / sigma ^ 2 :=
        (div_le_div_iff_of_pos_right hsigmaSqPos).2 hraw
  rw [gaussianQuadraticCenteredLaw_map_div_eq_diagonal f hF hsigma.ne']
  exact smallBall_diagonalCenteredLaw_le_of_relative_rankTwo_tail
    a lam hsum hrho htail heps x

end Erdos88.GaussianQuadratic
