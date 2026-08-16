import Wikipedia.GreenTao.Sieve.WTrickedEulerCorrection

/-!
# Quantitative convergence of the W-tricked Euler correction

`WTrickedEulerCorrection` writes the normalized finite small-prime
correction as

`∏_{p ≤ w} ((1 - p⁻¹)^m * Z_p(z, v)⁻¹)`.

This file controls that product when every phase is close to one.  The
important cancellation is

`z + v - z v - 1 = -(1-z)(1-v)`,

so the perturbation is quadratic in the phase error.  We first prove a
one-pair bound valid at every prime, then accumulate it over the finite
form system and over all primes at most `w`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology

/-! ## One paired phase -/

/-- A zeta numerator has norm at least one half at every prime when its
phase lies in the closed unit ball. -/
theorem one_half_le_norm_phaseZetaNumerator
    {p : ℕ} (hp : p.Prime)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (1 : ℝ) / 2 ≤
      ‖1 - (p : ℂ)⁻¹ * z‖ := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hsmall :
      ‖(p : ℂ)⁻¹ * z‖ ≤ (1 : ℝ) / 2 := by
    calc
      ‖(p : ℂ)⁻¹ * z‖ =
          (1 / (p : ℝ)) * ‖z‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        ring
      _ ≤ (1 / (p : ℝ)) * 1 := by
        exact mul_le_mul_of_nonneg_left hz
          (one_div_nonneg.mpr hpR.le)
      _ ≤ (1 : ℝ) / 2 := by
        simp only [mul_one]
        rw [div_le_iff₀ hpR]
        have hp2R : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast hp.two_le
        nlinarith
  calc
    (1 : ℝ) / 2 ≤
        1 - ‖(p : ℂ)⁻¹ * z‖ := by
      linarith
    _ = ‖(1 : ℂ)‖ -
          ‖(p : ℂ)⁻¹ * z‖ := by
      rw [norm_one]
    _ ≤ ‖1 - (p : ℂ)⁻¹ * z‖ :=
      norm_sub_norm_le _ _

/-- The normalized residual for one paired phase. -/
noncomputable def phasePairNormalizationResidual
    (p : ℕ) (z v : ℂ) : ℂ :=
  (1 - (p : ℂ)⁻¹) *
    (phasePairZetaEulerLocalModel p z v)⁻¹

/-- Exact quadratic cancellation before dividing by the shifted pair
factor. -/
theorem phasePairZetaEulerLocalModel_sub_unshifted_eq
    {p : ℕ} (hp : p.Prime)
    {z v : ℂ} (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    phasePairZetaEulerLocalModel p z v -
        (1 - (p : ℂ)⁻¹) =
      ((p : ℂ)⁻¹ * (1 - z) * (1 - v)) /
        (1 - (p : ℂ)⁻¹ * z * v) := by
  have hd0 :
      1 - (p : ℂ)⁻¹ * z * v ≠ 0 :=
    phasePairZetaDenominator_ne_zero hp hz hv
  rw [phasePairZetaEulerLocalModel]
  apply (eq_div_iff hd0).2
  rw [sub_mul, div_mul_cancel₀ _ hd0]
  ring

/-- A paired zeta factor has a uniform lower norm bound at every prime. -/
theorem one_sixth_le_norm_phasePairZetaEulerLocalModel
    {p : ℕ} (hp : p.Prime)
    {z v : ℂ} (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    (1 : ℝ) / 6 ≤
      ‖phasePairZetaEulerLocalModel p z v‖ := by
  have hzhalf :=
    one_half_le_norm_phaseZetaNumerator hp hz
  have hvhalf :=
    one_half_le_norm_phaseZetaNumerator hp hv
  have hdhalf :=
    one_half_le_norm_phasePairZetaDenominator hp hz hv
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hsmall :
      ‖(p : ℂ)⁻¹ * z * v‖ ≤ (1 : ℝ) / 2 := by
    calc
      ‖(p : ℂ)⁻¹ * z * v‖ =
          (1 / (p : ℝ)) * ‖z‖ * ‖v‖ := by
        rw [norm_mul, norm_mul, norm_inv,
          Complex.norm_natCast]
        ring
      _ ≤ (1 / (p : ℝ)) * 1 * 1 := by
        gcongr
      _ ≤ (1 : ℝ) / 2 := by
        simp only [mul_one]
        rw [div_le_iff₀ hpR]
        have hp2R : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast hp.two_le
        nlinarith
  have hdUpper :
      ‖1 - (p : ℂ)⁻¹ * z * v‖ ≤
        (3 : ℝ) / 2 := by
    calc
      ‖1 - (p : ℂ)⁻¹ * z * v‖ ≤
          ‖(1 : ℂ)‖ +
            ‖(p : ℂ)⁻¹ * z * v‖ :=
        norm_sub_le _ _
      _ ≤ (3 : ℝ) / 2 := by
        rw [norm_one]
        linarith
  have hdPos :
      0 < ‖1 - (p : ℂ)⁻¹ * z * v‖ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      hdhalf
  rw [phasePairZetaEulerLocalModel,
    Complex.norm_div, norm_mul]
  rw [le_div_iff₀ hdPos]
  nlinarith [norm_nonneg
    (1 - (p : ℂ)⁻¹ * z),
    norm_nonneg (1 - (p : ℂ)⁻¹ * v)]

/-- Quadratic difference bound before normalizing by the pair factor. -/
theorem norm_phasePairZetaEulerLocalModel_sub_unshifted_le
    {p : ℕ} (hp : p.Prime)
    {z v : ℂ} (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hzclose : ‖z - 1‖ ≤ δ)
    (hvclose : ‖v - 1‖ ≤ δ) :
    ‖phasePairZetaEulerLocalModel p z v -
        (1 - (p : ℂ)⁻¹)‖ ≤
      2 * δ ^ 2 / (p : ℝ) := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hdhalf :=
    one_half_le_norm_phasePairZetaDenominator hp hz hv
  have hdPos :
      0 < ‖1 - (p : ℂ)⁻¹ * z * v‖ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      hdhalf
  have hzclose' : ‖1 - z‖ ≤ δ := by
    rw [norm_sub_rev]
    exact hzclose
  have hvclose' : ‖1 - v‖ ≤ δ := by
    rw [norm_sub_rev]
    exact hvclose
  rw [phasePairZetaEulerLocalModel_sub_unshifted_eq
    hp hz hv, Complex.norm_div, norm_mul, norm_mul,
    norm_inv, Complex.norm_natCast]
  rw [div_le_iff₀ hdPos]
  have hnum :
      (p : ℝ)⁻¹ * ‖1 - z‖ * ‖1 - v‖ ≤
        (1 / (p : ℝ)) * δ ^ 2 := by
    calc
      (p : ℝ)⁻¹ * ‖1 - z‖ * ‖1 - v‖ ≤
          (p : ℝ)⁻¹ * δ * δ := by
        gcongr
      _ = (1 / (p : ℝ)) * δ ^ 2 := by
        rw [one_div]
        ring
  calc
    (p : ℝ)⁻¹ * ‖1 - z‖ * ‖1 - v‖ ≤
        (1 / (p : ℝ)) * δ ^ 2 :=
      hnum
    _ ≤
        (2 * δ ^ 2 / (p : ℝ)) *
          ‖1 - (p : ℂ)⁻¹ * z * v‖ := by
      calc
        (1 / (p : ℝ)) * δ ^ 2 =
            (2 * δ ^ 2 / (p : ℝ)) *
              ((1 : ℝ) / 2) := by
          field_simp
        _ ≤
            (2 * δ ^ 2 / (p : ℝ)) *
              ‖1 - (p : ℂ)⁻¹ * z * v‖ :=
          mul_le_mul_of_nonneg_left hdhalf
            (div_nonneg
              (mul_nonneg (by norm_num) (sq_nonneg δ))
              hpR.le)

/-- If both phases are within `δ` of one, one normalized pair residual is
within `12 δ² / p` of one. -/
theorem norm_phasePairNormalizationResidual_sub_one_le
    {p : ℕ} (hp : p.Prime)
    {z v : ℂ} (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hzclose : ‖z - 1‖ ≤ δ)
    (hvclose : ‖v - 1‖ ≤ δ) :
    ‖phasePairNormalizationResidual p z v - 1‖ ≤
      12 * δ ^ 2 / (p : ℝ) := by
  let Q := phasePairZetaEulerLocalModel p z v
  have hQlower :
      (1 : ℝ) / 6 ≤ ‖Q‖ := by
    exact one_sixth_le_norm_phasePairZetaEulerLocalModel
      hp hz hv
  have hQpos : 0 < ‖Q‖ :=
    (by norm_num : (0 : ℝ) < 1 / 6).trans_le
      hQlower
  have hQ0 : Q ≠ 0 :=
    norm_pos_iff.mp hQpos
  have hdiff :=
    norm_phasePairZetaEulerLocalModel_sub_unshifted_le
      hp hz hv hδ hzclose hvclose
  rw [phasePairNormalizationResidual,
    ← div_eq_mul_inv, div_sub_one hQ0,
    Complex.norm_div]
  have hreverse :
      ‖(1 - (p : ℂ)⁻¹) - Q‖ ≤
        2 * δ ^ 2 / (p : ℝ) := by
    rw [norm_sub_rev]
    exact hdiff
  rw [div_le_iff₀ hQpos]
  calc
    ‖(1 - (p : ℂ)⁻¹) - Q‖ ≤
        2 * δ ^ 2 / (p : ℝ) :=
      hreverse
    _ =
        (12 * δ ^ 2 / (p : ℝ)) *
          ((1 : ℝ) / 6) := by
      field_simp
      ring
    _ ≤
        (12 * δ ^ 2 / (p : ℝ)) * ‖Q‖ :=
      mul_le_mul_of_nonneg_left hQlower
        (div_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg δ))
          (by exact_mod_cast hp.pos.le))

/-! ## A finite system at one prime -/

/-- The normalized residual of a finite phase system at one prime. -/
noncomputable def phaseSystemNormalizationResidual
    {κ : Type*} [Fintype κ]
    (p : ℕ) (z v : κ → ℂ) : ℂ :=
  unshiftedZetaSystemLocalFactor
      (Fintype.card κ) p *
    (phaseZetaSystemEulerLocalFactor p z v)⁻¹

/-- The normalized system residual factors into the normalized residuals
of its paired coordinates. -/
theorem phaseSystemNormalizationResidual_eq_prod
    {κ : Type*} [Fintype κ]
    (p : ℕ) (z v : κ → ℂ) :
    phaseSystemNormalizationResidual p z v =
      ∏ q, phasePairNormalizationResidual p (z q) (v q) := by
  rw [phaseSystemNormalizationResidual,
    unshiftedZetaSystemLocalFactor,
    phaseZetaSystemEulerLocalFactor,
    ← Finset.prod_inv_distrib]
  have hconst :
      (1 - (p : ℂ)⁻¹) ^ Fintype.card κ =
        ∏ _q : κ, (1 - (p : ℂ)⁻¹) := by
    simp
  rw [hconst, ← Finset.prod_mul_distrib]
  simp [phasePairNormalizationResidual]

/-- Accumulating the quadratic pair estimate across a finite system gives
an explicit exponential error bound. -/
theorem norm_phaseSystemNormalizationResidual_sub_one_le
    {κ : Type*} [Fintype κ]
    {p : ℕ} (hp : p.Prime)
    (z v : κ → ℂ)
    (hz : ∀ q, ‖z q‖ ≤ 1)
    (hv : ∀ q, ‖v q‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hzclose : ∀ q, ‖z q - 1‖ ≤ δ)
    (hvclose : ∀ q, ‖v q - 1‖ ≤ δ) :
    ‖phaseSystemNormalizationResidual p z v - 1‖ ≤
      Real.exp
          ((Fintype.card κ : ℝ) *
            (12 * δ ^ 2 / (p : ℝ))) -
        1 := by
  rw [phaseSystemNormalizationResidual_eq_prod]
  have hbase :=
    (Finset.univ : Finset κ).norm_prod_one_add_sub_one_le
      (fun q =>
        phasePairNormalizationResidual p (z q) (v q) - 1)
  have heq :
      (fun q : κ =>
        1 +
          (phasePairNormalizationResidual p
            (z q) (v q) - 1)) =
        fun q =>
          phasePairNormalizationResidual p (z q) (v q) := by
    funext q
    ring
  rw [heq] at hbase
  have hsum :
      (∑ q : κ,
          ‖phasePairNormalizationResidual p
              (z q) (v q) - 1‖) ≤
        (Fintype.card κ : ℝ) *
          (12 * δ ^ 2 / (p : ℝ)) := by
    calc
      (∑ q : κ,
          ‖phasePairNormalizationResidual p
              (z q) (v q) - 1‖) ≤
          ∑ _q : κ, 12 * δ ^ 2 / (p : ℝ) := by
        apply Finset.sum_le_sum
        intro q _hq
        exact
          norm_phasePairNormalizationResidual_sub_one_le
            hp (hz q) (hv q) hδ
            (hzclose q) (hvclose q)
      _ =
          (Fintype.card κ : ℝ) *
            (12 * δ ^ 2 / (p : ℝ)) := by
        simp
  exact hbase.trans
    (sub_le_sub_right
      (Real.exp_le_exp.mpr hsum) 1)

/-! ## Accumulation over the small primes -/

/-- There are at most `w + 1` primes in the small-prime finset. -/
theorem card_smallPrimeFinset_le (w : ℕ) :
    (smallPrimeFinset w).card ≤ w + 1 := by
  calc
    (smallPrimeFinset w).card =
        (Nat.primesLE w).card := by
      simp [smallPrimeFinset]
    _ ≤ (Finset.range (w + 1)).card := by
      apply Finset.card_le_card
      rw [Nat.primesLE_eq_filter_range]
      exact Finset.filter_subset _ _
    _ = w + 1 := by
      simp

/-- The normalized correction is the product of the one-prime normalized
phase-system residuals. -/
theorem normalizedSmallPrimeZetaCorrection_eq_prod_phaseSystemResidual
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (w : ℕ) (t u : κ → ℝ) :
    normalizedSmallPrimeZetaCorrection R w t u =
      ∏ p ∈ smallPrimeFinset w,
        phaseSystemNormalizationResidual (p : ℕ)
          (fun q =>
            SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) (t q))
          (fun q =>
            SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) (u q)) := by
  rw [normalizedSmallPrimeZetaCorrection_eq_phaseResidual
    hR]
  apply Finset.prod_congr rfl
  intro p _hp
  rfl

/-- Fully explicit finite-product estimate.  It retains the saving from
each individual prime instead of replacing `p` by the worst case `2`. -/
theorem norm_normalizedSmallPrimeZetaCorrection_sub_one_le_exp_sum
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (w : ℕ) (t u : κ → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (htclose :
      ∀ p ∈ smallPrimeFinset w, ∀ q,
        ‖SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (t q) - 1‖ ≤ δ)
    (huclose :
      ∀ p ∈ smallPrimeFinset w, ∀ q,
        ‖SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (u q) - 1‖ ≤ δ) :
    ‖normalizedSmallPrimeZetaCorrection R w t u - 1‖ ≤
      Real.exp
          (∑ p ∈ smallPrimeFinset w,
            (Real.exp
                ((Fintype.card κ : ℝ) *
                  (12 * δ ^ 2 / (p : ℝ))) -
              1)) -
        1 := by
  rw [normalizedSmallPrimeZetaCorrection_eq_prod_phaseSystemResidual
    hR]
  let localResidual : Nat.Primes → ℂ :=
    fun p =>
      phaseSystemNormalizationResidual (p : ℕ)
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (t q))
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (u q))
  have hbase :=
    (smallPrimeFinset w).norm_prod_one_add_sub_one_le
      (fun p => localResidual p - 1)
  have heq :
      (fun p : Nat.Primes =>
        1 + (localResidual p - 1)) =
        localResidual := by
    funext p
    ring
  rw [heq] at hbase
  have hsum :
      (∑ p ∈ smallPrimeFinset w,
          ‖localResidual p - 1‖) ≤
        ∑ p ∈ smallPrimeFinset w,
          (Real.exp
              ((Fintype.card κ : ℝ) *
                (12 * δ ^ 2 / (p : ℝ))) -
            1) := by
    apply Finset.sum_le_sum
    intro p hp
    exact
      norm_phaseSystemNormalizationResidual_sub_one_le
        p.prop
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (t q))
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (u q))
        (fun q =>
          SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
            hR p.prop (t q))
        (fun q =>
          SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
            hR p.prop (u q))
        hδ (htclose p hp) (huclose p hp)
  exact hbase.trans
    (sub_le_sub_right
      (Real.exp_le_exp.mpr hsum) 1)

/-- Worst-prime and cardinality simplification of the preceding bound. -/
theorem norm_normalizedSmallPrimeZetaCorrection_sub_one_le_exp
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (w : ℕ) (t u : κ → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (htclose :
      ∀ p ∈ smallPrimeFinset w, ∀ q,
        ‖SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (t q) - 1‖ ≤ δ)
    (huclose :
      ∀ p ∈ smallPrimeFinset w, ∀ q,
        ‖SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (u q) - 1‖ ≤ δ) :
    ‖normalizedSmallPrimeZetaCorrection R w t u - 1‖ ≤
      Real.exp
          ((w + 1 : ℕ) *
            (Real.exp
                (6 * (Fintype.card κ : ℝ) * δ ^ 2) -
              1)) -
        1 := by
  have hsum :=
    norm_normalizedSmallPrimeZetaCorrection_sub_one_le_exp_sum
      hR w t u hδ htclose huclose
  refine hsum.trans ?_
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  calc
    (∑ p ∈ smallPrimeFinset w,
        (Real.exp
            ((Fintype.card κ : ℝ) *
              (12 * δ ^ 2 / (p : ℝ))) -
          1)) ≤
        ∑ _p ∈ smallPrimeFinset w,
          (Real.exp
              (6 * (Fintype.card κ : ℝ) * δ ^ 2) -
            1) := by
      apply Finset.sum_le_sum
      intro p _hp
      apply sub_le_sub_right
      apply Real.exp_le_exp.mpr
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast p.prop.two_le
      have hδsq : 0 ≤ δ ^ 2 :=
        sq_nonneg δ
      have hm : 0 ≤ (Fintype.card κ : ℝ) :=
        Nat.cast_nonneg _
      have hpPos : (0 : ℝ) < (p : ℕ) := by
        exact_mod_cast p.prop.pos
      have hlocal :
          12 * δ ^ 2 / (p : ℝ) ≤
            6 * δ ^ 2 := by
        apply (div_le_iff₀ hpPos).2
        nlinarith
      exact
        (mul_le_mul_of_nonneg_left hlocal hm).trans_eq
          (by ring)
    _ =
        ((smallPrimeFinset w).card : ℝ) *
          (Real.exp
              (6 * (Fintype.card κ : ℝ) * δ ^ 2) -
            1) := by
      simp
      ring
    _ ≤
        (w + 1 : ℕ) *
          (Real.exp
              (6 * (Fintype.card κ : ℝ) * δ ^ 2) -
            1) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_smallPrimeFinset_le w
      · exact sub_nonneg.mpr
          (Real.one_le_exp
            (mul_nonneg
              (mul_nonneg (by norm_num)
                (Nat.cast_nonneg _))
              (sq_nonneg δ)))

/-! ## The actual cutoff phases -/

/-- Common logarithmic phase-size bound on primes at most `w` and Fourier
parameters of absolute value at most `T`. -/
noncomputable def cutoffPhaseMagnitudeBound
    (R w : ℕ) (T : ℝ) : ℝ :=
  (Real.log w / Real.log R) *
    (1 + 2 * Real.pi * T)

/-- Norm bound for the exponent defining a cutoff multiplicative phase. -/
theorem norm_cutoffPhaseExponent_le
    {x t T : ℝ} (hx : 0 ≤ x)
    (ht : |t| ≤ T) :
    ‖-(x : ℂ) +
        ((2 * Real.pi * (t * x) : ℝ) : ℂ) *
          Complex.I‖ ≤
      x * (1 + 2 * Real.pi * T) := by
  have htwoPi : 0 ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hosc :
      |2 * Real.pi * (t * x)| ≤
        2 * Real.pi * T * x := by
    calc
      |2 * Real.pi * (t * x)| =
          (2 * Real.pi) * |t| * x := by
        calc
          |2 * Real.pi * (t * x)| =
              |2 * Real.pi| * |t * x| := by
            rw [abs_mul]
          _ =
              (2 * Real.pi) * (|t| * |x|) := by
            rw [abs_of_nonneg htwoPi, abs_mul]
          _ = (2 * Real.pi) * |t| * x := by
            rw [abs_of_nonneg hx]
            ring
      _ ≤ (2 * Real.pi) * T * x := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ht htwoPi) hx
  calc
    ‖-(x : ℂ) +
        ((2 * Real.pi * (t * x) : ℝ) : ℂ) *
          Complex.I‖ ≤
        ‖-(x : ℂ)‖ +
          ‖((2 * Real.pi * (t * x) : ℝ) : ℂ) *
            Complex.I‖ :=
      norm_add_le _ _
    _ =
        x + |2 * Real.pi * (t * x)| := by
      rw [norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hx,
        norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, mul_one]
    _ ≤ x + 2 * Real.pi * T * x := by
      linarith
    _ = x * (1 + 2 * Real.pi * T) := by
      ring

/-- A cutoff phase is close to one when its exponent bound is at most one. -/
theorem norm_cutoffMultiplicativePhase_sub_one_le
    {x t T : ℝ} (hx : 0 ≤ x)
    (ht : |t| ≤ T)
    (hsmall : x * (1 + 2 * Real.pi * T) ≤ 1) :
    ‖SmoothSieveCutoff.cutoffMultiplicativePhase x t - 1‖ ≤
      2 * x * (1 + 2 * Real.pi * T) := by
  have hexponent :=
    norm_cutoffPhaseExponent_le hx ht
  rw [SmoothSieveCutoff.cutoffMultiplicativePhase]
  exact
    (Complex.norm_exp_sub_one_le
      (hexponent.trans hsmall)).trans
      (by nlinarith)

/-- Uniform actual-phase estimate on all primes at most `w`. -/
theorem norm_divisorMultiplicativePhase_sub_one_le_bound
    {R w : ℕ} (hR : 1 < R) (hw : 2 ≤ w)
    {T : ℝ} (hT : 0 ≤ T)
    {p : Nat.Primes} (hpw : (p : ℕ) ≤ w)
    {t : ℝ} (ht : |t| ≤ T)
    (hsmall : cutoffPhaseMagnitudeBound R w T ≤ 1) :
    ‖SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) t - 1‖ ≤
      2 * cutoffPhaseMagnitudeBound R w T := by
  have hlogR :
      0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  have hlogp :
      0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg
      (by exact_mod_cast p.prop.one_le)
  have hlogw :
      0 ≤ Real.log (w : ℝ) :=
    Real.log_nonneg
      (by exact_mod_cast (Nat.one_le_of_lt hw))
  have hlogle :
      Real.log (p : ℝ) ≤ Real.log (w : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast p.prop.pos)
      (by exact_mod_cast hpw)
  have hx :
      0 ≤ Real.log (p : ℝ) / Real.log R :=
    div_nonneg hlogp hlogR.le
  have hxle :
      Real.log (p : ℝ) / Real.log R ≤
        Real.log (w : ℝ) / Real.log R :=
    div_le_div_of_nonneg_right hlogle hlogR.le
  have hcoef :
      0 ≤ 1 + 2 * Real.pi * T := by
    positivity
  have hphaseBound :
      (Real.log (p : ℝ) / Real.log R) *
          (1 + 2 * Real.pi * T) ≤
        cutoffPhaseMagnitudeBound R w T := by
    rw [cutoffPhaseMagnitudeBound]
    exact mul_le_mul_of_nonneg_right hxle hcoef
  rw [SmoothSieveCutoff.divisorMultiplicativePhase]
  refine
    (norm_cutoffMultiplicativePhase_sub_one_le
      hx ht (hphaseBound.trans hsmall)).trans ?_
  calc
    2 *
          (Real.log (p : ℝ) / Real.log R) *
          (1 + 2 * Real.pi * T) =
        2 *
          ((Real.log (p : ℝ) / Real.log R) *
            (1 + 2 * Real.pi * T)) := by
      ring
    _ ≤ 2 * cutoffPhaseMagnitudeBound R w T :=
      mul_le_mul_of_nonneg_left hphaseBound (by norm_num)

/-- Explicit correction estimate in the actual truncated Fourier box. -/
theorem norm_normalizedSmallPrimeZetaCorrection_sub_one_le_box
    {κ : Type*} [Fintype κ]
    {R w : ℕ} (hR : 1 < R) (hw : 2 ≤ w)
    {T : ℝ} (hT : 0 ≤ T)
    (t u : κ → ℝ)
    (ht : ∀ q, |t q| ≤ T)
    (hu : ∀ q, |u q| ≤ T)
    (hsmall : cutoffPhaseMagnitudeBound R w T ≤ 1) :
    ‖normalizedSmallPrimeZetaCorrection R w t u - 1‖ ≤
      Real.exp
          ((w + 1 : ℕ) *
            (Real.exp
                (24 * (Fintype.card κ : ℝ) *
                  cutoffPhaseMagnitudeBound R w T ^ 2) -
              1)) -
        1 := by
  have hA0 :
      0 ≤ cutoffPhaseMagnitudeBound R w T := by
    rw [cutoffPhaseMagnitudeBound]
    have hlogR :
        0 < Real.log (R : ℝ) :=
      Real.log_pos (by exact_mod_cast hR)
    have hlogw :
        0 ≤ Real.log (w : ℝ) :=
      Real.log_nonneg
        (by exact_mod_cast (Nat.one_le_of_lt hw))
    positivity
  have hbound :=
    norm_normalizedSmallPrimeZetaCorrection_sub_one_le_exp
      (show 2 ≤ R by omega) w t u
      (show 0 ≤ 2 * cutoffPhaseMagnitudeBound R w T by
        positivity)
      (fun p hp q =>
        norm_divisorMultiplicativePhase_sub_one_le_bound
          hR hw hT (mem_smallPrimeFinset.mp hp)
          (ht q) hsmall)
      (fun p hp q =>
        norm_divisorMultiplicativePhase_sub_one_le_bound
          hR hw hT (mem_smallPrimeFinset.mp hp)
          (hu q) hsmall)
  have heq :
      6 * (Fintype.card κ : ℝ) *
          (2 * cutoffPhaseMagnitudeBound R w T) ^ 2 =
        24 * (Fintype.card κ : ℝ) *
          cutoffPhaseMagnitudeBound R w T ^ 2 := by
    ring
  rw [heq] at hbound
  exact hbound

/-! ## Linearized control and joint convergence -/

/-- A two-level exponential error is linear in its inner exponent in the
range needed below.  The single smallness condition also forces the
inner exponent to lie in the unit interval. -/
theorem exp_mul_exp_sub_one_sub_one_le_linear
    {N a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a)
    (hsmall : 2 * N * a ≤ 1) :
    Real.exp (N * (Real.exp a - 1)) - 1 ≤
      4 * N * a := by
  have hN0 : 0 ≤ N := hN.trans' zero_le_one
  have ha_le : a ≤ 2 * N * a := by
    calc
      a = 1 * a := by ring
      _ ≤ (2 * N) * a := by
        apply mul_le_mul_of_nonneg_right _ ha
        nlinarith
      _ = 2 * N * a := by ring
  have ha_one : a ≤ 1 :=
    ha_le.trans hsmall
  have habs : |a| ≤ 1 := by
    rw [abs_of_nonneg ha]
    exact ha_one
  have hinner0 : 0 ≤ Real.exp a - 1 :=
    sub_nonneg.mpr (Real.one_le_exp ha)
  have hinner :
      Real.exp a - 1 ≤ 2 * a := by
    calc
      Real.exp a - 1 =
          |Real.exp a - 1| := by
        rw [abs_of_nonneg hinner0]
      _ ≤ 2 * |a| :=
        Real.abs_exp_sub_one_le habs
      _ = 2 * a := by
        rw [abs_of_nonneg ha]
  have houter0 :
      0 ≤ N * (Real.exp a - 1) :=
    mul_nonneg hN0 hinner0
  have houter_one :
      N * (Real.exp a - 1) ≤ 1 := by
    calc
      N * (Real.exp a - 1) ≤
          N * (2 * a) :=
        mul_le_mul_of_nonneg_left hinner hN0
      _ = 2 * N * a := by ring
      _ ≤ 1 := hsmall
  have houter_abs :
      |N * (Real.exp a - 1)| ≤ 1 := by
    rw [abs_of_nonneg houter0]
    exact houter_one
  have houterExp0 :
      0 ≤ Real.exp (N * (Real.exp a - 1)) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp houter0)
  calc
    Real.exp (N * (Real.exp a - 1)) - 1 =
        |Real.exp (N * (Real.exp a - 1)) - 1| := by
      rw [abs_of_nonneg houterExp0]
    _ ≤ 2 * |N * (Real.exp a - 1)| :=
      Real.abs_exp_sub_one_le houter_abs
    _ = 2 * (N * (Real.exp a - 1)) := by
      rw [abs_of_nonneg houter0]
    _ ≤ 2 * (N * (2 * a)) := by
      gcongr
    _ = 4 * N * a := by ring

/-- Linear form of the actual Fourier-box correction estimate.  Its
smallness hypothesis is expressed in the same scale that occurs in the
joint limit theorem below. -/
theorem norm_normalizedSmallPrimeZetaCorrection_sub_one_le_linear
    {κ : Type*} [Fintype κ]
    {R w : ℕ} (hR : 1 < R) (hw : 2 ≤ w)
    {T : ℝ} (hT : 0 ≤ T)
    (t u : κ → ℝ)
    (ht : ∀ q, |t q| ≤ T)
    (hu : ∀ q, |u q| ≤ T)
    (hphase : cutoffPhaseMagnitudeBound R w T ≤ 1)
    (hlinear :
      48 * (Fintype.card κ : ℝ) *
          ((w + 1 : ℕ) : ℝ) *
          cutoffPhaseMagnitudeBound R w T ^ 2 ≤ 1) :
    ‖normalizedSmallPrimeZetaCorrection R w t u - 1‖ ≤
      96 * (Fintype.card κ : ℝ) *
        ((w + 1 : ℕ) : ℝ) *
        cutoffPhaseMagnitudeBound R w T ^ 2 := by
  have hA0 :
      0 ≤ cutoffPhaseMagnitudeBound R w T := by
    rw [cutoffPhaseMagnitudeBound]
    have hlogR :
        0 < Real.log (R : ℝ) :=
      Real.log_pos (by exact_mod_cast hR)
    have hlogw :
        0 ≤ Real.log (w : ℝ) :=
      Real.log_nonneg
        (by exact_mod_cast (Nat.one_le_of_lt hw))
    positivity
  have hN :
      (1 : ℝ) ≤ ((w + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le w)
  have ha :
      0 ≤
        24 * (Fintype.card κ : ℝ) *
          cutoffPhaseMagnitudeBound R w T ^ 2 := by
    positivity
  have hsmall :
      2 * ((w + 1 : ℕ) : ℝ) *
          (24 * (Fintype.card κ : ℝ) *
            cutoffPhaseMagnitudeBound R w T ^ 2) ≤ 1 := by
    calc
      2 * ((w + 1 : ℕ) : ℝ) *
          (24 * (Fintype.card κ : ℝ) *
            cutoffPhaseMagnitudeBound R w T ^ 2) =
          48 * (Fintype.card κ : ℝ) *
            ((w + 1 : ℕ) : ℝ) *
            cutoffPhaseMagnitudeBound R w T ^ 2 := by
        ring
      _ ≤ 1 := hlinear
  have hbox :=
    norm_normalizedSmallPrimeZetaCorrection_sub_one_le_box
      hR hw hT t u ht hu hphase
  calc
    ‖normalizedSmallPrimeZetaCorrection R w t u - 1‖ ≤
        Real.exp
            (((w + 1 : ℕ) : ℝ) *
              (Real.exp
                  (24 * (Fintype.card κ : ℝ) *
                    cutoffPhaseMagnitudeBound R w T ^ 2) -
                1)) -
          1 := hbox
    _ ≤
        4 * ((w + 1 : ℕ) : ℝ) *
          (24 * (Fintype.card κ : ℝ) *
            cutoffPhaseMagnitudeBound R w T ^ 2) :=
      exp_mul_exp_sub_one_sub_one_le_linear hN ha hsmall
    _ =
        96 * (Fintype.card κ : ℝ) *
          ((w + 1 : ℕ) : ℝ) *
          cutoffPhaseMagnitudeBound R w T ^ 2 := by
      ring

/-- Joint `(w,R)` convergence criterion for the normalized small-prime
zeta correction.  It is enough that

`(w + 1) * ((log w / log R) * (1 + 2πT))² → 0`

and that the Fourier parameters eventually remain in the box of radius
`T`.  No relation between `w`, `R`, and `T` beyond this explicit scale is
imposed. -/
theorem tendsto_normalizedSmallPrimeZetaCorrection_of_joint_scale
    {κ : Type*} [Fintype κ]
    (R w : ℕ → ℕ) (T : ℕ → ℝ)
    (t u : ℕ → κ → ℝ)
    (hR : ∀ᶠ n in atTop, 1 < R n)
    (hw : ∀ᶠ n in atTop, 2 ≤ w n)
    (hT : ∀ᶠ n in atTop, 0 ≤ T n)
    (ht : ∀ᶠ n in atTop, ∀ q, |t n q| ≤ T n)
    (hu : ∀ᶠ n in atTop, ∀ q, |u n q| ≤ T n)
    (hscale :
      Tendsto
        (fun n =>
          (((w n + 1 : ℕ) : ℝ) *
            cutoffPhaseMagnitudeBound
                (R n) (w n) (T n) ^ 2))
        atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        normalizedSmallPrimeZetaCorrection
          (R n) (w n) (t n) (u n))
      atTop (𝓝 1) := by
  let B : ℕ → ℝ := fun n =>
    ((w n + 1 : ℕ) : ℝ) *
      cutoffPhaseMagnitudeBound
          (R n) (w n) (T n) ^ 2
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa only [B] using hscale
  have hBsmall :
      ∀ᶠ n in atTop, B n ≤ 1 :=
    ((tendsto_order.1 hB).2 1 zero_lt_one).mono
      (fun _ hn => hn.le)
  have hphase :
      ∀ᶠ n in atTop,
        cutoffPhaseMagnitudeBound
            (R n) (w n) (T n) ≤ 1 := by
    filter_upwards [hR, hw, hT, hBsmall] with
      n hRn hwn hTn hBsmalln
    have hA0 :
        0 ≤ cutoffPhaseMagnitudeBound
          (R n) (w n) (T n) := by
      rw [cutoffPhaseMagnitudeBound]
      have hlogR :
          0 < Real.log (R n : ℝ) :=
        Real.log_pos (by exact_mod_cast hRn)
      have hlogw :
          0 ≤ Real.log (w n : ℝ) :=
        Real.log_nonneg
          (by exact_mod_cast (Nat.one_le_of_lt hwn))
      positivity
    have hN :
        (1 : ℝ) ≤ ((w n + 1 : ℕ) : ℝ) := by
      exact_mod_cast
        Nat.succ_le_succ (Nat.zero_le (w n))
    have hA2 :
        cutoffPhaseMagnitudeBound
              (R n) (w n) (T n) ^ 2 ≤
          ((w n + 1 : ℕ) : ℝ) *
            cutoffPhaseMagnitudeBound
              (R n) (w n) (T n) ^ 2 := by
      nlinarith [sq_nonneg
        (cutoffPhaseMagnitudeBound
          (R n) (w n) (T n))]
    have hA2one :
        cutoffPhaseMagnitudeBound
            (R n) (w n) (T n) ^ 2 ≤ 1 := by
      apply hA2.trans
      simpa only [B] using hBsmalln
    nlinarith [sq_nonneg
      (cutoffPhaseMagnitudeBound
        (R n) (w n) (T n))]
  have hscaled48 :
      Tendsto
        (fun n => (48 * (Fintype.card κ : ℝ)) * B n)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul hB :
        Tendsto
          (fun n => (48 * (Fintype.card κ : ℝ)) * B n)
          atTop
          (𝓝 ((48 * (Fintype.card κ : ℝ)) * 0)))
  have hlinear :
      ∀ᶠ n in atTop,
        48 * (Fintype.card κ : ℝ) * B n ≤ 1 := by
    filter_upwards [
      (tendsto_order.1 hscaled48).2 1 zero_lt_one
    ] with n hn
    exact hn.le
  have herror :
      ∀ᶠ n in atTop,
        ‖normalizedSmallPrimeZetaCorrection
              (R n) (w n) (t n) (u n) -
            1‖ ≤
          96 * (Fintype.card κ : ℝ) * B n := by
    filter_upwards
      [hR, hw, hT, ht, hu, hphase, hlinear]
      with n hRn hwn hTn htn hun hphasen hlinearn
    have hn :=
      norm_normalizedSmallPrimeZetaCorrection_sub_one_le_linear
        hRn hwn hTn (t n) (u n) htn hun hphasen
        (by simpa only [B, mul_assoc] using hlinearn)
    simpa only [B, mul_assoc] using hn
  have hscaled96 :
      Tendsto
        (fun n => 96 * (Fintype.card κ : ℝ) * B n)
        atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using
      (tendsto_const_nhds.mul hB :
        Tendsto
          (fun n =>
            (96 * (Fintype.card κ : ℝ)) * B n)
          atTop
          (𝓝 ((96 * (Fintype.card κ : ℝ)) * 0)))
  apply tendsto_iff_norm_sub_tendsto_zero.2
  exact
    squeeze_zero'
      (Eventually.of_forall fun _ => norm_nonneg _)
      herror hscaled96

end Wikipedia.SzemeredisTheorem
