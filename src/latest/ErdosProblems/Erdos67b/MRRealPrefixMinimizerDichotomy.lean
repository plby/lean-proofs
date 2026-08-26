import ErdosProblems.Erdos67b.MRGSLemma71RealPrefix
import ErdosProblems.Erdos67b.MRHalaszMinimizer
import ErdosProblems.Erdos67b.MRRealPrefixNormToSigned
import ErdosProblems.Erdos67b.MRRealTwistSeparationQuantitative

/-!
# The real prefix minimizer dichotomy

This file selects an attained Archimedean minimizer and separates the four
branches used in the real Granville--Soundararajan argument: full Halasz
nonpretentiousness, a genuine near nonzero twist, a noncentral low-distance
obstruction, or the already-compiled zero-frequency slow-variation branch.
-/

open scoped ComplexConjugate
open Filter

namespace Erdos67b

noncomputable section

/-- The deliberately small moving distance threshold used by the real
prefix dichotomy.  The `max` only makes the definition total at the few
small values of `X`; it disappears throughout the analytic range. -/
def realPrefixMovingThreshold (X : ℕ) : ℕ :=
  Nat.floor (max 0
    ((1 / 16 : ℝ) * Real.log (Real.log (X : ℝ))))

theorem realPrefixMovingThreshold_cast_le
    {X : ℕ} (hX : 3 ≤ X) :
    (realPrefixMovingThreshold X : ℝ) ≤
      (1 / 16 : ℝ) * Real.log (Real.log (X : ℝ)) := by
  have hlogX : 1 < Real.log (X : ℝ) := by
    have hexp : Real.exp 1 < (X : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hX)
    rw [← Real.exp_lt_exp, Real.exp_log (by positivity)]
    exact hexp
  have hloglog : 0 ≤ Real.log (Real.log (X : ℝ)) :=
    (Real.log_nonneg hlogX.le)
  unfold realPrefixMovingThreshold
  rw [max_eq_right (mul_nonneg (by norm_num) hloglog)]
  exact Nat.floor_le (mul_nonneg (by norm_num) hloglog)

/-- At every finite height window, either the coefficient is uniformly
nonpretentious at level `A`, or an attained minimizing twist has distance
strictly below `A`. -/
theorem archimedeanNonpretentious_or_exists_minimizer_lt
    (f : ℕ → ℂ) (A X : ℕ) :
    MRArchimedeanNonpretentious f A X ∨
      ∃ t₀ : ℝ, |t₀| ≤ X ∧
        pretentiousDistSq f (archimedeanTwist t₀) X < A ∧
        ∀ t : ℝ, |t| ≤ X →
          pretentiousDistSq f (archimedeanTwist t₀) X ≤
            pretentiousDistSq f (archimedeanTwist t) X := by
  obtain ⟨t₀, ht₀, hmin⟩ :=
    exists_pretentiousDistSq_archimedean_minimizer f X
      (show (0 : ℝ) ≤ X by positivity)
  have habs₀ : |t₀| ≤ X := abs_le.mpr ⟨ht₀.1, ht₀.2⟩
  by_cases hA : (A : ℝ) ≤
      pretentiousDistSq f (archimedeanTwist t₀) X
  · left
    intro t ht
    exact hA.trans (hmin t (abs_le.mp ht))
  · right
    exact ⟨t₀, habs₀, lt_of_not_ge hA,
      fun t ht ↦ hmin t (abs_le.mp ht)⟩

/-- Exact unconditional selection used before the analytic branch bounds.
The fourth branch is already the desired uniform prefix stability.  The
second branch is in the range of `MRGSLemma71RealPrefix`; the first is the
ordinary finite-Halasz branch.  Consequently the third displayed branch is
the precise quantitative real-twist separation seam still needed to join
the two compiled estimates. -/
theorem real_prefix_minimizer_near_or_halasz_or_stable
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, ‖f n‖ ≤ 1)
    {A X : ℕ} (hX : 3 ≤ X)
    (hA : (A : ℝ) ≤
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ))) :
    MRArchimedeanNonpretentious f A (3 * X) ∨
      (∃ t₀ : ℝ, t₀ ≠ 0 ∧ |t₀| ≤ 1 ∧
        pretentiousDistSq f (archimedeanTwist t₀) (3 * X) < A) ∨
      (∃ t₀ : ℝ, 1 < |t₀| ∧ |t₀| ≤ 3 * X ∧
        pretentiousDistSq f (archimedeanTwist t₀) (3 * X) < A) ∨
      (∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z - mu‖ ≤
          realGSPrefixVariationConstant *
            (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) := by
  rcases archimedeanNonpretentious_or_exists_minimizer_lt
      f A (3 * X) with hnonpret | ⟨t₀, ht₀, hdist, _hmin⟩
  · exact Or.inl hnonpret
  · by_cases htzero : t₀ = 0
    · subst t₀
      have hsmall :
          pretentiousDistSq f (archimedeanTwist 0) (3 * X) ≤
            (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) := by
        exact le_trans (le_of_lt hdist) hA
      exact Or.inr (Or.inr (Or.inr
        (exists_uniform_positivePrefixMean_stable_of_zeroDistance_small
          hmul hreal hbound hX hsmall)))
    · by_cases htnear : |t₀| ≤ 1
      · exact Or.inr (Or.inl ⟨t₀, htzero, htnear, hdist⟩)
      · have ht₀' : |t₀| ≤ 3 * (X : ℝ) := by
          exact_mod_cast ht₀
        exact Or.inr (Or.inr (Or.inl
          ⟨t₀, lt_of_not_ge htnear, ht₀', hdist⟩))

/-- The minimizer split at the moving `1/16 log log X` threshold.  This is
the exact quantitative form used by the eventual real-prefix argument. -/
theorem real_prefix_movingThreshold_dichotomy
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 3 ≤ X) :
    MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) ∨
      (∃ t₀ : ℝ, t₀ ≠ 0 ∧ |t₀| ≤ 1 ∧
        pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
          realPrefixMovingThreshold X) ∨
      (∃ t₀ : ℝ, 1 < |t₀| ∧ |t₀| ≤ 3 * X ∧
        pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
          realPrefixMovingThreshold X) ∨
      (∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z - mu‖ ≤
          realGSPrefixVariationConstant *
            (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) := by
  apply real_prefix_minimizer_near_or_halasz_or_stable
    hmul hreal hbound hX
  calc
    (realPrefixMovingThreshold X : ℝ) ≤
        (1 / 16 : ℝ) * Real.log (Real.log (X : ℝ)) :=
      realPrefixMovingThreshold_cast_le hX
    _ ≤ (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) := by
      have hlogX : 1 < Real.log (X : ℝ) := by
        have hexp : Real.exp 1 < (X : ℝ) :=
          Real.exp_one_lt_three.trans_le (by exact_mod_cast hX)
        rw [← Real.exp_lt_exp, Real.exp_log (by positivity)]
        exact hexp
      have hloglog : 0 ≤ Real.log (Real.log (X : ℝ)) :=
        Real.log_nonneg hlogX.le
      nlinarith

/-- The near-twist scalar closes with room to spare at the moving
`1/16 log log X` threshold.  The displayed prime-reciprocal estimate is
the standard explicit Mertens bound after replacing `log log (3X)` by at
most twice `log log X`; an eventual wrapper below discharges it. -/
theorem abs_norm_positivePrefixMean_sub_norm_le_movingThreshold
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t : ℝ) {X Z : ℕ} (hX : 3 ≤ X) (hXZ : X ≤ Z)
    (hZ : Z ≤ 3 * X) (ht : t ≠ 0) (ht_small : |t| ≤ 1)
    (hdist : pretentiousDistSq f (archimedeanTwist t) (3 * X) <
      realPrefixMovingThreshold X)
    (hprime : PrimeEstimates.primeReciprocals (3 * X) ≤
      (278 / 100 : ℝ) * Real.log (Real.log (X : ℝ))) :
    |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| ≤
      (realGSNearTwistNormConstant * Real.exp 8) *
        (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by
  let L : ℝ := Real.log (Real.log (X : ℝ))
  let A : ℝ := realPrefixMovingThreshold X
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hL : 0 ≤ L := by
    dsimp only [L]
    have hlogXone : 1 < Real.log (X : ℝ) := by
      rw [← Real.exp_lt_exp, Real.exp_log (by positivity)]
      exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hX)
    exact Real.log_nonneg hlogXone.le
  have hA : 0 ≤ A := by positivity
  have hAle : A ≤ (1 / 16 : ℝ) * L := by
    exact realPrefixMovingThreshold_cast_le hX
  have hp : 0 ≤ PrimeEstimates.primeReciprocals (3 * X) :=
    PrimeEstimates.primeReciprocals_nonneg (3 * X)
  have hprod :
      2 * A * PrimeEstimates.primeReciprocals (3 * X) ≤
        ((3 / 4 : ℝ) * L) ^ 2 := by
    calc
      2 * A * PrimeEstimates.primeReciprocals (3 * X) ≤
          2 * ((1 / 16 : ℝ) * L) *
            PrimeEstimates.primeReciprocals (3 * X) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAle (by norm_num)) hp
      _ ≤ 2 * ((1 / 16 : ℝ) * L) * ((278 / 100 : ℝ) * L) := by
        exact mul_le_mul_of_nonneg_left hprime
          (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hL))
      _ ≤ ((3 / 4 : ℝ) * L) ^ 2 := by
        nlinarith [sq_nonneg L]
  have hsqrt :
      Real.sqrt
          (2 * A * PrimeEstimates.primeReciprocals (3 * X)) ≤
        (3 / 4 : ℝ) * L := by
    apply (Real.sqrt_le_iff).2
    exact ⟨mul_nonneg (by norm_num) hL, hprod⟩
  have hbase :=
    abs_norm_positivePrefixMean_sub_norm_le_nearTwistDistance
      hmul hbound t hX hXZ hZ ht ht_small hA (le_of_lt hdist)
  have hexp :
      Real.exp
          (Real.sqrt
              (2 * A * PrimeEstimates.primeReciprocals (3 * X)) + 8) ≤
        Real.exp 8 * (Real.log (X : ℝ)) ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ Real.exp ((3 / 4 : ℝ) * L + 8) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp 8 * Real.exp ((3 / 4 : ℝ) * L) := by
        rw [Real.exp_add]
        ring
      _ = Real.exp 8 * (Real.log (X : ℝ)) ^ (3 / 4 : ℝ) := by
        congr 1
        rw [Real.rpow_def_of_pos hlogX]
        dsimp only [L]
        congr 1
        ring
  calc
    |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| ≤
        realGSNearTwistNormConstant / Real.log (X : ℝ) *
          Real.exp
            (Real.sqrt
                (2 * A * PrimeEstimates.primeReciprocals (3 * X)) + 8) :=
      hbase
    _ ≤ realGSNearTwistNormConstant / Real.log (X : ℝ) *
          (Real.exp 8 * (Real.log (X : ℝ)) ^ (3 / 4 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hexp
        (div_nonneg realGSNearTwistNormConstant_nonneg hlogX.le)
    _ = (realGSNearTwistNormConstant * Real.exp 8) *
          (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      calc
        realGSNearTwistNormConstant *
              (Real.log (X : ℝ)) ^ (-(1 : ℝ)) *
              (Real.exp 8 * (Real.log (X : ℝ)) ^ (3 / 4 : ℝ)) =
            (realGSNearTwistNormConstant * Real.exp 8) *
              ((Real.log (X : ℝ)) ^ (-(1 : ℝ)) *
                (Real.log (X : ℝ)) ^ (3 / 4 : ℝ)) := by ring
        _ = (realGSNearTwistNormConstant * Real.exp 8) *
              (Real.log (X : ℝ)) ^ (-(1 : ℝ) + 3 / 4) := by
          rw [Real.rpow_add hlogX]
        _ = _ := by norm_num

/-- The explicit Mertens estimate in precisely the rescaled form consumed
by `abs_norm_positivePrefixMean_sub_norm_le_movingThreshold`. -/
theorem eventually_primeReciprocals_three_mul_le_278 :
    ∀ᶠ X : ℕ in atTop,
      PrimeEstimates.primeReciprocals (3 * X) ≤
        (278 / 100 : ℝ) * Real.log (Real.log (X : ℝ)) := by
  have hthree : Tendsto (fun X : ℕ ↦ 3 * X) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with X hNX
    omega
  have hprime : ∀ᶠ X : ℕ in atTop,
      PrimeEstimates.primeReciprocals (3 * X) ≤
        (139 / 100 : ℝ) * Real.log (Real.log ((3 * X : ℕ) : ℝ)) :=
    hthree.eventually PrimeEstimates.eventually_primeReciprocals_le_139
  have hloglog : Tendsto
      (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlarge : ∀ᶠ X : ℕ in atTop,
      Real.log 2 ≤ Real.log (Real.log (X : ℝ)) :=
    hloglog.eventually (eventually_ge_atTop (Real.log 2))
  filter_upwards [hprime, hlarge, eventually_ge_atTop 3] with X hp hL hX
  have hXR : (0 : ℝ) < X := by positivity
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlog3X : 0 < Real.log ((3 * X : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * X by omega))
  have hlog3le : Real.log 3 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  have hinner :
      Real.log ((3 * X : ℕ) : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hXR.ne']
    linarith
  have houter :
      Real.log (Real.log ((3 * X : ℕ) : ℝ)) ≤
        2 * Real.log (Real.log (X : ℝ)) := by
    have hlogmono := Real.log_le_log hlog3X hinner
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogX.ne'] at hlogmono
    linarith
  calc
    PrimeEstimates.primeReciprocals (3 * X) ≤
        (139 / 100 : ℝ) * Real.log (Real.log ((3 * X : ℕ) : ℝ)) := hp
    _ ≤ (139 / 100 : ℝ) *
        (2 * Real.log (Real.log (X : ℝ))) := by gcongr
    _ = (278 / 100 : ℝ) * Real.log (Real.log (X : ℝ)) := by ring

/-- Eventual near-twist branch with every scalar premise discharged. -/
theorem eventually_abs_norm_positivePrefixMean_sub_norm_le_nearTwist :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ) (t : ℝ) (Z : ℕ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n : ℕ, ‖f n‖ ≤ 1) →
      X ≤ Z → Z ≤ 3 * X → t ≠ 0 → |t| ≤ 1 →
      pretentiousDistSq f (archimedeanTwist t) (3 * X) <
        realPrefixMovingThreshold X →
      |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| ≤
        (realGSNearTwistNormConstant * Real.exp 8) *
          (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by
  filter_upwards [eventually_primeReciprocals_three_mul_le_278,
    eventually_ge_atTop 3] with X hprime hX
  intro f t Z hmul hbound hXZ hZ ht ht_small hdist
  exact abs_norm_positivePrefixMean_sub_norm_le_movingThreshold
    hmul hbound t hX hXZ hZ ht ht_small hdist hprime

/-- After quantitative real symmetry, the only low-distance minimizer not
covered by the GS near-twist estimate lies beyond the fourth power of the
logarithmic height.  This is the exact reciprocal-Halasz tail branch. -/
theorem eventually_real_prefix_movingThreshold_far_dichotomy :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) ∨
        (∃ t₀ : ℝ, t₀ ≠ 0 ∧ |t₀| ≤ 1 ∧
          pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
            realPrefixMovingThreshold X) ∨
        (∃ t₀ : ℝ,
          (Real.log (X : ℝ)) ^ (4 : ℕ) < |t₀| ∧
          |t₀| ≤ 3 * X ∧
          pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
            realPrefixMovingThreshold X) ∨
        (∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
          ‖positivePrefixMean f Z - mu‖ ≤
            realGSPrefixVariationConstant *
              (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) := by
  filter_upwards
      [eventually_quarter_log_log_le_oppositeTwistDistSq_polylog,
        eventually_ge_atTop 4] with X hsep hX
  intro f hmul hreal hbound
  rcases real_prefix_movingThreshold_dichotomy
      (X := X) hmul hreal hbound (by omega) with
    hnonpret | hnear | hmedium | hstable
  · exact Or.inl hnonpret
  · exact Or.inr (Or.inl hnear)
  · obtain ⟨t₀, ht₀one, ht₀X, hdist⟩ := hmedium
    by_cases htpoly : |t₀| ≤ (Real.log (X : ℝ)) ^ (4 : ℕ)
    · have hopposite := hsep t₀ ht₀one htpoly
      have hrealDist :=
        one_fourth_mul_le_pretentiousDistSq_of_real_of_twist_separation
          hreal (fun n _ ↦ hbound n) hopposite
      have hrealDistTop :
          ((1 / 4 : ℝ) * Real.log (Real.log (X : ℝ))) / 4 ≤
            pretentiousDistSq f (archimedeanTwist t₀) (3 * X) :=
        hrealDist.trans (pretentiousDistSq_mono (by omega)
          (fun n _ ↦ hbound n)
          (fun n hn ↦ (norm_archimedeanTwist hn.pos t₀).le))
      have hthreshold := realPrefixMovingThreshold_cast_le (by omega : 3 ≤ X)
      exfalso
      have : (realPrefixMovingThreshold X : ℝ) ≤
          pretentiousDistSq f (archimedeanTwist t₀) (3 * X) := by
        calc
          (realPrefixMovingThreshold X : ℝ) ≤
              (1 / 16 : ℝ) * Real.log (Real.log (X : ℝ)) := hthreshold
          _ = ((1 / 4 : ℝ) * Real.log (Real.log (X : ℝ))) / 4 := by ring
          _ ≤ pretentiousDistSq f (archimedeanTwist t₀) (3 * X) := hrealDistTop
      exact (not_lt_of_ge this) hdist
    · exact Or.inr (Or.inr (Or.inl
        ⟨t₀, lt_of_not_ge htpoly, ht₀X, hdist⟩))
  · exact Or.inr (Or.inr (Or.inr hstable))

/-- The same final split with the near-twist existential already converted
to uniform slow variation of the prefix norms. -/
theorem eventually_real_prefix_halasz_or_far_or_normStable_or_stable :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) ∨
        (∃ t₀ : ℝ,
          (Real.log (X : ℝ)) ^ (4 : ℕ) < |t₀| ∧
          |t₀| ≤ 3 * X ∧
          pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
            realPrefixMovingThreshold X) ∨
        (∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
          |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| ≤
            (realGSNearTwistNormConstant * Real.exp 8) *
              (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) ∨
        (∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
          ‖positivePrefixMean f Z - mu‖ ≤
            realGSPrefixVariationConstant *
              (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) := by
  filter_upwards
      [eventually_real_prefix_movingThreshold_far_dichotomy,
        eventually_abs_norm_positivePrefixMean_sub_norm_le_nearTwist]
      with X hsplit hnear
  intro f hmul hreal hbound
  rcases hsplit f hmul hreal hbound with
    hnonpret | htwist | hfar | hstable
  · exact Or.inl hnonpret
  · right; right; left
    obtain ⟨t₀, ht₀, ht₀one, hdist⟩ := htwist
    intro Z hXZ hZ
    exact hnear f t₀ Z hmul hbound hXZ hZ ht₀ ht₀one hdist
  · exact Or.inr (Or.inl hfar)
  · exact Or.inr (Or.inr (Or.inr hstable))

/-- A single explicit constant for the signed prefix-stability branch. -/
def realGSSignedPrefixStabilityConstant : ℝ :=
  3 * (realGSNearTwistNormConstant * Real.exp 8) + 4 +
    realGSPrefixVariationConstant

theorem realGSSignedPrefixStabilityConstant_nonneg :
    0 ≤ realGSSignedPrefixStabilityConstant := by
  unfold realGSSignedPrefixStabilityConstant
  have hnear : 0 ≤ realGSNearTwistNormConstant * Real.exp 8 :=
    mul_nonneg realGSNearTwistNormConstant_nonneg (Real.exp_pos 8).le
  linarith [realGSPrefixVariationConstant_nonneg]

/-- The adjacent-prefix error `4/X` is no larger than the target negative
quarter power once `X ≥ 3`. -/
theorem four_div_nat_le_four_mul_log_rpow_neg_quarter
    {X : ℕ} (hX : 3 ≤ X) :
    (4 : ℝ) / X ≤ 4 * (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by
  have hXR : (0 : ℝ) < X := by positivity
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hlogpos : 0 < Real.log (X : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < X by omega))
  have hlogle : Real.log (X : ℝ) ≤ (X : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hXR
    linarith
  have hroot : (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) ≤ (X : ℝ) := by
    calc
      (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) ≤
          (X : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hlogpos.le hlogle (by norm_num)
      _ ≤ (X : ℝ) :=
        Real.rpow_le_self_of_one_le hXone (by norm_num)
  have hinv : (1 : ℝ) / X ≤
      1 / ((Real.log (X : ℝ)) ^ (1 / 4 : ℝ)) :=
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogpos _ ) hroot
  have hrpow : 1 / ((Real.log (X : ℝ)) ^ (1 / 4 : ℝ)) =
      (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by
    rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring,
      Real.rpow_neg hlogpos.le, one_div]
  calc
    (4 : ℝ) / X = 4 * ((1 : ℝ) / X) := by ring
    _ ≤ 4 * (1 / ((Real.log (X : ℝ)) ^ (1 / 4 : ℝ))) := by
      gcongr
    _ = 4 * (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by rw [hrpow]

/-- Final minimizer split after turning norm stability into stability around
the single common mean `positivePrefixMean f X`.  The only analytic branches
left are the ordinary sharp-prefix Halasz estimate and the high-frequency
low-distance minimizer. -/
theorem eventually_real_prefix_halasz_or_far_or_stable :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) ∨
        (∃ t₀ : ℝ,
          (Real.log (X : ℝ)) ^ (4 : ℕ) < |t₀| ∧
          |t₀| ≤ 3 * X ∧
          pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
            realPrefixMovingThreshold X) ∨
        (∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
          ‖positivePrefixMean f Z - mu‖ ≤
            realGSSignedPrefixStabilityConstant *
              (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) := by
  filter_upwards
      [eventually_real_prefix_halasz_or_far_or_normStable_or_stable,
        eventually_ge_atTop 3] with X hsplit hX
  intro f hmul hreal hbound
  rcases hsplit f hmul hreal hbound with
    hnonpret | hfar | hnorm | hstable
  · exact Or.inl hnonpret
  · exact Or.inr (Or.inl hfar)
  · right; right
    refine ⟨positivePrefixMean f X, ?_⟩
    intro Z hXZ hZ
    have hsigned := uniform_positivePrefixMean_stable_of_real_of_norm_stable
      hreal hbound (show 1 ≤ X by omega)
        (mul_nonneg
          (mul_nonneg realGSNearTwistNormConstant_nonneg (Real.exp_pos 8).le)
        (Real.rpow_nonneg (Real.log_pos (by
          exact_mod_cast (show 1 < X by omega))).le _))
      hnorm Z hXZ hZ
    have hfour := four_div_nat_le_four_mul_log_rpow_neg_quarter hX
    calc
      ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
          3 * ((realGSNearTwistNormConstant * Real.exp 8) *
            (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) + 4 / X := hsigned
      _ ≤ realGSSignedPrefixStabilityConstant *
          (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by
        unfold realGSSignedPrefixStabilityConstant
        have hrpow : 0 ≤ (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) :=
          Real.rpow_nonneg (Real.log_pos (by
            exact_mod_cast (show 1 < X by omega))).le _
        nlinarith [realGSPrefixVariationConstant_nonneg]
  · right; right
    obtain ⟨mu, hmu⟩ := hstable
    refine ⟨mu, ?_⟩
    intro Z hXZ hZ
    have h := hmu Z hXZ hZ
    have hrpow : 0 ≤ (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) :=
      Real.rpow_nonneg (Real.log_pos (by
        exact_mod_cast (show 1 < X by omega))).le _
    exact h.trans (by
      unfold realGSSignedPrefixStabilityConstant
      have hnear : 0 ≤ 3 *
          (realGSNearTwistNormConstant * Real.exp 8) + 4 := by
        have := realGSNearTwistNormConstant_nonneg
        positivity
      nlinarith [mul_nonneg hnear hrpow])

/-- Reordered final split.  Before exposing either unresolved analytic
branch, use the zero-frequency GS theorem.  Consequently both unresolved
branches retain the strict failure of its `3/4 log log X` hypothesis. -/
theorem eventually_real_prefix_halaszLargeZero_or_farLargeZero_or_stable :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      (MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) ∧
        (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
          pretentiousDistSq f (archimedeanTwist 0) (3 * X)) ∨
        ((∃ t₀ : ℝ,
          (Real.log (X : ℝ)) ^ (4 : ℕ) < |t₀| ∧
          |t₀| ≤ 3 * X ∧
          pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
            realPrefixMovingThreshold X) ∧
          (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
            pretentiousDistSq f (archimedeanTwist 0) (3 * X)) ∨
        (∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
          ‖positivePrefixMean f Z - mu‖ ≤
            realGSSignedPrefixStabilityConstant *
              (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) := by
  filter_upwards [eventually_real_prefix_halasz_or_far_or_stable,
    eventually_ge_atTop 3] with X hsplit hX
  intro f hmul hreal hbound
  by_cases hzero : pretentiousDistSq f (archimedeanTwist 0) (3 * X) ≤
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ))
  · right; right
    obtain ⟨mu, hmu⟩ :=
      exists_uniform_positivePrefixMean_stable_of_zeroDistance_small
        hmul hreal hbound hX hzero
    refine ⟨mu, ?_⟩
    intro Z hXZ hZ
    have h := hmu Z hXZ hZ
    have hlogpos : 0 < Real.log (X : ℝ) := Real.log_pos (by
      exact_mod_cast (show 1 < X by omega))
    have hrpow : 0 ≤ (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) :=
      Real.rpow_nonneg hlogpos.le _
    exact h.trans (mul_le_mul_of_nonneg_right (by
      unfold realGSSignedPrefixStabilityConstant
      have hnear : 0 ≤ 3 *
          (realGSNearTwistNormConstant * Real.exp 8) + 4 := by
        have := realGSNearTwistNormConstant_nonneg
        positivity
      linarith) hrpow)
  · have hzeroLarge :
        (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
          pretentiousDistSq f (archimedeanTwist 0) (3 * X) :=
      lt_of_not_ge hzero
    rcases hsplit f hmul hreal hbound with hnonpret | hfar | hstable
    · exact Or.inl ⟨hnonpret, hzeroLarge⟩
    · exact Or.inr (Or.inl ⟨hfar, hzeroLarge⟩)
    · exact Or.inr (Or.inr hstable)

/-- Consumer for the two remaining analytic estimates.  Supplying ordinary
prefix smallness in the Halasz and high-frequency minimizer branches upgrades
the minimizer split to unconditional stability around one common mean. -/
theorem eventually_uniform_real_prefix_stable_of_halasz_of_far
    {C_halasz C_far : ℝ}
    (hhalasz : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          C_halasz * (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ))
    (hfar : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      (∃ t₀ : ℝ,
        (Real.log (X : ℝ)) ^ (4 : ℕ) < |t₀| ∧
        |t₀| ≤ 3 * X ∧
        pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
          realPrefixMovingThreshold X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          C_far * (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      ∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z - mu‖ ≤
          max C_halasz (max C_far realGSSignedPrefixStabilityConstant) *
            (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by
  filter_upwards
      [eventually_real_prefix_halasz_or_far_or_stable, hhalasz, hfar,
        eventually_ge_atTop 3] with X hsplit hhalaszX hfarX hX
  intro f hmul hreal hbound
  have hrpow : 0 ≤ (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) :=
    Real.rpow_nonneg (Real.log_pos (by
      exact_mod_cast (show 1 < X by omega))).le _
  rcases hsplit f hmul hreal hbound with hnonpret | hfarBranch | hstable
  · refine ⟨0, ?_⟩
    intro Z hXZ hZ
    simpa using (hhalaszX f hmul hreal hbound hnonpret Z hXZ hZ).trans
      (mul_le_mul_of_nonneg_right
        (le_max_left C_halasz (max C_far realGSSignedPrefixStabilityConstant))
        hrpow)
  · refine ⟨0, ?_⟩
    intro Z hXZ hZ
    simpa using (hfarX f hmul hreal hbound hfarBranch Z hXZ hZ).trans
      (mul_le_mul_of_nonneg_right
        ((le_max_left C_far realGSSignedPrefixStabilityConstant).trans
          (le_max_right C_halasz
            (max C_far realGSSignedPrefixStabilityConstant)))
        hrpow)
  · obtain ⟨mu, hmu⟩ := hstable
    refine ⟨mu, ?_⟩
    intro Z hXZ hZ
    exact (hmu Z hXZ hZ).trans (mul_le_mul_of_nonneg_right
      ((le_max_right C_far realGSSignedPrefixStabilityConstant).trans
        (le_max_right C_halasz
          (max C_far realGSSignedPrefixStabilityConstant)))
      hrpow)

/-- Large-zero-distance version of the final consumer.  This is the adapter
for the source-correct ordinary Halasz estimate: both analytic inputs may use
the retained strict lower bound at the zero twist. -/
theorem eventually_uniform_real_prefix_stable_of_halaszLargeZero_of_farLargeZero
    {C_halasz C_far : ℝ}
    (hhalasz : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) →
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          C_halasz * (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ))
    (hfar : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      (∃ t₀ : ℝ,
        (Real.log (X : ℝ)) ^ (4 : ℕ) < |t₀| ∧
        |t₀| ≤ 3 * X ∧
        pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
          realPrefixMovingThreshold X) →
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          C_far * (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      ∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z - mu‖ ≤
          max C_halasz (max C_far realGSSignedPrefixStabilityConstant) *
            (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by
  filter_upwards
      [eventually_real_prefix_halaszLargeZero_or_farLargeZero_or_stable,
        hhalasz, hfar, eventually_ge_atTop 3]
      with X hsplit hhalaszX hfarX hX
  intro f hmul hreal hbound
  have hrpow : 0 ≤ (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) :=
    Real.rpow_nonneg (Real.log_pos (by
      exact_mod_cast (show 1 < X by omega))).le _
  rcases hsplit f hmul hreal hbound with
    ⟨hnonpret, hzero⟩ | ⟨hfarBranch, hzero⟩ | hstable
  · refine ⟨0, ?_⟩
    intro Z hXZ hZ
    simpa using
      (hhalaszX f hmul hreal hbound hnonpret hzero Z hXZ hZ).trans
        (mul_le_mul_of_nonneg_right
          (le_max_left C_halasz
            (max C_far realGSSignedPrefixStabilityConstant)) hrpow)
  · refine ⟨0, ?_⟩
    intro Z hXZ hZ
    simpa using
      (hfarX f hmul hreal hbound hfarBranch hzero Z hXZ hZ).trans
        (mul_le_mul_of_nonneg_right
          ((le_max_left C_far realGSSignedPrefixStabilityConstant).trans
            (le_max_right C_halasz
              (max C_far realGSSignedPrefixStabilityConstant))) hrpow)
  · obtain ⟨mu, hmu⟩ := hstable
    refine ⟨mu, ?_⟩
    intro Z hXZ hZ
    exact (hmu Z hXZ hZ).trans (mul_le_mul_of_nonneg_right
      ((le_max_right C_far realGSSignedPrefixStabilityConstant).trans
        (le_max_right C_halasz
          (max C_far realGSSignedPrefixStabilityConstant))) hrpow)

/-- Small-exponent version of the large-zero-distance consumer.  The GS and
signed branches were proved with exponent `1/4`, hence they feed every fixed
`0 < c ≤ 1/4`; the two unresolved analytic inputs need only supply exponent
`c`. -/
theorem eventually_uniform_real_prefix_stable_rpow_of_halaszLargeZero_of_farLargeZero
    {c C_halasz C_far : ℝ} (hcQuarter : c ≤ 1 / 4)
    (hhalasz : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) →
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          C_halasz * (Real.log (X : ℝ)) ^ (-c))
    (hfar : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      (∃ t₀ : ℝ,
        (Real.log (X : ℝ)) ^ (4 : ℕ) < |t₀| ∧
        |t₀| ≤ 3 * X ∧
        pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
          realPrefixMovingThreshold X) →
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          C_far * (Real.log (X : ℝ)) ^ (-c)) :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      ∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z - mu‖ ≤
          max C_halasz (max C_far realGSSignedPrefixStabilityConstant) *
            (Real.log (X : ℝ)) ^ (-c) := by
  filter_upwards
      [eventually_real_prefix_halaszLargeZero_or_farLargeZero_or_stable,
        hhalasz, hfar, eventually_ge_atTop 3]
      with X hsplit hhalaszX hfarX hX
  intro f hmul hreal hbound
  have hlog : 1 ≤ Real.log (X : ℝ) := by
    have hexp : Real.exp 1 < (X : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hX)
    exact (Real.exp_le_exp.mp (hexp.le.trans_eq
      (Real.exp_log (by positivity)).symm))
  have hrpow : 0 ≤ (Real.log (X : ℝ)) ^ (-c) :=
    Real.rpow_nonneg (by positivity) _
  have hrpowQuarter :
      (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) ≤
        (Real.log (X : ℝ)) ^ (-c) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    linarith
  rcases hsplit f hmul hreal hbound with
    ⟨hnonpret, hzero⟩ | ⟨hfarBranch, hzero⟩ | hstable
  · refine ⟨0, ?_⟩
    intro Z hXZ hZ
    simpa using
      (hhalaszX f hmul hreal hbound hnonpret hzero Z hXZ hZ).trans
        (mul_le_mul_of_nonneg_right
          (le_max_left C_halasz
            (max C_far realGSSignedPrefixStabilityConstant)) hrpow)
  · refine ⟨0, ?_⟩
    intro Z hXZ hZ
    simpa using
      (hfarX f hmul hreal hbound hfarBranch hzero Z hXZ hZ).trans
        (mul_le_mul_of_nonneg_right
          ((le_max_left C_far realGSSignedPrefixStabilityConstant).trans
            (le_max_right C_halasz
              (max C_far realGSSignedPrefixStabilityConstant))) hrpow)
  · obtain ⟨mu, hmu⟩ := hstable
    refine ⟨mu, ?_⟩
    intro Z hXZ hZ
    calc
      ‖positivePrefixMean f Z - mu‖ ≤
          realGSSignedPrefixStabilityConstant *
            (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := hmu Z hXZ hZ
      _ ≤ realGSSignedPrefixStabilityConstant *
          (Real.log (X : ℝ)) ^ (-c) :=
        mul_le_mul_of_nonneg_left hrpowQuarter
          realGSSignedPrefixStabilityConstant_nonneg
      _ ≤ max C_halasz
            (max C_far realGSSignedPrefixStabilityConstant) *
          (Real.log (X : ℝ)) ^ (-c) :=
        mul_le_mul_of_nonneg_right
          ((le_max_right C_far realGSSignedPrefixStabilityConstant).trans
            (le_max_right C_halasz
              (max C_far realGSSignedPrefixStabilityConstant))) hrpow

/-- Fixed `1/1000` specialization matching the weak finite-Halasz scalar
schedule. -/
theorem eventually_uniform_real_prefix_stable_one_thousandth_of_halaszLargeZero_of_farLargeZero
    {C_halasz C_far : ℝ}
    (hhalasz : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) →
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          C_halasz * (Real.log (X : ℝ)) ^ (-1 / 1000 : ℝ))
    (hfar : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      (∃ t₀ : ℝ,
        (Real.log (X : ℝ)) ^ (4 : ℕ) < |t₀| ∧
        |t₀| ≤ 3 * X ∧
        pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
          realPrefixMovingThreshold X) →
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          C_far * (Real.log (X : ℝ)) ^ (-1 / 1000 : ℝ)) :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      ∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z - mu‖ ≤
          max C_halasz (max C_far realGSSignedPrefixStabilityConstant) *
            (Real.log (X : ℝ)) ^ (-1 / 1000 : ℝ) := by
  have h :=
    eventually_uniform_real_prefix_stable_rpow_of_halaszLargeZero_of_farLargeZero
      (c := (1 / 1000 : ℝ)) (C_halasz := C_halasz) (C_far := C_far)
      (by norm_num) (by simpa only [neg_div] using hhalasz)
      (by simpa only [neg_div] using hfar)
  simpa only [neg_div] using h

end

end Erdos67b
