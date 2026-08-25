import ErdosProblems.Erdos67.MRPerronProjectionErrorBound

/-!
# Quantitative Perron error for a dyadically supported coefficient

This file bounds the explicit error term left by the finite Lemma-14 Perron
reduction.  A one-bounded coefficient supported on `(Y,2Y]` has coefficient
mass at most `H_(2Y)` on the line `sigma = 1`.  At truncation height `X / 2`,
the reciprocal-distance estimate gives a pointwise harmonic bound at both
endpoints of every interval `(x,x+H]` with `X < x <= 2X` and `H <= X`.
-/

open scoped BigOperators
open Finset

namespace Erdos67.MRRestrictedPerronErrorBound

noncomputable section

open BoundedGaps.Maynard
open MRPerronProjectionErrorBound

/-- Monotonicity of the real cast of the harmonic numbers. -/
theorem harmonic_cast_mono {m n : ℕ} (hmn : m ≤ n) :
    (harmonic m : ℝ) ≤ (harmonic n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans hmn⟩
  · intro k hk hkm
    positivity

theorem harmonic_cast_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  exact Finset.sum_nonneg fun k hk ↦ by positivity

/-- For a raw one-bounded coefficient, a single near-diagonal Perron
summand is controlled by reciprocal distance from the endpoint. -/
theorem one_bounded_near_summand_le
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {z n : ℕ} (hz : 0 < z) {T : ℝ} (hT : 0 < T) :
    ‖a n‖ * dirichletPerronNearError z T n ≤
      (2 * (z : ℝ) / T) * perronReciprocalDistance z n := by
  rw [dirichletPerronNearError]
  split_ifs with hcentral
  · rcases hcentral with ⟨hn, hlower, hupper, hnz⟩
    have hdist : (0 : ℝ) < |(z : ℝ) - n| := by
      apply abs_pos.mpr
      rw [sub_ne_zero]
      exact_mod_cast hnz.symm
    have hnear0 : 0 ≤ min 1
        (2 * (z : ℝ) / (T * |(z : ℝ) - n|)) := by
      exact le_min (by norm_num) (by positivity)
    have hnear : min 1
        (2 * (z : ℝ) / (T * |(z : ℝ) - n|)) ≤
        2 * (z : ℝ) / (T * |(z : ℝ) - n|) := min_le_right _ _
    calc
      ‖a n‖ * min 1 (2 * (z : ℝ) / (T * |(z : ℝ) - n|)) ≤
          1 * min 1 (2 * (z : ℝ) / (T * |(z : ℝ) - n|)) :=
        mul_le_mul_of_nonneg_right (ha n hn) hnear0
      _ ≤ 2 * (z : ℝ) / (T * |(z : ℝ) - n|) := by
        simpa only [one_mul] using hnear
      _ = (2 * (z : ℝ) / T) * perronReciprocalDistance z n := by
        rw [perronReciprocalDistance, if_neg hnz]
        field_simp [ne_of_gt hT, ne_of_gt hdist]
  · have hfactor : 0 ≤ (2 * (z : ℝ) / T) := by positivity
    rw [mul_zero]
    exact mul_nonneg hfactor (perronReciprocalDistance_nonneg z n)

/-- The near-diagonal Perron mass of a raw one-bounded coefficient is at
most `4 z H_z / T`. -/
theorem dirichletPerronNearMass_one_bounded_le_harmonic
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {z : ℕ} (hz : 0 < z) {T : ℝ} (hT : 0 < T) :
    dirichletPerronNearMass a z T ≤
      4 * (z : ℝ) * (harmonic z : ℝ) / T := by
  unfold dirichletPerronNearMass
  rw [tsum_eq_sum (s := Finset.range (2 * z))]
  · calc
      (∑ n ∈ Finset.range (2 * z),
          ‖a n‖ * dirichletPerronNearError z T n) ≤
          ∑ n ∈ Finset.range (2 * z),
            (2 * (z : ℝ) / T) * perronReciprocalDistance z n := by
        apply Finset.sum_le_sum
        intro n hn
        exact one_bounded_near_summand_le ha hz hT
      _ = (2 * (z : ℝ) / T) *
          ∑ n ∈ Finset.range (2 * z), perronReciprocalDistance z n := by
        rw [Finset.mul_sum]
      _ ≤ (2 * (z : ℝ) / T) * (2 * (harmonic z : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
          (sum_range_two_mul_perronReciprocalDistance_le z hz)
        positivity
      _ = 4 * (z : ℝ) * (harmonic z : ℝ) / T := by ring
  · intro n hn
    have hnLower : 2 * z ≤ n := by simpa using hn
    have hnLowerR : (2 : ℝ) * z ≤ n := by exact_mod_cast hnLower
    rw [dirichletPerronNearError, if_neg]
    · simp
    · intro h
      exact (not_lt_of_ge hnLowerR) h.2.2.1

/-- The reciprocal mass of an arbitrary subset of `(Y,2Y]` is at most
one. -/
theorem sum_inv_dyadicRestrictedSupport_le_one (S : Finset ℕ) (Y : ℕ) :
    (∑ n ∈ dyadicRestrictedSupport S Y, ((n : ℝ))⁻¹) ≤ 1 := by
  let D := dyadicRestrictedSupport S Y
  have hsubset : D ⊆ Finset.Ioc Y (2 * Y) := by
    intro n hn
    exact (Finset.mem_inter.mp hn).1
  have hcardNat : D.card ≤ Y := by
    calc
      D.card ≤ (Finset.Ioc Y (2 * Y)).card := Finset.card_le_card hsubset
      _ = Y := by simp; omega
  have hcard : (D.card : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hcardNat
  have hpoint : ∀ n ∈ D, ((n : ℝ))⁻¹ ≤ ((Y + 1 : ℕ) : ℝ)⁻¹ := by
    intro n hn
    have hnIoc := Finset.mem_Ioc.mp (hsubset hn)
    have hYonePos : (0 : ℝ) < (Y + 1 : ℕ) := by positivity
    have hYoneLe : (((Y + 1 : ℕ) : ℝ)) ≤ n := by exact_mod_cast (by omega)
    simpa only [one_div] using one_div_le_one_div_of_le hYonePos hYoneLe
  change (∑ n ∈ D, ((n : ℝ))⁻¹) ≤ 1
  calc
    (∑ n ∈ D, ((n : ℝ))⁻¹) ≤
        ∑ _n ∈ D, (((Y + 1 : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      exact hpoint n hn
    _ = (D.card : ℝ) * (((Y + 1 : ℕ) : ℝ))⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Y : ℝ) * (((Y + 1 : ℕ) : ℝ))⁻¹ := by
      gcongr
    _ ≤ 1 := by
      rw [inv_eq_one_div, mul_one_div]
      apply (div_le_one (by positivity)).2
      norm_num

/-- On `sigma = 1`, a one-bounded coefficient supported in `(Y,2Y]` has
absolute Perron coefficient mass at most one. -/
theorem dirichletPerronCoefficientMass_dyadicRestricted_le_one
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (Y : ℕ) :
    dirichletPerronCoefficientMass
        (dyadicRestrictedCoefficient S f Y) 1 ≤
      1 := by
  let D : Finset ℕ := dyadicRestrictedSupport S Y
  have hsupp : ∀ n ∉ D,
      ‖LSeries.term (dyadicRestrictedCoefficient S f Y)
        ((1 : ℝ) : ℂ) n‖ = 0 := by
    intro n hn
    unfold LSeries.term dyadicRestrictedCoefficient
    rw [if_neg hn]
    simp
  unfold dirichletPerronCoefficientMass
  rw [tsum_eq_sum (s := D) hsupp]
  calc
    (∑ n ∈ D,
        ‖LSeries.term (dyadicRestrictedCoefficient S f Y)
          ((1 : ℝ) : ℂ) n‖) ≤
        ∑ n ∈ D, ((n : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnIoc : n ∈ Finset.Ioc Y (2 * Y) :=
        (Finset.mem_inter.mp hn).1
      have hnpos : 0 < n := by
        rw [Finset.mem_Ioc] at hnIoc
        omega
      rw [LSeries.norm_term_eq, if_neg hnpos.ne',
        dyadicRestrictedCoefficient, if_pos hn]
      norm_num only [Complex.ofReal_re, Real.rpow_one]
      simpa only [one_div] using
        div_le_div_of_nonneg_right (hf n hnpos) (Nat.cast_nonneg n)
    _ ≤ 1 := sum_inv_dyadicRestrictedSupport_le_one S Y

/-- Explicit envelope for the square mass of finite Lemma-14 Perron errors
at truncation height `X / 2`.  The `H_(3X)` factor is genuine for this
absolute pointwise error: for a dense one-bounded coefficient, the
near-diagonal reciprocal-distance mass is harmonic. -/
def dyadicRestrictedPerronErrorHalfHeightBound (X H : ℕ) : ℝ :=
  (X : ℝ) *
    ((48 * (harmonic (3 * X) : ℝ) + 385) / H) ^ 2

/-- Uniform finite bound for the spatially decoupled Lemma-14 Perron error.
It applies in particular to the two dyadic-cover choices `Y = X` and
`Y = 2X`. -/
theorem dyadicRestrictedPerronErrorMeanSquareAt_halfHeight_le
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y X H : ℕ} (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X) :
    dyadicRestrictedPerronErrorMeanSquareAt
        S f Y X H ((X : ℝ) / 2) ≤
      dyadicRestrictedPerronErrorHalfHeightBound X H := by
  classical
  let a : ℕ → ℂ := dyadicRestrictedCoefficient S f Y
  let B : ℝ :=
    (48 * (harmonic (3 * X) : ℝ) + 385) / H
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hT : (0 : ℝ) < (X : ℝ) / 2 := by positivity
  have ha : ∀ n, 0 < n → ‖a n‖ ≤ 1 := by
    intro n hn
    dsimp only [a, dyadicRestrictedCoefficient]
    split_ifs
    · exact hf n hn
    · simp
  have hmass : dirichletPerronCoefficientMass a 1 ≤ 1 := by
    dsimp only [a]
    exact dirichletPerronCoefficientMass_dyadicRestricted_le_one
      S hf Y
  have hpoint : ∀ x ∈ Finset.Ioc X (2 * X),
      lemma14PerronEndpointError a x H ((X : ℝ) / 2) ≤ B := by
    intro x hxmem
    have hxIoc := Finset.mem_Ioc.mp hxmem
    have hxpos : 0 < x := by omega
    have hxHpos : 0 < x + H := by omega
    have hxle : x ≤ 2 * X := hxIoc.2
    have hxHle : x + H ≤ 3 * X := by omega
    have hharmx : (harmonic x : ℝ) ≤ (harmonic (3 * X) : ℝ) :=
      harmonic_cast_mono (by omega)
    have hharmxH : (harmonic (x + H) : ℝ) ≤
        (harmonic (3 * X) : ℝ) := harmonic_cast_mono hxHle
    have hnearx : dirichletPerronNearMass a x ((X : ℝ) / 2) ≤
        24 * (harmonic (3 * X) : ℝ) := by
      calc
        _ ≤ 4 * (x : ℝ) * (harmonic x : ℝ) / ((X : ℝ) / 2) :=
          dirichletPerronNearMass_one_bounded_le_harmonic ha hxpos hT
        _ = 8 * ((x : ℝ) / X) * (harmonic x : ℝ) := by
          field_simp [ne_of_gt hXR]
          all_goals ring
        _ ≤ 8 * 3 * (harmonic (3 * X) : ℝ) := by
          have hxRle : (x : ℝ) / X ≤ 3 := by
            rw [div_le_iff₀ hXR]
            exact_mod_cast (show x ≤ 3 * X by omega)
          have hharmnonneg : 0 ≤ (harmonic x : ℝ) :=
            harmonic_cast_nonneg x
          calc
            8 * ((x : ℝ) / X) * (harmonic x : ℝ) ≤
                8 * 3 * (harmonic x : ℝ) := by gcongr
            _ ≤ 8 * 3 * (harmonic (3 * X) : ℝ) := by gcongr
        _ = _ := by ring
    have hnearxH : dirichletPerronNearMass a (x + H) ((X : ℝ) / 2) ≤
        24 * (harmonic (3 * X) : ℝ) := by
      calc
        _ ≤ 4 * ((x + H : ℕ) : ℝ) * (harmonic (x + H) : ℝ) /
            ((X : ℝ) / 2) :=
          dirichletPerronNearMass_one_bounded_le_harmonic ha hxHpos hT
        _ = 8 * (((x + H : ℕ) : ℝ) / X) *
            (harmonic (x + H) : ℝ) := by
          field_simp [ne_of_gt hXR]
          all_goals ring
        _ ≤ 8 * 3 * (harmonic (3 * X) : ℝ) := by
          have hxHRle : (((x + H : ℕ) : ℝ) / X) ≤ 3 := by
            rw [div_le_iff₀ hXR]
            exact_mod_cast hxHle
          have hharmnonneg : 0 ≤ (harmonic (x + H) : ℝ) :=
            harmonic_cast_nonneg (x + H)
          calc
            8 * (((x + H : ℕ) : ℝ) / X) *
                (harmonic (x + H) : ℝ) ≤
                8 * 3 * (harmonic (x + H) : ℝ) := by gcongr
            _ ≤ 8 * 3 * (harmonic (3 * X) : ℝ) := by gcongr
        _ = _ := by ring
    have htailx :
        (32 * (x : ℝ) ^ (1 : ℝ) / ((X : ℝ) / 2)) *
            dirichletPerronCoefficientMass a 1 ≤
          192 := by
      rw [Real.rpow_one]
      have hfactor : 32 * (x : ℝ) / ((X : ℝ) / 2) ≤ 192 := by
        rw [div_le_iff₀ hT]
        nlinarith [show (x : ℝ) ≤ 2 * X by exact_mod_cast hxle]
      calc
        _ ≤ (32 * (x : ℝ) / ((X : ℝ) / 2)) * 1 := by
          exact mul_le_mul_of_nonneg_left hmass (by positivity)
        _ ≤ 192 := by simpa using hfactor
    have htailxH :
        (32 * (((x + H : ℕ) : ℝ)) ^ (1 : ℝ) / ((X : ℝ) / 2)) *
            dirichletPerronCoefficientMass a 1 ≤
          192 := by
      rw [Real.rpow_one]
      have hfactor : 32 * (((x + H : ℕ) : ℝ)) / ((X : ℝ) / 2) ≤ 192 := by
        rw [div_le_iff₀ hT]
        have hxHleR : (((x + H : ℕ) : ℝ)) ≤ 3 * (X : ℝ) := by
          exact_mod_cast hxHle
        nlinarith
      calc
        _ ≤ (32 * (((x + H : ℕ) : ℝ)) / ((X : ℝ) / 2)) * 1 := by
          exact mul_le_mul_of_nonneg_left hmass (by positivity)
        _ ≤ 192 := by simpa using hfactor
    have hendx : ‖a x‖ ≤ 1 := ha x hxpos
    have hendxH : ‖a (x + H)‖ ≤ 1 := ha (x + H) hxHpos
    unfold lemma14PerronEndpointError MRHalaszPerron.perronTruncationError
    dsimp only [B]
    apply div_le_div_of_nonneg_right _ hHR.le
    calc
      (dirichletPerronNearMass a (x + H) ((X : ℝ) / 2) +
            (32 * (((x + H : ℕ) : ℝ)) ^ (1 : ℝ) /
              ((X : ℝ) / 2)) * dirichletPerronCoefficientMass a 1 +
          (dirichletPerronNearMass a x ((X : ℝ) / 2) +
            (32 * (x : ℝ) ^ (1 : ℝ) / ((X : ℝ) / 2)) *
              dirichletPerronCoefficientMass a 1) +
          (1 / 2 : ℝ) * (‖a (x + H)‖ + ‖a x‖)) ≤
          (24 * (harmonic (3 * X) : ℝ) + 192) +
            (24 * (harmonic (3 * X) : ℝ) + 192) + 1 := by
        gcongr
        · nlinarith
      _ = 48 * (harmonic (3 * X) : ℝ) + 385 := by ring
  have hBnonneg : 0 ≤ B := by
    dsimp only [B]
    have h3Xnonneg : 0 ≤ (harmonic (3 * X) : ℝ) :=
      harmonic_cast_nonneg (3 * X)
    positivity
  have hmassActualNonneg : 0 ≤ dirichletPerronCoefficientMass a 1 := by
    unfold dirichletPerronCoefficientMass
    exact tsum_nonneg fun n ↦ norm_nonneg _
  have hnearActualNonneg (z : ℕ) :
      0 ≤ dirichletPerronNearMass a z ((X : ℝ) / 2) := by
    unfold dirichletPerronNearMass
    apply tsum_nonneg
    intro n
    apply mul_nonneg (norm_nonneg _)
    unfold dirichletPerronNearError
    split_ifs <;> positivity
  have herrorNonneg (x : ℕ) :
      0 ≤ lemma14PerronEndpointError a x H ((X : ℝ) / 2) := by
    unfold lemma14PerronEndpointError MRHalaszPerron.perronTruncationError
    apply div_nonneg
    · have htailNonneg (z : ℕ) :
          0 ≤ (32 * (z : ℝ) ^ (1 : ℝ) / ((X : ℝ) / 2)) *
            dirichletPerronCoefficientMass a 1 := by positivity
      exact add_nonneg
        (add_nonneg
          (add_nonneg (hnearActualNonneg (x + H))
            (htailNonneg (x + H)))
          (add_nonneg (hnearActualNonneg x) (htailNonneg x)))
        (mul_nonneg (by norm_num)
          (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    · exact_mod_cast hH.le
  unfold dyadicRestrictedPerronErrorMeanSquareAt
    dyadicRestrictedPerronErrorHalfHeightBound
  dsimp only [a] at hpoint ⊢
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        lemma14PerronEndpointError
          (dyadicRestrictedCoefficient S f Y) x H ((X : ℝ) / 2) ^ 2) ≤
        ∑ x ∈ Finset.Ioc X (2 * X), B ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact (sq_le_sq₀ (herrorNonneg x) hBnonneg).2 (hpoint x hx)
    _ = (X : ℝ) * B ^ 2 := by
      have hcard : (Finset.Ioc X (2 * X)).card = X := by
        simp
        omega
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = (X : ℝ) *
        ((48 * (harmonic (3 * X) : ℝ) + 385) / H) ^ 2 := rfl

end

end Erdos67.MRRestrictedPerronErrorBound
