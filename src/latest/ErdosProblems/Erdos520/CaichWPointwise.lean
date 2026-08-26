import ErdosProblems.Erdos520.CaichWoverX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators Interval ENNReal

namespace Erdos
namespace Problem520

/-!
# The single-atom branch of the Caich `W` estimate

When `(X + 1) p > x`, the two cutoffs occurring in the short difference
are less than one integer apart throughout `p ≤ t ≤ p(1+1/X)`.  Hence the
short support contains at most one integer.  This yields pointwise and
`L^r` bounds with constant one, with no divisor estimate.
-/

/-- Floor-safe large-prime condition. -/
def caichWLargePrimeCondition (X x p : ℕ) : Prop :=
  x < p * (X + 1)

/-- The two natural cutoffs differ by at most one in the large-prime
branch. -/
theorem caichW_natDiv_le_floor_add_one_of_largePrime
    {X x p : ℕ} (hX : 0 < X) (hp : 0 < p)
    (hlarge : caichWLargePrimeCondition X x p)
    {t : ℝ} (hpt : (p : ℝ) ≤ t)
    (htq : t ≤ (p : ℝ) * (1 + 1 / (X : ℝ))) :
    x / p ≤ Nat.floor ((x : ℝ) / t) + 1 := by
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have htR : (0 : ℝ) < t := hpR.trans_le hpt
  have hfactor : (0 : ℝ) < 1 + 1 / (X : ℝ) := by positivity
  have hqR : (0 : ℝ) < (p : ℝ) * (1 + 1 / (X : ℝ)) :=
    mul_pos hpR hfactor
  have hlargeR : (x : ℝ) < (p : ℝ) * ((X : ℝ) + 1) := by
    exact_mod_cast hlarge
  have hgap :
      (x : ℝ) / (p : ℝ) -
          (x : ℝ) / ((p : ℝ) * (1 + 1 / (X : ℝ))) =
        (x : ℝ) / ((p : ℝ) * ((X : ℝ) + 1)) := by
    field_simp [hXR.ne', hpR.ne']
    <;> ring
  have hsmall :
      (x : ℝ) / ((p : ℝ) * ((X : ℝ) + 1)) < 1 := by
    apply (div_lt_one (mul_pos hpR (by positivity))).2
    exact hlargeR
  have hbase :
      (x : ℝ) / (p : ℝ) <
        (x : ℝ) / ((p : ℝ) * (1 + 1 / (X : ℝ))) + 1 := by
    linarith [hgap]
  have hdenom :
      (x : ℝ) / ((p : ℝ) * (1 + 1 / (X : ℝ))) ≤
        (x : ℝ) / t := by
    exact div_le_div_of_nonneg_left (by positivity) htR htq
  have hnatCast : ((x / p : ℕ) : ℝ) ≤ (x : ℝ) / (p : ℝ) :=
    Nat.cast_div_le
  have hreal : ((x / p : ℕ) : ℝ) < (x : ℝ) / t + 1 := by
    linarith
  by_contra hnot
  have hsucc : Nat.floor ((x : ℝ) / t) + 2 ≤ x / p := by omega
  have hfloor : (x : ℝ) / t <
      (Nat.floor ((x : ℝ) / t) : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using!
      (Nat.lt_floor_add_one ((x : ℝ) / t))
  have hsuccR :
      (Nat.floor ((x : ℝ) / t) : ℝ) + 2 ≤ (x / p : ℕ) := by
    exact_mod_cast hsucc
  norm_num at hsuccR
  linarith

/-- In the large-prime branch the literal short support has at most one
element. -/
theorem caichWShortSupport_card_le_one_of_largePrime
    {X x p : ℕ} (hX : 0 < X) (hp : 0 < p)
    (hlarge : caichWLargePrimeCondition X x p)
    {t : ℝ} (hpt : (p : ℝ) ≤ t)
    (htq : t ≤ (p : ℝ) * (1 + 1 / (X : ℝ))) :
    (caichWShortSupport x p t).card ≤ 1 := by
  let z : ℕ := Nat.floor ((x : ℝ) / t)
  have hcutoff : x / p ≤ z + 1 := by
    simpa only [z] using!
      caichW_natDiv_le_floor_add_one_of_largePrime hX hp hlarge hpt htq
  have hsub : caichWShortSupport x p t ⊆ Finset.Ioc z (x / p) := by
    intro n hn
    have hnDiff := Finset.mem_sdiff.mp hn
    have hnUpper := hnDiff.1
    have hnInfo := Nat.mem_smoothNumbersUpTo.mp hnUpper
    have hzn : z < n := by
      by_contra hnot
      have hnLower : n ∈ Nat.smoothNumbersUpTo z p := by
        rw [Nat.mem_smoothNumbersUpTo]
        exact ⟨by omega, hnInfo.2⟩
      exact hnDiff.2 hnLower
    exact Finset.mem_Ioc.mpr ⟨hzn, hnInfo.1⟩
  calc
    (caichWShortSupport x p t).card ≤ (Finset.Ioc z (x / p)).card :=
      Finset.card_le_card hsub
    _ = x / p - z := by simp
    _ ≤ 1 := by omega

/-- The short RMF difference is a sum over at most one atom, so its absolute
value is at most one. -/
theorem abs_caichWShortDifference_le_one_of_largePrime
    {X x p : ℕ} (hX : 0 < X) (hp : 0 < p)
    (hlarge : caichWLargePrimeCondition X x p)
    {t : ℝ} (hpt : (p : ℝ) ≤ t)
    (htq : t ≤ (p : ℝ) * (1 + 1 / (X : ℝ)))
    (omega : Omega) :
    |caichWShortDifference x p t omega| ≤ 1 := by
  rw [caichWShortDifference_eq_sum x p hp hpt omega]
  calc
    |∑ n ∈ caichWShortSupport x p t, f omega n| ≤
        ∑ n ∈ caichWShortSupport x p t, |f omega n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ caichWShortSupport x p t, (1 : ℝ) := by
      gcongr with n hn
      exact abs_f_le_one omega n
    _ = ((caichWShortSupport x p t).card : ℝ) := by simp
    _ ≤ 1 := by
      exact_mod_cast caichWShortSupport_card_le_one_of_largePrime
        hX hp hlarge hpt htq

/-- The squared short kernel is pointwise at most one in the large-prime
branch. -/
theorem caichWShortKernel_le_one_of_largePrime
    {X x p : ℕ} (hX : 0 < X) (hp : 0 < p)
    (hlarge : caichWLargePrimeCondition X x p)
    {t : ℝ} (hpt : (p : ℝ) ≤ t)
    (htq : t ≤ (p : ℝ) * (1 + 1 / (X : ℝ)))
    (omega : Omega) :
    caichWShortKernel x p t omega ≤ 1 := by
  have habs := abs_caichWShortDifference_le_one_of_largePrime
    hX hp hlarge hpt htq omega
  unfold caichWShortKernel
  exact pow_le_one₀ (abs_nonneg _) habs

/-- A large prime contributes at most one to `W`, pointwise in `omega`.
This uses only the single-atom geometry of the short interval. -/
theorem caichWPrimeContribution_le_one_of_largePrime
    {X x p : ℕ} (hX : 0 < X) (hp : 0 < p)
    (hlarge : caichWLargePrimeCondition X x p)
    (omega : Omega) :
    caichWPrimeContribution (X : ℝ) x p omega ≤ 1 := by
  let q : ℝ := (p : ℝ) * (1 + 1 / (X : ℝ))
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpq : (p : ℝ) ≤ q := by
    dsimp only [q]
    have hinv : (0 : ℝ) ≤ 1 / (X : ℝ) := by positivity
    nlinarith
  have hint_nonneg :
      0 ≤ ∫ t in (p : ℝ)..q, caichWShortKernel x p t omega :=
    intervalIntegral.integral_nonneg hpq fun t _ht ↦
      caichWShortKernel_nonneg x p t omega
  have hnorm :
      ‖∫ t in (p : ℝ)..q, caichWShortKernel x p t omega‖ ≤
        1 * |q - (p : ℝ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le hpq] at ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (caichWShortKernel_nonneg x p t omega)]
    exact caichWShortKernel_le_one_of_largePrime hX hp hlarge
      (le_of_lt ht.1) ht.2 omega
  have hlength : q - (p : ℝ) = (p : ℝ) / (X : ℝ) := by
    dsimp only [q]
    field_simp [hXR.ne']
    ring
  have hint_le :
      (∫ t in (p : ℝ)..q, caichWShortKernel x p t omega) ≤
        (p : ℝ) / (X : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hint_nonneg] at hnorm
    rw [hlength, abs_of_nonneg (by positivity)] at hnorm
    simpa only [one_mul] using! hnorm
  unfold caichWPrimeContribution caichShortPrimeAverage
  change (X : ℝ) / (p : ℝ) *
      (∫ t in (p : ℝ)..q, caichWShortKernel x p t omega) ≤ 1
  calc
    (X : ℝ) / (p : ℝ) *
        (∫ t in (p : ℝ)..q, caichWShortKernel x p t omega) ≤
      (X : ℝ) / (p : ℝ) * ((p : ℝ) / (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = 1 := by field_simp [hXR.ne', hpR.ne']

/-- Consequently every positive integral moment of one large-prime
contribution has `L^r` root at most one. -/
theorem caichWPrimeContribution_moment_root_le_one_of_largePrime
    {X x p r : ℕ} (hX : 0 < X) (hp : 0 < p)
    (hlarge : caichWLargePrimeCondition X x p) (hr : 0 < r) :
    (∫ omega, caichWPrimeContribution (X : ℝ) x p omega ^ r ∂μ) ^
        (1 / (r : ℝ)) ≤ 1 := by
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hint : Integrable
      (fun omega ↦ caichWPrimeContribution (X : ℝ) x p omega ^ r) μ :=
    integrable_caichWPrimeContribution_pow hXR x hp hr
  have hmoment_nonneg :
      0 ≤ ∫ omega, caichWPrimeContribution (X : ℝ) x p omega ^ r ∂μ :=
    integral_nonneg fun omega ↦ pow_nonneg
      (caichWPrimeContribution_nonneg hXR x hp omega) r
  have hmoment_le :
      (∫ omega, caichWPrimeContribution (X : ℝ) x p omega ^ r ∂μ) ≤ 1 := by
    calc
      (∫ omega, caichWPrimeContribution (X : ℝ) x p omega ^ r ∂μ) ≤
          ∫ _omega : Omega, (1 : ℝ) ∂μ := by
        apply integral_mono hint (integrable_const 1)
        intro omega
        exact pow_le_one₀
          (caichWPrimeContribution_nonneg hXR x hp omega)
          (caichWPrimeContribution_le_one_of_largePrime
            hX hp hlarge omega)
      _ = 1 := by simp
  exact Real.rpow_le_one hmoment_nonneg hmoment_le (by positivity)

end Problem520
end Erdos
