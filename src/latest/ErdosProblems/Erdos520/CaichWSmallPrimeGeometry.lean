import ErdosProblems.Erdos520.CaichWoverX
import ErdosProblems.Erdos520.CaichDivisorBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# The many-atom branch of the Caich `W` estimate

For `p * (X + 1) ≤ x`, the length of the short interval between the two
cutoffs is at least one.  Consequently the harmless unit loss caused by the
floor can be absorbed into the interval length.  This gives the support
cardinality estimate that supplies the power of `X` in the Bonami budget.
-/

/-- The literal short support has the expected length, up to the factor two
which absorbs the floor loss, in the small-prime branch. -/
theorem caichWShortSupport_card_cast_le_of_smallPrime
    {X x p : ℕ} (hX : 0 < X) (hp : 0 < p)
    (hsmall : p * (X + 1) ≤ x)
    {t : ℝ} (hpt : (p : ℝ) ≤ t)
    (htq : t ≤ (p : ℝ) * (1 + 1 / (X : ℝ))) :
    ((caichWShortSupport x p t).card : ℝ) ≤
      2 * (x : ℝ) / ((p : ℝ) * (X : ℝ)) := by
  let z : ℕ := Nat.floor ((x : ℝ) / t)
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have htR : (0 : ℝ) < t := hpR.trans_le hpt
  have hzle : z ≤ x / p := by
    simpa only [z] using! caichW_floor_div_le_nat_div x p hp hpt
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
  have hcardNat :
      (caichWShortSupport x p t).card ≤ x / p - z := by
    calc
      (caichWShortSupport x p t).card ≤ (Finset.Ioc z (x / p)).card :=
        Finset.card_le_card hsub
      _ = x / p - z := by simp
  have hfloor : (x : ℝ) / t < (z : ℝ) + 1 := by
    simpa only [z, Nat.cast_add, Nat.cast_one] using!
      (Nat.lt_floor_add_one ((x : ℝ) / t))
  have hnatCast : ((x / p : ℕ) : ℝ) ≤ (x : ℝ) / (p : ℝ) :=
    Nat.cast_div_le
  have hdenom :
      (x : ℝ) / ((p : ℝ) * (1 + 1 / (X : ℝ))) ≤
        (x : ℝ) / t := by
    exact div_le_div_of_nonneg_left (by positivity) htR htq
  have hgap :
      (x : ℝ) / (p : ℝ) -
          (x : ℝ) / ((p : ℝ) * (1 + 1 / (X : ℝ))) =
        (x : ℝ) / ((p : ℝ) * ((X : ℝ) + 1)) := by
    field_simp [hXR.ne', hpR.ne']
    ring
  have hsmallR :
      (p : ℝ) * ((X : ℝ) + 1) ≤ (x : ℝ) := by
    exact_mod_cast hsmall
  have hone_le_gap :
      (1 : ℝ) ≤ (x : ℝ) / ((p : ℝ) * ((X : ℝ) + 1)) := by
    rw [le_div_iff₀ (mul_pos hpR (by positivity))]
    simpa only [one_mul] using! hsmallR
  have hgap_le :
      (x : ℝ) / ((p : ℝ) * ((X : ℝ) + 1)) ≤
        (x : ℝ) / ((p : ℝ) * (X : ℝ)) := by
    apply div_le_div_of_nonneg_left (by positivity)
    · positivity
    · exact mul_le_mul_of_nonneg_left (by linarith) hpR.le
  have hwidth :
      ((x / p - z : ℕ) : ℝ) ≤
        2 * (x : ℝ) / ((p : ℝ) * (X : ℝ)) := by
    rw [Nat.cast_sub hzle]
    calc
      ((x / p : ℕ) : ℝ) - (z : ℝ) ≤
          (x : ℝ) / (p : ℝ) - (x : ℝ) / t + 1 := by
        linarith
      _ ≤ (x : ℝ) / (p : ℝ) -
            (x : ℝ) / ((p : ℝ) * (1 + 1 / (X : ℝ))) + 1 := by
        linarith
      _ = (x : ℝ) / ((p : ℝ) * ((X : ℝ) + 1)) + 1 := by
        rw [hgap]
      _ ≤ 2 * ((x : ℝ) / ((p : ℝ) * ((X : ℝ) + 1))) := by
        linarith
      _ ≤ 2 * ((x : ℝ) / ((p : ℝ) * (X : ℝ))) := by
        gcongr
      _ = 2 * (x : ℝ) / ((p : ℝ) * (X : ℝ)) := by ring
  exact (by exact_mod_cast hcardNat :
    ((caichWShortSupport x p t).card : ℝ) ≤
      ((x / p - z : ℕ) : ℝ)).trans hwidth

/-- The short divisor energy is bounded by the global divisor sum at its
upper endpoint.  The ambient logarithm is enlarged from `x / p` to `x`,
which is the form used when summing over primes. -/
theorem caichWShortDivisorEnergy_le_of_smallPrime
    {r x p : ℕ} (hr : 1 ≤ r) (hxp : 3 ≤ x / p)
    (t : ℝ) :
    caichWShortDivisorEnergy r x p t ≤
      ((x / p : ℕ) : ℝ) *
        (2 * Real.log (x : ℝ)) ^ (4 * r - 4) := by
  have hm : 1 ≤ 4 * r - 3 := by omega
  have hglobal := sum_orderedDivisorCount_le_two_log
    (4 * r - 3) (x / p) (caichWShortSupport x p t)
    hm hxp (caichWShortSupport_subset_Ioc x p t)
  have hglobal' :
      (∑ n ∈ caichWShortSupport x p t,
          (orderedDivisorCount (4 * r - 3) n : ℝ)) ≤
        ((x / p : ℕ) : ℝ) *
          (2 * Real.log ((x / p : ℕ) : ℝ)) ^ ((4 * r - 3) - 1) := by
    simpa only [Nat.cast_sum] using! hglobal
  have hxp_le_x : x / p ≤ x := Nat.div_le_self x p
  have hlog_nonneg : 0 ≤ 2 * Real.log ((x / p : ℕ) : ℝ) := by
    have : 0 ≤ Real.log ((x / p : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ x / p by omega))
    positivity
  have hlog_le :
      2 * Real.log ((x / p : ℕ) : ℝ) ≤
        2 * Real.log (x : ℝ) := by
    gcongr
  unfold caichWShortDivisorEnergy
  calc
    (∑ n ∈ caichWShortSupport x p t,
        (orderedDivisorCount (4 * r - 3) n : ℝ)) ≤
        ((x / p : ℕ) : ℝ) *
          (2 * Real.log ((x / p : ℕ) : ℝ)) ^
            ((4 * r - 3) - 1) := hglobal'
    _ = ((x / p : ℕ) : ℝ) *
          (2 * Real.log ((x / p : ℕ) : ℝ)) ^ (4 * r - 4) := by
      congr 2
    _ ≤ ((x / p : ℕ) : ℝ) *
          (2 * Real.log (x : ℝ)) ^ (4 * r - 4) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlog_nonneg hlog_le (4 * r - 4)) (by positivity)

end Problem520
end Erdos
