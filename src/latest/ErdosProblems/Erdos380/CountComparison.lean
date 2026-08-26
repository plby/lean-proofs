import ErdosProblems.Erdos380.SingletonCount
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Exact comparison functions and the excess count

With the convention `P(1) = 1`, the displayed comparison set includes one.
This file handles that term explicitly and identifies the remaining
asymptotic obligation. It does not prove that obligation.
-/

open scoped BigOperators Topology Asymptotics
open Filter Asymptotics

namespace Erdos380

lemma two_pow_singletonBad (k : ℕ) : SingletonBad (2 ^ (k + 2)) := by
  have hp := Nat.prime_two
  refine ⟨?_, ?_⟩
  · have h : 2 ^ 1 ≤ 2 ^ (k + 2) := by gcongr <;> omega
    simpa using h
  · rw [largestPrimeFactor_pow 2 (by omega), largestPrimeFactor_of_prime hp]
    exact pow_dvd_pow 2 (by omega)

lemma singletonBadUpTo_card_ge {N k : ℕ} (hk : 2 ^ (k + 2) ≤ N) :
    k ≤ (singletonBadUpTo N).card := by
  classical
  let f : ℕ → ℕ := fun j => 2 ^ (j + 2)
  have hf : Function.Injective f := by
    intro i j hij
    have h := Nat.pow_right_injective (by decide : 2 ≤ 2) hij
    omega
  have hsub : (Finset.range k).image f ⊆ singletonBadUpTo N := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    have hjk : j < k := Finset.mem_range.mp hj
    have hjN : f j ≤ N := by
      apply le_trans _ hk
      dsimp [f]
      gcongr
      omega
    have hjBad := two_pow_singletonBad j
    exact mem_singletonBadUpTo.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)), hjN, hjBad⟩
  have h := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hf, Finset.card_range] using h

theorem tendsto_A_atTop : Tendsto A atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨k, hk⟩ := exists_nat_ge b
  filter_upwards [eventually_ge_atTop ((2 ^ (k + 2) : ℕ) : ℝ)] with x hx
  have hfloor : 2 ^ (k + 2) ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hA : (k : ℝ) ≤ A x := by
    unfold A
    exact_mod_cast singletonBadUpTo_card_ge hfloor
  exact hk.trans hA

noncomputable section

/-- The comparison set exactly as written, including `1` under our convention. -/
def repeatedLargestPrimeUpTo (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => largestPrimeFactor n ^ 2 ∣ n

def repeatedLargestPrimeCount (x : ℝ) : ℝ :=
  ((repeatedLargestPrimeUpTo ⌊x⌋₊).card : ℝ)

lemma repeatedLargestPrimeUpTo_eq_insert {N : ℕ} (hN : 1 ≤ N) :
    repeatedLargestPrimeUpTo N = insert 1 (singletonBadUpTo N) := by
  classical
  ext n
  simp only [repeatedLargestPrimeUpTo, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_insert, mem_singletonBadUpTo, SingletonBad]
  by_cases hn : n = 1
  · subst n
    simp [hN]
  · simp only [hn, false_or]
    omega

lemma repeatedLargestPrimeCount_eq_A_add_one {x : ℝ} (hx : 1 ≤ x) :
    repeatedLargestPrimeCount x = A x + 1 := by
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hnot : 1 ∉ singletonBadUpTo ⌊x⌋₊ := by simp [SingletonBad]
  rw [repeatedLargestPrimeCount, repeatedLargestPrimeUpTo_eq_insert hN,
    Finset.card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one]
  rfl

theorem one_isLittleO_A : (fun _ : ℝ => (1 : ℝ)) =o[atTop] A := by
  apply (isLittleO_one_left_iff ℝ).mpr
  simpa only [Real.norm_eq_abs, abs_of_nonneg (A_nonneg _)] using tendsto_A_atTop

theorem repeatedLargestPrimeCount_isEquivalent_A : repeatedLargestPrimeCount ~[atTop] A := by
  have h := (IsEquivalent.refl : A ~[atTop] A).add_isLittleO one_isLittleO_A
  apply h.congr_left
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (repeatedLargestPrimeCount_eq_A_add_one hx).symm

/-- Points covered by bad intervals but not themselves bad singletons. -/
def excessPointsUpTo (N : ℕ) : Finset ℕ := badPointsUpTo N \ singletonBadUpTo N

def excessCount (x : ℝ) : ℝ := ((excessPointsUpTo ⌊x⌋₊).card : ℝ)

theorem B_eq_A_add_excessCount (x : ℝ) : B x = A x + excessCount x := by
  have h := Finset.card_sdiff_add_card_eq_card
    (singletonBadUpTo_subset_badPointsUpTo ⌊x⌋₊)
  unfold B A excessCount excessPointsUpTo
  exact_mod_cast (by omega : (badPointsUpTo ⌊x⌋₊).card =
    (singletonBadUpTo ⌊x⌋₊).card + (badPointsUpTo ⌊x⌋₊ \ singletonBadUpTo ⌊x⌋₊).card)

/-- Exact equivalence, not a replacement of the asymptotic by a lower bound. -/
theorem bad_asymptotic_iff_excess_littleO :
    B ~[atTop] repeatedLargestPrimeCount ↔ excessCount =o[atTop] A := by
  have hBA : B ~[atTop] repeatedLargestPrimeCount ↔ B ~[atTop] A :=
    ⟨fun h => h.trans repeatedLargestPrimeCount_isEquivalent_A,
      fun h => h.trans repeatedLargestPrimeCount_isEquivalent_A.symm⟩
  rw [hBA]
  change (B - A) =o[atTop] A ↔ excessCount =o[atTop] A
  have heq : B - A = excessCount := by
    funext x
    change B x - A x = excessCount x
    rw [B_eq_A_add_excessCount]
    ring
  rw [heq]

end

end Erdos380
