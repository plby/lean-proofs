/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Data.Nat.Choose.Bounds
import PrimeNumberTheoremAnd.Consequences
import UnitFractions.Definitions

/-!
# Erdős 285: a reservoir of products of five nearby primes

Martin's proof uses a positive-density theorem for smooth numbers only to obtain
enough unused denominators for a cardinality adjustment.  A smaller reservoir
suffices for that use.  This file constructs one from products of five distinct
primes in the interval `(9y/10,y]`.

There are asymptotically a positive constant times `y / log y` primes in this
interval.  Products of five-element subsets are distinct by unique
factorization, so the reservoir has order `(y / log y)^5`.  Every product lies
in `(y^5/2,y^5]` and every prime-power divisor is at most `y`.
-/

open Filter Finset Real Asymptotics
open scoped BigOperators Topology

namespace Erdos285

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Primes in the fixed narrow interval `(9y/10,y]`. -/
def reservoirPrimes (y : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊y⌋₊ \ Nat.primesLE ⌊(9 / 10 : ℝ) * y⌋₊

/-- Products of five distinct primes in `reservoirPrimes y`. -/
def smoothReservoir (y : ℝ) : Finset ℕ :=
  (reservoirPrimes y).powersetCard 5 |>.image fun S ↦ S.prod id

lemma mem_reservoirPrimes {y : ℝ} {p : ℕ} (hp : p ∈ reservoirPrimes y) :
    p.Prime ∧ (9 / 10 : ℝ) * y < p ∧ (p : ℝ) ≤ y := by
  rw [reservoirPrimes, Finset.mem_sdiff] at hp
  have hpUpper := Nat.mem_primesLE.mp hp.1
  have hpLower : ⌊(9 / 10 : ℝ) * y⌋₊ < p := by
    simpa [Nat.mem_primesLE, hpUpper.2] using hp.2
  have hy : 0 ≤ y := by
    have hfloorPos : 0 < ⌊y⌋₊ := lt_of_lt_of_le hpUpper.2.pos hpUpper.1
    exact zero_le_one.trans (Nat.floor_pos.mp hfloorPos)
  refine ⟨hpUpper.2, Nat.lt_of_floor_lt hpLower, ?_⟩
  exact (Nat.cast_le.mpr hpUpper.1).trans (Nat.floor_le hy)

lemma reservoirPrime_pos {y : ℝ} {p : ℕ} (hp : p ∈ reservoirPrimes y) : 0 < p :=
  (mem_reservoirPrimes hp).1.pos

private lemma product_of_primes_factors_toFinset {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    (S.prod id).primeFactorsList.toFinset = S := by
  have hprod : (S.sort (· ≤ ·)).prod = S.prod id := by
    calc
      (S.sort (· ≤ ·)).prod = (S.sort (· ≤ ·)).toFinset.prod id := by
        simpa using (List.prod_toFinset id (S.sort_nodup (· ≤ ·))).symm
      _ = S.prod id := by rw [Finset.sort_toFinset]
  have hprime : ∀ p ∈ S.sort (· ≤ ·), p.Prime := by
    intro p hp
    exact hS p ((Finset.mem_sort (· ≤ ·)).mp hp)
  have hperm : List.Perm (S.sort (· ≤ ·)) (S.prod id).primeFactorsList :=
    Nat.primeFactorsList_unique hprod hprime
  exact (List.toFinset_eq_of_perm _ _ hperm).symm.trans (Finset.sort_toFinset _ _)

lemma prod_injective_on_primeSubsets (y : ℝ) :
    Set.InjOn (fun S : Finset ℕ ↦ S.prod id) (reservoirPrimes y).powerset := by
  intro A hA B hB hprod
  have hAprime : ∀ p ∈ A, p.Prime := by
    intro p hp
    exact (mem_reservoirPrimes (Finset.mem_powerset.mp hA hp)).1
  have hBprime : ∀ p ∈ B, p.Prime := by
    intro p hp
    exact (mem_reservoirPrimes (Finset.mem_powerset.mp hB hp)).1
  change A.prod id = B.prod id at hprod
  calc
    A = (A.prod id).primeFactorsList.toFinset :=
      (product_of_primes_factors_toFinset hAprime).symm
    _ = (B.prod id).primeFactorsList.toFinset := by rw [hprod]
    _ = B := product_of_primes_factors_toFinset hBprime

lemma smoothReservoir_card (y : ℝ) :
    (smoothReservoir y).card = Nat.choose (reservoirPrimes y).card 5 := by
  rw [smoothReservoir, Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard 5 (reservoirPrimes y)
  · apply (prod_injective_on_primeSubsets y).mono
    intro S hS
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1

lemma smoothReservoir_card_lower (y : ℝ) :
    (((reservoirPrimes y).card + 1 - 5 : ℕ) : ℝ) ^ 5 /
        ((Nat.factorial 5 : ℕ) : ℝ) ≤
      (smoothReservoir y).card := by
  rw [smoothReservoir_card]
  exact Nat.pow_le_choose 5 (reservoirPrimes y).card

/-- Select any requested number of unused cardinality-adjustment terms from the
reservoir.  All interval and smoothness properties are then inherited from the
ambient finset. -/
lemma exists_smoothReservoir_subset_card_eq {y : ℝ} {m : ℕ}
    (hm : m ≤ (smoothReservoir y).card) :
    ∃ T ⊆ smoothReservoir y, T.card = m :=
  Finset.exists_subset_card_eq hm

lemma mem_smoothReservoir_source {y : ℝ} {n : ℕ} (hn : n ∈ smoothReservoir y) :
    ∃ S ⊆ reservoirPrimes y, S.card = 5 ∧ n = S.prod id := by
  rw [smoothReservoir, Finset.mem_image] at hn
  obtain ⟨S, hS, rfl⟩ := hn
  exact ⟨S, (Finset.mem_powersetCard.mp hS).1, (Finset.mem_powersetCard.mp hS).2, rfl⟩

lemma smoothReservoir_upper {y : ℝ} (_hy : 0 ≤ y) {n : ℕ}
    (hn : n ∈ smoothReservoir y) :
    (n : ℝ) ≤ y ^ 5 := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_smoothReservoir_source hn
  push_cast
  calc
    ∏ p ∈ S, (p : ℝ) ≤ ∏ _p ∈ S, y := by
      exact Finset.prod_le_prod (fun _ _ ↦ by positivity)
        (fun p hp ↦ (mem_reservoirPrimes (hS hp)).2.2)
    _ = y ^ 5 := by simp [Finset.prod_const, hcard]

lemma smoothReservoir_lower {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hn : n ∈ smoothReservoir y) :
    y ^ 5 / 2 < (n : ℝ) := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_smoothReservoir_source hn
  push_cast
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hprod : ((9 / 10 : ℝ) * y) ^ S.card < ∏ p ∈ S, (p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_lt_prod_of_nonempty
      (fun _ _ ↦ mul_pos (by norm_num) hy)
      (fun p hp ↦ (mem_reservoirPrimes (hS hp)).2.1) hSne
  rw [hcard] at hprod
  calc
    y ^ 5 / 2 < ((9 / 10 : ℝ) * y) ^ 5 := by
      have hy5 : 0 < y ^ 5 := pow_pos hy _
      rw [mul_pow]
      norm_num
      nlinarith
    _ < ∏ p ∈ S, (p : ℝ) := hprod

lemma smoothReservoir_primePower_bound {y : ℝ} {n : ℕ}
    (hn : n ∈ smoothReservoir y) :
    UnitFractions.is_smooth y n := by
  obtain ⟨S, hS, -, rfl⟩ := mem_smoothReservoir_source hn
  intro q hq hqDvd
  have hprimeS : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (mem_reservoirPrimes (hS hp)).1
  have hsquarefree : Squarefree (S.prod id) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp <|
        (Nat.coprime_primes (hprimeS p hp) (hprimeS q hq)).2 hpq
    · intro p hp
      exact (hprimeS p hp).squarefree
  have hqprime : q.Prime :=
    Nat.squarefree_and_prime_pow_iff_prime.mp
      ⟨hsquarefree.squarefree_of_dvd hqDvd, hq⟩
  obtain ⟨p, hpS, hqDvdP⟩ := hqprime.prime.exists_mem_finset_dvd hqDvd
  have hqp : q = p := by
    exact (Nat.dvd_prime (hprimeS p hpS)).mp hqDvdP |>.resolve_left hqprime.ne_one
  subst p
  exact (mem_reservoirPrimes (hS hpS)).2.2

/-! ## Prime-number-theorem input -/

lemma reservoirPrimes_card_eq (y : ℝ) (hy : 0 ≤ y) :
    ((reservoirPrimes y).card : ℝ) =
      Nat.primeCounting ⌊y⌋₊ - Nat.primeCounting ⌊(9 / 10 : ℝ) * y⌋₊ := by
  have hfloor : ⌊(9 / 10 : ℝ) * y⌋₊ ≤ ⌊y⌋₊ := by
    exact Nat.floor_mono (by nlinarith)
  have hsub : Nat.primesLE ⌊(9 / 10 : ℝ) * y⌋₊ ⊆ Nat.primesLE ⌊y⌋₊ :=
    Nat.primesLE_mono hfloor
  rw [reservoirPrimes, Finset.card_sdiff_of_subset hsub, Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting]
  rw [Nat.cast_sub (Nat.monotone_primeCounting hfloor)]

/-- A quantitative eventual lower bound for the number of primes in `(9y/10,y]`.
The deliberately loose constant makes the statement convenient downstream. -/
theorem eventually_reservoirPrimes_card_lower :
    ∀ᶠ y : ℝ in atTop,
      y / (100 * Real.log y) ≤ ((reservoirPrimes y).card : ℝ) := by
  obtain ⟨e, he, hpi⟩ := pi_alt
  have heBound := he.bound (show (0 : ℝ) < 1 / 100 by norm_num)
  have hscale : Tendsto (fun y : ℝ ↦ (9 / 10 : ℝ) * y) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have heBoundScaled := hscale.eventually heBound
  filter_upwards [heBound, heBoundScaled, eventually_gt_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop (-100 * Real.log (9 / 10 : ℝ))]
      with y hey hecy hy hlogLarge
  have hy0 : 0 ≤ y := by linarith
  have hyPos : 0 < y := by linarith
  have hcy0 : 0 < (9 / 10 : ℝ) * y := mul_pos (by norm_num) hyPos
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogcy : 0 < Real.log ((9 / 10 : ℝ) * y) := by
    apply Real.log_pos
    nlinarith
  have hlogCompare : (99 / 100 : ℝ) * Real.log y ≤
      Real.log ((9 / 10 : ℝ) * y) := by
    rw [Real.log_mul (by norm_num : (9 / 10 : ℝ) ≠ 0) (ne_of_gt hyPos)]
    nlinarith
  have heLower : (99 / 100 : ℝ) ≤ 1 + e y := by
    have := (abs_le.mp (show |e y| ≤ (1 / 100 : ℝ) by simpa using hey)).1
    linarith
  have heUpper : 1 + e ((9 / 10 : ℝ) * y) ≤ (101 / 100 : ℝ) := by
    have := (abs_le.mp (show |e ((9 / 10 : ℝ) * y)| ≤ (1 / 100 : ℝ) by
      simpa using hecy)).2
    linarith
  have hpiLower : (99 / 100 : ℝ) * (y / Real.log y) ≤
      Nat.primeCounting ⌊y⌋₊ := by
    rw [hpi y]
    simpa [mul_div_assoc] using
      mul_le_mul_of_nonneg_right heLower (div_nonneg hy0 hlogy.le)
  have hpiUpper : (Nat.primeCounting ⌊(9 / 10 : ℝ) * y⌋₊ : ℝ) ≤
      (19 / 20 : ℝ) * (y / Real.log y) := by
    rw [hpi ((9 / 10 : ℝ) * y)]
    apply (div_le_iff₀ hlogcy).2
    calc
      (1 + e ((9 / 10 : ℝ) * y)) * ((9 / 10 : ℝ) * y)
          ≤ (101 / 100 : ℝ) * ((9 / 10 : ℝ) * y) := by
            exact mul_le_mul_of_nonneg_right heUpper hcy0.le
      _ ≤ (19 / 20 : ℝ) * (y / Real.log y) *
          ((99 / 100 : ℝ) * Real.log y) := by
            field_simp
            nlinarith
      _ ≤ (19 / 20 : ℝ) * (y / Real.log y) *
          Real.log ((9 / 10 : ℝ) * y) := by
            gcongr
  rw [reservoirPrimes_card_eq y hy0]
  calc
    y / (100 * Real.log y) ≤
        (99 / 100 : ℝ) * (y / Real.log y) -
          (19 / 20 : ℝ) * (y / Real.log y) := by
      field_simp
      nlinarith
    _ ≤ (Nat.primeCounting ⌊y⌋₊ : ℝ) -
        Nat.primeCounting ⌊(9 / 10 : ℝ) * y⌋₊ := sub_le_sub hpiLower hpiUpper

/-- The five-prime reservoir eventually has at least a fixed multiple of
`(y / log y)^5` elements. -/
theorem eventually_smoothReservoir_card_lower :
    ∀ᶠ y : ℝ in atTop,
      (y / (200 * Real.log y)) ^ 5 / 120 ≤ ((smoothReservoir y).card : ℝ) := by
  have hgrowth : Tendsto (fun y : ℝ ↦ y / (100 * Real.log y)) atTop atTop := by
    have h := (Real.tendsto_exp_div_pow_atTop 1).const_mul_atTop
      (show (0 : ℝ) < 1 / 100 by norm_num)
    refine (h.comp Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [Function.comp_apply, pow_one]
    rw [Real.exp_log hy]
    ring
  filter_upwards [eventually_reservoirPrimes_card_lower,
    eventually_gt_atTop 2,
    hgrowth.eventually_ge_atTop 10]
      with y hband hy hgrowth10
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hbandNonneg : 0 ≤ y / (100 * Real.log y) := by positivity
  have hcardLarge : 10 ≤ (reservoirPrimes y).card := by
    exact_mod_cast hgrowth10.trans hband
  have hhalf : y / (200 * Real.log y) ≤
      (((reservoirPrimes y).card + 1 - 5 : ℕ) : ℝ) := by
    have hhalfCard : y / (200 * Real.log y) ≤ ((reservoirPrimes y).card : ℝ) / 2 := by
      calc
        y / (200 * Real.log y) = (y / (100 * Real.log y)) / 2 := by ring
        _ ≤ ((reservoirPrimes y).card : ℝ) / 2 := by gcongr
    have hfour : 4 ≤ (reservoirPrimes y).card := hcardLarge.trans' (by omega)
    calc
      y / (200 * Real.log y) ≤ ((reservoirPrimes y).card : ℝ) / 2 := hhalfCard
      _ ≤ (((reservoirPrimes y).card + 1 - 5 : ℕ) : ℝ) := by
        rw [show (reservoirPrimes y).card + 1 - 5 =
          (reservoirPrimes y).card - 4 by omega, Nat.cast_sub hfour]
        push_cast
        have hc : (10 : ℝ) ≤ (reservoirPrimes y).card := by exact_mod_cast hcardLarge
        nlinarith
  calc
    (y / (200 * Real.log y)) ^ 5 / 120 ≤
        ((((reservoirPrimes y).card + 1 - 5 : ℕ) : ℝ) ^ 5) /
          ((Nat.factorial 5 : ℕ) : ℝ) := by
      norm_num
      gcongr
    _ ≤ ((smoothReservoir y).card : ℝ) := smoothReservoir_card_lower y

end

end Erdos285

#print axioms Erdos285.eventually_smoothReservoir_card_lower
