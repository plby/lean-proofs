import ErdosProblems.Erdos239.External.Erdos67.MRTDensity
import ErdosProblems.Erdos239.External.Erdos67.MRIntervalSieve
import ErdosProblems.Erdos851.ConcreteBetaCardinality

/-!
# A beta sieve on arbitrary integer intervals

The concrete beta sieve used by `MRTDensity` is packaged on `[1,X]` (or,
equivalently, on a translated dyadic interval).  The finite Halasz argument
also needs the same dimension-one estimate on an arbitrary interval
`(L,U]`.  This file changes only the interval model: the Rosser main-term
estimate is reused verbatim, while exact floor counting gives remainder at
most one for every sieve divisor.  Consequently the final level remainder
is still exactly `(Q^S)^2`.
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction

namespace Erdos67.MRIntervalBetaSieve

noncomputable section

open Erdos851
open Erdos851.FiniteCombinatorialSieve
open Erdos851.FiniteSieveApplication
open Erdos851.ShiftSieve
open Erdos67.MRIntervalSieve
open Erdos69.HalaszMean

/-- Integers in `(L,U]` having no prime divisor in the closed block `I`. -/
def intervalMissingPrimeBlockSet (I : ℕ × ℕ) (L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter fun n ↦ ∀ p ∈ primesInBlock I, ¬p ∣ n

theorem mem_intervalMissingPrimeBlockSet {I : ℕ × ℕ} {L U n : ℕ} :
    n ∈ intervalMissingPrimeBlockSet I L U ↔
      L < n ∧ n ≤ U ∧ ∀ p ∈ primesInBlock I, ¬p ∣ n := by
  simp [intervalMissingPrimeBlockSet, and_assoc]

/-- The dimension-one `BoundingSieve` on an arbitrary interval `(L,U]`.
The local density is the singleton-shift density `1/p`. -/
noncomputable def intervalOneShiftBoundingSieve
    (L U z Y : ℕ) : BoundingSieve :=
  { support := Finset.Ioc L U
    prodPrimes := Erdos387.sievePrimeProduct z Y
    prodPrimes_squarefree := Erdos387.sievePrimeProduct_squarefree z Y
    weights := fun _ ↦ 1
    weights_nonneg := fun _ ↦ zero_le_one
    totalMass := (U - L : ℕ)
    nu := shiftNu {0}
    nu_mult := shiftNu_mult {0}
    nu_pos_of_prime := by
      intro p hp _
      rw [shiftNu_singleton_prime 0 hp]
      exact oneShiftDensity_pos hp
    nu_lt_one_of_prime := by
      intro p hp _
      rw [shiftNu_singleton_prime 0 hp]
      exact oneShiftDensity_lt_one hp }

@[simp] theorem intervalOneShiftBoundingSieve_totalMass
    {L U z Y : ℕ} :
    (intervalOneShiftBoundingSieve L U z Y).totalMass = (U - L : ℕ) := by
  simp [intervalOneShiftBoundingSieve]

/-- The multiple sum is the literal count of multiples in `(L,U]`. -/
theorem intervalOneShiftBoundingSieve_multSum
    {L U z Y d : ℕ} :
    (intervalOneShiftBoundingSieve L U z Y).multSum d =
      (((Finset.Ioc L U).filter fun n ↦ d ∣ n).card : ℝ) := by
  rw [BoundingSieve.multSum]
  simp [intervalOneShiftBoundingSieve]

/-- The sifted sum is the cardinality of the interval points coprime to the
whole sieve-prime product. -/
theorem intervalOneShiftBoundingSieve_siftedSum
    {L U z Y : ℕ} :
    (intervalOneShiftBoundingSieve L U z Y).siftedSum =
      (((Finset.Ioc L U).filter fun n ↦
        Nat.Coprime (Erdos387.sievePrimeProduct z Y) n).card : ℝ) := by
  rw [BoundingSieve.siftedSum]
  change (∑ n ∈ Finset.Ioc L U,
      if Nat.Coprime (Erdos387.sievePrimeProduct z Y) n then 1 else 0) = _
  simp_rw [← Finset.sum_filter]
  simp

/-- Exact one-dimensional remainder bound on an arbitrary interval.  This
is stronger than the `|rem d| <= d` hypothesis used by the finite beta
sieve. -/
theorem intervalOneShiftBoundingSieve_abs_rem_le_one
    {L U z Y d : ℕ} (hLU : L ≤ U)
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    |(intervalOneShiftBoundingSieve L U z Y).rem d| ≤ 1 := by
  have hdpos : 0 < d := Erdos387.pos_of_dvd_sievePrimeProduct hd
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (Erdos387.sievePrimeProduct_squarefree z Y)
  have hcountLower := cast_div_interval_lower hLU d hdpos
  have hcountUpper := cast_div_interval_upper hLU d hdpos
  rw [BoundingSieve.rem, intervalOneShiftBoundingSieve_multSum,
    intervalOneShiftBoundingSieve_totalMass]
  change |((((Finset.Ioc L U).filter fun n ↦ d ∣ n).card : ℕ) : ℝ) -
      shiftNu {0} d * ((U - L : ℕ) : ℝ)| ≤ 1
  rw [shiftNu_squarefree hsq]
  have hnu : nuClasses {0} d = 1 := by
    simp [nuClasses, localNu_singleton]
  rw [hnu]
  have hcard :
      (((((Finset.Ioc L U).filter fun n ↦ d ∣ n).card : ℕ) : ℝ)) =
        ((U / d : ℕ) : ℝ) - ((L / d : ℕ) : ℝ) := by
    calc
      (((((Finset.Ioc L U).filter fun n ↦ d ∣ n).card : ℕ) : ℝ)) =
          ∑ n ∈ (Finset.Ioc L U).filter (fun n ↦ d ∣ n), (1 : ℝ) := by simp
      _ = ∑ n ∈ Finset.Ioc L U, dvdIndicator d n := by
        simp [dvdIndicator]
      _ = ((U / d : ℕ) : ℝ) - ((L / d : ℕ) : ℝ) :=
        sum_dvdIndicator_Ioc_interval hLU d
  have hfrac :
      ((1 : ℝ) / (d : ℝ)) * ((U - L : ℕ) : ℝ) =
        ((U - L : ℕ) : ℝ) / (d : ℝ) := by ring
  rw [hcard, Nat.cast_one, hfrac, abs_le]
  constructor <;> nlinarith

/-- The exact remainder hypothesis expected by the abstract beta sieve. -/
theorem intervalOneShiftBoundingSieve_abs_rem_le
    {L U z Y d : ℕ} (hLU : L ≤ U)
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    |(intervalOneShiftBoundingSieve L U z Y).rem d| ≤ d := by
  exact (intervalOneShiftBoundingSieve_abs_rem_le_one hLU hd).trans
    (by exact_mod_cast Erdos387.pos_of_dvd_sievePrimeProduct hd)

/-- The abstract Rosser upper sieve, specialized to the arbitrary interval
model.  The square-level remainder is unchanged from the dyadic model. -/
theorem intervalOneShiftBoundingSieve_siftedSum_le_upperMain_add_sq
    {L U z y S : ℕ} (hLU : L ≤ U) (hz : 2 ≤ z) (hzy : z ≤ y)
    (_hS : 1 ≤ S) :
    let P := ascendingSievePrimes z y
    let D := y ^ S
    let stop := rosserStoppingPredicate 100 D
    (intervalOneShiftBoundingSieve L U z (y + 1)).siftedSum ≤
      ((U - L : ℕ) : ℝ) * upperMainTerm stop oneShiftDensity P +
        (D : ℝ) ^ 2 := by
  classical
  dsimp only
  let P := ascendingSievePrimes z y
  let D := y ^ S
  let stop := rosserStoppingPredicate 100 D
  let sieve := intervalOneShiftBoundingSieve L U z (y + 1)
  have hprod : P.prod = sieve.prodPrimes := by
    change P.prod = Erdos387.sievePrimeProduct z (y + 1)
    exact ascendingSievePrimes_prod z y
  have hsort : P.Pairwise (· ≤ ·) := ascendingSievePrimes_pairwise z y
  have hnodup : P.Nodup := ascendingSievePrimes_nodup z y
  have hprime : ∀ p ∈ P, p.Prime := ascendingSievePrimes_prime
  have hD : 1 ≤ D := by
    dsimp only [D]
    exact one_le_pow₀ (by omega)
  have hrem : ∀ d : ℕ, d ∣ sieve.prodPrimes → d ≤ D →
      |sieve.rem d| ≤ (d : ℝ) := by
    intro d hd _
    exact intervalOneShiftBoundingSieve_abs_rem_le hLU hd
  have hupper := boundingSieve_siftedSum_le_upperMain_add_sq
    sieve P stop D hprod hsort hnodup hprime
    (by
      intro t ht hadm
      apply prod_le_of_upperAdmissible_rosserStoppingPredicate
        (by norm_num : 1 ≤ 100) hD
        (hsort.sublist (List.mem_sublists.mp ht))
        (by
          intro p hp
          exact (hprime p ((List.mem_sublists.mp ht).subset hp)).one_le)
        hadm)
    hrem
  have hnu : ∀ p ∈ P, sieve.nu p = oneShiftDensity p := by
    intro p hp
    change shiftNu {0} p = oneShiftDensity p
    exact shiftNu_singleton_prime 0 (hprime p hp)
  rw [upperMainTerm_congr_on stop (fun p ↦ sieve.nu p)
    oneShiftDensity P hnu] at hupper
  change sieve.siftedSum ≤
    sieve.totalMass * upperMainTerm stop oneShiftDensity P + (D : ℝ) ^ 2
      at hupper
  simpa only [sieve, intervalOneShiftBoundingSieve_totalMass] using hupper

/-- Avoiding the closed prime block on `(L,U]` is exactly coprimality with
its squarefree prime product. -/
theorem intervalMissingPrimeBlockSet_eq_filter_coprime
    (I : ℕ × ℕ) (L U : ℕ) :
    intervalMissingPrimeBlockSet I L U =
      (Finset.Ioc L U).filter fun n ↦ (primeBlockProduct I).Coprime n := by
  classical
  ext n
  simp only [mem_intervalMissingPrimeBlockSet, Finset.mem_filter,
    Finset.mem_Ioc]
  rw [← not_hasPrimeFactorInBlock_iff_coprime_primeBlockProduct]
  simp only [HasPrimeFactorInBlock, not_exists, not_and, and_assoc]

/-- The concrete dimension-one beta sieve on an arbitrary interval.
The main term is the length of `(L,U]` times the closed-block Euler density,
and the only finite remainder is the standard square level `(Q^S)^2`. -/
theorem exists_card_intervalMissingPrimeBlockSet_beta_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ L U P Q S : ℕ, L ≤ U → 3 ≤ P → P ≤ Q → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((intervalMissingPrimeBlockSet (P, Q) L U).card : ℝ) ≤
          ((U - L : ℕ) : ℝ) *
              ((1 + eta) * primeBlockDensity (P, Q)) +
            ((Q ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hmain⟩ :=
    Erdos851.BetaSieveFundamental.exists_oneShift_concrete_finiteMainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro L U P Q S hLU hP hPQ hS hlog
  dsimp only
  let primes := ascendingSievePrimes (P - 1) Q
  let D := Q ^ S
  let stop := rosserStoppingPredicate 100 D
  have hm := hmain (P - 1) Q S (by omega) (by omega) (by omega)
    hS hlog
  dsimp only at hm
  have hb := intervalOneShiftBoundingSieve_siftedSum_le_upperMain_add_sq
    (L := L) (U := U) (z := P - 1) (y := Q) (S := S)
    hLU (by omega) (by omega) (by omega)
  dsimp only at hb
  have hsift :
      (intervalOneShiftBoundingSieve L U (P - 1) (Q + 1)).siftedSum =
        ((intervalMissingPrimeBlockSet (P, Q) L U).card : ℝ) := by
    rw [intervalOneShiftBoundingSieve_siftedSum,
      sievePrimeProduct_pred_succ_eq_primeBlockProduct (by omega),
      intervalMissingPrimeBlockSet_eq_filter_coprime]
  rw [hsift] at hb
  change
    ((intervalMissingPrimeBlockSet (P, Q) L U).card : ℝ) ≤
      ((U - L : ℕ) : ℝ) *
          upperMainTerm stop oneShiftDensity primes + (D : ℝ) ^ 2 at hb
  have hmUpper := hm.2
  change
    upperMainTerm stop oneShiftDensity primes ≤
      (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
        localEulerProduct oneShiftDensity (P - 1) Q at hmUpper
  calc
    ((intervalMissingPrimeBlockSet (P, Q) L U).card : ℝ) ≤
        ((U - L : ℕ) : ℝ) *
            upperMainTerm stop oneShiftDensity primes + (D : ℝ) ^ 2 := hb
    _ ≤ ((U - L : ℕ) : ℝ) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            localEulerProduct oneShiftDensity (P - 1) Q) +
          (D : ℝ) ^ 2 := by
      gcongr
    _ = ((U - L : ℕ) : ℝ) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            primeBlockDensity (P, Q)) +
          ((Q ^ S : ℕ) : ℝ) ^ 2 := by
      rw [oneShift_localEulerProduct_pred_eq_primeBlockDensity (by omega)]

/-- Direct coprimality-filter form consumed by the finite Halasz estimates. -/
theorem exists_card_Ioc_filter_coprime_primeBlockProduct_beta_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ L U P Q S : ℕ, L ≤ U → 3 ≤ P → P ≤ Q → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (((Finset.Ioc L U).filter fun n ↦
            (primeBlockProduct (P, Q)).Coprime n).card : ℝ) ≤
          ((U - L : ℕ) : ℝ) *
              ((1 + eta) * primeBlockDensity (P, Q)) +
            ((Q ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hbeta⟩ :=
    exists_card_intervalMissingPrimeBlockSet_beta_bound
  refine ⟨A, hA, ?_⟩
  intro L U P Q S hLU hP hPQ hS hlog
  dsimp only
  have h := hbeta L U P Q S hLU hP hPQ hS hlog
  rwa [intervalMissingPrimeBlockSet_eq_filter_coprime] at h

end

end Erdos67.MRIntervalBetaSieve
