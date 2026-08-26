import ErdosProblems.Erdos4.CutoffSimplex
import ErdosProblems.Erdos4.CoefficientMass
import ErdosProblems.Erdos4.WeightedHarmonic
import Mathlib.NumberTheory.Primorial

/-!
# Squarefree arithmetic inside ideal projection fibers

Completing the anchor coordinate by a squarefree integer gives an
injective family of compatible labels. Its coordinate divisor is that
integer, and its fiber weight is its reciprocal totient. Only primes
already frozen in another coordinate have to be excluded.
-/

open scoped BigOperators

namespace Erdos4.ArithmeticFibers

open DivisorCoefficients IdealProjection IdealAction CutoffSimplex

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

theorem freeze_ne_anchor (j : Fin k) (a : Option (Fin k)) :
    freeze j a ≠ some j := by
  unfold freeze
  split_ifs with h
  · simp
  · exact h

theorem freeze_idempotent (j : Fin k) (a : Option (Fin k)) :
    freeze j (freeze j a) = freeze j a := by
  unfold freeze
  split_ifs <;> simp_all

def completion (ell : P → ℕ) (j : Fin k) (a : P → Option (Fin k))
    (u : ℕ) : P → Option (Fin k) :=
  fun p => if ell p ∣ u then some j else freeze j (a p)

def AvoidsFrozen (ell : P → ℕ) (j : Fin k) (a : P → Option (Fin k))
    (u : ℕ) : Prop := ∀ p, ell p ∣ u → freeze j (a p) = none

theorem compatible_completion (ell : P → ℕ) (j : Fin k)
    (a : P → Option (Fin k)) {u : ℕ} (hu : AvoidsFrozen ell j a u) :
    Compatible j a (completion ell j a u) := by
  intro p
  by_cases hp : ell p ∣ u
  · rw [hu p hp]
    simp [completion, hp, freeze]
  · simp only [completion, if_neg hp, freeze_idempotent]

omit [DecidableEq P] in
theorem prod_dividing_eq_primeFactors {M : Type*} [CommMonoid M]
    (ell : P → ℕ) (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {u : ℕ} (hu : u ≠ 0) (hcover : ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (f : ℕ → M) :
    (∏ p, if ell p ∣ u then f (ell p) else 1) = ∏ q ∈ u.primeFactors, f q := by
  classical
  rw [← Finset.prod_filter]
  apply Finset.prod_bij (fun p _ => ell p)
  · intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p, (Finset.mem_filter.mp hp).2, hu⟩
  · intro p hp q hq hpq
    exact hinj hpq
  · intro q hq
    obtain ⟨p, hp⟩ := hcover q hq
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hp⟩
    rw [hp]
    exact Nat.dvd_of_mem_primeFactors hq
  · intro p hp
    rfl

theorem coordinateDivisor_completion (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (j : Fin k) (a : P → Option (Fin k)) {u : ℕ} (hu : Squarefree u)
    (hcover : ∀ q ∈ u.primeFactors, ∃ p, ell p = q) :
    coordinateDivisor ell (completion ell j a u) j = u := by
  calc
    coordinateDivisor ell (completion ell j a u) j =
        ∏ p, if ell p ∣ u then ell p else 1 := by
      apply Finset.prod_congr rfl
      intro p _hp
      by_cases hp : ell p ∣ u
      · simp [completion, hp]
      · simp [completion, hp, freeze_ne_anchor]
    _ = ∏ q ∈ u.primeFactors, q :=
      prod_dividing_eq_primeFactors ell hprime hinj hu.ne_zero hcover id
    _ = u := Nat.prod_primeFactors_of_squarefree hu

theorem cofactor_eq_of_compatible (ell : P → ℕ) (j : Fin k)
    (a b : P → Option (Fin k)) (hab : Compatible j a b) :
    cofactor ell j a = cofactor ell j b := by
  unfold cofactor totalDivisor
  apply Finset.prod_congr rfl
  intro p _hp
  change (if freeze j (a p) = none then 1 else ell p) =
    (if freeze j (b p) = none then 1 else ell p)
  rw [hab p]

theorem totalDivisor_completion (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (j : Fin k) (a : P → Option (Fin k)) {u : ℕ} (hu : Squarefree u)
    (hcover : ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (havoid : AvoidsFrozen ell j a u) :
    totalDivisor ell (completion ell j a u) = cofactor ell j a * u := by
  rw [← cofactor_mul_coordinateDivisor ell j,
    coordinateDivisor_completion ell hprime hinj j a hu hcover,
    ← cofactor_eq_of_compatible ell j a _ (compatible_completion ell j a havoid)]

theorem totient_eq_prod_of_squarefree {u : ℕ} (hu : Squarefree u) :
    Nat.totient u = ∏ p ∈ u.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hu,
    Nat.div_self hu.ne_zero.bot_lt, one_mul]

theorem fiberWeight_completion (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    (j : Fin k) (a : P → Option (Fin k)) {u : ℕ} (hu : Squarefree u)
    (hcover : ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (havoid : AvoidsFrozen ell j a u) :
    fiberWeight ell j a (completion ell j a u) = 1 / (Nat.totient u : ℝ) := by
  calc
    fiberWeight ell j a (completion ell j a u) =
        ∏ p, if ell p ∣ u then ((ell p : ℝ) - 1)⁻¹ else 1 := by
      apply Finset.prod_congr rfl
      intro p _hp
      by_cases hp : ell p ∣ u
      · simp only [completion, if_pos hp, havoid p hp]
        exact CoefficientMass.localWeight_some_sq (hprime p).one_le j
      · by_cases ha : freeze j (a p) = none
        · simp [completion, hp, ha, localWeight]
        · simp only [if_neg ha, if_neg hp]
    _ = ∏ p ∈ u.primeFactors, ((p : ℝ) - 1)⁻¹ :=
      prod_dividing_eq_primeFactors ell hprime hinj hu.ne_zero hcover
        (fun p => ((p : ℝ) - 1)⁻¹)
    _ = (∏ p ∈ u.primeFactors, ((p : ℝ) - 1))⁻¹ := Finset.prod_inv_distrib _
    _ = 1 / (Nat.totient u : ℝ) := by
      rw [one_div, totient_eq_prod_of_squarefree hu, Nat.cast_prod]
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
      norm_num

def primeWindow (K R : ℕ) : Finset ℕ := R.primesLE.filter (fun p => K < p)

theorem mem_primeWindow {K R p : ℕ} :
    p ∈ primeWindow K R ↔ p.Prime ∧ K < p ∧ p ≤ R := by
  simp only [primeWindow, Finset.mem_filter, Nat.mem_primesLE]
  tauto

theorem primeFactors_covered {K R u : ℕ} (huR : u ≤ R)
    (huW : u.Coprime (primorial K)) :
    ∀ q ∈ u.primeFactors, ∃ p : primeWindow K R, (p : ℕ) = q := by
  intro q hq
  have hprime := Nat.prime_of_mem_primeFactors hq
  have hqW : ¬q ∣ primorial K :=
    hprime.coprime_iff_not_dvd.mp (huW.of_dvd_left (Nat.dvd_of_mem_primeFactors hq))
  have hK : K < q := by
    by_contra h
    exact hqW (hprime.dvd_primorial_iff.mpr (by omega))
  exact ⟨⟨q, mem_primeWindow.mpr ⟨hprime, hK, (Nat.le_of_mem_primeFactors hq).trans huR⟩⟩, rfl⟩

end Erdos4.ArithmeticFibers
