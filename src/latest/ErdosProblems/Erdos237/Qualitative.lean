import ErdosProblems.Erdos237.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import BoundedGaps.Maynard.AsymptoticPositivity

/-!
# A qualitative route to Erdős 237

This file does not import `ErdosProblems.Axioms`. It proves the elementary
reduction to a qualitative prime-tuple statement, with that statement an
explicit hypothesis, not an axiom. `Unconditional.lean` proves that hypothesis.

Pigeonholing modulo `k!` replaces the quantitative Mertens sieve. The
analytic input only asks for one translate containing enough primes, for
admissible tuples of one suitable cardinality for each requested count.
-/

namespace Erdos237

open Finset

/-- A finite set with at least `k! * k` elements contains `k` elements in a
single residue class modulo `k!`. -/
theorem exists_card_eq_same_residue (S : Finset ℕ) (k : ℕ)
    (hS : k.factorial * k ≤ S.card) :
    ∃ B : Finset ℕ, B ⊆ S ∧ B.card = k ∧
      ∃ r : ℕ, ∀ a ∈ B, a % k.factorial = r := by
  obtain ⟨r, _, hr⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := S) (t := range k.factorial) (f := fun a => a % k.factorial)
    (n := k) (fun a _ => mem_range.mpr (Nat.mod_lt a (Nat.factorial_pos k)))
    (nonempty_range_iff.mpr (Nat.factorial_ne_zero k)) (by simpa using hS)
  obtain ⟨B, hB, hcard⟩ := exists_subset_card_eq hr
  exact ⟨B, hB.trans (filter_subset _ _), hcard, r,
    fun a ha => (mem_filter.mp (hB ha)).2⟩

/-- Reflect a finite set in its largest element, so prime shifts become
representations by subtraction. -/
def reflected (B : Finset ℕ) : Finset ℕ :=
  B.image (fun a => B.sup id - a)

theorem reflected_card (B : Finset ℕ) : (reflected B).card = B.card := by
  apply card_image_of_injOn
  intro a ha b hb hab
  have ha' : a ≤ B.sup id := le_sup (f := id) ha
  have hb' : b ≤ B.sup id := le_sup (f := id) hb
  dsimp only at hab
  omega

/-- A tuple in one residue class modulo `k!`, after reflection, is admissible.
Small primes see just one residue; larger primes exceed the tuple's size. -/
theorem reflected_isAdmissible (B : Finset ℕ) (k : ℕ) (hcard : B.card = k)
    (r : ℕ) (hr : ∀ a ∈ B, a % k.factorial = r) :
    BoundedGaps.IsAdmissible (reflected B) := by
  intro p hp
  by_cases hpk : p ≤ k
  · have hdvd : p ∣ k.factorial := Nat.dvd_factorial hp.pos hpk
    have hconstant : ∀ h ∈ reflected B, h % p = (B.sup id - r) % p := by
      intro h hh
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hh
      have ha' : a ≤ B.sup id := le_sup (f := id) ha
      have har : a % k.factorial = r := hr a ha
      have hra : r ≤ a := har ▸ Nat.mod_le _ _
      have hmod : Nat.ModEq p a r := Nat.ModEq.of_dvd hdvd (by
        change a % k.factorial = r % k.factorial
        rw [har, Nat.mod_eq_of_lt (har ▸ Nat.mod_lt a (Nat.factorial_pos k))])
      exact Nat.ModEq.sub_left ha' (hra.trans ha') hmod
    have hsub : (reflected B).image (fun h => h % p) ⊆ {(B.sup id - r) % p} := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := mem_image.mp hx
      simpa using hconstant h hh
    exact (card_le_card hsub).trans_lt (by simpa using hp.one_lt)
  · exact card_image_le.trans_lt (by rw [reflected_card, hcard]; omega)

/-- Reflecting a prime shift produces a representation of `n + max B`. -/
theorem primeShiftCount_reflected (B : Finset ℕ) (n : ℕ) :
    BoundedGaps.primeShiftCount (reflected B) n =
      repCount (B : Set ℕ) (n + B.sup id) := by
  have hrc : repCount (B : Set ℕ) (n + B.sup id) =
      (B.filter (fun a => (n + (B.sup id - a)).Prime)).card := by
    simp only [repCount, ← Set.ncard_coe_finset]
    congr 1
    ext a
    simp only [Set.mem_ofPred_eq, mem_coe, mem_filter]
    constructor
    · rintro ⟨ha, _, hp⟩
      have ha' : a ≤ B.sup id := le_sup (f := id) ha
      exact ⟨ha, by simpa [Nat.add_sub_assoc ha'] using hp⟩
    · rintro ⟨ha, hp⟩
      have ha' : a ≤ B.sup id := le_sup (f := id) ha
      exact ⟨ha, by omega, by simpa [Nat.add_sub_assoc ha'] using hp⟩
  rw [hrc]
  unfold BoundedGaps.primeShiftCount reflected
  rw [filter_image]
  apply card_image_of_injOn
  intro a ha b hb hab
  have ha' : a ≤ B.sup id := le_sup (f := id) (mem_filter.mp ha).1
  have hb' : b ≤ B.sup id := le_sup (f := id) (mem_filter.mp hb).1
  dsimp only at hab
  omega

/-- The only prime-distribution input needed by the qualitative route.
No quantitative threshold and no infinitely-many-translates conclusion are
required. This is a proposition to prove, not an additional axiom. -/
def QualitativePrimeTuples : Prop :=
  ∀ m : ℕ, ∃ k : ℕ, ∀ H : Finset ℕ, H.card = k →
    BoundedGaps.IsAdmissible H → ∃ n : ℕ, m ≤ BoundedGaps.primeShiftCount H n

/-- The qualitative prime-tuple theorem implies the finite Chen–Ding
conclusion, with the elementary threshold `k! * k`. -/
theorem chen_ding_of_qualitative (hprime : QualitativePrimeTuples) (m : ℕ) :
    ∃ ℓ₀ : ℕ, ∀ S : Finset ℕ, ℓ₀ ≤ S.card →
      ∃ n : ℕ, m ≤ repCount (S : Set ℕ) n := by
  obtain ⟨k, hk⟩ := hprime m
  refine ⟨k.factorial * k, fun S hS => ?_⟩
  obtain ⟨B, hBS, hcard, r, hr⟩ := exists_card_eq_same_residue S k hS
  obtain ⟨n, hn⟩ := hk (reflected B) ((reflected_card B).trans hcard)
    (reflected_isAdmissible B k hcard r hr)
  refine ⟨n + B.sup id, ?_⟩
  rw [primeShiftCount_reflected] at hn
  exact hn.trans (repCount_mono (by exact_mod_cast hBS) _)

/-- Reduction of the exact final statement to the qualitative prime-tuple theorem. -/
theorem erdos_237_of_qualitative (hprime : QualitativePrimeTuples)
    (A : Set ℕ) (hA : A.Infinite) :
    ∀ C : ℕ, ∃ n : ℕ, C < repCount A n := by
  intro C
  obtain ⟨ℓ₀, hℓ₀⟩ := chen_ding_of_qualitative hprime (C + 1)
  obtain ⟨S, hSA, hcard⟩ := hA.exists_subset_card_eq ℓ₀
  obtain ⟨n, hn⟩ := hℓ₀ S hcard.ge
  exact ⟨n, (Nat.lt_of_succ_le hn).trans_le (repCount_mono hSA n)⟩

end Erdos237
