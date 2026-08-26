/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.GILDivisorBounds

/-! # Divisibility and multiplication of full reciprocal prime mass -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem primeDivisorReciprocalMass_mono {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) :
    primeDivisorReciprocalMass a ≤ primeDivisorReciprocalMass b :=
  Finset.sum_le_sum_of_subset_of_nonneg (Nat.primeFactors_mono hab hb)
    (fun p hp hnot ↦ by positivity)

theorem primeDivisorReciprocalMass_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    primeDivisorReciprocalMass (a * b) ≤ primeDivisorReciprocalMass a + primeDivisorReciprocalMass b := by
  unfold primeDivisorReciprocalMass
  rw [Nat.primeFactors_mul ha hb]
  have hsum := Finset.sum_union_inter (s₁ := a.primeFactors) (s₂ := b.primeFactors)
    (f := fun p : ℕ ↦ (1 : ℝ) / p)
  have hnonneg : 0 ≤ ∑ p ∈ a.primeFactors ∩ b.primeFactors, (1 : ℝ) / p :=
    Finset.sum_nonneg fun p hp ↦ by positivity
  linarith only [hsum, hnonneg]

theorem primeDivisorReciprocalMass_prime_le_one {p : ℕ} (hp : p.Prime) :
    primeDivisorReciprocalMass p ≤ 1 := by
  simp only [primeDivisorReciprocalMass, hp.primeFactors, Finset.sum_singleton]
  exact (div_le_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_le)

theorem primeDivisorReciprocalMass_prime_mul_le {p d : ℕ} (hp : p.Prime) (hd : d ≠ 0) :
    primeDivisorReciprocalMass (p * d) ≤ primeDivisorReciprocalMass d + 1 := by
  calc
    _ ≤ primeDivisorReciprocalMass p + primeDivisorReciprocalMass d :=
      primeDivisorReciprocalMass_mul_le hp.ne_zero hd
    _ ≤ 1 + primeDivisorReciprocalMass d := add_le_add (primeDivisorReciprocalMass_prime_le_one hp) le_rfl
    _ = _ := by ring

theorem eventually_gilCofactors_divisor_primeMass_le {S : ℕ} (hS : 0 < S) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ gilCofactors N S C, ∀ d : ℕ,
      d ∣ shiftedTotient m → primeDivisorReciprocalMass d ≤ C + 2 := by
  filter_upwards [eventually_gilCofactors_full_primeMass_le hS C] with N hN
  intro m hm d hd
  have hmpos := oddRawCofactors_pos (gilCofactors_subset_oddRaw N S C hm)
  have hsne : shiftedTotient m ≠ 0 := by dsimp [shiftedTotient]; omega
  exact (primeDivisorReciprocalMass_mono hsne hd).trans (hN m hm)

#print axioms eventually_gilCofactors_divisor_primeMass_le

end Erdos822
