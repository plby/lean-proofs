/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Sharp entropy bounds for arbitrary finite prime-exponent profiles.
Informal source: BBMST Lemmas 6.3 and 7.3.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.DivisorEntropyBound

namespace Erdos1189

open Finset

def profileCoordinates (P : Finset ℕ) (γ : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  P.biUnion fun p => (range (γ p)).image (fun e => (p, e))

lemma mem_profileCoordinates {P : Finset ℕ} {γ : ℕ → ℕ} {p e : ℕ} :
    (p, e) ∈ profileCoordinates P γ ↔ p ∈ P ∧ e < γ p := by
  simp [profileCoordinates]

lemma sum_profileCoordinates (P : Finset ℕ) (γ : ℕ → ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ c ∈ profileCoordinates P γ, f c) = ∑ p ∈ P, ∑ e ∈ range (γ p), f (p, e) := by
  rw [profileCoordinates, sum_biUnion]
  · apply sum_congr rfl
    intro p _
    exact sum_image (fun e _ d _ h => (Prod.mk.inj h).2)
  · intro p _ q _ hpq
    apply disjoint_left.mpr
    intro c hc hd
    obtain ⟨e, _, he⟩ := mem_image.mp hc
    obtain ⟨f, _, hf⟩ := mem_image.mp hd
    exact hpq (Prod.mk.inj (he.trans hf.symm)).1

def profileWeight (P : Finset ℕ) (γ : ℕ → ℕ) : ℕ := ∑ p ∈ P, γ p * (p - 1)

noncomputable def profileEntropy (P : Finset ℕ) (γ : ℕ → ℕ) : ℝ :=
  ∑ p ∈ P, Real.log ((γ p : ℝ) + 1)

lemma profileEntropy_nonneg (P : Finset ℕ) (γ : ℕ → ℕ) : 0 ≤ profileEntropy P γ :=
  sum_nonneg fun p _ => Real.log_nonneg (by have := Nat.cast_nonneg (γ p) (α := ℝ); linarith)

lemma profileCoordinates_mass (P : Finset ℕ) (γ : ℕ → ℕ) :
    coordinateMass (profileCoordinates P γ) = profileEntropy P γ := by
  rw [coordinateMass, sum_profileCoordinates]
  exact sum_congr rfl (fun p _ => sum_logIncrement (γ p))

lemma profileCoordinates_weight (P : Finset ℕ) (γ : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    coordinateWeight (profileCoordinates P γ) = profileWeight P γ := by
  rw [coordinateWeight, sum_profileCoordinates, profileWeight, Nat.cast_sum]
  apply sum_congr rfl
  intro p hp
  simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_mul,
    Nat.cast_sub (hP p hp).one_lt.le, Nat.cast_one]

theorem exists_uniform_profileEntropy_bound {b : ℝ} (hb : 2 * Real.sqrt tau < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (γ : ℕ → ℕ), (∀ p ∈ P, p.Prime) →
      profileEntropy P γ ≤
        b * Real.sqrt ((profileWeight P γ : ℝ) / Real.log (profileWeight P γ)) + C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_coordinateMass_bound hb
  refine ⟨C, hC, ?_⟩
  intro P γ hP
  have hprime : ∀ c ∈ profileCoordinates P γ, c.1.Prime :=
    fun c hc => hP c.1 (mem_profileCoordinates.mp hc).1
  have h := hbound (profileWeight P γ) (profileCoordinates P γ) hprime
    (profileCoordinates_weight P γ hP).le
  simpa only [profileCoordinates_mass] using h

lemma exponent_le_profileWeight {P : Finset ℕ} {γ : ℕ → ℕ}
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ P) : γ p ≤ profileWeight P γ := by
  have hterm : γ p * (p - 1) ≤ profileWeight P γ :=
    single_le_sum (f := fun p => γ p * (p - 1)) (fun _ _ => Nat.zero_le _) hp
  have hprime := (hP p hp).two_le
  exact (Nat.le_mul_of_pos_right _ (by omega)).trans hterm

lemma profileEntropy_small_primes (P : Finset ℕ) (γ : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (T : ℕ) :
    profileEntropy (P.filter (fun p => p ≤ T)) γ ≤
      (T : ℝ) * Real.log ((profileWeight P γ : ℝ) + 1) := by
  have hcard : (P.filter (fun p => p ≤ T)).card ≤ T := by
    have hsub : P.filter (fun p => p ≤ T) ⊆ Ioc 0 T := by
      intro p hp
      obtain ⟨hpP, hpT⟩ := mem_filter.mp hp
      exact mem_Ioc.mpr ⟨(hP p hpP).pos, hpT⟩
    simpa only [Nat.card_Ioc, Nat.sub_zero] using card_le_card hsub
  calc
    _ ≤ ∑ _p ∈ P.filter (fun p => p ≤ T), Real.log ((profileWeight P γ : ℝ) + 1) := by
      apply sum_le_sum
      intro p hp
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.add_le_add_right (exponent_le_profileWeight hP (mem_filter.mp hp).1) 1
    _ = (P.filter (fun p => p ≤ T)).card * Real.log ((profileWeight P γ : ℝ) + 1) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Real.log_nonneg (by have := Nat.cast_nonneg (profileWeight P γ) (α := ℝ); linarith))

theorem exists_profileEntropy_large_prime_bound {b : ℝ} (hb : 2 * Real.sqrt tau < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (γ : ℕ → ℕ) (T : ℕ),
      (∀ p ∈ P, p.Prime) →
      profileEntropy P γ ≤
        b * Real.sqrt ((profileWeight (P.filter (fun p => T < p)) γ : ℝ) /
          Real.log (profileWeight (P.filter (fun p => T < p)) γ)) + C +
            T * Real.log ((profileWeight P γ : ℝ) + 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_profileEntropy_bound hb
  refine ⟨C, hC, ?_⟩
  intro P γ T hP
  have hlarge := hbound (P.filter (fun p => T < p)) γ (fun p hp => hP p (mem_filter.mp hp).1)
  have hsmall := profileEntropy_small_primes P γ hP T
  have hsplit := sum_filter_add_sum_filter_not P (fun p => T < p)
    (fun p => Real.log ((γ p : ℝ) + 1))
  simp only [not_lt] at hsplit
  change profileEntropy (P.filter (fun p => T < p)) γ +
    profileEntropy (P.filter (fun p => p ≤ T)) γ = profileEntropy P γ at hsplit
  linarith

end Erdos1189
