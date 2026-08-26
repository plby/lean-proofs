/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite modulus sets with bounded prime-exponent profiles and their exact counts.
Informal source: BBMST Lemma 7.1.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameDivisorProfiles
import ErdosProblems.Erdos1189.ProfilePerturbation
import ErdosProblems.Erdos1189.PrimeProfiles

namespace Erdos1189

open Finset

noncomputable def boundedProfileModuli (N : ℕ) (γ : ℕ → ℕ) : Finset ℕ :=
  univ.image (fun e : (p : N.primeFactors) → Fin (γ p + 1) =>
    primePowerProfile N (fun p => (e p).val))

lemma boundedProfileModuli_card (N : ℕ) (γ : ℕ → ℕ) :
    (boundedProfileModuli N γ).card = ∏ p ∈ N.primeFactors, (γ p + 1) := by
  classical
  have hinj : Function.Injective (fun e : (p : N.primeFactors) → Fin (γ p + 1) =>
      primePowerProfile N (fun p => (e p).val)) := by
    intro e f hef
    have h := primePowerProfile_injective N hef
    funext p
    exact Fin.ext (congrFun h p)
  rw [boundedProfileModuli, card_image_of_injective _ hinj, card_univ, Fintype.card_pi]
  simp only [Fintype.card_fin]
  exact prod_coe_sort N.primeFactors (fun p => γ p + 1)

lemma boundedProfileModuli_card_pos (N : ℕ) (γ : ℕ → ℕ) :
    0 < (boundedProfileModuli N γ).card := by
  rw [boundedProfileModuli_card]
  exact prod_pos fun _ _ => Nat.succ_pos _

lemma log_boundedProfileModuli_card (N : ℕ) (γ : ℕ → ℕ) :
    Real.log (boundedProfileModuli N γ).card = profileEntropy N.primeFactors γ := by
  rw [boundedProfileModuli_card, Nat.cast_prod, Real.log_prod (fun _ _ => by positivity)]
  simp only [Nat.cast_add, Nat.cast_one, profileEntropy]

lemma mem_boundedProfileModuli {N d : ℕ} {γ : ℕ → ℕ} (hN : N ≠ 0) (hd : d ∣ N)
    (hγ : ∀ p : N.primeFactors, d.factorization p ≤ γ p) :
    d ∈ boundedProfileModuli N γ := by
  classical
  refine mem_image.mpr ⟨fun p => ⟨d.factorization p, Nat.lt_succ_of_le (hγ p)⟩, mem_univ _, ?_⟩
  exact primePowerProfile_of_divisor hN hd

noncomputable def frameAllowedModuli {N : ℕ} (rank : PrimeCoordinate N → ℕ)
    (i : PrimeCoordinate N) (T : ℕ) : Finset ℕ :=
  boundedProfileModuli N (frameExponentBound rank i T)

lemma log_frameAllowedModuli_card {N : ℕ} (rank : PrimeCoordinate N → ℕ)
    (i : PrimeCoordinate N) (T : ℕ) :
    Real.log (frameAllowedModuli rank i T).card ≤
      profileEntropy N.primeFactors (fibreExponent (rankPrefix rank i)) + Real.log 2 +
        T * Real.log ((T : ℝ) + 1) := by
  rw [frameAllowedModuli, log_boundedProfileModuli_card]
  exact profileEntropy_frame_increment N.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
      (fibreExponent (rankPrefix rank i)) i.1.property T

lemma frame_family_subset_allowed {N : ℕ} {D : Finset ℕ} {residue : ℕ → ℕ} {δ : ℝ}
    (frame : Grid.GeneralizedFrame (fun d => congruenceBox N d (residue d)) D δ)
    (hδ : 0 < δ) (hN : N ≠ 0) (hD : ∀ d ∈ D, d ∣ N) {T : ℕ}
    (hT : 1 / δ ≤ (T : ℝ)) (i : PrimeCoordinate N) :
    frame.families i ⊆ frameAllowedModuli frame.rank i T := by
  intro d hd
  exact mem_boundedProfileModuli hN (hD d (frame.subset i hd))
    (frame_modulus_exponent_le frame hδ hN hD i hd hT)

end Erdos1189
