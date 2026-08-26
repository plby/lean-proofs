/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Binary chains for the divisor construction in Erdős Problem 1189.
Informal source: the elementary binary covering construction.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FibreObstruction
import Mathlib.Algebra.Ring.GeomSum

namespace Erdos1189

open Finset

/-- The moduli `2, 4, ..., 2^a`. -/
def binaryChain (a : ℕ) : Finset ℕ :=
  (range a).image fun i => 2 ^ (i + 1)

lemma mem_binaryChain {a d : ℕ} :
    d ∈ binaryChain a ↔ ∃ i < a, d = 2 ^ (i + 1) := by
  simp [binaryChain, eq_comm]

lemma binaryChain_pos {a d : ℕ} (hd : d ∈ binaryChain a) : 0 < d := by
  obtain ⟨i, _, rfl⟩ := mem_binaryChain.mp hd
  positivity

lemma binaryChain_nontrivial {a d : ℕ} (hd : d ∈ binaryChain a) : 1 < d := by
  obtain ⟨i, _, rfl⟩ := mem_binaryChain.mp hd
  exact one_lt_pow₀ (by decide) (by omega)

lemma binaryChain_dvd {a d : ℕ} (hd : d ∈ binaryChain a) : d ∣ 2 ^ a := by
  obtain ⟨i, hi, rfl⟩ := mem_binaryChain.mp hd
  exact pow_dvd_pow 2 (by omega)

lemma binaryChain_card (a : ℕ) : (binaryChain a).card = a := by
  rw [binaryChain, card_image_of_injective, card_range]
  intro i j h
  have := Nat.pow_right_injective (by decide : 2 ≤ 2) h
  omega

lemma binaryChain_weight (a : ℕ) : (∑ d ∈ binaryChain a, 2 ^ a / d) + 1 = 2 ^ a := by
  have hinj : Function.Injective (fun i : ℕ => 2 ^ (i + 1)) := by
    intro i j h
    have := Nat.pow_right_injective (by decide : 2 ≤ 2) h
    omega
  rw [binaryChain, sum_image (fun i _ j _ h => hinj h)]
  have heq : (∑ i ∈ range a, 2 ^ a / 2 ^ (i + 1)) = ∑ i ∈ range a, 2 ^ (a - 1 - i) := by
    apply sum_congr rfl
    intro i hi
    rw [Nat.pow_div (by simpa using mem_range.mp hi) (by decide)]
    congr 1
    omega
  rw [heq, sum_range_reflect]
  simpa using geom_sum_mul_add (1 : ℕ) a

/-- The binary classes leave precisely the multiples of `2^a` uncovered. -/
lemma binary_cover_or_dvd (a x : ℕ) :
    (∃ i < a, x ≡ 2 ^ i [MOD 2 ^ (i + 1)]) ∨ 2 ^ a ∣ x := by
  induction a with
  | zero => exact Or.inr (by simp)
  | succ a ih =>
      rcases ih with ⟨i, hi, hxi⟩ | hdiv
      · exact Or.inl ⟨i, by omega, hxi⟩
      · obtain ⟨t, rfl⟩ := hdiv
        by_cases ht : t % 2 = 0
        · right
          obtain ⟨u, rfl⟩ := Nat.dvd_of_mod_eq_zero ht
          exact ⟨u, by rw [pow_succ]; ring⟩
        · left
          refine ⟨a, by omega, ?_⟩
          have ht' : t ≡ 1 [MOD 2] := by
            have := Nat.mod_lt t (by decide : 0 < 2)
            simp only [Nat.ModEq]
            omega
          simpa only [mul_one, ← pow_succ] using ht'.mul_left' (2 ^ a)

end Erdos1189
