/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The family in Section 4.2 of Pickhardt and Omniscience Research Agent,
"Irreducible Covering Sets: A Solution of Erdős Problem 1189".
Formal author: OpenAI Codex.

Coverage uses a translated binary assignment. Irreducibility is proved by
the fibre-counting obstruction, without assuming Simpson's theorem.
This file establishes the extremal lower bound, not the matching upper bound.
-/

import ErdosProblems.Erdos1189.SunDivisors

namespace Erdos1189

open Finset

def extremalTerminal (r : ℕ) : Finset ℕ := {3, 3 * 2 ^ (r - 1), 3 * 2 ^ r}

def extremalModuli (r : ℕ) : Finset ℕ := binaryChain r ∪ extremalTerminal r

lemma three_not_dvd_two_pow (i : ℕ) : ¬ 3 ∣ 2 ^ i := by
  intro h
  have := Nat.prime_three.dvd_of_dvd_pow h
  norm_num at this

lemma extremalTerminal_dvd {r d : ℕ} (hd : d ∈ extremalTerminal r) :
    3 ∣ d ∧ d ∣ 3 * 2 ^ r := by
  simp only [extremalTerminal, mem_insert, mem_singleton] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨dvd_rfl, dvd_mul_right _ _⟩
  · exact ⟨dvd_mul_right _ _, Nat.mul_dvd_mul_left 3 (pow_dvd_pow 2 (by omega))⟩
  · exact ⟨dvd_mul_right _ _, dvd_rfl⟩

lemma extremalTerminal_lt {r : ℕ} (hr : 2 ≤ r) :
    3 < 3 * 2 ^ (r - 1) ∧ 3 * 2 ^ (r - 1) < 3 * 2 ^ r := by
  have hpow : 1 < 2 ^ (r - 1) := one_lt_pow₀ (by decide) (by omega)
  have heq : 2 ^ r = 2 ^ (r - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  constructor <;> nlinarith

lemma extremalTerminal_card {r : ℕ} (hr : 2 ≤ r) : (extremalTerminal r).card = 3 := by
  obtain ⟨h₁, h₂⟩ := extremalTerminal_lt hr
  simp [extremalTerminal, ne_of_lt h₁, ne_of_lt h₂, ne_of_lt (h₁.trans h₂)]

lemma extremalModuli_nontrivial {r d : ℕ} (hd : d ∈ extremalModuli r) : 1 < d := by
  rcases mem_union.mp hd with hd | hd
  · exact binaryChain_nontrivial hd
  · simp only [extremalTerminal, mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · decide
    · have : 0 < 2 ^ (r - 1) := by positivity
      omega
    · have : 0 < 2 ^ r := by positivity
      omega

lemma extremalModuli_dvd {r d : ℕ} (hd : d ∈ extremalModuli r) : d ∣ 3 * 2 ^ r := by
  rcases mem_union.mp hd with hd | hd
  · exact (binaryChain_dvd hd).trans (dvd_mul_left _ _)
  · exact (extremalTerminal_dvd hd).2

def extremalResidue (r d : ℕ) : ℕ :=
  if d = 3 then 0 else
  if d = 3 * 2 ^ (r - 1) then 2 ^ r else
  if d = 3 * 2 ^ r then 2 * 2 ^ r else 2 ^ (d.factorization 2 - 1)

lemma extremalResidue_binary (r i : ℕ) : extremalResidue r (2 ^ (i + 1)) = 2 ^ i := by
  have h₀ : 2 ^ (i + 1) ≠ 3 := by
    intro h
    exact three_not_dvd_two_pow (i + 1) (h ▸ dvd_rfl)
  have h₁ : 2 ^ (i + 1) ≠ 3 * 2 ^ (r - 1) := by
    intro h
    exact three_not_dvd_two_pow (i + 1) (h ▸ dvd_mul_right _ _)
  have h₂ : 2 ^ (i + 1) ≠ 3 * 2 ^ r := by
    intro h
    exact three_not_dvd_two_pow (i + 1) (h ▸ dvd_mul_right _ _)
  rw [extremalResidue, if_neg h₀, if_neg h₁, if_neg h₂,
    Nat.factorization_pow_self Nat.prime_two]
  simp

lemma extremal_natural_cover {r : ℕ} (hr : 2 ≤ r) (x : ℕ) :
    ∃ d ∈ extremalModuli r, x ≡ extremalResidue r d [MOD d] := by
  rcases binary_cover_or_dvd r x with ⟨i, hi, hxi⟩ | hdiv
  · refine ⟨2 ^ (i + 1), mem_union_left _ (mem_binaryChain.mpr ⟨i, hi, rfl⟩), ?_⟩
    rw [extremalResidue_binary]
    exact hxi
  · obtain ⟨y, rfl⟩ := hdiv
    obtain ⟨h₁, h₂⟩ := extremalTerminal_lt hr
    have hmod : 2 ^ r * y ≡ 2 ^ r * (y % 3) [MOD 3 * 2 ^ r] := by
      simpa only [Nat.mul_comm] using (Nat.mod_modEq y 3).symm.mul_left' (2 ^ r)
    have hy : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
    rcases hy with hy | hy | hy
    · refine ⟨3, by simp [extremalModuli, extremalTerminal], ?_⟩
      simpa [extremalResidue, hy] using hmod.of_dvd (dvd_mul_right 3 (2 ^ r))
    · refine ⟨3 * 2 ^ (r - 1), by simp [extremalModuli, extremalTerminal], ?_⟩
      simpa [extremalResidue, ne_of_gt h₁, hy] using
        hmod.of_dvd (Nat.mul_dvd_mul_left 3 (pow_dvd_pow 2 (by omega : r - 1 ≤ r)))
    · refine ⟨3 * 2 ^ r, by simp [extremalModuli, extremalTerminal], ?_⟩
      rw [extremalResidue, if_neg (ne_of_gt (h₁.trans h₂)), if_neg (ne_of_gt h₂), if_pos rfl]
      simpa only [hy, Nat.mul_comm] using hmod

lemma extremal_covering {r : ℕ} (hr : 2 ≤ r) : IsCoveringSet (extremalModuli r) := by
  refine ⟨fun d hd => extremalModuli_nontrivial hd, fun d => extremalResidue r d, ?_⟩
  apply (covers_iff_finite_period (N := 3 * 2 ^ r) (by positivity)
    (fun d hd => extremalModuli_dvd hd)).mpr
  intro x
  obtain ⟨d, hd, hxd⟩ := extremal_natural_cover hr x
  exact ⟨d, hd, Int.natCast_modEq_iff.mpr hxd⟩

theorem extremal_irreducible {r : ℕ} (hr : 2 ≤ r) :
    IsIrreducibleCoveringSet (extremalModuli r) := by
  apply irreducible_of_fibre_cover (N := 2 ^ r) (p := 3)
    (by positivity) (by decide) ((by decide : Nat.Coprime 2 3).pow_left r)
    (fun d hd => binaryChain_pos hd) (fun d hd => binaryChain_dvd hd)
    (binaryChain_weight r) (extremalTerminal_card hr)
    (fun d hd => (extremalTerminal_dvd hd).1)
    (by simp [extremalTerminal]) (extremal_covering hr)

lemma extremalModuli_card {r : ℕ} (hr : 2 ≤ r) : (extremalModuli r).card = r + 3 := by
  have hd : Disjoint (binaryChain r) (extremalTerminal r) := by
    apply disjoint_left.mpr
    intro d hdD hdB
    obtain ⟨i, _, rfl⟩ := mem_binaryChain.mp hdD
    exact three_not_dvd_two_pow (i + 1) (extremalTerminal_dvd hdB).1
  rw [extremalModuli, card_union_of_disjoint hd, binaryChain_card, extremalTerminal_card hr]

lemma extremalModuli_largest (r : ℕ) : (extremalModuli r).sup id = 3 * 2 ^ r := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro d hd
    exact Nat.le_of_dvd (by positivity) (extremalModuli_dvd hd)
  · apply le_sup (f := id)
    simp [extremalModuli, extremalTerminal]

/-- The extremal construction exists at every requested cardinality. -/
theorem exists_irreducible_extremal {k : ℕ} (hk : 5 ≤ k) :
    ∃ D : Finset ℕ, IsIrreducibleCoveringSet D ∧ D.card = k ∧
      D.sup id = 3 * 2 ^ (k - 3) := by
  refine ⟨extremalModuli (k - 3), extremal_irreducible (by omega), ?_,
    extremalModuli_largest _⟩
  rw [extremalModuli_card (by omega)]
  omega

end Erdos1189
