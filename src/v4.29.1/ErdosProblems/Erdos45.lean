/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 45.
https://www.erdosproblems.com/forum/thread/45

Informal authors:
- Ernest S. Croot III

Formal authors:
- Bhavik Mehta
- Thomas Bloom

URLs:
- https://github.com/b-mehta/unit-fractions
-/
import ErdosProblems.Erdos46
import Mathlib.Combinatorics.Compactness

namespace Erdos45

open UnitFractions

theorem erdos45 :
    ∀ k : ℕ, 2 ≤ k → ∃ nₖ : ℕ, ∀ c : ℕ → Fin k,
      ∃ D' : Finset ℕ, D' ⊆ ((nₖ.divisors.erase 1).erase nₖ) ∧
        rec_sum D' = 1 ∧ ∃ a : Fin k, ∀ d ∈ D', c d = a := by
  intro k hk
  classical
  let a0 : Fin k := ⟨0, lt_of_lt_of_le zero_lt_two hk⟩
  let GoodBound : ℕ → Prop := fun N =>
    ∀ c : ℕ → Fin k,
      ∃ D' : Finset ℕ, D' ⊆ Finset.Icc 2 N ∧
        rec_sum D' = 1 ∧ ∃ a : Fin k, ∀ d ∈ D', c d = a
  have hinterval : ∃ N : ℕ, GoodBound N := by
    by_contra hinterval
    have hbadN : ∀ N : ℕ, ∃ c : ℕ → Fin k,
        ¬ ∃ D' : Finset ℕ, D' ⊆ Finset.Icc 2 N ∧
          rec_sum D' = 1 ∧ ∃ a : Fin k, ∀ d ∈ D', c d = a := by
      intro N
      have hN : ¬ GoodBound N := by
        intro hgood
        exact hinterval ⟨N, hgood⟩
      dsimp [GoodBound] at hN
      exact not_forall.mp hN
    let M : Finset ℕ → ℕ := fun s => s.sum id + 2
    let g : Finset ℕ → ℕ → Fin k := fun s => Classical.choose (hbadN (M s))
    obtain ⟨χ, hχ⟩ := Finset.rado_selection (β := fun _ : ℕ => Fin k) g
    let cInt : ℤ → Fin k := fun z => if hz : 0 ≤ z then χ z.toNat else a0
    rcases Erdos46.erdos46 cInt with ⟨S, hSge2, hrecS, ⟨a, hmonoS⟩⟩
    obtain ⟨t, hSt, hχt⟩ := hχ S
    have hSM : S ⊆ Finset.Icc 2 (M t) := by
      intro n hn
      rw [Finset.mem_Icc]
      refine ⟨hSge2 n hn, ?_⟩
      dsimp [M]
      have hnt : n ∈ t := hSt hn
      have hle : n ≤ t.sum id := by
        simpa using
          (Finset.single_le_sum (f := fun m : ℕ => m) (fun m _ => Nat.zero_le m) hnt)
      exact le_trans hle (Nat.le_add_right _ _)
    have hmonoGt : ∃ b : Fin k, ∀ n ∈ S, g t n = b := by
      refine ⟨a, ?_⟩
      intro n hn
      have hχa : χ n = a := by
        simpa [cInt, a0] using hmonoS n hn
      calc
        g t n = χ n := by symm; exact hχt n hn
        _ = a := hχa
    rcases hmonoGt with ⟨b, hbmono⟩
    have hbad_t :
        ∀ D' : Finset ℕ, D' ⊆ Finset.Icc 2 (M t) → rec_sum D' = 1 →
          ∀ b : Fin k, ∃ d ∈ D', g t d ≠ b := by
      intro D' hD' hrec b
      by_contra hDbad
      push Not at hDbad
      exact (Classical.choose_spec (hbadN (M t))) ⟨D', hD', hrec, b, hDbad⟩
    obtain ⟨d, hdS, hdne⟩ := hbad_t S hSM hrecS b
    exact hdne (hbmono d hdS)
  rcases hinterval with ⟨N, hN⟩
  refine ⟨Nat.factorial (N + 2), ?_⟩
  intro c
  rcases hN c with ⟨D', hD', hrecD', a, hmonoD'⟩
  refine ⟨D', ?_, hrecD', a, hmonoD'⟩
  intro d hd
  have hdIcc := hD' hd
  rw [Finset.mem_Icc] at hdIcc
  simp only [Finset.mem_erase, Nat.mem_divisors]
  refine ⟨?_, ?_, ?_⟩
  · have hfact : N < Nat.factorial (N + 2) := by
      exact lt_of_lt_of_le (by omega) (Nat.self_le_factorial _)
    exact ne_of_lt (lt_of_le_of_lt hdIcc.2 hfact)
  · exact ne_of_gt (lt_of_lt_of_le one_lt_two hdIcc.1)
  · exact ⟨Nat.dvd_factorial (lt_of_lt_of_le zero_lt_two hdIcc.1)
      (le_trans hdIcc.2 (Nat.le_add_right N 2)), Nat.factorial_ne_zero _⟩

#print axioms erdos45
-- 'Erdos45.erdos45' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos45
