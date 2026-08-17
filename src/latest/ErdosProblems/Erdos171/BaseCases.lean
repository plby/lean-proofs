/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Binary
import ErdosProblems.Erdos171.Framework

/-!
# The one-letter base case of density Hales--Jewett

A proper line needs at least one coordinate even when the alphabet has one
letter.  In every positive dimension the cube itself is a singleton, so a
positive-density set contains its unique word and hence contains a line.
-/

namespace Erdos171

open Set

/-- The all-wildcard line over the one-letter alphabet. -/
def oneLetterLine (n : ℕ) (hn : 1 ≤ n) :
    Combinatorics.Line (Fin 1) (Fin n) where
  idxFun _ := none
  proper := ⟨⟨0, hn⟩, rfl⟩

@[simp] theorem oneLetterLine_apply (n : ℕ) (hn : 1 ≤ n) (a : Fin 1) :
    oneLetterLine n hn a = fun _ ↦ 0 := by
  funext i
  simpa [oneLetterLine, Combinatorics.Line.coe_apply] using
    (Subsingleton.elim a (0 : Fin 1))

/-- Every nonempty set in a positive-dimensional one-letter cube contains a
proper combinatorial line. -/
theorem containsLine_one_of_nonempty {n : ℕ} (hn : 1 ≤ n)
    {A : Set (Word 1 n)} (hA : A.Nonempty) : ContainsLine A := by
  obtain ⟨w, hw⟩ := hA
  refine ⟨oneLetterLine n hn, ?_⟩
  rintro _ ⟨a, rfl⟩
  convert hw using 1

/-- Set/cardinality form of the eventual density Hales--Jewett theorem for the
one-letter alphabet.  The exact threshold is `N = 1`. -/
theorem exists_containsLine_of_dense_one (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Set (Word 1 n),
      eps * (1 : ℝ) ^ n ≤ A.ncard → ContainsLine A := by
  refine ⟨1, ?_⟩
  intro n hn A hdense
  have hncardR : 0 < (A.ncard : ℝ) := by
    have hle : eps ≤ (A.ncard : ℝ) := by simpa using hdense
    exact heps.trans_le hle
  have hncard : 0 < A.ncard := by exact_mod_cast hncardR
  exact containsLine_one_of_nonempty hn ((Set.ncard_pos (Set.toFinite A)).mp hncard)

/-- Finset form of the same exact one-letter base case. -/
theorem exists_containsLine_of_dense_one_finset (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Word 1 n),
      eps * (1 : ℝ) ^ n ≤ A.card → ContainsLine (A : Set (Word 1 n)) := by
  obtain ⟨N, hN⟩ := exists_containsLine_of_dense_one eps heps
  refine ⟨N, ?_⟩
  intro n hn A hdense
  apply hN n hn (A : Set (Word 1 n))
  simpa only [Set.ncard_coe_finset] using hdense

/-- Predicate-level wrapper for the exact eventual density-Hales--Jewett
framework at alphabet size one. -/
theorem eventualDensityHJ_one : EventualDensityHJ 1 := by
  intro delta hdelta
  refine ⟨1, ?_⟩
  intro n hn A hA
  apply containsLine_one_of_nonempty hn
  exact (density_pos A).mp (hdelta.trans_le hA)

/-- Predicate-level wrapper for the binary Sperner proof. -/
theorem eventualDensityHJ_two : EventualDensityHJ 2 := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := exists_containsLine_of_dense_binary_finset delta hdelta
  refine ⟨N, ?_⟩
  intro n hn A hA
  apply hN n hn A
  have hden : delta ≤ (A.card : ℝ) / (2 : ℝ) ^ n := by
    simpa [density, card_word] using hA
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp hden

/-- One-witness density Hales--Jewett for the one-letter alphabet. -/
theorem finiteDensityHJ_one : FiniteDensityHJ 1 := by
  intro delta hdelta
  obtain ⟨n₀, hn₀⟩ := eventualDensityHJ_one delta hdelta
  exact ⟨n₀, hn₀ n₀ le_rfl⟩

/-- One-witness density Hales--Jewett for the binary alphabet. -/
theorem finiteDensityHJ_two : FiniteDensityHJ 2 := by
  intro delta hdelta
  obtain ⟨n₀, hn₀⟩ := eventualDensityHJ_two delta hdelta
  exact ⟨n₀, hn₀ n₀ le_rfl⟩

end Erdos171
