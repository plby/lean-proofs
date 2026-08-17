/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos185.DHJ.Cube
import ErdosProblems.Erdos185.DHJ.Density
import ErdosProblems.Erdos185.DHJ.Uniformity
import ErdosProblems.Erdos171.Insensitive
import ErdosProblems.Erdos171.InsensitiveTiling

/-!
# Almost tilings of insensitive subsets of the ternary cube

This file specializes the Dodos--Kanellopoulos--Tyros greedy tiling theorem
to the ternary cube.  The input needed by the generic tiling development is
the restricted multidimensional density theorem for the binary subalphabet;
`restricted_binary_subspace` supplies exactly that input.  The generic
finite recursion then tiles one insensitive set by subspaces, and its
intersection recursion applies this successively to two insensitive factors.

The public result preserves an arbitrary lower bound on the ambient
dimension.  It is the two-factor form used by the density-increment argument.
-/

namespace Erdos185.DHJ

open Combinatorics
open Erdos171

/-- The specialized restricted-subspace theorem is precisely the restricted
multidimensional density hypothesis over the binary subalphabet. -/
theorem finiteRestrictedMDHJ_binary (d : ℕ) :
    Erdos171.FiniteRestrictedMDHJ 2 d := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := restricted_binary_subspace d delta hdelta
  refine ⟨N, ?_⟩
  intro A hA
  obtain ⟨U, hU⟩ := hN A hA
  rw [Erdos171.containsRestrictedSubspace_iff]
  refine ⟨U, ?_⟩
  intro x
  exact hU x

/-- DKT Lemma 12, specialized to one `(i,2)`-insensitive ternary set, with
an arbitrary lower bound on the ambient dimension. -/
theorem exists_one_insensitive_tiling_dimension_at_least
    (d lower : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ∃ N : ℕ, lower ≤ N ∧
      Erdos171.OneInsensitiveTilingAt 2 d N beta := by
  exact (finiteRestrictedMDHJ_binary d).exists_oneInsensitiveTilingAt_ge
    hbeta lower

/-- Exact-existential-dimension form of the one-factor tiling theorem. -/
theorem exists_one_insensitive_tiling_dimension
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ∃ N : ℕ, Erdos171.OneInsensitiveTilingAt 2 d N beta := by
  obtain ⟨N, _hN, htile⟩ :=
    exists_one_insensitive_tiling_dimension_at_least d 0 beta hbeta
  exact ⟨N, htile⟩

/-- DKT Corollary 13 for the intersection of one `(0,2)`-insensitive set and
one `(1,2)`-insensitive set.  The tiling dimension is exactly `d`, its ambient
dimension may be required to exceed `lower`, and the uncovered density is
strictly below `4 * beta`.

We invoke the generic two-factor theorem at the smaller error parameter
`beta / 2`.  Thus its strict density premise is implied even when the input
density is exactly `4 * beta`, and its stronger uncovered bound (`2 * beta`)
implies the stated one. -/
theorem exists_two_insensitive_tiling_dimension
    (d lower : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ∃ N : ℕ, lower ≤ N ∧ ∀ D0 D1 : Finset (Word 3 N),
      Erdos171.IsLastInsensitive (0 : Fin 2) (D0 : Set (Word 3 N)) →
      Erdos171.IsLastInsensitive (1 : Fin 2) (D1 : Set (Word 3 N)) →
      4 * beta ≤ density (D0 ∩ D1) →
      ∃ T : Erdos171.SubspaceTiling (Fin d) (Fin 3) (Fin N),
        T.IsContainedIn (D0 ∩ D1) ∧
          density ((D0 ∩ D1) \ T.covered) < 4 * beta := by
  have hhalf : 0 < beta / 2 := by linarith
  have hone : ∀ m lower', ∃ n, lower' ≤ n ∧
      Erdos171.OneInsensitiveTilingAt 2 m n (beta / 2) := by
    intro m lower'
    exact (finiteRestrictedMDHJ_binary m).exists_oneInsensitiveTilingAt_ge
      hhalf lower'
  obtain ⟨N, hN, hinter⟩ :=
    Erdos171.exists_insensitiveIntersectionTilingAt_ge
      hhalf hone 1 d lower
  refine ⟨N, hN, ?_⟩
  intro D0 D1 hD0 hD1 hmass
  let D : Fin 2 → Finset (Word 3 N) := ![D0, D1]
  let label : Fin 2 → Fin 2 := ![0, 1]
  have hD : ∀ j, Erdos171.IsLastInsensitive (label j)
      (D j : Set (Word 3 N)) := by
    intro j
    fin_cases j
    · simpa [D, label] using hD0
    · simpa [D, label] using hD1
  have hfamily : Erdos171.familyInter D = D0 ∩ D1 := by
    ext x
    simp only [Erdos171.mem_familyInter, Finset.mem_inter]
    constructor
    · intro hx
      exact ⟨by simpa [D] using hx 0, by simpa [D] using hx 1⟩
    · rintro ⟨hx0, hx1⟩ j
      fin_cases j
      · simpa [D] using hx0
      · simpa [D] using hx1
  have hdense : 2 * (2 : ℝ) * (beta / 2) <
      density (Erdos171.familyInter D) := by
    rw [hfamily]
    linarith
  obtain ⟨T, hT, herr⟩ := hinter label D hD hdense
  refine ⟨T, ?_, ?_⟩
  · simpa only [hfamily] using hT
  · rw [hfamily] at herr
    norm_num at herr
    have herr' : density ((D0 ∩ D1) \ T.covered) < 2 * beta := by
      rw [density_eq_card_div_card, Erdos171.card_word]
      norm_num
      nlinarith [herr]
    linarith

end Erdos185.DHJ
