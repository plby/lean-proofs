/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.Defs
import ErdosProblems.Erdos63.Numerics
import ErdosProblems.Erdos63.Subdivision

/-!
# The elementary Liu--Montgomery reduction

This file formalizes the last, elementary step in the proof of
Liu--Montgomery's even-cycle interval theorem.  It deliberately does **not**
postulate their deep expander theorem.  Instead,
`LiuMontgomeryIntervalAlternative` records the precise dichotomy needed from
that theorem:

* either the ambient graph contains the one-subdivision of a sufficiently
  large complete graph; or
* a bipartite-expander subgraph supplies an exact path of length one less than
  every requested even cycle length, between the ends of a fixed edge.

The theorems below prove that either alternative gives the full even-cycle
interval.  The numerical lemmas in `Numerics` then extract a power of two,
with arbitrarily large exponent when such intervals have unbounded upper
endpoint.
-/

open Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Closing a simple path of length at least two with an edge between its
endpoints produces a simple cycle whose length is one larger. -/
theorem hasCycleLength_succ_of_adj_hasPathBetweenLength {x y : V} {q : ℕ}
    (hxy : G.Adj x y) (hq : 2 ≤ q) (hpath : HasPathBetweenLength G x y q) :
    HasCycleLength G (q + 1) := by
  obtain ⟨p, hp, hlen⟩ := hpath
  refine ⟨y, Walk.cons hxy.symm p, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨hp, ?_⟩
    intro hedge
    have hedge' : s(x, y) ∈ p.edges := by
      simpa only [Sym2.eq_swap] using hedge
    have hp_one : p.length = 1 := hp.length_eq_one_of_mem_edges hedge'
    omega
  · simp [hlen]

/-- The exact source-level alternative used in the final reduction of
Liu--Montgomery Theorem 1.1 at a real interval endpoint `ell`.

The second branch is the conclusion needed from the exact-path theorem after
its numerical window has been compared with
`[(Real.log ell)^8, ell]`.  Keeping it as a field of this proposition makes all
deep graph-expansion input an explicit hypothesis of the reduction theorems.
-/
def LiuMontgomeryIntervalAlternative (G : SimpleGraph V) (ell : ℝ) : Prop :=
  (∃ t : ℕ, ell ≤ (2 * t : ℕ) ∧ oneSubdivisionClique t ⊑ G) ∨
    ∃ (H : SimpleGraph V) (x y : V),
      H ≤ G ∧ H.Adj x y ∧
        ∀ m : ℕ, Even m → 6 ≤ m →
          Real.log ell ^ 8 ≤ m → m ≤ ell →
            HasPathBetweenLength H x y (m - 1)

/-- Either branch of `LiuMontgomeryIntervalAlternative` supplies every even
cycle length in `[(Real.log ell)^8, ell]`, once the lower endpoint is at least
six. -/
theorem even_cycle_interval_of_liuMontgomeryAlternative {ell : ℝ}
    (hlog6 : (6 : ℝ) ≤ Real.log ell ^ 8)
    (halt : LiuMontgomeryIntervalAlternative G ell) :
    ∀ m : ℕ, Even m → Real.log ell ^ 8 ≤ m → m ≤ ell →
      HasCycleLength G m := by
  intro m heven hlower hupper
  have h6 : 6 ≤ m := by
    exact_mod_cast hlog6.trans hlower
  rcases halt with hsub | hpath
  · obtain ⟨t, hellt, htG⟩ := hsub
    have hmt : m ≤ 2 * t := by
      exact_mod_cast hupper.trans hellt
    have hcopy : cycleGraph m ⊑ G :=
      every_even_cycle_isContained_of_oneSubdivisionClique htG heven h6 hmt
    exact (hasCycleLength_iff_cycleGraph_isContained (by omega)).2 hcopy
  · obtain ⟨H, x, y, hHG, hxy, hexact⟩ := hpath
    have hmone : 2 ≤ m - 1 := by omega
    have hcycleH : HasCycleLength H ((m - 1) + 1) :=
      hasCycleLength_succ_of_adj_hasPathBetweenLength hxy hmone
        (hexact m heven h6 hlower hupper)
    have hcycleH' : HasCycleLength H m := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at hcycleH
      exact hcycleH
    exact hcycleH'.mono hHG

/-- A single sufficiently large Liu--Montgomery alternative contains a
power-of-two cycle whose exponent is beyond any prescribed cutoff. -/
theorem dyadic_cycle_of_liuMontgomeryAlternative {ell : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hlarge : (2 : ℝ) ^ N ≤ ell)
    (hlog : Real.log ell ^ 8 ≤ ell / 2)
    (hlog6 : (6 : ℝ) ≤ Real.log ell ^ 8)
    (halt : LiuMontgomeryIntervalAlternative G ell) :
    ∃ n : ℕ, N ≤ n ∧ HasCycleLength G (2 ^ n) := by
  apply Numerics.exists_two_pow_of_even_log_interval hN hlarge hlog
    (fun m ↦ HasCycleLength G m)
  exact even_cycle_interval_of_liuMontgomeryAlternative hlog6 halt

/-- If a fixed graph admits Liu--Montgomery alternatives with arbitrarily
large interval endpoint, then its power-of-two cycle exponents are unbounded.

The hypothesis remains an ordinary parameter.  In particular, this theorem
does not assert or hide the missing expander construction.
-/
theorem dyadic_tail_of_arbitrarily_large_liuMontgomeryAlternatives
    (hsource : ∀ B : ℝ, ∃ ell : ℝ, B ≤ ell ∧
      LiuMontgomeryIntervalAlternative G ell) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ HasCycleLength G (2 ^ n) := by
  apply Numerics.exists_two_pow_of_arbitrarily_large_even_log_intervals
    (fun m ↦ HasCycleLength G m) _ N
  intro B
  obtain ⟨ell, hell, halt⟩ := hsource (max B (Real.exp 6))
  have hBell : B ≤ ell := (le_max_left _ _).trans hell
  have hexpell : Real.exp 6 ≤ ell := (le_max_right _ _).trans hell
  have hell_pos : 0 < ell := (Real.exp_pos 6).trans_le hexpell
  have hsix_log : (6 : ℝ) ≤ Real.log ell :=
    (Real.le_log_iff_exp_le hell_pos).2 hexpell
  have hlog6 : (6 : ℝ) ≤ Real.log ell ^ 8 := by
    calc
      (6 : ℝ) ≤ 6 ^ 8 := by norm_num
      _ ≤ Real.log ell ^ 8 := by gcongr
  refine ⟨ell, hBell, ?_⟩
  exact even_cycle_interval_of_liuMontgomeryAlternative hlog6 halt

end Erdos63
