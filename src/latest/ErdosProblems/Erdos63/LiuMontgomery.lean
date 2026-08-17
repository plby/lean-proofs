/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.Bridges
import ErdosProblems.Erdos63.LiuMontgomeryReduction
import ErdosProblems.Erdos63.LiuMontgomerySource
import ErdosProblems.Erdos63.PathCycles

/-!
# The finite Liu--Montgomery input for Erdős Problem 63

This file is the integration boundary between the finite graph-theoretic
machinery in Liu--Montgomery and the compactness argument in `Bridges`.

The source theorem is most conveniently packaged uniformly in a requested
lower bound for the interval endpoint.  The elementary argument below then
chooses one endpoint bound which simultaneously guarantees

* that the logarithmic lower endpoint is at most half the upper endpoint;
* that the upper endpoint is at least the requested power of two; and
* that the logarithmic lower endpoint is at least six.

Those three inequalities let `dyadic_cycle_of_liuMontgomeryAlternative`
extract the desired power-of-two cycle.
-/

open Filter SimpleGraph
open scoped SimpleGraph

namespace Erdos63

universe u

variable {V : Type u} {G G' : SimpleGraph V}

/-- The interval alternative is monotone when edges are added to the ambient
graph.  This is the transport used after the expander has been extracted as a
subgraph of the original finite graph. -/
theorem LiuMontgomeryIntervalAlternative.mono {ell : ℝ}
    (hGG' : G ≤ G') (h : LiuMontgomeryIntervalAlternative G ell) :
    LiuMontgomeryIntervalAlternative G' ell := by
  rcases h with hsub | hpath
  · left
    obtain ⟨t, hell, hcopy⟩ := hsub
    exact ⟨t, hell, hcopy.trans (SimpleGraph.IsContained.of_le hGG')⟩
  · right
    obtain ⟨H, x, y, hHG, hxy, hpaths⟩ := hpath
    exact ⟨H, x, y, hHG.trans hGG', hxy, hpaths⟩

/-- Convert an interval alternative in an extracted subgraph into cycle
statements in the original graph. -/
theorem even_cycle_interval_of_subgraph_liuMontgomeryAlternative
    (K : G.Subgraph) {ell : ℝ}
    (hlog6 : (6 : ℝ) ≤ Real.log ell ^ 8)
    (halt : LiuMontgomeryIntervalAlternative K.coe ell) :
    ∀ m : ℕ, Even m → Real.log ell ^ 8 ≤ m → m ≤ ell →
      HasCycleLength G m := by
  intro m heven hlower hupper
  exact HasCycleLength.of_subgraph K
    (even_cycle_interval_of_liuMontgomeryAlternative hlog6 halt
      m heven hlower hupper)

/-- The uniform finite conclusion supplied by the graph-theoretic part of
Liu--Montgomery's proof.  For every requested lower bound `B`, a sufficiently
large average degree forces one of the two source alternatives at an endpoint
`ell ≥ B`.

The predicate is separated from its construction so that the numerical and
graph-theoretic dependency boundaries remain explicit. -/
def LiuMontgomeryFiniteSource : Prop :=
  ∀ B : ℝ, ∃ d : ℕ, 0 < d ∧
    ∀ {W : Type u} [Fintype W] [Nonempty W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      AvgDegreeAtLeast H d →
        ∃ ell : ℝ, B ≤ ell ∧ LiuMontgomeryIntervalAlternative H ell

/-- Source-facing formulation after the subdivision/exact-path dichotomy has
been discharged.  This form is stable under transporting cycles out of an
extracted subgraph, even when extraction changes the vertex type to a
subtype. -/
def LiuMontgomeryFiniteIntervalSource : Prop :=
  ∀ B : ℝ, ∃ d : ℕ, 0 < d ∧
    ∀ {W : Type u} [Fintype W] [Nonempty W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      AvgDegreeAtLeast H d →
        ∃ ell : ℝ, B ≤ ell ∧
          ∀ m : ℕ, Even m → Real.log ell ^ 8 ≤ m → m ≤ ell →
            HasCycleLength H m

/-- The graph-theoretic alternative gives the even-cycle interval once its
endpoint is large enough that the logarithmic lower endpoint exceeds six. -/
theorem liuMontgomeryFiniteIntervalSource_of_alternatives
    (hsource : LiuMontgomeryFiniteSource.{u}) :
    LiuMontgomeryFiniteIntervalSource.{u} := by
  intro B
  obtain ⟨d, hd, hfinite⟩ := hsource (max B (Real.exp 6))
  refine ⟨d, hd, ?_⟩
  intro W _ _ H _ havg
  obtain ⟨ell, hell, halt⟩ := hfinite H havg
  have hBell : B ≤ ell := (le_max_left B (Real.exp 6)).trans hell
  have hexpell : Real.exp 6 ≤ ell :=
    (le_max_right B (Real.exp 6)).trans hell
  have hell_pos : 0 < ell := (Real.exp_pos 6).trans_le hexpell
  have hsix_log : (6 : ℝ) ≤ Real.log ell :=
    (Real.le_log_iff_exp_le hell_pos).2 hexpell
  have hlog6 : (6 : ℝ) ≤ Real.log ell ^ 8 := by
    calc
      (6 : ℝ) ≤ 6 ^ 8 := by norm_num
      _ ≤ Real.log ell ^ 8 := by gcongr
  exact ⟨ell, hBell, even_cycle_interval_of_liuMontgomeryAlternative hlog6 halt⟩

/-- An unbounded family of Liu--Montgomery even-cycle intervals implies the
finite power-tail theorem. -/
theorem finitePowerTail_of_liuMontgomeryFiniteIntervalSource
    (hsource : LiuMontgomeryFiniteIntervalSource.{u}) :
    FinitePowerTailTheorem.{u} := by
  intro lower
  obtain ⟨L, hL⟩ :=
    Filter.eventually_atTop.mp Numerics.eventually_log_pow_eight_le_half
  let N : ℕ := max lower 1
  let B : ℝ := max L ((2 : ℝ) ^ N)
  obtain ⟨d, hd, hfinite⟩ := hsource B
  refine ⟨d, hd, ?_⟩
  intro W _ _ H _ havg
  obtain ⟨ell, hell, hinterval⟩ := hfinite H havg
  have hLell : L ≤ ell :=
    (le_max_left L ((2 : ℝ) ^ N)).trans hell
  have hlarge : (2 : ℝ) ^ N ≤ ell :=
    (le_max_right L ((2 : ℝ) ^ N)).trans hell
  have hlog : Real.log ell ^ 8 ≤ ell / 2 := hL ell hLell
  obtain ⟨n, hn, hcycle⟩ := Numerics.exists_two_pow_of_even_log_interval
    (N := N) (P := fun m ↦ HasCycleLength H m)
    (le_max_right lower 1) hlarge hlog hinterval
  exact ⟨n, (le_max_left lower 1).trans hn, hcycle⟩

/-- The uniform source theorem implies the finite power-tail statement used
by the compactness bridge. -/
theorem finitePowerTail_of_liuMontgomeryFiniteSource
    (hsource : LiuMontgomeryFiniteSource.{u}) :
    FinitePowerTailTheorem.{u} :=
  finitePowerTail_of_liuMontgomeryFiniteIntervalSource
    (liuMontgomeryFiniteIntervalSource_of_alternatives hsource)

/-- The unconditional finite power-tail theorem supplied by the complete
Liu--Montgomery finite interval argument. -/
theorem liuMontgomery_finitePowerTail : FinitePowerTailTheorem.{u} :=
  finitePowerTail_of_liuMontgomeryFiniteIntervalSource
    liuMontgomery_finite_even_cycle_intervals_raw

end Erdos63
