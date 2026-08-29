/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkClosure

/-!
# Roof-maximality bookkeeping for the dependent Section 6 stages

The dependent recursion starts with the finite part of a maximal quotient
wave and chooses a finite-character roof-maximal extension at every
successor.  These lemmas keep the resulting roof invariant separate from the
recursive definition.
-/

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Every wave selected by the dependent Section 6 recursion roofs every wave
in its stage quotient. -/
theorem sectionSixAccumStage_roofs
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ)
    (W : (G.quotient
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).Wave) :
    (G.quotient
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).RoofLE
        W.1 (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1 := by
  cases n with
  | zero =>
      have h := (G.quotient (F y)).roofLE_of_isMax
        (SafeLink.maximalQuotientWave_isMax G (F y)) W
      simpa only [sectionSixAccumStage, RoofLE,
        DWeb.Wave.finitePathSubfamily_terminalFrontier] using h
  | succ n =>
      exact G.sectionSixAccumNext_roofs hNoEnter F K Y Q T
        (G.sectionSixAccumStage hNoEnter F K Y Q T y n) W

theorem sectionSixAccumStage_isRoofMaximal
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    (G.quotient
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier)
        |>.IsRoofMaximal
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave := by
  intro W _
  exact G.sectionSixAccumStage_roofs hNoEnter F K Y Q T y n W

end DWeb

end Erdos599
