/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCut
import ErdosProblems.Erdos599.HindranceGrounding

/-!
# Final assembly of Assertions 8.18 and 8.22

Assertion 8.18 proves that the concrete set `BB` separates the original
source from the target.  Assertion 8.22 orthogonalizes that bookkeeping
boundary: it constructs a warp starting in the original source whose
terminal frontier is a separating subset of `BB`, and retains an unused
source after essential trimming.  This file records the exact sufficient
composition into an ordinary hindrance.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFinalAssembly

open DirectedPath

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- The precise output required from the simultaneous grounding switch.
The first three fields are Assertion 8.22 itself.  The final field is the
stationary unused-source conclusion from the paragraph immediately after
Assertion 8.22: the essential part of the constructed warp omits an original
source.  This is deliberately stated directly rather than via an inessential
member of `warp`; first-hit pruning discards components which do not meet the
cut, while their unused source is still exactly what makes the essential part
a hindrance. -/
structure Assertion822Output
    (L : PopularAuxiliary.Input Gamma I) (C : Set L.LV) where
  warp : Set Gamma.DPath
  isWarp : Gamma.IsWarp warp
  initial_subset_source : Gamma.initialSet warp ⊆ Gamma.source
  /-- The globally orthogonalized boundary actually used by the warp. -/
  frontier : Set V
  terminalFrontier_eq : Gamma.terminalFrontier warp = frontier
  frontier_subset_BB : frontier ⊆ GroundingCut.BB L C
  frontier_separates : Popular.IsSeparator Gamma frontier
  essential_initial_ne_source :
    Gamma.initialSet (Gamma.essentialWarpPart warp) ≠ Gamma.source

/-- Exact final step of source Theorem 7.30: the finite descent decoder of
Assertion 8.18 and the simultaneous warp of Assertion 8.22 yield an ordinary
hindrance in the original web. -/
theorem Assertion822Output.exists_hindrance
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (O : Assertion822Output L C)
    (hC : Popular.IsSeparator L.lambda C)
    (hterminal : Popular.IsSeparator Gamma L.terminalCut)
    (hdecode : GroundingCut.FiniteDescentDecoder L C) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  have hwave : Gamma.IsWave O.warp :=
    DWeb.isWave_of_terminalFrontier_isSeparator O.isWarp
      O.initial_subset_source (by
        rw [O.terminalFrontier_eq]
        exact O.frontier_separates)
  exact ⟨Gamma.essentialWarpPart O.warp, hwave.essentialWarpPart,
    O.essential_initial_ne_source⟩

end GroundingFinalAssembly
end Erdos599
