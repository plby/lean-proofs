/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualGraphDistribution
import ErdosProblems.Erdos207.LaterTriangleScaleUpdate

/-! # Promotion of the corrected residual law to a later vortex prefix -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsResidualGraphStronglyWellDistributed.future_stage
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k i : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (hnonempty : ∀ a, (W.U a).Nonempty) (hki : k ≤ i) :
    IsResidualGraphStronglyWellDistributed L W i G initial later p C b := by
  intro Ifix Dfix Efix hdis hE
  have hscale : laterTriangleScale W k p Dfix ≤ laterTriangleScale W i p Dfix :=
    prod_le_prod' (fun T _ ↦ W.laterTrianglePointScale_mono hnonempty hki le_rfl T)
  exact (h Ifix Dfix Efix hdis hE).trans (by gcongr)

end

end Erdos207
