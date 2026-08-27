/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualReserveDistribution

/-! # Restricting the marked reserve without weakening the full-union residual test -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.restrict_reserve
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell+1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve reserve' : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (h : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (hsub : L.SupportedOn fun ω ↦ reserve' ω ⊆ reserve ω) :
    IsResidualReserveStronglyWellDistributed L W k G initial later reserve' p r C b := by
  intro Ifix Dfix Efix Rfix hdis hE
  apply le_trans _ (h Ifix Dfix Efix Rfix hdis hE)
  apply L.probability_mono_of_supported hsub
  intro ω hω hevent
  exact ⟨hevent.1, hevent.2.trans hω⟩

end

end Erdos207
