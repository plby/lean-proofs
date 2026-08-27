/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteSupportedSubtype
import ErdosProblems.Erdos207.ResidualReserveDistribution

/-! # Good-outcome reindexing preserves the corrected distribution laws -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem IsResidualGraphStronglyWellDistributed.supportedSubtype
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Omega → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    {Good : Omega → Prop} [DecidablePred Good] (hgood : L.SupportedOn Good) :
    IsResidualGraphStronglyWellDistributed (L.supportedSubtype hgood) W k G
      (fun x ↦ initial x.val) (fun x ↦ later x.val) p C b := by
  intro Ifix Dfix Efix hdis hE
  change (L.supportedSubtype hgood).probability
    (fun x ↦ ResidualDistributionEvent initial later Ifix Dfix Efix x.val) ≤ _
  rw [FiniteLaw.supportedSubtype_probability]
  exact h Ifix Dfix Efix hdis hE

theorem IsResidualReserveStronglyWellDistributed.supportedSubtype
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Omega → TripleSystemOn V} {reserve : Omega → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (h : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    {Good : Omega → Prop} [DecidablePred Good] (hgood : L.SupportedOn Good) :
    IsResidualReserveStronglyWellDistributed (L.supportedSubtype hgood) W k G
      (fun x ↦ initial x.val) (fun x ↦ later x.val) (fun x ↦ reserve x.val) p r C b := by
  intro Ifix Dfix Efix Rfix hdis hE
  change (L.supportedSubtype hgood).probability
    (fun x ↦ ResidualReserveDistributionEvent initial later reserve Ifix Dfix Efix Rfix x.val) ≤ _
  rw [FiniteLaw.supportedSubtype_probability]
  exact h Ifix Dfix Efix Rfix hdis hE

theorem IsResidualGraphStronglyWellDistributed.conditionSubtype
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Omega → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (Good : Omega → Prop) [DecidablePred Good] (hpos : 0 < L.probability Good) :
    IsResidualGraphStronglyWellDistributed (L.conditionSubtype Good hpos) W k G
      (fun x ↦ initial x.val) (fun x ↦ later x.val) p (C / L.probability Good) b :=
  (h.conditionOn Good hpos).supportedSubtype (L.conditionOn_supported Good hpos)

theorem IsResidualReserveStronglyWellDistributed.conditionSubtype
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Omega → TripleSystemOn V} {reserve : Omega → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (h : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (Good : Omega → Prop) [DecidablePred Good] (hpos : 0 < L.probability Good) :
    IsResidualReserveStronglyWellDistributed (L.conditionSubtype Good hpos) W k G
      (fun x ↦ initial x.val) (fun x ↦ later x.val) (fun x ↦ reserve x.val)
      p r (C / L.probability Good) b :=
  (h.conditionOn Good hpos).supportedSubtype (L.conditionOn_supported Good hpos)

end

end Erdos207
