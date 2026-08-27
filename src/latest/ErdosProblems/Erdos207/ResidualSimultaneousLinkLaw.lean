/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualForcedReserveNumeric
import ErdosProblems.Erdos207.LinkReserveAccounting

/-! # The genuine simultaneous link law closes the corrected residual update -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.jointBind_simultaneousLink_numeric
    {Ω O V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {linkLaw : Ω → FiniteLaw (TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)}
    {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (U : Finset V) (center : Ω → O ↪ V) (K : Ω → O → BipartiteLink V)
    (alpha J factor delta : ℝ≥0)
    (hC : 1 ≤ C) (hJ : 1 ≤ J) (hfactor : 1 ≤ factor) (halpha : alpha ≤ 1)
    (hkn : k ≤ next) (hnonempty : ∀ i, (W.U i).Nonempty)
    (hnew : alpha * p ^ 3 * r ^ 2 ≤ factor * (p / ((W.U k).card : ℝ≥0)))
    (hcenter : ∀ ω, 0 < L.mass ω → ∀ o, (K ω o).center = center ω o)
    (hout : ∀ ω, 0 < L.mass ω → ∀ o, center ω o ∉ U)
    (hleft : ∀ ω, 0 < L.mass ω → ∀ o, (K ω o).left ⊆ U)
    (hright : ∀ ω, 0 < L.mass ω → ∀ o, (K ω o).right ⊆ U)
    (hspokes : ∀ ω, 0 < L.mass ω → ∀ o, (K ω o).SpokesIn (reserve ω))
    (hC4 : ∀ ω, 0 < L.mass ω → ∀ Q,
      (linkLaw ω).probability (fun M ↦ Q ⊆ M) ≤ alpha ^ Q.card + J ^ Q.card * delta)
    (hstruct : ∀ ω, 0 < L.mass ω → (linkLaw ω).SupportedOn fun M ↦
      IsPackingOn ((initial ω ∪ later ω) ∪ M) ∧
        Disjoint (initial ω ∪ later ω) M ∧ IsSimultaneousLinkFamily (K ω) M ∧
        ∀ T ∈ M, tripleEdgeFinset T ⊆ graphEdges G ∧ T.1 ⊆ W.U k) :
    IsResidualGraphStronglyWellDistributed (L.jointBind linkLaw) W next G
      (jointInitial initial) (jointLater later (fun _ M ↦ M))
      p (2 * max (C ^ 5 * factor) J) (b + delta) := by
  apply hstrong.jointBind_forcedReserve_numeric (fun _ M ↦ M) (familyCrossingEdges U) 2
    alpha J factor delta hC hJ hfactor halpha hkn hnonempty hnew hC4
  · intro ω hω M hM
    have hs := hstruct ω hω M hM
    exact ⟨hs.1, hs.2.1, fun T hT ↦ (hs.2.2.2 T hT).1⟩
  · intro ω hω M hM Q hQM
    have hs := hstruct ω hω M hM
    exact (hs.2.2.1.mono hQM).familyCrossingEdges_subset
      (hcenter ω hω) (hout ω hω) (hleft ω hω) (hright ω hω) (hspokes ω hω)
  · intro ω hω M hM
    have hs := hstruct ω hω M hM
    refine ⟨fun T hT ↦ (hs.2.2.2 T hT).2, ?_⟩
    intro Q hQM
    exact (hs.2.2.1.mono hQM).card_familyCrossingEdges
      (hcenter ω hω) (hout ω hω) (hleft ω hω) (hright ω hω)
      (hs.1.mono (hQM.trans subset_union_right))

end

end Erdos207
