/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawSampledLinkCoverLaw
import ErdosProblems.Erdos207.ResidualSimultaneousLinkLaw

/-! # The totalized link law feeds the corrected three-edge/two-spoke update -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.jointBind_rawSampledLink_numeric
    {Ω O V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {linkLaw : Ω → FiniteLaw (TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later available : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)}
    {p r C b : ℝ≥0} {F : ForbiddenFamilyOn V}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (U : Finset V) (center : Ω → O ↪ V) (K : Ω → O → BipartiteLink V)
    (sigma factor : ℝ≥0) (hC : 1 ≤ C) (hfactor : 1 ≤ factor) (hsigma : sigma ≤ 1)
    (hkn : k ≤ next) (hnonempty : ∀ i, (W.U i).Nonempty)
    (hnew : sigma * p ^ 3 * r ^ 2 ≤ factor * (p / ((W.U k).card : ℝ≥0)))
    (hcenter : ∀ ω, 0 < L.mass ω → ∀ o, (K ω o).center = center ω o)
    (hout : ∀ ω, 0 < L.mass ω → ∀ o, center ω o ∉ U)
    (hleft : ∀ ω, 0 < L.mass ω → ∀ o, (K ω o).left ⊆ U)
    (hright : ∀ ω, 0 < L.mass ω → ∀ o, (K ω o).right ⊆ U)
    (hspokes : ∀ ω, 0 < L.mass ω → ∀ o, (K ω o).SpokesIn (reserve ω))
    (hC4 : ∀ ω, 0 < L.mass ω → ∀ Q,
      (linkLaw ω).probability (fun M ↦ Q ⊆ M) ≤ sigma ^ Q.card)
    (hstruct : ∀ ω, 0 < L.mass ω → (linkLaw ω).SupportedOn fun M ↦
      IsSafeLinkSubfamily F (available ω) (initial ω ∪ later ω) M ∧ IsSimultaneousLinkFamily (K ω) M)
    (hgeometry : ∀ ω, 0 < L.mass ω → ∀ T ∈ available ω,
      tripleEdgeFinset T ⊆ graphEdges G ∧ T.1 ⊆ W.U k) :
    IsResidualGraphStronglyWellDistributed (L.jointBind linkLaw) W next G
      (jointInitial initial) (jointLater later (fun _ M ↦ M))
      p (2 * max (C ^ 5 * factor) 1) b := by
  have hC4' : ∀ ω, 0 < L.mass ω → ∀ Q,
      (linkLaw ω).probability (fun M ↦ Q ⊆ M) ≤ sigma ^ Q.card + (1 : ℝ≥0) ^ Q.card * 0 := by
    intro ω hω Q
    simpa only [mul_zero, add_zero] using hC4 ω hω Q
  have hstruct' : ∀ ω, 0 < L.mass ω → (linkLaw ω).SupportedOn fun M ↦
      IsPackingOn ((initial ω ∪ later ω) ∪ M) ∧ Disjoint (initial ω ∪ later ω) M ∧
        IsSimultaneousLinkFamily (K ω) M ∧
          ∀ T ∈ M, tripleEdgeFinset T ⊆ graphEdges G ∧ T.1 ⊆ W.U k := by
    intro ω hω M hM
    have hs := hstruct ω hω M hM
    exact ⟨hs.1.2.2.1, hs.1.2.1, hs.2, fun T hT ↦ hgeometry ω hω T (hs.1.1 hT)⟩
  simpa only [add_zero] using hstrong.jointBind_simultaneousLink_numeric U center K sigma 1 factor 0
    hC le_rfl hfactor hsigma hkn hnonempty hnew hcenter hout hleft hright hspokes hC4' hstruct'

end

end Erdos207
