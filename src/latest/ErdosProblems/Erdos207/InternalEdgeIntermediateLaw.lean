/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeIntermediateState
import ErdosProblems.Erdos207.IterationChosenLink

/-!
# Choosing all residual links on the support of the internal law

The internal-edge kernel produces a law, whereas the simultaneous-link
kernel expects one family of bipartite links at every point of the ambient
sample type.  Zero-mass points carry no structural information.  We
therefore choose the canonical residual-link data where it exists and use
the empty link at irrelevant points.  On the support this recovers all the
structural and reserve-support conclusions of the pointwise bridge.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Pointwise hypotheses that turn an internal-edge outcome into the
reserve-supported intermediate state. -/
def InternalOutcomeReady
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (G : Omega -> SimpleGraph V) (U : Finset V)
    (reserve : Omega -> Finset (Sym2 V))
    (F : ForbiddenFamilyOn V)
    (A I D Mstar Q : Omega -> TripleSystemOn V) (omega : Omega) : Prop :=
  (∀ v, Even ((neighborsIn (G omega) univ v).card)) ∧
    G omega <= leaveGraph (I omega ∪ D omega) ∧
    ConsistsOfTriangles (G omega) (A omega) ∧
    Mstar omega ⊆ A omega ∧
    Disjoint (I omega) (D omega ∪ Mstar omega) ∧
    IsPackingOn (I omega ∪ (D omega ∪ Mstar omega)) ∧
    GreedyReachable F (I omega ∪ (D omega ∪ Mstar omega)) (Q omega) ∧
    Q omega ⊆ (I omega ∪ (D omega ∪ Mstar omega)) ∪ A omega ∧
    (∀ e ∈ internalOuterEdges (G omega) U,
      (coveredGraph (Q omega)).Adj e.out.1 e.out.2) ∧
    CoversCrossingOutsideReserve (G omega) U (reserve omega) (Mstar omega)

/-- A total family of residual links.  At a ready outcome it is chosen from
`exists_residualLinks_of_internalOutcome`; elsewhere it is the empty link.
The latter branch is never used at a positive-mass outcome. -/
def internalOutcomeResidualLinks
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (G : Omega -> SimpleGraph V) (U : Finset V)
    (reserve : Omega -> Finset (Sym2 V))
    (F : ForbiddenFamilyOn V)
    (A I D Mstar Q : Omega -> TripleSystemOn V)
    (omega : Omega) : {x : V // x ∉ U} -> BipartiteLink V := by
  classical
  let R := internalStageFamily (I omega) (D omega) (Mstar omega) (Q omega)
  let center := outsideVertexEmbedding U
  by_cases hready : InternalOutcomeReady G U reserve F A I D Mstar Q omega
  · rcases hready with
      ⟨heven, hold, htri, hselected, hdisjoint, hpacking, hreach,
        hQsub, hinternal, hcrossing⟩
    exact Classical.choose (exists_residualLinks_of_internalOutcome
      (F := F) heven hold htri hselected hdisjoint hpacking hreach hQsub
        hinternal hcrossing)
  · exact fun o => emptyBipartiteLink (center o)

/-- The totalized choice agrees with the complete intermediate-state data
at every ready outcome. -/
theorem internalOutcomeResidualLinks_spec
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {G : Omega -> SimpleGraph V} {U : Finset V}
    {reserve : Omega -> Finset (Sym2 V)}
    {F : ForbiddenFamilyOn V}
    {A I D Mstar Q : Omega -> TripleSystemOn V}
    {omega : Omega}
    (hready : InternalOutcomeReady G U reserve F A I D Mstar Q omega) :
    let R := internalStageFamily (I omega) (D omega) (Mstar omega) (Q omega)
    let center := outsideVertexEmbedding U
    IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega) R
        (internalOutcomeResidualLinks G U reserve F A I D Mstar Q omega) ∧
      (∀ o, (internalOutcomeResidualLinks G U reserve F A I D Mstar Q omega o).center =
        center o) ∧
      (∀ o, center o ∉ U) ∧
      (∀ o, (internalOutcomeResidualLinks G U reserve F A I D Mstar Q omega o).left ⊆ U) ∧
      (∀ o, (internalOutcomeResidualLinks G U reserve F A I D Mstar Q omega o).right ⊆ U) ∧
      (∀ o, (internalOutcomeResidualLinks G U reserve F A I D Mstar Q omega o).SpokesIn
        (reserve omega)) := by
  dsimp only
  rw [internalOutcomeResidualLinks, dif_pos hready]
  rcases hready with
    ⟨heven, hold, htri, hselected, hdisjoint, hpacking, hreach,
      hQsub, hinternal, hcrossing⟩
  exact Classical.choose_spec (exists_residualLinks_of_internalOutcome
    (F := F) heven hold htri hselected hdisjoint hpacking hreach hQsub
      hinternal hcrossing)

/-- Law-level form of `internalOutcomeResidualLinks_spec`. -/
theorem FiniteLaw.SupportedOn.internalOutcomeResidualLinks
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {law : FiniteLaw Omega}
    {G : Omega -> SimpleGraph V} {U : Finset V}
    {reserve : Omega -> Finset (Sym2 V)}
    {F : ForbiddenFamilyOn V}
    {A I D Mstar Q : Omega -> TripleSystemOn V}
    (hready : law.SupportedOn
      (InternalOutcomeReady G U reserve F A I D Mstar Q)) :
    let R := fun omega =>
      internalStageFamily (I omega) (D omega) (Mstar omega) (Q omega)
    let center := fun _omega => outsideVertexEmbedding U
    let K := internalOutcomeResidualLinks G U reserve F A I D Mstar Q
    law.SupportedOn (fun omega =>
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
          (R omega) (K omega) ∧
        (∀ o, (K omega o).center = center omega o) ∧
        (∀ o, center omega o ∉ U) ∧
        (∀ o, (K omega o).left ⊆ U) ∧
        (∀ o, (K omega o).right ⊆ U) ∧
        (∀ o, (K omega o).SpokesIn (reserve omega))) := by
  dsimp only
  intro omega hmass
  exact internalOutcomeResidualLinks_spec (hready omega hmass)

end

end Erdos207
