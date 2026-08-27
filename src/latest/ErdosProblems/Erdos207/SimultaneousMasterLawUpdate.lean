/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousLinkMasterLaw
import ErdosProblems.Erdos207.StrongWellDistributedAdjoin
import ErdosProblems.Erdos207.MasterIterationUpdate

/-!
# Law-level master update from simultaneous link covers

This file assembles the law-theoretic end of one master stage.  The input law
already contains the internal family `R`.  A conditional simultaneous-link
law adds `L`; the actual master family is `R ∪ L`.  Support is transported to
`IsMasterCoverStep`, while the C4 inclusion estimate for `L` is transported
to strong well-distributedness by the powerset adjoin theorem.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Structural hypotheses on an intermediate state, just before adjoining
its simultaneous link cover. -/
def IsIntermediateLinkState
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V)
    (A I D R : TripleSystemOn V)
    (K : {x : V // x ∉ U} → BipartiteLink V) : Prop :=
  (∀ o, @IsResidualBipartition V _ _ G (Classical.decRel G.Adj)
      R o.1 (K o)) ∧
    R ⊆ A ∧ Disjoint I (D ∪ R)

/-- If both sides of every residual bipartition lie in the next vortex set,
then the preliminary/internal family has already covered every current graph
edge with both endpoints outside that set. -/
lemma IsIntermediateLinkState.covers_internal_of_sides
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V}
    {A I D R : TripleSystemOn V}
    {K : {x : V // x ∉ U} → BipartiteLink V}
    (hstate : IsIntermediateLinkState G U A I D R K)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U) :
    ∀ u v : V, G.Adj u v → u ∉ U → v ∉ U →
      (coveredGraph R).Adj u v := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  intro u v huv hu hv
  by_contra hcovered
  let o : {x : V // x ∉ U} := ⟨u, hu⟩
  have hvres : v ∈ residualNeighbors G R u :=
    mem_residualNeighbors_iff.mpr ⟨huv, hcovered⟩
  have hvunion : v ∈ (K o).left ∪ (K o).right := by
    rw [(hstate.1 o).2.1]
    exact hvres
  rcases mem_union.mp hvunion with hvleft | hvright
  · exact hv (hleft o hvleft)
  · exact hv (hright o hvright)

/-- Conditional link-cover support and the intermediate-state certificate
give support on complete master cover steps for `R ∪ L`. -/
theorem FiniteLaw.SupportedOn.jointBind_masterCoverStep
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {law : FiniteLaw Omega}
    {linkLaw : Omega → FiniteLaw (TripleSystemOn V)}
    {F : ForbiddenFamilyOn V} {U : Finset V}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {K : (omega : Omega) → {x : V // x ∉ U} → BipartiteLink V}
    (hstate : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
        (R omega) (K omega))
    (hlink : ∀ omega, (linkLaw omega).SupportedOn
      (IsSimultaneousLinkCover F (A omega)
        (I omega ∪ (D omega ∪ R omega)) (K omega))) :
    (law.jointBind linkLaw).SupportedOn fun z ↦
      IsMasterCoverStep F (G z.1) U (A z.1) (I z.1) (D z.1)
        (R z.1 ∪ z.2) := by
  have hjoint := hstate.jointBind
    (Q := fun omega L ↦ IsSimultaneousLinkCover F (A omega)
      (I omega ∪ (D omega ∪ R omega)) (K omega) L)
    (fun omega _hstate ↦ hlink omega)
  intro z hz
  have hz' := hjoint z hz
  letI : DecidableRel (G z.1).Adj := Classical.decRel (G z.1).Adj
  exact hz'.2.isMasterCoverStep hz'.1.1 hz'.1.2.1 hz'.1.2.2

/-- The conditional C4 link law closes the strong-distribution update once
the scalar partition inequality has been verified. -/
theorem IsStronglyWellDistributed.jointBind_simultaneousLink
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega}
    {linkLaw : Omega → FiniteLaw (TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {I D R : Omega → TripleSystemOn V}
    {p C b p' C' b' : ℝ≥0}
    (hstrong : IsStronglyWellDistributed law W k I
      (fun omega ↦ D omega ∪ R omega) p C b)
    (addedBound : TripleSystemOn V → ℝ≥0)
    (hC4 : ∀ omega Q,
      (linkLaw omega).probability (fun L ↦ Q ⊆ L) ≤ addedBound Q)
    (hpartition : ∀ (Ifix Dfix : TripleSystemOn V)
      (Efix : Finset (Sym2 V)), Disjoint Ifix Dfix →
      ∀ S ∈ Dfix.powerset,
        addedBound (Dfix \ S) *
          (C ^ (Ifix.card + S.card + Efix.card) *
            (p ^ Efix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k p S + b)) ≤
          C' ^ (Ifix.card + Dfix.card + Efix.card) *
            (p' ^ Efix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W next p' Dfix + b')) :
    IsStronglyWellDistributed (law.jointBind linkLaw) W next
      (fun z ↦ I z.1) (fun z ↦ D z.1 ∪ (R z.1 ∪ z.2))
      p' (2 * C') b' := by
  have h := hstrong.jointBind_adjoin
    (added := fun _omega L ↦ L) addedBound hC4 hpartition
  have hInitial : jointInitial I =
      (fun z : Omega × TripleSystemOn V ↦ I z.1) := rfl
  have hLater :
      jointLater (fun omega ↦ D omega ∪ R omega) (fun _omega L ↦ L) =
        (fun z : Omega × TripleSystemOn V ↦
          D z.1 ∪ (R z.1 ∪ z.2)) := by
    funext z
    simp only [jointLater, union_assoc]
  rw [← hInitial, ← hLater]
  exact h

/-- Once parity and next-stage typicality are supported, the structural and
strong-distribution results above give the complete updated master law. -/
theorem masterIterationGood_of_simultaneousLinkKernel
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega}
    {linkLaw : Omega → FiniteLaw (TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {U : Finset V}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {K : (omega : Omega) → {x : V // x ∉ U} → BipartiteLink V}
    {p eta xi xi' C b : ℝ≥0} {h : ℕ}
    (hU : U = W.U next)
    (heven : HasEvenStageGraphs (law.jointBind linkLaw)
      (fun z ↦ updatedStageGraph (G z.1) U (R z.1 ∪ z.2)))
    (hstrong : IsStronglyWellDistributed (law.jointBind linkLaw) W next
      (fun z ↦ I z.1) (fun z ↦ D z.1 ∪ (R z.1 ∪ z.2)) p C b)
    (hold : law.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W k F (G omega) (A omega)
        (I omega) (D omega) p eta xi h)
    (hstate : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
        (R omega) (K omega))
    (hlink : ∀ omega, (linkLaw omega).SupportedOn
      (IsSimultaneousLinkCover F (A omega)
        (I omega ∪ (D omega ∪ R omega)) (K omega)))
    (htyp : (law.jointBind linkLaw).SupportedOn fun z ↦
      IsIterationTypical W next
        (updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
        (updatedStageAvailable F U (A z.1) (I z.1) (D z.1)
          (R z.1 ∪ z.2)) p eta xi' h) :
    IsMasterIterationGood (law.jointBind linkLaw) W next F
      (fun z ↦ updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
      (fun z ↦ updatedStageAvailable F U (A z.1) (I z.1) (D z.1)
        (R z.1 ∪ z.2))
      (fun z ↦ I z.1) (fun z ↦ D z.1 ∪ (R z.1 ∪ z.2))
      p eta xi' C b h := by
  subst U
  apply masterIterationGood_of_supported_update (next := next) heven hstrong
  · have hjoint := hold.jointBind
      (K := linkLaw) (Q := fun _omega _L ↦ True)
      (fun _omega _h ↦ by
        intro _L _hmass
        trivial)
    intro z hz
    exact (hjoint z hz).1
  · exact hstate.jointBind_masterCoverStep hlink
  · exact htyp

end

end Erdos207
