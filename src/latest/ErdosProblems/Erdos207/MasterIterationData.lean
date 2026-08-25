/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StrongWellDistributed
import ErdosProblems.Erdos207.GreedyLegality

/-!
# Finite data and updates for the KSSS master iteration

This file formalizes KSSS Definitions 10.4 and 10.5.  Pointwise stage data
record the packing, forbidden-avoidance, typicality, and availability
conditions.  The law-level predicate adds strong well-distributedness and a
single probability bound for the pointwise conditions.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Restrict an ambient graph to a finite vertex set without changing the
ambient vertex type. -/
def graphRestrictedTo
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (U : Finset V) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ U ∧ v ∈ U
  symm.symm := by
    rintro u v ⟨huv, hu, hv⟩
    exact ⟨huv.symm, hv, hu⟩
  loopless.irrefl := by
    rintro u ⟨huu, -, -⟩
    exact G.loopless.irrefl u huu

lemma graphRestrictedTo_adj
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {U : Finset V}
    {u v : V} :
    (graphRestrictedTo G U).Adj u v ↔ G.Adj u v ∧ u ∈ U ∧ v ∈ U := by
  constructor
  · exact id
  · exact id

lemma graphRestrictedTo_le
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (U : Finset V) :
    graphRestrictedTo G U ≤ G := by
  intro u v huv
  exact (graphRestrictedTo_adj.mp huv).1

lemma graphRestrictedTo_supported
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (U : Finset V) :
    GraphSupportedOn (graphRestrictedTo G U) (U : Set V) := by
  intro u v huv
  exact ⟨(graphRestrictedTo_adj.mp huv).2.1,
    (graphRestrictedTo_adj.mp huv).2.2⟩

/-- The graph remaining at the next stage after selecting `M`: first retain
only edges inside `U`, then remove all edges covered by `M`. -/
def updatedStageGraph
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (M : TripleSystemOn V) :
    SimpleGraph V :=
  graphRestrictedTo G U ⊓ (coveredGraph M)ᶜ

lemma updatedStageGraph_le
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (M : TripleSystemOn V) :
    updatedStageGraph G U M ≤ G := by
  exact le_trans inf_le_left (graphRestrictedTo_le G U)

lemma updatedStageGraph_supported
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (M : TripleSystemOn V) :
    GraphSupportedOn (updatedStageGraph G U M) (U : Set V) := by
  intro u v huv
  exact graphRestrictedTo_supported G U huv.1

lemma updatedStageGraph_disjoint_covered
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (M : TripleSystemOn V) :
    Disjoint (updatedStageGraph G U M) (coveredGraph M) := by
  apply SimpleGraph.disjoint_left.mpr
  intro u v huv hM
  exact huv.2.2 hM

/-- Available triangles retained at the next stage. -/
noncomputable def updatedStageAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (U : Finset V)
    (A I D M : TripleSystemOn V) : TripleSystemOn V :=
  (legalAvailable F (I ∪ (D ∪ M)) A).filter fun T ↦ T.1 ⊆ U

@[simp]
lemma mem_updatedStageAvailable_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {U : Finset V}
    {A I D M : TripleSystemOn V} {T : TripleOn V} :
    T ∈ updatedStageAvailable F U A I D M ↔
      T ∈ A ∧ IsLegalExtension F (I ∪ (D ∪ M)) T ∧ T.1 ⊆ U := by
  classical
  simp [updatedStageAvailable, and_assoc]

lemma updatedStageAvailable_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (U : Finset V)
    (A I D M : TripleSystemOn V) :
    updatedStageAvailable F U A I D M ⊆ A := by
  exact (filter_subset _ _).trans (legalAvailable_subset_right F _ A)

/-- The pointwise conditions IG2--IG4 for one outcome. -/
def IsMasterStagePointwiseGood
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1))
    (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (A I D : TripleSystemOn V)
    (p eta ξ : ℝ≥0) (h : ℕ) : Prop :=
  Disjoint I D ∧
  IsPackingOn (I ∪ D) ∧
  AvoidsForbidden (I ∪ D) F ∧
  IsIterationTypical W k G A p eta ξ h ∧
  G ≤ leaveGraph (I ∪ D) ∧
  ConsistsOfTriangles G A ∧
  ∀ T ∈ A, ¬ CompletesForbidden F (I ∪ D) T

/-- The pointwise master-stage predicate depends on the initial/later
classification only through disjointness and the accumulated selected
family.  This permits the deterministic cover construction to use a
convenient structural partition while the probability law retains the
distinguished initial family from the long first nibble. -/
theorem IsMasterStagePointwiseGood.reclassify
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {A I D I' D' : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (hgood : IsMasterStagePointwiseGood W k F G A I D p eta xi h)
    (hdisjoint : Disjoint I' D')
    (hunion : I' ∪ D' = I ∪ D) :
    IsMasterStagePointwiseGood W k F G A I' D' p eta xi h := by
  rcases hgood with
    ⟨_disjoint, hpacking, havoid, htyp, hleave, htri, hlegal⟩
  refine ⟨hdisjoint, ?_, ?_, htyp, ?_, htri, ?_⟩
  · simpa only [hunion] using hpacking
  · simpa only [hunion] using havoid
  · simpa only [hunion] using hleave
  · simpa only [hunion] using hlegal

/-- All graphs in the stage law satisfy the divisibility parity condition
IG0.  The multiple-of-three condition is recovered from the global leave
when assembling the final absorber certificate. -/
def HasEvenStageGraphs
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (G : Ω → SimpleGraph V) : Prop :=
  L.SupportedOn fun ω ↦ ∀ v : V, Even ((neighborsIn (G ω) univ v).card)

/-- Exact finite-law version of KSSS stage-`k` iteration-goodness. -/
def IsMasterIterationGood
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1))
    (F : ForbiddenFamilyOn V)
    (G : Ω → SimpleGraph V)
    (A I D : Ω → TripleSystemOn V)
    (p eta ξ C b : ℝ≥0) (h : ℕ) : Prop :=
  HasEvenStageGraphs L G ∧
  IsStronglyWellDistributed L W k I D p C b ∧
  1 - ξ ≤ L.probability (fun ω ↦
    IsMasterStagePointwiseGood W k F (G ω) (A ω) (I ω) (D ω)
      p eta ξ h)

/-- The deterministic update of all data after choosing a stage family
`M`. -/
def updateMasterStage
    {Ω V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V)
    (G : Ω → SimpleGraph V)
    (A I D M : Ω → TripleSystemOn V) (ω : Ω) :
    SimpleGraph V × TripleSystemOn V × TripleSystemOn V × TripleSystemOn V :=
  (updatedStageGraph (G ω) (W.U next) (M ω),
    updatedStageAvailable F (W.U next) (A ω) (I ω) (D ω) (M ω),
    I ω, D ω ∪ M ω)

@[simp]
lemma updateMasterStage_graph
    {Ω V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V)
    (G : Ω → SimpleGraph V) (A I D M : Ω → TripleSystemOn V) (ω : Ω) :
    (updateMasterStage W next F G A I D M ω).1 =
      updatedStageGraph (G ω) (W.U next) (M ω) := rfl

end

end Erdos207
