/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterCoverDownExtraction
import ErdosProblems.Erdos207.InitialMasterLaw

/-!
# Compressing a master law to a fixed state space

The three random parts of one master step naturally produce a nested product
sample space.  Iterating such products would make the sample-space type depend
on the entire history.  This file pushes every completed stage forward to the
fixed finite type containing just its current graph, available family, and the
initial/later selected families.  All master-iteration, selection, and
cumulative-coverage assertions are invariant under this pushforward.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The data retained between two consecutive master stages.  A reducible
product avoids storing a second copy of the ambient `DecidableEq` instance. -/
abbrev MasterStateOn (V : Type*) [DecidableEq V] :=
  SimpleGraph V × TripleSystemOn V × TripleSystemOn V × TripleSystemOn V

noncomputable instance MasterStateOn.instDecidableEq
    {V : Type*} [DecidableEq V] : DecidableEq (MasterStateOn V) :=
  Classical.decEq _

def MasterStateOn.graph
    {V : Type*} [DecidableEq V] (state : MasterStateOn V) : SimpleGraph V :=
  state.1

def MasterStateOn.available
    {V : Type*} [DecidableEq V] (state : MasterStateOn V) :
    TripleSystemOn V :=
  state.2.1

def MasterStateOn.initial
    {V : Type*} [DecidableEq V] (state : MasterStateOn V) :
    TripleSystemOn V :=
  state.2.2.1

def MasterStateOn.later
    {V : Type*} [DecidableEq V] (state : MasterStateOn V) :
    TripleSystemOn V :=
  state.2.2.2

/-- Package four state functions into the fixed master-state type. -/
def packMasterState
    {Omega V : Type*} [DecidableEq V]
    (G : Omega → SimpleGraph V)
    (A I D : Omega → TripleSystemOn V) (omega : Omega) :
    MasterStateOn V :=
  (G omega, A omega, I omega, D omega)

@[simp] lemma packMasterState_graph
    {Omega V : Type*} [DecidableEq V]
    (G : Omega → SimpleGraph V)
    (A I D : Omega → TripleSystemOn V) (omega : Omega) :
    MasterStateOn.graph (packMasterState G A I D omega) = G omega := rfl

@[simp] lemma packMasterState_available
    {Omega V : Type*} [DecidableEq V]
    (G : Omega → SimpleGraph V)
    (A I D : Omega → TripleSystemOn V) (omega : Omega) :
    MasterStateOn.available (packMasterState G A I D omega) = A omega := rfl

@[simp] lemma packMasterState_initial
    {Omega V : Type*} [DecidableEq V]
    (G : Omega → SimpleGraph V)
    (A I D : Omega → TripleSystemOn V) (omega : Omega) :
    MasterStateOn.initial (packMasterState G A I D omega) = I omega := rfl

@[simp] lemma packMasterState_later
    {Omega V : Type*} [DecidableEq V]
    (G : Omega → SimpleGraph V)
    (A I D : Omega → TripleSystemOn V) (omega : Omega) :
    MasterStateOn.later (packMasterState G A I D omega) = D omega := rfl

/-- A completed master law may be pushed forward to the fixed master-state
space without changing any clause of iteration-goodness. -/
theorem IsMasterIterationGood.map_packMasterState
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq Omega] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hgood : IsMasterIterationGood law W k F G A I D
      p eta xi C b h) :
    IsMasterIterationGood
      (law.map (packMasterState G A I D)) W k F
      MasterStateOn.graph MasterStateOn.available
      MasterStateOn.initial MasterStateOn.later
      p eta xi C b h := by
  let f := packMasterState G A I D
  have heven : HasEvenStageGraphs (law.map f) MasterStateOn.graph := by
    exact hgood.1.map f (fun omega homega ↦ by
      simpa [f, packMasterState, MasterStateOn.graph] using homega)
  have hstrong : IsStronglyWellDistributed (law.map f) W k
      MasterStateOn.initial MasterStateOn.later p C b := by
    intro Ifix Dfix Efix hdisjoint
    rw [FiniteLaw.probability_map]
    have hevent :
        (fun omega ↦ StrongDistributionEvent MasterStateOn.initial
          MasterStateOn.later Ifix Dfix Efix (f omega)) =
        StrongDistributionEvent I D Ifix Dfix Efix := by
      funext omega
      rfl
    rw [hevent]
    exact hgood.2.1 Ifix Dfix Efix hdisjoint
  have hpoint :
      1 - xi ≤ (law.map f).probability (fun state ↦
        IsMasterStagePointwiseGood W k F
          (MasterStateOn.graph state) (MasterStateOn.available state)
          (MasterStateOn.initial state) (MasterStateOn.later state)
          p eta xi h) := by
    rw [FiniteLaw.probability_map]
    simpa only [f, packMasterState_graph, packMasterState_available,
      packMasterState_initial, packMasterState_later] using hgood.2.2
  exact ⟨heven, hstrong, hpoint⟩

/-- Support of the selected-family containment is preserved by master-state
compression. -/
theorem FiniteLaw.SupportedOn.map_packMasterState_selected
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq Omega] [DecidableEq V]
    {law : FiniteLaw Omega}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {ambient : TripleSystemOn V}
    (hselected : law.SupportedOn fun omega ↦ I omega ∪ D omega ⊆ ambient) :
    (law.map (packMasterState G A I D)).SupportedOn fun state ↦
      MasterStateOn.initial state ∪ MasterStateOn.later state ⊆ ambient := by
  exact hselected.map (packMasterState G A I D)
    (fun omega homega ↦ by simpa using homega)

/-- Support of cumulative coverage is preserved by master-state
compression. -/
theorem FiniteLaw.SupportedOn.map_packMasterState_coverage
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq Omega] [DecidableEq V]
    {law : FiniteLaw Omega}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {Gzero : SimpleGraph V}
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph Gzero (G omega) (I omega) (D omega)) :
    (law.map (packMasterState G A I D)).SupportedOn fun state ↦
      CoversOriginalGraph Gzero (MasterStateOn.graph state)
        (MasterStateOn.initial state) (MasterStateOn.later state) := by
  exact hcover.map (packMasterState G A I D)
    (fun omega homega ↦ by simpa using homega)

/-- A constant description of the ambient available family is preserved by
master-state compression. -/
theorem FiniteLaw.SupportedOn.map_packMasterState_available_eq
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq Omega] [DecidableEq V]
    {law : FiniteLaw Omega}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {ambient : TripleSystemOn V}
    (havailable : law.SupportedOn fun omega ↦ A omega = ambient) :
    (law.map (packMasterState G A I D)).SupportedOn fun state ↦
      MasterStateOn.available state = ambient := by
  exact havailable.map (packMasterState G A I D)
    (fun omega homega ↦ by simpa using homega)

/-- The fixed-state invariant carried by the finite vortex induction. -/
def IsCompressedMasterLaw
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (law : FiniteLaw (MasterStateOn V))
    (W : Vortex V ell) (k : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (Gzero : SimpleGraph V)
    (ambient : TripleSystemOn V)
    (p eta xi C b : ℝ≥0) (h : ℕ) : Prop :=
  IsMasterIterationGood law W k F
      MasterStateOn.graph MasterStateOn.available
      MasterStateOn.initial MasterStateOn.later
      p eta xi C b h ∧
    law.SupportedOn (fun state ↦
      MasterStateOn.available state ⊆ ambient) ∧
    law.SupportedOn (fun state ↦
      MasterStateOn.initial state ∪ MasterStateOn.later state ⊆ ambient) ∧
    law.SupportedOn (fun state ↦
      CoversOriginalGraph Gzero (MasterStateOn.graph state)
        (MasterStateOn.initial state) (MasterStateOn.later state)) ∧
    law.SupportedOn (fun state ↦ MasterStateOn.graph state ≤ Gzero) ∧
    law.SupportedOn (fun state ↦
      GraphSupportedOn (MasterStateOn.graph state) (W.U k : Set V))

/-- Compress any law satisfying the four induction clauses. -/
theorem IsMasterIterationGood.compress
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq Omega] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {Gzero : SimpleGraph V}
    {ambient : TripleSystemOn V}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hgood : IsMasterIterationGood law W k F G A I D
      p eta xi C b h)
    (havailable : law.SupportedOn fun omega ↦ A omega ⊆ ambient)
    (hselected : law.SupportedOn fun omega ↦ I omega ∪ D omega ⊆ ambient)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph Gzero (G omega) (I omega) (D omega))
    (hsub : law.SupportedOn fun omega ↦ G omega ≤ Gzero)
    (hsupport : law.SupportedOn fun omega ↦
      GraphSupportedOn (G omega) (W.U k : Set V)) :
    IsCompressedMasterLaw (law.map (packMasterState G A I D))
      W k F Gzero ambient p eta xi C b h := by
  refine ⟨hgood.map_packMasterState, ?_,
    hselected.map_packMasterState_selected,
    hcover.map_packMasterState_coverage, ?_, ?_⟩
  exact havailable.map (packMasterState G A I D)
    (fun omega homega ↦ by simpa using homega)
  exact hsub.map (packMasterState G A I D)
    (fun omega homega ↦ by simpa using homega)
  exact hsupport.map (packMasterState G A I D)
    (fun omega homega ↦ by simpa using homega)

/-- The deterministic initial state in the fixed sample space. -/
def initialMasterState
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) : MasterStateOn V :=
  (G, A, ∅, ∅)

/-- A pointwise-good empty initial state starts the compressed induction. -/
theorem initialCompressedMasterLaw_of_pointwise
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {Gzero : SimpleGraph V}
    {ambient : TripleSystemOn V}
    {eta xi : ℝ≥0} {h : ℕ}
    (heven : ∀ v : V, Even ((neighborsIn Gzero univ v).card))
    (hsupport : GraphSupportedOn Gzero (W.U k : Set V))
    (hpoint : IsMasterStagePointwiseGood W k F Gzero ambient ∅ ∅
      1 eta xi h) :
    IsCompressedMasterLaw
      (FiniteLaw.pure (initialMasterState Gzero ambient))
      W k F Gzero ambient 1 eta xi 1 0 h := by
  let L0 : FiniteLaw (PUnit.{1}) := FiniteLaw.pure PUnit.unit
  have hgood0 : IsMasterIterationGood L0 W k F
      (fun _ : PUnit.{1} ↦ Gzero) (fun _ : PUnit.{1} ↦ ambient)
      (fun _ : PUnit.{1} ↦ (∅ : TripleSystemOn V))
      (fun _ : PUnit.{1} ↦ (∅ : TripleSystemOn V))
      1 eta xi 1 0 h :=
    initialMasterIterationGood_of_pointwise heven hpoint
  have havailable0 : L0.SupportedOn fun _ : PUnit.{1} ↦ ambient ⊆ ambient :=
    FiniteLaw.supportedOn_pure _ Subset.rfl
  have hselected0 : L0.SupportedOn fun _ : PUnit.{1} ↦
      (∅ : TripleSystemOn V) ∪ ∅ ⊆ ambient :=
    FiniteLaw.supportedOn_pure _ (by simp)
  have hcover0 : L0.SupportedOn fun _ : PUnit.{1} ↦
      CoversOriginalGraph Gzero Gzero
        (∅ : TripleSystemOn V) ∅ := by
    apply FiniteLaw.supportedOn_pure
    intro u v huv
    exact Or.inr huv
  have hsupport0 : L0.SupportedOn fun _ : PUnit.{1} ↦
      GraphSupportedOn Gzero (W.U k : Set V) :=
    FiniteLaw.supportedOn_pure _ hsupport
  have hsub0 : L0.SupportedOn fun _ : PUnit.{1} ↦ Gzero ≤ Gzero :=
    FiniteLaw.supportedOn_pure _ le_rfl
  have hcompressed := hgood0.compress havailable0 hselected0 hcover0
    hsub0 hsupport0
  have hmap : L0.map
      (packMasterState (fun _ : PUnit.{1} ↦ Gzero)
        (fun _ : PUnit.{1} ↦ ambient)
        (fun _ : PUnit.{1} ↦ (∅ : TripleSystemOn V))
        (fun _ : PUnit.{1} ↦ (∅ : TripleSystemOn V))) =
      FiniteLaw.pure (initialMasterState Gzero ambient) := by
    apply FiniteLaw.ext
    intro state
    simp [L0, FiniteLaw.map, FiniteLaw.pure, packMasterState,
      initialMasterState]
    by_cases hstate : state = (Gzero, ambient, ∅, ∅)
    · simp [hstate]
    · simp [hstate, Ne.symm hstate]
  rw [hmap] at hcompressed
  exact hcompressed

/-- Variant of `initialCompressedMasterLaw_of_pointwise` in which the
pointwise initial available family is only a subset of the fixed ambient
family recorded by the compressed induction. -/
theorem initialCompressedMasterLaw_of_pointwise_subset
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {Gzero : SimpleGraph V}
    {A ambient : TripleSystemOn V}
    {eta xi : ℝ≥0} {h : ℕ}
    (heven : ∀ v : V, Even ((neighborsIn Gzero univ v).card))
    (hsupport : GraphSupportedOn Gzero (W.U k : Set V))
    (hA : A ⊆ ambient)
    (hpoint : IsMasterStagePointwiseGood W k F Gzero A ∅ ∅
      1 eta xi h) :
    IsCompressedMasterLaw
      (FiniteLaw.pure (initialMasterState Gzero A))
      W k F Gzero ambient 1 eta xi 1 0 h := by
  let L0 : FiniteLaw (PUnit.{1}) := FiniteLaw.pure PUnit.unit
  have hgood0 : IsMasterIterationGood L0 W k F
      (fun _ : PUnit.{1} ↦ Gzero) (fun _ : PUnit.{1} ↦ A)
      (fun _ : PUnit.{1} ↦ (∅ : TripleSystemOn V))
      (fun _ : PUnit.{1} ↦ (∅ : TripleSystemOn V))
      1 eta xi 1 0 h :=
    initialMasterIterationGood_of_pointwise heven hpoint
  have havailable0 : L0.SupportedOn fun _ : PUnit.{1} ↦ A ⊆ ambient :=
    FiniteLaw.supportedOn_pure _ hA
  have hselected0 : L0.SupportedOn fun _ : PUnit.{1} ↦
      (∅ : TripleSystemOn V) ∪ ∅ ⊆ ambient :=
    FiniteLaw.supportedOn_pure _ (by simp)
  have hcover0 : L0.SupportedOn fun _ : PUnit.{1} ↦
      CoversOriginalGraph Gzero Gzero (∅ : TripleSystemOn V) ∅ := by
    apply FiniteLaw.supportedOn_pure
    intro u v huv
    exact Or.inr huv
  have hsupport0 : L0.SupportedOn fun _ : PUnit.{1} ↦
      GraphSupportedOn Gzero (W.U k : Set V) :=
    FiniteLaw.supportedOn_pure _ hsupport
  have hsub0 : L0.SupportedOn fun _ : PUnit.{1} ↦ Gzero ≤ Gzero :=
    FiniteLaw.supportedOn_pure _ le_rfl
  have hcompressed := hgood0.compress havailable0 hselected0 hcover0
    hsub0 hsupport0
  have hmap : L0.map
      (packMasterState (fun _ : PUnit.{1} ↦ Gzero)
        (fun _ : PUnit.{1} ↦ A)
        (fun _ : PUnit.{1} ↦ (∅ : TripleSystemOn V))
        (fun _ : PUnit.{1} ↦ (∅ : TripleSystemOn V))) =
      FiniteLaw.pure (initialMasterState Gzero A) := by
    apply FiniteLaw.ext
    intro state
    simp [L0, FiniteLaw.map, FiniteLaw.pure, packMasterState,
      initialMasterState]
    by_cases hstate : state = (Gzero, A, ∅, ∅)
    · simp [hstate]
    · simp [hstate, Ne.symm hstate]
  rw [hmap] at hcompressed
  exact hcompressed

/-- A completed cover step preserves the three deterministic induction
invariants; compressing its joint law therefore produces the next fixed-state
master law. -/
theorem compressMasterUpdate
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {kernel : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {Gzero : SimpleGraph V}
    {ambient : TripleSystemOn V}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {M : Omega × Xi → TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hgood : IsMasterIterationGood (law.jointBind kernel) W next F
      (fun z ↦ updatedStageGraph (G z.1) (W.U next) (M z))
      (fun z ↦ updatedStageAvailable F (W.U next)
        (A z.1) (I z.1) (D z.1) (M z))
      (fun z ↦ I z.1) (fun z ↦ D z.1 ∪ M z)
      p eta xi C b h)
    (hstep : (law.jointBind kernel).SupportedOn fun z ↦
      IsMasterCoverStep F (G z.1) (W.U next)
        (A z.1) (I z.1) (D z.1) (M z))
    (havailable : law.SupportedOn fun omega ↦ A omega ⊆ ambient)
    (hselected : law.SupportedOn fun omega ↦
      I omega ∪ D omega ⊆ ambient)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph Gzero (G omega) (I omega) (D omega))
    (hsub : law.SupportedOn fun omega ↦ G omega ≤ Gzero) :
    IsCompressedMasterLaw
      ((law.jointBind kernel).map (packMasterState
        (fun z ↦ updatedStageGraph (G z.1) (W.U next) (M z))
        (fun z ↦ updatedStageAvailable F (W.U next)
          (A z.1) (I z.1) (D z.1) (M z))
        (fun z ↦ I z.1) (fun z ↦ D z.1 ∪ M z)))
      W next F Gzero ambient p eta xi C b h := by
  let joint := law.jointBind kernel
  have havailableJoint : joint.SupportedOn fun z ↦ A z.1 ⊆ ambient := by
    have hbind := havailable.jointBind (K := kernel)
      (Q := fun _omega _xi ↦ True)
      (fun _omega _havailable ↦ by intro _xi _hmass; trivial)
    exact fun z hz ↦ (hbind z hz).1
  have hselectedJoint : joint.SupportedOn fun z ↦
      I z.1 ∪ D z.1 ⊆ ambient := by
    have hbind := hselected.jointBind (K := kernel)
      (Q := fun _omega _xi ↦ True)
      (fun _omega _hselected ↦ by intro _xi _hmass; trivial)
    exact fun z hz ↦ (hbind z hz).1
  have hcoverJoint : joint.SupportedOn fun z ↦
      CoversOriginalGraph Gzero (G z.1) (I z.1) (D z.1) := by
    have hbind := hcover.jointBind (K := kernel)
      (Q := fun _omega _xi ↦ True)
      (fun _omega _hcover ↦ by intro _xi _hmass; trivial)
    exact fun z hz ↦ (hbind z hz).1
  have hnewAvailable : joint.SupportedOn fun z ↦
      updatedStageAvailable F (W.U next)
          (A z.1) (I z.1) (D z.1) (M z) ⊆ ambient := by
    intro z hz
    exact (updatedStageAvailable_subset F (W.U next)
      (A z.1) (I z.1) (D z.1) (M z)).trans
        (havailableJoint z hz)
  have hnewSelected : joint.SupportedOn fun z ↦
      I z.1 ∪ (D z.1 ∪ M z) ⊆ ambient := by
    intro z hz T hT
    rcases mem_union.mp hT with hTI | hTDM
    · exact hselectedJoint z hz (mem_union_left (D z.1) hTI)
    · rcases mem_union.mp hTDM with hTD | hTM
      · exact hselectedJoint z hz (mem_union_right (I z.1) hTD)
      · exact havailableJoint z hz ((hstep z hz).selected hTM)
  have hnewCover : joint.SupportedOn fun z ↦
      CoversOriginalGraph Gzero
        (updatedStageGraph (G z.1) (W.U next) (M z))
        (I z.1) (D z.1 ∪ M z) := by
    intro z hz
    exact (hcoverJoint z hz).updated (hstep z hz)
  have hnewSupport : joint.SupportedOn fun z ↦
      GraphSupportedOn
        (updatedStageGraph (G z.1) (W.U next) (M z))
        (W.U next : Set V) := by
    intro z _hz
    exact updatedStageGraph_supported (G z.1) (W.U next) (M z)
  have hsubJoint : joint.SupportedOn fun z ↦ G z.1 ≤ Gzero := by
    have hbind := hsub.jointBind (K := kernel)
      (Q := fun _omega _xi ↦ True)
      (fun _omega _hsub ↦ by intro _xi _hmass; trivial)
    exact fun z hz ↦ (hbind z hz).1
  have hnewSub : joint.SupportedOn fun z ↦
      updatedStageGraph (G z.1) (W.U next) (M z) ≤ Gzero := by
    intro z hz
    exact (updatedStageGraph_le (G z.1) (W.U next) (M z)).trans
      (hsubJoint z hz)
  exact hgood.compress hnewAvailable hnewSelected hnewCover hnewSub hnewSupport

/-- At the terminal vortex level, a compressed iteration-good law is already
an outside packing: its support invariant says that the current remainder is
entirely contained in the flexible set. -/
theorem IsCompressedMasterLaw.exists_ksssOutsidePacking
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (MasterStateOn V)} {W : Vortex V ell}
    {k : Fin (ell + 1)} {q : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B : TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hmaster : IsCompressedMasterLaw law W k
      (absorberErdosForbiddenConfigurationsOn q B)
      (graphDifference (SimpleGraph.completeGraph V) H)
      (outsideAvailableTriangles H B) p eta xi C b h)
    (hX : W.U k = X) (hxi : xi < 1) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  apply exists_ksssOutsidePacking_of_finalMasterIterationGood
    hmaster.1 hxi hmaster.2.2.1 hmaster.2.2.2.1
  intro state hmass
  simpa only [hX] using hmaster.2.2.2.2.2 state hmass

/-- Conditioning a compressed law on its pointwise-good event preserves all
four deterministic induction invariants and exposes pointwise goodness on
the whole support. -/
theorem IsCompressedMasterLaw.conditionPointwise
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (MasterStateOn V)} {W : Vortex V ell}
    {k : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hmaster : IsCompressedMasterLaw law W k F Gzero ambient
      p eta xi C b h)
    (hxi : xi < 1) :
    let Good := masterPointwiseGoodEvent W k F
      MasterStateOn.graph MasterStateOn.available
      MasterStateOn.initial MasterStateOn.later p eta xi h
    let Lc := conditionedMasterLaw law W k F
      MasterStateOn.graph MasterStateOn.available
      MasterStateOn.initial MasterStateOn.later p eta xi C b h hxi
      hmaster.1
    IsCompressedMasterLaw Lc W k F Gzero ambient p eta xi
        (C / law.probability Good) b h ∧
      Lc.SupportedOn Good := by
  dsimp only
  let Good := masterPointwiseGoodEvent W k F
    MasterStateOn.graph MasterStateOn.available
    MasterStateOn.initial MasterStateOn.later p eta xi h
  have hpos : 0 < law.probability Good :=
    (tsub_pos_iff_lt.mpr hxi).trans_le hmaster.1.2.2
  let Lc := law.conditionOn Good hpos
  have hgood := hmaster.1.conditionPointwise hxi
  have havailable := hmaster.2.1.conditionOn hpos
  have hselected := hmaster.2.2.1.conditionOn hpos
  have hcover := hmaster.2.2.2.1.conditionOn hpos
  have hsub := hmaster.2.2.2.2.1.conditionOn hpos
  have hsupport := hmaster.2.2.2.2.2.conditionOn hpos
  have hGoodSupport : Lc.SupportedOn Good :=
    law.conditionOn_supported Good hpos
  refine ⟨?_, hGoodSupport⟩
  simpa only [Lc, Good, conditionedMasterLaw] using
    (show IsCompressedMasterLaw Lc W k F Gzero ambient p eta xi
      (C / law.probability Good) b h from
      ⟨hgood, havailable, hselected, hcover, hsub, hsupport⟩)

end

end Erdos207
