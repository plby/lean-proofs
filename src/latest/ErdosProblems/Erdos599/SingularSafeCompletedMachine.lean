/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularProtectedDeltaLift
import ErdosProblems.Erdos599.SingularSafeDesignatedLinkage
import ErdosProblems.Erdos599.SingularTargetRowMachine
import ErdosProblems.Erdos599.SingularPendingReentry

/-!
# A safe-completed target-row machine

This module gives a construction-specific positive replacement for the
false arbitrary-row successor used in the published proof of Assertion
9.17.  A state does not retain an arbitrary half-way row.  It retains a
target linkage `completed` for exactly the sources already requested, and
the certificate that deleting its whole carrier leaves an unhindered web.

At a successor, only the newly requested sources are linked in that residual
web.  The lifted new paths are disjoint from the old carrier.  Thus old
completed paths are frozen, old trivial paths at newly requested sources are
extended, and the new residual is again unhindered.  This proves literal
`ForwardExtension`, including the branch which is false for an arbitrary
half-way linkage.

The sole selection input is `SafeBatchSelectionBelow`: a set-valued version
of the safe-link theorem for every designated set of size below `kappa`.
Theorem 6.1 proves its singleton instance.  Existing lower cardinal
linkability does not by itself prove the deletion-unhindered field; keeping
the premise explicit prevents the omitted compatibility argument from being
hidden in the row recursion.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeCompletedMachine

open SingularExtension SingularMatrix SingularTargetRowMachine
  SingularPendingReentry SingularSafeDesignatedLinkage
  RegularProtectedDeltaLift

universe u

variable {V : Type u}

/-- A safely completed batch in a vertex-deleted residual of `G`. -/
structure SafeBatchInDeletion (G : DWeb V) (X A : Set V) where
  paths : Set (G.delete X).DPath
  linkage : IsLinkageBetween (G.delete X) A (G.delete X).target paths
  residual : ((G.delete X).delete ((G.delete X).vertexSet paths)).IsUnhindered

namespace SafeBatchInDeletion

/-- `SafeBatchInDeletion` is exactly the ambient safe-designated selector,
viewed in a particular deleted residual.  Keeping this adapter explicit lets
the finite and full-source constructions from `SingularSafeDesignatedLinkage`
feed the completed-row machine without any deletion reassociation. -/
def ofSafeDesignated
    {G : DWeb V} {X A : Set V}
    (S : SafeDesignatedLinkage (G.delete X) A) :
    SafeBatchInDeletion G X A where
  paths := S.paths
  linkage := S.linkage
  residual := S.residual_unhindered

/-- Forget the outer ambient presentation of a deleted safe batch. -/
def toSafeDesignated
    {G : DWeb V} {X A : Set V}
    (S : SafeBatchInDeletion G X A) :
    SafeDesignatedLinkage (G.delete X) A where
  paths := S.paths
  linkage := S.linkage
  residual_unhindered := S.residual

end SafeBatchInDeletion

/-- The exact additional selection theorem which makes the completed-row
recursion future-proof.  It is deliberately restricted to residuals of the
one ambient web used by the singular construction. -/
def SafeBatchSelectionBelow (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (X A : Set V), (G.delete X).IsUnhindered →
    A ⊆ (G.delete X).source → #A < kappa →
      Nonempty (SafeBatchInDeletion G X A)

/-- A target linkage together with the ambient residual-safety certificate
needed to add another disjoint target batch later. -/
structure SafeCompletedState (G : DWeb V) where
  sources : Set V
  sources_subset : sources ⊆ G.source
  completed : Set G.DPath
  linkage : IsLinkageBetween G sources G.target completed
  residual : (G.delete (G.vertexSet completed)).IsUnhindered

namespace SafeCompletedState

variable {G : DWeb V}

/-- Fill every source not yet completed with its trivial path. -/
def displayed (S : SafeCompletedState G) : Set G.DPath :=
  S.completed ∪ G.trivialPath '' (G.source \ S.sources)

theorem displayed_isWarp (hNorm : G.IsNormalized)
    (S : SafeCompletedState G) : G.IsWarp S.displayed := by
  apply Set.PairwiseDisjoint.union S.linkage.isWarp
    (G.isWarp_trivialPaths (G.source \ S.sources))
  intro p hp q hq _hpq
  obtain ⟨x, hx, rfl⟩ := hq
  rw [G.support_trivialPath]
  apply Set.disjoint_singleton_right.2
  intro hxp
  have hxeq : x = p.initial :=
    hNorm.eq_initial_of_mem_path p hxp hx.1
  have hpinitial : p.initial ∈ S.sources := by
    rw [← S.linkage.initialSet_eq]
    exact ⟨p, hp, rfl⟩
  exact hx.2 (hxeq.symm ▸ hpinitial)

theorem displayed_finiteCharacter (S : SafeCompletedState G) :
    G.HasFiniteCharacter S.displayed := by
  apply SingularContinuation.finiteCharacter_union G
    S.linkage.finiteCharacter
  rintro p ⟨x, _hx, rfl⟩
  exact ⟨DirectedPath.FinitePath.trivial G.graph x, rfl⟩

theorem displayed_initialSet (S : SafeCompletedState G) :
    G.initialSet S.displayed = G.source := by
  unfold displayed
  rw [G.initialSet_union, G.initialSet_trivialPaths,
    S.linkage.initialSet_eq, Set.union_comm,
    Set.sdiff_union_of_subset S.sources_subset]

theorem displayed_links (S : SafeCompletedState G) :
    LinksToTarget G S.displayed S.sources := by
  have hlinks := linksToTarget_of_linkageToTarget S.linkage
  intro a ha
  obtain ⟨p, hp, hpa⟩ := hlinks a ha
  exact ⟨p, Or.inl hp, hpa⟩

/-- The target-row stage displayed by a family of safely completed states. -/
def stage {I : Type u} (hNorm : G.IsNormalized)
    (S : I → SafeCompletedState G) :
    TargetRowStage G I where
  sources i := (S i).sources
  paths i := (S i).displayed
  isWarp i := displayed_isWarp hNorm (S i)
  finiteCharacter i := (S i).displayed_finiteCharacter
  initialSet i := (S i).displayed_initialSet
  links i := (S i).displayed_links

end SafeCompletedState

/-- Vertex deletion preserves the normalized-edge condition. -/
theorem isNormalized_delete {G : DWeb V} (hNorm : G.IsNormalized)
    (X : Set V) : (G.delete X).IsNormalized := by
  intro x y hxy
  refine ⟨?_, ?_⟩
  · exact fun hy ↦ (hNorm hxy.1).1 hy.1
  · exact fun hx ↦ (hNorm hxy.1).2 hx.1

namespace SafeBatchInDeletion

/-- Every finite request set has the exact safe batch needed by the machine.
This is the unconditional finite branch of the selection problem. -/
theorem exists_finite
    {G : DWeb V} (hNorm : G.IsNormalized)
    {X A : Set V} (hresidual : (G.delete X).IsUnhindered)
    (hAfinite : A.Finite) (hA : A ⊆ (G.delete X).source) :
    Nonempty (SafeBatchInDeletion G X A) := by
  obtain ⟨S⟩ := SingularSafeDesignatedLinkage.exists_finite
    (G.delete X) (isNormalized_delete hNorm X) hresidual hAfinite hA
  exact ⟨ofSafeDesignated S⟩

/-- When the request is the whole residual source and that source is below
the induction cardinal, the lower extension clause gives a safe batch: its
carrier deletes every remaining source. -/
theorem exists_full_of_source_below
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {G : DWeb V} {X : Set V}
    (hresidual : (G.delete X).IsUnhindered)
    (hsource : #(G.delete X).source < kappa) :
    Nonempty (SafeBatchInDeletion G X (G.delete X).source) := by
  obtain ⟨S⟩ := SingularSafeDesignatedLinkage.exists_full_of_source_below
    hlower hresidual hsource
  exact ⟨ofSafeDesignated S⟩

end SafeBatchInDeletion

/-- Lifting a deleted-web family does not change its total vertex set. -/
theorem vertexSet_liftDeleteFamily
    (G : DWeb V) (X : Set V) (W : Set (G.delete X).DPath) :
    G.vertexSet (G.liftDeleteFamily X W) = (G.delete X).vertexSet W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hxp⟩
    exact ⟨q, hq, by simpa using hxp⟩
  · rintro ⟨q, hq, hxq⟩
    exact ⟨G.liftDeletePath X q, ⟨q, hq, rfl⟩, by simpa using hxq⟩

/-- Sources outside a completed linkage survive deletion of its carrier.
Normalization is the essential endpoint-purity input. -/
theorem sdiff_sources_subset_delete_source
    {G : DWeb V} (hNorm : G.IsNormalized)
    (S : SafeCompletedState G) {B : Set V} (hB : B ⊆ G.source) :
    B \ S.sources ⊆ (G.delete (G.vertexSet S.completed)).source := by
  rintro b ⟨hbB, hbOld⟩
  refine ⟨hB hbB, ?_⟩
  rintro ⟨p, hpP, hbp⟩
  have hbeq : b = p.initial :=
    hNorm.eq_initial_of_mem_path p hbp (hB hbB)
  apply hbOld
  rw [hbeq]
  rw [← S.linkage.initialSet_eq]
  exact ⟨p, hpP, rfl⟩

/-- In a normalized web, a finite path whose endpoints lie on the two
distinguished sides is automatically endpoint-pure for every intermediate
source set containing its start. -/
theorem isPathBetween_of_normalized
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source)
    (q : DirectedPath.FinitePath G.graph)
    (hstart : q.start ∈ A) (hfinish : q.finish ∈ G.target) :
    IsPathBetween G A G.target (.inl q) := by
  refine ⟨q, rfl, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxq, hxA | hxT⟩
      · have hxs : x = q.start :=
          hNorm.eq_start_of_mem_walk q.walk hxq (hA hxA)
        simp [hxs]
      · have hxf : x = q.finish :=
          hNorm.eq_finish_of_mem_walk q.walk hxq hxT
        simp [hxf]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨q.start_mem_support, Or.inl hstart⟩
      · exact ⟨q.finish_mem_support, Or.inr hfinish⟩
  · ext x
    constructor
    · rintro ⟨hxq, hxA⟩
      have hxs : x = q.start :=
        hNorm.eq_start_of_mem_walk q.walk hxq (hA hxA)
      exact Set.mem_singleton_iff.2 hxs
    · intro hx
      have hxs : x = q.start := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨q.start_mem_support, hstart⟩

/-- Lift one safely selected residual batch and freeze the previously
completed target paths. -/
noncomputable def extend
    {G : DWeb V} (hNorm : G.IsNormalized)
    (S : SafeCompletedState G) (B : Set V) (hB : B ⊆ G.source)
    (hSB : S.sources ⊆ B)
    (Q : SafeBatchInDeletion G (G.vertexSet S.completed)
      (B \ S.sources)) : SafeCompletedState G := by
  let X := G.vertexSet S.completed
  let H := G.delete X
  let R : Set G.DPath := G.liftDeleteFamily X Q.paths
  have hnewSource : B \ S.sources ⊆ H.source := by
    exact sdiff_sources_subset_delete_source hNorm S hB
  have hQR : IsLinkageBetween G (B \ S.sources) H.target R := by
    exact RegularProtectedDeltaLift.IsLinkageBetween.liftDeleteFamily
      G X Q.linkage
  have hRwarp : G.IsWarp R := hQR.isWarp
  have hRavoid : Disjoint (G.vertexSet R) X := by
    apply G.vertexSet_liftDeleteFamily_disjoint
    rw [Q.linkage.initialSet_eq]
    exact hnewSource
  have hcross : ∀ p ∈ S.completed, ∀ q ∈ R, p ≠ q →
      Disjoint p.support q.support := by
    intro p hp q hq _
    apply Set.disjoint_left.2
    intro x hxp hxq
    exact Set.disjoint_left.1 hRavoid ⟨q, hq, hxq⟩ ⟨p, hp, hxp⟩
  let P : Set G.DPath := S.completed ∪ R
  have hPwarp : G.IsWarp P := by
    exact Set.PairwiseDisjoint.union S.linkage.isWarp hRwarp hcross
  have hPfinite : G.HasFiniteCharacter P :=
    SingularContinuation.finiteCharacter_union G
      S.linkage.finiteCharacter hQR.finiteCharacter
  have hPinitial : G.initialSet P = B := by
    dsimp only [P]
    rw [G.initialSet_union, S.linkage.initialSet_eq,
      hQR.initialSet_eq]
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  have hPterminal : G.terminalFrontier P ⊆ G.target := by
    rw [G.terminalFrontier_union]
    apply Set.union_subset S.linkage.terminalFrontier_subset
    exact hQR.terminalFrontier_subset.trans Set.sdiff_subset
  have hPbetween : ∀ p ∈ P, IsPathBetween G B G.target p := by
    intro p hp
    rcases hp with hpOld | hpNew
    · obtain ⟨q, rfl, _hends, _hsource⟩ :=
        S.linkage.endpointPure p hpOld
      apply isPathBetween_of_normalized hNorm hB q
      · apply hSB
        rw [← S.linkage.initialSet_eq]
        exact ⟨Sum.inl q, hpOld, rfl⟩
      · apply S.linkage.terminalFrontier_subset
        exact ⟨Sum.inl q, hpOld, rfl⟩
    · obtain ⟨q, rfl, _hends, _hsource⟩ := hQR.endpointPure p hpNew
      apply isPathBetween_of_normalized hNorm hB q
      · have hqi : q.start ∈ G.initialSet R :=
          ⟨Sum.inl q, hpNew, rfl⟩
        rw [hQR.initialSet_eq] at hqi
        exact hqi.1
      · exact (hQR.terminalFrontier_subset
          ⟨Sum.inl q, hpNew, rfl⟩).1
  have hPlink : IsLinkageBetween G B G.target P :=
    ⟨hPwarp, hPfinite, hPinitial, hPterminal, hPbetween⟩
  refine
    { sources := B
      sources_subset := hB
      completed := P
      linkage := hPlink
      residual := ?_ }
  have hvertex : G.vertexSet P = X ∪ H.vertexSet Q.paths := by
    dsimp only [P, R, X, H]
    rw [G.vertexSet_union, vertexSet_liftDeleteFamily]
  rw [hvertex, ← G.delete_delete]
  exact Q.residual

@[simp] theorem extend_sources
    {G : DWeb V} (hNorm : G.IsNormalized)
    (S : SafeCompletedState G) (B : Set V) (hB : B ⊆ G.source)
    (hSB : S.sources ⊆ B)
    (Q : SafeBatchInDeletion G (G.vertexSet S.completed)
      (B \ S.sources)) :
    (extend hNorm S B hB hSB Q).sources = B := rfl

@[simp] theorem extend_completed
    {G : DWeb V} (hNorm : G.IsNormalized)
    (S : SafeCompletedState G) (B : Set V) (hB : B ⊆ G.source)
    (hSB : S.sources ⊆ B)
    (Q : SafeBatchInDeletion G (G.vertexSet S.completed)
      (B \ S.sources)) :
    (extend hNorm S B hB hSB Q).completed =
      S.completed ∪
        G.liftDeleteFamily (G.vertexSet S.completed) Q.paths := rfl

/-- The displayed full-source row is literally forward-extended by a safe
completed successor. -/
theorem forward_displayed_extend
    {G : DWeb V} (hNorm : G.IsNormalized)
    (S : SafeCompletedState G) (B : Set V) (hB : B ⊆ G.source)
    (hSB : S.sources ⊆ B)
    (Q : SafeBatchInDeletion G (G.vertexSet S.completed)
      (B \ S.sources)) :
    G.ForwardExtension S.displayed
      (extend hNorm S B hB hSB Q).displayed := by
  let R := G.liftDeleteFamily (G.vertexSet S.completed) Q.paths
  let T := extend hNorm S B hB hSB Q
  have hRinitial : G.initialSet R = B \ S.sources := by
    dsimp only [R]
    rw [G.initialSet_liftDeleteFamily, Q.linkage.initialSet_eq]
  constructor
  · intro p hp
    rcases hp with hpOld | hpTrivial
    · refine ⟨p, ?_, G.extends_refl p⟩
      exact Or.inl (by simpa [T, R] using (Or.inl hpOld : p ∈ S.completed ∪ R))
    · obtain ⟨x, hx, rfl⟩ := hpTrivial
      by_cases hxB : x ∈ B
      · have hxInitial : x ∈ G.initialSet R := by
          rw [hRinitial]
          exact ⟨hxB, hx.2⟩
        obtain ⟨q, hqR, hqx⟩ := hxInitial
        refine ⟨q, ?_, extends_trivialPath_of_initial_eq G hqx⟩
        exact Or.inl (by simpa [T, R] using (Or.inr hqR : q ∈ S.completed ∪ R))
      · refine ⟨G.trivialPath x, ?_, G.extends_refl _⟩
        exact Or.inr ⟨x, ⟨hx.1, hxB⟩, rfl⟩
  · intro q hq
    rcases hq with hqCompleted | hqTrivial
    · change q ∈ S.completed ∪ R at hqCompleted
      rcases hqCompleted with hqOld | hqNew
      · exact ⟨q, Or.inl hqOld, G.extends_refl q⟩
      · have hqi : q.initial ∈ B \ S.sources := by
          rw [← hRinitial]
          exact ⟨q, hqNew, rfl⟩
        refine ⟨G.trivialPath q.initial, ?_,
          extends_trivialPath_of_initial_eq G rfl⟩
        exact Or.inr ⟨q.initial, ⟨hB hqi.1, hqi.2⟩, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hqTrivial
      refine ⟨G.trivialPath x, ?_, G.extends_refl _⟩
      exact Or.inr ⟨x, ⟨hx.1, fun hxOld ↦ hx.2 (hSB hxOld)⟩, rfl⟩

/-- The empty completed linkage is the safe base state. -/
def emptyState (G : DWeb V) (hG : G.IsUnhindered) :
    SafeCompletedState G where
  sources := ∅
  sources_subset := Set.empty_subset _
  completed := ∅
  linkage := by simpa using empty_linkage G
  residual := by
    have hempty : G.vertexSet ∅ = ∅ := by
      ext x
      simp [DWeb.vertexSet]
    rw [hempty, G.delete_empty]
    exact hG

/-- Select and install one safe residual batch. -/
noncomputable def selectedExtension
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : SafeBatchSelectionBelow G kappa)
    (hNorm : G.IsNormalized) (S : SafeCompletedState G)
    (B : Set V) (hB : B ⊆ G.source) (hSB : S.sources ⊆ B)
    (hnewCard : #((B \ S.sources : Set V)) < kappa) : SafeCompletedState G :=
  extend hNorm S B hB hSB <| Classical.choice <|
    hselect (G.vertexSet S.completed) (B \ S.sources) S.residual
      (sdiff_sources_subset_delete_source hNorm S hB) hnewCard

theorem forward_selectedExtension
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : SafeBatchSelectionBelow G kappa)
    (hNorm : G.IsNormalized) (S : SafeCompletedState G)
    (B : Set V) (hB : B ⊆ G.source) (hSB : S.sources ⊆ B)
    (hnewCard : #((B \ S.sources : Set V)) < kappa) :
    G.ForwardExtension S.displayed
      (selectedExtension hselect hNorm S B hB hSB hnewCard).displayed :=
  forward_displayed_extend hNorm S B hB hSB _

@[simp] theorem selectedExtension_sources
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : SafeBatchSelectionBelow G kappa)
    (hNorm : G.IsNormalized) (S : SafeCompletedState G)
    (B : Set V) (hB : B ⊆ G.source) (hSB : S.sources ⊆ B)
    (hnewCard : #((B \ S.sources : Set V)) < kappa) :
    (selectedExtension hselect hNorm S B hB hSB hnewCard).sources = B :=
  rfl

/-- A simultaneous safe-completed stage, retaining the exact singular scale
in every column. -/
structure SafeCompletedStage
    (G : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular) where
  column : Index kappa → SafeCompletedState G
  sources_card : ∀ i,
    #((column i).sources) = scale kappa hkappa hsingular i

namespace SafeCompletedStage

variable {G : DWeb V} {kappa : Cardinal.{u}}
variable {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}

def row (hNorm : G.IsNormalized)
    (S : SafeCompletedStage G kappa hkappa hsingular) :
    TargetRowStage G (Index kappa) :=
  SafeCompletedState.stage hNorm S.column

/-- The initial source layers are installed as safely completed batches. -/
noncomputable def initial
    (hselect : SafeBatchSelectionBelow G kappa)
    (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa) :
    SafeCompletedStage G kappa hkappa hsingular := by
  let E := emptyState G hG
  let A : Index kappa → Set V :=
    sourceLayer A₀ kappa hcard hkappa hsingular
  let C : Index kappa → SafeCompletedState G := fun i ↦
    selectedExtension hselect hNorm E (A i)
      ((sourceLayer_subset A₀ kappa hcard hkappa hsingular i).trans hA₀)
      (by exact Set.empty_subset _)
      (by
        have hle : #((A i \ E.sources : Set V)) ≤ #(A i) :=
          Cardinal.mk_subtype_mono Set.sdiff_subset
        have hAi : #(A i) = scale kappa hkappa hsingular i := by
          exact sourceLayer_card A₀ kappa hcard hkappa hsingular i
        rw [hAi] at hle
        exact hle.trans_lt (scale_below kappa hkappa hsingular i))
  exact
    { column := C
      sources_card := by
        intro i
        simp only [C]
        exact sourceLayer_card A₀ kappa hcard hkappa hsingular i }

@[simp] theorem initial_sources
    (hselect : SafeBatchSelectionBelow G kappa)
    (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa) :
    ((initial (hkappa := hkappa) (hsingular := hsingular)
      hselect hG hNorm hA₀ hcard).row hNorm).sources =
      sourceLayer A₀ kappa hcard hkappa hsingular := by
  rfl

/-- One simultaneous competitor-closing step.  Each column selects its new
batch only in its own certified residual. -/
noncomputable def next
    {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (hselect : SafeBatchSelectionBelow G kappa)
    (hNorm : G.IsNormalized)
    (S : SafeCompletedStage G kappa hkappa hsingular) :
    SafeCompletedStage G kappa hkappa hsingular := by
  let R := S.row hNorm
  let B : Index kappa → Set V := nextTargetSources G fixed R
  have hBsub : ∀ i, B i ⊆ G.source := by
    intro i
    exact nextTargetSources_subset_source hfixedInitial R
      (fun j ↦ (S.column j).sources_subset) i
  have hBcard : ∀ i, #(B i) = scale kappa hkappa hsingular i := by
    intro i
    exact mk_nextTargetSources_eq hfixedWarp R
      (scale_infinite kappa hkappa hsingular i)
      (scale_index_le kappa hkappa hsingular i) i (S.sources_card i)
  have hSB : ∀ i, (S.column i).sources ⊆ B i := by
    intro i x hx
    exact Or.inl hx
  let C : Index kappa → SafeCompletedState G := fun i ↦
    selectedExtension hselect hNorm (S.column i) (B i)
      (hBsub i) (hSB i)
      (by
        have hle : #((B i \ (S.column i).sources : Set V)) ≤ #(B i) :=
          Cardinal.mk_subtype_mono Set.sdiff_subset
        rw [hBcard i] at hle
        exact hle.trans_lt (scale_below kappa hkappa hsingular i))
  exact
    { column := C
      sources_card := by
        intro i
        simp only [C, selectedExtension_sources]
        exact hBcard i }

@[simp] theorem next_sources
    {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (hselect : SafeBatchSelectionBelow G kappa)
    (hNorm : G.IsNormalized)
    (S : SafeCompletedStage G kappa hkappa hsingular) :
    ((next hfixedWarp hfixedInitial hselect hNorm S).row hNorm).sources =
      nextTargetSources G fixed (S.row hNorm) := by
  rfl

theorem forward_next
    {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (hselect : SafeBatchSelectionBelow G kappa)
    (hNorm : G.IsNormalized)
    (S : SafeCompletedStage G kappa hkappa hsingular) (i : Index kappa) :
    G.ForwardExtension ((S.row hNorm).paths i)
      (((next hfixedWarp hfixedInitial hselect hNorm S).row hNorm).paths i) := by
  let R := S.row hNorm
  let B : Index kappa → Set V := nextTargetSources G fixed R
  have hBsub : B i ⊆ G.source := by
    exact nextTargetSources_subset_source hfixedInitial R
      (fun j ↦ (S.column j).sources_subset) i
  have hBcard : #(B i) = scale kappa hkappa hsingular i := by
    exact mk_nextTargetSources_eq hfixedWarp R
      (scale_infinite kappa hkappa hsingular i)
      (scale_index_le kappa hkappa hsingular i) i (S.sources_card i)
  have hSB : (S.column i).sources ⊆ B i := by
    intro x hx
    exact Or.inl hx
  have hnew : #((B i \ (S.column i).sources : Set V)) < kappa := by
    have hle : #((B i \ (S.column i).sources : Set V)) ≤ #(B i) :=
      Cardinal.mk_subtype_mono Set.sdiff_subset
    rw [hBcard] at hle
    exact hle.trans_lt (scale_below kappa hkappa hsingular i)
  simpa only [next, row, SafeCompletedState.stage, B, R] using
    (forward_selectedExtension (kappa := kappa) hselect hNorm
      (S.column i) (B i) hBsub hSB hnew)

end SafeCompletedStage

/-- The safe-batch selector compiles to the exact private machine consumed
by the singular competitor matrix. -/
noncomputable def targetRowMachine
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed)
    (hselect : SafeBatchSelectionBelow G kappa) :
    TargetRowMachine G fixed
      (sourceLayer A₀ kappa hcard hkappa hsingular) where
  State := SafeCompletedStage G kappa hkappa hsingular
  row S := S.row hNorm
  initial := SafeCompletedStage.initial hselect hG hNorm hA₀ hcard
  next S := SafeCompletedStage.next hfixed.isWarp
    (hfixed.initialSet_eq.le.trans Set.sdiff_subset) hselect hNorm S
  sources_initial := SafeCompletedStage.initial_sources
    hselect hG hNorm hA₀ hcard
  sources_next S := SafeCompletedStage.next_sources
    hfixed.isWarp (hfixed.initialSet_eq.le.trans Set.sdiff_subset)
      hselect hNorm S
  forward_next S i := SafeCompletedStage.forward_next
    hfixed.isWarp (hfixed.initialSet_eq.le.trans Set.sdiff_subset)
      hselect hNorm S i

/-- Normalized safe-batch selection is sufficient for the singular extension
clause.  This is the public consumer of the set-valued safe-link theorem. -/
theorem singularExtensionClauseAt_of_safeBatchSelection
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hselect : SafeBatchSelectionBelow Gamma.normalized kappa) :
    ExtensionClauseAt Gamma kappa := by
  apply singularExtensionClauseAt_of_normalizedTargetRowMachine
    kappa hkappa hsingular Gamma
  intro A₀ hA₀ hcard fixed hfixed
  exact targetRowMachine hkappa hsingular hGamma.normalized
    Gamma.normalized_isNormalized hA₀ hcard hfixed hselect

end SingularSafeCompletedMachine
end CardinalInduction
end Erdos599
