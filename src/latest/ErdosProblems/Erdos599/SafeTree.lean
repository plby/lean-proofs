/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteDeletion
import ErdosProblems.Erdos599.FamilyTools

/-!
# The rooted tree and countable closure in the safe-link theorem

This file formalizes the set-theoretic core of Section 6 of
Aharoni--Berger.  The two main constructions are:

* the inclusion-maximal set reachable from a distinguished source while
  preserving all finite safe deletions; and
* the countable closing-up operation used in Proposition 6.3.

The graph-specific finite-deletion and iterated-arrow lemmas are kept in
their respective modules.  The results here expose exactly the invariants
those lemmas consume; in particular, maximality produces an actual finite
obstruction at every outer-boundary vertex.
-/

noncomputable section

namespace Erdos599

open Set
open DirectedPath

universe u

namespace DWeb

variable {V : Type u} (Γ : DWeb V)

/-! ## Safe target paths -/

/-- Deleting the finite vertex set `F` leaves an unhindered web. -/
def SafeDeletion (F : Set V) : Prop :=
  (Γ.delete F).IsUnhindered

/-- Delete the root together with an additional finite set. -/
def SafeAfterRootDeletion (a : V) (F : Set V) : Prop :=
  Γ.SafeDeletion (insert a F)

@[simp]
theorem delete_empty : Γ.delete ∅ = Γ := by
  cases Γ with
  | mk graph source target =>
      simp only [DWeb.delete, DWeb.inducedGraph, compl_empty, sdiff_empty]
      congr
      ext u v
      simp

/-- A finite path from `a` to the target whose whole support can safely be
deleted. -/
def IsSafeTargetPath (a : V) (p : FinitePath Γ.graph) : Prop :=
  p.start = a ∧ p.finish ∈ Γ.target ∧
    (Γ.delete p.support).IsUnhindered

/-- There is a safely deletable finite path from `a` to the target. -/
def HasSafeTargetPath (a : V) : Prop :=
  ∃ p : FinitePath Γ.graph, Γ.IsSafeTargetPath a p

/-! ## The maximal reachable tree set -/

/-- The exact rooted-set invariant used in the proof of Theorem 6.1.
After deleting the root, every finite subset of the remaining tree is
safely deletable as well. -/
def IsTreeSet (a : V) (T : Set V) : Prop :=
  a ∈ T ∧
    T ∩ Γ.source ⊆ {a} ∧
    (∀ t ∈ T, ∃ p : FinitePath Γ.graph,
      p.start = a ∧ p.finish = t ∧ p.support ⊆ T) ∧
    ∀ F : Set V, F.Finite → F ⊆ T \ {a} →
      Γ.SafeAfterRootDeletion a F

/-- The singleton root is an admissible tree set as soon as deleting the
root is safe. -/
theorem isTreeSet_singleton {a : V} (_ha : a ∈ Γ.source)
    (hsafe : (Γ.delete {a}).IsUnhindered) : Γ.IsTreeSet a {a} := by
  refine ⟨Set.mem_singleton a, ?_, ?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro t ht
    have hta : t = a := by simpa using ht
    subst t
    let p : FinitePath Γ.graph :=
      { start := a
        finish := a
        walk := .nil
        isPath := Walk.isPath_nil a }
    exact ⟨p, rfl, rfl, by simp [p, FinitePath.support]⟩
  · intro F hF hFsub
    have hFempty : F = ∅ := by
      apply Set.Subset.antisymm ?_ (Set.empty_subset F)
      intro x hx
      have hx' := hFsub hx
      exact hx'.2 (by simpa using hx'.1)
    simpa [SafeAfterRootDeletion, SafeDeletion, hFempty] using hsafe

/-- A finite subset of the union of a nonempty inclusion-chain is already
contained in one member of the chain. -/
theorem finite_subset_sUnion_of_chain {c : Set (Set V)}
    (hc : IsChain (· ⊆ ·) c) (hcne : c.Nonempty)
    {F : Set V} (hF : F.Finite) (hFc : F ⊆ ⋃₀ c) :
    ∃ T ∈ c, F ⊆ T := by
  induction F, hF using Set.Finite.induction_on with
  | empty =>
      obtain ⟨T, hTc⟩ := hcne
      exact ⟨T, hTc, Set.empty_subset T⟩
  | @insert x F hx hF ih =>
      have hFsub : F ⊆ ⋃₀ c := fun z hz ↦ hFc (Set.mem_insert_of_mem x hz)
      obtain ⟨TF, hTFc, hFTF⟩ := ih hFsub
      obtain ⟨Tx, hTxc, hxTx⟩ := Set.mem_sUnion.1 (hFc (Set.mem_insert x F))
      by_cases hEq : Tx = TF
      · subst Tx
        exact ⟨TF, hTFc, Set.insert_subset hxTx hFTF⟩
      · rcases hc hTxc hTFc hEq with hTxTF | hTFTx
        · exact ⟨TF, hTFc, Set.insert_subset (hTxTF hxTx) hFTF⟩
        · exact ⟨Tx, hTxc, Set.insert_subset hxTx (hFTF.trans hTFTx)⟩

/-- Unions of nonempty inclusion-chains of tree sets are tree sets. -/
theorem sUnion_isTreeSet {a : V} {c : Set (Set V)}
    (hcsub : c ⊆ {T | Γ.IsTreeSet a T})
    (hc : IsChain (· ⊆ ·) c) (hcne : c.Nonempty) :
    Γ.IsTreeSet a (⋃₀ c) := by
  obtain ⟨T₀, hT₀c⟩ := hcne
  have hT₀ := hcsub hT₀c
  refine ⟨Set.mem_sUnion_of_mem hT₀.1 hT₀c, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨T, hTc, hxT⟩ := Set.mem_sUnion.1 hx.1
    exact (hcsub hTc).2.1 ⟨hxT, hx.2⟩
  · intro t ht
    obtain ⟨T, hTc, htT⟩ := Set.mem_sUnion.1 ht
    obtain ⟨p, hpstart, hpfinish, hpT⟩ := (hcsub hTc).2.2.1 t htT
    exact ⟨p, hpstart, hpfinish,
      hpT.trans (Set.subset_sUnion_of_mem hTc)⟩
  · intro F hF hFsub
    have hFsUnion : F ⊆ ⋃₀ c := hFsub.trans Set.sdiff_subset
    obtain ⟨T, hTc, hFT⟩ :=
      finite_subset_sUnion_of_chain hc ⟨T₀, hT₀c⟩ hF hFsUnion
    apply (hcsub hTc).2.2.2 F hF
    intro x hx
    exact ⟨hFT hx, hFsub hx |>.2⟩

/-- Zorn's lemma gives an inclusion-maximal rooted tree set. -/
theorem exists_maximalTreeSet {a : V} (ha : a ∈ Γ.source)
    (hsafe : (Γ.delete {a}).IsUnhindered) :
    ∃ T : Set V, Maximal (Γ.IsTreeSet a) T := by
  apply zorn_subset
  intro c hcsub hc
  by_cases hcne : c.Nonempty
  · exact ⟨⋃₀ c, Γ.sUnion_isTreeSet hcsub hc hcne,
      fun T hTc ↦ Set.subset_sUnion_of_mem hTc⟩
  · have hcempty : c = ∅ := Set.not_nonempty_iff_eq_empty.mp hcne
    exact ⟨{a}, Γ.isTreeSet_singleton ha hsafe,
      by simp [hcempty]⟩

/-- The outer vertex boundary of `T`. -/
def outerBoundary (T : Set V) : Set V :=
  {y | y ∉ T ∧ ∃ t ∈ T, Γ.graph.Adj t y}

/-- Append a genuinely new boundary vertex to a path contained in `T`. -/
def appendBoundaryVertex {a t y : V} {T : Set V}
    (p : FinitePath Γ.graph) (_hpstart : p.start = a)
    (hpfinish : p.finish = t) (hpT : p.support ⊆ T)
    (hyT : y ∉ T) (e : Γ.graph.Adj t y) : FinitePath Γ.graph where
  start := p.start
  finish := y
  walk := p.walk.concat (hpfinish.symm ▸ e)
  isPath := by
    simp only [Walk.IsPath, Walk.support_concat]
    apply p.isPath.append (by simp)
    rw [List.disjoint_singleton]
    intro hy
    exact hyT (hpT hy)

@[simp]
theorem appendBoundaryVertex_start {a t y : V} {T : Set V}
    (p : FinitePath Γ.graph) (hpstart : p.start = a)
    (hpfinish : p.finish = t) (hpT : p.support ⊆ T)
    (hyT : y ∉ T) (e : Γ.graph.Adj t y) :
    (Γ.appendBoundaryVertex p hpstart hpfinish hpT hyT e).start = a :=
  hpstart

@[simp]
theorem appendBoundaryVertex_finish {a t y : V} {T : Set V}
    (p : FinitePath Γ.graph) (hpstart : p.start = a)
    (hpfinish : p.finish = t) (hpT : p.support ⊆ T)
    (hyT : y ∉ T) (e : Γ.graph.Adj t y) :
    (Γ.appendBoundaryVertex p hpstart hpfinish hpT hyT e).finish = y :=
  rfl

theorem appendBoundaryVertex_support_subset {a t y : V} {T : Set V}
    (p : FinitePath Γ.graph) (hpstart : p.start = a)
    (hpfinish : p.finish = t) (hpT : p.support ⊆ T)
    (hyT : y ∉ T) (e : Γ.graph.Adj t y) :
    (Γ.appendBoundaryVertex p hpstart hpfinish hpT hyT e).support ⊆
      insert y T := by
  intro x hx
  change x ∈ (p.walk.concat (hpfinish.symm ▸ e)).support at hx
  rw [Walk.support_concat] at hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hxy
  · exact Set.mem_insert_of_mem y (hpT hx)
  · exact hxy ▸ Set.mem_insert y T

/-- If all finite deletions remain safe after adjoining `y`, then `y` can
be adjoined to the rooted tree set. -/
theorem isTreeSet_insert_boundary {a y : V} {T : Set V}
    (hT : Γ.IsTreeSet a T) (hyT : y ∉ T) (hyA : y ∉ Γ.source)
    (hedge : ∃ t ∈ T, Γ.graph.Adj t y)
    (hsafe : ∀ F : Set V, F.Finite → F ⊆ T \ {a} →
      Γ.SafeAfterRootDeletion a (insert y F)) :
    Γ.IsTreeSet a (insert y T) := by
  refine ⟨Set.mem_insert_of_mem y hT.1, ?_, ?_, ?_⟩
  · rintro x ⟨hx, hxA⟩
    rcases hx with rfl | hxT
    · exact (hyA hxA).elim
    · exact hT.2.1 ⟨hxT, hxA⟩
  · intro x hx
    rcases hx with rfl | hxT
    · obtain ⟨t, htT, hty⟩ := hedge
      obtain ⟨p, hpstart, hpfinish, hpT⟩ := hT.2.2.1 t htT
      exact ⟨Γ.appendBoundaryVertex p hpstart hpfinish hpT hyT hty,
        Γ.appendBoundaryVertex_start p hpstart hpfinish hpT hyT hty,
        Γ.appendBoundaryVertex_finish p hpstart hpfinish hpT hyT hty,
        Γ.appendBoundaryVertex_support_subset p hpstart hpfinish hpT hyT hty⟩
    · obtain ⟨p, hpstart, hpfinish, hpT⟩ := hT.2.2.1 x hxT
      exact ⟨p, hpstart, hpfinish,
        hpT.trans (Set.subset_insert y T)⟩
  · intro F hF hFsub
    by_cases hyF : y ∈ F
    · let F₀ := F \ {y}
      have hF₀fin : F₀.Finite := hF.sdiff
      have hF₀sub : F₀ ⊆ T \ {a} := by
        intro x hx
        have hxnew := hFsub hx.1
        refine ⟨?_, hxnew.2⟩
        rcases hxnew.1 with hxy | hxT
        · exact (hx.2 (hxy ▸ Set.mem_singleton y)).elim
        · exact hxT
      have hEq : insert y F₀ = F := by
        ext x
        by_cases hxy : x = y
        · subst x
          simp [hyF]
        · simp [F₀, hxy]
      exact hEq ▸ hsafe F₀ hF₀fin hF₀sub
    · apply hT.2.2.2 F hF
      intro x hx
      have hxnew := hFsub hx
      refine ⟨?_, hxnew.2⟩
      rcases hxnew.1 with hxy | hxT
      · exact (hyF (hxy ▸ hx)).elim
      · exact hxT

/-- Maximality turns every eligible outer-boundary vertex into a concrete
finite obstruction.  This is the rooted-tree step in the proof of
Theorem 6.1. -/
theorem exists_finite_obstruction_of_maximal
    {a y : V} {T : Set V} (hT : Maximal (Γ.IsTreeSet a) T)
    (hy : y ∈ Γ.outerBoundary T) (hyA : y ∉ Γ.source) :
    ∃ F : Set V, F.Finite ∧ F ⊆ T \ {a} ∧
      ¬ Γ.SafeAfterRootDeletion a (insert y F) := by
  by_contra hnone
  push Not at hnone
  have hnew : Γ.IsTreeSet a (insert y T) :=
    Γ.isTreeSet_insert_boundary hT.1 hy.1 hyA hy.2 hnone
  have hback : insert y T ⊆ T := hT.2 hnew (Set.subset_insert y T)
  exact hy.1 (hback (Set.mem_insert y T))

/-- The support of a concrete finite path is finite. -/
theorem finitePath_support_finite (p : FinitePath Γ.graph) :
    p.support.Finite := by
  exact p.walk.support.finite_toSet

/-- If no safely deletable root-to-target path exists, an admissible tree
set cannot meet the target. -/
theorem disjoint_target_of_not_hasSafeTargetPath {a : V} {T : Set V}
    (hT : Γ.IsTreeSet a T) (hnone : ¬ Γ.HasSafeTargetPath a) :
    Disjoint T Γ.target := by
  rw [Set.disjoint_left]
  intro t htT htB
  obtain ⟨p, hpstart, hpfinish, hpT⟩ := hT.2.2.1 t htT
  let F := p.support \ {a}
  have hFfin : F.Finite := (Γ.finitePath_support_finite p).sdiff
  have hFsub : F ⊆ T \ {a} := by
    intro x hx
    exact ⟨hpT hx.1, hx.2⟩
  have hsafe := hT.2.2.2 F hFfin hFsub
  apply hnone
  refine ⟨p, hpstart, hpfinish ▸ htB, ?_⟩
  have heq : insert a F = p.support := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [F, hpstart ▸ p.start_mem_support]
    · simp [F, hxa]
  simpa [SafeAfterRootDeletion, SafeDeletion, heq] using hsafe

/-! ## Countable closing-up -/

/-- The members of `W` whose support meets `X`. -/
def pathsMeeting (W : Set Γ.DPath) (X : Set V) : Set Γ.DPath :=
  {p | p ∈ W ∧ (p.support ∩ X).Nonempty}

/-- Every finite path or ray has countable support. -/
theorem path_support_countable (p : Γ.DPath) : p.support.Countable := by
  rcases p with p | r
  · exact p.walk.support.finite_toSet.countable
  · exact Set.countable_range r.toFun

/-- Only countably many members of a disjoint path family can meet a
countable vertex set. -/
theorem pathsMeeting_countable {W : Set Γ.DPath} {X : Set V}
    (hW : Γ.IsWarp W) (hX : X.Countable) :
    (Γ.pathsMeeting W X).Countable := by
  exact FamilyTools.countable_of_pairwiseDisjoint_of_meets
    (I := Γ.pathsMeeting W X) (F := Path.support) (S := X)
    (hdisj := by
      intro p hp q hq hpq
      exact hW hp.1 hq.1 hpq)
    (hS := hX)
    (hmeet := by
      intro p hp
      obtain ⟨x, hxp, hxX⟩ := hp.2
      exact ⟨x, hxX, hxp⟩)

/-- Vertices lying on members of `W` which meet `X`. -/
def meetingVertexSet (W : Set Γ.DPath) (X : Set V) : Set V :=
  ⋃ p ∈ Γ.pathsMeeting W X, p.support

theorem meetingVertexSet_countable {W : Set Γ.DPath} {X : Set V}
    (hW : Γ.IsWarp W) (hX : X.Countable) :
    (Γ.meetingVertexSet W X).Countable := by
  exact (Γ.pathsMeeting_countable hW hX).biUnion
    fun p _ ↦ Γ.path_support_countable p

/-- The `n`th finite closing-up stage. -/
def closureStage (_Γ : DWeb V) (step : Set V → Set V) (X₀ : Set V) : ℕ → Set V
  | 0 => X₀
  | n + 1 => step (closureStage _Γ step X₀ n)

/-- The union of all finite closing-up stages. -/
def omegaClosure (step : Set V → Set V) (X₀ : Set V) : Set V :=
  ⋃ n, Γ.closureStage step X₀ n

theorem closureStage_mono_of_inflationary {step : Set V → Set V}
    {X₀ : Set V} (hinflate : ∀ X, X ⊆ step X) :
    Monotone (Γ.closureStage step X₀) := by
  apply monotone_nat_of_le_succ
  intro n
  exact hinflate _

/-- One exact closing-up step from Proposition 6.3.  The warp may depend on
the current deletion set, which matches the maximal-wave recursion. -/
def closingStep (W : Set V → Set Γ.DPath) (F G : V → Set V)
    (Y Q T X : Set V) : Set V :=
  X ∪
    (⋃ z ∈ Y ∩ Γ.meetingVertexSet (W X) X, F z) ∪
    (⋃ t ∈ X \ Q, G t) ∪
    (Γ.meetingVertexSet (W X) X ∩ T)

theorem subset_closingStep (W : Set V → Set Γ.DPath) (F G : V → Set V)
    (Y Q T X : Set V) :
    X ⊆ Γ.closingStep W F G Y Q T X := by
  intro x hx
  simp only [closingStep, Set.mem_union]
  exact Or.inl (Or.inl (Or.inl hx))

theorem closingStep_countable
    {W : Set V → Set Γ.DPath} {F G : V → Set V}
    {Y Q T X : Set V} (hwarp : Γ.IsWarp (W X))
    (hX : X.Countable) (hF : ∀ z, (F z).Finite)
    (hG : ∀ t, (G t).Countable) :
    (Γ.closingStep W F G Y Q T X).Countable := by
  have hM : (Γ.meetingVertexSet (W X) X).Countable :=
    Γ.meetingVertexSet_countable hwarp hX
  have hY : (Y ∩ Γ.meetingVertexSet (W X) X).Countable :=
    hM.mono Set.inter_subset_right
  have hFU : (⋃ z ∈ Y ∩ Γ.meetingVertexSet (W X) X, F z).Countable :=
    hY.biUnion fun z _ ↦ (hF z).countable
  have hXQ : (X \ Q).Countable := hX.mono Set.sdiff_subset
  have hGU : (⋃ t ∈ X \ Q, G t).Countable :=
    hXQ.biUnion fun t _ ↦ hG t
  have hMT : (Γ.meetingVertexSet (W X) X ∩ T).Countable :=
    hM.mono Set.inter_subset_left
  exact (((hX.union hFU).union hGU).union hMT)

/-- All finite stages of the closing-up recursion are countable. -/
theorem closureStage_countable
    {W : Set V → Set Γ.DPath} {F G : V → Set V}
    {Y Q T X₀ : Set V} (hX₀ : X₀.Countable)
    (hwarp : ∀ X, X.Countable → Γ.IsWarp (W X))
    (hF : ∀ z, (F z).Finite) (hG : ∀ t, (G t).Countable) :
    ∀ n, (Γ.closureStage (Γ.closingStep W F G Y Q T) X₀ n).Countable
  | 0 => hX₀
  | n + 1 => by
      apply Γ.closingStep_countable
      · apply hwarp
        exact closureStage_countable hX₀ hwarp hF hG n
      · exact closureStage_countable hX₀ hwarp hF hG n
      · exact hF
      · exact hG

/-- The union of the finite closing-up stages is countable. -/
theorem omegaClosure_countable
    {W : Set V → Set Γ.DPath} {F G : V → Set V}
    {Y Q T X₀ : Set V} (hX₀ : X₀.Countable)
    (hwarp : ∀ X, X.Countable → Γ.IsWarp (W X))
    (hF : ∀ z, (F z).Finite) (hG : ∀ t, (G t).Countable) :
    (Γ.omegaClosure (Γ.closingStep W F G Y Q T) X₀).Countable := by
  apply Set.countable_iUnion
  exact Γ.closureStage_countable hX₀ hwarp hF hG

theorem closureStage_monotone
    (W : Set V → Set Γ.DPath) (F G : V → Set V)
    (Y Q T X₀ : Set V) :
    Monotone
      (Γ.closureStage (Γ.closingStep W F G Y Q T) X₀) := by
  apply Γ.closureStage_mono_of_inflationary
  exact Γ.subset_closingStep W F G Y Q T

/-- Every finite obstruction indexed by a boundary vertex seen at stage
`n` is present at stage `n+1`. -/
theorem F_subset_nextStage
    (W : Set V → Set Γ.DPath) (F G : V → Set V)
    (Y Q T X₀ : Set V) (n : ℕ) {z : V}
    (hz : z ∈ Y ∩ Γ.meetingVertexSet
      (W (Γ.closureStage (Γ.closingStep W F G Y Q T) X₀ n))
      (Γ.closureStage (Γ.closingStep W F G Y Q T) X₀ n)) :
    F z ⊆ Γ.closureStage (Γ.closingStep W F G Y Q T) X₀ (n + 1) := by
  intro x hx
  change x ∈ Γ.closingStep W F G Y Q T
    (Γ.closureStage (Γ.closingStep W F G Y Q T) X₀ n)
  simp only [closingStep, Set.mem_union]
  exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion_of_mem z
    (Set.mem_iUnion_of_mem hz hx))))

/-- Every grounding set indexed by a nondeleted tree vertex at stage `n`
is present at stage `n+1`. -/
theorem G_subset_nextStage
    (W : Set V → Set Γ.DPath) (F G : V → Set V)
    (Y Q T X₀ : Set V) (n : ℕ) {t : V}
    (ht : t ∈ Γ.closureStage
        (Γ.closingStep W F G Y Q T) X₀ n \ Q) :
    G t ⊆ Γ.closureStage (Γ.closingStep W F G Y Q T) X₀ (n + 1) := by
  intro x hx
  change x ∈ Γ.closingStep W F G Y Q T
    (Γ.closureStage (Γ.closingStep W F G Y Q T) X₀ n)
  simp only [closingStep, Set.mem_union]
  exact Or.inl (Or.inr (Set.mem_iUnion_of_mem t
    (Set.mem_iUnion_of_mem ht hx)))

/-- The tree vertices on paths meeting the current stage are added at the
next stage. -/
theorem meeting_tree_subset_nextStage
    (W : Set V → Set Γ.DPath) (F G : V → Set V)
    (Y Q T X₀ : Set V) (n : ℕ) :
    Γ.meetingVertexSet
        (W (Γ.closureStage (Γ.closingStep W F G Y Q T) X₀ n))
        (Γ.closureStage (Γ.closingStep W F G Y Q T) X₀ n) ∩ T ⊆
      Γ.closureStage (Γ.closingStep W F G Y Q T) X₀ (n + 1) := by
  intro x hx
  change x ∈ Γ.closingStep W F G Y Q T
    (Γ.closureStage (Γ.closingStep W F G Y Q T) X₀ n)
  simp only [closingStep, Set.mem_union]
  exact Or.inr hx

/-! ## The two inclusions in Assertion 6.4 -/

/-- The essential paths of `W` which meet `X`. -/
def essentialMeetingPaths (W : Set Γ.DPath) (X : Set V) : Set Γ.DPath :=
  Γ.pathsMeeting (Γ.essentialWarpPart W) X

/-- First half of Assertion 6.4.  A terminal on the tree is inserted into
`X` by closing-up.  If it were outside `Q`, the grounding invariant would
put it in the strict roof, contradicting essentiality of that terminal. -/
theorem terminalFrontier_essentialMeeting_inter_tree_subset
    {W : Set Γ.DPath} {X T Q : Set V}
    (hclosed : Γ.meetingVertexSet W X ∩ T ⊆ X)
    (hground : X \ Q ⊆ Γ.strictRoof (Γ.terminalFrontier W)) :
    Γ.terminalFrontier (Γ.essentialMeetingPaths W X) ∩ T ⊆ Q := by
  intro t ht
  obtain ⟨p, hp, hpt⟩ := ht.1
  have hpW : p ∈ W := hp.1.1
  have hpmeet : (p.support ∩ X).Nonempty := hp.2
  have htSupport : t ∈ p.support := Γ.terminal_mem_support hpt
  have htMeeting : t ∈ Γ.meetingVertexSet W X := by
    refine Set.mem_iUnion_of_mem p (Set.mem_iUnion_of_mem ?_ htSupport)
    exact ⟨hpW, hpmeet⟩
  have htX : t ∈ X := hclosed ⟨htMeeting, ht.2⟩
  by_contra htQ
  have htStrict := hground ⟨htX, htQ⟩
  have htEssential : t ∈ Γ.essential (Γ.terminalFrontier W) := by
    obtain ⟨s, hps, hsEssential⟩ := hp.1.2
    have hst : s = t := Option.some.inj (hps.symm.trans hpt)
    exact hst ▸ hsEssential
  exact Set.disjoint_left.1
    (Γ.disjoint_strictRoof_essential (Γ.terminalFrontier W))
    htStrict htEssential

/-- A point internal to one member of an essential subwarp cannot be a
terminal of another member of the original warp. -/
theorem not_mem_terminalFrontier_of_mem_support_of_not_terminal
    {W : Set Γ.DPath} (hW : Γ.IsWarp W) {p : Γ.DPath}
    (hpW : p ∈ W) {q : V} (hqp : q ∈ p.support)
    (hqpterm : Γ.terminal? p ≠ some q) :
    q ∉ Γ.terminalFrontier W := by
  rintro ⟨r, hrW, hrt⟩
  have hqr : q ∈ r.support := Γ.terminal_mem_support hrt
  have hpr : p = r := by
    by_contra hne
    exact Set.disjoint_left.1 (hW hpW hrW hne) hqp hqr
  subst r
  exact hqpterm hrt

/-- Second half of Assertion 6.4.  Self-roofing puts every nonterminal
point of an essential path into the strict roof.  Thus a set `Q` disjoint
from that strict roof can meet such a path only at its terminal. -/
theorem vertexSet_essentialMeeting_inter_subset_terminalFrontier
    {W : Set Γ.DPath} {X Q : Set V} (hW : Γ.IsWarp W)
    (hself : Γ.vertexSet (Γ.essentialWarpPart W) ⊆
      Γ.roof (Γ.terminalFrontier W))
    (hQ : Disjoint Q (Γ.strictRoof (Γ.terminalFrontier W))) :
    Γ.vertexSet (Γ.essentialMeetingPaths W X) ∩ Q ⊆
      Γ.terminalFrontier (Γ.essentialMeetingPaths W X) := by
  intro q hq
  obtain ⟨p, hp, hqp⟩ := hq.1
  by_contra hqterm
  have hpW : p ∈ W := hp.1.1
  have hnotTerminal : Γ.terminal? p ≠ some q := by
    intro hpq
    exact hqterm ⟨p, hp, hpq⟩
  have hqNotFrontier : q ∉ Γ.terminalFrontier W :=
    Γ.not_mem_terminalFrontier_of_mem_support_of_not_terminal
      hW hpW hqp hnotTerminal
  have hqRoof : q ∈ Γ.roof (Γ.terminalFrontier W) := by
    apply hself
    exact ⟨p, hp.1, hqp⟩
  have hqNotEssential : q ∉ Γ.essential (Γ.terminalFrontier W) :=
    fun h ↦ hqNotFrontier (Γ.essential_subset _ h)
  have hqStrict : q ∈ Γ.strictRoof (Γ.terminalFrontier W) :=
    ⟨hqRoof, hqNotEssential⟩
  exact Set.disjoint_left.1 hQ hq.2 hqStrict

/-- Assertion 6.4 packaged in its two-inclusion form. -/
theorem assertion6_4
    {W : Set Γ.DPath} {X T Q : Set V} (hW : Γ.IsWave W)
    (hclosed : Γ.meetingVertexSet W X ∩ T ⊆ X)
    (hground : X \ Q ⊆ Γ.strictRoof (Γ.terminalFrontier W))
    (hQ : Disjoint Q (Γ.strictRoof (Γ.terminalFrontier W))) :
    Γ.terminalFrontier (Γ.essentialMeetingPaths W X) ∩ T ⊆ Q ∧
      Γ.vertexSet (Γ.essentialMeetingPaths W X) ∩ Q ⊆
        Γ.terminalFrontier (Γ.essentialMeetingPaths W X) :=
  ⟨Γ.terminalFrontier_essentialMeeting_inter_tree_subset hclosed hground,
    Γ.vertexSet_essentialMeeting_inter_subset_terminalFrontier
      hW.1 (hW.essentialWarpPart.self_roofing.trans_eq (by
        rw [Γ.terminalFrontier_essentialWarpPart, Γ.roof_essential])) hQ⟩

/-! ## The finite-deletion contradiction in Assertion 6.5 -/

/-- The set-theoretic conclusion of Assertion 6.5.  The graph-specific
premise `hremove` is exactly what roof-maximality supplies: deleting a path
which terminates at `t` leaves a hindrance after the already chosen finite
set `R` has been deleted.  The maximal-tree invariant then rules out such a
terminal in `X`. -/
theorem assertion6_5_of_terminal_removal
    {a : V} {T R : Set V} {W : Set Γ.DPath}
    (hT : Γ.IsTreeSet a T)
    (hRfin : R.Finite) (hRT : R ⊆ T \ {a})
    (htermOffRoot : Γ.terminalFrontier W ⊆ {a}ᶜ)
    (hremove : ∀ t ∈ T ∩ Γ.terminalFrontier W,
      (Γ.delete (insert a (insert t R))).IsHindered) :
    Disjoint T (Γ.terminalFrontier W) := by
  rw [Set.disjoint_left]
  intro t htT htterm
  have hFfin : (insert t R).Finite := hRfin.insert t
  have hFsub : insert t R ⊆ T \ {a} := by
    apply Set.insert_subset
    · exact ⟨htT, htermOffRoot htterm⟩
    · exact hRT
  have hsafe := hT.2.2.2 (insert t R) hFfin hFsub
  have hnotHindered :
      ¬ (Γ.delete (insert a (insert t R))).IsHindered := by
    exact (Γ.delete (insert a (insert t R))).isUnhindered_iff_not_isHindered.1
      (by simpa [SafeAfterRootDeletion, SafeDeletion] using hsafe)
  exact hnotHindered (hremove t ⟨htT, htterm⟩)

end DWeb
end Erdos599
