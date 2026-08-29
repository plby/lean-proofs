/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingRelationalReduction

/-!
# Finite edge difference for balance-preserving reducing outputs

A finite switch may create directed cycles which its path realization
discards. Equality of signed balances still forces every untouched old
finite path to survive. Thus both edge differences with the original warp
are finite; a bare subset-of-union statement is not being mistaken for this.
-/

noncomputable section

namespace Erdos599.Alternating.SwitchingCore.RelationalReduction

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

private theorem hasOutgoing_of_same_balance
    {E U : Set (V × V)} (hsub : U ⊆ E)
    (hbalance : ∀ x, edgeBalance U x = edgeBalance E x)
    {x : V} (hout : HasOutgoing E x)
    (hstart : ¬HasIncoming E x ∨ HasIncoming U x) :
    HasOutgoing U x := by
  by_contra hnoOut
  have hb := hbalance x
  rcases hstart with hnoIn | hin
  · have hnoInU : ¬HasIncoming U x := by
      rintro ⟨y, hy⟩
      exact hnoIn ⟨y, hsub hy⟩
    simp [edgeBalance, propInt, hout, hnoOut, hnoIn, hnoInU] at hb
  · have hinE : HasIncoming E x := by
      obtain ⟨y, hy⟩ := hin
      exact ⟨y, hsub hy⟩
    simp [edgeBalance, propInt, hout, hnoOut, hinE, hin] at hb

/-- Balance-preserving subrelations retain a directed walk starting at a
source of the ambient relation (or at a vertex already reached in the
subrelation). No choice of a cycle decomposition is needed. -/
theorem walk_edges_subset_of_same_balance
    {E U : Set (V × V)} (hsub : U ⊆ E)
    (hunique : Relator.RightUnique (fun x y ↦ (x, y) ∈ E))
    (hbalance : ∀ x, edgeBalance U x = edgeBalance E x)
    {a b : V} (p : Walk Gamma.graph a b)
    (hp : p.edgeSet ⊆ E)
    (hstart : ¬HasIncoming E a ∨ HasIncoming U a) :
    p.edgeSet ⊆ U := by
  induction p with
  | nil => simp [Walk.edgeSet]
  | @cons a c b hac p ih =>
      have hacE : (a, c) ∈ E := hp (by simp [Walk.edgeSet])
      obtain ⟨z, haz⟩ := hasOutgoing_of_same_balance hsub hbalance
        ⟨c, hacE⟩ hstart
      have hzc : z = c := hunique (hsub haz) hacE
      have hacU : (a, c) ∈ U := hzc ▸ haz
      have hpE : p.edgeSet ⊆ E := by
        intro e he
        exact hp (by simp [Walk.edgeSet, he])
      have hpU := ih hpE (Or.inr ⟨a, hacU⟩)
      intro e he
      simp only [Walk.edgeSet_cons, Set.mem_union, Set.mem_singleton_iff] at he
      exact he.elim (fun h ↦ h ▸ hacU) (fun h ↦ hpU h)

/-- Tails of removed edges and heads of inserted edges are enough to locate
every old owner whose edges can be lost by a balanced subrelation. -/
def modificationBoundary (R F : Set (V × V)) : Set V :=
  Prod.fst '' R ∪ Prod.snd '' F

def modificationOwnerCarrier {Z : Set Gamma.DPath}
    (hZ : Gamma.IsWarp Z) (R F : Set (V × V)) : Set V :=
  ⋃ x ∈ modificationBoundary R F, coveredPathSupport hZ x

theorem modificationOwnerCarrier_finite {Z : Set Gamma.DPath}
    (hZ : Gamma.IsWarp Z) (hZfin : Gamma.HasFiniteCharacter Z)
    {R F : Set (V × V)} (hR : R.Finite) (hF : F.Finite) :
    (modificationOwnerCarrier hZ R F).Finite :=
  ((hR.image Prod.fst).union (hF.image Prod.snd)).biUnion fun x _ ↦
    coveredPathSupport_finite hZ hZfin x

/-- If an old member has no modification-boundary vertex, a balanced
subrelation of the switched relation retains every edge of that member. -/
theorem oldPath_edges_subset_of_avoids_modificationBoundary
    {Z : Set Gamma.DPath} (hZ : Gamma.IsWarp Z)
    (hZfin : Gamma.HasFiniteCharacter Z)
    {R F U : Set (V × V)}
    (hsub : U ⊆ (familyEdges Z \ R) ∪ F)
    (hunique : Relator.RightUnique
      (fun x y ↦ (x, y) ∈ (familyEdges Z \ R) ∪ F))
    (hbalance : ∀ x, edgeBalance U x =
      edgeBalance ((familyEdges Z \ R) ∪ F) x)
    (p : FinitePath Gamma.graph) (hpZ : (.inl p : Gamma.DPath) ∈ Z)
    (havoid : ∀ x ∈ p.support, x ∉ modificationBoundary R F) :
    p.edgeSet ⊆ U := by
  have hpE : p.edgeSet ⊆ (familyEdges Z \ R) ∪ F := by
    intro e he
    left
    refine ⟨?_, ?_⟩
    · simp only [familyEdges, Set.mem_iUnion]
      exact ⟨.inl p, hpZ, he⟩
    · intro heR
      exact havoid e.1 (p.edgeSet_subset_support_prod he).1
        (Or.inl ⟨e, heR, rfl⟩)
  have hstartInitial : p.start ∈ Gamma.initialSet Z := ⟨.inl p, hpZ, rfl⟩
  rw [initialSet_eq_vertexSet_diff_hasIncoming hZ hZfin] at hstartInitial
  have hnoIn : ¬HasIncoming ((familyEdges Z \ R) ∪ F) p.start := by
    rintro ⟨x, hx⟩
    rcases hx with hxOld | hxNew
    · exact hstartInitial.2 ⟨x, hxOld.1⟩
    · exact havoid p.start p.start_mem_support
        (Or.inr ⟨(x, p.start), hxNew, rfl⟩)
  exact walk_edges_subset_of_same_balance hsub hunique hbalance
    p.walk hpE (Or.inl hnoIn)

/-- Every missing old edge lies on one of the finitely many touched owners. -/
theorem oldEdges_sdiff_subset_modificationOwnerCarrier_prod
    {Z : Set Gamma.DPath} (hZ : Gamma.IsWarp Z)
    (hZfin : Gamma.HasFiniteCharacter Z)
    {R F U : Set (V × V)}
    (hsub : U ⊆ (familyEdges Z \ R) ∪ F)
    (hunique : Relator.RightUnique
      (fun x y ↦ (x, y) ∈ (familyEdges Z \ R) ∪ F))
    (hbalance : ∀ x, edgeBalance U x =
      edgeBalance ((familyEdges Z \ R) ∪ F) x) :
    familyEdges Z \ U ⊆
      modificationOwnerCarrier hZ R F ×ˢ modificationOwnerCarrier hZ R F := by
  intro e he
  have heZ := he.1
  simp only [familyEdges, Set.mem_iUnion] at heZ
  obtain ⟨p, hpZ, hep⟩ := heZ
  obtain ⟨q, rfl⟩ := hZfin hpZ
  have htouched : ∃ x ∈ q.support, x ∈ modificationBoundary R F := by
    by_contra hnot
    have havoid : ∀ x ∈ q.support, x ∉ modificationBoundary R F := by
      intro x hx hboundary
      exact hnot ⟨x, hx, hboundary⟩
    exact he.2 (oldPath_edges_subset_of_avoids_modificationBoundary
      hZ hZfin hsub hunique hbalance q hpZ havoid hep)
  obtain ⟨x, hxq, hxb⟩ := htouched
  have hcovered : q.support ⊆ modificationOwnerCarrier hZ R F := by
    intro z hz
    apply Set.mem_iUnion.mpr
    refine ⟨x, Set.mem_iUnion.mpr ⟨hxb, ?_⟩⟩
    rw [coveredPathSupport_eq_of_mem hZ hpZ hxq]
    exact hz
  exact ⟨hcovered (q.edgeSet_subset_support_prod hep).1,
    hcovered (q.edgeSet_subset_support_prod hep).2⟩

/-- The finite-difference certificate for any balanced reducing realization.
In particular cycle deletion cannot discard infinitely many untouched old
edges. The theorem does not assume that the output uses all switched edges. -/
theorem finite_edge_differences_of_same_balance
    {Z : Set Gamma.DPath} (hZ : Gamma.IsWarp Z)
    (hZfin : Gamma.HasFiniteCharacter Z)
    {R F U : Set (V × V)} (hR : R.Finite) (hF : F.Finite)
    (hsub : U ⊆ (familyEdges Z \ R) ∪ F)
    (hunique : Relator.RightUnique
      (fun x y ↦ (x, y) ∈ (familyEdges Z \ R) ∪ F))
    (hbalance : ∀ x, edgeBalance U x =
      edgeBalance ((familyEdges Z \ R) ∪ F) x) :
    (familyEdges Z \ U).Finite ∧ (U \ familyEdges Z).Finite := by
  constructor
  · have hC := modificationOwnerCarrier_finite hZ hZfin hR hF
    exact (hC.prod hC).subset
      (oldEdges_sdiff_subset_modificationOwnerCarrier_prod
        hZ hZfin hsub hunique hbalance)
  · apply hF.subset
    intro e he
    rcases hsub he.1 with heOld | heNew
    · exact (he.2 heOld.1).elim
    · exact heNew

#print axioms walk_edges_subset_of_same_balance
#print axioms finite_edge_differences_of_same_balance

end Erdos599.Alternating.SwitchingCore.RelationalReduction
