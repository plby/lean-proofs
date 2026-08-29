/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GeneralArrow315
import ErdosProblems.Erdos599.SafeLinkAssertion68
import ErdosProblems.Erdos599.QuotientRoofTransport

/-!
# Final general-arrow assembly for Proposition 6.3

The countable ground wave is initially constructed after deleting the root
and the scheduling set `R`.  Assertion 6.6 shows that it avoids `Q`, so it
can be restricted through the additional deletion of `Q`.  Lemma 3.15 then
arrows it with the reduced quotient wave.  This file performs the required
dependent casts and records that Lemma 3.15 preserves the boundary roof.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace SafeLink

variable {V : Type u}

/-- Restrict a ground wave through the disjoint `Q` deletion and commute
the two vertex deletions. -/
noncomputable def restrictGroundWave (G : DWeb V) (R Q : Set V)
    (ground : (G.delete R).Wave)
    (havoid : Disjoint ((G.delete R).vertexSet ground.1) Q) :
    ((G.delete Q).delete R).Wave := by
  let groundQ : ((G.delete R).delete Q).Wave :=
    ⟨(G.delete R).restrictDeleteFamily Q ground.1 havoid,
      DWeb.IsWave.restrictDeleteFamily (G.delete R) ground.2 havoid⟩
  have heq : (G.delete R).delete Q = (G.delete Q).delete R := by
    simp only [G.delete_delete]
    congr 1
    ext x
    simp only [Set.mem_union]
    tauto
  exact heq ▸ groundQ

@[simp]
theorem terminalFrontier_restrictGroundWave
    (G : DWeb V) (R Q : Set V)
    (ground : (G.delete R).Wave)
    (havoid : Disjoint ((G.delete R).vertexSet ground.1) Q) :
    ((G.delete Q).delete R).terminalFrontier
        (restrictGroundWave G R Q ground havoid).1 =
      (G.delete R).terminalFrontier ground.1 := by
  let groundQ : ((G.delete R).delete Q).Wave :=
    ⟨(G.delete R).restrictDeleteFamily Q ground.1 havoid,
      DWeb.IsWave.restrictDeleteFamily (G.delete R) ground.2 havoid⟩
  let heq : (G.delete R).delete Q = (G.delete Q).delete R := by
    simp only [G.delete_delete]
    congr 1
    ext x
    simp only [Set.mem_union]
    tauto
  change ((G.delete Q).delete R).terminalFrontier (heq ▸ groundQ).1 = _
  rw [DWeb.terminalFrontier_castWebWave]
  dsimp only [groundQ]
  rw [(G.delete R).terminalFrontier_restrictDeleteFamily]

/-- A roof obtained before the disjoint `Q` deletion remains a roof after
the two deletions are commuted. -/
theorem roof_restrictGroundWave
    (G : DWeb V) (R Q : Set V)
    (ground : (G.delete R).Wave)
    (havoid : Disjoint ((G.delete R).vertexSet ground.1) Q)
    {z : V}
    (hz : z ∈ (G.delete R).roof
      ((G.delete R).terminalFrontier ground.1)) :
    z ∈ ((G.delete Q).delete R).roof
      (((G.delete Q).delete R).terminalFrontier
        (restrictGroundWave G R Q ground havoid).1) := by
  rw [terminalFrontier_restrictGroundWave]
  intro p hp
  let q : DirectedPath.FinitePath (G.delete R).graph :=
    p.lift (fun {_ _}
      (e : ((G.delete Q).delete R).graph.Adj _ _) ↦
        ⟨e.1.1, e.2.1, e.2.2⟩)
  have hq : (G.delete R).IsTargetPathFrom z q := by
    exact ⟨hp.1, hp.2.1.1, hp.2.2⟩
  obtain ⟨x, hxq, hxTerm⟩ := hz q hq
  have hsupp : q.support = p.support := by
    dsimp only [q]
    exact _root_.Erdos599.DirectedPath.FinitePath.support_lift _ p
  exact ⟨x, hsupp ▸ hxq, hxTerm⟩

/-- Once every reduced quotient path meets the retained ground roof,
Lemma 3.15 produces the boundary-roofing wave in the common web with the
root and `Q` deleted. -/
theorem finalBoundaryWave_of_ground_and_quotient
    (G : DWeb V) (hG : G.IsNormalized) {a : V}
    {T X R Q : Set V} (hT : G.IsTreeSet a T)
    (hXT : X ⊆ T \ {a}) (hRX : R ⊆ X)
    (ground : ((G.delete {a}).delete R).Wave)
    (hgroundQ : Disjoint (((G.delete {a}).delete R).vertexSet ground.1) Q)
    (W : (((G.delete {a}).delete Q).quotient X).Wave)
    (hmeet : ∀ p ∈ W.1, ∃ u ∈ p.support, u ∉ R ∧
      u ∈ (((G.delete {a}).delete Q).delete R).roof
        ((((G.delete {a}).delete Q).delete R).terminalFrontier
          (restrictGroundWave (G.delete {a}) R Q ground hgroundQ).1))
    {y : V}
    (hyground : y ∈ ((G.delete {a}).delete R).roof
      (((G.delete {a}).delete R).terminalFrontier ground.1)) :
    ∃ U : Set ((G.delete (insert a Q)).DPath),
      (G.delete (insert a Q)).IsWave U ∧
        y ∈ (G.delete (insert a Q)).roof
          ((G.delete (insert a Q)).terminalFrontier U) := by
  let base := G.delete {a}
  let H := base.delete Q
  let groundH : (H.delete R).Wave :=
    restrictGroundWave base R Q ground hgroundQ
  let L : Set H.DPath := H.arrow (H.liftDeleteFamily R groundH.1)
    (liftQuotientFamily H X W.1)
  have hNoEnterBase : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  have hNoEnterH : H.NoEdgeEnters H.source := hNoEnterBase.delete
  have hSourceX : Disjoint H.source X := by
    exact (tree_offRoot_disjoint_delete_source G hT hXT).mono_left
      Set.sdiff_subset
  have hL : H.IsWave L := by
    exact H.isWave_arrow_delete_quotient hRX hNoEnterH hSourceX
      groundH.2 W.2 hmeet
  have hyGroundH : y ∈ (H.delete R).roof
      ((H.delete R).terminalFrontier groundH.1) :=
    roof_restrictGroundWave base R Q ground hgroundQ hyground
  have hyL : y ∈ H.roof (H.terminalFrontier L) := by
    exact H.roof_delete_subset_arrow_delete_quotient hRX hNoEnterH
      hSourceX groundH.2 W.2 hmeet hyGroundH
  have heq : H = G.delete (insert a Q) := by
    dsimp only [H, base]
    rw [G.delete_delete]
    congr 1
  rw [← heq]
  exact ⟨L, hL, hyL⟩

end SafeLink

end Erdos599
