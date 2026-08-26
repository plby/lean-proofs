/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.ShortCycle
import ErdosProblems.Erdos570.RamseyRegion
import ErdosProblems.Erdos570.CycleCode
import Mathlib.Data.Fintype.Pigeonhole

/-!
# The deletable-vertex branch for the quadrilateral

This is the main local induction in the `C₄` proof.  If deleting a target
vertex of degree at least two is removed, a low red-degree host
vertex is an immediate blue apex.  Otherwise every host vertex has many red
neighbors; deleting one vertex and `d+1` of those neighbors leaves room for
the smaller target, and pigeonhole closes a red rectangle.
-/

open scoped SimpleGraph

namespace Erdos569

open Erdos570

open Erdos79

theorem ramseyAt_c4_of_degree_ge_two
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (v : Fin H.vertexCount) (hd : 2 ≤ H.graph.degree v)
    (horder : H.vertexCount ≤ H.edgeCount)
    (hIH : ∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
      graphRamseyNumber (cycleCode 4) Q ≤ (3 * Q.edgeCount + 1)) :
    RamseyAt (cycleCode 4) H ((3 * H.edgeCount + 1)) := by
  classical
  let d := H.graph.degree v
  let m := H.edgeCount
  let N := (3 * m + 1)
  let Q := supportCode (deleteVertexCode H v)
  have hdle : d ≤ m := by
    dsimp only [d, m]
    rw [GraphCode.edgeCount_eq_card_edgeFinset]
    exact H.graph.degree_le_card_edgeFinset (v := v)
  have hQedge : Q.edgeCount = m - d := by
    simp [Q, m, d, deleteVertexCode_edgeCount]
  have hQlt : Q.edgeCount < m := by
    rw [hQedge]
    omega
  have hQram : graphRamseyNumber (cycleCode 4) Q ≤
      (3 * (m - d) + 1) := by
    rw [← hQedge]
    exact hIH Q (supportCode_noIsolated _) (by simpa [m] using hQlt)
  have hQat : RamseyAt (cycleCode 4) Q ((3 * (m - d) + 1)) :=
    ramseyAt_of_graphRamseyNumber_le hQram
  intro C
  let : DecidableRel C.Adj := Classical.decRel _
  by_cases hred : (cycleCode 4).graph ⊑ C
  · exact Or.inl hred
  by_cases hblue : H.graph ⊑ Cᶜ
  · exact Or.inr hblue
  have hlowImpossible : ∀ w : Fin N, d < C.degree w := by
    intro w
    by_contra hnle
    have hwdeg : C.degree w ≤ d := Nat.le_of_not_gt hnle
    let closed : Finset (Fin N) := insert w (C.neighborFinset w)
    let S : Finset (Fin N) := closedᶜ
    have hwNotNeighbor : w ∉ C.neighborFinset w := by simp
    have hclosedCard : closed.card = C.degree w + 1 := by
      simp [closed, hwNotNeighbor, Nat.add_comm]
    have hreserve : (3 * (m - d) + 1) + (d + 1) ≤ N := by
      dsimp only [N]
      omega
    have hroom : (3 * (m - d) + 1) ≤ S.card := by
      rw [show S.card = N - closed.card by
        simp [S, Finset.card_compl]]
      rw [hclosedCard]
      omega
    rcases Erdos570.RamseyAt.on_finset hQat C S hroom with hcycleS | hcopyQ
    · exact hred (hcycleS.trans
        (SimpleGraph.Embedding.induce (S : Set (Fin N))).isContained) |>.elim
    · have hdeleteRoom : (deleteVertexCode H v).vertexCount ≤ S.card := by
        rw [show S.card = N - closed.card by
          simp [S, Finset.card_compl]]
        rw [hclosedCard, deleteVertexCode_vertexCount]
        have hdOrder : d < H.vertexCount := by
          dsimp only [d]
          simpa using H.graph.degree_lt_card_verts v
        have hNbase : 2 * m + 1 ≤ N := by
          dsimp only [N]
          omega
        apply Nat.le_sub_of_add_le
        omega
      have hdeleteRegion : (deleteVertexCode H v).graph ⊑
          Cᶜ.induce (S : Set (Fin N)) :=
        isContained_induce_of_supportCode_isContained Cᶜ S hcopyQ hdeleteRoom
      have hcopyDelete :
          H.graph.induce ({v} : Set (Fin H.vertexCount))ᶜ ⊑
            Cᶜ.induce (S : Set (Fin N)) :=
        deleteVertexGraph_isContained_of_code_isContained v hdeleteRegion
      have hwS : w ∉ S := by simp [S, closed]
      have hwBlue : ∀ x ∈ S, Cᶜ.Adj w x := by
        intro x hx
        have hxClosed : x ∉ closed := by simpa [S] using hx
        have hxw : x ≠ w := by
          intro h
          subst x
          exact hxClosed (by simp [closed])
        have hxNotAdj : ¬C.Adj w x := by
          intro hadj
          apply hxClosed
          simp [closed, C.mem_neighborFinset, hadj]
        exact (SimpleGraph.compl_adj C w x).2 ⟨hxw.symm, hxNotAdj⟩
      exact hblue (isContained_of_deleteVertex_copy_and_apex
        H v C S w hwS hcopyDelete hwBlue) |>.elim
  have hhigh : ∀ w : Fin N, d + 1 ≤ C.degree w := by
    intro w
    exact (Nat.succ_le_iff).2 (hlowImpossible w)
  have hNpos : 0 < N := by
    dsimp only [N, m]
    omega
  let w : Fin N := ⟨0, hNpos⟩
  have hchoose : d + 1 ≤ (C.neighborFinset w).card := by
    simpa only [SimpleGraph.degree] using hhigh w
  obtain ⟨Y, hYneighbor, hYcard⟩ := Finset.exists_subset_card_eq hchoose
  have hwY : w ∉ Y := by
    intro hw
    have : w ∈ C.neighborFinset w := hYneighbor hw
    simp at this
  let removed : Finset (Fin N) := insert w Y
  let S : Finset (Fin N) := removedᶜ
  have hremovedCard : removed.card = d + 2 := by
    simp [removed, hwY, hYcard]
  have hreserve : (3 * (m - d) + 1) + (d + 2) ≤ N := by
    dsimp only [N]
    omega
  have hroom : (3 * (m - d) + 1) ≤ S.card := by
    rw [show S.card = N - removed.card by simp [S, Finset.card_compl]]
    rw [hremovedCard]
    omega
  rcases Erdos570.RamseyAt.on_finset hQat C S hroom with hcycleS | hcopyQ
  · exact Or.inl (hcycleS.trans
      (SimpleGraph.Embedding.induce (S : Set (Fin N))).isContained)
  · have hdeleteRoom : (deleteVertexCode H v).vertexCount ≤ S.card := by
      rw [show S.card = N - removed.card by simp [S, Finset.card_compl]]
      rw [hremovedCard, deleteVertexCode_vertexCount]
      have hdOrder : d < H.vertexCount := by
        dsimp only [d]
        simpa using H.graph.degree_lt_card_verts v
      have hNbase : 2 * m + 1 ≤ N := by
        dsimp only [N]
        omega
      apply Nat.le_sub_of_add_le
      omega
    have hdeleteRegion : (deleteVertexCode H v).graph ⊑
        Cᶜ.induce (S : Set (Fin N)) :=
      isContained_induce_of_supportCode_isContained Cᶜ S hcopyQ hdeleteRoom
    have hcopyDelete :
        H.graph.induce ({v} : Set (Fin H.vertexCount))ᶜ ⊑
          Cᶜ.induce (S : Set (Fin N)) :=
      deleteVertexGraph_isContained_of_code_isContained v hdeleteRegion
    obtain ⟨copy⟩ := hcopyDelete
    let D := {x : Fin H.vertexCount // x ≠ v}
    let lift : D → {x : Fin H.vertexCount //
        x ∈ ({v} : Set (Fin H.vertexCount))ᶜ} := fun x ↦ ⟨x.1, by
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2⟩
    let image : D → Fin N := fun x ↦ (copy (lift x)).1
    have himageMem (x : D) : image x ∈ S := (copy (lift x)).2
    let neighborLift : H.graph.neighborFinset v → D := fun x ↦
      ⟨x.1, (H.graph.ne_of_adj
        ((H.graph.mem_neighborFinset v x.1).mp x.2)).symm⟩
    have badExists (y : Y) : ∃ x : H.graph.neighborFinset v,
        C.Adj y.1 (image (neighborLift x)) := by
      by_contra hall
      have hallBlue : ∀ x : H.graph.neighborFinset v,
          Cᶜ.Adj y.1 (image (neighborLift x)) := by
        intro x
        rw [SimpleGraph.compl_adj]
        have hyS : y.1 ∉ S := by simp [S, removed, y.2]
        have hne : y.1 ≠ image (neighborLift x) := by
          intro heq
          exact hyS (heq ▸ himageMem (neighborLift x))
        refine ⟨hne, ?_⟩
        exact not_exists.mp hall x
      have hyS : y.1 ∉ S := by simp [S, removed, y.2]
      apply hblue
      apply isContained_of_deleteVertex_copy_and_apex_on_copy
        H v C S y.1 hyS copy
      intro z hvz
      let zn : H.graph.neighborFinset v :=
        ⟨z.1, (H.graph.mem_neighborFinset v z.1).mpr hvz⟩
      have hzlift : lift (neighborLift zn) = z := by
        apply Subtype.ext
        rfl
      simpa [image, hzlift] using hallBlue zn
    let bad : Y → H.graph.neighborFinset v := fun y ↦
      Classical.choose (badExists y)
    have hbadRed (y : Y) :
        C.Adj y.1 (image (neighborLift (bad y))) := by
      exact Classical.choose_spec (badExists y)
    have hdomain : Fintype.card Y = d + 1 := by simpa using hYcard
    have hcodomain : Fintype.card (H.graph.neighborFinset v) = d := by
      rw [Fintype.card_coe]
      exact H.graph.card_neighborFinset_eq_degree v
    obtain ⟨y₁, y₂, hyne, hbadEq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt bad (by omega)
    let x := image (neighborLift (bad y₁))
    have hxEq : image (neighborLift (bad y₂)) = x := by
      simp [x, hbadEq]
    have hwy₁ : C.Adj w y₁.1 := by
      exact (C.mem_neighborFinset w y₁.1).mp (hYneighbor y₁.2)
    have hwy₂ : C.Adj w y₂.1 := by
      exact (C.mem_neighborFinset w y₂.1).mp (hYneighbor y₂.2)
    have hxy₁ : C.Adj x y₁.1 := (hbadRed y₁).symm
    have hxy₂ : C.Adj x y₂.1 := by
      rw [← hxEq]
      exact (hbadRed y₂).symm
    have hwx : w ≠ x := by
      intro heq
      have hwS : w ∉ S := by simp [S, removed]
      exact hwS (heq ▸ himageMem (neighborLift (bad y₁)))
    exact Or.inl (by
      simpa [cycleCode] using cycleGraph_four_isContained_of_rectangle
        hwy₁ hxy₁ hxy₂ hwy₂ hwx (Subtype.coe_ne_coe.mpr hyne))

end Erdos569
