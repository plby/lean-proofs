/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceTheorem66Adapters
import ErdosProblems.Erdos916.AHTSourceTheorem66Case4

/-!
# Component adapters for the deleted-centre AHT splitter

The Watkins--Mesner splitter used in AHT Theorem 6.6 lives in
`deleteVertex G center`.  This file transports its literal finite component
and external-boundary predicates to the ambient graph.  The ambient deletion
set is the image of the splitter deletion set together with `center`.
-/

namespace Erdos916

open _root_.SimpleGraph
open AHTClaim3CardinalityCertificateDeleted

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

@[simp] theorem ahtDeletedFinsetVal_union {center : V}
    (S T : Finset {v : V // v ≠ center}) :
    ahtDeletedFinsetVal (S ∪ T) =
      ahtDeletedFinsetVal S ∪ ahtDeletedFinsetVal T := by
  simp [ahtDeletedFinsetVal, Finset.map_union]

@[simp] theorem ahtDeletedFinsetVal_insert {center : V}
    (q : {v : V // v ≠ center})
    (S : Finset {v : V // v ≠ center}) :
    ahtDeletedFinsetVal (insert q S) =
      insert q.1 (ahtDeletedFinsetVal S) := by
  simp [ahtDeletedFinsetVal]

@[simp] theorem ahtDeletedFinsetVal_singleton {center : V}
    (q : {v : V // v ≠ center}) :
    ahtDeletedFinsetVal ({q} : Finset {v : V // v ≠ center}) =
      ({q.1} : Finset V) := by
  simp [ahtDeletedFinsetVal]

/-- Local component-coincidence lemma for the adapter layer.  Two literal
components of the same vertex-deleted graph that share a vertex have the
same carrier. -/
theorem component_mem_of_shared
    {S C D : Finset V} (hC : IsComponentAfterDeleting G S C)
    (hD : IsComponentAfterDeleting G S D) {w v : V}
    (hwC : w ∈ C) (hwD : w ∈ D) (hvD : v ∈ D) : v ∈ C := by
  let wD : {q : V // q ∈ (D : Set V)} := ⟨w, hwD⟩
  let vD : {q : V // q ∈ (D : Set V)} := ⟨v, hvD⟩
  obtain ⟨p⟩ := hD.2.2.1.preconnected wD vD
  have walk_mem : ∀ {a b : {q : V // q ∈ (D : Set V)}}
      (q : (G.induce (D : Set V)).Walk a b), a.1 ∈ C → b.1 ∈ C := by
    intro a b q ha
    induction q with
    | nil => exact ha
    | @cons a b c hab q ih =>
        apply ih
        exact hC.2.2.2 a.1 ha b.1
          (fun hbS ↦ Finset.disjoint_left.mp hD.2.1 b.2 hbS) hab
  exact walk_mem p hwC

/-- A neighbour finset contained in two displayed vertices has cardinality,
and hence degree, at most two. -/
theorem degree_le_two_of_neighborFinset_subset_pair_local
    {p a b : V} (hsub : G.neighborFinset p ⊆ {a, b}) :
    G.degree p ≤ 2 := by
  rw [← G.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_insert_le a ({b} : Finset V)).trans (by simp))

/-- A literal component of the centre-deleted graph is the same ambient
component after also placing `center` in the deletion set. -/
theorem IsComponentAfterDeleting.ambient_of_deleteVertex
    {center : V} {S C : Finset {v : V // v ≠ center}}
    (hC : IsComponentAfterDeleting (deleteVertex G center) S C) :
    IsComponentAfterDeleting G
      (ahtDeletedFinsetVal S ∪ {center}) (ahtDeletedFinsetVal C) := by
  classical
  have hdisMapped :
      Disjoint (ahtDeletedFinsetVal C) (ahtDeletedFinsetVal S) :=
    disjoint_ahtDeletedFinsetVal hC.2.1
  have hdis : Disjoint (ahtDeletedFinsetVal C)
      (ahtDeletedFinsetVal S ∪ {center}) := by
    apply Finset.disjoint_right.mpr
    intro q hqSep hqC
    rcases Finset.mem_union.mp hqSep with hqS | hqCenter
    · exact Finset.disjoint_left.mp hdisMapped hqC hqS
    · have hqc : q = center := by simpa using hqCenter
      exact center_not_mem_ahtDeletedFinsetVal C (hqc ▸ hqC)
  let inc :
      (deleteVertex G center).induce (C : Set {v : V // v ≠ center}) →g
        G.induce (ahtDeletedFinsetVal C : Set V) :=
    { toFun := fun q ↦ ⟨q.1.1, val_mem_ahtDeletedFinsetVal.mpr q.2⟩
      map_rel' := by
        intro p q hpq
        exact (deleteVertex_adj (G := G)).mp hpq }
  have hincSurj : Function.Surjective inc := by
    rintro ⟨q, hqC⟩
    obtain ⟨q', hq'C, hq'val⟩ :=
      exists_subtype_of_mem_ahtDeletedFinsetVal hqC
    refine ⟨⟨q', hq'C⟩, ?_⟩
    apply Subtype.ext
    exact hq'val
  have hconn : (G.induce (ahtDeletedFinsetVal C : Set V)).Connected :=
    hC.2.2.1.map inc hincSurj
  refine ⟨ahtDeletedFinsetVal_nonempty.mpr hC.1, hdis, hconn, ?_⟩
  intro u huC v hvSep huv
  obtain ⟨u', hu'C, hu'val⟩ :=
    exists_subtype_of_mem_ahtDeletedFinsetVal huC
  have hvc : v ≠ center := by
    intro h
    apply hvSep
    exact Finset.mem_union_right _ (by simp [h])
  let v' : {w : V // w ≠ center} := ⟨v, hvc⟩
  have hvS : v' ∉ S := by
    intro hvS
    apply hvSep
    apply Finset.mem_union_left
    exact val_mem_ahtDeletedFinsetVal.mpr hvS
  have huvDel : (deleteVertex G center).Adj u' v' :=
    (deleteVertex_adj (G := G)).mpr (by simpa [hu'val] using huv)
  have hvC : v' ∈ C := hC.2.2.2 u' hu'C v' hvS huvDel
  exact val_mem_ahtDeletedFinsetVal.mpr hvC

/-- An external boundary in the centre-deleted graph maps to the same
ambient boundary, with `center` added as the only possible new neighbour. -/
theorem HasExternalBoundaryIn.ambient_of_deleteVertex
    {center : V} {C T : Finset {v : V // v ≠ center}}
    (hboundary : HasExternalBoundaryIn (deleteVertex G center) C T) :
    HasExternalBoundaryIn G (ahtDeletedFinsetVal C)
      (ahtDeletedFinsetVal T ∪ {center}) := by
  intro u huC v huv hvC
  by_cases hvc : v = center
  · exact Finset.mem_union_right _ (by simp [hvc])
  obtain ⟨u', hu'C, hu'val⟩ :=
    exists_subtype_of_mem_ahtDeletedFinsetVal huC
  let v' : {w : V // w ≠ center} := ⟨v, hvc⟩
  have hvC' : v' ∉ C := by
    intro hv'
    apply hvC
    exact val_mem_ahtDeletedFinsetVal.mpr hv'
  have huvDel : (deleteVertex G center).Adj u' v' :=
    (deleteVertex_adj (G := G)).mpr (by simpa [hu'val] using huv)
  have hvT : v' ∈ T := hboundary u' hu'C v' huvDel hvC'
  exact Finset.mem_union_left _ (val_mem_ahtDeletedFinsetVal.mpr hvT)

/-- Remove the added centre from a mapped external boundary when the
component has no edge to that centre. -/
theorem HasExternalBoundaryIn.erase_center
    {C T : Finset V} {center : V}
    (hboundary : HasExternalBoundaryIn G C (T ∪ {center}))
    (hnoCenter : ∀ u ∈ C, ¬G.Adj u center) :
    HasExternalBoundaryIn G C T := by
  intro u huC v huv hvC
  rcases Finset.mem_union.mp (hboundary u huC v huv hvC) with hvT | hvc
  · exact hvT
  · have hveq : v = center := by simpa using hvc
    exact False.elim (hnoCenter u huC (by simpa [hveq] using huv))

/-- The form used for a centre-deleted splitter component which has no
ambient edge to the deleted centre. -/
theorem HasExternalBoundaryIn.ambient_of_deleteVertex_of_no_center
    {center : V} {C T : Finset {v : V // v ≠ center}}
    (hboundary : HasExternalBoundaryIn (deleteVertex G center) C T)
    (hnoCenter : ∀ u ∈ ahtDeletedFinsetVal C, ¬G.Adj u center) :
    HasExternalBoundaryIn G (ahtDeletedFinsetVal C)
      (ahtDeletedFinsetVal T) := by
  exact (hboundary.ambient_of_deleteVertex).erase_center hnoCenter

/-- Condition (vii) for a component of the centre-deleted splitter becomes
the ambient left/right boundary dichotomy once that component has no edge to
the deleted centre.  The three matched-pair alternatives are eliminated by
ambient three-connectivity. -/
theorem WatkinsMesnerSplitter.ambient_component_boundary_left_or_right
    {center : V} {x y z : {v : V // v ≠ center}}
    (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)
    (hthree : IsThreeConnected G)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    {D : Finset {v : V // v ≠ center}}
    (hD : IsComponentAfterDeleting (deleteVertex G center)
      (S.aSet ∪ S.bSet) D)
    (hnoCenter : ∀ u ∈ ahtDeletedFinsetVal D, ¬G.Adj u center) :
    HasExternalBoundaryIn G (ahtDeletedFinsetVal D)
        (ahtDeletedFinsetVal S.aSet) ∨
      HasExternalBoundaryIn G (ahtDeletedFinsetVal D)
        (ahtDeletedFinsetVal S.bSet) := by
  have hDambient : IsComponentAfterDeleting G
      (ahtDeletedFinsetVal S.aSet ∪
        ahtDeletedFinsetVal S.bSet ∪ {center})
      (ahtDeletedFinsetVal D) := by
    simpa using hD.ambient_of_deleteVertex
  have hcenterAB :
      center ∉ ahtDeletedFinsetVal S.aSet ∪
        ahtDeletedFinsetVal S.bSet := by
    simp [center_not_mem_ahtDeletedFinsetVal]
  have hoptions := S.component_boundary_of_both_triples
    hAcard hBcard D hD
  have hoptionsAmbient :
      HasExternalBoundaryIn G (ahtDeletedFinsetVal D)
          (ahtDeletedFinsetVal S.aSet) ∨
        HasExternalBoundaryIn G (ahtDeletedFinsetVal D)
          (ahtDeletedFinsetVal S.bSet) ∨
        HasExternalBoundaryIn G (ahtDeletedFinsetVal D)
          {S.xA.1, S.xB.1} ∨
        HasExternalBoundaryIn G (ahtDeletedFinsetVal D)
          {S.yA.1, S.yB.1} ∨
        HasExternalBoundaryIn G (ahtDeletedFinsetVal D)
          {S.zA.1, S.zB.1} := by
    rcases hoptions with hA | hB | hX | hY | hZ
    · exact Or.inl (hA.ambient_of_deleteVertex_of_no_center hnoCenter)
    · exact Or.inr (Or.inl
        (hB.ambient_of_deleteVertex_of_no_center hnoCenter))
    · exact Or.inr (Or.inr (Or.inl (by
        simpa using hX.ambient_of_deleteVertex_of_no_center hnoCenter)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        simpa using hY.ambient_of_deleteVertex_of_no_center hnoCenter))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by
        simpa using hZ.ambient_of_deleteVertex_of_no_center hnoCenter))))
  exact component_boundary_in_left_or_right_of_both_triples
    hthree (ahtDeletedFinsetVal S.aSet)
      (ahtDeletedFinsetVal S.bSet) (ahtDeletedFinsetVal D) center
      hDambient hcenterAB
      (val_mem_ahtDeletedFinsetVal.mpr S.X_A_attachment.1)
      (val_mem_ahtDeletedFinsetVal.mpr S.Y_A_attachment.1)
      (val_mem_ahtDeletedFinsetVal.mpr S.Z_A_attachment.1)
      (val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1)
      (val_mem_ahtDeletedFinsetVal.mpr S.Y_B_attachment.1)
      (val_mem_ahtDeletedFinsetVal.mpr S.Z_B_attachment.1)
      hoptionsAmbient

namespace WatkinsMesnerSplitter

variable {center : V} {x y z : {v : V // v ≠ center}}
variable (S : WatkinsMesnerSplitter (deleteVertex G center) x y z)

theorem adj_x_xA_of_xPart_card_one (hx : S.xPart.card = 1) :
    G.Adj x.1 S.xA.1 := by
  obtain ⟨w, hwX, hwxA⟩ := S.X_A_attachment.2.1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hx
  have hwt : w = t := by simpa [ht] using hwX
  have hxt : x = t := by simpa [ht] using S.x_mem_X
  have hwx : w = x := hwt.trans hxt.symm
  exact (deleteVertex_adj (G := G)).mp (hwx ▸ hwxA)

theorem adj_x_xB_of_xPart_card_one (hx : S.xPart.card = 1) :
    G.Adj x.1 S.xB.1 := by
  obtain ⟨w, hwX, hwxB⟩ := S.X_B_attachment.2.1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hx
  have hwt : w = t := by simpa [ht] using hwX
  have hxt : x = t := by simpa [ht] using S.x_mem_X
  have hwx : w = x := hwt.trans hxt.symm
  exact (deleteVertex_adj (G := G)).mp (hwx ▸ hwxB)

/-- A splitter-side vertex is distinct from all three displayed terminal
vertices.  Keeping this in the centre-deleted subtype avoids repeatedly
reconstructing the same component-disjointness argument in Claim (8). -/
theorem aSet_val_ne_terminals {a : {v : V // v ≠ center}}
    (ha : a ∈ S.aSet) :
    a.1 ≠ x.1 ∧ a.1 ≠ y.1 ∧ a.1 ≠ z.1 := by
  constructor
  · intro hax
    have hax' : a = x := Subtype.ext hax
    exact Finset.disjoint_left.mp S.X_component.2.1 S.x_mem_X
      (Finset.mem_union_left _ (hax' ▸ ha))
  constructor
  · intro hay
    have hay' : a = y := Subtype.ext hay
    exact Finset.disjoint_left.mp S.Y_component.2.1 S.y_mem_Y
      (Finset.mem_union_left _ (hay' ▸ ha))
  · intro haz
    have haz' : a = z := Subtype.ext haz
    exact Finset.disjoint_left.mp S.Z_component.2.1 S.z_mem_Z
      (Finset.mem_union_left _ (haz' ▸ ha))

theorem a_attachments_pairwise_ne_of_card_three
    (hAcard : S.aSet.card = 3) :
    S.xA ≠ S.yA ∧ S.xA ≠ S.zA ∧ S.yA ≠ S.zA := by
  have hEq := S.A_eq
  constructor
  · intro hxy
    have hsub : S.aSet ⊆ ({S.yA, S.zA} :
        Finset {v : V // v ≠ center}) := by
      intro q hq
      rw [hEq] at hq
      simpa [hxy] using hq
    have hle := Finset.card_le_card hsub
    have hpair : ({S.yA, S.zA} :
        Finset {v : V // v ≠ center}).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  constructor
  · intro hxz
    have hsub : S.aSet ⊆ ({S.yA, S.zA} :
        Finset {v : V // v ≠ center}) := by
      intro q hq
      rw [hEq] at hq
      simpa [hxz] using hq
    have hle := Finset.card_le_card hsub
    have hpair : ({S.yA, S.zA} :
        Finset {v : V // v ≠ center}).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  · intro hyz
    have hsub : S.aSet ⊆ ({S.xA, S.zA} :
        Finset {v : V // v ≠ center}) := by
      intro q hq
      rw [hEq] at hq
      simpa [hyz] using hq
    have hle := Finset.card_le_card hsub
    have hpair : ({S.xA, S.zA} :
        Finset {v : V // v ≠ center}).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega

theorem b_attachments_pairwise_ne_of_card_three
    (hBcard : S.bSet.card = 3) :
    S.xB ≠ S.yB ∧ S.xB ≠ S.zB ∧ S.yB ≠ S.zB := by
  have hEq := S.B_eq
  constructor
  · intro hxy
    have hsub : S.bSet ⊆ ({S.yB, S.zB} :
        Finset {v : V // v ≠ center}) := by
      intro q hq
      rw [hEq] at hq
      simpa [hxy] using hq
    have hle := Finset.card_le_card hsub
    have hpair : ({S.yB, S.zB} :
        Finset {v : V // v ≠ center}).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  constructor
  · intro hxz
    have hsub : S.bSet ⊆ ({S.yB, S.zB} :
        Finset {v : V // v ≠ center}) := by
      intro q hq
      rw [hEq] at hq
      simpa [hxz] using hq
    have hle := Finset.card_le_card hsub
    have hpair : ({S.yB, S.zB} :
        Finset {v : V // v ≠ center}).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  · intro hyz
    have hsub : S.bSet ⊆ ({S.xB, S.zB} :
        Finset {v : V // v ≠ center}) := by
      intro q hq
      rw [hEq] at hq
      simpa [hyz] using hq
    have hle := Finset.card_le_card hsub
    have hpair : ({S.xB, S.zB} :
        Finset {v : V // v ≠ center}).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega

/-- On a singleton splitter side all three named attachments are literally
the same subtype vertex. -/
theorem b_attachments_eq_of_card_one (hBcard : S.bSet.card = 1) :
    S.xB = S.yB ∧ S.xB = S.zB := by
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hBcard
  have hxb : S.xB = b := by simpa [hb] using S.X_B_attachment.1
  have hyb : S.yB = b := by simpa [hb] using S.Y_B_attachment.1
  have hzb : S.zB = b := by simpa [hb] using S.Z_B_attachment.1
  exact ⟨hxb.trans hyb.symm, hxb.trans hzb.symm⟩

theorem adj_y_yA_of_yPart_card_one (hy : S.yPart.card = 1) :
    G.Adj y.1 S.yA.1 := by
  obtain ⟨w, hwY, hwyA⟩ := S.Y_A_attachment.2.1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hy
  have hwt : w = t := by simpa [ht] using hwY
  have hyt : y = t := by simpa [ht] using S.y_mem_Y
  have hwy : w = y := hwt.trans hyt.symm
  exact (deleteVertex_adj (G := G)).mp (hwy ▸ hwyA)

theorem adj_y_yB_of_yPart_card_one (hy : S.yPart.card = 1) :
    G.Adj y.1 S.yB.1 := by
  obtain ⟨w, hwY, hwyB⟩ := S.Y_B_attachment.2.1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hy
  have hwt : w = t := by simpa [ht] using hwY
  have hyt : y = t := by simpa [ht] using S.y_mem_Y
  have hwy : w = y := hwt.trans hyt.symm
  exact (deleteVertex_adj (G := G)).mp (hwy ▸ hwyB)

theorem adj_z_zA_of_zPart_card_one (hz : S.zPart.card = 1) :
    G.Adj z.1 S.zA.1 := by
  obtain ⟨w, hwZ, hwzA⟩ := S.Z_A_attachment.2.1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hz
  have hwt : w = t := by simpa [ht] using hwZ
  have hzt : z = t := by simpa [ht] using S.z_mem_Z
  have hwz : w = z := hwt.trans hzt.symm
  exact (deleteVertex_adj (G := G)).mp (hwz ▸ hwzA)

theorem adj_z_zB_of_zPart_card_one (hz : S.zPart.card = 1) :
    G.Adj z.1 S.zB.1 := by
  obtain ⟨w, hwZ, hwzB⟩ := S.Z_B_attachment.2.1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hz
  have hwt : w = t := by simpa [ht] using hwZ
  have hzt : z = t := by simpa [ht] using S.z_mem_Z
  have hwz : w = z := hwt.trans hzt.symm
  exact (deleteVertex_adj (G := G)).mp (hwz ▸ hwzB)

/-- In the final singleton-terminal, both-triples branch there are no edges
between the two splitter sides.  Condition (vi) makes any such edge a
matched attachment edge, which would close a triangle through its terminal.
-/
theorem no_edges_between_sides_of_both_triples_singletons
    (htri : AHTTriangleFree G)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    (hx : S.xPart.card = 1) (hy : S.yPart.card = 1)
    (hz : S.zPart.card = 1) :
    ∀ a ∈ S.aSet, ∀ b ∈ S.bSet, ¬G.Adj a.1 b.1 := by
  intro a ha b hb hab
  have hdel : (deleteVertex G center).Adj a b :=
    (deleteVertex_adj (G := G)).mpr hab
  rcases S.matched_edges_of_both_triples hAcard hBcard
      a ha b hb hdel with hX | hY | hZ
  · have hxAB : G.Adj S.xA.1 S.xB.1 := by
      simpa [hX.1, hX.2] using hab
    exact htri (S.adj_x_xA_of_xPart_card_one hx)
      hxAB (S.adj_x_xB_of_xPart_card_one hx).symm
  · have hyAB : G.Adj S.yA.1 S.yB.1 := by
      simpa [hY.1, hY.2] using hab
    exact htri (S.adj_y_yA_of_yPart_card_one hy)
      hyAB (S.adj_y_yB_of_yPart_card_one hy).symm
  · have hzAB : G.Adj S.zA.1 S.zB.1 := by
      simpa [hZ.1, hZ.2] using hab
    exact htri (S.adj_z_zA_of_zPart_card_one hz)
      hzAB (S.adj_z_zB_of_zPart_card_one hz).symm

/-- The finite family of centre-free deletion components assigned to the
`A` side by condition (vii).  Its elements are ambient finsets, but every
member retains the literal component of `deleteVertex G center` from which
it arose. -/
noncomputable def ambientLeftComponents : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun C ↦
    ∃ D : Finset {v : V // v ≠ center},
      IsComponentAfterDeleting (deleteVertex G center)
          (S.aSet ∪ S.bSet) D ∧
        (∀ u ∈ ahtDeletedFinsetVal D, ¬G.Adj u center) ∧
        C = ahtDeletedFinsetVal D ∧
        HasExternalBoundaryIn G C (ahtDeletedFinsetVal S.aSet)

/-- The ambient `C_A` of the source proof: the union of all centre-free
components assigned to the `A` side. -/
noncomputable def ambientLeftCarrier : Finset V :=
  ahtComponentSideUnion S.ambientLeftComponents

theorem mem_ambientLeftComponents_iff (C : Finset V) :
    C ∈ S.ambientLeftComponents ↔
      ∃ D : Finset {v : V // v ≠ center},
        IsComponentAfterDeleting (deleteVertex G center)
            (S.aSet ∪ S.bSet) D ∧
          (∀ u ∈ ahtDeletedFinsetVal D, ¬G.Adj u center) ∧
          C = ahtDeletedFinsetVal D ∧
          HasExternalBoundaryIn G C (ahtDeletedFinsetVal S.aSet) := by
  classical
  simp only [ambientLeftComponents, Finset.mem_filter, Finset.mem_univ,
    true_and]

theorem ambientLeftCarrier_externalBoundary :
    HasExternalBoundaryIn G S.ambientLeftCarrier
      (ahtDeletedFinsetVal S.aSet) := by
  classical
  apply componentSideUnion_externalBoundary
  intro C hC
  exact (S.mem_ambientLeftComponents_iff C).mp hC |>.choose_spec.2.2.2

theorem ambientLeftCarrier_disjoint :
    Disjoint S.ambientLeftCarrier (ahtDeletedFinsetVal S.aSet) := by
  classical
  apply componentSideUnion_disjoint
  intro C hC
  obtain ⟨D, hD, -, rfl, -⟩ :=
    (S.mem_ambientLeftComponents_iff C).mp hC
  have hdis := disjoint_ahtDeletedFinsetVal hD.2.1
  rw [ahtDeletedFinsetVal_union] at hdis
  exact hdis.mono_right Finset.subset_union_left

theorem ambientLeftCarrier_disjoint_right :
    Disjoint S.ambientLeftCarrier (ahtDeletedFinsetVal S.bSet) := by
  classical
  apply componentSideUnion_disjoint
  intro C hC
  obtain ⟨D, hD, -, rfl, -⟩ :=
    (S.mem_ambientLeftComponents_iff C).mp hC
  have hdis := disjoint_ahtDeletedFinsetVal hD.2.1
  rw [ahtDeletedFinsetVal_union] at hdis
  exact hdis.mono_right Finset.subset_union_right

theorem center_not_mem_ambientLeftCarrier :
    center ∉ S.ambientLeftCarrier := by
  classical
  intro hcenter
  obtain ⟨C, hC, hcenterC⟩ := Finset.mem_biUnion.mp hcenter
  obtain ⟨D, -, -, rfl, -⟩ :=
    (S.mem_ambientLeftComponents_iff C).mp hC
  exact center_not_mem_ahtDeletedFinsetVal D hcenterC

theorem mem_ambientLeftCarrier_of_component
    {D : Finset {v : V // v ≠ center}}
    (hD : IsComponentAfterDeleting (deleteVertex G center)
      (S.aSet ∪ S.bSet) D)
    (hnoCenter : ∀ u ∈ ahtDeletedFinsetVal D, ¬G.Adj u center)
    (hleft : HasExternalBoundaryIn G (ahtDeletedFinsetVal D)
      (ahtDeletedFinsetVal S.aSet))
    {q : V} (hq : q ∈ ahtDeletedFinsetVal D) :
    q ∈ S.ambientLeftCarrier := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨ahtDeletedFinsetVal D, ?_, hq⟩
  apply (S.mem_ambientLeftComponents_iff _).mpr
  exact ⟨D, hD, hnoCenter, rfl, hleft⟩

theorem no_center_adj_of_disjoint_terminalParts
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    {D : Finset {v : V // v ≠ center}}
    (hDx : Disjoint D S.xPart) (hDy : Disjoint D S.yPart)
    (hDz : Disjoint D S.zPart) :
    ∀ u ∈ ahtDeletedFinsetVal D, ¬G.Adj u center := by
  intro u huD huc
  obtain ⟨u', hu'D, hu'val⟩ :=
    exists_subtype_of_mem_ahtDeletedFinsetVal huD
  rcases hcenterNeighbors huc.symm with hux | huy | huz
  · have hu'x : u' = x := Subtype.ext (hu'val.trans hux)
    exact Finset.disjoint_left.mp hDx hu'D (hu'x ▸ S.x_mem_X)
  · have hu'y : u' = y := Subtype.ext (hu'val.trans huy)
    exact Finset.disjoint_left.mp hDy hu'D (hu'y ▸ S.y_mem_Y)
  · have hu'z : u' = z := Subtype.ext (hu'val.trans huz)
    exact Finset.disjoint_left.mp hDz hu'D (hu'z ▸ S.z_mem_Z)

/-- In the both-triples branch, every neighbour of `y_A` is in the
`A`-side component union, is the singleton terminal `y`, lies back in `A`,
or is the matched attachment `y_B`.  This is the exact location field of
`AHTRelevantTripleSideLocal`; all component classification happens in the
centre-deleted graph and is transported only afterwards. -/
theorem yA_neighbor_location_of_both_triples
    (hthree : IsThreeConnected G)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    (hy : S.yPart.card = 1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1) :
    ∀ ⦃q : V⦄, G.Adj S.yA.1 q →
      q ∈ S.ambientLeftCarrier ∨ q = y.1 ∨
        q ∈ ahtDeletedFinsetVal S.aSet ∨ q = S.yB.1 := by
  classical
  have hneA := S.a_attachments_pairwise_ne_of_card_three hAcard
  have hcenterNotA : ∀ a ∈ S.aSet, ¬G.Adj a.1 center := by
    intro a haA hac
    rcases hcenterNeighbors hac.symm with hax | hay | haz
    · have hax' : a = x := Subtype.ext hax
      exact Finset.disjoint_left.mp S.X_component.2.1 S.x_mem_X
        (Finset.mem_union_left _ (hax' ▸ haA))
    · have hay' : a = y := Subtype.ext hay
      exact Finset.disjoint_left.mp S.Y_component.2.1 S.y_mem_Y
        (Finset.mem_union_left _ (hay' ▸ haA))
    · have haz' : a = z := Subtype.ext haz
      exact Finset.disjoint_left.mp S.Z_component.2.1 S.z_mem_Z
        (Finset.mem_union_left _ (haz' ▸ haA))
  intro q hyAq
  by_cases hqA : q ∈ ahtDeletedFinsetVal S.aSet
  · exact Or.inr (Or.inr (Or.inl hqA))
  by_cases hqB : q ∈ ahtDeletedFinsetVal S.bSet
  · obtain ⟨q', hq'B, hq'val⟩ :=
      exists_subtype_of_mem_ahtDeletedFinsetVal hqB
    have hdel : (deleteVertex G center).Adj S.yA q' :=
      (deleteVertex_adj (G := G)).mpr (by simpa [hq'val] using hyAq)
    rcases S.matched_edges_of_both_triples hAcard hBcard
        S.yA S.Y_A_attachment.1 q' hq'B hdel with hX | hY | hZ
    · exact False.elim (hneA.1 hX.1.symm)
    · right
      right
      right
      exact hq'val.symm.trans (congrArg Subtype.val hY.2)
    · exact False.elim (hneA.2.2 hZ.1)
  by_cases hqc : q = center
  · subst q
    exact False.elim (hcenterNotA S.yA S.Y_A_attachment.1 hyAq)
  let q' : {v : V // v ≠ center} := ⟨q, hqc⟩
  have hq'A : q' ∉ S.aSet := by
    intro h
    exact hqA (val_mem_ahtDeletedFinsetVal.mpr h)
  have hq'B : q' ∉ S.bSet := by
    intro h
    exact hqB (val_mem_ahtDeletedFinsetVal.mpr h)
  let K : Finset {v : V // v ≠ center} := S.aSet ∪ S.bSet
  have hqK : q' ∉ (K : Set {v : V // v ≠ center}) := by
    simpa only [K, Finset.mem_coe, Finset.mem_union, not_or] using
      And.intro hq'A hq'B
  let C : (deleteVertex G center).ComponentCompl (K : Set _) :=
    (deleteVertex G center).componentComplMk hqK
  let D : Finset {v : V // v ≠ center} :=
    componentCarrier K C
  have hD : IsComponentAfterDeleting (deleteVertex G center) K D :=
    isComponentAfterDeleting_componentCarrier K C
  have hqD : q' ∈ D := by
    change q' ∈ componentCarrier K C
    rw [mem_componentCarrier]
    exact ⟨hqK, rfl⟩
  by_cases hqX : q' ∈ S.xPart
  · have hdel : (deleteVertex G center).Adj q' S.yA :=
      (deleteVertex_adj (G := G)).mpr (by simpa using hyAq.symm)
    have heq := S.X_A_attachment.2.2 q' hqX S.yA
      S.Y_A_attachment.1 hdel
    exact False.elim (hneA.1 heq.symm)
  by_cases hqY : q' ∈ S.yPart
  · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hy
    have hqt : q' = t := by simpa [ht] using hqY
    have hyt : y = t := by simpa [ht] using S.y_mem_Y
    exact Or.inr (Or.inl (congrArg Subtype.val (hqt.trans hyt.symm)))
  by_cases hqZ : q' ∈ S.zPart
  · have hdel : (deleteVertex G center).Adj q' S.yA :=
      (deleteVertex_adj (G := G)).mpr (by simpa using hyAq.symm)
    have heq := S.Z_A_attachment.2.2 q' hqZ S.yA
      S.Y_A_attachment.1 hdel
    exact False.elim (hneA.2.2 heq)
  have hDX : Disjoint D S.xPart := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwX
    exact hqX (component_mem_of_shared
      S.X_component (by simpa only [K] using hD) hwX hwD hqD)
  have hDY : Disjoint D S.yPart := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwY
    exact hqY (component_mem_of_shared
      S.Y_component (by simpa only [K] using hD) hwY hwD hqD)
  have hDZ : Disjoint D S.zPart := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwZ
    exact hqZ (component_mem_of_shared
      S.Z_component (by simpa only [K] using hD) hwZ hwD hqD)
  have hnoCenter := S.no_center_adj_of_disjoint_terminalParts
    hcenterNeighbors hDX hDY hDZ
  rcases S.ambient_component_boundary_left_or_right hthree hAcard hBcard
      hD hnoCenter with hleft | hright
  · exact Or.inl (S.mem_ambientLeftCarrier_of_component
      hD hnoCenter hleft (val_mem_ahtDeletedFinsetVal.mpr hqD))
  · exfalso
    have hyAnotD : S.yA.1 ∉ ahtDeletedFinsetVal D := by
      intro hyAD
      exact Finset.disjoint_left.mp hD.2.1
        (val_mem_ahtDeletedFinsetVal.mp hyAD)
        (Finset.mem_union_left _ S.Y_A_attachment.1)
    have hyAB := hright q (val_mem_ahtDeletedFinsetVal.mpr hqD)
      S.yA.1 hyAq.symm hyAnotD
    exact Finset.disjoint_left.mp S.A_disjoint_B
      S.Y_A_attachment.1 (val_mem_ahtDeletedFinsetVal.mp hyAB)

/-- The cyclic companion of `yA_neighbor_location_of_both_triples` for
`z_A`.  The component family is unchanged by cyclically relabelling the
three terminal components. -/
theorem zA_neighbor_location_of_both_triples
    (hthree : IsThreeConnected G)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    (hz : S.zPart.card = 1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1) :
    ∀ ⦃q : V⦄, G.Adj S.zA.1 q →
      q ∈ S.ambientLeftCarrier ∨ q = z.1 ∨
        q ∈ ahtDeletedFinsetVal S.aSet ∨ q = S.zB.1 := by
  classical
  have hneA := S.a_attachments_pairwise_ne_of_card_three hAcard
  have hcenterNotA : ∀ a ∈ S.aSet, ¬G.Adj a.1 center := by
    intro a haA hac
    rcases hcenterNeighbors hac.symm with hax | hay | haz
    · have hax' : a = x := Subtype.ext hax
      exact Finset.disjoint_left.mp S.X_component.2.1 S.x_mem_X
        (Finset.mem_union_left _ (hax' ▸ haA))
    · have hay' : a = y := Subtype.ext hay
      exact Finset.disjoint_left.mp S.Y_component.2.1 S.y_mem_Y
        (Finset.mem_union_left _ (hay' ▸ haA))
    · have haz' : a = z := Subtype.ext haz
      exact Finset.disjoint_left.mp S.Z_component.2.1 S.z_mem_Z
        (Finset.mem_union_left _ (haz' ▸ haA))
  intro q hzAq
  by_cases hqA : q ∈ ahtDeletedFinsetVal S.aSet
  · exact Or.inr (Or.inr (Or.inl hqA))
  by_cases hqB : q ∈ ahtDeletedFinsetVal S.bSet
  · obtain ⟨q', hq'B, hq'val⟩ :=
      exists_subtype_of_mem_ahtDeletedFinsetVal hqB
    have hdel : (deleteVertex G center).Adj S.zA q' :=
      (deleteVertex_adj (G := G)).mpr (by simpa [hq'val] using hzAq)
    rcases S.matched_edges_of_both_triples hAcard hBcard
        S.zA S.Z_A_attachment.1 q' hq'B hdel with hX | hY | hZ
    · exact False.elim (hneA.2.1 hX.1.symm)
    · exact False.elim (hneA.2.2 hY.1.symm)
    · right
      right
      right
      exact hq'val.symm.trans (congrArg Subtype.val hZ.2)
  by_cases hqc : q = center
  · subst q
    exact False.elim (hcenterNotA S.zA S.Z_A_attachment.1 hzAq)
  let q' : {v : V // v ≠ center} := ⟨q, hqc⟩
  have hq'A : q' ∉ S.aSet := by
    intro h
    exact hqA (val_mem_ahtDeletedFinsetVal.mpr h)
  have hq'B : q' ∉ S.bSet := by
    intro h
    exact hqB (val_mem_ahtDeletedFinsetVal.mpr h)
  let K : Finset {v : V // v ≠ center} := S.aSet ∪ S.bSet
  have hqK : q' ∉ (K : Set {v : V // v ≠ center}) := by
    simpa only [K, Finset.mem_coe, Finset.mem_union, not_or] using
      And.intro hq'A hq'B
  let C : (deleteVertex G center).ComponentCompl (K : Set _) :=
    (deleteVertex G center).componentComplMk hqK
  let D : Finset {v : V // v ≠ center} := componentCarrier K C
  have hD : IsComponentAfterDeleting (deleteVertex G center) K D :=
    isComponentAfterDeleting_componentCarrier K C
  have hqD : q' ∈ D := by
    change q' ∈ componentCarrier K C
    rw [mem_componentCarrier]
    exact ⟨hqK, rfl⟩
  by_cases hqX : q' ∈ S.xPart
  · have hdel : (deleteVertex G center).Adj q' S.zA :=
      (deleteVertex_adj (G := G)).mpr (by simpa using hzAq.symm)
    have heq := S.X_A_attachment.2.2 q' hqX S.zA
      S.Z_A_attachment.1 hdel
    exact False.elim (hneA.2.1 heq.symm)
  by_cases hqY : q' ∈ S.yPart
  · have hdel : (deleteVertex G center).Adj q' S.zA :=
      (deleteVertex_adj (G := G)).mpr (by simpa using hzAq.symm)
    have heq := S.Y_A_attachment.2.2 q' hqY S.zA
      S.Z_A_attachment.1 hdel
    exact False.elim (hneA.2.2 heq.symm)
  by_cases hqZ : q' ∈ S.zPart
  · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hz
    have hqt : q' = t := by simpa [ht] using hqZ
    have hzt : z = t := by simpa [ht] using S.z_mem_Z
    exact Or.inr (Or.inl (congrArg Subtype.val (hqt.trans hzt.symm)))
  have hDX : Disjoint D S.xPart := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwX
    exact hqX (component_mem_of_shared
      S.X_component (by simpa only [K] using hD) hwX hwD hqD)
  have hDY : Disjoint D S.yPart := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwY
    exact hqY (component_mem_of_shared
      S.Y_component (by simpa only [K] using hD) hwY hwD hqD)
  have hDZ : Disjoint D S.zPart := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwZ
    exact hqZ (component_mem_of_shared
      S.Z_component (by simpa only [K] using hD) hwZ hwD hqD)
  have hnoCenter := S.no_center_adj_of_disjoint_terminalParts
    hcenterNeighbors hDX hDY hDZ
  rcases S.ambient_component_boundary_left_or_right hthree hAcard hBcard
      hD hnoCenter with hleft | hright
  · exact Or.inl (S.mem_ambientLeftCarrier_of_component
      hD hnoCenter hleft (val_mem_ahtDeletedFinsetVal.mpr hqD))
  · exfalso
    have hzAnotD : S.zA.1 ∉ ahtDeletedFinsetVal D := by
      intro hzAD
      exact Finset.disjoint_left.mp hD.2.1
        (val_mem_ahtDeletedFinsetVal.mp hzAD)
        (Finset.mem_union_left _ S.Z_A_attachment.1)
    have hzAB := hright q (val_mem_ahtDeletedFinsetVal.mpr hqD)
      S.zA.1 hzAq.symm hzAnotD
    exact Finset.disjoint_left.mp S.A_disjoint_B
      S.Z_A_attachment.1 (val_mem_ahtDeletedFinsetVal.mp hzAB)

/-- In the both-triples, singleton-`Y`, singleton-`Z` branch the ambient
`A`-side component union is nonempty.  If it were empty, the two attachment
vertices `y_A,z_A` would each have all neighbours among their terminal and
the other two `A` attachments.  Minimum degree three and triangle-freeness
then give the same exhaustive contradiction as the corrected deleted-centre
Case 3 argument. -/
theorem ambientLeftCarrier_nonempty_of_both_triples
    (hthree : IsThreeConnected G) (htri : AHTTriangleFree G)
    (hmin : ∀ q : V, 3 ≤ G.degree q)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1) :
    S.ambientLeftCarrier.Nonempty := by
  classical
  by_contra hnone
  have hempty : S.ambientLeftCarrier = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnone
  have hAeq : ahtDeletedFinsetVal S.aSet =
      {S.xA.1, S.yA.1, S.zA.1} := by
    simp [S.A_eq]
  have hyA := S.adj_y_yA_of_yPart_card_one hy
  have hyB := S.adj_y_yB_of_yPart_card_one hy
  have hzA := S.adj_z_zA_of_zPart_card_one hz
  have hzB := S.adj_z_zB_of_zPart_card_one hz
  have hNyA : G.neighborFinset S.yA.1 ⊆
      {y.1, S.xA.1, S.zA.1} := by
    intro q hq
    have hadj : G.Adj S.yA.1 q := by simpa using hq
    rcases S.yA_neighbor_location_of_both_triples hthree hAcard hBcard
        hy hcenterNeighbors hadj with hqC | rfl | hqA | rfl
    · exact False.elim (by simpa [hempty] using hqC)
    · simp
    · rw [hAeq] at hqA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqA ⊢
      rcases hqA with hqx | hqy | hqz
      · exact Or.inr (Or.inl hqx)
      · subst q
        exact False.elim (G.loopless.irrefl S.yA.1 hadj)
      · exact Or.inr (Or.inr hqz)
    · exact False.elim (htri hyA hadj hyB.symm)
  have hNzA : G.neighborFinset S.zA.1 ⊆
      {z.1, S.xA.1, S.yA.1} := by
    intro q hq
    have hadj : G.Adj S.zA.1 q := by simpa using hq
    rcases S.zA_neighbor_location_of_both_triples hthree hAcard hBcard
        hz hcenterNeighbors hadj with hqC | rfl | hqA | rfl
    · exact False.elim (by simpa [hempty] using hqC)
    · simp
    · rw [hAeq] at hqA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqA ⊢
      rcases hqA with hqx | hqy | hqz
      · exact Or.inr (Or.inl hqx)
      · exact Or.inr (Or.inr hqy)
      · subst q
        exact False.elim (G.loopless.irrefl S.zA.1 hadj)
    · exact False.elim (htri hzA hadj hzB.symm)
  by_cases hyAzAedge : G.Adj S.yA.1 S.zA.1
  · by_cases hyAxAedge : G.Adj S.yA.1 S.xA.1
    · have hzAxAedge : ¬G.Adj S.zA.1 S.xA.1 := by
        intro h
        exact htri hyAzAedge h hyAxAedge.symm
      have hsub : G.neighborFinset S.zA.1 ⊆ {z.1, S.yA.1} := by
        intro q hq
        have hadj : G.Adj S.zA.1 q := by simpa using hq
        have hmem := hNzA hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
        rcases hmem with h | h | h
        · exact Or.inl h
        · exact False.elim (hzAxAedge (by simpa [h] using hadj))
        · exact Or.inr h
      have hle := degree_le_two_of_neighborFinset_subset_pair_local hsub
      have hge := hmin S.zA.1
      omega
    · have hsub : G.neighborFinset S.yA.1 ⊆ {y.1, S.zA.1} := by
        intro q hq
        have hadj : G.Adj S.yA.1 q := by simpa using hq
        have hmem := hNyA hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
        rcases hmem with h | h | h
        · exact Or.inl h
        · exact False.elim (hyAxAedge (by simpa [h] using hadj))
        · exact Or.inr h
      have hle := degree_le_two_of_neighborFinset_subset_pair_local hsub
      have hge := hmin S.yA.1
      omega
  · have hsub : G.neighborFinset S.yA.1 ⊆ {y.1, S.xA.1} := by
      intro q hq
      have hadj : G.Adj S.yA.1 q := by simpa using hq
      have hmem := hNyA hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hyAzAedge (by simpa [h] using hadj))
    have hle := degree_le_two_of_neighborFinset_subset_pair_local hsub
    have hge := hmin S.yA.1
    omega

/-- None of the three terminal components is absorbed into `C_A`: each
contains its displayed neighbour of `center`, whereas every component in
`C_A` is centre-free. -/
theorem terminalParts_disjoint_ambientLeftCarrier
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1) :
    Disjoint (ahtDeletedFinsetVal S.xPart) S.ambientLeftCarrier ∧
      Disjoint (ahtDeletedFinsetVal S.yPart) S.ambientLeftCarrier ∧
      Disjoint (ahtDeletedFinsetVal S.zPart) S.ambientLeftCarrier := by
  classical
  have one_part
      {part : Finset {v : V // v ≠ center}}
      (hpart : IsComponentAfterDeleting (deleteVertex G center)
        (S.aSet ∪ S.bSet) part)
      {t : {v : V // v ≠ center}} (ht : t ∈ part)
      (hct : G.Adj center t.1) :
      Disjoint (ahtDeletedFinsetVal part) S.ambientLeftCarrier := by
    apply Finset.disjoint_left.mpr
    intro q hqPart hqCarrier
    obtain ⟨C, hCfamily, hqC⟩ := Finset.mem_biUnion.mp hqCarrier
    obtain ⟨D, hD, hnoCenter, rfl, -⟩ :=
      (S.mem_ambientLeftComponents_iff C).mp hCfamily
    obtain ⟨qPart, hqPart', hqPartVal⟩ :=
      exists_subtype_of_mem_ahtDeletedFinsetVal hqPart
    obtain ⟨qD, hqD, hqDVal⟩ :=
      exists_subtype_of_mem_ahtDeletedFinsetVal hqC
    have hsame : qPart = qD := Subtype.ext (hqPartVal.trans hqDVal.symm)
    have htD : t ∈ D :=
      component_mem_of_shared hD hpart (hsame ▸ hqD) hqPart' ht
    exact hnoCenter t.1
      (val_mem_ahtDeletedFinsetVal.mpr htD) hct.symm
  exact ⟨one_part S.X_component S.x_mem_X hcx,
    one_part S.Y_component S.y_mem_Y hcy,
    one_part S.Z_component S.z_mem_Z hcz⟩

/-- A terminal twin pair, the three vertices of the opposite splitter side,
and `center` give six distinct vertices outside `C_A ∪ A`.  This is the
source cardinality input needed by Claim (1) in the both-triples branch. -/
theorem six_le_complement_leftCarrier_of_xTwinPair
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1) (hBcard : S.bSet.card = 3)
    {p q : V} (hp : p ∈ ahtDeletedFinsetVal S.xPart)
    (hq : q ∈ ahtDeletedFinsetVal S.xPart)
    (hpq : AHTTwinPair G p q) :
    6 ≤ (Finset.univ \
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet)).card := by
  classical
  let P : Finset V := {p, q}
  let B : Finset V := ahtDeletedFinsetVal S.bSet
  let T : Finset V := (P ∪ B) ∪ {center}
  have hterminal := S.terminalParts_disjoint_ambientLeftCarrier hcx hcy hcz
  have hXsep := disjoint_ahtDeletedFinsetVal S.X_component.2.1
  rw [ahtDeletedFinsetVal_union] at hXsep
  have hpCarrier : p ∉ S.ambientLeftCarrier := fun h ↦
    Finset.disjoint_left.mp hterminal.1 hp h
  have hqCarrier : q ∉ S.ambientLeftCarrier := fun h ↦
    Finset.disjoint_left.mp hterminal.1 hq h
  have hpA : p ∉ ahtDeletedFinsetVal S.aSet := fun h ↦
    Finset.disjoint_left.mp hXsep hp (Finset.mem_union_left _ h)
  have hqA : q ∉ ahtDeletedFinsetVal S.aSet := fun h ↦
    Finset.disjoint_left.mp hXsep hq (Finset.mem_union_left _ h)
  have hPB : Disjoint P B := by
    apply Finset.disjoint_left.mpr
    intro r hrP hrB
    have hrX : r ∈ ahtDeletedFinsetVal S.xPart := by
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hrP
      rcases hrP with rfl | rfl
      · exact hp
      · exact hq
    exact Finset.disjoint_left.mp hXsep hrX
      (Finset.mem_union_right _ hrB)
  have hTC : Disjoint (P ∪ B) ({center} : Finset V) := by
    apply Finset.disjoint_right.mpr
    intro r hrCenter hr
    have hrc : r = center := by simpa using hrCenter
    subst r
    rcases Finset.mem_union.mp hr with hrP | hrB
    · simp only [P, Finset.mem_insert, Finset.mem_singleton] at hrP
      rcases hrP with h | h
      · exact center_not_mem_ahtDeletedFinsetVal S.xPart (h ▸ hp)
      · exact center_not_mem_ahtDeletedFinsetVal S.xPart (h ▸ hq)
    · exact center_not_mem_ahtDeletedFinsetVal S.bSet hrB
  have hPcard : P.card = 2 := by
    simp [P, hpq.falseTwins.1]
  have hBcard' : B.card = 3 := by
    simpa [B] using hBcard
  have hTcard : T.card = 6 := by
    change ((P ∪ B) ∪ {center}).card = 6
    rw [Finset.card_union_of_disjoint hTC,
      Finset.card_union_of_disjoint hPB]
    simp [hPcard, hBcard']
  have hPCarrier : Disjoint P S.ambientLeftCarrier := by
    apply Finset.disjoint_left.mpr
    intro r hrP hrCarrier
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hrP
    rcases hrP with rfl | rfl
    · exact hpCarrier hrCarrier
    · exact hqCarrier hrCarrier
  have hBCarrier : Disjoint B S.ambientLeftCarrier := by
    simpa [B] using S.ambientLeftCarrier_disjoint_right.symm
  have hCenterCarrier :
      Disjoint ({center} : Finset V) S.ambientLeftCarrier := by
    apply Finset.disjoint_left.mpr
    intro r hrCenter hrCarrier
    have hrc : r = center := by simpa using hrCenter
    subst r
    exact S.center_not_mem_ambientLeftCarrier hrCarrier
  have hPA : Disjoint P (ahtDeletedFinsetVal S.aSet) := by
    apply Finset.disjoint_left.mpr
    intro r hrP hrA
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hrP
    rcases hrP with rfl | rfl
    · exact hpA hrA
    · exact hqA hrA
  have hBA : Disjoint B (ahtDeletedFinsetVal S.aSet) := by
    simpa [B] using (disjoint_ahtDeletedFinsetVal S.A_disjoint_B).symm
  have hCenterA :
      Disjoint ({center} : Finset V) (ahtDeletedFinsetVal S.aSet) := by
    apply Finset.disjoint_left.mpr
    intro r hrCenter hrA
    have hrc : r = center := by simpa using hrCenter
    subst r
    exact center_not_mem_ahtDeletedFinsetVal S.aSet hrA
  have hTbad : Disjoint T
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet) := by
    change Disjoint ((P ∪ B) ∪ {center})
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet)
    apply Finset.disjoint_union_left.mpr
    constructor
    · apply Finset.disjoint_union_left.mpr
      exact ⟨Finset.disjoint_union_right.mpr ⟨hPCarrier, hPA⟩,
        Finset.disjoint_union_right.mpr ⟨hBCarrier, hBA⟩⟩
    · exact Finset.disjoint_union_right.mpr ⟨hCenterCarrier, hCenterA⟩
  have hTsub : T ⊆ Finset.univ \
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet) := by
    intro r hrT
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ r,
      fun hrBad ↦ Finset.disjoint_left.mp hTbad hrT hrBad⟩
  rw [← hTcard]
  exact Finset.card_le_card hTsub

/-- In the mixed `|A|=3, |B|=1` branch, the terminal twin pair, the other
two displayed terminals, `x_B`, and the deleted centre are six distinct
vertices outside `C_A ∪ A`.  This is the source's Claim-(5) cardinality
input before the fan argument begins. -/
theorem six_le_complement_leftCarrier_of_xTwinPair_mixed
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1) {p q : V}
    (hp : p ∈ ahtDeletedFinsetVal S.xPart)
    (hq : q ∈ ahtDeletedFinsetVal S.xPart)
    (hpq : AHTTwinPair G p q) :
    6 ≤ (Finset.univ \
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet)).card := by
  classical
  let T : Finset V := {p, q, y.1, z.1, S.xB.1, center}
  have hterminal := S.terminalParts_disjoint_ambientLeftCarrier hcx hcy hcz
  have hXsep := disjoint_ahtDeletedFinsetVal S.X_component.2.1
  have hYsep := disjoint_ahtDeletedFinsetVal S.Y_component.2.1
  have hZsep := disjoint_ahtDeletedFinsetVal S.Z_component.2.1
  have hXY := disjoint_ahtDeletedFinsetVal S.X_disjoint_Y
  have hXZ := disjoint_ahtDeletedFinsetVal S.X_disjoint_Z
  have hYZ := disjoint_ahtDeletedFinsetVal S.Y_disjoint_Z
  rw [ahtDeletedFinsetVal_union] at hXsep hYsep hZsep
  have hpY : p ≠ y.1 := by
    intro h
    exact Finset.disjoint_left.mp hXY hp
      (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
  have hpZ : p ≠ z.1 := by
    intro h
    exact Finset.disjoint_left.mp hXZ hp
      (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
  have hqY : q ≠ y.1 := by
    intro h
    exact Finset.disjoint_left.mp hXY hq
      (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
  have hqZ : q ≠ z.1 := by
    intro h
    exact Finset.disjoint_left.mp hXZ hq
      (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
  have hyz : y.1 ≠ z.1 := by
    intro h
    exact Finset.disjoint_left.mp hYZ
      (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
      (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
  have hpB : p ≠ S.xB.1 := by
    intro h
    exact Finset.disjoint_left.mp hXsep hp
      (Finset.mem_union_right _
        (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1))
  have hqB : q ≠ S.xB.1 := by
    intro h
    exact Finset.disjoint_left.mp hXsep hq
      (Finset.mem_union_right _
        (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1))
  have hyB : y.1 ≠ S.xB.1 := by
    intro h
    exact Finset.disjoint_left.mp hYsep
      (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
      (Finset.mem_union_right _
        (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1))
  have hzB : z.1 ≠ S.xB.1 := by
    intro h
    exact Finset.disjoint_left.mp hZsep
      (val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
      (Finset.mem_union_right _
        (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1))
  have hpC : p ≠ center := fun h ↦
    center_not_mem_ahtDeletedFinsetVal S.xPart (h ▸ hp)
  have hqC : q ≠ center := fun h ↦
    center_not_mem_ahtDeletedFinsetVal S.xPart (h ▸ hq)
  have hyC : y.1 ≠ center := y.2
  have hzC : z.1 ≠ center := z.2
  have hBC : S.xB.1 ≠ center := S.xB.2
  have hTcard : T.card = 6 := by
    simp [T, hpq.falseTwins.1, hpY, hpZ, hpB, hpC, hqY, hqZ,
      hqB, hqC, hyz, hyB, hyC, hzB, hzC, hBC]
  have hTsub : T ⊆ Finset.univ \
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet) := by
    intro r hrT
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, ?_⟩
    intro hrBad
    rcases Finset.mem_union.mp hrBad with hrCarrier | hrA
    · simp only [T, Finset.mem_insert, Finset.mem_singleton] at hrT
      rcases hrT with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Finset.disjoint_left.mp hterminal.1 hp hrCarrier
      · exact Finset.disjoint_left.mp hterminal.1 hq hrCarrier
      · exact Finset.disjoint_left.mp hterminal.2.1
          (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y) hrCarrier
      · exact Finset.disjoint_left.mp hterminal.2.2
          (val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z) hrCarrier
      · exact Finset.disjoint_left.mp S.ambientLeftCarrier_disjoint_right
          hrCarrier (val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1)
      · exact S.center_not_mem_ambientLeftCarrier hrCarrier
    · simp only [T, Finset.mem_insert, Finset.mem_singleton] at hrT
      rcases hrT with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Finset.disjoint_left.mp hXsep hp
          (Finset.mem_union_left _ hrA)
      · exact Finset.disjoint_left.mp hXsep hq
          (Finset.mem_union_left _ hrA)
      · exact Finset.disjoint_left.mp hYsep
          (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
          (Finset.mem_union_left _ hrA)
      · exact Finset.disjoint_left.mp hZsep
          (val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
          (Finset.mem_union_left _ hrA)
      · exact Finset.disjoint_left.mp
          (disjoint_ahtDeletedFinsetVal S.A_disjoint_B) hrA
          (val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1)
      · exact center_not_mem_ahtDeletedFinsetVal S.aSet hrA
  rw [← hTcard]
  exact Finset.card_le_card hTsub

/-- Package the actual `A`-side union and the two singleton-terminal
attachments as the local three-boundary datum consumed by Claim (1). -/
noncomputable def relevantLeftSideLocal_of_both_triples
    (hthree : IsThreeConnected G) (htri : AHTTriangleFree G)
    (hmin : ∀ q : V, 3 ≤ G.degree q)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 3)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1) :
    AHTRelevantTripleSideLocal G where
  carrier := S.ambientLeftCarrier
  boundary := ahtDeletedFinsetVal S.aSet
  anchor := S.yA.1
  terminal := y.1
  matched := S.yB.1
  carrier_nonempty := S.ambientLeftCarrier_nonempty_of_both_triples
    hthree htri hmin hAcard hBcard hy hz hcenterNeighbors
  carrier_disjoint_boundary := S.ambientLeftCarrier_disjoint
  boundary_card := by simpa using hAcard
  external_boundary := S.ambientLeftCarrier_externalBoundary
  anchor_mem := val_mem_ahtDeletedFinsetVal.mpr S.Y_A_attachment.1
  anchor_adj_terminal := (S.adj_y_yA_of_yPart_card_one hy).symm
  terminal_adj_matched := S.adj_y_yB_of_yPart_card_one hy
  anchor_neighbor_location :=
    S.yA_neighbor_location_of_both_triples
      hthree hAcard hBcard hy hcenterNeighbors

/-- Any vertex of the `X` terminal component lies outside the relevant
`A`-side carrier together with its three-vertex boundary. -/
theorem xPart_mem_complement_leftCarrier
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1) {p : V}
    (hp : p ∈ ahtDeletedFinsetVal S.xPart) :
    p ∈ Finset.univ \
      (S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet) := by
  have hterminal := S.terminalParts_disjoint_ambientLeftCarrier hcx hcy hcz
  have hXsep := disjoint_ahtDeletedFinsetVal S.X_component.2.1
  rw [ahtDeletedFinsetVal_union] at hXsep
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, ?_⟩
  intro hpbad
  rcases Finset.mem_union.mp hpbad with hpCarrier | hpA
  · exact Finset.disjoint_left.mp hterminal.1 hp hpCarrier
  · exact Finset.disjoint_left.mp hXsep hp
      (Finset.mem_union_left _ hpA)

/-- The retained interior in the final all-singleton replacement is the
`A`-side component union together with the three `A` attachments. -/
noncomputable def finalLeftVerts : Finset V :=
  S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet

theorem finalLeftVerts_nonempty : S.finalLeftVerts.Nonempty := by
  obtain ⟨a, ha⟩ := S.A_nonempty
  exact ⟨a.1, Finset.mem_union_right _
    (val_mem_ahtDeletedFinsetVal.mpr ha)⟩

/-- The three singleton terminals are disjoint from the retained `A` side.
-/
theorem finalLeftVerts_disjoint_terminals
    (hcx : G.Adj center x.1) (hcy : G.Adj center y.1)
    (hcz : G.Adj center z.1) :
    Disjoint S.finalLeftVerts ({x.1, y.1, z.1} : Finset V) := by
  have hterminal := S.terminalParts_disjoint_ambientLeftCarrier hcx hcy hcz
  have hXsep := disjoint_ahtDeletedFinsetVal S.X_component.2.1
  have hYsep := disjoint_ahtDeletedFinsetVal S.Y_component.2.1
  have hZsep := disjoint_ahtDeletedFinsetVal S.Z_component.2.1
  rw [ahtDeletedFinsetVal_union] at hXsep hYsep hZsep
  apply Finset.disjoint_left.mpr
  intro q hqVerts hqTerminal
  change q ∈ S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet at hqVerts
  rcases Finset.mem_union.mp hqVerts with hqCarrier | hqA
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hqTerminal
    rcases hqTerminal with rfl | rfl | rfl
    · exact Finset.disjoint_left.mp hterminal.1
        (val_mem_ahtDeletedFinsetVal.mpr S.x_mem_X) hqCarrier
    · exact Finset.disjoint_left.mp hterminal.2.1
        (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y) hqCarrier
    · exact Finset.disjoint_left.mp hterminal.2.2
        (val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z) hqCarrier
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hqTerminal
    rcases hqTerminal with rfl | rfl | rfl
    · exact Finset.disjoint_left.mp hXsep
        (val_mem_ahtDeletedFinsetVal.mpr S.x_mem_X)
        (Finset.mem_union_left _ hqA)
    · exact Finset.disjoint_left.mp hYsep
        (val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)
        (Finset.mem_union_left _ hqA)
    · exact Finset.disjoint_left.mp hZsep
        (val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)
        (Finset.mem_union_left _ hqA)

/-- The deleted centre witnesses that the final retained fragment has a
nonempty opposite side. -/
theorem center_mem_complement_finalLeftVerts_terminals :
    center ∈ Finset.univ \
      (S.finalLeftVerts ∪ ({x.1, y.1, z.1} : Finset V)) := by
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ center, ?_⟩
  intro hbad
  rcases Finset.mem_union.mp hbad with hverts | hterminal
  · change center ∈
      S.ambientLeftCarrier ∪ ahtDeletedFinsetVal S.aSet at hverts
    rcases Finset.mem_union.mp hverts with hcarrier | hA
    · exact S.center_not_mem_ambientLeftCarrier hcarrier
    · exact center_not_mem_ahtDeletedFinsetVal S.aSet hA
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hterminal
    rcases hterminal with h | h | h
    · exact x.2 h.symm
    · exact y.2 h.symm
    · exact z.2 h.symm

/-- Each displayed terminal has an edge into the final retained side. -/
theorem terminals_meet_finalLeftVerts
    (hx : S.xPart.card = 1) (hy : S.yPart.card = 1)
    (hz : S.zPart.card = 1) :
    (∃ a ∈ S.finalLeftVerts, G.Adj x.1 a) ∧
      (∃ a ∈ S.finalLeftVerts, G.Adj y.1 a) ∧
      (∃ a ∈ S.finalLeftVerts, G.Adj z.1 a) := by
  exact ⟨⟨S.xA.1, Finset.mem_union_right _
      (val_mem_ahtDeletedFinsetVal.mpr S.X_A_attachment.1),
      S.adj_x_xA_of_xPart_card_one hx⟩,
    ⟨S.yA.1, Finset.mem_union_right _
      (val_mem_ahtDeletedFinsetVal.mpr S.Y_A_attachment.1),
      S.adj_y_yA_of_yPart_card_one hy⟩,
    ⟨S.zA.1, Finset.mem_union_right _
      (val_mem_ahtDeletedFinsetVal.mpr S.Z_A_attachment.1),
      S.adj_z_zA_of_zPart_card_one hz⟩⟩

/-! ## The extra residual component in the mixed `3/1` branch -/

/-- Minimum degree three supplies a neighbour outside any prescribed pair.
This tiny finite form is the degree input in both residual-seed subcases of
source Claim (8). -/
theorem exists_adj_ne_pair {w a b : V} (hdeg : 3 ≤ G.degree w) :
    ∃ q : V, G.Adj w q ∧ q ≠ a ∧ q ≠ b := by
  classical
  by_contra hnone
  have hsub : G.neighborFinset w ⊆ {a, b} := by
    intro q hq
    have hadj : G.Adj w q := by simpa using hq
    by_contra hqpair
    have hqa : q ≠ a := by
      intro h
      exact hqpair (by simp [h])
    have hqb : q ≠ b := by
      intro h
      exact hqpair (by simp [h])
    exact hnone ⟨q, hadj, hqa, hqb⟩
  have hN : 3 ≤ (G.neighborFinset w).card := by
    simpa only [G.card_neighborFinset_eq_degree] using hdeg
  have hpair : ({a, b} : Finset V).card ≤ 2 :=
    Finset.card_insert_le _ _
  exact (by
    have := Finset.card_le_card hsub
    omega)

/-- The concrete residual component `D'` selected in the mixed branch of
source Claim (8).  It is a component after deleting `A`, `B`, and `center`,
is distinct from the three terminal components, and has a displayed vertex
adjacent to the singleton `B` attachment.  The existence theorem is the
degree/triangle-free argument immediately preceding the two fans. -/
structure MixedResidualComponent where
  carrier : Finset V
  component : IsComponentAfterDeleting G
    (ahtDeletedFinsetVal S.aSet ∪
      ahtDeletedFinsetVal S.bSet ∪ {center}) carrier
  disjoint_xPart : Disjoint carrier (ahtDeletedFinsetVal S.xPart)
  disjoint_yPart : Disjoint carrier (ahtDeletedFinsetVal S.yPart)
  disjoint_zPart : Disjoint carrier (ahtDeletedFinsetVal S.zPart)
  xBPrime : V
  xBPrime_mem : xBPrime ∈ carrier
  adj_xBPrime_xB : G.Adj xBPrime S.xB.1

namespace MixedResidualComponent

variable (R : S.MixedResidualComponent)

theorem xBPrime_ne_xB : R.xBPrime ≠ S.xB.1 := by
  intro h
  exact Finset.disjoint_left.mp R.component.2.1 R.xBPrime_mem
    (Finset.mem_union_left _ (Finset.mem_union_right _
      (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_B_attachment.1)))

theorem xBPrime_ne_center : R.xBPrime ≠ center := by
  intro h
  exact Finset.disjoint_left.mp R.component.2.1 R.xBPrime_mem
    (Finset.mem_union_right _ (by simp [h]))

theorem xBPrime_ne_xA : R.xBPrime ≠ S.xA.1 := by
  intro h
  exact Finset.disjoint_left.mp R.component.2.1 R.xBPrime_mem
    (Finset.mem_union_left _ (Finset.mem_union_left _
      (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.X_A_attachment.1)))

theorem xBPrime_ne_yA : R.xBPrime ≠ S.yA.1 := by
  intro h
  exact Finset.disjoint_left.mp R.component.2.1 R.xBPrime_mem
    (Finset.mem_union_left _ (Finset.mem_union_left _
      (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.Y_A_attachment.1)))

theorem xBPrime_ne_zA : R.xBPrime ≠ S.zA.1 := by
  intro h
  exact Finset.disjoint_left.mp R.component.2.1 R.xBPrime_mem
    (Finset.mem_union_left _ (Finset.mem_union_left _
      (h ▸ val_mem_ahtDeletedFinsetVal.mpr S.Z_A_attachment.1)))

theorem xBPrime_ne_x : R.xBPrime ≠ x.1 := by
  intro heq
  exact Finset.disjoint_left.mp R.disjoint_xPart R.xBPrime_mem
    (heq ▸ val_mem_ahtDeletedFinsetVal.mpr S.x_mem_X)

theorem xBPrime_ne_y : R.xBPrime ≠ y.1 := by
  intro heq
  exact Finset.disjoint_left.mp R.disjoint_yPart R.xBPrime_mem
    (heq ▸ val_mem_ahtDeletedFinsetVal.mpr S.y_mem_Y)

theorem xBPrime_ne_z : R.xBPrime ≠ z.1 := by
  intro heq
  exact Finset.disjoint_left.mp R.disjoint_zPart R.xBPrime_mem
    (heq ▸ val_mem_ahtDeletedFinsetVal.mpr S.z_mem_Z)

theorem xBPrime_ne_xPart {q : V}
    (hq : q ∈ ahtDeletedFinsetVal S.xPart) : R.xBPrime ≠ q := by
  intro h
  exact Finset.disjoint_left.mp R.disjoint_xPart R.xBPrime_mem (h ▸ hq)

end MixedResidualComponent

/-- A single neighbour of `x_B` outside the splitter deletion set and the
three terminal components determines the literal residual component `D'`.
This separates the paper's finite degree/triangle-free selection of that
neighbour from all subsequent component bookkeeping. -/
noncomputable def mixedResidualComponentOfNeighbor
    {q : V}
    (hqSep : q ∉ ahtDeletedFinsetVal S.aSet ∪
      ahtDeletedFinsetVal S.bSet ∪ {center})
    (hqX : q ∉ ahtDeletedFinsetVal S.xPart)
    (hqY : q ∉ ahtDeletedFinsetVal S.yPart)
    (hqZ : q ∉ ahtDeletedFinsetVal S.zPart)
    (hqxB : G.Adj q S.xB.1) : S.MixedResidualComponent := by
  let K : Finset V := ahtDeletedFinsetVal S.aSet ∪
    ahtDeletedFinsetVal S.bSet ∪ {center}
  let C : G.ComponentCompl (K : Set V) := G.componentComplMk (by
    simpa only [K, Finset.mem_coe] using hqSep)
  let D : Finset V := componentCarrier K C
  have hD : IsComponentAfterDeleting G K D :=
    isComponentAfterDeleting_componentCarrier K C
  have hqD : q ∈ D := by
    change q ∈ componentCarrier K C
    rw [mem_componentCarrier]
    exact ⟨by simpa only [K, Finset.mem_coe] using hqSep, rfl⟩
  have hX : IsComponentAfterDeleting G K
      (ahtDeletedFinsetVal S.xPart) := by
    simpa only [K, ahtDeletedFinsetVal_union] using
      S.X_component.ambient_of_deleteVertex (G := G)
  have hY : IsComponentAfterDeleting G K
      (ahtDeletedFinsetVal S.yPart) := by
    simpa only [K, ahtDeletedFinsetVal_union] using
      S.Y_component.ambient_of_deleteVertex (G := G)
  have hZ : IsComponentAfterDeleting G K
      (ahtDeletedFinsetVal S.zPart) := by
    simpa only [K, ahtDeletedFinsetVal_union] using
      S.Z_component.ambient_of_deleteVertex (G := G)
  have hDX : Disjoint D (ahtDeletedFinsetVal S.xPart) := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwX
    exact hqX (component_mem_of_shared
      hX hD hwX hwD hqD)
  have hDY : Disjoint D (ahtDeletedFinsetVal S.yPart) := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwY
    exact hqY (component_mem_of_shared
      hY hD hwY hwD hqD)
  have hDZ : Disjoint D (ahtDeletedFinsetVal S.zPart) := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwZ
    exact hqZ (component_mem_of_shared
      hZ hD hwZ hwD hqD)
  exact {
    carrier := D
    component := by simpa only [K] using hD
    disjoint_xPart := hDX
    disjoint_yPart := hDY
    disjoint_zPart := hDZ
    xBPrime := q
    xBPrime_mem := hqD
    adj_xBPrime_xB := hqxB }

/-- The same residual certificate when the source component is still kept
in the centre-deleted subtype.  This is the form used while deciding
whether the component belongs to `C_A`. -/
noncomputable def mixedResidualComponentOfDeletedComponent
    {D : Finset {v : V // v ≠ center}}
    (hD : IsComponentAfterDeleting (deleteVertex G center)
      (S.aSet ∪ S.bSet) D)
    (hDX : Disjoint D S.xPart) (hDY : Disjoint D S.yPart)
    (hDZ : Disjoint D S.zPart)
    (xBPrime : {v : V // v ≠ center}) (hxBPrime : xBPrime ∈ D)
    (hadj : (deleteVertex G center).Adj xBPrime S.xB) :
    S.MixedResidualComponent where
  carrier := ahtDeletedFinsetVal D
  component := by simpa using hD.ambient_of_deleteVertex (G := G)
  disjoint_xPart := disjoint_ahtDeletedFinsetVal hDX
  disjoint_yPart := disjoint_ahtDeletedFinsetVal hDY
  disjoint_zPart := disjoint_ahtDeletedFinsetVal hDZ
  xBPrime := xBPrime.1
  xBPrime_mem := val_mem_ahtDeletedFinsetVal.mpr hxBPrime
  adj_xBPrime_xB := (deleteVertex_adj (G := G)).mp hadj

/-- A residual deleted component which is not assigned to `C_A` must meet
the singleton side `B`.  The only other ambient deletion vertex is
`center`, and adjacency to it is excluded by the three terminal-component
disjointness hypotheses. -/
theorem exists_xBPrime_of_not_leftBoundary
    {D : Finset {v : V // v ≠ center}}
    (hD : IsComponentAfterDeleting (deleteVertex G center)
      (S.aSet ∪ S.bSet) D)
    (hDX : Disjoint D S.xPart) (hDY : Disjoint D S.yPart)
    (hDZ : Disjoint D S.zPart)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hBcard : S.bSet.card = 1)
    (hnotLeft : ¬HasExternalBoundaryIn G (ahtDeletedFinsetVal D)
      (ahtDeletedFinsetVal S.aSet)) :
    ∃ xBPrime ∈ D, (deleteVertex G center).Adj xBPrime S.xB := by
  have hDambient := hD.ambient_of_deleteVertex (G := G)
  have hnoCenter := S.no_center_adj_of_disjoint_terminalParts
    hcenterNeighbors hDX hDY hDZ
  rw [HasExternalBoundaryIn] at hnotLeft
  push Not at hnotLeft
  obtain ⟨u, huD, v, huv, hvD, hvA⟩ := hnotLeft
  have hvDelete : v ∈
      ahtDeletedFinsetVal (S.aSet ∪ S.bSet) ∪ {center} := by
    by_contra hv
    exact hvD (hDambient.2.2.2 u huD v hv huv)
  rcases Finset.mem_union.mp hvDelete with hvAB | hvCenter
  · rw [ahtDeletedFinsetVal_union] at hvAB
    rcases Finset.mem_union.mp hvAB with hvA' | hvB
    · exact False.elim (hvA hvA')
    · obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hBcard
      have hxBb : S.xB = b := by simpa [hb] using S.X_B_attachment.1
      have hvEq : v = S.xB.1 := by
        have hvb : v = b.1 := by
          simpa [hb] using hvB
        exact hvb.trans (congrArg Subtype.val hxBb).symm
      obtain ⟨u', hu'D, hu'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal huD
      refine ⟨u', hu'D, (deleteVertex_adj (G := G)).mpr ?_⟩
      simpa [hu'val, hvEq] using huv
  · have hvEq : v = center := by simpa using hvCenter
    exact False.elim (hnoCenter u huD (by simpa [hvEq] using huv))

/-- Once a residual component contains a vertex outside `C_A`, the previous
boundary lemma supplies `x'_B` and hence the full mixed residual
certificate. -/
theorem exists_mixedResidualComponent_of_not_mem_leftCarrier
    {D : Finset {v : V // v ≠ center}}
    (hD : IsComponentAfterDeleting (deleteVertex G center)
      (S.aSet ∪ S.bSet) D)
    (hDX : Disjoint D S.xPart) (hDY : Disjoint D S.yPart)
    (hDZ : Disjoint D S.zPart)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hBcard : S.bSet.card = 1) {q : {v : V // v ≠ center}}
    (hqD : q ∈ D) (hqNotLeft : q.1 ∉ S.ambientLeftCarrier) :
    Nonempty S.MixedResidualComponent := by
  have hnoCenter := S.no_center_adj_of_disjoint_terminalParts
    hcenterNeighbors hDX hDY hDZ
  have hnotBoundary : ¬HasExternalBoundaryIn G (ahtDeletedFinsetVal D)
      (ahtDeletedFinsetVal S.aSet) := by
    intro hleft
    exact hqNotLeft (S.mem_ambientLeftCarrier_of_component
      hD hnoCenter hleft (val_mem_ahtDeletedFinsetVal.mpr hqD))
  obtain ⟨xBPrime, hxBPrime, hadj⟩ :=
    S.exists_xBPrime_of_not_leftBoundary hD hDX hDY hDZ
      hcenterNeighbors hBcard hnotBoundary
  exact ⟨S.mixedResidualComponentOfDeletedComponent
    hD hDX hDY hDZ xBPrime hxBPrime hadj⟩

/-- Any centre-deleted vertex outside `A ∪ B`, the three terminal
components, and `C_A` canonically generates the required residual
component.  The sole remaining existence argument is therefore the
paper's local minimum-degree/triangle-free production of this seed. -/
theorem exists_mixedResidualComponent_of_seed
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hBcard : S.bSet.card = 1) {q : {v : V // v ≠ center}}
    (hqSep : q ∉ S.aSet ∪ S.bSet)
    (hqX : q ∉ S.xPart) (hqY : q ∉ S.yPart) (hqZ : q ∉ S.zPart)
    (hqNotLeft : q.1 ∉ S.ambientLeftCarrier) :
    Nonempty S.MixedResidualComponent := by
  letI : DecidableRel (deleteVertex G center).Adj := fun p r ↦
    inferInstanceAs (Decidable (G.Adj p.1 r.1))
  let K : Finset {v : V // v ≠ center} := S.aSet ∪ S.bSet
  let C : (deleteVertex G center).ComponentCompl (K : Set _) :=
    (deleteVertex G center).componentComplMk (by
      simpa only [K, Finset.mem_coe] using hqSep)
  let D : Finset {v : V // v ≠ center} := componentCarrier K C
  have hD : IsComponentAfterDeleting (deleteVertex G center) K D :=
    isComponentAfterDeleting_componentCarrier K C
  have hqD : q ∈ D := by
    change q ∈ componentCarrier K C
    rw [mem_componentCarrier]
    exact ⟨by simpa only [K, Finset.mem_coe] using hqSep, rfl⟩
  have hDX : Disjoint D S.xPart := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwX
    exact hqX (component_mem_of_shared
      S.X_component (by simpa only [K] using hD) hwX hwD hqD)
  have hDY : Disjoint D S.yPart := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwY
    exact hqY (component_mem_of_shared
      S.Y_component (by simpa only [K] using hD) hwY hwD hqD)
  have hDZ : Disjoint D S.zPart := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwZ
    exact hqZ (component_mem_of_shared
      S.Z_component (by simpa only [K] using hD) hwZ hwD hqD)
  exact S.exists_mixedResidualComponent_of_not_mem_leftCarrier
    (by simpa only [K] using hD) hDX hDY hDZ hcenterNeighbors hBcard
      hqD hqNotLeft

/-- A neighbour of `y_A` which lies neither on side `A`, at the singleton
terminal `y`, nor in `C_A` is already a residual seed.  Component
maximality and unique attachments exclude the other terminal components;
triangle-freeness excludes the singleton `B` side. -/
theorem exists_mixedResidualComponent_of_yA_neighbor
    (htri : AHTTriangleFree G)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 1)
    (hy : S.yPart.card = 1) {q : V}
    (hyAq : G.Adj S.yA.1 q)
    (hqA : q ∉ ahtDeletedFinsetVal S.aSet)
    (hqy : q ≠ y.1) (hqLeft : q ∉ S.ambientLeftCarrier) :
    Nonempty S.MixedResidualComponent := by
  classical
  have hAne := S.a_attachments_pairwise_ne_of_card_three hAcard
  have hyATerm := S.aSet_val_ne_terminals S.Y_A_attachment.1
  have hqCenter : q ≠ center := by
    intro hqc
    have hcyA : G.Adj center S.yA.1 := by
      simpa [hqc] using hyAq.symm
    rcases hcenterNeighbors hcyA with h | h | h
    · exact hyATerm.1 h
    · exact hyATerm.2.1 h
    · exact hyATerm.2.2 h
  let q' : {v : V // v ≠ center} := ⟨q, hqCenter⟩
  have hqA' : q' ∉ S.aSet := by
    intro h
    exact hqA (val_mem_ahtDeletedFinsetVal.mpr h)
  have hqB' : q' ∉ S.bSet := by
    intro hqB
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hBcard
    have hqb : q' = b := by simpa [hb] using hqB
    have hyBb : S.yB = b := by simpa [hb] using S.Y_B_attachment.1
    have hqEq : q = S.yB.1 :=
      congrArg Subtype.val (hqb.trans hyBb.symm)
    have hyAqB : G.Adj S.yA.1 S.yB.1 := by simpa [hqEq] using hyAq
    exact htri (S.adj_y_yA_of_yPart_card_one hy)
      hyAqB (S.adj_y_yB_of_yPart_card_one hy).symm
  have hqX : q' ∉ S.xPart := by
    intro hqX
    have hdel : (deleteVertex G center).Adj q' S.yA :=
      (deleteVertex_adj (G := G)).mpr (by simpa [q'] using hyAq.symm)
    have heq := S.X_A_attachment.2.2 q' hqX
      S.yA S.Y_A_attachment.1 hdel
    exact hAne.1 heq.symm
  have hqY : q' ∉ S.yPart := by
    intro hqY
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hy
    have hqt : q' = t := by simpa [ht] using hqY
    have hyt : y = t := by simpa [ht] using S.y_mem_Y
    exact hqy (congrArg Subtype.val (hqt.trans hyt.symm))
  have hqZ : q' ∉ S.zPart := by
    intro hqZ
    have hdel : (deleteVertex G center).Adj q' S.yA :=
      (deleteVertex_adj (G := G)).mpr (by simpa [q'] using hyAq.symm)
    have heq := S.Z_A_attachment.2.2 q' hqZ
      S.yA S.Y_A_attachment.1 hdel
    exact hAne.2.2 heq
  exact S.exists_mixedResidualComponent_of_seed hcenterNeighbors hBcard
    (by simp [hqA', hqB']) hqX hqY hqZ (by simpa [q'] using hqLeft)

/-- The `z_A` companion of
`exists_mixedResidualComponent_of_yA_neighbor`. -/
theorem exists_mixedResidualComponent_of_zA_neighbor
    (htri : AHTTriangleFree G)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 1)
    (hz : S.zPart.card = 1) {q : V}
    (hzAq : G.Adj S.zA.1 q)
    (hqA : q ∉ ahtDeletedFinsetVal S.aSet)
    (hqz : q ≠ z.1) (hqLeft : q ∉ S.ambientLeftCarrier) :
    Nonempty S.MixedResidualComponent := by
  classical
  have hAne := S.a_attachments_pairwise_ne_of_card_three hAcard
  have hzATerm := S.aSet_val_ne_terminals S.Z_A_attachment.1
  have hqCenter : q ≠ center := by
    intro hqc
    have hczA : G.Adj center S.zA.1 := by
      simpa [hqc] using hzAq.symm
    rcases hcenterNeighbors hczA with h | h | h
    · exact hzATerm.1 h
    · exact hzATerm.2.1 h
    · exact hzATerm.2.2 h
  let q' : {v : V // v ≠ center} := ⟨q, hqCenter⟩
  have hqA' : q' ∉ S.aSet := by
    intro h
    exact hqA (val_mem_ahtDeletedFinsetVal.mpr h)
  have hqB' : q' ∉ S.bSet := by
    intro hqB
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hBcard
    have hqb : q' = b := by simpa [hb] using hqB
    have hzBb : S.zB = b := by simpa [hb] using S.Z_B_attachment.1
    have hqEq : q = S.zB.1 :=
      congrArg Subtype.val (hqb.trans hzBb.symm)
    have hzAqB : G.Adj S.zA.1 S.zB.1 := by simpa [hqEq] using hzAq
    exact htri (S.adj_z_zA_of_zPart_card_one hz)
      hzAqB (S.adj_z_zB_of_zPart_card_one hz).symm
  have hqX : q' ∉ S.xPart := by
    intro hqX
    have hdel : (deleteVertex G center).Adj q' S.zA :=
      (deleteVertex_adj (G := G)).mpr (by simpa [q'] using hzAq.symm)
    have heq := S.X_A_attachment.2.2 q' hqX
      S.zA S.Z_A_attachment.1 hdel
    exact hAne.2.1 heq.symm
  have hqY : q' ∉ S.yPart := by
    intro hqY
    have hdel : (deleteVertex G center).Adj q' S.zA :=
      (deleteVertex_adj (G := G)).mpr (by simpa [q'] using hzAq.symm)
    have heq := S.Y_A_attachment.2.2 q' hqY
      S.zA S.Z_A_attachment.1 hdel
    exact hAne.2.2 heq.symm
  have hqZ : q' ∉ S.zPart := by
    intro hqZ
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hz
    have hqt : q' = t := by simpa [ht] using hqZ
    have hzt : z = t := by simpa [ht] using S.z_mem_Z
    exact hqz (congrArg Subtype.val (hqt.trans hzt.symm))
  exact S.exists_mixedResidualComponent_of_seed hcenterNeighbors hBcard
    (by simp [hqA', hqB']) hqX hqY hqZ (by simpa [q'] using hqLeft)

/-- The local degree/triangle-free selection of the source component `D'`
in the normalized mixed branch `|A|=3, |B|=1`.  Claim (5) gives
`|C_A|≤1`.  If `C_A={d}`, tightness makes `d` adjacent to all three
`A` attachments and a third neighbour of `y_A` leaves `A∪C_A`.  If
`C_A=∅`, triangle-freeness lets one of `y_A,z_A` have at most one possible
neighbour in `A`, and minimum degree again supplies the residual seed. -/
theorem exists_mixedResidualComponent_of_leftCarrier_card_le_one
    (hthree : IsThreeConnected G) (htri : AHTTriangleFree G)
    (hcenterNeighbors : ∀ ⦃r : V⦄, G.Adj center r →
      r = x.1 ∨ r = y.1 ∨ r = z.1)
    (hAcard : S.aSet.card = 3) (hBcard : S.bSet.card = 1)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    (hcard : S.ambientLeftCarrier.card ≤ 1) :
    Nonempty S.MixedResidualComponent := by
  classical
  have hAeq : ahtDeletedFinsetVal S.aSet =
      {S.xA.1, S.yA.1, S.zA.1} := by
    simp [S.A_eq]
  by_cases hC : S.ambientLeftCarrier.Nonempty
  · have hCcard : S.ambientLeftCarrier.card = 1 := by
      have hpos := Finset.card_pos.mpr hC
      omega
    obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hCcard
    have htight := externalBoundary_tight_of_card_three hthree
      S.ambientLeftCarrier (ahtDeletedFinsetVal S.aSet)
      S.ambientLeftCarrier_disjoint S.ambientLeftCarrier_externalBoundary
      hC (by simpa using hAcard) S.center_not_mem_ambientLeftCarrier
      (center_not_mem_ahtDeletedFinsetVal S.aSet)
    have hdA (a : {v : V // v ≠ center}) (ha : a ∈ S.aSet) :
        G.Adj d a.1 := by
      obtain ⟨c, hcC, hca⟩ := htight a.1
        (val_mem_ahtDeletedFinsetVal.mpr ha)
      have hcd : c = d := by simpa [hd] using hcC
      simpa [hcd] using hca
    have hdyA : G.Adj d S.yA.1 := hdA S.yA S.Y_A_attachment.1
    have hdxA : G.Adj d S.xA.1 := hdA S.xA S.X_A_attachment.1
    have hdzA : G.Adj d S.zA.1 := hdA S.zA S.Z_A_attachment.1
    obtain ⟨q, hyAq, hqy, hqd⟩ :=
      exists_adj_ne_pair (G := G) (hthree.degree_ge S.yA.1)
        (a := y.1) (b := d)
    have hqA : q ∉ ahtDeletedFinsetVal S.aSet := by
      intro hqA
      rw [hAeq] at hqA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqA
      rcases hqA with rfl | rfl | rfl
      · exact htri hyAq hdxA.symm hdyA
      · exact G.loopless.irrefl S.yA.1 hyAq
      · exact htri hyAq hdzA.symm hdyA
    have hqLeft : q ∉ S.ambientLeftCarrier := by
      simpa [hd] using hqd
    exact S.exists_mixedResidualComponent_of_yA_neighbor htri
      hcenterNeighbors hAcard hBcard hy hyAq hqA hqy hqLeft
  · have hCempty : S.ambientLeftCarrier = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hC
    by_cases hyAzA : G.Adj S.yA.1 S.zA.1
    · by_cases hyAxA : G.Adj S.yA.1 S.xA.1
      · have hzAxA : ¬G.Adj S.zA.1 S.xA.1 := by
          intro h
          exact htri hyAzA h hyAxA.symm
        obtain ⟨q, hzAq, hqz, hqyA⟩ :=
          exists_adj_ne_pair (G := G) (hthree.degree_ge S.zA.1)
            (a := z.1) (b := S.yA.1)
        have hqA : q ∉ ahtDeletedFinsetVal S.aSet := by
          intro hqA
          rw [hAeq] at hqA
          simp only [Finset.mem_insert, Finset.mem_singleton] at hqA
          rcases hqA with rfl | rfl | rfl
          · exact hzAxA hzAq
          · exact hqyA rfl
          · exact G.loopless.irrefl S.zA.1 hzAq
        exact S.exists_mixedResidualComponent_of_zA_neighbor htri
          hcenterNeighbors hAcard hBcard hz hzAq hqA hqz
            (by simpa [hCempty])
      · obtain ⟨q, hyAq, hqy, hqzA⟩ :=
          exists_adj_ne_pair (G := G) (hthree.degree_ge S.yA.1)
            (a := y.1) (b := S.zA.1)
        have hqA : q ∉ ahtDeletedFinsetVal S.aSet := by
          intro hqA
          rw [hAeq] at hqA
          simp only [Finset.mem_insert, Finset.mem_singleton] at hqA
          rcases hqA with rfl | rfl | rfl
          · exact hyAxA hyAq
          · exact G.loopless.irrefl S.yA.1 hyAq
          · exact hqzA rfl
        exact S.exists_mixedResidualComponent_of_yA_neighbor htri
          hcenterNeighbors hAcard hBcard hy hyAq hqA hqy
            (by simpa [hCempty])
    · obtain ⟨q, hyAq, hqy, hqxA⟩ :=
        exists_adj_ne_pair (G := G) (hthree.degree_ge S.yA.1)
          (a := y.1) (b := S.xA.1)
      have hqA : q ∉ ahtDeletedFinsetVal S.aSet := by
        intro hqA
        rw [hAeq] at hqA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqA
        rcases hqA with rfl | rfl | rfl
        · exact hqxA rfl
        · exact G.loopless.irrefl S.yA.1 hyAq
        · exact hyAzA hyAq
      exact S.exists_mixedResidualComponent_of_yA_neighbor htri
        hcenterNeighbors hAcard hBcard hy hyAq hqA hqy
          (by simpa [hCempty])

/-- If the other two terminal components are singletons and both splitter
sides are singletons, those two terminals have the same three neighbours:
`center` and the two common attachments.  They are therefore an ambient
degree-three twin pair adjacent to `center`, contradicting the source
choice that `center` is not close to any twin. -/
theorem false_of_yz_singletons_both_sides_singletons
    (hthree : IsThreeConnected G) (hnotClose : ¬IsCloseToAHTTwin G center)
    (hcy : G.Adj center y.1) (hcz : G.Adj center z.1)
    (hcenterNeighbors : ∀ ⦃q : V⦄, G.Adj center q →
      q = x.1 ∨ q = y.1 ∨ q = z.1)
    (hy : S.yPart.card = 1) (hz : S.zPart.card = 1)
    (hAcard : S.aSet.card = 1) (hBcard : S.bSet.card = 1) : False := by
  classical
  have hyAzA : S.yA = S.zA := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hAcard
    have hya : S.yA = a := by simpa [ha] using S.Y_A_attachment.1
    have hza : S.zA = a := by simpa [ha] using S.Z_A_attachment.1
    exact hya.trans hza.symm
  have hyBzB : S.yB = S.zB := by
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hBcard
    have hyb : S.yB = b := by simpa [hb] using S.Y_B_attachment.1
    have hzb : S.zB = b := by simpa [hb] using S.Z_B_attachment.1
    exact hyb.trans hzb.symm
  have hNy : G.neighborFinset y.1 ⊆ {center, S.yA.1, S.yB.1} := by
    intro q hq
    have hyq : G.Adj y.1 q := by simpa using hq
    by_cases hqc : q = center
    · simp [hqc]
    let q' : {v : V // v ≠ center} := ⟨q, hqc⟩
    have hdel : (deleteVertex G center).Adj y q' :=
      (deleteVertex_adj (G := G)).mpr hyq
    by_cases hqA : q' ∈ S.aSet
    · have heq := S.Y_A_attachment.2.2 y S.y_mem_Y q' hqA hdel
      have hval : q = S.yA.1 := congrArg Subtype.val heq
      simp [hval]
    by_cases hqB : q' ∈ S.bSet
    · have heq := S.Y_B_attachment.2.2 y S.y_mem_Y q' hqB hdel
      have hval : q = S.yB.1 := congrArg Subtype.val heq
      simp [hval]
    · have hqSep : q' ∉ S.aSet ∪ S.bSet := by simp [hqA, hqB]
      have hqY := S.Y_component.2.2.2 y S.y_mem_Y q' hqSep hdel
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hy
      have hqt : q' = t := by simpa [ht] using hqY
      have hyt : y = t := by simpa [ht] using S.y_mem_Y
      have hqy : q = y.1 := congrArg Subtype.val (hqt.trans hyt.symm)
      exact False.elim (G.loopless.irrefl y.1 (by simpa [hqy] using hyq))
  have hNz : G.neighborFinset z.1 ⊆ {center, S.yA.1, S.yB.1} := by
    intro q hq
    have hzq : G.Adj z.1 q := by simpa using hq
    by_cases hqc : q = center
    · simp [hqc]
    let q' : {v : V // v ≠ center} := ⟨q, hqc⟩
    have hdel : (deleteVertex G center).Adj z q' :=
      (deleteVertex_adj (G := G)).mpr hzq
    by_cases hqA : q' ∈ S.aSet
    · have heq := S.Z_A_attachment.2.2 z S.z_mem_Z q' hqA hdel
      have hval : q = S.zA.1 := congrArg Subtype.val heq
      simp [hval, ← hyAzA]
    by_cases hqB : q' ∈ S.bSet
    · have heq := S.Z_B_attachment.2.2 z S.z_mem_Z q' hqB hdel
      have hval : q = S.zB.1 := congrArg Subtype.val heq
      simp [hval, ← hyBzB]
    · have hqSep : q' ∉ S.aSet ∪ S.bSet := by simp [hqA, hqB]
      have hqZ := S.Z_component.2.2.2 z S.z_mem_Z q' hqSep hdel
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hz
      have hqt : q' = t := by simpa [ht] using hqZ
      have hzt : z = t := by simpa [ht] using S.z_mem_Z
      have hqz : q = z.1 := congrArg Subtype.val (hqt.trans hzt.symm)
      exact False.elim (G.loopless.irrefl z.1 (by simpa [hqz] using hzq))
  have htripleCard :
      ({center, S.yA.1, S.yB.1} : Finset V).card ≤ 3 := by
    calc
      ({center, S.yA.1, S.yB.1} : Finset V).card ≤
          ({S.yA.1, S.yB.1} : Finset V).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ 2 + 1 := Nat.add_le_add_right
        ((Finset.card_insert_le S.yA.1 ({S.yB.1} : Finset V)).trans
          (by simp)) 1
      _ = 3 := rfl
  have triple_eq_neighbor {w : V}
      (hsub : G.neighborFinset w ⊆ {center, S.yA.1, S.yB.1}) :
      G.neighborFinset w = {center, S.yA.1, S.yB.1} := by
    apply Finset.eq_of_subset_of_card_le hsub
    have hN : 3 ≤ (G.neighborFinset w).card := by
      simpa only [G.card_neighborFinset_eq_degree] using hthree.degree_ge w
    omega
  have hNyEq := triple_eq_neighbor hNy
  have hNzEq := triple_eq_neighbor hNz
  have hyz : y.1 ≠ z.1 := by
    intro hyz
    have hyz' : y = z := Subtype.ext hyz
    exact Finset.disjoint_left.mp S.Y_disjoint_Z S.y_mem_Y
      (hyz' ▸ S.z_mem_Z)
  have hsets : G.neighborSet y.1 = G.neighborSet z.1 := by
    ext q
    have hq : q ∈ G.neighborFinset y.1 ↔
        q ∈ G.neighborFinset z.1 := by rw [hNyEq, hNzEq]
    simpa only [SimpleGraph.mem_neighborSet,
      ← SimpleGraph.mem_neighborFinset] using hq
  have hdegy : G.degree y.1 = 3 := by
    have hge := hthree.degree_ge y.1
    have hle : G.degree y.1 ≤ 3 := by
      rw [← G.card_neighborFinset_eq_degree, hNyEq]
      exact htripleCard
    omega
  have htwin : AHTTwinPair G y.1 z.1 := ⟨⟨hyz, hsets⟩, hdegy⟩
  exact hnotClose (IsCloseToAHTTwin.of_adj_left htwin hcy)

end WatkinsMesnerSplitter

end Erdos916
