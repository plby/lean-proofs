/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceLemma63
import ErdosProblems.Erdos916.AHTSourceLemma65
import ErdosProblems.Erdos916.AHTSourceTheorem66Case2
import ErdosProblems.Erdos916.AHTWatkinsMesner

/-!
# The deleted-center cardinality half of AHT Theorem 6.6, claim (3)

This file isolates the size comparison for the graph `G_X` in claim (3) of
the proof of Theorem 6.6 of Aboulker--Havet--Trotignon.  The certificate
below contains only the literal splitter, its two terminal-component
certificates, and the three vertex-cover facts of the source construction.
In particular, it has no field asserting a cardinal inequality.

The proof follows the published argument.  A hypothetical non-smaller
replacement first gives `|Y| + |Z| ≤ 4`.  The terminal-component trichotomy
then rules out a three-vertex component by Lemma 6.3.  When both components
are singletons, Lemma 6.3 and the choice of `center` orient `A` as the
three-element side.  The refined replacement cover leaves just one possible
equality case; in that case one of `y_A,z_A` has degree at most two.
-/

namespace Erdos916

open SimpleGraph

universe u w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The ambient image of a vertex finset in `G - center`.  This is the
injective set map used to compare the Watkins--Mesner decomposition, whose
vertices are subtypes, with the ambient replacement graph. -/
def ahtDeletedFinsetVal {center : V}
    (S : Finset {v : V // v ≠ center}) : Finset V :=
  S.map (Function.Embedding.subtype _)

/-- Concrete local data for the `G_X` size comparison in AHT claim (3).

`gxVerts` is the actual vertex finset of the replacement graph.  The three
cover fields are literal consequences of the construction in the three
successive source cases; they are finset inclusions, not cardinal bounds.
The last orientation field records the harmless exchange of the names
`A,B` made in the source before the final singleton calculation. -/
structure AHTClaim3CardinalityCertificateDeleted
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (center : V) (x y z : {v : V // v ≠ center})
    (W : Type w) [DecidableEq W] where
  splitter : WatkinsMesnerSplitter (deleteVertex G center) x y z
  yLocal : AHTTerminalComponentLocal G
  zLocal : AHTTerminalComponentLocal G
  yLocal_part : yLocal.part = ahtDeletedFinsetVal splitter.yPart
  yLocal_terminal : yLocal.terminal = y.1
  yLocal_boundaryA : yLocal.boundaryA = splitter.yA.1
  yLocal_boundaryB : yLocal.boundaryB = splitter.yB.1
  yLocal_center : yLocal.center = center
  zLocal_part : zLocal.part = ahtDeletedFinsetVal splitter.zPart
  zLocal_terminal : zLocal.terminal = z.1
  zLocal_boundaryA : zLocal.boundaryA = splitter.zA.1
  zLocal_boundaryB : zLocal.boundaryB = splitter.zB.1
  zLocal_center : zLocal.center = center
  center_adj_x : G.Adj center x.1
  center_adj_y : G.Adj center y.1
  center_adj_z : G.Adj center z.1
  center_neighbor_location :
    ∀ ⦃q : V⦄, G.Adj center q → q = x.1 ∨ q = y.1 ∨ q = z.1
  center_not_close : ¬IsCloseToAHTTwin G center
  oldVertex : V ↪ W
  gxVerts : Finset W
  gxGraph : SimpleGraph gxVerts
  yPrime : W
  zPrime : W
  xAPrime : W
  xBPrime : W
  /-- Before any case split, `G_X` has at most the old
  `A ∪ B ∪ X ∪ {center}` vertices and the four displayed replacement
  vertices. -/
  gx_cover_four :
    gxVerts ⊆
      (((ahtDeletedFinsetVal splitter.aSet ∪
          ahtDeletedFinsetVal splitter.bSet ∪
          ahtDeletedFinsetVal splitter.xPart ∪ {center}).map
          oldVertex) ∪ {yPrime, zPrime, xAPrime, xBPrime})
  /-- If one of `Y,Z` is non-singleton, only the two named boundary
  representatives, `X`, and `center` can be old vertices of `G_X`. -/
  gx_cover_of_large_terminal :
    (2 ≤ splitter.yPart.card ∨ 2 ≤ splitter.zPart.card) →
      gxVerts ⊆
        (((ahtDeletedFinsetVal splitter.xPart ∪
            {splitter.xA.1, splitter.xB.1, center}).map
            oldVertex) ∪ {yPrime, zPrime, xAPrime, xBPrime})
  /-- After `Y,Z` are singletons and `A` is the three-side, the source
  construction retains `A,X,x_B,center` and only the two possible fresh
  `x`-pins. -/
  gx_cover_of_singletons_A :
    splitter.yPart.card = 1 → splitter.zPart.card = 1 →
      splitter.aSet.card = 3 →
      gxVerts ⊆
        (((ahtDeletedFinsetVal splitter.aSet ∪
            ahtDeletedFinsetVal splitter.xPart ∪
            {splitter.xB.1, center}).map
            oldVertex) ∪ {xAPrime, xBPrime})
  /-- The names have been exchanged if necessary so that equality of the
  two `A`-attachments forces equality of the two `B`-attachments. -/
  oriented : splitter.yA = splitter.zA → splitter.yB = splitter.zB

namespace AHTClaim3CardinalityCertificateDeleted

variable {W : Type w} [DecidableEq W]
variable {center : V} {x y z : {v : V // v ≠ center}}
variable (C : AHTClaim3CardinalityCertificateDeleted G center x y z W)

@[simp] theorem card_ahtDeletedFinsetVal
    (S : Finset {v : V // v ≠ center}) :
    (ahtDeletedFinsetVal S).card = S.card := by
  exact Finset.card_map _

@[simp] theorem val_mem_ahtDeletedFinsetVal
    {S : Finset {v : V // v ≠ center}} {q : {v : V // v ≠ center}} :
    q.1 ∈ ahtDeletedFinsetVal S ↔ q ∈ S := by
  constructor
  · intro h
    rw [ahtDeletedFinsetVal, Finset.mem_map] at h
    obtain ⟨r, hr, hval⟩ := h
    have hrq : r = q := Subtype.ext hval
    simpa [hrq] using hr
  · intro h
    exact Finset.mem_map.mpr ⟨q, h, rfl⟩

@[simp] theorem ahtDeletedFinsetVal_nonempty
    {S : Finset {v : V // v ≠ center}} :
    (ahtDeletedFinsetVal S).Nonempty ↔ S.Nonempty := by
  constructor
  · rintro ⟨q, hq⟩
    rw [ahtDeletedFinsetVal, Finset.mem_map] at hq
    obtain ⟨q', hq', -⟩ := hq
    exact ⟨q', hq'⟩
  · rintro ⟨q, hq⟩
    exact ⟨q.1, val_mem_ahtDeletedFinsetVal.mpr hq⟩

theorem center_not_mem_ahtDeletedFinsetVal
    (S : Finset {v : V // v ≠ center}) :
    center ∉ ahtDeletedFinsetVal S := by
  intro h
  rw [ahtDeletedFinsetVal, Finset.mem_map] at h
  obtain ⟨q, -, hq⟩ := h
  exact q.2 hq

theorem exists_subtype_of_mem_ahtDeletedFinsetVal
    {S : Finset {v : V // v ≠ center}} {q : V}
    (h : q ∈ ahtDeletedFinsetVal S) :
    ∃ q' ∈ S, q'.1 = q := by
  rw [ahtDeletedFinsetVal, Finset.mem_map] at h
  obtain ⟨q', hq', hval⟩ := h
  exact ⟨q', hq', hval⟩

theorem disjoint_ahtDeletedFinsetVal
    {S T : Finset {v : V // v ≠ center}} (h : Disjoint S T) :
    Disjoint (ahtDeletedFinsetVal S) (ahtDeletedFinsetVal T) := by
  exact (Finset.disjoint_map (Function.Embedding.subtype _)).2 h

theorem ambient_adj_of_deleteVertex
    {p q : {v : V // v ≠ center}}
    (h : (deleteVertex G center).Adj p q) : G.Adj p.1 q.1 := by
  exact (deleteVertex_adj (G := G)).mp h

/-- The actual vertex type of the replacement graph `G_X`. -/
abbrev GXVertex := C.gxVerts

/-- The replacement graph, with its concrete vertex type. -/
abbrev GX : SimpleGraph C.GXVertex := C.gxGraph

private theorem eq_of_mem_of_card_eq_one
    {S : Finset V} {p q : V} (hp : p ∈ S) (hq : q ∈ S)
    (hcard : S.card = 1) : p = q := by
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard
  have hpr : p = r := by simpa [hr] using hp
  have hqr : q = r := by simpa [hr] using hq
  exact hpr.trans hqr.symm

private theorem card_quad_le (a b c d : W) :
    ({a, b, c, d} : Finset W).card ≤ 4 := by
  calc
    ({a, b, c, d} : Finset W).card
        ≤ ({b, c, d} : Finset W).card + 1 := Finset.card_insert_le _ _
    _ ≤ (({c, d} : Finset W).card + 1) + 1 := by
      exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ ≤ ((({d} : Finset W).card + 1) + 1) + 1 := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
    _ = 4 := by simp

private theorem card_pair_le' {T : Type*} [DecidableEq T] (a b : T) :
    ({a, b} : Finset T).card ≤ 2 := by
  calc
    ({a, b} : Finset T).card ≤ ({b} : Finset T).card + 1 :=
      Finset.card_insert_le _ _
    _ = 2 := by simp

private theorem exceptional_card_eq_three
    {D : AHTTerminalComponentLocal G}
    (h : AHTTerminalExceptionalTriple D) : D.part.card = 3 := by
  obtain ⟨p, q, hp, hq, hpq, hpart, hpA, hqA, hpB, hqB⟩ := h
  rw [hpart]
  simp [hp.symm, hq.symm, hpq]

private theorem singleton_eq
    {S : Finset V} {p : V} (hp : p ∈ S) (hcard : S.card = 1) :
    S = {p} := by
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  have hpq : p = q := by simpa [hq] using hp
  simpa [hpq] using hq

private theorem attachment_adj_of_singleton
    {S T : Finset {v : V // v ≠ center}}
    {p a : {v : V // v ≠ center}}
    (hp : p ∈ S) (hS : S.card = 1)
    (hatt : IsUniqueAttachment (deleteVertex G center) S T a) :
    G.Adj p.1 a.1 := by
  obtain ⟨q, hqS, hqa⟩ := hatt.2.1
  have hqp : q = p := by
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hS
    have hqr : q = r := by simpa [hr] using hqS
    have hpr : p = r := by simpa [hr] using hp
    exact hqr.trans hpr.symm
  apply ambient_adj_of_deleteVertex
  simpa [hqp] using hqa

private theorem degree_le_two_of_neighborFinset_subset_pair
    {p a b : V} (hsub : G.neighborFinset p ⊆ {a, b}) :
    G.degree p ≤ 2 := by
  rw [← G.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card hsub).trans (card_pair_le' _ _)

/-- The cardinality conclusion of AHT Theorem 6.6, claim (3). -/
theorem gxVerts_card_lt
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G) :
    C.gxVerts.card < Fintype.card V := by
  let A := ahtDeletedFinsetVal C.splitter.aSet
  let B := ahtDeletedFinsetVal C.splitter.bSet
  let X := ahtDeletedFinsetVal C.splitter.xPart
  let Y := ahtDeletedFinsetVal C.splitter.yPart
  let Z := ahtDeletedFinsetVal C.splitter.zPart
  let U := ((((A ∪ B) ∪ X) ∪ Y) ∪ Z) ∪ {center}
  let K := ((A ∪ B) ∪ X) ∪ {center}
  have hAB : Disjoint A B := by
    simpa [A, B] using
      disjoint_ahtDeletedFinsetVal C.splitter.A_disjoint_B
  have hABX : Disjoint (A ∪ B) X := by
    simpa [A, B, X, ahtDeletedFinsetVal, Finset.map_union] using
      disjoint_ahtDeletedFinsetVal C.splitter.X_component.2.1.symm
  have hABY : Disjoint (A ∪ B) Y := by
    simpa [A, B, Y, ahtDeletedFinsetVal, Finset.map_union] using
      disjoint_ahtDeletedFinsetVal C.splitter.Y_component.2.1.symm
  have hABZ : Disjoint (A ∪ B) Z := by
    simpa [A, B, Z, ahtDeletedFinsetVal, Finset.map_union] using
      disjoint_ahtDeletedFinsetVal C.splitter.Z_component.2.1.symm
  have hXY : Disjoint X Y := by
    simpa [X, Y] using
      disjoint_ahtDeletedFinsetVal C.splitter.X_disjoint_Y
  have hXZ : Disjoint X Z := by
    simpa [X, Z] using
      disjoint_ahtDeletedFinsetVal C.splitter.X_disjoint_Z
  have hYZ : Disjoint Y Z := by
    simpa [Y, Z] using
      disjoint_ahtDeletedFinsetVal C.splitter.Y_disjoint_Z
  have hABX_Y : Disjoint ((A ∪ B) ∪ X) Y := by
    apply Finset.disjoint_left.mpr
    intro q hq hqY
    rcases Finset.mem_union.mp hq with hqAB | hqX
    · exact Finset.disjoint_left.mp hABY hqAB hqY
    · exact Finset.disjoint_left.mp hXY hqX hqY
  have hABXY_Z : Disjoint (((A ∪ B) ∪ X) ∪ Y) Z := by
    apply Finset.disjoint_left.mpr
    intro q hq hqZ
    rcases Finset.mem_union.mp hq with hqABX | hqY
    · rcases Finset.mem_union.mp hqABX with hqAB | hqX
      · exact Finset.disjoint_left.mp hABZ hqAB hqZ
      · exact Finset.disjoint_left.mp hXZ hqX hqZ
    · exact Finset.disjoint_left.mp hYZ hqY hqZ
  have hcAB : center ∉ A ∪ B := by
    simp [A, B, center_not_mem_ahtDeletedFinsetVal]
  have hcX : center ∉ X := by
    simpa [X] using center_not_mem_ahtDeletedFinsetVal C.splitter.xPart
  have hcY : center ∉ Y := by
    simpa [Y] using center_not_mem_ahtDeletedFinsetVal C.splitter.yPart
  have hcZ : center ∉ Z := by
    simpa [Z] using center_not_mem_ahtDeletedFinsetVal C.splitter.zPart
  have hABXYZ_c : Disjoint ((((A ∪ B) ∪ X) ∪ Y) ∪ Z) {center} := by
    apply Finset.disjoint_right.mpr
    intro q hqc hq
    have hqcenter : q = center := by simpa using hqc
    subst q
    simp only [Finset.mem_union] at hq
    rcases hq with hq | hqZ
    · rcases hq with hq | hqY
      · rcases hq with hqAB | hqX
        · exact hcAB (by simpa using hqAB)
        · exact hcX hqX
      · exact hcY hqY
    · exact hcZ hqZ
  have hABXY : Disjoint ((A ∪ B) ∪ X) Y := hABX_Y
  have hcardU :
      U.card = A.card + B.card + X.card + Y.card + Z.card + 1 := by
    dsimp [U]
    rw [Finset.card_union_of_disjoint hABXYZ_c,
      Finset.card_singleton,
      Finset.card_union_of_disjoint hABXY_Z,
      Finset.card_union_of_disjoint hABXY,
      Finset.card_union_of_disjoint hABX,
      Finset.card_union_of_disjoint hAB]
  have hK_c : Disjoint ((A ∪ B) ∪ X) {center} := by
    apply Finset.disjoint_right.mpr
    intro q hqc hq
    have hqcenter : q = center := by simpa using hqc
    subst q
    rcases Finset.mem_union.mp hq with hqAB | hqX
    · exact hcAB hqAB
    · exact hcX hqX
  have hcardK : K.card = A.card + B.card + X.card + 1 := by
    dsimp [K]
    rw [Finset.card_union_of_disjoint hK_c, Finset.card_singleton,
      Finset.card_union_of_disjoint hABX,
      Finset.card_union_of_disjoint hAB]
  have hUle : U.card ≤ Fintype.card V := by
    simpa using Finset.card_le_card (Finset.subset_univ U)
  have hpinsFour :
      ({C.yPrime, C.zPrime, C.xAPrime, C.xBPrime} : Finset W).card ≤ 4 :=
    card_quad_le _ _ _ _
  have hGXleFour : C.gxVerts.card ≤ K.card + 4 := by
    let P : Finset W := {C.yPrime, C.zPrime, C.xAPrime, C.xBPrime}
    have hcover : C.gxVerts ⊆ (K.map C.oldVertex) ∪ P := by
      simpa [A, B, X, K, P] using C.gx_cover_four
    calc
      C.gxVerts.card ≤ ((K.map C.oldVertex) ∪ P).card :=
        Finset.card_le_card hcover
      _ ≤ (K.map C.oldVertex).card + P.card := Finset.card_union_le _ _
      _ = K.card + P.card := by rw [Finset.card_map]
      _ ≤ K.card + 4 := by dsimp [P]; omega
  by_contra hsmall
  have hGle : Fintype.card V ≤ C.gxVerts.card := Nat.le_of_not_gt hsmall
  have hYZle : Y.card + Z.card ≤ 4 := by
    have hUle' := hUle
    have hGXleFour' := hGXleFour
    rw [hcardU] at hUle'
    rw [hcardK] at hGXleFour'
    omega
  have hYpos : 1 ≤ Y.card := by
    apply Finset.one_le_card.mpr
    simpa [Y] using C.splitter.Y_component.1
  have hZpos : 1 ≤ Z.card := by
    apply Finset.one_le_card.mpr
    simpa [Z] using C.splitter.Z_component.1
  have htri : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  have hmin : ∀ q : V, 3 ≤ G.degree q := hthree.degree_ge
  have hYraw := aht_theorem66_claim6_terminal_component C.yLocal htri hmin
  have hZraw := aht_theorem66_claim6_terminal_component C.zLocal htri hmin
  have hYcases : Y.card = 1 ∨ AHTTerminalExceptionalTriple C.yLocal := by
    rcases hYraw with h1 | h4 | hex
    · exact Or.inl (by simpa [Y, C.yLocal_part] using h1)
    · have : 4 ≤ Y.card := by simpa [Y, C.yLocal_part] using h4
      omega
    · exact Or.inr hex
  have hZcases : Z.card = 1 ∨ AHTTerminalExceptionalTriple C.zLocal := by
    rcases hZraw with h1 | h4 | hex
    · exact Or.inl (by simpa [Z, C.zLocal_part] using h1)
    · have : 4 ≤ Z.card := by simpa [Z, C.zLocal_part] using h4
      omega
    · exact Or.inr hex
  have hlarge_implies_AB_singletons
      (hlarge : 2 ≤ Y.card ∨ 2 ≤ Z.card)
      (hYZeq : Y.card + Z.card = 4) : A.card = 1 ∧ B.card = 1 := by
    let L := X ∪ {C.splitter.xA.1, C.splitter.xB.1, center}
    have hxAA : C.splitter.xA.1 ∈ A := by
      simpa [A] using C.splitter.X_A_attachment.1
    have hxBB : C.splitter.xB.1 ∈ B := by
      simpa [B] using C.splitter.X_B_attachment.1
    have hxAXB : C.splitter.xA.1 ≠ C.splitter.xB.1 := by
      intro h
      exact Finset.disjoint_left.mp hAB hxAA (h.symm ▸ hxBB)
    have hxAX : C.splitter.xA.1 ∉ X := by
      intro h
      exact Finset.disjoint_left.mp hABX
        (Finset.mem_union_left _ hxAA) h
    have hxBX : C.splitter.xB.1 ∉ X := by
      intro h
      exact Finset.disjoint_left.mp hABX
        (Finset.mem_union_right _ hxBB) h
    have hcxA : center ≠ C.splitter.xA.1 := by
      exact C.splitter.xA.2.symm
    have hcxB : center ≠ C.splitter.xB.1 := by
      exact C.splitter.xB.2.symm
    have hXL : Disjoint X ({C.splitter.xA.1, C.splitter.xB.1, center} : Finset V) := by
      apply Finset.disjoint_left.mpr
      intro q hqX hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hxAX hqX
      · exact hxBX hqX
      · exact hcX hqX
    have hcardL : L.card = X.card + 3 := by
      dsimp [L]
      rw [Finset.card_union_of_disjoint hXL]
      have htriple :
          ({C.splitter.xA.1, C.splitter.xB.1, center} : Finset V).card = 3 := by
        exact Finset.card_eq_three.mpr
          ⟨C.splitter.xA.1, C.splitter.xB.1, center,
            hxAXB, hcxA.symm, hcxB.symm, rfl⟩
      rw [htriple]
    have hcoverLarge : C.gxVerts ⊆
        (L.map C.oldVertex) ∪
          ({C.yPrime, C.zPrime, C.xAPrime, C.xBPrime} : Finset W) := by
      apply C.gx_cover_of_large_terminal
      simpa [Y, Z] using hlarge
    have hGXle : C.gxVerts.card ≤ L.card + 4 := by
      calc
        C.gxVerts.card ≤ ((L.map C.oldVertex) ∪
            ({C.yPrime, C.zPrime, C.xAPrime, C.xBPrime} : Finset W)).card :=
          Finset.card_le_card hcoverLarge
        _ ≤ (L.map C.oldVertex).card +
            ({C.yPrime, C.zPrime, C.xAPrime, C.xBPrime} : Finset W).card :=
          Finset.card_union_le _ _
        _ = L.card +
            ({C.yPrime, C.zPrime, C.xAPrime, C.xBPrime} : Finset W).card := by
          rw [Finset.card_map]
        _ ≤ L.card + 4 := by omega
    have hApos : 1 ≤ A.card := by
      apply Finset.one_le_card.mpr
      simpa [A] using C.splitter.A_nonempty
    have hBpos : 1 ≤ B.card := by
      apply Finset.one_le_card.mpr
      simpa [B] using C.splitter.B_nonempty
    have hUle' := hUle
    rw [hcardU] at hUle'
    rw [hcardL] at hGXle
    omega
  have hAeq_of_one (hA : A.card = 1) :
      C.splitter.xA.1 = C.splitter.yA.1 ∧
        C.splitter.xA.1 = C.splitter.zA.1 := by
    constructor
    · exact eq_of_mem_of_card_eq_one (S := A)
        (by simpa [A] using C.splitter.X_A_attachment.1)
        (by simpa [A] using C.splitter.Y_A_attachment.1)
        (by simpa [A] using hA)
    · exact eq_of_mem_of_card_eq_one (S := A)
        (by simpa [A] using C.splitter.X_A_attachment.1)
        (by simpa [A] using C.splitter.Z_A_attachment.1)
        (by simpa [A] using hA)
  have hBeq_of_one (hB : B.card = 1) :
      C.splitter.xB.1 = C.splitter.yB.1 ∧
        C.splitter.xB.1 = C.splitter.zB.1 := by
    constructor
    · exact eq_of_mem_of_card_eq_one (S := B)
        (by simpa [B] using C.splitter.X_B_attachment.1)
        (by simpa [B] using C.splitter.Y_B_attachment.1)
        (by simpa [B] using hB)
    · exact eq_of_mem_of_card_eq_one (S := B)
        (by simpa [B] using C.splitter.X_B_attachment.1)
        (by simpa [B] using C.splitter.Z_B_attachment.1)
        (by simpa [B] using hB)
  have false_of_Y_exception_Z_one
      (hYex : AHTTerminalExceptionalTriple C.yLocal)
      (hZ1 : Z.card = 1) : False := by
    have hY3Local := exceptional_card_eq_three hYex
    have hY3 : Y.card = 3 := by
      simpa [Y, C.yLocal_part] using hY3Local
    have hYZeq : Y.card + Z.card = 4 := by omega
    obtain ⟨hA1, hB1⟩ := hlarge_implies_AB_singletons
      (Or.inl (by omega)) hYZeq
    obtain ⟨hxAyA, hxAzA⟩ := hAeq_of_one hA1
    obtain ⟨hxByB, hxBzB⟩ := hBeq_of_one hB1
    obtain ⟨p, q, hpne, hqne, hpq, hpart,
      hpA, hqA, hpB, hqB⟩ := hYex
    have hpY : p ∈ Y := by
      change p ∈ ahtDeletedFinsetVal C.splitter.yPart
      rw [← C.yLocal_part, hpart]
      simp
    have hqY : q ∈ Y := by
      change q ∈ ahtDeletedFinsetVal C.splitter.yPart
      rw [← C.yLocal_part, hpart]
      simp
    have hzXA : G.Adj C.splitter.xA.1 z.1 := by
      have hzA := attachment_adj_of_singleton C.splitter.z_mem_Z
        (by simpa [Z] using hZ1) C.splitter.Z_A_attachment
      simpa [hxAzA] using hzA.symm
    have hzXB : G.Adj C.splitter.xB.1 z.1 := by
      have hzB := attachment_adj_of_singleton C.splitter.z_mem_Z
        (by simpa [Z] using hZ1) C.splitter.Z_B_attachment
      simpa [hxBzB] using hzB.symm
    have hpXA : G.Adj C.splitter.xA.1 p := by
      simpa [C.yLocal_boundaryA, hxAyA] using hpA
    have hqXA : G.Adj C.splitter.xA.1 q := by
      simpa [C.yLocal_boundaryA, hxAyA] using hqA
    have hpXB : G.Adj C.splitter.xB.1 p := by
      simpa [C.yLocal_boundaryB, hxByB] using hpB
    have hqXB : G.Adj C.splitter.xB.1 q := by
      simpa [C.yLocal_boundaryB, hxByB] using hqB
    have hxAAmb : C.splitter.xA.1 ∈ A := by
      change C.splitter.xA.1 ∈ ahtDeletedFinsetVal C.splitter.aSet
      exact val_mem_ahtDeletedFinsetVal.mpr C.splitter.X_A_attachment.1
    have hxBAmb : C.splitter.xB.1 ∈ B := by
      change C.splitter.xB.1 ∈ ahtDeletedFinsetVal C.splitter.bSet
      exact val_mem_ahtDeletedFinsetVal.mpr C.splitter.X_B_attachment.1
    have hxAXB : C.splitter.xA.1 ≠ C.splitter.xB.1 := by
      intro h
      exact Finset.disjoint_left.mp hAB hxAAmb (by simpa [h] using hxBAmb)
    have hzZAmb : z.1 ∈ Z := by
      change z.1 ∈ ahtDeletedFinsetVal C.splitter.zPart
      exact val_mem_ahtDeletedFinsetVal.mpr C.splitter.z_mem_Z
    have hpz : p ≠ z.1 := by
      intro h
      exact Finset.disjoint_left.mp hYZ hpY
        (by simpa [h] using hzZAmb)
    have hqz : q ≠ z.1 := by
      intro h
      exact Finset.disjoint_left.mp hYZ hqY
        (by simpa [h] using hzZAmb)
    have htwin := aht_twinPair_of_three_common_neighbors
      hthree halmost hxAXB hpq hpz hqz
      hpXA hqXA hzXA hpXB hqXB hzXB
    obtain ⟨d, hdX, hdxA⟩ := C.splitter.X_A_attachment.2.1
    have hdXambient : d.1 ∈ X := by simpa [X] using hdX
    have hdp : d.1 ≠ p := by
      intro h
      exact Finset.disjoint_left.mp hXY hdXambient (h.symm ▸ hpY)
    have hdq : d.1 ≠ q := by
      intro h
      exact Finset.disjoint_left.mp hXY hdXambient (h.symm ▸ hqY)
    have hdz : d.1 ≠ z.1 := by
      intro h
      exact Finset.disjoint_left.mp hXZ hdXambient
        (by simpa [h] using hzZAmb)
    have hdxAambient : G.Adj d.1 C.splitter.xA.1 :=
      ambient_adj_of_deleteVertex hdxA
    have hfour : 4 ≤ G.degree C.splitter.xA.1 :=
      four_le_degree_of_three_neighbors_and_extra
        hpXA hqXA hzXA hdxAambient.symm hpq hpz hqz hdp hdq hdz
    have hthreeDeg : G.degree C.splitter.xA.1 = 3 := htwin.2
    omega
  have false_of_Z_exception_Y_one
      (hZex : AHTTerminalExceptionalTriple C.zLocal)
      (hY1 : Y.card = 1) : False := by
    have hZ3Local := exceptional_card_eq_three hZex
    have hZ3 : Z.card = 3 := by
      simpa [Z, C.zLocal_part] using hZ3Local
    have hYZeq : Y.card + Z.card = 4 := by omega
    obtain ⟨hA1, hB1⟩ := hlarge_implies_AB_singletons
      (Or.inr (by omega)) hYZeq
    obtain ⟨hxAyA, hxAzA⟩ := hAeq_of_one hA1
    obtain ⟨hxByB, hxBzB⟩ := hBeq_of_one hB1
    obtain ⟨p, q, hpne, hqne, hpq, hpart,
      hpA, hqA, hpB, hqB⟩ := hZex
    have hpZ : p ∈ Z := by
      change p ∈ ahtDeletedFinsetVal C.splitter.zPart
      rw [← C.zLocal_part, hpart]
      simp
    have hqZ : q ∈ Z := by
      change q ∈ ahtDeletedFinsetVal C.splitter.zPart
      rw [← C.zLocal_part, hpart]
      simp
    have hyXA : G.Adj C.splitter.xA.1 y.1 := by
      have hyA := attachment_adj_of_singleton C.splitter.y_mem_Y
        (by simpa [Y] using hY1) C.splitter.Y_A_attachment
      simpa [hxAyA] using hyA.symm
    have hyXB : G.Adj C.splitter.xB.1 y.1 := by
      have hyB := attachment_adj_of_singleton C.splitter.y_mem_Y
        (by simpa [Y] using hY1) C.splitter.Y_B_attachment
      simpa [hxByB] using hyB.symm
    have hpXA : G.Adj C.splitter.xA.1 p := by
      simpa [C.zLocal_boundaryA, hxAzA] using hpA
    have hqXA : G.Adj C.splitter.xA.1 q := by
      simpa [C.zLocal_boundaryA, hxAzA] using hqA
    have hpXB : G.Adj C.splitter.xB.1 p := by
      simpa [C.zLocal_boundaryB, hxBzB] using hpB
    have hqXB : G.Adj C.splitter.xB.1 q := by
      simpa [C.zLocal_boundaryB, hxBzB] using hqB
    have hxAAmb : C.splitter.xA.1 ∈ A := by
      change C.splitter.xA.1 ∈ ahtDeletedFinsetVal C.splitter.aSet
      exact val_mem_ahtDeletedFinsetVal.mpr C.splitter.X_A_attachment.1
    have hxBAmb : C.splitter.xB.1 ∈ B := by
      change C.splitter.xB.1 ∈ ahtDeletedFinsetVal C.splitter.bSet
      exact val_mem_ahtDeletedFinsetVal.mpr C.splitter.X_B_attachment.1
    have hxAXB : C.splitter.xA.1 ≠ C.splitter.xB.1 := by
      intro h
      exact Finset.disjoint_left.mp hAB hxAAmb (by simpa [h] using hxBAmb)
    have hyYAmb : y.1 ∈ Y := by
      change y.1 ∈ ahtDeletedFinsetVal C.splitter.yPart
      exact val_mem_ahtDeletedFinsetVal.mpr C.splitter.y_mem_Y
    have hpy : p ≠ y.1 := by
      intro h
      exact Finset.disjoint_left.mp hYZ
        (by simpa [h] using hyYAmb) hpZ
    have hqy : q ≠ y.1 := by
      intro h
      exact Finset.disjoint_left.mp hYZ
        (by simpa [h] using hyYAmb) hqZ
    have htwin := aht_twinPair_of_three_common_neighbors
      hthree halmost hxAXB hpq hpy hqy
      hpXA hqXA hyXA hpXB hqXB hyXB
    obtain ⟨d, hdX, hdxA⟩ := C.splitter.X_A_attachment.2.1
    have hdXambient : d.1 ∈ X := by simpa [X] using hdX
    have hdp : d.1 ≠ p := by
      intro h
      exact Finset.disjoint_left.mp hXZ hdXambient (h.symm ▸ hpZ)
    have hdq : d.1 ≠ q := by
      intro h
      exact Finset.disjoint_left.mp hXZ hdXambient (h.symm ▸ hqZ)
    have hdy : d.1 ≠ y.1 := by
      intro h
      exact Finset.disjoint_left.mp hXY hdXambient
        (by simpa [h] using hyYAmb)
    have hdxAambient : G.Adj d.1 C.splitter.xA.1 :=
      ambient_adj_of_deleteVertex hdxA
    have hfour : 4 ≤ G.degree C.splitter.xA.1 :=
      four_le_degree_of_three_neighbors_and_extra
        hpXA hqXA hyXA hdxAambient.symm hpq hpy hqy hdp hdq hdy
    have hthreeDeg : G.degree C.splitter.xA.1 = 3 := htwin.2
    omega
  have hY1 : Y.card = 1 := by
    rcases hYcases with h | h
    · exact h
    · rcases hZcases with hZ1 | hZex
      · exact (false_of_Y_exception_Z_one h hZ1).elim
      · have hY3 : Y.card = 3 := by
          simpa [Y, C.yLocal_part] using exceptional_card_eq_three h
        have hZ3 : Z.card = 3 := by
          simpa [Z, C.zLocal_part] using exceptional_card_eq_three hZex
        omega
  have hZ1 : Z.card = 1 := by
    rcases hZcases with h | h
    · exact h
    · exact (false_of_Z_exception_Y_one h hY1).elim
  have hYset : Y = {y.1} := singleton_eq
    (by simpa [Y] using C.splitter.y_mem_Y) hY1
  have hZset : Z = {z.1} := singleton_eq
    (by simpa [Z] using C.splitter.z_mem_Z) hZ1
  have hyA : G.Adj y.1 C.splitter.yA.1 :=
    attachment_adj_of_singleton C.splitter.y_mem_Y
      (by simpa [Y] using hY1) C.splitter.Y_A_attachment
  have hyB : G.Adj y.1 C.splitter.yB.1 :=
    attachment_adj_of_singleton C.splitter.y_mem_Y
      (by simpa [Y] using hY1) C.splitter.Y_B_attachment
  have hzA : G.Adj z.1 C.splitter.zA.1 :=
    attachment_adj_of_singleton C.splitter.z_mem_Z
      (by simpa [Z] using hZ1) C.splitter.Z_A_attachment
  have hzB : G.Adj z.1 C.splitter.zB.1 :=
    attachment_adj_of_singleton C.splitter.z_mem_Z
      (by simpa [Z] using hZ1) C.splitter.Z_B_attachment
  have hyz : y.1 ≠ z.1 := by
    have hyYAmb : y.1 ∈ Y := by
      change y.1 ∈ ahtDeletedFinsetVal C.splitter.yPart
      exact val_mem_ahtDeletedFinsetVal.mpr C.splitter.y_mem_Y
    have hzZAmb : z.1 ∈ Z := by
      change z.1 ∈ ahtDeletedFinsetVal C.splitter.zPart
      exact val_mem_ahtDeletedFinsetVal.mpr C.splitter.z_mem_Z
    intro h
    exact Finset.disjoint_left.mp hYZ hyYAmb (by simpa [h] using hzZAmb)
  have hyAAmb : C.splitter.yA.1 ∈ A := by
    change C.splitter.yA.1 ∈ ahtDeletedFinsetVal C.splitter.aSet
    exact val_mem_ahtDeletedFinsetVal.mpr C.splitter.Y_A_attachment.1
  have hyBAmb : C.splitter.yB.1 ∈ B := by
    change C.splitter.yB.1 ∈ ahtDeletedFinsetVal C.splitter.bSet
    exact val_mem_ahtDeletedFinsetVal.mpr C.splitter.Y_B_attachment.1
  have hyAyB : C.splitter.yA.1 ≠ C.splitter.yB.1 := by
    intro h
    exact Finset.disjoint_left.mp hAB hyAAmb (by simpa [h] using hyBAmb)
  have hcyA : center ≠ C.splitter.yA.1 := by
    exact C.splitter.yA.2.symm
  have hcyB : center ≠ C.splitter.yB.1 := by
    exact C.splitter.yB.2.symm
  have hyAzA : C.splitter.yA.1 ≠ C.splitter.zA.1 := by
    intro heqA
    have heqASub : C.splitter.yA = C.splitter.zA := Subtype.ext heqA
    have heqBSub : C.splitter.yB = C.splitter.zB := C.oriented heqASub
    have heqB : C.splitter.yB.1 = C.splitter.zB.1 :=
      congrArg Subtype.val heqBSub
    have htwin0 := aht_twinPair_of_three_common_neighbors
      hthree halmost hyz hyAyB hcyA.symm hcyB.symm
      hyA hyB C.center_adj_y.symm
      (by simpa [heqA] using hzA)
      (by simpa [heqB] using hzB)
      C.center_adj_z.symm
    have htwin : AHTTwinPair G y.1 z.1 := ⟨htwin0.1, htwin0.2⟩
    exact C.center_not_close
      (IsCloseToAHTTwin.of_adj_left htwin C.center_adj_y)
  have hA3 : A.card = 3 := by
    rcases C.splitter.A_card with hA1 | hA3
    · obtain ⟨hxy, hxz⟩ := hAeq_of_one (by simpa [A] using hA1)
      exact (hyAzA (hxy.symm.trans hxz)).elim
    · simpa [A] using hA3
  let R := (A ∪ X) ∪ {C.splitter.xB.1, center}
  let P : Finset W := {C.xAPrime, C.xBPrime}
  have hAX : Disjoint A X := by
    apply Finset.disjoint_left.mpr
    intro q hqA hqX
    exact Finset.disjoint_left.mp hABX
      (Finset.mem_union_left B hqA) hqX
  have hxBB : C.splitter.xB.1 ∈ B := by
    simpa [B] using C.splitter.X_B_attachment.1
  have hxB_not_A : C.splitter.xB.1 ∉ A := by
    intro hqA
    exact Finset.disjoint_left.mp hAB hqA hxBB
  have hxB_not_X : C.splitter.xB.1 ∉ X := by
    intro hqX
    exact Finset.disjoint_left.mp hABX
      (Finset.mem_union_right A hxBB) hqX
  have hcxB : center ≠ C.splitter.xB.1 := by
    exact C.splitter.xB.2.symm
  have hAX_pair :
      Disjoint (A ∪ X) ({C.splitter.xB.1, center} : Finset V) := by
    apply Finset.disjoint_left.mpr
    intro q hqAX hqPair
    rcases Finset.mem_union.mp hqAX with hqA | hqX
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hqPair
      rcases hqPair with rfl | rfl
      · exact hxB_not_A hqA
      · exact (center_not_mem_ahtDeletedFinsetVal C.splitter.aSet)
          (by simpa [A] using hqA)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hqPair
      rcases hqPair with rfl | rfl
      · exact hxB_not_X hqX
      · exact (center_not_mem_ahtDeletedFinsetVal C.splitter.xPart)
          (by simpa [X] using hqX)
  have hcardR : R.card = A.card + X.card + 2 := by
    dsimp [R]
    rw [Finset.card_union_of_disjoint hAX_pair,
      Finset.card_union_of_disjoint hAX]
    have : C.splitter.xB.1 ≠ center := hcxB.symm
    simp [this]
  have hcoverRef : C.gxVerts ⊆ (R.map C.oldVertex) ∪ P := by
    simpa [A, X, R, P] using
      C.gx_cover_of_singletons_A
        (by simpa [Y] using hY1) (by simpa [Z] using hZ1)
        (by simpa [A] using hA3)
  have hGXref : C.gxVerts.card ≤ R.card + 2 := by
    calc
      C.gxVerts.card ≤ ((R.map C.oldVertex) ∪ P).card :=
        Finset.card_le_card hcoverRef
      _ ≤ (R.map C.oldVertex).card + P.card := Finset.card_union_le _ _
      _ = R.card + P.card := by rw [Finset.card_map]
      _ ≤ R.card + 2 := by
        have := card_pair_le' C.xAPrime C.xBPrime
        simpa [P] using Nat.add_le_add_left this R.card
  have hBpos : 1 ≤ B.card := by
    apply Finset.one_le_card.mpr
    simpa [B] using C.splitter.B_nonempty
  have hB1 : B.card = 1 := by
    have hUle' := hUle
    have hGXref' := hGXref
    rw [hcardU] at hUle'
    rw [hcardR] at hGXref'
    omega
  have hxAA : C.splitter.xA.1 ∈ A := by
    simpa [A] using C.splitter.X_A_attachment.1
  have hxAR : C.splitter.xA.1 ∈ R := by
    simp [R, hxAA]
  have hxBR : C.splitter.xB.1 ∈ R := by simp [R]
  have hxAPrime_fresh :
      C.oldVertex C.splitter.xA.1 ≠ C.xAPrime := by
    intro heq
    have hsmallCover :
        (R.map C.oldVertex) ∪ P ⊆
          (R.map C.oldVertex) ∪ {C.xBPrime} := by
      intro q hq
      rcases Finset.mem_union.mp hq with hqR | hqP
      · exact Finset.mem_union_left _ hqR
      · simp only [P, Finset.mem_insert, Finset.mem_singleton] at hqP
        rcases hqP with rfl | rfl
        · apply Finset.mem_union_left
          rw [← heq]
          exact Finset.mem_map.mpr ⟨C.splitter.xA.1, hxAR, rfl⟩
        · exact Finset.mem_union_right _ (by simp)
    have hGXone : C.gxVerts.card ≤ R.card + 1 := by
      calc
        C.gxVerts.card ≤
            ((R.map C.oldVertex) ∪ {C.xBPrime}).card :=
          Finset.card_le_card (hcoverRef.trans hsmallCover)
        _ ≤ (R.map C.oldVertex).card + ({C.xBPrime} : Finset W).card :=
          Finset.card_union_le _ _
        _ = R.card + 1 := by simp
    have hUle' := hUle
    rw [hcardU] at hUle'
    rw [hcardR] at hGXone
    omega
  have hxBPrime_fresh :
      C.oldVertex C.splitter.xB.1 ≠ C.xBPrime := by
    intro heq
    have hsmallCover :
        (R.map C.oldVertex) ∪ P ⊆
          (R.map C.oldVertex) ∪ {C.xAPrime} := by
      intro q hq
      rcases Finset.mem_union.mp hq with hqR | hqP
      · exact Finset.mem_union_left _ hqR
      · simp only [P, Finset.mem_insert, Finset.mem_singleton] at hqP
        rcases hqP with rfl | rfl
        · exact Finset.mem_union_right _ (by simp)
        · apply Finset.mem_union_left
          rw [← heq]
          exact Finset.mem_map.mpr ⟨C.splitter.xB.1, hxBR, rfl⟩
    have hGXone : C.gxVerts.card ≤ R.card + 1 := by
      calc
        C.gxVerts.card ≤
            ((R.map C.oldVertex) ∪ {C.xAPrime}).card :=
          Finset.card_le_card (hcoverRef.trans hsmallCover)
        _ ≤ (R.map C.oldVertex).card + ({C.xAPrime} : Finset W).card :=
          Finset.card_union_le _ _
        _ = R.card + 1 := by simp
    have hUle' := hUle
    rw [hcardU] at hUle'
    rw [hcardR] at hGXone
    omega
  have hUcard : U.card = Fintype.card V := by
    have hUle' := hUle
    have hGXref' := hGXref
    rw [hcardU] at hUle'
    rw [hcardR] at hGXref'
    omega
  have hUeq : U = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ U)
    simpa [hUcard]
  have hcoverV (q : V) :
      q ∈ A ∨ q ∈ B ∨ q ∈ X ∨ q ∈ Y ∨ q ∈ Z ∨ q = center := by
    have hqU : q ∈ U := by rw [hUeq]; simp
    have hcases :
        q = center ∨ q ∈ A ∨ q ∈ B ∨ q ∈ X ∨ q ∈ Y ∨ q ∈ Z := by
      simpa [U] using hqU
    rcases hcases with h | hA | hB | hX | hY | hZ
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl hA
    · exact Or.inr (Or.inl hB)
    · exact Or.inr (Or.inr (Or.inl hX))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hY)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hZ))))
  obtain ⟨hxByB, hxBzB⟩ := hBeq_of_one hB1
  have hAeq : A = {C.splitter.xA.1, C.splitter.yA.1, C.splitter.zA.1} := by
    simp [A, C.splitter.A_eq, ahtDeletedFinsetVal]
  have hxAyA : C.splitter.xA.1 ≠ C.splitter.yA.1 := by
    intro h
    have hle : A.card ≤ 2 := by
      rw [hAeq]
      simpa [h] using
        (card_pair_le' C.splitter.yA.1 C.splitter.zA.1)
    omega
  have hxAzA : C.splitter.xA.1 ≠ C.splitter.zA.1 := by
    intro h
    have hle : A.card ≤ 2 := by
      rw [hAeq]
      simpa [h] using
        (card_pair_le' C.splitter.yA.1 C.splitter.zA.1)
    omega
  have hyA_mem_A : C.splitter.yA.1 ∈ A := by
    simpa [A] using C.splitter.Y_A_attachment.1
  have hzA_mem_A : C.splitter.zA.1 ∈ A := by
    simpa [A] using C.splitter.Z_A_attachment.1
  have hyA_not_center_adj : ¬G.Adj C.splitter.yA.1 center := by
    intro hadj
    rcases C.center_neighbor_location hadj.symm with h | h | h
    · exact Finset.disjoint_left.mp hABX
        (Finset.mem_union_left B hyA_mem_A)
        (by simpa [X, h] using C.splitter.x_mem_X)
    · exact Finset.disjoint_left.mp hABY
        (Finset.mem_union_left B hyA_mem_A)
        (by simpa [Y, h] using C.splitter.y_mem_Y)
    · exact Finset.disjoint_left.mp hABZ
        (Finset.mem_union_left B hyA_mem_A)
        (by simpa [Z, h] using C.splitter.z_mem_Z)
  have hzA_not_center_adj : ¬G.Adj C.splitter.zA.1 center := by
    intro hadj
    rcases C.center_neighbor_location hadj.symm with h | h | h
    · exact Finset.disjoint_left.mp hABX
        (Finset.mem_union_left B hzA_mem_A)
        (by simpa [X, h] using C.splitter.x_mem_X)
    · exact Finset.disjoint_left.mp hABY
        (Finset.mem_union_left B hzA_mem_A)
        (by simpa [Y, h] using C.splitter.y_mem_Y)
    · exact Finset.disjoint_left.mp hABZ
        (Finset.mem_union_left B hzA_mem_A)
        (by simpa [Z, h] using C.splitter.z_mem_Z)
  have hNyA : G.neighborFinset C.splitter.yA.1 ⊆
      {y.1, C.splitter.xA.1, C.splitter.zA.1} := by
    intro q hq
    have hadj : G.Adj C.splitter.yA.1 q := by simpa using hq
    rcases hcoverV q with hqA | hqB | hqX | hqY | hqZ | rfl
    · have : q = C.splitter.xA.1 ∨ q = C.splitter.yA.1 ∨
          q = C.splitter.zA.1 := by simpa [hAeq] using hqA
      rcases this with rfl | rfl | rfl
      · simp
      · exact False.elim (G.loopless.irrefl _ hadj)
      · simp
    · have hqxB : q = C.splitter.xB.1 :=
        eq_of_mem_of_card_eq_one hqB hxBB hB1
      have hqyB : q = C.splitter.yB.1 := hqxB.trans hxByB
      exact False.elim (htri hyA (hqyB ▸ hadj) hyB.symm)
    · obtain ⟨q', hq'X, hq'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal (by simpa [X] using hqX)
      have hdel : (deleteVertex G center).Adj q' C.splitter.yA :=
        (deleteVertex_adj (G := G)).mpr (by simpa [hq'val] using hadj.symm)
      have heq := C.splitter.X_A_attachment.2.2 q' hq'X
        C.splitter.yA C.splitter.Y_A_attachment.1 hdel
      exact False.elim (hxAyA (congrArg Subtype.val heq).symm)
    · have hqy : q = y.1 := by simpa [hYset] using hqY
      simpa [hqy]
    · obtain ⟨q', hq'Z, hq'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal (by simpa [Z] using hqZ)
      have hdel : (deleteVertex G center).Adj q' C.splitter.yA :=
        (deleteVertex_adj (G := G)).mpr (by simpa [hq'val] using hadj.symm)
      have heq := C.splitter.Z_A_attachment.2.2 q' hq'Z
        C.splitter.yA C.splitter.Y_A_attachment.1 hdel
      exact False.elim (hyAzA (congrArg Subtype.val heq))
    · exact False.elim (hyA_not_center_adj hadj)
  have hNzA : G.neighborFinset C.splitter.zA.1 ⊆
      {z.1, C.splitter.xA.1, C.splitter.yA.1} := by
    intro q hq
    have hadj : G.Adj C.splitter.zA.1 q := by simpa using hq
    rcases hcoverV q with hqA | hqB | hqX | hqY | hqZ | rfl
    · have : q = C.splitter.xA.1 ∨ q = C.splitter.yA.1 ∨
          q = C.splitter.zA.1 := by simpa [hAeq] using hqA
      rcases this with rfl | rfl | rfl
      · simp
      · simp
      · exact False.elim (G.loopless.irrefl _ hadj)
    · have hqxB : q = C.splitter.xB.1 :=
        eq_of_mem_of_card_eq_one hqB hxBB hB1
      have hqzB : q = C.splitter.zB.1 := hqxB.trans hxBzB
      exact False.elim (htri hzA (hqzB ▸ hadj) hzB.symm)
    · obtain ⟨q', hq'X, hq'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal (by simpa [X] using hqX)
      have hdel : (deleteVertex G center).Adj q' C.splitter.zA :=
        (deleteVertex_adj (G := G)).mpr (by simpa [hq'val] using hadj.symm)
      have heq := C.splitter.X_A_attachment.2.2 q' hq'X
        C.splitter.zA C.splitter.Z_A_attachment.1 hdel
      exact False.elim (hxAzA (congrArg Subtype.val heq).symm)
    · obtain ⟨q', hq'Y, hq'val⟩ :=
        exists_subtype_of_mem_ahtDeletedFinsetVal (by simpa [Y] using hqY)
      have hdel : (deleteVertex G center).Adj q' C.splitter.zA :=
        (deleteVertex_adj (G := G)).mpr (by simpa [hq'val] using hadj.symm)
      have heq := C.splitter.Y_A_attachment.2.2 q' hq'Y
        C.splitter.zA C.splitter.Z_A_attachment.1 hdel
      exact False.elim (hyAzA (congrArg Subtype.val heq).symm)
    · have hqz : q = z.1 := by simpa [hZset] using hqZ
      simpa [hqz]
    · exact False.elim (hzA_not_center_adj hadj)
  by_cases hyAzAedge : G.Adj C.splitter.yA.1 C.splitter.zA.1
  · by_cases hyAxAedge : G.Adj C.splitter.yA.1 C.splitter.xA.1
    · have hzAxAedge : ¬G.Adj C.splitter.zA.1 C.splitter.xA.1 := by
        intro h
        exact htri hyAzAedge h hyAxAedge.symm
      have hsub : G.neighborFinset C.splitter.zA.1 ⊆
          {z.1, C.splitter.yA.1} := by
        intro q hq
        have hadj : G.Adj C.splitter.zA.1 q := by simpa using hq
        have hmem := hNzA hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
        rcases hmem with h | h | h
        · exact Or.inl h
        · exact False.elim (hzAxAedge (by simpa [h] using hadj))
        · exact Or.inr h
      have hle := degree_le_two_of_neighborFinset_subset_pair hsub
      have hge := hmin C.splitter.zA.1
      omega
    · have hsub : G.neighborFinset C.splitter.yA.1 ⊆
          {y.1, C.splitter.zA.1} := by
        intro q hq
        have hadj : G.Adj C.splitter.yA.1 q := by simpa using hq
        have hmem := hNyA hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
        rcases hmem with h | h | h
        · exact Or.inl h
        · exact False.elim (hyAxAedge (by simpa [h] using hadj))
        · exact Or.inr h
      have hle := degree_le_two_of_neighborFinset_subset_pair hsub
      have hge := hmin C.splitter.yA.1
      omega
  · have hsub : G.neighborFinset C.splitter.yA.1 ⊆
        {y.1, C.splitter.xA.1} := by
      intro q hq
      have hadj : G.Adj C.splitter.yA.1 q := by simpa using hq
      have hmem := hNyA hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hyAzAedge (by simpa [h] using hadj))
    have hle := degree_le_two_of_neighborFinset_subset_pair hsub
    have hge := hmin C.splitter.yA.1
    omega

/-- The concrete replacement graph has the same strictly smaller vertex
count as its defining vertex finset. -/
theorem gx_card_lt
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G) :
    Fintype.card C.GXVertex < Fintype.card V := by
  simpa [GXVertex] using C.gxVerts_card_lt hthree halmost

end AHTClaim3CardinalityCertificateDeleted

end Erdos916
