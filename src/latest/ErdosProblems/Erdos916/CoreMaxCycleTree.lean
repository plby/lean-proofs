/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.BridgeTwo

/-!
# The tree-bridge branch of the maximum-cycle analysis

This module records all of the data carried by an end vertex of an acyclic
complementary bridge.  In the wheel-free minimum-degree-three branch, an end
vertex has one neighbour in the bridge and two on the rim, and hence ambient
degree exactly three.  Keeping the unique bridge neighbour explicit is the
input needed by the remaining Thomassen--Toft `N6` path surgery.

The two-vertex bridge is deliberately not folded into that surgery.  In that
case the two bridge vertices are adjacent and therefore cannot be false twins
(the `K_{3,3}` terminal configuration is the basic example); it is handled by
`BridgeTwo`.
-/

namespace Erdos916

open SimpleGraph
open Erdos751.BV

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The exact local data at a leaf of the tree induced by the complementary
bridge.  The last equality is stronger than a cardinality statement: it names
the leaf's unique neighbour in the bridge. -/
structure BridgeLeafData (M : MaxCycleCertificate G) where
  vertex : V
  parent : V
  vertex_mem : vertex ∈ bridgeSet G M.cycle M.bridge
  parent_mem : parent ∈ bridgeSet G M.cycle M.bridge
  vertex_ne_parent : vertex ≠ parent
  adj_parent : G.Adj vertex parent
  bridge_degree_eq_one :
    (G.induce (bridgeSet G M.cycle M.bridge)).degree
      ⟨vertex, vertex_mem⟩ = 1
  bridge_neighbors :
    G.neighborFinset vertex \ M.cycle.verts (G := G) = {parent}
  degree_eq_three : G.degree vertex = 3
  cycle_neighbors_card :
    (G.neighborFinset vertex ∩ M.cycle.verts (G := G)).card = 2

namespace BridgeLeafData

variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {M : MaxCycleCertificate G}

/-- A named enumeration of the two rim attachments of a bridge leaf. -/
structure AttachmentPair (L : BridgeLeafData G M) where
  first : V
  second : V
  ne : first ≠ second
  neighbors_eq :
    G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) = {first, second}

namespace AttachmentPair

theorem first_adj (A : AttachmentPair (G := G) (M := M) L) :
    G.Adj L.vertex A.first := by
  have : A.first ∈
      G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) := by
    rw [A.neighbors_eq]
    simp
  simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp this).1

theorem second_adj (A : AttachmentPair (G := G) (M := M) L) :
    G.Adj L.vertex A.second := by
  have : A.second ∈
      G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) := by
    rw [A.neighbors_eq]
    simp
  simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp this).1

theorem first_mem_cycle (A : AttachmentPair (G := G) (M := M) L) :
    A.first ∈ M.cycle.vSet (G := G) := by
  apply M.cycle.mem_vSet_iff.mpr
  have : A.first ∈
      G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) := by
    rw [A.neighbors_eq]
    simp
  exact (Finset.mem_inter.mp this).2

theorem second_mem_cycle (A : AttachmentPair (G := G) (M := M) L) :
    A.second ∈ M.cycle.vSet (G := G) := by
  apply M.cycle.mem_vSet_iff.mpr
  have : A.second ∈
      G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) := by
    rw [A.neighbors_eq]
    simp
  exact (Finset.mem_inter.mp this).2

theorem vertex_ne_first (A : AttachmentPair (G := G) (M := M) L) :
    L.vertex ≠ A.first := A.first_adj.ne

theorem vertex_ne_second (A : AttachmentPair (G := G) (M := M) L) :
    L.vertex ≠ A.second := A.second_adj.ne

theorem parent_ne_first (A : AttachmentPair (G := G) (M := M) L) :
    L.parent ≠ A.first := by
  intro h
  have hpout := (M.mem_bridge_iff_not_mem_cycle G L.parent).mp L.parent_mem
  exact hpout (h ▸ A.first_mem_cycle)

theorem parent_ne_second (A : AttachmentPair (G := G) (M := M) L) :
    L.parent ≠ A.second := by
  intro h
  have hpout := (M.mem_bridge_iff_not_mem_cycle G L.parent).mp L.parent_mem
  exact hpout (h ▸ A.second_mem_cycle)

end AttachmentPair

/-- Every bridge leaf admits a named pair of its two rim attachments. -/
theorem exists_attachmentPair (L : BridgeLeafData G M) :
    Nonempty (AttachmentPair L) := by
  obtain ⟨a, b, hab, hpair⟩ :=
    Finset.card_eq_two.mp L.cycle_neighbors_card
  exact ⟨⟨a, b, hab, hpair⟩⟩

/-- Deleting a named leaf leaves the induced bridge connected.  This is the
clean subtype form consumed by the leaf-rerouting target comparison. -/
theorem bridge_delete_connected (L : BridgeLeafData G M) :
    ((G.induce (bridgeSet G M.cycle M.bridge)).induce
      ({(⟨L.vertex, L.vertex_mem⟩ :
        bridgeSet G M.cycle M.bridge)} :
        Set (bridgeSet G M.cycle M.bridge))ᶜ).Connected := by
  apply (M.bridge_connected G).induce_compl_singleton_of_degree_eq_one
  exact L.bridge_degree_eq_one

/-- Ambient-subtype form of `bridge_delete_connected`: the graph induced by
the bridge carrier with the leaf removed is connected. -/
theorem bridge_sdiff_connected (L : BridgeLeafData G M) :
    (G.induce (bridgeSet G M.cycle M.bridge \ {L.vertex})).Connected := by
  let B : Set V := bridgeSet G M.cycle M.bridge
  let xB : B := ⟨L.vertex, by simpa only [B] using L.vertex_mem⟩
  let e :
      (bridgeSet G M.cycle M.bridge \ {L.vertex}) ≃
        ↥(({xB} : Set B)ᶜ) :=
    { toFun := fun v ↦
        ⟨⟨v.1, v.2.1⟩, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          exact v.2.2 (congrArg Subtype.val h)⟩
      invFun := fun v ↦
        ⟨v.1.1, v.1.2, by
          simp only [Set.mem_singleton_iff]
          intro h
          apply v.2
          apply Subtype.ext
          exact h⟩
      left_inv := by intro v; apply Subtype.ext; rfl
      right_inv := by intro v; apply Subtype.ext; apply Subtype.ext; rfl }
  let iso :
      G.induce (bridgeSet G M.cycle M.bridge \ {L.vertex}) ≃g
        (G.induce B).induce (({xB} : Set B)ᶜ) :=
    { toEquiv := e
      map_rel_iff' := by intro _ _; rfl }
  apply iso.connected_iff.mpr
  simpa only [B, xB] using L.bridge_delete_connected

/-- The unique parent survives deletion of the leaf. -/
theorem parent_mem_bridge_sdiff (L : BridgeLeafData G M) :
    L.parent ∈ bridgeSet G M.cycle M.bridge \ {L.vertex} := by
  exact ⟨L.parent_mem, by simpa only [Set.mem_singleton_iff] using
    L.vertex_ne_parent.symm⟩

/-- Any bridge vertex different from the leaf, in particular a distinguished
root, survives in the connected graph after leaf deletion. -/
theorem mem_bridge_sdiff_of_ne (L : BridgeLeafData G M) {x₀ : V}
    (hx₀B : x₀ ∈ bridgeSet G M.cycle M.bridge)
    (hx₀ : x₀ ≠ L.vertex) :
    x₀ ∈ bridgeSet G M.cycle M.bridge \ {L.vertex} := by
  exact ⟨hx₀B, by simpa only [Set.mem_singleton_iff] using hx₀⟩

/-- A named bridge leaf has no second neighbour in the bridge. -/
theorem eq_parent_of_mem_bridge_of_adj (L : BridgeLeafData G M) {z : V}
    (hzB : z ∈ bridgeSet G M.cycle M.bridge)
    (hz : G.Adj L.vertex z) : z = L.parent := by
  have hzC : z ∉ M.cycle.vSet (G := G) :=
    (M.mem_bridge_iff_not_mem_cycle G z).mp hzB
  have hzOff : z ∈ G.neighborFinset L.vertex \ M.cycle.verts (G := G) := by
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simpa only [SimpleGraph.mem_neighborFinset] using hz
    · simpa only [M.cycle.mem_vSet_iff] using hzC
  rw [L.bridge_neighbors] at hzOff
  simpa only [Finset.mem_singleton] using hzOff

/-- The complete ambient neighbourhood of a bridge leaf is its two rim
neighbours together with its named parent. -/
theorem neighborFinset_eq_cycle_union_parent (L : BridgeLeafData G M) :
    G.neighborFinset L.vertex =
      (G.neighborFinset L.vertex ∩ M.cycle.verts (G := G)) ∪ {L.parent} := by
  calc
    G.neighborFinset L.vertex =
        (G.neighborFinset L.vertex ∩ M.cycle.verts (G := G)) ∪
          (G.neighborFinset L.vertex \ M.cycle.verts (G := G)) :=
      M.neighborFinset_eq_cycle_union_bridge G L.vertex
    _ = (G.neighborFinset L.vertex ∩ M.cycle.verts (G := G)) ∪
          {L.parent} := congrArg
      (fun S : Finset V ↦
        (G.neighborFinset L.vertex ∩ M.cycle.verts (G := G)) ∪ S)
      L.bridge_neighbors

/-- Two displayed leaves with the same parent and the same rim-attachment
set are false twins. -/
theorem areFalseTwins_of_same_parent_and_cycle_neighbors
    (L K : BridgeLeafData G M) (hvertex : L.vertex ≠ K.vertex)
    (hparent : L.parent = K.parent)
    (hcycle :
      G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) =
        G.neighborFinset K.vertex ∩ M.cycle.verts (G := G)) :
    AreFalseTwins G L.vertex K.vertex := by
  refine ⟨hvertex, ?_⟩
  have hfin : G.neighborFinset L.vertex = G.neighborFinset K.vertex := by
    rw [L.neighborFinset_eq_cycle_union_parent,
      K.neighborFinset_eq_cycle_union_parent, hparent, hcycle]
  ext z
  simpa only [SimpleGraph.mem_neighborSet, ← SimpleGraph.mem_neighborFinset]
    using Finset.ext_iff.mp hfin z

/-- The exact unresolved split for two tree leaves: either they are already
false twins, or their named parents or their two rim-attachment sets differ.
The latter two alternatives are precisely the hypotheses used in the `N6`
cycle-exchange surgery. -/
theorem falseTwins_or_parent_ne_or_cycle_neighbors_ne
    (L K : BridgeLeafData G M) (hvertex : L.vertex ≠ K.vertex) :
    AreFalseTwins G L.vertex K.vertex ∨
      L.parent ≠ K.parent ∨
      G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) ≠
        G.neighborFinset K.vertex ∩ M.cycle.verts (G := G) := by
  by_cases hp : L.parent = K.parent
  · by_cases hC :
        G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) =
          G.neighborFinset K.vertex ∩ M.cycle.verts (G := G)
    · exact Or.inl (L.areFalseTwins_of_same_parent_and_cycle_neighbors
        K hvertex hp hC)
    · exact Or.inr (Or.inr hC)
  · exact Or.inr (Or.inl hp)

end BridgeLeafData

/-- Two distinct leaves extracted from an acyclic complementary bridge. -/
structure TwoBridgeLeafData (M : MaxCycleCertificate G) where
  left : BridgeLeafData G M
  right : BridgeLeafData G M
  ne : left.vertex ≠ right.vertex

namespace TwoBridgeLeafData

variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {M : MaxCycleCertificate G}

/-- Of two distinct bridge leaves, at least one avoids any prescribed root. -/
theorem left_ne_or_right_ne (D : TwoBridgeLeafData G M) (x₀ : V) :
    D.left.vertex ≠ x₀ ∨ D.right.vertex ≠ x₀ := by
  by_contra h
  push Not at h
  exact D.ne (h.1.trans h.2.symm)

/-- Package an actual leaf avoiding a prescribed root, retaining which side
of the two-leaf certificate it came from. -/
theorem exists_leaf_ne (D : TwoBridgeLeafData G M) (x₀ : V) :
    ∃ L : BridgeLeafData G M,
      (L = D.left ∨ L = D.right) ∧ L.vertex ≠ x₀ := by
  rcases D.left_ne_or_right_ne x₀ with hleft | hright
  · exact ⟨D.left, Or.inl rfl, hleft⟩
  · exact ⟨D.right, Or.inr rfl, hright⟩

end TwoBridgeLeafData

namespace MaxCycleCertificate

variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (M : MaxCycleCertificate G)

/-- In a connected bridge with at least three vertices, two distinct bridge
leaves cannot be adjacent.  If they were, deleting one leaf would leave the
other isolated, contradicting connectedness of deletion of a degree-one
vertex.  This isolates the precise reason the two-vertex bridge is a separate
terminal case. -/
theorem BridgeLeafData.not_adj_of_three_le_bridge
    (L K : BridgeLeafData G M) (hne : L.vertex ≠ K.vertex)
    (hcard : 3 ≤ (bridgeSet G M.cycle M.bridge).ncard) :
    ¬G.Adj L.vertex K.vertex := by
  classical
  intro hLK
  let B : Set V := bridgeSet G M.cycle M.bridge
  let xB : B := ⟨L.vertex, by simpa only [B] using L.vertex_mem⟩
  let yB : B := ⟨K.vertex, by simpa only [B] using K.vertex_mem⟩
  have hxyB : xB ≠ yB := by
    intro h
    exact hne (congrArg Subtype.val h)
  have hxdeg : (G.induce B).degree xB = 1 := by
    simpa only [B, xB] using L.bridge_degree_eq_one
  have hconn : (G.induce B).Connected := by
    simpa only [B] using M.bridge_connected G
  have hdelete : ((G.induce B).induce ({xB} : Set B)ᶜ).Connected :=
    hconn.induce_compl_singleton_of_degree_eq_one hxdeg
  have hBcard : B.toFinset.card ≥ 3 := by
    rw [Set.toFinset_card, Set.fintypeCard_eq_ncard]
    simpa only [B] using hcard
  have hpaircard : ({L.vertex, K.vertex} : Finset V).card = 2 := by
    simp [hne]
  have hpairlt : ({L.vertex, K.vertex} : Finset V).card < B.toFinset.card := by
    omega
  obtain ⟨z, hzBfin, hzpair⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hpairlt
  have hzB : z ∈ B := Set.mem_toFinset.mp hzBfin
  have hzx : z ≠ L.vertex := by
    intro h
    apply hzpair
    simp [h]
  have hzy : z ≠ K.vertex := by
    intro h
    apply hzpair
    simp [h]
  let zB : B := ⟨z, hzB⟩
  have hzxB : zB ≠ xB := by
    intro h
    exact hzx (congrArg Subtype.val h)
  have hzyB : zB ≠ yB := by
    intro h
    exact hzy (congrArg Subtype.val h)
  let yD : ↥(({xB} : Set B)ᶜ) := ⟨yB, by simpa [hxyB.symm]⟩
  let zD : ↥(({xB} : Set B)ᶜ) := ⟨zB, by simpa [hzxB]⟩
  have hyzD : yD ≠ zD := by
    intro h
    exact hzyB (congrArg Subtype.val h).symm
  letI : Nontrivial ↥(({xB} : Set B)ᶜ) := ⟨⟨yD, zD, hyzD⟩⟩
  have hKparent : K.parent = L.vertex :=
    (K.eq_parent_of_mem_bridge_of_adj L.vertex_mem hLK.symm).symm
  have hyisolated :
      ((G.induce B).induce ({xB} : Set B)ᶜ).IsIsolated yD := by
    intro w hyw
    have hywG : G.Adj K.vertex w.1.1 := by
      exact hyw
    have hwB : w.1.1 ∈ bridgeSet G M.cycle M.bridge := by
      simpa only [B] using w.1.2
    have hwp : w.1.1 = K.parent :=
      K.eq_parent_of_mem_bridge_of_adj hwB hywG
    have hwx : w.1 = xB := by
      apply Subtype.ext
      exact hwp.trans hKparent
    exact w.2 (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
      using hwx)
  have hyzero :
      ((G.induce B).induce ({xB} : Set B)ᶜ).degree yD = 0 :=
    (((G.induce B).induce ({xB} : Set B)ᶜ).degree_eq_zero yD).mpr
      hyisolated
  have hypos :
      0 < ((G.induce B).induce ({xB} : Set B)ᶜ).degree yD :=
    hdelete.preconnected.degree_pos_of_nontrivial yD
  omega

/-- A leaf of the induced bridge tree carries `BridgeLeafData`. -/
theorem bridgeLeafData_of_degree_eq_one
    (hno : ¬HasWheelWitness G) (hmin : ∀ v : V, 3 ≤ G.degree v)
    {z : V} (hzB : z ∈ bridgeSet G M.cycle M.bridge)
    (hzleaf : (G.induce
      (bridgeSet G M.cycle M.bridge)).degree ⟨z, hzB⟩ = 1) :
    ∃ L : BridgeLeafData G M, L.vertex = z := by
  classical
  let B : Set V := bridgeSet G M.cycle M.bridge
  let zB : B := ⟨z, by simpa only [B] using hzB⟩
  have hzleaf' : (G.induce B).degree zB = 1 := by
    simpa only [B, zB] using hzleaf
  obtain ⟨pB, hzp, hpuniq⟩ :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hzleaf'
  let p : V := pB.1
  have hpB : p ∈ bridgeSet G M.cycle M.bridge := by
    simpa only [p, B] using pB.2
  have hzpG : G.Adj z p := by
    exact hzp
  have hzne : z ≠ p := hzpG.ne
  have hoff :
      G.neighborFinset z \ M.cycle.verts (G := G) = {p} := by
    ext w
    constructor
    · intro hw
      have hw' := Finset.mem_sdiff.mp hw
      have hwB : w ∈ B := by
        change w ∈ bridgeSet G M.cycle M.bridge
        apply (M.mem_bridge_iff_not_mem_cycle G w).mpr
        simpa only [M.cycle.mem_vSet_iff] using hw'.2
      let wB : B := ⟨w, hwB⟩
      have hzwB : (G.induce B).Adj zB wB := by
        exact (show G.Adj z w by
          simpa only [SimpleGraph.mem_neighborFinset] using hw'.1)
      have hwpB : wB = pB := hpuniq wB hzwB
      have hwp : w = p := congrArg Subtype.val hwpB
      simpa only [Finset.mem_singleton] using hwp
    · intro hw
      have hwp : w = p := by simpa only [Finset.mem_singleton] using hw
      subst w
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · simpa only [SimpleGraph.mem_neighborFinset] using hzpG
      · have hpout : p ∉ M.cycle.vSet (G := G) :=
          (M.mem_bridge_iff_not_mem_cycle G p).mp hpB
        simpa only [M.cycle.mem_vSet_iff] using hpout
  have hcycleLe :
      (G.neighborFinset z ∩ M.cycle.verts (G := G)).card ≤ 2 :=
    M.card_neighbors_on_cycle_le_two_of_noWheel G hno hzB
  have hsplit := Finset.card_sdiff_add_card_inter
    (G.neighborFinset z) (M.cycle.verts (G := G))
  have hoffcard :
      (G.neighborFinset z \ M.cycle.verts (G := G)).card = 1 := by
    rw [hoff]
    simp
  rw [hoffcard, G.card_neighborFinset_eq_degree] at hsplit
  have hzmin := hmin z
  have hzdeg : G.degree z = 3 := by omega
  have hzcycle :
      (G.neighborFinset z ∩ M.cycle.verts (G := G)).card = 2 := by
    omega
  refine ⟨
    { vertex := z
      parent := p
      vertex_mem := hzB
      parent_mem := hpB
      vertex_ne_parent := hzne
      adj_parent := hzpG
      bridge_degree_eq_one := by simpa only [B, zB] using hzleaf'
      bridge_neighbors := hoff
      degree_eq_three := hzdeg
      cycle_neighbors_card := hzcycle }, rfl⟩

/-- Strong form of the two-leaf theorem.  Unlike the earlier cardinality-only
version, this exposes each leaf's unique parent and its full neighbourhood
decomposition. -/
theorem exists_twoBridgeLeafData_of_bridge_isAcyclic
    (hno : ¬HasWheelWitness G) (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hcard : 2 ≤ (bridgeSet G M.cycle M.bridge).ncard)
    (hacyc : (G.induce
      (bridgeSet G M.cycle M.bridge)).IsAcyclic) :
    Nonempty (TwoBridgeLeafData G M) := by
  classical
  let B : Set V := bridgeSet G M.cycle M.bridge
  have hcardType : 2 ≤ Fintype.card B := by
    rw [Set.fintypeCard_eq_ncard]
    simpa only [B] using hcard
  letI : Nontrivial B := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have htree : (G.induce B).IsTree := by
    refine ⟨?_, ?_⟩
    · simpa only [B] using M.bridge_connected G
    · simpa only [B] using hacyc
  obtain ⟨x, y, hxy, hxleaf, hyleaf⟩ :=
    htree.exists_ne_and_degree_eq_one
  obtain ⟨L, hLvertex⟩ := M.bridgeLeafData_of_degree_eq_one hno hmin x.2
    (by simpa only [B] using hxleaf)
  obtain ⟨K, hKvertex⟩ := M.bridgeLeafData_of_degree_eq_one hno hmin y.2
    (by simpa only [B] using hyleaf)
  refine ⟨⟨L, K, ?_⟩⟩
  rw [hLvertex, hKvertex]
  intro h
  exact hxy (Subtype.ext h)

/-- Unconditional algebraic split at the two leaves of an acyclic bridge.
Only the two unequal-data cases remain for the Thomassen--Toft path surgery. -/
theorem exists_falseTwins_or_differing_two_bridge_leaves
    (hno : ¬HasWheelWitness G) (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hcard : 2 ≤ (bridgeSet G M.cycle M.bridge).ncard)
    (hacyc : (G.induce
      (bridgeSet G M.cycle M.bridge)).IsAcyclic) :
    (∃ x y : V, AreFalseTwins G x y ∧ G.degree x = 3) ∨
      ∃ L K : BridgeLeafData G M, L.vertex ≠ K.vertex ∧
        (L.parent ≠ K.parent ∨
          G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) ≠
            G.neighborFinset K.vertex ∩ M.cycle.verts (G := G)) := by
  obtain ⟨D⟩ := M.exists_twoBridgeLeafData_of_bridge_isAcyclic
    hno hmin hcard hacyc
  rcases D.left.falseTwins_or_parent_ne_or_cycle_neighbors_ne
      D.right D.ne with htwins | hdiff
  · exact Or.inl ⟨D.left.vertex, D.right.vertex, htwins,
      D.left.degree_eq_three⟩
  · exact Or.inr ⟨D.left, D.right, D.ne, hdiff⟩

/-- The exceptional two-vertex tree bridge nevertheless has the requested
wheel-or-false-twin output.  `BridgeTwo` first produces the exact induced
`K_{2,3}` reduction; its size-two part is a degree-three false-twin pair. -/
theorem wheel_or_falseTwins_of_bridge_ncard_eq_two
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hBcard : (bridgeSet G M.cycle M.bridge).ncard = 2) :
    HasWheelWitness G ∨
      ∃ x y : V, AreFalseTwins G x y ∧ G.degree x = 3 := by
  rcases M.wheel_or_reduction_of_bridge_ncard_eq_two hmin hBcard with
    hW | hR
  · exact Or.inl hW
  · obtain ⟨R⟩ := hR
    obtain ⟨x, y, hxy, hxdeg, -⟩ := hasRichFalseTwins_of_k23Reduction R
    exact Or.inr ⟨x, y, hxy, hxdeg⟩

/-- Strongest unconditional reduction currently available for an acyclic
complementary bridge.  The two-vertex terminal is completely discharged.
For a larger tree, the remaining leaves are nonadjacent and differ either in
their parent or in their two rim attachments; this is the exact input to the
published bridge-endblock path surgery. -/
theorem wheel_or_falseTwins_or_differing_nonadjacent_tree_leaves
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hacyc : (G.induce
      (bridgeSet G M.cycle M.bridge)).IsAcyclic) :
    HasWheelWitness G ∨
      (∃ x y : V, AreFalseTwins G x y ∧ G.degree x = 3) ∨
      ∃ L K : BridgeLeafData G M, L.vertex ≠ K.vertex ∧
        ¬G.Adj L.vertex K.vertex ∧
        (L.parent ≠ K.parent ∨
          G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) ≠
            G.neighborFinset K.vertex ∩ M.cycle.verts (G := G)) := by
  by_cases hW : HasWheelWitness G
  · exact Or.inl hW
  right
  have htwo := M.two_le_ncard_bridge_of_noWheel G hW hmin
  by_cases heq : (bridgeSet G M.cycle M.bridge).ncard = 2
  · rcases M.wheel_or_falseTwins_of_bridge_ncard_eq_two hmin heq with
      hW' | htwins
    · exact False.elim (hW hW')
    · exact Or.inl htwins
  · have hthree : 3 ≤ (bridgeSet G M.cycle M.bridge).ncard := by omega
    rcases M.exists_falseTwins_or_differing_two_bridge_leaves
        hW hmin htwo hacyc with htwins | ⟨L, K, hne, hdiff⟩
    · exact Or.inl htwins
    · exact Or.inr ⟨L, K, hne,
        MaxCycleCertificate.BridgeLeafData.not_adj_of_three_le_bridge
          M L K hne hthree, hdiff⟩

end MaxCycleCertificate

end Erdos916
