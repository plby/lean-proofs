/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSection7
import ErdosProblems.Erdos916.AHTConnectivity
import ErdosProblems.Erdos916.AHTSourceLemma62
import ErdosProblems.Erdos916.AHTSourceLemma63
import ErdosProblems.Erdos916.AHTSourceLemma64
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# The two-separation step in AHT Section 7

This file supplies the finite two-cut bookkeeping left after the cut-vertex
reduction in `AHTSection7`.  A component of `G - {a,b}`, together with the two
attachment vertices, is an end set.  Interior vertices have no ambient
neighbours outside that set, so false twins and their degrees lift from the
virtual-edge torso.

The last part isolates the source's only exceptional boundary configuration.
Two disjoint false-twin pairs either contain a pair wholly in the interior, or
the pairs cross the two attachment vertices.  If the torso is `K₃,₃`, the
crossing case is resolved unconditionally by choosing two vertices in one
bipartition class away from both attachments.
-/

attribute [local instance] Classical.propDecidable

namespace Erdos916

open _root_.SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace AHTSection7TwoSeparation

/-- A component end determined by deleting two distinct attachment vertices.
`proper` records that the deleted graph has another component. -/
structure TwoCutEnd (G : SimpleGraph V) [DecidableRel G.Adj] where
  a : V
  b : V
  boundary_ne : a ≠ b
  component :
    (G.induce (fun w : V ↦ w ≠ a ∧ w ≠ b)).ConnectedComponent
  proper : ∃ z, z ∉ component.supp

namespace TwoCutEnd

variable (E : TwoCutEnd G)

/-- The ambient vertices belonging to the selected component of
`G - {a,b}`. -/
def side : Set V :=
  {v | ∃ (hva : v ≠ E.a) (hvb : v ≠ E.b),
    (⟨v, hva, hvb⟩ : {w : V // w ≠ E.a ∧ w ≠ E.b}) ∈ E.component.supp}

/-- Put both attachment vertices back into the selected component. -/
def verts : Set V := insert E.a (insert E.b E.side)

@[simp] theorem mem_side_iff {v : V} :
    v ∈ E.side ↔
      ∃ (hva : v ≠ E.a) (hvb : v ≠ E.b),
        (⟨v, hva, hvb⟩ : {w : V // w ≠ E.a ∧ w ≠ E.b}) ∈
          E.component.supp :=
  Iff.rfl

@[simp] theorem left_not_mem_side : E.a ∉ E.side := by
  rintro ⟨ha, -, -⟩
  exact ha rfl

@[simp] theorem right_not_mem_side : E.b ∉ E.side := by
  rintro ⟨-, hb, -⟩
  exact hb rfl

theorem side_nonempty : E.side.Nonempty := by
  obtain ⟨⟨v, hva, hvb⟩, hv⟩ := E.component.nonempty_supp
  exact ⟨v, hva, hvb, hv⟩

@[simp] theorem left_mem_verts : E.a ∈ E.verts := by
  simp [verts]

@[simp] theorem right_mem_verts : E.b ∈ E.verts := by
  simp [verts]

/-- Swapping the two deleted boundary vertices gives an isomorphic deleted
graph; the map only exchanges the two proof components of its subtype. -/
def swapDeletedEquiv :
    {w : V // w ≠ E.a ∧ w ≠ E.b} ≃ {w : V // w ≠ E.b ∧ w ≠ E.a} where
  toFun w := ⟨w.1, w.2.2, w.2.1⟩
  invFun w := ⟨w.1, w.2.2, w.2.1⟩
  left_inv w := Subtype.ext rfl
  right_inv w := Subtype.ext rfl

def swapDeletedIso :
    G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b) ≃g
      G.induce (fun w : V ↦ w ≠ E.b ∧ w ≠ E.a) where
  toEquiv := E.swapDeletedEquiv
  map_rel_iff' := by intro _ _; rfl

/-- The same component end with its two attachment labels exchanged. -/
def swap : TwoCutEnd G where
  a := E.b
  b := E.a
  boundary_ne := E.boundary_ne.symm
  component := E.component.map E.swapDeletedIso
  proper := by
    obtain ⟨z, hz⟩ := E.proper
    refine ⟨E.swapDeletedIso z, ?_⟩
    intro hz'
    apply hz
    exact ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mp hz'

@[simp] theorem swap_left : E.swap.a = E.b := rfl

@[simp] theorem swap_right : E.swap.b = E.a := rfl

/-- Boundary swapping changes neither the selected ambient component side
nor its underlying vertices. -/
theorem swap_side : E.swap.side = E.side := by
  ext v
  constructor
  · rintro ⟨hvb, hva, hv⟩
    refine ⟨hva, hvb, ?_⟩
    change (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk
      ⟨v, hva, hvb⟩ = E.component
    apply (ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
      (φ := E.swapDeletedIso) (C := E.component)
      (v := (⟨v, hva, hvb⟩ : {w : V // w ≠ E.a ∧ w ≠ E.b}))).mp
    change (G.induce (fun w : V ↦ w ≠ E.b ∧ w ≠ E.a)).connectedComponentMk
      ⟨v, hvb, hva⟩ = E.component.map E.swapDeletedIso at hv
    have heq : E.swapDeletedIso
        (⟨v, hva, hvb⟩ : {w : V // w ≠ E.a ∧ w ≠ E.b}) =
          (⟨v, hvb, hva⟩ : {w : V // w ≠ E.b ∧ w ≠ E.a}) :=
      Subtype.ext rfl
    rw [heq]
    exact hv
  · rintro ⟨hva, hvb, hv⟩
    refine ⟨hvb, hva, ?_⟩
    change (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk
      ⟨v, hva, hvb⟩ = E.component at hv
    change (G.induce (fun w : V ↦ w ≠ E.b ∧ w ≠ E.a)).connectedComponentMk
      ⟨v, hvb, hva⟩ = E.component.map E.swapDeletedIso
    have hmap := (ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
      (φ := E.swapDeletedIso) (C := E.component)
      (v := (⟨v, hva, hvb⟩ : {w : V // w ≠ E.a ∧ w ≠ E.b}))).mpr hv
    have heq : E.swapDeletedIso
        (⟨v, hva, hvb⟩ : {w : V // w ≠ E.a ∧ w ≠ E.b}) =
          (⟨v, hvb, hva⟩ : {w : V // w ≠ E.b ∧ w ≠ E.a}) :=
      Subtype.ext rfl
    rw [heq] at hmap
    exact hmap

theorem swap_verts : E.swap.verts = E.verts := by
  rw [verts, verts, E.swap_side]
  exact Set.insert_comm E.b E.a E.side

/-- No edge from the selected component can leave the end set except through
one of the two attachment vertices. -/
theorem neighborSet_subset_verts {v : V} (hv : v ∈ E.side) :
    G.neighborSet v ⊆ E.verts := by
  intro w hvw
  by_cases hwa : w = E.a
  · simp [verts, hwa]
  by_cases hwb : w = E.b
  · simp [verts, hwb]
  obtain ⟨hva, hvb, hvK⟩ := hv
  have hadj :
      (G.induce (fun z : V ↦ z ≠ E.a ∧ z ≠ E.b)).Adj
        ⟨v, hva, hvb⟩ ⟨w, hwa, hwb⟩ := hvw
  have hwK :
      (⟨w, hwa, hwb⟩ : {z : V // z ≠ E.a ∧ z ≠ E.b}) ∈
        E.component.supp :=
    E.component.mem_supp_of_adj_mem_supp hvK hadj
  exact Set.mem_insert_iff.mpr <| Or.inr <|
    Set.mem_insert_iff.mpr <| Or.inr ⟨hwa, hwb, hwK⟩

/-- Membership in the end set away from both attachments is exactly
membership in the component side. -/
theorem mem_side_of_mem_verts {v : V} (hv : v ∈ E.verts)
    (hva : v ≠ E.a) (hvb : v ≠ E.b) : v ∈ E.side := by
  simpa [verts, hva, hvb] using hv

/-- A two-cut component end omits an ambient vertex. -/
theorem verts_ne_univ : E.verts ≠ Set.univ := by
  obtain ⟨z, hz⟩ := E.proper
  intro hall
  have hzv : z.1 ∈ E.verts := by rw [hall]; exact Set.mem_univ _
  have hzside : z.1 ∈ E.side :=
    E.mem_side_of_mem_verts hzv z.2.1 z.2.2
  rcases hzside with ⟨hza, hzb, hzK⟩
  exact hz (by simpa only [Subtype.coe_eta] using hzK)

/-- The selected two-cut end is strictly smaller than the ambient graph. -/
theorem card_verts_lt :
    Fintype.card {v : V // v ∈ E.verts} < Fintype.card V := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem E.verts).mp E.verts_ne_univ
  exact Fintype.card_subtype_lt hx

private def sideHom :
    E.component.toSimpleGraph →g G.induce E.side where
  toFun z := ⟨z.1.1, z.1.2.1, z.1.2.2, z.2⟩
  map_rel' h := h

private theorem sideHom_surjective : Function.Surjective E.sideHom := by
  rintro ⟨v, hva, hvb, hvK⟩
  exact ⟨⟨⟨v, hva, hvb⟩, hvK⟩, rfl⟩

/-- The component side is connected in the ambient graph. -/
theorem side_connected : (G.induce E.side).Connected :=
  E.component.connected_toSimpleGraph.map E.sideHom E.sideHom_surjective

/-- Vertex-two-connectivity forces the left attachment to have an actual
neighbour in the selected component side. -/
private theorem exists_left_attachment
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected) :
    ∃ z, z ∈ E.side ∧ G.Adj E.a z := by
  obtain ⟨v, hv⟩ := E.side_nonempty
  obtain ⟨hva, hvb, hvK⟩ := hv
  let v' : {w : V // w ≠ E.b} := ⟨v, hvb⟩
  let a' : {w : V // w ≠ E.b} := ⟨E.a, E.boundary_ne⟩
  obtain ⟨p⟩ := hdelete E.b v' a'
  let rec firstExit {w : {w : V // w ≠ E.b}}
      (hwside : w.1 ∈ E.side)
      (q : (G.induce (fun z : V ↦ z ≠ E.b)).Walk w a') :
      ∃ z, z ∈ E.side ∧ G.Adj E.a z := by
    cases q with
    | nil =>
        exact False.elim (E.left_not_mem_side (by simpa [a'] using hwside))
    | @cons _ z _ hwz q =>
        by_cases hza : z.1 = E.a
        · have hAdj : G.Adj w.1 z.1 := hwz
          exact ⟨w.1, hwside, by simpa [hza] using hAdj.symm⟩
        · obtain ⟨hwa, hwb, hwK⟩ := hwside
          have hPairAdj :
              (G.induce (fun r : V ↦ r ≠ E.a ∧ r ≠ E.b)).Adj
                ⟨w.1, hwa, hwb⟩ ⟨z.1, hza, z.2⟩ := hwz
          have hzK :
              (⟨z.1, hza, z.2⟩ : {r : V // r ≠ E.a ∧ r ≠ E.b}) ∈
                E.component.supp :=
            E.component.mem_supp_of_adj_mem_supp hwK hPairAdj
          exact firstExit ⟨hza, z.2, hzK⟩ q
  termination_by q.length
  exact firstExit ⟨hva, hvb, hvK⟩ p

/-- The symmetric attachment fact for the right boundary vertex. -/
private theorem exists_right_attachment
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected) :
    ∃ z, z ∈ E.side ∧ G.Adj E.b z := by
  obtain ⟨v, hv⟩ := E.side_nonempty
  obtain ⟨hva, hvb, hvK⟩ := hv
  let v' : {w : V // w ≠ E.a} := ⟨v, hva⟩
  let b' : {w : V // w ≠ E.a} := ⟨E.b, E.boundary_ne.symm⟩
  obtain ⟨p⟩ := hdelete E.a v' b'
  let rec firstExit {w : {w : V // w ≠ E.a}}
      (hwside : w.1 ∈ E.side)
      (q : (G.induce (fun z : V ↦ z ≠ E.a)).Walk w b') :
      ∃ z, z ∈ E.side ∧ G.Adj E.b z := by
    cases q with
    | nil =>
        exact False.elim (E.right_not_mem_side (by simpa [b'] using hwside))
    | @cons _ z _ hwz q =>
        by_cases hzb : z.1 = E.b
        · have hAdj : G.Adj w.1 z.1 := hwz
          exact ⟨w.1, hwside, by simpa [hzb] using hAdj.symm⟩
        · obtain ⟨hwa, hwb, hwK⟩ := hwside
          have hPairAdj :
              (G.induce (fun r : V ↦ r ≠ E.a ∧ r ≠ E.b)).Adj
                ⟨w.1, hwa, hwb⟩ ⟨z.1, z.2, hzb⟩ := hwz
          have hzK :
              (⟨z.1, z.2, hzb⟩ : {r : V // r ≠ E.a ∧ r ≠ E.b}) ∈
                E.component.supp :=
            E.component.mem_supp_of_adj_mem_supp hwK hPairAdj
          exact firstExit ⟨z.2, hzb, hzK⟩ q
  termination_by q.length
  exact firstExit ⟨hva, hvb, hvK⟩ p

/-- Putting both attachment vertices back gives a connected induced end
graph in every vertex-two-connected ambient graph. -/
theorem verts_connected
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected) :
    (G.induce E.verts).Connected := by
  obtain ⟨za, hza, haza⟩ := E.exists_left_attachment hdelete
  obtain ⟨zb, hzb, hbzb⟩ := E.exists_right_attachment hdelete
  have hright : (G.induce (insert E.b E.side)).Connected := by
    rw [Set.insert_eq]
    exact G.connected_induce_union
      SimpleGraph.Preconnected.of_subsingleton E.side_connected.preconnected
      (by simp) hzb hbzb
  rw [verts, Set.insert_eq]
  exact G.connected_induce_union
    SimpleGraph.Preconnected.of_subsingleton hright.preconnected
    (by simp) (by simp [hza]) haza

end TwoCutEnd

/-! ## Extracting a genuine two-cut -/

/-- A connected graph on at least four vertices which is not vertex-three-
connected has a genuine two-cut component end. -/
theorem exists_twoCutEnd_of_not_vertexThreeConnected
    (hcard : 4 ≤ Fintype.card V) (hconn : G.Connected)
    (hnot : ¬VertexThreeConnected G) : Nonempty (TwoCutEnd G) := by
  classical
  have hpair : ∃ a b : V, a ≠ b ∧
      ¬(G.induce (fun w : V ↦ w ≠ a ∧ w ≠ b)).Connected := by
    by_contra hnone
    apply hnot
    refine ⟨hcard, hconn, ?_⟩
    intro a b hab
    by_contra hdisc
    exact hnone ⟨a, b, hab, hdisc⟩
  obtain ⟨a, b, hab, hdisc⟩ := hpair
  let D : SimpleGraph {w : V // w ≠ a ∧ w ≠ b} :=
    G.induce (fun w : V ↦ w ≠ a ∧ w ≠ b)
  have hsmall : ({a, b} : Finset V).card < Fintype.card V := by
    have hle := Finset.card_insert_le a ({b} : Finset V)
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hqa : q ≠ a := by intro h; exact hq (by simp [h])
  have hqb : q ≠ b := by intro h; exact hq (by simp [h])
  let qD : {w : V // w ≠ a ∧ w ≠ b} := ⟨q, hqa, hqb⟩
  let : Nonempty {w : V // w ≠ a ∧ w ≠ b} := ⟨qD⟩
  have hnpre : ¬D.Preconnected := by
    intro hp
    exact hdisc { preconnected := hp, nonempty := ⟨qD⟩ }
  obtain ⟨u, v, huv⟩ :
      ∃ u v : {w : V // w ≠ a ∧ w ≠ b}, ¬D.Reachable u v := by
    change ¬∀ u v, D.Reachable u v at hnpre
    obtain ⟨u, hu⟩ := Classical.not_forall.mp hnpre
    obtain ⟨v, huv⟩ := Classical.not_forall.mp hu
    exact ⟨u, v, huv⟩
  let K : D.ConnectedComponent := D.connectedComponentMk u
  have hvK : v ∉ K.supp := by
    intro hv
    apply huv
    have heq : D.connectedComponentMk v = K := by
      simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hv
    exact SimpleGraph.ConnectedComponent.exact heq.symm
  exact ⟨⟨a, b, hab, K, ⟨v, hvK⟩⟩⟩

/-- From any genuine two-cut one can choose a component side avoiding a
prescribed exceptional vertex (unless that vertex itself is an attachment). -/
theorem exists_twoCutEnd_avoiding_of_not_vertexThreeConnected
    (x₀ : V) (hcard : 4 ≤ Fintype.card V) (hconn : G.Connected)
    (hnot : ¬VertexThreeConnected G) :
    ∃ E : TwoCutEnd G, x₀ = E.a ∨ x₀ = E.b ∨ x₀ ∉ E.side := by
  classical
  obtain ⟨E⟩ := exists_twoCutEnd_of_not_vertexThreeConnected hcard hconn hnot
  by_cases hxa : x₀ = E.a
  · exact ⟨E, Or.inl hxa⟩
  by_cases hxb : x₀ = E.b
  · exact ⟨E, Or.inr (Or.inl hxb)⟩
  by_cases hxside : x₀ ∈ E.side
  · obtain ⟨z, hzOutside⟩ := E.proper
    obtain ⟨v, hvE⟩ := E.component.nonempty_supp
    let K' :=
      (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk z
    have hKne : K' ≠ E.component := by
      intro h
      apply hzOutside
      have :
          (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk z =
            E.component := h
      simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using this
    have hvOutside : v ∉ K'.supp := by
      intro hvK'
      apply hKne
      have hvEq :
          (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk v =
            K' := by
        simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hvK'
      have hvEqE :
          (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk v =
            E.component := by
        simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hvE
      exact hvEq.symm.trans hvEqE
    let E' : TwoCutEnd G := ⟨E.a, E.b, E.boundary_ne, K', ⟨v, hvOutside⟩⟩
    refine ⟨E', Or.inr (Or.inr ?_)⟩
    rintro ⟨hxneA, hxneB, hxK'⟩
    rcases hxside with ⟨hxa₀, hxb₀, hxE⟩
    apply hKne
    have hxEqK' :
        (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk
            ⟨x₀, hxneA, hxneB⟩ = K' := by
      simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hxK'
    have hxEqE :
        (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk
            ⟨x₀, hxneA, hxneB⟩ = E.component := by
      simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hxE
    exact hxEqK'.symm.trans hxEqE
  · exact ⟨E, Or.inr (Or.inr hxside)⟩

/-- Because adjacent vertices which survive a two-deletion lie in the same
component, some component end avoids both of two prescribed adjacent
vertices.  This is the elementary reason the nested end chosen inside a
torso can avoid both old attachments. -/
theorem exists_twoCutEnd_avoiding_adjacent
    (E : TwoCutEnd G) {c d : V} (hcd : G.Adj c d) :
    ∃ F : TwoCutEnd G, c ∉ F.side ∧ d ∉ F.side := by
  classical
  by_cases hnone : c ∉ E.side ∧ d ∉ E.side
  · exact ⟨E, hnone⟩
  · have ht : c ∈ E.side ∨ d ∈ E.side := by tauto
    obtain ⟨z, hzOutside⟩ := E.proper
    obtain ⟨v, hvE⟩ := E.component.nonempty_supp
    let K' :=
      (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk z
    have hKne : K' ≠ E.component := by
      intro h
      apply hzOutside
      simpa only [K', SimpleGraph.ConnectedComponent.mem_supp_iff] using h
    have hvOutside : v ∉ K'.supp := by
      intro hvK'
      apply hKne
      have hvEq :
          (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk v =
            K' := by
        simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hvK'
      have hvEqE :
          (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk v =
            E.component := by
        simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hvE
      exact hvEq.symm.trans hvEqE
    let F : TwoCutEnd G := ⟨E.a, E.b, E.boundary_ne, K', ⟨v, hvOutside⟩⟩
    have hcOld (hca : c ≠ E.a) (hcb : c ≠ E.b) :
        (⟨c, hca, hcb⟩ : {w : V // w ≠ E.a ∧ w ≠ E.b}) ∈ E.component.supp := by
      by_cases hcs : c ∈ E.side
      · rcases hcs with ⟨hca', hcb', hcE⟩
        simpa only [Subtype.coe_eta] using hcE
      · have hds : d ∈ E.side := ht.resolve_left hcs
        obtain ⟨hda, hdb, hdE⟩ := hds
        have hAdj :
            (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).Adj
              ⟨d, hda, hdb⟩ ⟨c, hca, hcb⟩ := hcd.symm
        exact E.component.mem_supp_of_adj_mem_supp hdE hAdj
    have hdOld (hda : d ≠ E.a) (hdb : d ≠ E.b) :
        (⟨d, hda, hdb⟩ : {w : V // w ≠ E.a ∧ w ≠ E.b}) ∈ E.component.supp := by
      by_cases hds : d ∈ E.side
      · rcases hds with ⟨hda', hdb', hdE⟩
        simpa only [Subtype.coe_eta] using hdE
      · have hcs : c ∈ E.side := ht.resolve_right hds
        obtain ⟨hca, hcb, hcE⟩ := hcs
        have hAdj :
            (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).Adj
              ⟨c, hca, hcb⟩ ⟨d, hda, hdb⟩ := hcd
        exact E.component.mem_supp_of_adj_mem_supp hcE hAdj
    refine ⟨F, ?_, ?_⟩
    · rintro ⟨hca, hcb, hcK⟩
      apply hKne
      have hcEqK :
          (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk
              ⟨c, hca, hcb⟩ = K' := by
        simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hcK
      have hcEqE :
          (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk
              ⟨c, hca, hcb⟩ = E.component := by
        simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hcOld hca hcb
      exact hcEqK.symm.trans hcEqE
    · rintro ⟨hda, hdb, hdK⟩
      apply hKne
      have hdEqK :
          (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk
              ⟨d, hda, hdb⟩ = K' := by
        simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hdK
      have hdEqE :
          (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk
              ⟨d, hda, hdb⟩ = E.component := by
        simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hdOld hda hdb
      exact hdEqK.symm.trans hdEqE

namespace TwoCutEnd

/-- Cardinal minimality among all two-cut component ends which avoid the
same exceptional vertex. -/
def IsMinimalAvoiding (E : TwoCutEnd G) (x₀ : V) : Prop :=
  (x₀ = E.a ∨ x₀ = E.b ∨ x₀ ∉ E.side) ∧
    ∀ F : TwoCutEnd G,
      x₀ = F.a ∨ x₀ = F.b ∨ x₀ ∉ F.side →
      Fintype.card {v : V // v ∈ E.verts} ≤
        Fintype.card {v : V // v ∈ F.verts}

/-- Every vertex on an end side avoids the distinguished vertex omitted by
a minimal pointed end. -/
theorem IsMinimalAvoiding.ne_exception_of_mem_side
    {E : TwoCutEnd G} {x₀ w : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hw : w ∈ E.side) : w ≠ x₀ := by
  intro h
  subst w
  rcases hminimal.1 with hxa | hxb | hxout
  · exact E.left_not_mem_side (hxa ▸ hw)
  · exact E.right_not_mem_side (hxb ▸ hw)
  · exact hxout hw

/-- Minimality and avoidance are invariant under exchanging the two boundary
labels. -/
theorem IsMinimalAvoiding.swap
    {E : TwoCutEnd G} {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀) :
    E.swap.IsMinimalAvoiding x₀ := by
  constructor
  · rcases hminimal.1 with hxa | hxb | hxout
    · exact Or.inr (Or.inl hxa)
    · exact Or.inl hxb
    · exact Or.inr (Or.inr (by simpa only [E.swap_side] using hxout))
  · intro F havoid
    rw [show Fintype.card {v : V // v ∈ E.swap.verts} =
        Fintype.card {v : V // v ∈ E.verts} by
      exact Fintype.card_congr (Equiv.setCongr E.swap_verts)]
    exact hminimal.2 F havoid

end TwoCutEnd

/-- A finite nonempty family of exceptional-vertex-avoiding ends contains a
cardinality-minimal member. -/
theorem exists_minimal_twoCutEnd_avoiding
    (x₀ : V) (hex : ∃ E : TwoCutEnd G,
      x₀ = E.a ∨ x₀ = E.b ∨ x₀ ∉ E.side) :
    ∃ E : TwoCutEnd G, E.IsMinimalAvoiding x₀ := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ E : TwoCutEnd G,
      (x₀ = E.a ∨ x₀ = E.b ∨ x₀ ∉ E.side) ∧
        Fintype.card {v : V // v ∈ E.verts} = n
  have hP : ∃ n, P n := by
    obtain ⟨E, havoid⟩ := hex
    exact ⟨_, E, havoid, rfl⟩
  let n := Nat.find hP
  obtain ⟨E, havoid, hcardE⟩ := Nat.find_spec hP
  refine ⟨E, havoid, ?_⟩
  intro F havoidF
  by_contra hle
  have hcardEn : Fintype.card {v : V // v ∈ E.verts} = n := by
    simpa [n] using hcardE
  have hlt : Fintype.card {v : V // v ∈ F.verts} < n := by
    rw [← hcardEn]
    omega
  exact Nat.find_min hP hlt ⟨F, havoidF, rfl⟩

/-- A non-three-connected graph has a minimal end avoiding the distinguished
vertex. -/
theorem exists_minimal_twoCutEnd_avoiding_of_not_vertexThreeConnected
    (x₀ : V) (hcard : 4 ≤ Fintype.card V) (hconn : G.Connected)
    (hnot : ¬VertexThreeConnected G) :
    ∃ E : TwoCutEnd G, E.IsMinimalAvoiding x₀ :=
  exists_minimal_twoCutEnd_avoiding x₀
    (exists_twoCutEnd_avoiding_of_not_vertexThreeConnected x₀ hcard hconn hnot)

/-! ## Lifting from the virtual-edge torso -/

namespace TwoCutEnd

variable (E : TwoCutEnd G)

/-- The virtual-edge torso on a two-cut component end. -/
abbrev torso : SimpleGraph {v : V // v ∈ E.verts} :=
  AHTTorso.torsoOn G E.verts E.a E.b E.left_mem_verts E.right_mem_verts

/-- The actual induced end graph, denoted `J` in the nonedge branch of
Section 7. -/
abbrev inducedEnd : SimpleGraph {v : V // v ∈ E.verts} :=
  G.induce E.verts

/-- Identify the vertex types of an end and its boundary swap. -/
def swapVertsEquiv :
    {v : V // v ∈ E.swap.verts} ≃ {v : V // v ∈ E.verts} :=
  Equiv.setCongr E.swap_verts

/-- The actual induced end graph is unchanged, up to the canonical
proof-only equivalence, by swapping the attachment labels. -/
def swapInducedEndIso : E.swap.inducedEnd ≃g E.inducedEnd where
  toEquiv := E.swapVertsEquiv
  map_rel_iff' := by intro _ _; rfl

/-- False twins transport along graph isomorphisms. -/
private theorem areFalseTwins_mapIso
    {X Y : Type u} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    {K : SimpleGraph X} [DecidableRel K.Adj]
    {L : SimpleGraph Y} [DecidableRel L.Adj]
    (e : K ≃g L) {u v : X} (h : AreFalseTwins K u v) :
    AreFalseTwins L (e u) (e v) := by
  constructor
  · exact e.injective.ne h.1
  · ext w
    simp only [SimpleGraph.mem_neighborSet]
    have ht := h.adj_iff (e.symm w)
    have huMap := e.map_adj_iff (v := u) (w := e.symm w)
    have hvMap := e.map_adj_iff (v := v) (w := e.symm w)
    simpa using huMap.trans (ht.trans hvMap.symm)

/-- The actual end graph has at least the two distinct attachments. -/
theorem two_le_card_inducedEnd :
    2 ≤ Fintype.card {v : V // v ∈ E.verts} := by
  rw [show (2 : ℕ) = 1 + 1 by omega]
  apply Fintype.one_lt_card_iff.mpr
  exact ⟨⟨E.a, E.left_mem_verts⟩, ⟨E.b, E.right_mem_verts⟩,
    fun h ↦ E.boundary_ne (congrArg Subtype.val h)⟩

/-- Wheel-freeness descends to the actual induced end graph. -/
theorem noWheel_inducedEnd (hnoWheel : ¬HasWheelWitness G) :
    ¬HasWheelWitness E.inducedEnd := by
  intro hW
  exact hnoWheel (HasWheelWitness.induce E.verts hW)

/-- In the genuinely virtual case, the virtual edge contributes exactly the
right attachment to the left attachment's neighbourhood. -/
theorem torso_left_neighborFinset_eq_insert
    (hab : ¬G.Adj E.a E.b) :
    E.torso.neighborFinset ⟨E.a, E.left_mem_verts⟩ =
      insert ⟨E.b, E.right_mem_verts⟩
        (E.inducedEnd.neighborFinset ⟨E.a, E.left_mem_verts⟩) := by
  classical
  ext w
  simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
  change
    (G.Adj E.a w.1 ∨
      (SimpleGraph.edge
        (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts})
        ⟨E.b, E.right_mem_verts⟩).Adj
          ⟨E.a, E.left_mem_verts⟩ w) ↔
      w = ⟨E.b, E.right_mem_verts⟩ ∨ G.Adj E.a w.1
  have hne :
      (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) ≠
        ⟨E.b, E.right_mem_verts⟩ :=
    fun h ↦ E.boundary_ne (congrArg Subtype.val h)
  rw [SimpleGraph.edge_adj]
  have hnot : w = ⟨E.b, E.right_mem_verts⟩ →
      ¬(⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) = w := by
    intro hwb haw
    exact hne (haw.trans hwb)
  tauto

/-- Symmetric neighbourhood formula at the right attachment. -/
theorem torso_right_neighborFinset_eq_insert
    (hab : ¬G.Adj E.a E.b) :
    E.torso.neighborFinset ⟨E.b, E.right_mem_verts⟩ =
      insert ⟨E.a, E.left_mem_verts⟩
        (E.inducedEnd.neighborFinset ⟨E.b, E.right_mem_verts⟩) := by
  classical
  ext w
  simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
  change
    (G.Adj E.b w.1 ∨
      (SimpleGraph.edge
        (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts})
        ⟨E.b, E.right_mem_verts⟩).Adj
          ⟨E.b, E.right_mem_verts⟩ w) ↔
      w = ⟨E.a, E.left_mem_verts⟩ ∨ G.Adj E.b w.1
  have hne :
      (⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) ≠
        ⟨E.a, E.left_mem_verts⟩ :=
    fun h ↦ E.boundary_ne (congrArg Subtype.val h).symm
  rw [SimpleGraph.edge_adj]
  have hnot : w = ⟨E.a, E.left_mem_verts⟩ →
      ¬(⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) = w := by
    intro hwa hbw
    exact hne (hbw.trans hwa)
  tauto

/-- Adding the missing virtual edge raises the left attachment degree by
exactly one. -/
theorem degree_torso_left_eq_degree_inducedEnd_add_one
    (hab : ¬G.Adj E.a E.b) :
    E.torso.degree ⟨E.a, E.left_mem_verts⟩ =
      E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩ + 1 := by
  classical
  rw [← E.torso.card_neighborFinset_eq_degree,
    E.torso_left_neighborFinset_eq_insert hab,
    Finset.card_insert_of_notMem,
    E.inducedEnd.card_neighborFinset_eq_degree]
  rw [SimpleGraph.mem_neighborFinset]
  exact hab

/-- Symmetric degree formula at the right attachment. -/
theorem degree_torso_right_eq_degree_inducedEnd_add_one
    (hab : ¬G.Adj E.a E.b) :
    E.torso.degree ⟨E.b, E.right_mem_verts⟩ =
      E.inducedEnd.degree ⟨E.b, E.right_mem_verts⟩ + 1 := by
  classical
  rw [← E.torso.card_neighborFinset_eq_degree,
    E.torso_right_neighborFinset_eq_insert hab,
    Finset.card_insert_of_notMem,
    E.inducedEnd.card_neighborFinset_eq_degree]
  rw [SimpleGraph.mem_neighborFinset]
  exact fun h ↦ hab h.symm

/-- The first, purely finite step of source Claim (10).  A false twin of the
left attachment in the actual end graph, when that attachment has degree at
least three there, supplies three distinct common neighbours, all strictly
inside the selected component side. -/
theorem exists_three_interior_commonNeighbors_left
    (hab : ¬G.Adj E.a E.b)
    (hdeg : 3 ≤ E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩)
    {a' : {v : V // v ∈ E.verts}}
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a') :
    ∃ x y z : {v : V // v ∈ E.verts},
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      E.inducedEnd.Adj ⟨E.a, E.left_mem_verts⟩ x ∧
      E.inducedEnd.Adj ⟨E.a, E.left_mem_verts⟩ y ∧
      E.inducedEnd.Adj ⟨E.a, E.left_mem_verts⟩ z ∧
      E.inducedEnd.Adj a' x ∧ E.inducedEnd.Adj a' y ∧
      E.inducedEnd.Adj a' z ∧
      x.1 ≠ E.a ∧ x.1 ≠ E.b ∧ y.1 ≠ E.a ∧ y.1 ≠ E.b ∧
      z.1 ≠ E.a ∧ z.1 ≠ E.b := by
  classical
  have hcard : 2 <
      (E.inducedEnd.neighborFinset ⟨E.a, E.left_mem_verts⟩).card := by
    rw [E.inducedEnd.card_neighborFinset_eq_degree]
    omega
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp hcard
  have hax : E.inducedEnd.Adj ⟨E.a, E.left_mem_verts⟩ x := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx
  have hay : E.inducedEnd.Adj ⟨E.a, E.left_mem_verts⟩ y := by
    simpa only [SimpleGraph.mem_neighborFinset] using hy
  have haz : E.inducedEnd.Adj ⟨E.a, E.left_mem_verts⟩ z := by
    simpa only [SimpleGraph.mem_neighborFinset] using hz
  have hinside {w : {v : V // v ∈ E.verts}}
      (haw : E.inducedEnd.Adj ⟨E.a, E.left_mem_verts⟩ w) :
      w.1 ≠ E.a ∧ w.1 ≠ E.b := by
    constructor
    · intro hwa
      exact haw.ne (Subtype.ext hwa.symm)
    · intro hwb
      apply hab
      have hawG : G.Adj E.a w.1 := haw
      simpa [hwb] using hawG
  exact ⟨x, y, z, hxy, hxz, hyz, hax, hay, haz,
    (htwin.adj_iff x).mp hax, (htwin.adj_iff y).mp hay,
    (htwin.adj_iff z).mp haz,
    (hinside hax).1, (hinside hax).2,
    (hinside hay).1, (hinside hay).2,
    (hinside haz).1, (hinside haz).2⟩

/-- Symmetric common-neighbour extraction at the right attachment. -/
theorem exists_three_interior_commonNeighbors_right
    (hab : ¬G.Adj E.a E.b)
    (hdeg : 3 ≤ E.inducedEnd.degree ⟨E.b, E.right_mem_verts⟩)
    {b' : {v : V // v ∈ E.verts}}
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.b, E.right_mem_verts⟩ b') :
    ∃ x y z : {v : V // v ∈ E.verts},
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      E.inducedEnd.Adj ⟨E.b, E.right_mem_verts⟩ x ∧
      E.inducedEnd.Adj ⟨E.b, E.right_mem_verts⟩ y ∧
      E.inducedEnd.Adj ⟨E.b, E.right_mem_verts⟩ z ∧
      E.inducedEnd.Adj b' x ∧ E.inducedEnd.Adj b' y ∧
      E.inducedEnd.Adj b' z ∧
      x.1 ≠ E.a ∧ x.1 ≠ E.b ∧ y.1 ≠ E.a ∧ y.1 ≠ E.b ∧
      z.1 ≠ E.a ∧ z.1 ≠ E.b := by
  classical
  have hcard : 2 <
      (E.inducedEnd.neighborFinset ⟨E.b, E.right_mem_verts⟩).card := by
    rw [E.inducedEnd.card_neighborFinset_eq_degree]
    omega
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp hcard
  have hbx : E.inducedEnd.Adj ⟨E.b, E.right_mem_verts⟩ x := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx
  have hby : E.inducedEnd.Adj ⟨E.b, E.right_mem_verts⟩ y := by
    simpa only [SimpleGraph.mem_neighborFinset] using hy
  have hbz : E.inducedEnd.Adj ⟨E.b, E.right_mem_verts⟩ z := by
    simpa only [SimpleGraph.mem_neighborFinset] using hz
  have hinside {w : {v : V // v ∈ E.verts}}
      (hbw : E.inducedEnd.Adj ⟨E.b, E.right_mem_verts⟩ w) :
      w.1 ≠ E.a ∧ w.1 ≠ E.b := by
    constructor
    · intro hwa
      apply hab
      have hbwG : G.Adj E.b w.1 := hbw
      simpa [hwa] using hbwG.symm
    · intro hwb
      exact hbw.ne (Subtype.ext hwb.symm)
  exact ⟨x, y, z, hxy, hxz, hyz, hbx, hby, hbz,
    (htwin.adj_iff x).mp hbx, (htwin.adj_iff y).mp hby,
    (htwin.adj_iff z).mp hbz,
    (hinside hbx).1, (hinside hbx).2,
    (hinside hby).1, (hinside hby).2,
    (hinside hbz).1, (hinside hbz).2⟩

/-- False twins wholly in the component side of the actual induced end graph
lift to ambient false twins.  This is the lifting step used after applying
the Section 7 induction hypothesis to `J`. -/
theorem falseTwins_inducedEnd_lift
    {u v : {w : V // w ∈ E.verts}}
    (hua : u.1 ≠ E.a) (hub : u.1 ≠ E.b)
    (hva : v.1 ≠ E.a) (hvb : v.1 ≠ E.b)
    (htwin : AreFalseTwins E.inducedEnd u v) :
    AreFalseTwins G u.1 v.1 := by
  have huside : u.1 ∈ E.side := E.mem_side_of_mem_verts u.2 hua hub
  have hvside : v.1 ∈ E.side := E.mem_side_of_mem_verts v.2 hva hvb
  have hNu : G.neighborSet u.1 ⊆ E.verts :=
    E.neighborSet_subset_verts huside
  have hNv : G.neighborSet v.1 ⊆ E.verts :=
    E.neighborSet_subset_verts hvside
  refine ⟨fun huv ↦ htwin.1 (Subtype.ext huv), ?_⟩
  ext w
  constructor
  · intro huw
    have hw : w ∈ E.verts := hNu huw
    have hi : E.inducedEnd.Adj u ⟨w, hw⟩ := huw
    exact (htwin.adj_iff ⟨w, hw⟩).mp hi
  · intro hvw
    have hw : w ∈ E.verts := hNv hvw
    have hi : E.inducedEnd.Adj v ⟨w, hw⟩ := hvw
    exact (htwin.adj_iff ⟨w, hw⟩).mpr hi

/-- A degree-three pair wholly in the side of `J` lifts with its degree
unchanged. -/
theorem interiorFalseTwins_inducedEnd_lift
    {u v : {w : V // w ∈ E.verts}}
    (htwin : AreFalseTwins E.inducedEnd u v)
    (hdeg : E.inducedEnd.degree u = 3)
    (hua : u.1 ≠ E.a) (hub : u.1 ≠ E.b)
    (hva : v.1 ≠ E.a) (hvb : v.1 ≠ E.b) :
    ∃ p q : V, AreFalseTwins G p q ∧ G.degree p = 3 := by
  have huside : u.1 ∈ E.side := E.mem_side_of_mem_verts u.2 hua hub
  have hNu : G.neighborSet u.1 ⊆ E.verts :=
    E.neighborSet_subset_verts huside
  have hdegG : G.degree u.1 = 3 := by
    rw [← G.degree_induce_of_neighborSet_subset hNu]
    exact hdeg
  exact ⟨u.1, v.1,
    E.falseTwins_inducedEnd_lift hua hub hva hvb htwin, hdegG⟩

/-- If the left attachment retains degree at least three in `J`, then `J`
has minimum degree three away from the right attachment.  Interior degrees
agree with their ambient degrees because the component side is closed. -/
theorem inducedEnd_minDegreeThreeExcept_right
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hleft : 3 ≤
      E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩) :
    MinDegreeThreeExcept E.inducedEnd ⟨E.b, E.right_mem_verts⟩ := by
  intro w hwb
  by_cases hwa : w = ⟨E.a, E.left_mem_verts⟩
  · subst w
    exact hleft
  · have hwna : w.1 ≠ E.a := by
      intro h
      apply hwa
      exact Subtype.ext h
    have hwnb : w.1 ≠ E.b := by
      intro h
      apply hwb
      exact Subtype.ext h
    have hwside : w.1 ∈ E.side :=
      E.mem_side_of_mem_verts w.2 hwna hwnb
    have hclosed : G.neighborSet w.1 ⊆ E.verts :=
      E.neighborSet_subset_verts hwside
    rw [G.degree_induce_of_neighborSet_subset hclosed]
    exact hminSide w.1 hwside

/-- Symmetrically, a high-degree right attachment makes the left attachment
the sole possible low-degree vertex of `J`. -/
theorem inducedEnd_minDegreeThreeExcept_left
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hright : 3 ≤
      E.inducedEnd.degree ⟨E.b, E.right_mem_verts⟩) :
    MinDegreeThreeExcept E.inducedEnd ⟨E.a, E.left_mem_verts⟩ := by
  intro w hwa
  by_cases hwb : w = ⟨E.b, E.right_mem_verts⟩
  · subst w
    exact hright
  · have hwna : w.1 ≠ E.a := by
      intro h
      apply hwa
      exact Subtype.ext h
    have hwnb : w.1 ≠ E.b := by
      intro h
      apply hwb
      exact Subtype.ext h
    have hwside : w.1 ∈ E.side :=
      E.mem_side_of_mem_verts w.2 hwna hwnb
    have hclosed : G.neighborSet w.1 ⊆ E.verts :=
      E.neighborSet_subset_verts hwside
    rw [G.degree_induce_of_neighborSet_subset hclosed]
    exact hminSide w.1 hwside

/-- All induction hypotheses for the smaller pointed graph `J`, in the
branch where the left attachment is high and the right attachment is kept as
the possible low-degree exception. -/
theorem inducedEnd_pointedData_right
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G)
    (hleft : 3 ≤
      E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩) :
    2 ≤ Fintype.card {v : V // v ∈ E.verts} ∧
      E.inducedEnd.Connected ∧
      MinDegreeThreeExcept E.inducedEnd
        ⟨E.b, E.right_mem_verts⟩ ∧
      ¬HasWheelWitness E.inducedEnd :=
  ⟨E.two_le_card_inducedEnd, E.verts_connected hdelete,
    E.inducedEnd_minDegreeThreeExcept_right hminSide hleft,
    E.noWheel_inducedEnd hnoWheel⟩

/-- Symmetric pointed induction data when the right attachment is high. -/
theorem inducedEnd_pointedData_left
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G)
    (hright : 3 ≤
      E.inducedEnd.degree ⟨E.b, E.right_mem_verts⟩) :
    2 ≤ Fintype.card {v : V // v ∈ E.verts} ∧
      E.inducedEnd.Connected ∧
      MinDegreeThreeExcept E.inducedEnd
        ⟨E.a, E.left_mem_verts⟩ ∧
      ¬HasWheelWitness E.inducedEnd :=
  ⟨E.two_le_card_inducedEnd, E.verts_connected hdelete,
    E.inducedEnd_minDegreeThreeExcept_left hminSide hright,
    E.noWheel_inducedEnd hnoWheel⟩

/-- The virtual-edge torso is connected whenever the ambient graph remains
connected after deleting either attachment. -/
theorem torso_connected
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected) :
    E.torso.Connected := by
  apply (E.verts_connected hdelete).mono
  intro u v huv
  exact Or.inl huv

/-- If every interior vertex has ambient degree at least three, the end torso
has at least four vertices. -/
theorem four_le_card_torso
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v) :
    4 ≤ Fintype.card {v : V // v ∈ E.verts} := by
  obtain ⟨v, hvside⟩ := E.side_nonempty
  obtain ⟨hva, hvb, hvK⟩ := hvside
  let vT : {w : V // w ∈ E.verts} :=
    ⟨v, Set.mem_insert_iff.mpr <| Or.inr <|
      Set.mem_insert_iff.mpr <| Or.inr ⟨hva, hvb, hvK⟩⟩
  have hclosed : G.neighborSet v ⊆ E.verts :=
    E.neighborSet_subset_verts ⟨hva, hvb, hvK⟩
  have hdeg : 3 ≤ E.torso.degree vT := by
    rw [AHTTorso.degree_torsoOn_eq hva hvb hclosed]
    exact hminSide v ⟨hva, hvb, hvK⟩
  have hlt := E.torso.degree_lt_card_verts vT
  omega

/-- The two attachments are adjacent in every virtual-edge torso. -/
theorem torso_boundary_adj :
    E.torso.Adj ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩ := by
  apply Or.inr
  rw [SimpleGraph.edge_adj]
  exact ⟨Or.inl ⟨rfl, rfl⟩,
    fun h ↦ E.boundary_ne (congrArg Subtype.val h)⟩

/-- The exact source conversion used in the nonedge branch: centre
confinement plus degree three at both attachments makes the end torso almost
wheel-free. -/
theorem almostWheelFree_torso_of_centres_of_boundary_degrees
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hdega : E.torso.degree ⟨E.a, E.left_mem_verts⟩ = 3)
    (hdegb : E.torso.degree ⟨E.b, E.right_mem_verts⟩ = 3) :
    AlmostWheelFree E.torso :=
  almostWheelFree_of_at_of_adj_of_degree_three hcentres
    E.torso_boundary_adj hdega hdegb

/-- A component of a nested two-cut torso end which avoids both old
attachments cannot escape the old end in the ambient graph.  This is the
path-lifting core of the minimal-end proof of AHT Lemma 4.4. -/
private theorem ambient_component_subset_nested_side
    (F : TwoCutEnd E.torso)
    (hleft : (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) ∉ F.side)
    (hright : (⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) ∉ F.side)
    {z : {v : V // v ∈ E.verts}} (hz : z ∈ F.side)
    {w : {v : V // v ≠ F.a.1 ∧ v ≠ F.b.1}}
    (hw : w ∈
      ((G.induce (fun v : V ↦ v ≠ F.a.1 ∧ v ≠ F.b.1)).connectedComponentMk
        ⟨z.1, (fun h ↦ (F.mem_side_iff.mp hz).1 (Subtype.ext h)),
          (fun h ↦ (F.mem_side_iff.mp hz).2.1 (Subtype.ext h))⟩).supp) :
    ∃ hwE : w.1 ∈ E.verts,
      (⟨w.1, hwE⟩ : {v : V // v ∈ E.verts}) ∈ F.side := by
  classical
  let zD : {v : V // v ≠ F.a.1 ∧ v ≠ F.b.1} :=
    ⟨z.1, (fun h ↦ (F.mem_side_iff.mp hz).1 (Subtype.ext h)),
      (fun h ↦ (F.mem_side_iff.mp hz).2.1 (Subtype.ext h))⟩
  have hcomp :
      (G.induce (fun v : V ↦ v ≠ F.a.1 ∧ v ≠ F.b.1)).connectedComponentMk w =
        (G.induce (fun v : V ↦ v ≠ F.a.1 ∧ v ≠ F.b.1)).connectedComponentMk zD := by
    simpa only [zD, SimpleGraph.ConnectedComponent.mem_supp_iff] using hw
  have hreach :
      (G.induce (fun v : V ↦ v ≠ F.a.1 ∧ v ≠ F.b.1)).Reachable zD w :=
    SimpleGraph.ConnectedComponent.exact hcomp.symm
  obtain ⟨p⟩ := hreach
  let P := fun r : {v : V // v ≠ F.a.1 ∧ v ≠ F.b.1} ↦
    ∃ hrE : r.1 ∈ E.verts,
      (⟨r.1, hrE⟩ : {v : V // v ∈ E.verts}) ∈ F.side
  have hzP : P zD := ⟨z.2, by simpa [zD] using hz⟩
  have propagate {r s : {v : V // v ≠ F.a.1 ∧ v ≠ F.b.1}}
      (hr : P r)
      (hrs : (G.induce (fun v : V ↦ v ≠ F.a.1 ∧ v ≠ F.b.1)).Adj r s) :
      P s := by
    obtain ⟨hrE, hrF⟩ := hr
    let rE : {v : V // v ∈ E.verts} := ⟨r.1, hrE⟩
    have hra : r.1 ≠ E.a := by
      intro h
      apply hleft
      have hre : rE = ⟨E.a, E.left_mem_verts⟩ := Subtype.ext h
      exact hre ▸ hrF
    have hrb : r.1 ≠ E.b := by
      intro h
      apply hright
      have hre : rE = ⟨E.b, E.right_mem_verts⟩ := Subtype.ext h
      exact hre ▸ hrF
    have hrside : r.1 ∈ E.side := E.mem_side_of_mem_verts hrE hra hrb
    have hrsG : G.Adj r.1 s.1 := hrs
    have hsE : s.1 ∈ E.verts := E.neighborSet_subset_verts hrside hrsG
    let sE : {v : V // v ∈ E.verts} := ⟨s.1, hsE⟩
    have hrsT : E.torso.Adj rE sE :=
      (AHTTorso.torsoOn_adj_iff_of_ne_boundary
        (G := G) (S := E.verts) (a := E.a) (b := E.b)
        (ha := E.left_mem_verts) (hb := E.right_mem_verts)
        (u := rE) (w := sE) hra hrb).mpr hrsG
    obtain ⟨hrx, hry, hrK⟩ := hrF
    have hsx : sE ≠ F.a := by
      intro h
      exact s.2.1 (congrArg (fun q : {v : V // v ∈ E.verts} ↦ q.1) h)
    have hsy : sE ≠ F.b := by
      intro h
      exact s.2.2 (congrArg (fun q : {v : V // v ∈ E.verts} ↦ q.1) h)
    have hrsD :
        (E.torso.induce (fun q : {v : V // v ∈ E.verts} ↦
          q ≠ F.a ∧ q ≠ F.b)).Adj
          ⟨rE, hrx, hry⟩ ⟨sE, hsx, hsy⟩ := hrsT
    have hsK :
        (⟨sE, hsx, hsy⟩ :
          {q : {v : V // v ∈ E.verts} // q ≠ F.a ∧ q ≠ F.b}) ∈
          F.component.supp :=
      F.component.mem_supp_of_adj_mem_supp hrK hrsD
    exact ⟨hsE, hsx, hsy, hsK⟩
  let rec follow {r s : {v : V // v ≠ F.a.1 ∧ v ≠ F.b.1}}
      (hr : P r)
      (q : (G.induce (fun v : V ↦ v ≠ F.a.1 ∧ v ≠ F.b.1)).Walk r s) :
      P s := by
    cases q with
    | nil => exact hr
    | cons hrs q => exact follow (propagate hr hrs) q
  termination_by q.length
  exact follow hzP p

/-- Regard a component end of an end torso, chosen away from both old
attachments, as an end of the original graph. -/
private noncomputable def nestedAmbientEnd
    (F : TwoCutEnd E.torso)
    (hleft : (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) ∉ F.side)
    (hright : (⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) ∉ F.side)
    (z : {v : V // v ∈ E.verts}) (hz : z ∈ F.side) : TwoCutEnd G := by
  classical
  let zD : {v : V // v ≠ F.a.1 ∧ v ≠ F.b.1} :=
    ⟨z.1, (fun h ↦ (F.mem_side_iff.mp hz).1 (Subtype.ext h)),
      (fun h ↦ (F.mem_side_iff.mp hz).2.1 (Subtype.ext h))⟩
  let K :=
    (G.induce (fun v : V ↦ v ≠ F.a.1 ∧ v ≠ F.b.1)).connectedComponentMk zD
  let hex := (Set.ne_univ_iff_exists_notMem E.verts).mp E.verts_ne_univ
  let o : V := Classical.choose hex
  have ho : o ∉ E.verts := Classical.choose_spec hex
  have hoa : o ≠ F.a.1 := by
    intro h
    apply ho
    simpa [h] using F.a.2
  have hob : o ≠ F.b.1 := by
    intro h
    apply ho
    simpa [h] using F.b.2
  let oD : {v : V // v ≠ F.a.1 ∧ v ≠ F.b.1} := ⟨o, hoa, hob⟩
  have hoK : oD ∉ K.supp := by
    intro hm
    have hm' : oD ∈
        ((G.induce (fun v : V ↦ v ≠ F.a.1 ∧ v ≠ F.b.1)).connectedComponentMk
          zD).supp := by
      simpa [K] using hm
    obtain ⟨hoE, -⟩ := E.ambient_component_subset_nested_side F hleft hright hz hm'
    exact ho hoE
  exact ⟨F.a.1, F.b.1,
    fun h ↦ F.boundary_ne (Subtype.ext h), K, ⟨oD, hoK⟩⟩

/-- The ambient end obtained from a nested torso end has no vertices beyond
that nested end. -/
private theorem nestedAmbientEnd_side
    (F : TwoCutEnd E.torso)
    (hleft : (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) ∉ F.side)
    (hright : (⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) ∉ F.side)
    (z : {v : V // v ∈ E.verts}) (hz : z ∈ F.side)
    {w : V} (hw : w ∈ (nestedAmbientEnd E F hleft hright z hz).side) :
    ∃ hwE : w ∈ E.verts,
      (⟨w, hwE⟩ : {v : V // v ∈ E.verts}) ∈ F.side := by
  classical
  obtain ⟨hwa, hwb, hwK⟩ := hw
  change w ≠ F.a.1 at hwa
  change w ≠ F.b.1 at hwb
  let wD : {v : V // v ≠ F.a.1 ∧ v ≠ F.b.1} := ⟨w, hwa, hwb⟩
  let zD : {v : V // v ≠ F.a.1 ∧ v ≠ F.b.1} :=
    ⟨z.1, (fun h ↦ (F.mem_side_iff.mp hz).1 (Subtype.ext h)),
      (fun h ↦ (F.mem_side_iff.mp hz).2.1 (Subtype.ext h))⟩
  have hwK' : wD ∈
      ((G.induce (fun v : V ↦ v ≠ F.a.1 ∧ v ≠ F.b.1)).connectedComponentMk
        zD).supp := by
    change (⟨w, hwa, hwb⟩ : {v : V // v ≠ F.a.1 ∧ v ≠ F.b.1}) ∈
      ((G.induce (fun v : V ↦ v ≠ F.a.1 ∧ v ≠ F.b.1)).connectedComponentMk
        ⟨z.1, (fun h ↦ (F.mem_side_iff.mp hz).1 (Subtype.ext h)),
          (fun h ↦ (F.mem_side_iff.mp hz).2.1 (Subtype.ext h))⟩).supp at hwK
    simpa only [wD, zD] using hwK
  exact E.ambient_component_subset_nested_side F hleft hright hz hwK'

/-- A cardinality-minimal two-cut end has a three-connected virtual-edge
torso.  This is the connectivity conclusion of AHT Lemma 4.4. -/
theorem torso_vertexThreeConnected_of_minimalAvoiding
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v) :
    VertexThreeConnected E.torso := by
  classical
  refine ⟨E.four_le_card_torso hminSide, E.torso_connected hdelete, ?_⟩
  intro c d hcd
  by_contra hdisc
  have hnot : ¬VertexThreeConnected E.torso := by
    intro hthree
    exact hdisc (hthree.2.2 c d hcd)
  obtain ⟨F₀⟩ := exists_twoCutEnd_of_not_vertexThreeConnected
    (E.four_le_card_torso hminSide) (E.torso_connected hdelete) hnot
  obtain ⟨F, hleft, hright⟩ :=
    exists_twoCutEnd_avoiding_adjacent F₀ E.torso_boundary_adj
  obtain ⟨z, hz⟩ := F.side_nonempty
  let E' : TwoCutEnd G := nestedAmbientEnd E F hleft hright z hz
  have hsub {w : V} (hw : w ∈ E'.side) :
      ∃ hwE : w ∈ E.verts,
        (⟨w, hwE⟩ : {v : V // v ∈ E.verts}) ∈ F.side := by
    simpa [E'] using E.nestedAmbientEnd_side F hleft hright z hz hw
  have havoid : x₀ = E'.a ∨ x₀ = E'.b ∨ x₀ ∉ E'.side := by
    right
    right
    intro hx
    obtain ⟨hxE, hxF⟩ := hsub hx
    rcases hminimal.1 with hxa | hxb | hxout
    · apply hleft
      simpa [hxa] using hxF
    · apply hright
      simpa [hxb] using hxF
    · apply hxout
      have hxna : x₀ ≠ E.a := by
        intro h
        apply hleft
        simpa [h] using hxF
      have hxnb : x₀ ≠ E.b := by
        intro h
        apply hright
        simpa [h] using hxF
      exact E.mem_side_of_mem_verts hxE hxna hxnb
  let toF : {w : V // w ∈ E'.verts} →
      {q : {v : V // v ∈ E.verts} // q ∈ F.verts} := fun w ↦ by
    by_cases hwa : w.1 = F.a.1
    · exact ⟨F.a, F.left_mem_verts⟩
    by_cases hwb : w.1 = F.b.1
    · exact ⟨F.b, F.right_mem_verts⟩
    have hwa' : w.1 ≠ E'.a := by simpa [E', nestedAmbientEnd] using hwa
    have hwb' : w.1 ≠ E'.b := by simpa [E', nestedAmbientEnd] using hwb
    have hwside : w.1 ∈ E'.side :=
      E'.mem_side_of_mem_verts w.2 hwa' hwb'
    let hwP := hsub hwside
    let hwE : w.1 ∈ E.verts := Classical.choose hwP
    have hwF : (⟨w.1, hwE⟩ : {v : V // v ∈ E.verts}) ∈ F.side :=
      Classical.choose_spec hwP
    exact ⟨⟨w.1, hwE⟩, Set.mem_insert_iff.mpr <| Or.inr <|
      Set.mem_insert_iff.mpr <| Or.inr hwF⟩
  have htoFval (w : {q : V // q ∈ E'.verts}) : (toF w).1.1 = w.1 := by
    simp only [toF]
    split <;> rename_i hwa
    · exact hwa.symm
    split <;> rename_i hwb
    · exact hwb.symm
    · rfl
  have hinj : Function.Injective toF := by
    intro r s hrs
    apply Subtype.ext
    rw [← htoFval r, ← htoFval s, hrs]
  have hcardSub : Fintype.card {w : V // w ∈ E'.verts} ≤
      Fintype.card {q : {v : V // v ∈ E.verts} // q ∈ F.verts} :=
    Fintype.card_le_of_injective toF hinj
  have hminCard : Fintype.card {v : V // v ∈ E.verts} ≤
      Fintype.card {w : V // w ∈ E'.verts} := hminimal.2 E' havoid
  have hproperCard :
      Fintype.card {q : {v : V // v ∈ E.verts} // q ∈ F.verts} <
        Fintype.card {v : V // v ∈ E.verts} := F.card_verts_lt
  omega

/-- Adjacency in a one-edge graph identifies the corresponding unordered
pair.  Kept local because the equivalent Mathlib convenience lemma is newer
than the compiled dependency used by this development. -/
private theorem sym2_eq_of_edge_adj
    {W : Type*} {a b u v : W} (h : (SimpleGraph.edge a b).Adj u v) :
    s(a, b) = s(u, v) := by
  rw [SimpleGraph.edge_adj] at h
  rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Sym2.eq_swap

/-- Removing the virtual attachment edge from a torso cycle leaves a simple
path in the actual induced end graph, with exactly the same vertex support.
The orientation is chosen so that the path runs from the right attachment to
the left attachment. -/
private theorem cyclePath_of_mem_virtualEdge
    {root : {v : V // v ∈ E.verts}} {p : E.torso.Walk root root}
    (hp : p.IsCycle)
    (hedge : s(⟨E.a, E.left_mem_verts⟩,
      ⟨E.b, E.right_mem_verts⟩) ∈ p.edges) :
    ∃ q : (G.induce E.verts).Walk
        ⟨E.b, E.right_mem_verts⟩ ⟨E.a, E.left_mem_verts⟩,
      q.IsPath ∧ q.support.toFinset = p.support.toFinset := by
  classical
  let aT : {v : V // v ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  let bT : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  have ha : aT ∈ p.support := p.fst_mem_support_of_mem_edges hedge
  let r := p.rotate aT ha
  have hr : r.IsCycle := hp.rotate ha
  have hedgeR : s(aT, bT) ∈ r.edges := by
    exact (p.rotate_edges aT ha).mem_iff.mpr hedge
  have hrab : r.toSubgraph.Adj aT bT :=
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hedgeR
  obtain ⟨r', hr', hsnd, hverts⟩ :=
    hr.exists_isCycle_snd_verts_eq hrab
  let qT : E.torso.Walk bT aT := r'.tail.copy hsnd rfl
  have hqTpath : qT.IsPath := by
    simpa [qT] using hr'.isPath_tail
  have hqTnoEdge : s(aT, bT) ∉ qT.edges := by
    have hnil : ¬r'.Nil := hr'.not_nil
    have hhead : r'.edges.head (SimpleGraph.Walk.edges_eq_nil.not.mpr hnil) =
        s(aT, bT) := by
      rw [r'.head_edges_eq_mk_start_snd, hsnd]
    have hcons : r'.edges = s(aT, bT) :: r'.edges.tail := by
      rw [← hhead]
      exact (List.cons_head_tail (SimpleGraph.Walk.edges_eq_nil.not.mpr hnil)).symm
    have hnotTail : s(aT, bT) ∉ r'.edges.tail := by
      have hnodup := hr'.isTrail.edges_nodup
      rw [hcons] at hnodup
      exact (List.nodup_cons.mp hnodup).1
    simpa [qT, SimpleGraph.Walk.edges_tail] using hnotTail
  have hqEdges : ∀ e, e ∈ qT.edges → e ∈ (G.induce E.verts).edgeSet := by
    intro e
    induction e using Sym2.inductionOn with
    | hf u v =>
        intro huv
        change (G.induce E.verts).Adj u v
        have huvT : E.torso.Adj u v := qT.adj_of_mem_edges huv
        rcases huvT with huvG | huvVirtual
        · exact huvG
        · have heq : s(aT, bT) = s(u, v) :=
            sym2_eq_of_edge_adj huvVirtual
          exact False.elim (hqTnoEdge (by rw [heq]; exact huv))
  let q : (G.induce E.verts).Walk bT aT := qT.transfer (G.induce E.verts) hqEdges
  have hqpath : q.IsPath := hqTpath.transfer hqEdges
  have haTail : aT ∈ r'.tail.support := by
    exact r'.tail.end_mem_support
  have htailSupport : r'.tail.support.toFinset = r'.support.toFinset := by
    have hconsSupport := r'.cons_support_tail hr'.not_nil
    rw [← hconsSupport]
    simp [haTail]
  have hqSupport : q.support.toFinset = p.support.toFinset := by
    ext y
    simp only [q, SimpleGraph.Walk.support_transfer, qT,
      SimpleGraph.Walk.support_copy, List.mem_toFinset]
    rw [show y ∈ r'.tail.support ↔ y ∈ r'.support by
      simpa only [List.mem_toFinset] using
        Finset.ext_iff.mp htailSupport y]
    rw [← r'.mem_verts_toSubgraph, hverts, r.mem_verts_toSubgraph]
    exact p.mem_support_rotate_iff aT ha
  exact ⟨q, hqpath, hqSupport⟩

/-- A second component of the deleted graph supplies an attachment path whose
internal vertices lie outside the chosen end. -/
private theorem exists_external_attachment_path
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected) :
    ∃ r : G.Walk E.a E.b, r.IsPath ∧
      ∀ y, y ∈ r.support → y ∈ E.verts → y = E.a ∨ y = E.b := by
  classical
  obtain ⟨z, hzOutside⟩ := E.proper
  obtain ⟨v, hvE⟩ := E.component.nonempty_supp
  let K' :=
    (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk z
  have hKne : K' ≠ E.component := by
    intro h
    apply hzOutside
    simpa only [K', SimpleGraph.ConnectedComponent.mem_supp_iff] using h
  have hvOutside : v ∉ K'.supp := by
    intro hvK'
    apply hKne
    have hvEqK :
        (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk v =
          K' := by
      simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hvK'
    have hvEqE :
        (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk v =
          E.component := by
      simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hvE
    exact hvEqK.symm.trans hvEqE
  let O : TwoCutEnd G :=
    ⟨E.a, E.b, E.boundary_ne, K', ⟨v, hvOutside⟩⟩
  have hsides : Disjoint E.side O.side := by
    rw [Set.disjoint_left]
    intro y hyE hyO
    obtain ⟨hya, hyb, hyEK⟩ := hyE
    obtain ⟨hya', hyb', hyOK⟩ := hyO
    apply hKne
    have hyEqE :
        (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk
            ⟨y, hya, hyb⟩ = E.component := by
      simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hyEK
    have hyEqO :
        (G.induce (fun w : V ↦ w ≠ E.a ∧ w ≠ E.b)).connectedComponentMk
            ⟨y, hya, hyb⟩ = K' := by
      simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hyOK
    exact hyEqO.symm.trans hyEqE
  let aO : {w : V // w ∈ O.verts} := ⟨E.a, O.left_mem_verts⟩
  let bO : {w : V // w ∈ O.verts} := ⟨E.b, O.right_mem_verts⟩
  obtain ⟨rO, hrO⟩ := (O.verts_connected hdelete).exists_isPath aO bO
  let r : G.Walk E.a E.b :=
    rO.map (SimpleGraph.Embedding.induce O.verts).toHom
  have hr : r.IsPath := hrO.map Subtype.val_injective
  refine ⟨r, hr, ?_⟩
  intro y hyr hyEnd
  change y ∈ (rO.map (SimpleGraph.Embedding.induce O.verts).toHom).support at hyr
  rw [SimpleGraph.Walk.support_map] at hyr
  obtain ⟨yO, hyOr, hyval⟩ := List.mem_map.mp hyr
  have hyOmem : yO.1 ∈ O.verts := yO.2
  by_cases hya : y = E.a
  · exact Or.inl hya
  by_cases hyb : y = E.b
  · exact Or.inr hyb
  have hya' : yO.1 ≠ E.a := by
    intro h
    apply hya
    rw [← hyval]
    exact h
  have hyb' : yO.1 ≠ E.b := by
    intro h
    apply hyb
    rw [← hyval]
    exact h
  have hyOside : yO.1 ∈ O.side :=
    O.mem_side_of_mem_verts hyOmem hya' hyb'
  have hyEside : y ∈ E.side := E.mem_side_of_mem_verts hyEnd hya hyb
  have hyOsideY : y ∈ O.side := by
    rw [← hyval]
    exact hyOside
  exact False.elim (Set.disjoint_left.mp hsides hyEside hyOsideY)

/-- The centre-confinement half of AHT Lemma 4.4 in the genuinely virtual
edge case.  A torso wheel centred in the component side lifts by replacing
the virtual rim edge with a path through a different deleted component. -/
theorem almostWheelFreeAt_torso_of_boundary_nonadjacent
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b) :
    AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩ := by
  classical
  intro x hxa hxb hxWheel
  obtain ⟨s₀, p, hp, hxp, hthree⟩ := hxWheel
  let aT : {v : V // v ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  let bT : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  have hxa' : x.1 ≠ E.a := fun h ↦ hxa (Subtype.ext h)
  have hxb' : x.1 ≠ E.b := fun h ↦ hxb (Subtype.ext h)
  by_cases hedge : s(aT, bT) ∈ p.edges
  · obtain ⟨q, hqPath, hqSupport⟩ :=
      E.cyclePath_of_mem_virtualEdge hp hedge
    let qi : G.Walk E.b E.a :=
      q.map (SimpleGraph.Embedding.induce E.verts).toHom
    have hqiPath : qi.IsPath := hqPath.map Subtype.val_injective
    obtain ⟨r, hrPath, hrExternal⟩ :=
      E.exists_external_attachment_path hdelete
    have hbNotQiTail : E.b ∉ qi.support.tail := by
      have hnodup := hqiPath.support_nodup
      rw [← qi.cons_tail_support] at hnodup
      exact (List.nodup_cons.mp hnodup).1
    have haNotRTail : E.a ∉ r.support.tail := by
      have hnodup := hrPath.support_nodup
      rw [← r.cons_tail_support] at hnodup
      exact (List.nodup_cons.mp hnodup).1
    have hdisj : qi.support.tail.Disjoint r.support.tail := by
      rw [List.disjoint_left]
      intro y hyq hyr
      have hyqSupport : y ∈ qi.support := List.mem_of_mem_tail hyq
      have hyrSupport : y ∈ r.support := List.mem_of_mem_tail hyr
      have hyEnd : y ∈ E.verts := by
        change y ∈ (q.map (SimpleGraph.Embedding.induce E.verts).toHom).support at hyqSupport
        rw [SimpleGraph.Walk.support_map] at hyqSupport
        obtain ⟨yE, -, hyval⟩ := List.mem_map.mp hyqSupport
        rw [← hyval]
        exact yE.2
      rcases hrExternal y hyrSupport hyEnd with hya | hyb
      · exact haNotRTail (hya ▸ hyr)
      · exact hbNotQiTail (hyb ▸ hyq)
    have hqLong : 1 < qi.length := by
      have hne : E.b ≠ E.a := E.boundary_ne.symm
      by_contra hle
      have hle' : qi.length ≤ 1 := Nat.le_of_not_gt hle
      have hnzero : qi.length ≠ 0 := by
        intro hzero
        exact hne (SimpleGraph.Walk.eq_of_length_eq_zero hzero)
      have heq : qi.length = 1 := by omega
      have hba : G.Adj E.b E.a :=
        SimpleGraph.Walk.adj_of_length_eq_one heq
      exact hab hba.symm
    let cycle : G.Walk E.b E.b := qi.append r
    have hcycle : cycle.IsCycle :=
      hqiPath.isCycle_append hrPath hdisj (Or.inl hqLong)
    have hxNotQi : x.1 ∉ qi.support := by
      intro hxq
      change x.1 ∈ (q.map (SimpleGraph.Embedding.induce E.verts).toHom).support at hxq
      rw [SimpleGraph.Walk.support_map] at hxq
      obtain ⟨y, hyq, hyval⟩ := List.mem_map.mp hxq
      have hyq' : y ∈ q.support.toFinset := by simpa using hyq
      have hyp : y ∈ p.support.toFinset := by rwa [← hqSupport]
      apply hxp
      have : y = x := Subtype.ext hyval
      simpa [this] using hyp
    have hxNotR : x.1 ∉ r.support := by
      intro hxr
      have hxEnd : x.1 ∈ E.verts := x.2
      rcases hrExternal x.1 hxr hxEnd with h | h
      · exact hxa' h
      · exact hxb' h
    have hxNotCycle : x.1 ∉ cycle.support := by
      intro hx
      change x.1 ∈ (qi.append r).support at hx
      rw [SimpleGraph.Walk.mem_support_append_iff] at hx
      exact hx.elim hxNotQi hxNotR
    have htwo : 2 <
        (E.torso.neighborFinset x ∩ p.support.toFinset).card := by
      omega
    obtain ⟨y₁, y₂, y₃, hy₁, hy₂, hy₃, hy₁₂, hy₁₃, hy₂₃⟩ :=
      Finset.two_lt_card_iff.mp htwo
    have map_mem (y : {v : V // v ∈ E.verts})
        (hy : y ∈ E.torso.neighborFinset x ∩ p.support.toFinset) :
        y.1 ∈ G.neighborFinset x.1 ∩ cycle.support.toFinset := by
      rw [Finset.mem_inter] at hy ⊢
      constructor
      · rw [SimpleGraph.mem_neighborFinset] at hy ⊢
        exact (AHTTorso.torsoOn_adj_iff_of_ne_boundary hxa' hxb').mp hy.1
      · have hyq : y ∈ q.support.toFinset := by
          rw [hqSupport]
          exact hy.2
        have hyqi : y.1 ∈ qi.support.toFinset := by
          rw [List.mem_toFinset]
          change y.1 ∈ (q.map (SimpleGraph.Embedding.induce E.verts).toHom).support
          rw [SimpleGraph.Walk.support_map]
          exact List.mem_map.mpr ⟨y, by simpa using hyq, rfl⟩
        simp only [cycle, List.mem_toFinset,
          SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inl (by simpa using hyqi)
    have hthreeG : 2 <
        (G.neighborFinset x.1 ∩ cycle.support.toFinset).card := by
      apply Finset.two_lt_card_iff.mpr
      exact ⟨y₁.1, y₂.1, y₃.1, map_mem y₁ hy₁, map_mem y₂ hy₂,
        map_mem y₃ hy₃, Subtype.val_injective.ne hy₁₂,
        Subtype.val_injective.ne hy₁₃, Subtype.val_injective.ne hy₂₃⟩
    exact hnoWheel ⟨E.b, cycle, x.1, hcycle, hxNotCycle, by omega⟩
  · have hpEdges : ∀ e, e ∈ p.edges → e ∈ (G.induce E.verts).edgeSet := by
      intro e
      induction e using Sym2.inductionOn with
      | hf u v =>
          intro huv
          change (G.induce E.verts).Adj u v
          have huvT : E.torso.Adj u v := p.adj_of_mem_edges huv
          rcases huvT with huvG | huvVirtual
          · exact huvG
          · have heq : s(aT, bT) = s(u, v) :=
              sym2_eq_of_edge_adj huvVirtual
            exact False.elim (hedge (by rw [heq]; exact huv))
    let pI : (G.induce E.verts).Walk s₀ s₀ :=
      p.transfer (G.induce E.verts) hpEdges
    have hpI : pI.IsCycle := hp.transfer hpEdges
    have hxNotPI : x ∉ pI.support := by simpa [pI] using hxp
    have hfinEq :
        (G.induce E.verts).neighborFinset x ∩ pI.support.toFinset =
          E.torso.neighborFinset x ∩ p.support.toFinset := by
      ext y
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.induce_adj, List.mem_toFinset, pI,
        SimpleGraph.Walk.support_transfer]
      rw [AHTTorso.torsoOn_adj_iff_of_ne_boundary hxa' hxb']
    have hthreeI : 3 ≤
        ((G.induce E.verts).neighborFinset x ∩ pI.support.toFinset).card := by
      rw [hfinEq]
      exact hthree
    exact hnoWheel (HasWheelWitness.induce E.verts
      ⟨s₀, pI, x, hpI, hxNotPI, hthreeI⟩)

/-- If the attachment edge is already present in the ambient graph, adding
it to the torso changes nothing: the torso is the induced end graph. -/
theorem torso_eq_induce_of_boundary_adj (hab : G.Adj E.a E.b) :
    E.torso = G.induce E.verts := by
  ext u v
  simp only [torso, AHTTorso.torsoOn, SimpleGraph.sup_adj,
    SimpleGraph.induce_adj, SimpleGraph.edge_adj]
  constructor
  · rintro (huv | huv)
    · exact huv
    · rcases huv with ⟨hua, hvb⟩ | ⟨hub, hva⟩
      · have hua' : u.1 = E.a := congrArg Subtype.val hua
        have hvb' : v.1 = E.b := congrArg Subtype.val hvb
        simpa [hua', hvb'] using hab
      · have hub' : u.1 = E.b := congrArg Subtype.val hub
        have hva' : v.1 = E.a := congrArg Subtype.val hva
        simpa [hub', hva'] using hab.symm
  · exact Or.inl

/-- In the actual-edge case, an ambient wheel-free graph gives a genuinely
wheel-free end torso. -/
theorem noWheel_torso_of_boundary_adj
    (hnoWheel : ¬HasWheelWitness G) (hab : G.Adj E.a E.b) :
    ¬HasWheelWitness E.torso := by
  intro hW
  have hle : E.torso ≤ G.induce E.verts := by
    rw [E.torso_eq_induce_of_boundary_adj hab]
  have hWind : HasWheelWitness (G.induce E.verts) :=
    HasWheelWitness.mono hle hW
  exact hnoWheel (HasWheelWitness.induce E.verts hWind)

/-- All wheel centres of an end torso are attachments.  Together with
`torso_vertexThreeConnected_of_minimalAvoiding`, this is the full structural
content of AHT Lemma 4.4 used in Section 7. -/
theorem almostWheelFreeAt_torso
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hnoWheel : ¬HasWheelWitness G) :
    AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩ := by
  by_cases hab : G.Adj E.a E.b
  · intro x _ _ hx
    exact E.noWheel_torso_of_boundary_adj hnoWheel hab
      (hasWheelWitness_iff_exists_center.mpr ⟨x, hx⟩)
  · exact E.almostWheelFreeAt_torso_of_boundary_nonadjacent
      hdelete hnoWheel hab

/-- Source-exact end-torso conclusion of AHT Lemma 4.4 for a cardinality-
minimal two-cut end. -/
theorem minimalEnd_torso_structure
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G) :
    VertexThreeConnected E.torso ∧
      AlmostWheelFreeAt E.torso
        ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩ :=
  ⟨E.torso_vertexThreeConnected_of_minimalAvoiding hminimal hdelete hminSide,
    E.almostWheelFreeAt_torso hdelete hnoWheel⟩

/-- Consequently the actual-edge torso satisfies the source-exact
almost-wheel-free predicate through its wheel-free alternative. -/
theorem almostWheelFree_torso_of_boundary_adj
    (hnoWheel : ¬HasWheelWitness G) (hab : G.Adj E.a E.b) :
    AlmostWheelFree E.torso :=
  almostWheelFree_of_noWheel (E.noWheel_torso_of_boundary_adj hnoWheel hab)

/-- A concrete degree-three false-twin pair wholly inside an end torso. -/
def HasInteriorFalseTwins : Prop :=
  ∃ u v : {w : V // w ∈ E.verts},
    AreFalseTwins E.torso u v ∧ E.torso.degree u = 3 ∧
      u.1 ≠ E.a ∧ u.1 ≠ E.b ∧ v.1 ≠ E.a ∧ v.1 ≠ E.b

/-- Interior false twins in an end torso lift, with their degree unchanged,
to the ambient graph. -/
theorem interiorFalseTwins_lift (hpair : E.HasInteriorFalseTwins) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  obtain ⟨u, v, htwin, hdeg, hua, hub, hva, hvb⟩ := hpair
  have huside : u.1 ∈ E.side := E.mem_side_of_mem_verts u.2 hua hub
  have hvside : v.1 ∈ E.side := E.mem_side_of_mem_verts v.2 hva hvb
  have hNu : G.neighborSet u.1 ⊆ E.verts := E.neighborSet_subset_verts huside
  have hNv : G.neighborSet v.1 ⊆ E.verts := E.neighborSet_subset_verts hvside
  have htwinG : AreFalseTwins G u.1 v.1 :=
    AHTTorso.falseTwins_lift hua hub hva hvb hNu hNv htwin
  have hdegG : G.degree u.1 = 3 := by
    rw [← AHTTorso.degree_torsoOn_eq hua hub hNu]
    exact hdeg
  exact ⟨u.1, v.1, htwinG, hdegG⟩

/-- The pointed strengthening of the interior lift: minimal-end avoidance
ensures that both lifted side vertices avoid the distinguished vertex. -/
theorem interiorFalseTwins_lift_away
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hpair : E.HasInteriorFalseTwins) :
    AHTSection7.HasFalseTwinsAway G x₀ := by
  obtain ⟨u, v, htwin, hdeg, hua, hub, hva, hvb⟩ := hpair
  have huside : u.1 ∈ E.side := E.mem_side_of_mem_verts u.2 hua hub
  have hvside : v.1 ∈ E.side := E.mem_side_of_mem_verts v.2 hva hvb
  have hNu : G.neighborSet u.1 ⊆ E.verts := E.neighborSet_subset_verts huside
  have hNv : G.neighborSet v.1 ⊆ E.verts := E.neighborSet_subset_verts hvside
  have htwinG : AreFalseTwins G u.1 v.1 :=
    AHTTorso.falseTwins_lift hua hub hva hvb hNu hNv htwin
  have hdegG : G.degree u.1 = 3 := by
    rw [← AHTTorso.degree_torsoOn_eq hua hub hNu]
    exact hdeg
  exact ⟨u.1, v.1, htwinG, hdegG,
    hminimal.ne_exception_of_mem_side huside,
    hminimal.ne_exception_of_mem_side hvside⟩

/-- If a two-pair Section 6 output has its first pair away from both
attachments, it immediately gives an interior torso pair. -/
theorem interiorFalseTwins_of_firstPair
    (T : TwoDisjointFalseTwinPairs E.torso)
    (hu : T.u.1 ≠ E.a ∧ T.u.1 ≠ E.b)
    (hv : T.v.1 ≠ E.a ∧ T.v.1 ≠ E.b) :
    E.HasInteriorFalseTwins := by
  exact ⟨T.u, T.v, T.twins_uv, T.degree_u,
    hu.1, hu.2, hv.1, hv.2⟩

/-- The symmetric conversion for the second pair of a Section 6 output. -/
theorem interiorFalseTwins_of_secondPair
    (T : TwoDisjointFalseTwinPairs E.torso)
    (hx : T.x.1 ≠ E.a ∧ T.x.1 ≠ E.b)
    (hy : T.y.1 ≠ E.a ∧ T.y.1 ≠ E.b) :
    E.HasInteriorFalseTwins := by
  exact ⟨T.x, T.y, T.twins_xy, T.degree_x,
    hx.1, hx.2, hy.1, hy.2⟩

/-- The `K₃,₃` terminal case of the AHT boundary argument.  Two vertices
in one bipartition class can always be chosen away from the two attachments;
the resulting pair lifts to the ambient graph. -/
theorem falseTwins_lift_of_k33_torso
    (e : completeBipartiteGraph (Fin 3) (Fin 3) ≃g E.torso) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  obtain ⟨p, q, hpq, hdeg, hpa, hpb, hqa, hqb⟩ :=
    AHTSection7.exists_falseTwins_avoiding_two_of_k33_iso
      E.torso e
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩
  apply E.interiorFalseTwins_lift
  exact ⟨p, q, hpq, hdeg,
    (fun h ↦ hpa (Subtype.ext h)),
    (fun h ↦ hpb (Subtype.ext h)),
    (fun h ↦ hqa (Subtype.ext h)),
    (fun h ↦ hqb (Subtype.ext h))⟩

/-- Pointed version of the `K₃,₃` terminal: the selected same-part pair is
interior, hence its ambient lift avoids the distinguished vertex. -/
theorem falseTwinsAway_of_k33_torso
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (e : completeBipartiteGraph (Fin 3) (Fin 3) ≃g E.torso) :
    AHTSection7.HasFalseTwinsAway G x₀ := by
  obtain ⟨p, q, hpq, hdeg, hpa, hpb, hqa, hqb⟩ :=
    AHTSection7.exists_falseTwins_avoiding_two_of_k33_iso
      E.torso e
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩
  apply E.interiorFalseTwins_lift_away hminimal
  exact ⟨p, q, hpq, hdeg,
    (fun h ↦ hpa (Subtype.ext h)),
    (fun h ↦ hpb (Subtype.ext h)),
    (fun h ↦ hqa (Subtype.ext h)),
    (fun h ↦ hqb (Subtype.ext h))⟩

/-- A walk from the strict left side of a separation to its strict right
side must meet the separator.  This local copy keeps the end-torso module
independent of the compilation order of the Section 6.4 development. -/
private theorem walk_meets_separator
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (s : AHTSeparation H) {u v : W} (p : H.Walk u v)
    (hu : u ∈ s.left \ s.right) (hv : v ∈ s.right \ s.left) :
    ∃ x, x ∈ p.support ∧ x ∈ s.separator := by
  induction p with
  | nil =>
      rw [Finset.mem_sdiff] at hu hv
      exact (hv.2 hu.1).elim
  | @cons u w v huw p ih =>
      rw [Finset.mem_sdiff] at hu hv
      rcases s.mem_left_or_mem_right w with hwL | hwR
      · by_cases hwR : w ∈ s.right
        · exact ⟨w, by simp, Finset.mem_inter.2 ⟨hwL, hwR⟩⟩
        · obtain ⟨x, hxp, hxs⟩ := ih
              (Finset.mem_sdiff.2 ⟨hwL, hwR⟩) (Finset.mem_sdiff.2 hv)
          exact ⟨x, by simp [hxp], hxs⟩
      · by_cases hwL : w ∈ s.left
        · exact ⟨w, by simp, Finset.mem_inter.2 ⟨hwL, hwR⟩⟩
        · exact (s.not_adj hu.1 hu.2 hwR hwL huw).elim

/-- Connectivity after deletion of every two distinct vertices implies the
separation formulation of three-connectivity used by AHT Lemma 6.2. -/
private theorem isThreeConnected_of_vertexThreeConnected_local
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (hH : VertexThreeConnected H) : IsThreeConnected H := by
  refine ⟨Nat.lt_of_succ_le hH.1, ?_⟩
  intro s hs
  by_contra horder
  have hsepCard : s.separator.card ≤ 2 := by
    have hlt : s.order < 3 := Nat.lt_of_not_ge horder
    change s.separator.card ≤ 2
    change s.separator.card < 3 at hlt
    omega
  obtain ⟨u, hu⟩ := hs.1
  obtain ⟨v, hv⟩ := hs.2
  have huv : u ≠ v := by
    intro huv
    subst v
    exact (Finset.mem_sdiff.1 hv).2 (Finset.mem_sdiff.1 hu).1
  let T : Finset W := Finset.univ \ {u, v}
  have hsepT : s.separator ⊆ T := by
    intro x hx
    have hxLR := Finset.mem_inter.1 hx
    have hxu : x ≠ u := by
      intro hxu
      subst x
      exact (Finset.mem_sdiff.1 hu).2 hxLR.2
    have hxv : x ≠ v := by
      intro hxv
      subst x
      exact (Finset.mem_sdiff.1 hv).2 hxLR.1
    simp [T, hxu, hxv]
  have hcardT : 2 ≤ T.card := by
    have hcard := hH.1
    have hpair : ({u, v} : Finset W).card = 2 := by simp [huv]
    have hcardEq : T.card = Fintype.card W - 2 := by
      simp [T, Finset.card_sdiff, hpair]
    rw [hcardEq]
    omega
  obtain ⟨D, hsepD, hDT, hcardD⟩ :=
    Finset.exists_subsuperset_card_eq hsepT hsepCard hcardT
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcardD
  have huD : u ∉ ({x, y} : Finset W) := by
    intro huD
    have huT := hDT huD
    simpa [T] using huT
  have hvD : v ∉ ({x, y} : Finset W) := by
    intro hvD
    have hvT := hDT hvD
    simpa [T] using hvT
  let K := H.induce (fun z : W ↦ z ≠ x ∧ z ≠ y)
  let uK : {z : W // z ≠ x ∧ z ≠ y} := ⟨u, by simpa using huD⟩
  let vK : {z : W // z ≠ x ∧ z ≠ y} := ⟨v, by simpa using hvD⟩
  have hconnK : K.Connected := hH.2.2 x y hxy
  obtain ⟨p⟩ := hconnK uK vK
  let f : K →g H :=
    { toFun := Subtype.val
      map_rel' := by intro z w hzw; exact hzw }
  let q : H.Walk u v := p.map f
  obtain ⟨z, hzq, hzs⟩ := walk_meets_separator s q hu hv
  have hzD : z ∈ ({x, y} : Finset W) := hsepD hzs
  have hzNotD : z ∉ ({x, y} : Finset W) := by
    dsimp [q] at hzq
    rw [SimpleGraph.Walk.support_map] at hzq
    obtain ⟨zK, -, hzEq⟩ := List.mem_map.mp hzq
    subst z
    have hf : f zK = zK.1 := rfl
    rw [hf]
    have hzKprop : (zK : W) ≠ x ∧ (zK : W) ≠ y := zK.property
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hzKprop
  exact hzNotD hzD

/-- The numerical split in the nonedge branch of AHT Section 7.  Either both
attachments have torso degree three (so centre confinement upgrades to
`AlmostWheelFree`), or one attachment already has degree at least three in
the actual induced end graph `J`, which is the branch where the induction
hypothesis is applied to `J`. -/
theorem boundary_degree_dichotomy
    (hthree : VertexThreeConnected E.torso)
    (hab : ¬G.Adj E.a E.b) :
    (E.torso.degree ⟨E.a, E.left_mem_verts⟩ = 3 ∧
      E.torso.degree ⟨E.b, E.right_mem_verts⟩ = 3) ∨
      3 ≤ E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩ ∨
      3 ≤ E.inducedEnd.degree ⟨E.b, E.right_mem_verts⟩ := by
  have hthree' := isThreeConnected_of_vertexThreeConnected_local hthree
  have hda : 3 ≤ E.torso.degree ⟨E.a, E.left_mem_verts⟩ :=
    hthree'.degree_ge _
  have hdb : 3 ≤ E.torso.degree ⟨E.b, E.right_mem_verts⟩ :=
    hthree'.degree_ge _
  by_cases hea : E.torso.degree ⟨E.a, E.left_mem_verts⟩ = 3
  · by_cases heb : E.torso.degree ⟨E.b, E.right_mem_verts⟩ = 3
    · exact Or.inl ⟨hea, heb⟩
    · right
      right
      rw [E.degree_torso_right_eq_degree_inducedEnd_add_one hab] at hdb heb
      omega
  · right
    left
    rw [E.degree_torso_left_eq_degree_inducedEnd_add_one hab] at hda hea
    omega

/-- The complete structural form of the nonedge boundary-degree split for a
minimal end: the low-boundary branch is already a three-connected
almost-wheel-free torso, while the other branch identifies a boundary that
retains degree at least three in the smaller actual end graph. -/
theorem minimalEnd_almostWheelFree_or_induced_boundary_degree
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b) :
    (VertexThreeConnected E.torso ∧ AlmostWheelFree E.torso) ∨
      3 ≤ E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩ ∨
      3 ≤ E.inducedEnd.degree ⟨E.b, E.right_mem_verts⟩ := by
  have hstruct := E.minimalEnd_torso_structure
    hminimal hdelete hminSide hnoWheel
  rcases E.boundary_degree_dichotomy hstruct.1 hab with hlow | hhigh
  · exact Or.inl ⟨hstruct.1,
      E.almostWheelFree_torso_of_centres_of_boundary_degrees
        hstruct.2 hlow.1 hlow.2⟩
  · exact Or.inr hhigh

/-! ## The boundary-coincidence part of Claim (10) -/

/-- Two paths meeting only at their common endpoint concatenate to a path.
Kept local because the identical routing helper in `AHTK32Routing` is
private to that namespace. -/
private theorem Walk.IsPath.append_of_meet_only_endpoint
    {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  have hpN := hp.support_nodup
  have hqN := hq.support_nodup
  refine ⟨hpN, hqN.tail, ?_⟩
  intro x hxp y hyq hxy
  subst y
  have hxb : x = b := hinter x hxp (List.mem_of_mem_tail hyq)
  subst x
  rw [q.support_eq_cons] at hqN
  exact (List.nodup_cons.mp hqN).1 hyq

/-- Two paths with the same ends and no other common vertex form a simple
cycle as soon as the first path has a displayed internal vertex. -/
private theorem Walk.IsPath.isCycle_append_reverse_of_clean_meet
    {s t w : V} {p q : G.Walk s t} (hp : p.IsPath) (hq : q.IsPath)
    (hw : w ∈ p.support) (hws : w ≠ s) (hwt : w ≠ t)
    (hmeet : ∀ a, a ∈ p.support → a ∈ q.support →
      a = s ∨ a = t) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse
  · rw [List.disjoint_left]
    intro a hap haqr
    have hap' : a ∈ p.support := List.mem_of_mem_tail hap
    have haq' : a ∈ q.support := by
      have : a ∈ q.reverse.support := List.mem_of_mem_tail haqr
      simpa only [Walk.support_reverse, List.mem_reverse] using this
    rcases hmeet a hap' haq' with rfl | rfl
    · have hnd := hp.support_nodup
      rw [← p.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 hap
    · have hnd := hq.reverse.support_nodup
      rw [← q.reverse.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 haqr
  · left
    by_contra hlen
    have hle : p.length ≤ 1 := by omega
    have hends : p.support = [s, t] ∨ s = t := by
      cases p with
      | nil => exact Or.inr rfl
      | @cons _ a _ hadj r =>
          cases r with
          | nil => simp
          | @cons _ b _ hab r => simp at hle
    rcases hends with hsupp | hst
    · have hwst : w = s ∨ w = t := by simpa [hsupp] using hw
      exact hwst.elim hws hwt
    · subst t
      have hpnil : p = .nil := Walk.isPath_iff_eq_nil.mp hp
      subst p
      exact hws (by simpa using hw)

/-- Cutting a simple path at its final vertex returns the original path. -/
private theorem Walk.IsPath.takeUntil_end_eq_local
    {a b : V} {p : G.Walk a b} (hp : p.IsPath) :
    p.takeUntil b p.end_mem_support = p := by
  have hdrop : (p.dropUntil b p.end_mem_support).IsPath :=
    hp.dropUntil p.end_mem_support
  have hnil : p.dropUntil b p.end_mem_support = (.nil : G.Walk b b) :=
    Walk.isPath_iff_eq_nil.mp hdrop
  have hspec := p.take_spec p.end_mem_support
  simpa only [hnil, Walk.append_nil] using hspec

/-- A simple path cannot contain an internal vertex whose available
neighbours on the path are only the two endpoints and also contain a fourth,
distinct displayed vertex.  The two path neighbours force the path to have
length two. -/
theorem Walk.IsPath.not_mem_support_of_neighbors_subset_endpoints_of_extra
    {s t r w : V} {p : G.Walk s t} (hp : p.IsPath) (hst : s ≠ t)
    (hN : p.toSubgraph.neighborSet r ⊆ ({s, t} : Set V))
    (hrs : r ≠ s) (hrt : r ≠ t)
    (hwp : w ∈ p.support) (hws : w ≠ s) (hwt : w ≠ t)
    (hwr : w ≠ r) : r ∉ p.support := by
  intro hrp
  rw [Walk.mem_support_iff_exists_getVert] at hrp hwp
  obtain ⟨i, rfl, hile⟩ := hrp
  obtain ⟨j, rfl, hjle⟩ := hwp
  have hi0 : i ≠ 0 := by
    intro h
    subst i
    exact hrs (by simp)
  have hilast : i ≠ p.length := by
    intro h
    subst i
    exact hrt (by simp)
  have hilt : i < p.length := lt_of_le_of_ne hile hilast
  have heq : p.toSubgraph.neighborSet (p.getVert i) =
      ({s, t} : Set V) := by
    apply Set.eq_of_subset_of_ncard_le hN
    rw [hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt,
      Set.ncard_pair hst]
  have hsAdj : p.toSubgraph.Adj s (p.getVert i) := by
    have hsMem : s ∈ p.toSubgraph.neighborSet (p.getVert i) := by
      rw [heq]
      simp
    exact hsMem.symm
  have htAdj : p.toSubgraph.Adj t (p.getVert i) := by
    have htMem : t ∈ p.toSubgraph.neighborSet (p.getVert i) := by
      rw [heq]
      simp
    exact htMem.symm
  have hsnd : p.snd = p.getVert i :=
    hp.snd_of_toSubgraph_adj hsAdj
  have honeLe : 1 ≤ p.length := by omega
  have hOneEq : 1 = i :=
    hp.getVert_injOn honeLe hile hsnd
  have hiOne : i = 1 := hOneEq.symm
  have htAdjR : p.reverse.toSubgraph.Adj t (p.getVert i) := by
    simpa only [Walk.toSubgraph_reverse] using htAdj
  have hpen : p.penultimate = p.getVert i := by
    simpa only [Walk.snd_reverse] using
      hp.reverse.snd_of_toSubgraph_adj htAdjR
  have hpredLe : p.length - 1 ≤ p.length := Nat.sub_le _ _
  have hPredEq : p.length - 1 = i :=
    hp.getVert_injOn hpredLe hile hpen
  have hlen : p.length = 2 := by omega
  have hj0 : j ≠ 0 := by
    intro h
    subst j
    exact hws (by simp)
  have hjlast : j ≠ p.length := by
    intro h
    subst j
    exact hwt (by simp)
  have hji : j ≠ i := by
    intro h
    exact hwr (congrArg p.getVert h)
  omega

/-- A variant for a path whose initial endpoint is known not to be adjacent
to the putative internal vertex.  If all path-neighbours of that vertex are
the two endpoints, path simplicity would force the initial endpoint to be
adjacent to it. -/
theorem Walk.IsPath.not_mem_support_of_neighbors_subset_endpoints_of_start_not_adj
    {s t r : V} {p : G.Walk s t} (hp : p.IsPath) (hst : s ≠ t)
    (hN : p.toSubgraph.neighborSet r ⊆ ({s, t} : Set V))
    (hrs : r ≠ s) (hrt : r ≠ t) (hsr : ¬G.Adj s r) :
    r ∉ p.support := by
  intro hrp
  rw [Walk.mem_support_iff_exists_getVert] at hrp
  obtain ⟨i, rfl, hile⟩ := hrp
  have hi0 : i ≠ 0 := by
    intro h
    subst i
    exact hrs (by simp)
  have hilast : i ≠ p.length := by
    intro h
    subst i
    exact hrt (by simp)
  have hilt : i < p.length := lt_of_le_of_ne hile hilast
  have heq : p.toSubgraph.neighborSet (p.getVert i) =
      ({s, t} : Set V) := by
    apply Set.eq_of_subset_of_ncard_le hN
    rw [hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt,
      Set.ncard_pair hst]
  have hsAdj : p.toSubgraph.Adj s (p.getVert i) := by
    have hsMem : s ∈ p.toSubgraph.neighborSet (p.getVert i) := by
      rw [heq]
      simp
    exact hsMem.symm
  exact hsr (p.toSubgraph.adj_sub hsAdj)

/-- Strong first-hit extraction.  Unlike the older convenience theorem,
the returned path is definitionally the `takeUntil` prefix of the supplied
path; this retained equation is what the Claim (10) crossing splice needs. -/
theorem exists_firstHitPrefix_to_finset
    (S : Finset V) {r t : V} (hrS : r ∉ S) (htS : t ∈ S)
    (p : G.Walk r t) (hp : p.IsPath) :
    ∃ s : V, ∃ hs : s ∈ p.support, s ∈ S ∧
      (p.takeUntil s hs).IsPath ∧
      (∀ w, w ∈ (p.takeUntil s hs).support → w ∈ S → w = s) := by
  let P : ℕ → Prop := fun n ↦
    ∃ s : V, ∃ hs : s ∈ p.support,
      s ∈ S ∧ (p.takeUntil s hs).length = n
  have hP : ∃ n, P n := by
    exact ⟨(p.takeUntil t p.end_mem_support).length,
      t, p.end_mem_support, htS, rfl⟩
  let n := Nat.find hP
  obtain ⟨s, hs, hsS, hlen⟩ := Nat.find_spec hP
  refine ⟨s, hs, hsS, hp.takeUntil hs, ?_⟩
  intro w hw hws
  by_contra hne
  have hwp : w ∈ p.support := p.support_takeUntil_subset_support hs hw
  have hminimal : n ≤ (p.takeUntil w hwp).length := by
    apply Nat.find_min'
    exact ⟨w, hwp, hws, rfl⟩
  have hshort : ((p.takeUntil s hs).takeUntil w hw).length <
      (p.takeUntil s hs).length :=
    (p.takeUntil s hs).length_takeUntil_lt_length hw hne
  have heq : (p.takeUntil s hs).takeUntil w hw =
      p.takeUntil w hwp := by
    simpa only using p.takeUntil_takeUntil hs hw
  rw [heq, hlen] at hshort
  exact (Nat.not_lt_of_ge hminimal) hshort

/-- If a first hit of `S` were the final vertex, then no earlier distinct
vertex of the path could lie in `S`.  This is the small ordering fact used
to turn a cross-family intersection witness into a genuine internal hit. -/
theorem firstHit_ne_end_of_distinct_hit
    (S : Finset V) {r t s u : V} (p : G.Walk r t) (hp : p.IsPath)
    (hs : s ∈ p.support)
    (hfirst : ∀ w, w ∈ (p.takeUntil s hs).support → w ∈ S → w = s)
    (hu : u ∈ p.support) (huS : u ∈ S) (hut : u ≠ t) : s ≠ t := by
  intro hst
  subst s
  have hfull : p.takeUntil t hs = p := by
    simpa only using Walk.IsPath.takeUntil_end_eq_local hp
  have huPrefix : u ∈ (p.takeUntil t hs).support := by
    simpa only [hfull] using hu
  exact hut (hfirst u huPrefix huS)

/-- Along one walk, one of two support vertices occurs no later than the
other. -/
private theorem mem_takeUntil_or_mem_takeUntil_local
    {a b e f : V} (p : G.Walk a b)
    (he : e ∈ p.support) (hf : f ∈ p.support) :
    f ∈ (p.takeUntil e he).support ∨
      e ∈ (p.takeUntil f hf).support := by
  simp only [Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take,
    List.mem_take_iff_idxOf_lt hf, List.mem_take_iff_idxOf_lt he]
  omega

/-- A clean two-fan and an inside path carrying three displayed neighbours
form a wheel.  This is the path-gluing terminal used in both cases of the
second fan in Claim (10): the two arms form the outside half of the rim and
the inside path forms the other half. -/
theorem hasWheelCenteredAt_of_cleanTwoFan_inside_three
    {e f b k n₁ n₂ n₃ : V}
    (left : G.Walk e b) (right : G.Walk f b)
    (inside : G.Walk e f)
    (hleft : left.IsPath) (hright : right.IsPath)
    (hinside : inside.IsPath)
    (hef : e ≠ f) (hbe : b ≠ e) (hbf : b ≠ f)
    (harms : ∀ w, w ∈ left.support → w ∈ right.support → w = b)
    (hleft_inside : ∀ w, w ∈ left.support →
      w ∈ inside.support → w = e)
    (hright_inside : ∀ w, w ∈ right.support →
      w ∈ inside.support → w = f)
    (hkleft : k ∉ left.support) (hkright : k ∉ right.support)
    (hkinside : k ∉ inside.support)
    (hkn₁ : G.Adj k n₁) (hkn₂ : G.Adj k n₂) (hkn₃ : G.Adj k n₃)
    (hn₁ : n₁ ∈ inside.support) (hn₂ : n₂ ∈ inside.support)
    (hn₃ : n₃ ∈ inside.support)
    (hn₁n₂ : n₁ ≠ n₂) (hn₁n₃ : n₁ ≠ n₃) (hn₂n₃ : n₂ ≠ n₃) :
    HasWheelCenteredAt G k := by
  let outside : G.Walk e f := left.append right.reverse
  have houtside : outside.IsPath := by
    apply Walk.IsPath.append_of_meet_only_endpoint hleft hright.reverse
    intro w hwleft hwright
    apply harms w hwleft
    simpa [Walk.support_reverse] using hwright
  have hbOutside : b ∈ outside.support := by
    simp only [outside, Walk.mem_support_append_iff]
    exact Or.inl left.end_mem_support
  have hmeet : ∀ w, w ∈ outside.support →
      w ∈ inside.support → w = e ∨ w = f := by
    intro w hwout hwin
    have hwcases : w ∈ left.support ∨ w ∈ right.support := by
      simpa [outside, Walk.mem_support_append_iff, Walk.support_reverse]
        using hwout
    rcases hwcases with hwleft | hwright
    · exact Or.inl (hleft_inside w hwleft hwin)
    · exact Or.inr (hright_inside w hwright hwin)
  let rim : G.Walk e e := outside.append inside.reverse
  have hrim : rim.IsCycle := by
    exact Walk.IsPath.isCycle_append_reverse_of_clean_meet
      houtside hinside hbOutside hbe hbf hmeet
  have hkrim : k ∉ rim.support := by
    intro hk
    have hkCases : k ∈ outside.support ∨ k ∈ inside.support := by
      simpa [rim, Walk.mem_support_append_iff, Walk.support_reverse] using hk
    rcases hkCases with hkout | hkin
    · have : k ∈ left.support ∨ k ∈ right.support := by
        simpa [outside, Walk.mem_support_append_iff, Walk.support_reverse]
          using hkout
      exact this.elim hkleft hkright
    · exact hkinside hkin
  refine ⟨e, rim, hrim, hkrim, ?_⟩
  have memRim {w : V} (hw : w ∈ inside.support) : w ∈ rim.support := by
    simp only [rim, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse]
    exact Or.inr hw
  have hn₁' : n₁ ∈ G.neighborFinset k ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₁, memRim hn₁⟩
  have hn₂' : n₂ ∈ G.neighborFinset k ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₂, memRim hn₂⟩
  have hn₃' : n₃ ∈ G.neighborFinset k ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₃, memRim hn₃⟩
  have hcard := Finset.two_lt_card_iff.mpr
    ⟨n₁, n₂, n₃, hn₁', hn₂', hn₃', hn₁n₂, hn₁n₃, hn₂n₃⟩
  omega

/-- Centre confinement in a three-connected end torso already makes the
torso triangle-free.  This is the precise form of AHT Lemma 6.1 needed in
the high-boundary branch; no degree assumption on either exceptional
boundary vertex is required. -/
theorem torso_triangleFree_of_vertexThreeConnected_of_centres
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩) :
    AHTTriangleFree E.torso :=
  aht_triangleFree_of_threeConnected_almostWheelFreeAt
    (isThreeConnected_of_vertexThreeConnected_local hthree) hcentres

/-- In the triangle-free end torso, a neighbour of the left attachment is
not adjacent to the right attachment, because the boundary edge is present
virtually. -/
theorem not_torso_adj_right_of_adj_left
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    {x : {v : V // v ∈ E.verts}}
    (hax : E.torso.Adj ⟨E.a, E.left_mem_verts⟩ x) :
    ¬E.torso.Adj ⟨E.b, E.right_mem_verts⟩ x := by
  intro hbx
  exact (E.torso_triangleFree_of_vertexThreeConnected_of_centres
    hthree hcentres) E.torso_boundary_adj hbx hax.symm

/-- Symmetric boundary-neighbour exclusion. -/
theorem not_torso_adj_left_of_adj_right
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    {x : {v : V // v ∈ E.verts}}
    (hbx : E.torso.Adj ⟨E.b, E.right_mem_verts⟩ x) :
    ¬E.torso.Adj ⟨E.a, E.left_mem_verts⟩ x := by
  intro hax
  exact (E.torso_triangleFree_of_vertexThreeConnected_of_centres
    hthree hcentres) E.torso_boundary_adj hbx hax.symm

/-- Two distinct neighbours of the left attachment are nonadjacent in the
end torso. -/
theorem not_torso_adj_of_adj_left
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    {x y : {v : V // v ∈ E.verts}}
    (hax : E.torso.Adj ⟨E.a, E.left_mem_verts⟩ x)
    (hay : E.torso.Adj ⟨E.a, E.left_mem_verts⟩ y) :
    ¬E.torso.Adj x y := by
  intro hxy
  exact (E.torso_triangleFree_of_vertexThreeConnected_of_centres
    hthree hcentres) hax hxy hay.symm

/-- Symmetric nonadjacency of two neighbours of the right attachment. -/
theorem not_torso_adj_of_adj_right
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    {x y : {v : V // v ∈ E.verts}}
    (hbx : E.torso.Adj ⟨E.b, E.right_mem_verts⟩ x)
    (hby : E.torso.Adj ⟨E.b, E.right_mem_verts⟩ y) :
    ¬E.torso.Adj x y := by
  intro hxy
  exact (E.torso_triangleFree_of_vertexThreeConnected_of_centres
    hthree hcentres) hbx hxy hby.symm

/-- The boundary-coincidence subcase of AHT Claim (10).  If the two
attachments were false twins in the actual end graph, every common
interior neighbour `x` would complete the virtual boundary edge to the
triangle `x-a-b`.  Every vertex of a triangle in a three-connected graph is
a wheel centre, contradicting Lemma 4.4's confinement because `x` is an
interior vertex. -/
theorem not_falseTwins_inducedEnd_boundaries_of_left_degree_three
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (_hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b)
    (hdeg : 3 ≤ E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩) :
    ¬AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩ := by
  intro htwin
  let a : {v : V // v ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  let b : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  obtain ⟨x, _y, _z, _hxy, _hxz, _hyz, hax, _hay, _haz, hbx, _hby, _hbz,
      hxa, hxb, _hya, _hyb, _hza, _hzb⟩ :=
    E.exists_three_interior_commonNeighbors_left hab hdeg htwin
  have habT : E.torso.Adj a b := E.torso_boundary_adj
  have haxT : E.torso.Adj a x := Or.inl hax
  have hbxT : E.torso.Adj b x := Or.inl hbx
  have hxC : HasWheelCenteredAt E.torso x :=
    hasWheelCenteredAt_of_triangle_of_isThreeConnected
      (isThreeConnected_of_vertexThreeConnected_local hthree)
      haxT.symm habT hbxT
  exact hcentres x
    (fun h ↦ hxa (congrArg Subtype.val h))
    (fun h ↦ hxb (congrArg Subtype.val h)) hxC

/-- Hence any remaining high-degree false twin of the left attachment is an
interior vertex distinct from the opposite attachment.  This is exactly the
`a' ≠ b` branch singled out after the first paragraph of source Claim (10). -/
theorem left_falseTwin_ne_right_of_degree_three
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b)
    (hdeg : 3 ≤ E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩)
    {a' : {v : V // v ∈ E.verts}}
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a') :
    a' ≠ ⟨E.b, E.right_mem_verts⟩ := by
  intro h
  apply E.not_falseTwins_inducedEnd_boundaries_of_left_degree_three
    hthree hcentres hnoWheel hab hdeg
  simpa [h] using htwin

/-- In the surviving branch of Claim (10), the putative twin `a'` is a
genuine component-side vertex. -/
theorem left_falseTwin_mem_side_of_degree_three
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b)
    (hdeg : 3 ≤ E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩)
    {a' : {v : V // v ∈ E.verts}}
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a') :
    a'.1 ∈ E.side := by
  apply E.mem_side_of_mem_verts a'.2
  · intro h
    apply htwin.1
    exact (Subtype.ext h).symm
  · intro h
    apply E.left_falseTwin_ne_right_of_degree_three
      hthree hcentres hnoWheel hab hdeg htwin
    exact Subtype.ext h

/-- A common interior neighbour `x` of the left attachment and another
vertex has a third neighbour `x'` in the component side.  Three-connectivity
supplies the third neighbour; triangle-freeness excludes the right
attachment, since the virtual edge joins the two boundary vertices. -/
theorem exists_side_thirdNeighbor_of_left_commonNeighbor
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    {x a' : {v : V // v ∈ E.verts}}
    (hax : E.torso.Adj ⟨E.a, E.left_mem_verts⟩ x)
    (ha'x : E.torso.Adj a' x)
    (haa' : (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ≠ a') :
    ∃ x' : {v : V // v ∈ E.verts},
      E.torso.Adj x x' ∧
        x' ≠ ⟨E.a, E.left_mem_verts⟩ ∧ x' ≠ a' ∧
        x'.1 ∈ E.side := by
  let a : {v : V // v ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  let b : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  have hthree' := isThreeConnected_of_vertexThreeConnected_local hthree
  obtain ⟨x', hxx', hxa', hxother⟩ :=
    exists_third_neighbor_of_degree_ge_three
      (G := E.torso) (hthree'.degree_ge x) hax.symm ha'x.symm haa'
  have htri := E.torso_triangleFree_of_vertexThreeConnected_of_centres
    hthree hcentres
  have hxb' : x'.1 ≠ E.b := by
    intro h
    have hx'b : x' = b := Subtype.ext h
    subst x'
    exact htri E.torso_boundary_adj hxx'.symm hax.symm
  have hxaVal : x'.1 ≠ E.a := by
    intro h
    apply hxa'
    exact Subtype.ext h
  exact ⟨x', hxx', hxa', hxother,
    E.mem_side_of_mem_verts x'.2 hxaVal hxb'⟩

/-- The exact finite configuration at the start of the surviving
`a' ≠ b` branch of Claim (10).  The three common neighbours and the extra
neighbour of `x` all lie in the component side, and triangle-freeness keeps
the extra neighbour distinct from the other two common neighbours. -/
structure LeftClaim10Initial
    (a' : {v : V // v ∈ E.verts}) where
  x : {v : V // v ∈ E.verts}
  y : {v : V // v ∈ E.verts}
  z : {v : V // v ∈ E.verts}
  x' : {v : V // v ∈ E.verts}
  x_ne_y : x ≠ y
  x_ne_z : x ≠ z
  y_ne_z : y ≠ z
  left_adj_x : E.inducedEnd.Adj ⟨E.a, E.left_mem_verts⟩ x
  left_adj_y : E.inducedEnd.Adj ⟨E.a, E.left_mem_verts⟩ y
  left_adj_z : E.inducedEnd.Adj ⟨E.a, E.left_mem_verts⟩ z
  twin_adj_x : E.inducedEnd.Adj a' x
  twin_adj_y : E.inducedEnd.Adj a' y
  twin_adj_z : E.inducedEnd.Adj a' z
  next_adj_x : E.torso.Adj x x'
  next_ne_left : x' ≠ ⟨E.a, E.left_mem_verts⟩
  next_ne_twin : x' ≠ a'
  next_ne_y : x' ≠ y
  next_ne_z : x' ≠ z
  twin_mem_side : a'.1 ∈ E.side
  x_mem_side : x.1 ∈ E.side
  y_mem_side : y.1 ∈ E.side
  z_mem_side : z.1 ∈ E.side
  next_mem_side : x'.1 ∈ E.side

/-- Exchange the two common neighbours not used to choose `x'`.  This is
the harmless `y,z` symmetry used twice in the source proof. -/
def LeftClaim10Initial.swapYZ
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a') :
    E.LeftClaim10Initial a' where
  x := C.x
  y := C.z
  z := C.y
  x' := C.x'
  x_ne_y := C.x_ne_z
  x_ne_z := C.x_ne_y
  y_ne_z := C.y_ne_z.symm
  left_adj_x := C.left_adj_x
  left_adj_y := C.left_adj_z
  left_adj_z := C.left_adj_y
  twin_adj_x := C.twin_adj_x
  twin_adj_y := C.twin_adj_z
  twin_adj_z := C.twin_adj_y
  next_adj_x := C.next_adj_x
  next_ne_left := C.next_ne_left
  next_ne_twin := C.next_ne_twin
  next_ne_y := C.next_ne_z
  next_ne_z := C.next_ne_y
  twin_mem_side := C.twin_mem_side
  x_mem_side := C.x_mem_side
  y_mem_side := C.z_mem_side
  z_mem_side := C.y_mem_side
  next_mem_side := C.next_mem_side

/-- At exact degree three, the three displayed common neighbours exhaust
the actual-end neighbourhood of the left attachment. -/
theorem LeftClaim10Initial.inducedEnd_left_neighbors_eq
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a')
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3) :
    E.inducedEnd.neighborFinset ⟨E.a, E.left_mem_verts⟩ =
      {C.x, C.y, C.z} := by
  classical
  have hsubset : ({C.x, C.y, C.z} :
      Finset {v : V // v ∈ E.verts}) ⊆
      E.inducedEnd.neighborFinset ⟨E.a, E.left_mem_verts⟩ := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simpa only [SimpleGraph.mem_neighborFinset] using C.left_adj_x
    · simpa only [SimpleGraph.mem_neighborFinset] using C.left_adj_y
    · simpa only [SimpleGraph.mem_neighborFinset] using C.left_adj_z
  have hcardN :
      (E.inducedEnd.neighborFinset
        ⟨E.a, E.left_mem_verts⟩).card = 3 := by
    rw [E.inducedEnd.card_neighborFinset_eq_degree, hdeg]
  have hcardTriple :
      ({C.x, C.y, C.z} : Finset {v : V // v ∈ E.verts}).card = 3 := by
    simp [C.x_ne_y, C.x_ne_z, C.y_ne_z]
  exact (Finset.eq_of_subset_of_card_le hsubset (by
    rw [hcardN, hcardTriple])).symm

/-- In the torso, the only additional neighbour of the left attachment is
the other boundary vertex. -/
theorem LeftClaim10Initial.torso_left_neighbors_eq
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a')
    (hab : ¬G.Adj E.a E.b)
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3) :
    E.torso.neighborFinset ⟨E.a, E.left_mem_verts⟩ =
      {⟨E.b, E.right_mem_verts⟩, C.x, C.y, C.z} := by
  rw [E.torso_left_neighborFinset_eq_insert hab,
    C.inducedEnd_left_neighbors_eq (E := E) hdeg]

/-- The false twin has the same exact three neighbours in the actual end. -/
theorem LeftClaim10Initial.inducedEnd_twin_neighbors_eq
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a')
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3)
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a') :
    E.inducedEnd.neighborFinset a' = {C.x, C.y, C.z} := by
  calc
    E.inducedEnd.neighborFinset a' =
        E.inducedEnd.neighborFinset ⟨E.a, E.left_mem_verts⟩ :=
      htwin.neighborFinset_eq.symm
    _ = {C.x, C.y, C.z} :=
      C.inducedEnd_left_neighbors_eq (E := E) hdeg

/-- Since the false twin is interior, the virtual edge changes none of its
adjacencies; its torso neighbourhood is still exactly `{x,y,z}`. -/
theorem LeftClaim10Initial.torso_twin_neighbors_eq
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a')
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3)
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a') :
    E.torso.neighborFinset a' = {C.x, C.y, C.z} := by
  have ha : a'.1 ≠ E.a := by
    intro h
    apply E.left_not_mem_side
    rw [← h]
    exact C.twin_mem_side
  have hb : a'.1 ≠ E.b := by
    intro h
    apply E.right_not_mem_side
    rw [← h]
    exact C.twin_mem_side
  calc
    E.torso.neighborFinset a' = E.inducedEnd.neighborFinset a' := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset]
      rw [AHTTorso.torsoOn_adj_iff_of_ne_boundary ha hb]
      rfl
    _ = {C.x, C.y, C.z} :=
      C.inducedEnd_twin_neighbors_eq (E := E) hdeg htwin

/-- The left attachment is distinct from every displayed interior target. -/
theorem LeftClaim10Initial.left_ne_target
    {a' w : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a')
    (hw : w = C.x ∨ w = C.y ∨ w = C.z) :
    (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) ≠ w := by
  intro h
  apply E.left_not_mem_side
  have hv : E.a = w.1 := congrArg Subtype.val h
  rw [hv]
  rcases hw with rfl | rfl | rfl
  · exact C.x_mem_side
  · exact C.y_mem_side
  · exact C.z_mem_side

/-- The right attachment is distinct from every displayed interior target. -/
theorem LeftClaim10Initial.right_ne_target
    {a' w : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a')
    (hw : w = C.x ∨ w = C.y ∨ w = C.z) :
    (⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) ≠ w := by
  intro h
  apply E.right_not_mem_side
  have hv : E.b = w.1 := congrArg Subtype.val h
  rw [hv]
  rcases hw with rfl | rfl | rfl
  · exact C.x_mem_side
  · exact C.y_mem_side
  · exact C.z_mem_side

/-- The putative twin is distinct from each of its three displayed
neighbours. -/
theorem LeftClaim10Initial.twin_ne_target
    {a' w : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a')
    (hw : w = C.x ∨ w = C.y ∨ w = C.z) : a' ≠ w := by
  rcases hw with rfl | rfl | rfl
  · exact C.twin_adj_x.ne
  · exact C.twin_adj_y.ne
  · exact C.twin_adj_z.ne

/-- The additional neighbour `x'` differs from every target of the second
fan. -/
theorem LeftClaim10Initial.next_ne_target
    {a' w : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a')
    (hw : w = C.x ∨ w = C.y ∨ w = C.z) : C.x' ≠ w := by
  rcases hw with rfl | rfl | rfl
  · exact C.next_adj_x.ne.symm
  · exact C.next_ne_y
  · exact C.next_ne_z

/-- The two displayed interior vertices also differ from the right
attachment. -/
theorem LeftClaim10Initial.twin_ne_right
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a') :
    a' ≠ ⟨E.b, E.right_mem_verts⟩ := by
  intro h
  apply E.right_not_mem_side
  have hv : a'.1 = E.b := congrArg Subtype.val h
  rw [← hv]
  exact C.twin_mem_side

theorem LeftClaim10Initial.next_ne_right
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a') :
    C.x' ≠ ⟨E.b, E.right_mem_verts⟩ := by
  intro h
  apply E.right_not_mem_side
  have hv : C.x'.1 = E.b := congrArg Subtype.val h
  rw [← hv]
  exact C.next_mem_side

/-- The virtual boundary vertex is not adjacent to the interior twin: its
exact torso neighbourhood consists of the three interior targets. -/
theorem LeftClaim10Initial.not_right_adj_twin_of_degree_eq_three
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a')
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3)
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a') :
    ¬E.torso.Adj ⟨E.b, E.right_mem_verts⟩ a' := by
  intro hba'
  have hbN : (⟨E.b, E.right_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∈ E.torso.neighborFinset a' := by
    simpa only [SimpleGraph.mem_neighborFinset] using hba'.symm
  rw [C.torso_twin_neighbors_eq (E := E) hdeg htwin] at hbN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbN
  rcases hbN with h | h | h
  · exact C.right_ne_target (E := E) (Or.inl rfl) h
  · exact C.right_ne_target (E := E) (Or.inr (Or.inl rfl)) h
  · exact C.right_ne_target (E := E) (Or.inr (Or.inr rfl)) h

/-- Assemble the source's initial `x,y,z,x'` data unconditionally from a
putative high-degree false twin of the left attachment. -/
theorem exists_leftClaim10Initial
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b)
    (hdeg : 3 ≤ E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩)
    {a' : {v : V // v ∈ E.verts}}
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a') :
    Nonempty (E.LeftClaim10Initial a') := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hax, hay, haz, ha'x, ha'y, ha'z,
      hxa, hxb, hya, hyb, hza, hzb⟩ :=
    E.exists_three_interior_commonNeighbors_left hab hdeg htwin
  have haxT : E.torso.Adj ⟨E.a, E.left_mem_verts⟩ x := Or.inl hax
  have hayT : E.torso.Adj ⟨E.a, E.left_mem_verts⟩ y := Or.inl hay
  have hazT : E.torso.Adj ⟨E.a, E.left_mem_verts⟩ z := Or.inl haz
  have ha'xT : E.torso.Adj a' x := Or.inl ha'x
  obtain ⟨x', hxx', hx'a, hx'a', hx'side⟩ :=
    E.exists_side_thirdNeighbor_of_left_commonNeighbor
      hthree hcentres haxT ha'xT htwin.1
  have htri := E.torso_triangleFree_of_vertexThreeConnected_of_centres
    hthree hcentres
  have hx'y : x' ≠ y := by
    intro h
    subst x'
    exact htri haxT hxx' hayT.symm
  have hx'z : x' ≠ z := by
    intro h
    subst x'
    exact htri haxT hxx' hazT.symm
  exact ⟨{
    x := x
    y := y
    z := z
    x' := x'
    x_ne_y := hxy
    x_ne_z := hxz
    y_ne_z := hyz
    left_adj_x := hax
    left_adj_y := hay
    left_adj_z := haz
    twin_adj_x := ha'x
    twin_adj_y := ha'y
    twin_adj_z := ha'z
    next_adj_x := hxx'
    next_ne_left := hx'a
    next_ne_twin := hx'a'
    next_ne_y := hx'y
    next_ne_z := hx'z
    twin_mem_side := E.left_falseTwin_mem_side_of_degree_three
      hthree hcentres hnoWheel hab hdeg htwin
    x_mem_side := E.mem_side_of_mem_verts x.2 hxa hxb
    y_mem_side := E.mem_side_of_mem_verts y.2 hya hyb
    z_mem_side := E.mem_side_of_mem_verts z.2 hza hzb
    next_mem_side := hx'side }⟩

/-- The first two-fan in the surviving branch of Claim (10), in the
single-path form used throughout the source formalization.  Delete the
common neighbour `x` from the three-connected torso and apply the rooted
two-fan lemma to `x'` and the target set `{y,z,b}`.  The resulting path has
distinct target endpoints, contains `x'`, avoids `x`, and has no target in
its interior.  Endpoint cleanup (excluding `b`) is deliberately kept as a
separate step, since it is exactly where the source's first wheel is used. -/
structure LeftClaim10FirstFan
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a') where
  s : {v : V // v ∈ E.verts}
  t : {v : V // v ∈ E.verts}
  s_target :
    s = C.y ∨ s = C.z ∨ s = ⟨E.b, E.right_mem_verts⟩
  t_target :
    t = C.y ∨ t = C.z ∨ t = ⟨E.b, E.right_mem_verts⟩
  s_ne_t : s ≠ t
  path : E.torso.Walk s t
  path_isPath : path.IsPath
  next_mem : C.x' ∈ path.support
  deleted_not_mem : C.x ∉ path.support
  target_clean : ∀ w, w ∈ path.support →
    (w = C.y ∨ w = C.z ∨ w = ⟨E.b, E.right_mem_verts⟩) →
      w = s ∨ w = t

/-- Reverse the single-path presentation of a first fan. -/
def LeftClaim10FirstFan.reverse
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10FirstFan C) : E.LeftClaim10FirstFan C where
  s := F.t
  t := F.s
  s_target := F.t_target
  t_target := F.s_target
  s_ne_t := F.s_ne_t.symm
  path := F.path.reverse
  path_isPath := F.path_isPath.reverse
  next_mem := by
    change C.x' ∈ F.path.reverse.support
    simpa only [Walk.support_reverse, List.mem_reverse] using F.next_mem
  deleted_not_mem := by simpa [Walk.support_reverse] using F.deleted_not_mem
  target_clean := by
    intro w hw hwTarget
    have hw' : w ∈ F.path.support := by
      simpa [Walk.support_reverse] using hw
    rcases F.target_clean w hw' hwTarget with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- Regard the same first fan after exchanging `y` and `z`. -/
def LeftClaim10FirstFan.swapYZ
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10FirstFan C) :
    E.LeftClaim10FirstFan C.swapYZ where
  s := F.s
  t := F.t
  s_target := by
    rcases F.s_target with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  t_target := by
    rcases F.t_target with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  s_ne_t := F.s_ne_t
  path := F.path
  path_isPath := F.path_isPath
  next_mem := F.next_mem
  deleted_not_mem := F.deleted_not_mem
  target_clean := by
    intro w hw hwTarget
    apply F.target_clean w hw
    rcases hwTarget with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- Exhaustive endpoint split for the first fan.  Once the boundary-ending
case is contradicted by the first wheel, only the two orientations of the
`y`--`z` fan remain. -/
theorem LeftClaim10FirstFan.boundary_or_yz
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10FirstFan C) :
    (F.s = ⟨E.b, E.right_mem_verts⟩ ∨
      F.t = ⟨E.b, E.right_mem_verts⟩) ∨
      (F.s = C.y ∧ F.t = C.z) ∨
      (F.s = C.z ∧ F.t = C.y) := by
  rcases F.s_target with hs | hs | hs <;>
    rcases F.t_target with ht | ht | ht
  · exact False.elim (F.s_ne_t (hs.trans ht.symm))
  · exact Or.inr (Or.inl ⟨hs, ht⟩)
  · exact Or.inl (Or.inr ht)
  · exact Or.inr (Or.inr ⟨hs, ht⟩)
  · exact False.elim (F.s_ne_t (hs.trans ht.symm))
  · exact Or.inl (Or.inr ht)
  · exact Or.inl (Or.inl hs)
  · exact Or.inl (Or.inl hs)
  · exact False.elim (F.s_ne_t (hs.trans ht.symm))

/-- Existence of the source-exact first fan certificate.  This is a direct,
unconditional consequence of three-connectivity; it does not assume the
desired endpoint conclusion. -/
theorem exists_leftClaim10FirstFan
    {a' : {v : V // v ∈ E.verts}}
    (hthree : VertexThreeConnected E.torso)
    (C : E.LeftClaim10Initial a') :
    Nonempty (E.LeftClaim10FirstFan C) := by
  let H := E.torso.induce fun w : {v : V // v ∈ E.verts} ↦ w ≠ C.x
  have h2 := vertexTwoConnected_delete_of_isThreeConnected
    (isThreeConnected_of_vertexThreeConnected_local hthree) C.x
  have hyx : C.y ≠ C.x := C.x_ne_y.symm
  have hzx : C.z ≠ C.x := C.x_ne_z.symm
  have hbx : (⟨E.b, E.right_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ≠ C.x := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change E.b = C.x.1 at hv
    rw [hv]
    exact C.x_mem_side
  have hnextx : C.x' ≠ C.x := C.next_adj_x.ne.symm
  let yD : {w : {v : V // v ∈ E.verts} // w ≠ C.x} := ⟨C.y, hyx⟩
  let zD : {w : {v : V // v ∈ E.verts} // w ≠ C.x} := ⟨C.z, hzx⟩
  let bD : {w : {v : V // v ∈ E.verts} // w ≠ C.x} :=
    ⟨⟨E.b, E.right_mem_verts⟩, hbx⟩
  let nextD : {w : {v : V // v ∈ E.verts} // w ≠ C.x} :=
    ⟨C.x', hnextx⟩
  let S : Finset {w : {v : V // v ∈ E.verts} // w ≠ C.x} :=
    {yD, zD, bD}
  have hnextb : C.x' ≠
      (⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change C.x'.1 = E.b at hv
    rw [← hv]
    exact C.next_mem_side
  have hnextS : nextD ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h | h
    · exact C.next_ne_y (congrArg Subtype.val h)
    · exact C.next_ne_z (congrArg Subtype.val h)
    · exact hnextb (congrArg Subtype.val h)
  have hyDzD : yD ≠ zD := by
    intro h
    exact C.y_ne_z (congrArg Subtype.val h)
  have hScard : 2 ≤ S.card := by
    have hpair : ({yD, zD} :
        Finset {w : {v : V // v ∈ E.verts} // w ≠ C.x}).card = 2 := by
      simp [hyDzD]
    rw [← hpair]
    exact Finset.card_le_card (by simp [S])
  obtain ⟨s, t, hsS, htS, hst, p, hp, hnextp, htarget⟩ :=
    exists_targetPath_through_of_vertexTwoConnected
      S hnextS hScard h2.1 h2.2
  let inc : H →g E.torso :=
    (SimpleGraph.Embedding.induce (G := E.torso)
      (s := fun w : {v : V // v ∈ E.verts} ↦ w ≠ C.x)).toHom
  let pT : E.torso.Walk s.1 t.1 := p.map inc
  have hpT : pT.IsPath := hp.map Subtype.val_injective
  have hnextT : C.x' ∈ pT.support := by
    change C.x' ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨nextD, hnextp, rfl⟩
  have hxT : C.x ∉ pT.support := by
    change C.x ∉ (p.map inc).support
    rw [Walk.support_map]
    intro hx
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hx
    change w.1 = C.x at hw
    exact w.2 hw
  have hsTarget : s.1 = C.y ∨ s.1 = C.z ∨
      s.1 = (⟨E.b, E.right_mem_verts⟩ :
        {v : V // v ∈ E.verts}) := by
    have hsCases : s = yD ∨ s = zD ∨ s = bD := by
      simpa only [S, Finset.mem_insert, Finset.mem_singleton] using hsS
    rcases hsCases with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have htTarget : t.1 = C.y ∨ t.1 = C.z ∨
      t.1 = (⟨E.b, E.right_mem_verts⟩ :
        {v : V // v ∈ E.verts}) := by
    have htCases : t = yD ∨ t = zD ∨ t = bD := by
      simpa only [S, Finset.mem_insert, Finset.mem_singleton] using htS
    rcases htCases with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have htargetT : ∀ w, w ∈ pT.support →
      (w = C.y ∨ w = C.z ∨
        w = (⟨E.b, E.right_mem_verts⟩ :
          {v : V // v ∈ E.verts})) →
        w = s.1 ∨ w = t.1 := by
    intro w hwp hwTarget
    change w ∈ (p.map inc).support at hwp
    rw [Walk.support_map] at hwp
    obtain ⟨wD, hwDp, hwD⟩ := List.mem_map.mp hwp
    change wD.1 = w at hwD
    have hwDS : wD ∈ S := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton]
      rcases hwTarget with rfl | rfl | rfl
      · exact Or.inl (Subtype.ext hwD)
      · exact Or.inr (Or.inl (Subtype.ext hwD))
      · exact Or.inr (Or.inr (Subtype.ext hwD))
    rcases htarget wD hwDp hwDS with h | h
    · exact Or.inl (hwD.symm.trans (congrArg Subtype.val h))
    · exact Or.inr (hwD.symm.trans (congrArg Subtype.val h))
  exact ⟨{
    s := s.1
    t := t.1
    s_target := hsTarget
    t_target := htTarget
    s_ne_t := fun h ↦ hst (Subtype.ext h)
    path := pT
    path_isPath := hpT
    next_mem := hnextT
    deleted_not_mem := hxT
    target_clean := htargetT }⟩

/-- At exact attachment degree three, every first-fan path automatically
avoids both the left attachment and its putative false twin.  Their exact
neighbourhoods leave only the fan endpoints as possible path-neighbours,
while the displayed internal vertex `x'` prevents a two-edge path. -/
theorem LeftClaim10FirstFan.avoids_left_and_twin_of_degree_eq_three
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10FirstFan C) (hab : ¬G.Adj E.a E.b)
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3)
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a') :
    (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) ∉
        F.path.support ∧
      a' ∉ F.path.support := by
  let a : {v : V // v ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  have left_ne_first_target {w : {v : V // v ∈ E.verts}}
      (hw : w = C.y ∨ w = C.z ∨
        w = ⟨E.b, E.right_mem_verts⟩) : a ≠ w := by
    rcases hw with rfl | rfl | rfl
    · exact C.left_ne_target (E := E) (Or.inr (Or.inl rfl))
    · exact C.left_ne_target (E := E) (Or.inr (Or.inr rfl))
    · exact fun h ↦ E.boundary_ne (congrArg Subtype.val h)
  have twin_ne_first_target {w : {v : V // v ∈ E.verts}}
      (hw : w = C.y ∨ w = C.z ∨
        w = ⟨E.b, E.right_mem_verts⟩) : a' ≠ w := by
    rcases hw with rfl | rfl | rfl
    · exact C.twin_ne_target (E := E) (Or.inr (Or.inl rfl))
    · exact C.twin_ne_target (E := E) (Or.inr (Or.inr rfl))
    · exact C.twin_ne_right (E := E)
  have next_ne_first_target {w : {v : V // v ∈ E.verts}}
      (hw : w = C.y ∨ w = C.z ∨
        w = ⟨E.b, E.right_mem_verts⟩) : C.x' ≠ w := by
    rcases hw with rfl | rfl | rfl
    · exact C.next_ne_y
    · exact C.next_ne_z
    · exact C.next_ne_right (E := E)
  have hleftN : F.path.toSubgraph.neighborSet a ⊆
      ({F.s, F.t} : Set {v : V // v ∈ E.verts}) := by
    intro w hw
    have hws : w ∈ F.path.support := by
      simpa only [Walk.mem_verts_toSubgraph] using hw.snd_mem
    have haw : E.torso.Adj a w := F.path.toSubgraph.adj_sub hw
    have hwN : w ∈ E.torso.neighborFinset a := by
      simpa only [SimpleGraph.mem_neighborFinset] using haw
    rw [C.torso_left_neighbors_eq (E := E) hab hdeg] at hwN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwN
    rcases hwN with hwb | hwx | hwy | hwz
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
        F.target_clean w hws (Or.inr (Or.inr hwb))
    · exact False.elim (F.deleted_not_mem (hwx ▸ hws))
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
        F.target_clean w hws (Or.inl hwy)
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
        F.target_clean w hws (Or.inr (Or.inl hwz))
  have htwinN : F.path.toSubgraph.neighborSet a' ⊆
      ({F.s, F.t} : Set {v : V // v ∈ E.verts}) := by
    intro w hw
    have hws : w ∈ F.path.support := by
      simpa only [Walk.mem_verts_toSubgraph] using hw.snd_mem
    have haw : E.torso.Adj a' w := F.path.toSubgraph.adj_sub hw
    have hwN : w ∈ E.torso.neighborFinset a' := by
      simpa only [SimpleGraph.mem_neighborFinset] using haw
    rw [C.torso_twin_neighbors_eq (E := E) hdeg htwin] at hwN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwN
    rcases hwN with hwx | hwy | hwz
    · exact False.elim (F.deleted_not_mem (hwx ▸ hws))
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
        F.target_clean w hws (Or.inl hwy)
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
        F.target_clean w hws (Or.inr (Or.inl hwz))
  constructor
  · exact Walk.IsPath.not_mem_support_of_neighbors_subset_endpoints_of_extra
      F.path_isPath F.s_ne_t
        hleftN (left_ne_first_target F.s_target)
        (left_ne_first_target F.t_target) F.next_mem
        (next_ne_first_target F.s_target)
        (next_ne_first_target F.t_target) C.next_ne_left
  · exact Walk.IsPath.not_mem_support_of_neighbors_subset_endpoints_of_extra
      F.path_isPath F.s_ne_t
        htwinN (twin_ne_first_target F.s_target)
        (twin_ne_first_target F.t_target) F.next_mem
        (next_ne_first_target F.s_target)
        (next_ne_first_target F.t_target) C.next_ne_twin

/-- The displayed first wheel in Claim (10), with the two possible path
collisions stated explicitly.  If the target-minimal first-fan path is
oriented from `y` to the right attachment and avoids both the left
attachment and its putative twin, closing it along
`b-a-z-a'-y` is a simple rim.  Its centre `x` has the three spokes to
`x'`, `a`, and `a'`.

This lemma is the collision-free core of the source argument.  The only
remaining endpoint-cleanup work is therefore to reroute, or derive a wheel
directly, when the fan path meets `a` or `a'`. -/
theorem hasWheelCenteredAt_x_of_firstFan_y_right_of_clean
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10FirstFan C)
    (hsy : F.s = C.y)
    (htb : F.t = ⟨E.b, E.right_mem_verts⟩)
    (haNot : (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∉ F.path.support)
    (ha'Not : a' ∉ F.path.support) :
    HasWheelCenteredAt E.torso C.x := by
  let a : {v : V // v ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  let b : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  let p : E.torso.Walk C.y b := F.path.copy hsy htb
  have hp : p.IsPath := (Walk.isPath_copy _ _ _).mpr F.path_isPath
  have hpSupport : p.support = F.path.support := by
    simp only [p, Walk.support_copy]
  have hnextP : C.x' ∈ p.support := by
    simpa only [hpSupport] using F.next_mem
  have hxP : C.x ∉ p.support := by
    simpa only [hpSupport] using F.deleted_not_mem
  have haP : a ∉ p.support := by
    simpa only [a, hpSupport] using haNot
  have ha'P : a' ∉ p.support := by
    simpa only [hpSupport] using ha'Not
  have hza : C.z ≠ a := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change C.z.1 = E.a at hv
    rw [← hv]
    exact C.z_mem_side
  have hzb : C.z ≠ b := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change C.z.1 = E.b at hv
    rw [← hv]
    exact C.z_mem_side
  have hya : C.y ≠ a := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change C.y.1 = E.a at hv
    rw [← hv]
    exact C.y_mem_side
  have hyb : C.y ≠ b := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change C.y.1 = E.b at hv
    rw [← hv]
    exact C.y_mem_side
  have ha'a : a' ≠ a := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change a'.1 = E.a at hv
    rw [← hv]
    exact C.twin_mem_side
  have ha'b : a' ≠ b := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change a'.1 = E.b at hv
    rw [← hv]
    exact C.twin_mem_side
  have hba : E.torso.Adj b a := by
    simpa only [a, b] using E.torso_boundary_adj.symm
  have haz : E.torso.Adj a C.z := by
    exact Or.inl C.left_adj_z
  have hza' : E.torso.Adj C.z a' := by
    exact (show E.torso.Adj a' C.z from Or.inl C.twin_adj_z).symm
  have ha'y : E.torso.Adj a' C.y := by
    exact Or.inl C.twin_adj_y
  let r : E.torso.Walk b C.y :=
    ((hba.toWalk.concat haz).concat hza').concat ha'y
  have hr1 : hba.toWalk.IsPath := Walk.IsPath.of_adj hba
  have hr2 : (hba.toWalk.concat haz).IsPath :=
    hr1.concat (by simp [hza, hzb]) haz
  have hr3 : ((hba.toWalk.concat haz).concat hza').IsPath :=
    hr2.concat (by simp [ha'a, ha'b, hza'.ne.symm]) hza'
  have hr : r.IsPath :=
    hr3.concat (by
      simp [r, hya, hyb, C.y_ne_z, ha'y.ne.symm]) ha'y
  have hyNotTail : C.y ∉ p.support.tail := by
    have hnd := hp.support_nodup
    rw [← p.cons_tail_support] at hnd
    exact (List.nodup_cons.mp hnd).1
  have hzNotP : C.z ∉ p.support := by
    intro hzP
    have hzF : C.z ∈ F.path.support := by
      simpa only [hpSupport] using hzP
    rcases F.target_clean C.z hzF (Or.inr (Or.inl rfl)) with h | h
    · exact C.y_ne_z (h.trans hsy).symm
    · exact hzb (h.trans htb)
  have hdisj : p.support.tail.Disjoint r.support.tail := by
    rw [List.disjoint_left]
    intro w hwp hwr
    have hwrCases : w = a ∨ w = C.z ∨ w = a' ∨ w = C.y := by
      simpa [r] using hwr
    rcases hwrCases with rfl | rfl | rfl | rfl
    · exact haP (List.mem_of_mem_tail hwp)
    · exact hzNotP (List.mem_of_mem_tail hwp)
    · exact ha'P (List.mem_of_mem_tail hwp)
    · exact hyNotTail hwp
  have hxa : C.x ≠ a := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change C.x.1 = E.a at hv
    rw [← hv]
    exact C.x_mem_side
  have hxb : C.x ≠ b := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change C.x.1 = E.b at hv
    rw [← hv]
    exact C.x_mem_side
  have hxr : C.x ∉ r.support := by
    intro h
    have hcases : C.x = b ∨ C.x = a ∨ C.x = C.z ∨
        C.x = a' ∨ C.x = C.y := by
      simpa [r] using h
    rcases hcases with h | h | h | h | h
    · exact hxb h
    · exact hxa h
    · exact C.x_ne_z h
    · exact C.twin_adj_x.ne h.symm
    · exact C.x_ne_y h
  have hxa' : a ≠ a' := ha'a.symm
  exact hasWheelCenteredAt_of_path_append p r hp hr hdisj
    (Or.inr (by simp [r])) hxP hxr C.next_adj_x
    (show E.torso.Adj a C.x from Or.inl C.left_adj_x).symm
    (show E.torso.Adj a' C.x from Or.inl C.twin_adj_x).symm
    (Or.inl hnextP) (Or.inr (by simp [r, a])) (Or.inr (by simp [r]))
    C.next_ne_left C.next_ne_twin hxa'

/-- Reversed orientation of the same clean first-wheel construction. -/
theorem hasWheelCenteredAt_x_of_firstFan_right_y_of_clean
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10FirstFan C)
    (hsb : F.s = ⟨E.b, E.right_mem_verts⟩)
    (hty : F.t = C.y)
    (haNot : (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∉ F.path.support)
    (ha'Not : a' ∉ F.path.support) :
    HasWheelCenteredAt E.torso C.x := by
  apply E.hasWheelCenteredAt_x_of_firstFan_y_right_of_clean F.reverse
    hty hsb
  · simpa [LeftClaim10FirstFan.reverse, Walk.support_reverse] using haNot
  · simpa [LeftClaim10FirstFan.reverse, Walk.support_reverse] using ha'Not

/-- `y,z`-symmetric orientation of the clean first-wheel construction. -/
theorem hasWheelCenteredAt_x_of_firstFan_z_right_of_clean
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10FirstFan C)
    (hsz : F.s = C.z)
    (htb : F.t = ⟨E.b, E.right_mem_verts⟩)
    (haNot : (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∉ F.path.support)
    (ha'Not : a' ∉ F.path.support) :
    HasWheelCenteredAt E.torso C.x := by
  simpa [LeftClaim10Initial.swapYZ] using
    E.hasWheelCenteredAt_x_of_firstFan_y_right_of_clean
      (C := C.swapYZ) F.swapYZ hsz htb haNot ha'Not

/-- Reversed and `y,z`-symmetric orientation. -/
theorem hasWheelCenteredAt_x_of_firstFan_right_z_of_clean
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10FirstFan C)
    (hsb : F.s = ⟨E.b, E.right_mem_verts⟩)
    (htz : F.t = C.z)
    (haNot : (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∉ F.path.support)
    (ha'Not : a' ∉ F.path.support) :
    HasWheelCenteredAt E.torso C.x := by
  exact E.hasWheelCenteredAt_x_of_firstFan_z_right_of_clean F.reverse
    htz hsb
    (by simpa [LeftClaim10FirstFan.reverse, Walk.support_reverse] using haNot)
    (by simpa [LeftClaim10FirstFan.reverse, Walk.support_reverse] using ha'Not)

/-- Endpoint cleanup for a first fan whose path has no collision with the
two left-side hubs.  Centre confinement rules out a boundary endpoint,
because each of its four possible orientations gives the preceding wheel
centred at the interior vertex `x`. -/
theorem LeftClaim10FirstFan.no_boundary_of_clean
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10FirstFan C)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (haNot : (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∉ F.path.support)
    (ha'Not : a' ∉ F.path.support) :
    F.s ≠ ⟨E.b, E.right_mem_verts⟩ ∧
      F.t ≠ ⟨E.b, E.right_mem_verts⟩ := by
  have hxLeft : C.x ≠
      (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change C.x.1 = E.a at hv
    rw [← hv]
    exact C.x_mem_side
  have hxRight : C.x ≠
      (⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change C.x.1 = E.b at hv
    rw [← hv]
    exact C.x_mem_side
  constructor
  · intro hsb
    have hxC : HasWheelCenteredAt E.torso C.x := by
      rcases F.t_target with hty | htz | htb
      · exact E.hasWheelCenteredAt_x_of_firstFan_right_y_of_clean
          F hsb hty haNot ha'Not
      · exact E.hasWheelCenteredAt_x_of_firstFan_right_z_of_clean
          F hsb htz haNot ha'Not
      · exact False.elim (F.s_ne_t (hsb.trans htb.symm))
    exact hcentres C.x hxLeft hxRight hxC
  · intro htb
    have hxC : HasWheelCenteredAt E.torso C.x := by
      rcases F.s_target with hsy | hsz | hsb
      · exact E.hasWheelCenteredAt_x_of_firstFan_y_right_of_clean
          F hsy htb haNot ha'Not
      · exact E.hasWheelCenteredAt_x_of_firstFan_z_right_of_clean
          F hsz htb haNot ha'Not
      · exact False.elim (F.s_ne_t (hsb.trans htb.symm))
    exact hcentres C.x hxLeft hxRight hxC

/-- Exact degree makes the cleanliness assumptions in the preceding endpoint
exclusion automatic. -/
theorem LeftClaim10FirstFan.not_boundary_of_degree_eq_three
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10FirstFan C)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hab : ¬G.Adj E.a E.b)
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3)
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a') :
    ¬(F.s = ⟨E.b, E.right_mem_verts⟩ ∨
      F.t = ⟨E.b, E.right_mem_verts⟩) := by
  obtain ⟨ha, ha'⟩ :=
    F.avoids_left_and_twin_of_degree_eq_three (E := E) hab hdeg htwin
  obtain ⟨hs, ht⟩ := F.no_boundary_of_clean (E := E) hcentres ha ha'
  exact fun h ↦ h.elim hs ht

/-- Normalized surviving first fan after its boundary endpoint has been
excluded.  The path is oriented from `y` to `z`, contains `x'`, avoids the
deleted vertex `x`, and avoids the right attachment by target minimality. -/
structure LeftClaim10YZFan
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a') where
  path : E.torso.Walk C.y C.z
  path_isPath : path.IsPath
  next_mem : C.x' ∈ path.support
  deleted_not_mem : C.x ∉ path.support
  right_not_mem : (⟨E.b, E.right_mem_verts⟩ :
    {v : V // v ∈ E.verts}) ∉ path.support

/-- Reverse a normalized first fan while simultaneously exchanging `y`
and `z`. -/
def LeftClaim10YZFan.swapYZ
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) : E.LeftClaim10YZFan C.swapYZ where
  path := F.path.reverse
  path_isPath := F.path_isPath.reverse
  next_mem := by
    change C.x' ∈ F.path.reverse.support
    simpa only [Walk.support_reverse, List.mem_reverse] using F.next_mem
  deleted_not_mem := by
    simpa [LeftClaim10Initial.swapYZ, Walk.support_reverse] using
      F.deleted_not_mem
  right_not_mem := by
    change (⟨E.b, E.right_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∉ F.path.reverse.support
    simpa only [Walk.support_reverse, List.mem_reverse] using F.right_not_mem

/-- The normalized first fan inherits the automatic avoidance of the left
attachment and its putative twin. -/
theorem LeftClaim10YZFan.avoids_left_and_twin_of_degree_eq_three
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (hab : ¬G.Adj E.a E.b)
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3)
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a') :
    (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) ∉
        F.path.support ∧
      a' ∉ F.path.support := by
  let F' : E.LeftClaim10FirstFan C := {
    s := C.y
    t := C.z
    s_target := Or.inl rfl
    t_target := Or.inr (Or.inl rfl)
    s_ne_t := C.y_ne_z
    path := F.path
    path_isPath := F.path_isPath
    next_mem := F.next_mem
    deleted_not_mem := F.deleted_not_mem
    target_clean := by
      intro w hw hwTarget
      rcases hwTarget with hwy | hwz | hwb
      · exact Or.inl hwy
      · exact Or.inr hwz
      · exact False.elim (F.right_not_mem (hwb ▸ hw)) }
  simpa only [F'] using
    F'.avoids_left_and_twin_of_degree_eq_three (E := E) hab hdeg htwin

/-- Orient a first fan from `y` to `z` once neither endpoint is the right
attachment. -/
theorem LeftClaim10FirstFan.toYZFan
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10FirstFan C)
    (hsb : F.s ≠ ⟨E.b, E.right_mem_verts⟩)
    (htb : F.t ≠ ⟨E.b, E.right_mem_verts⟩) :
    Nonempty (E.LeftClaim10YZFan C) := by
  have hbNot : (⟨E.b, E.right_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∉ F.path.support := by
    intro hb
    rcases F.target_clean _ hb (Or.inr (Or.inr rfl)) with h | h
    · exact hsb h.symm
    · exact htb h.symm
  rcases F.boundary_or_yz with hboundary | hyz | hzy
  · exact False.elim (hboundary.elim hsb htb)
  · let p : E.torso.Walk C.y C.z := F.path.copy hyz.1 hyz.2
    exact ⟨{
      path := p
      path_isPath := (Walk.isPath_copy _ _ _).mpr F.path_isPath
      next_mem := by simpa [p, Walk.support_copy] using F.next_mem
      deleted_not_mem := by
        simpa [p, Walk.support_copy] using F.deleted_not_mem
      right_not_mem := by simpa [p, Walk.support_copy] using hbNot }⟩
  · let p : E.torso.Walk C.y C.z :=
      F.path.reverse.copy hzy.2 hzy.1
    exact ⟨{
      path := p
      path_isPath := (Walk.isPath_copy _ _ _).mpr F.path_isPath.reverse
      next_mem := by
        simpa [p, Walk.support_copy, Walk.support_reverse] using F.next_mem
      deleted_not_mem := by
        simpa [p, Walk.support_copy, Walk.support_reverse] using
          F.deleted_not_mem
      right_not_mem := by
        simpa [p, Walk.support_copy, Walk.support_reverse] using hbNot }⟩

/-- Split the normalized first-fan path at `x'`.  The two arms have only
their common start in common, in the standard `tail.Disjoint` form used by
the later path-splicing lemmas. -/
structure LeftClaim10YZArms
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a') where
  left : E.torso.Walk C.x' C.y
  right : E.torso.Walk C.x' C.z
  left_isPath : left.IsPath
  right_isPath : right.IsPath
  tails_disjoint : left.support.tail.Disjoint right.support.tail
  deleted_not_mem_left : C.x ∉ left.support
  deleted_not_mem_right : C.x ∉ right.support
  boundary_not_mem_left : (⟨E.b, E.right_mem_verts⟩ :
    {v : V // v ∈ E.verts}) ∉ left.support
  boundary_not_mem_right : (⟨E.b, E.right_mem_verts⟩ :
    {v : V // v ∈ E.verts}) ∉ right.support

/-- Exchange the two arms together with `y,z`. -/
def LeftClaim10YZArms.swapYZ
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (A : E.LeftClaim10YZArms C) : E.LeftClaim10YZArms C.swapYZ where
  left := A.right
  right := A.left
  left_isPath := A.right_isPath
  right_isPath := A.left_isPath
  tails_disjoint := A.tails_disjoint.symm
  deleted_not_mem_left := A.deleted_not_mem_right
  deleted_not_mem_right := A.deleted_not_mem_left
  boundary_not_mem_left := A.boundary_not_mem_right
  boundary_not_mem_right := A.boundary_not_mem_left

/-- The two first-fan arms meet only at their common start `x'`. -/
theorem LeftClaim10YZArms.meet_only_next
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (A : E.LeftClaim10YZArms C) {w : {v : V // v ∈ E.verts}}
    (hwL : w ∈ A.left.support) (hwR : w ∈ A.right.support) :
    w = C.x' := by
  by_cases h : w = C.x'
  · exact h
  have hwLTail : w ∈ A.left.support.tail := by
    rw [← A.left.cons_tail_support] at hwL
    exact (List.mem_cons.mp hwL).resolve_left h
  have hwRTail : w ∈ A.right.support.tail := by
    rw [← A.right.cons_tail_support] at hwR
    exact (List.mem_cons.mp hwR).resolve_left h
  exact False.elim (List.disjoint_left.mp A.tails_disjoint hwLTail hwRTail)

/-- The two internally disjoint arms encoded by a normalized first fan. -/
theorem LeftClaim10YZFan.toArms
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) : Nonempty (E.LeftClaim10YZArms C) := by
  let P : E.torso.Walk C.x' C.y :=
    (F.path.takeUntil C.x' F.next_mem).reverse
  let Q : E.torso.Walk C.x' C.z :=
    F.path.dropUntil C.x' F.next_mem
  have hP : P.IsPath :=
    (F.path_isPath.takeUntil F.next_mem).reverse
  have hQ : Q.IsPath := F.path_isPath.dropUntil F.next_mem
  have hdisj : P.support.tail.Disjoint Q.support.tail := by
    have hnd :
        ((F.path.takeUntil C.x' F.next_mem).support ++
          Q.support.tail).Nodup := by
      simpa only [← Walk.support_append, Q, F.path.take_spec F.next_mem]
        using F.path_isPath.support_nodup
    rw [List.disjoint_left]
    intro w hwP hwQ
    have hwTake : w ∈ (F.path.takeUntil C.x' F.next_mem).support := by
      have : w ∈ P.support := List.mem_of_mem_tail hwP
      simpa [P, Walk.support_reverse] using this
    exact ((List.nodup_append.mp hnd).2.2 w hwTake w hwQ) rfl
  have Psubset {w : {v : V // v ∈ E.verts}} (hw : w ∈ P.support) :
      w ∈ F.path.support := by
    apply F.path.support_takeUntil_subset_support F.next_mem
    simpa [P, Walk.support_reverse] using hw
  have Qsubset {w : {v : V // v ∈ E.verts}} (hw : w ∈ Q.support) :
      w ∈ F.path.support :=
    F.path.support_dropUntil_subset_support F.next_mem hw
  exact ⟨{
    left := P
    right := Q
    left_isPath := hP
    right_isPath := hQ
    tails_disjoint := hdisj
    deleted_not_mem_left := fun h ↦ F.deleted_not_mem (Psubset h)
    deleted_not_mem_right := fun h ↦ F.deleted_not_mem (Qsubset h)
    boundary_not_mem_left := fun h ↦ F.right_not_mem (Psubset h)
    boundary_not_mem_right := fun h ↦ F.right_not_mem (Qsubset h) }⟩

/-- Split a normalized first fan while retaining the two support-inclusion
certificates.  The later collision elimination needs these certificates to
promote an intersection with one arm to an intersection with the original
`y`--`z` path. -/
theorem LeftClaim10YZFan.toArms_with_subsets
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) :
    ∃ A : E.LeftClaim10YZArms C,
      (∀ w, w ∈ A.left.support → w ∈ F.path.support) ∧
      (∀ w, w ∈ A.right.support → w ∈ F.path.support) := by
  let P : E.torso.Walk C.x' C.y :=
    (F.path.takeUntil C.x' F.next_mem).reverse
  let Q : E.torso.Walk C.x' C.z :=
    F.path.dropUntil C.x' F.next_mem
  have hP : P.IsPath :=
    (F.path_isPath.takeUntil F.next_mem).reverse
  have hQ : Q.IsPath := F.path_isPath.dropUntil F.next_mem
  have hdisj : P.support.tail.Disjoint Q.support.tail := by
    have hnd :
        ((F.path.takeUntil C.x' F.next_mem).support ++
          Q.support.tail).Nodup := by
      simpa only [← Walk.support_append, Q, F.path.take_spec F.next_mem]
        using F.path_isPath.support_nodup
    rw [List.disjoint_left]
    intro w hwP hwQ
    have hwTake : w ∈ (F.path.takeUntil C.x' F.next_mem).support := by
      have : w ∈ P.support := List.mem_of_mem_tail hwP
      simpa [P, Walk.support_reverse] using this
    exact ((List.nodup_append.mp hnd).2.2 w hwTake w hwQ) rfl
  have Psubset {w : {v : V // v ∈ E.verts}} (hw : w ∈ P.support) :
      w ∈ F.path.support := by
    apply F.path.support_takeUntil_subset_support F.next_mem
    simpa [P, Walk.support_reverse] using hw
  have Qsubset {w : {v : V // v ∈ E.verts}} (hw : w ∈ Q.support) :
      w ∈ F.path.support :=
    F.path.support_dropUntil_subset_support F.next_mem hw
  refine ⟨{
    left := P
    right := Q
    left_isPath := hP
    right_isPath := hQ
    tails_disjoint := hdisj
    deleted_not_mem_left := fun h ↦ F.deleted_not_mem (Psubset h)
    deleted_not_mem_right := fun h ↦ F.deleted_not_mem (Qsubset h)
    boundary_not_mem_left := fun h ↦ F.right_not_mem (Psubset h)
    boundary_not_mem_right := fun h ↦ F.right_not_mem (Qsubset h) }, ?_, ?_⟩
  · intro w hw
    exact Psubset hw
  · intro w hw
    exact Qsubset hw

/-- The second two-fan in source Claim (10), again stored as one
target-minimal path.  Here the left attachment is deleted, the root is the
right attachment, and the targets are the three common neighbours
`{x,y,z}`. -/
structure LeftClaim10SecondFan
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a') where
  s : {v : V // v ∈ E.verts}
  t : {v : V // v ∈ E.verts}
  s_target : s = C.x ∨ s = C.y ∨ s = C.z
  t_target : t = C.x ∨ t = C.y ∨ t = C.z
  s_ne_t : s ≠ t
  path : E.torso.Walk s t
  path_isPath : path.IsPath
  right_mem : (⟨E.b, E.right_mem_verts⟩ :
    {v : V // v ∈ E.verts}) ∈ path.support
  left_not_mem : (⟨E.a, E.left_mem_verts⟩ :
    {v : V // v ∈ E.verts}) ∉ path.support
  target_clean : ∀ w, w ∈ path.support →
    (w = C.x ∨ w = C.y ∨ w = C.z) → w = s ∨ w = t

/-- Existence of the source-exact second fan certificate. -/
theorem exists_leftClaim10SecondFan
    {a' : {v : V // v ∈ E.verts}}
    (hthree : VertexThreeConnected E.torso)
    (C : E.LeftClaim10Initial a') :
    Nonempty (E.LeftClaim10SecondFan C) := by
  let H := E.torso.induce fun w : {v : V // v ∈ E.verts} ↦
    w ≠ ⟨E.a, E.left_mem_verts⟩
  have h2 := vertexTwoConnected_delete_of_isThreeConnected
    (isThreeConnected_of_vertexThreeConnected_local hthree)
      ⟨E.a, E.left_mem_verts⟩
  have hxa : C.x ≠
      (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change C.x.1 = E.a at hv
    rw [← hv]
    exact C.x_mem_side
  have hya : C.y ≠
      (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change C.y.1 = E.a at hv
    rw [← hv]
    exact C.y_mem_side
  have hza : C.z ≠
      (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change C.z.1 = E.a at hv
    rw [← hv]
    exact C.z_mem_side
  let xD : {w : {v : V // v ∈ E.verts} //
      w ≠ ⟨E.a, E.left_mem_verts⟩} := ⟨C.x, hxa⟩
  let yD : {w : {v : V // v ∈ E.verts} //
      w ≠ ⟨E.a, E.left_mem_verts⟩} := ⟨C.y, hya⟩
  let zD : {w : {v : V // v ∈ E.verts} //
      w ≠ ⟨E.a, E.left_mem_verts⟩} := ⟨C.z, hza⟩
  let bD : {w : {v : V // v ∈ E.verts} //
      w ≠ ⟨E.a, E.left_mem_verts⟩} :=
    ⟨⟨E.b, E.right_mem_verts⟩, fun h ↦
      E.boundary_ne (congrArg Subtype.val h).symm⟩
  let S : Finset {w : {v : V // v ∈ E.verts} //
      w ≠ ⟨E.a, E.left_mem_verts⟩} := {xD, yD, zD}
  have hbS : bD ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h | h
    · apply E.right_not_mem_side
      have hv := congrArg (fun w ↦ w.1.1) h
      change E.b = C.x.1 at hv
      rw [hv]
      exact C.x_mem_side
    · apply E.right_not_mem_side
      have hv := congrArg (fun w ↦ w.1.1) h
      change E.b = C.y.1 at hv
      rw [hv]
      exact C.y_mem_side
    · apply E.right_not_mem_side
      have hv := congrArg (fun w ↦ w.1.1) h
      change E.b = C.z.1 at hv
      rw [hv]
      exact C.z_mem_side
  have hxDyD : xD ≠ yD := by
    intro h
    exact C.x_ne_y (congrArg Subtype.val h)
  have hScard : 2 ≤ S.card := by
    have hpair : ({xD, yD} : Finset {w : {v : V // v ∈ E.verts} //
        w ≠ ⟨E.a, E.left_mem_verts⟩}).card = 2 := by
      simp [hxDyD]
    rw [← hpair]
    exact Finset.card_le_card (by simp [S])
  obtain ⟨s, t, hsS, htS, hst, p, hp, hbp, htarget⟩ :=
    exists_targetPath_through_of_vertexTwoConnected
      S hbS hScard h2.1 h2.2
  let inc : H →g E.torso :=
    (SimpleGraph.Embedding.induce (G := E.torso)
      (s := fun w : {v : V // v ∈ E.verts} ↦
        w ≠ ⟨E.a, E.left_mem_verts⟩)).toHom
  let pT : E.torso.Walk s.1 t.1 := p.map inc
  have hpT : pT.IsPath := hp.map Subtype.val_injective
  have hbT : (⟨E.b, E.right_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∈ pT.support := by
    change (⟨E.b, E.right_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨bD, hbp, rfl⟩
  have haT : (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∉ pT.support := by
    change (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∉ (p.map inc).support
    rw [Walk.support_map]
    intro ha
    obtain ⟨w, -, hw⟩ := List.mem_map.mp ha
    change w.1 = ⟨E.a, E.left_mem_verts⟩ at hw
    exact w.2 hw
  have endpointTarget (u : {w : {v : V // v ∈ E.verts} //
      w ≠ ⟨E.a, E.left_mem_verts⟩}) (hu : u ∈ S) :
      u.1 = C.x ∨ u.1 = C.y ∨ u.1 = C.z := by
    have huCases : u = xD ∨ u = yD ∨ u = zD := by
      simpa only [S, Finset.mem_insert, Finset.mem_singleton] using hu
    rcases huCases with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have htargetT : ∀ w, w ∈ pT.support →
      (w = C.x ∨ w = C.y ∨ w = C.z) →
        w = s.1 ∨ w = t.1 := by
    intro w hwp hwTarget
    change w ∈ (p.map inc).support at hwp
    rw [Walk.support_map] at hwp
    obtain ⟨wD, hwDp, hwD⟩ := List.mem_map.mp hwp
    change wD.1 = w at hwD
    have hwDS : wD ∈ S := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton]
      rcases hwTarget with rfl | rfl | rfl
      · exact Or.inl (Subtype.ext hwD)
      · exact Or.inr (Or.inl (Subtype.ext hwD))
      · exact Or.inr (Or.inr (Subtype.ext hwD))
    rcases htarget wD hwDp hwDS with h | h
    · exact Or.inl (hwD.symm.trans (congrArg Subtype.val h))
    · exact Or.inr (hwD.symm.trans (congrArg Subtype.val h))
  exact ⟨{
    s := s.1
    t := t.1
    s_target := endpointTarget s hsS
    t_target := endpointTarget t htS
    s_ne_t := fun h ↦ hst (Subtype.ext h)
    path := pT
    path_isPath := hpT
    right_mem := hbT
    left_not_mem := haT
    target_clean := htargetT }⟩

/-- At exact left-attachment degree three, the second target-minimal path
cannot contain the putative twin.  Its path-neighbours would have to be the
two target endpoints, while the right attachment is a third displayed path
vertex distinct from both endpoints and from the twin. -/
theorem LeftClaim10SecondFan.twin_not_mem_of_degree_eq_three
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10SecondFan C)
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3)
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a') :
    a' ∉ F.path.support := by
  have htwinN : F.path.toSubgraph.neighborSet a' ⊆
      ({F.s, F.t} : Set {v : V // v ∈ E.verts}) := by
    intro w hw
    have hws : w ∈ F.path.support := by
      simpa only [Walk.mem_verts_toSubgraph] using hw.snd_mem
    have ha'w : E.torso.Adj a' w := F.path.toSubgraph.adj_sub hw
    have hwN : w ∈ E.torso.neighborFinset a' := by
      simpa only [SimpleGraph.mem_neighborFinset] using ha'w
    rw [C.torso_twin_neighbors_eq (E := E) hdeg htwin] at hwN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwN
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      F.target_clean w hws hwN
  exact Walk.IsPath.not_mem_support_of_neighbors_subset_endpoints_of_extra
    F.path_isPath F.s_ne_t
      htwinN (C.twin_ne_target (E := E) F.s_target)
      (C.twin_ne_target (E := E) F.t_target) F.right_mem
      (C.right_ne_target (E := E) F.s_target)
      (C.right_ne_target (E := E) F.t_target)
      (C.twin_ne_right (E := E)).symm

/-- Split the second target-minimal path at the right attachment, producing
the source's two arms `P'`,`Q'`. -/
structure LeftClaim10SecondArms
    {a' : {v : V // v ∈ E.verts}} (C : E.LeftClaim10Initial a') where
  s : {v : V // v ∈ E.verts}
  t : {v : V // v ∈ E.verts}
  s_target : s = C.x ∨ s = C.y ∨ s = C.z
  t_target : t = C.x ∨ t = C.y ∨ t = C.z
  s_ne_t : s ≠ t
  left : E.torso.Walk ⟨E.b, E.right_mem_verts⟩ s
  right : E.torso.Walk ⟨E.b, E.right_mem_verts⟩ t
  left_isPath : left.IsPath
  right_isPath : right.IsPath
  tails_disjoint : left.support.tail.Disjoint right.support.tail
  left_attachment_not_mem_left :
    (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) ∉
      left.support
  left_attachment_not_mem_right :
    (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) ∉
      right.support
  target_clean_left : ∀ w, w ∈ left.support →
    (w = C.x ∨ w = C.y ∨ w = C.z) → w = s ∨ w = t
  target_clean_right : ∀ w, w ∈ right.support →
    (w = C.x ∨ w = C.y ∨ w = C.z) → w = s ∨ w = t

/-- Reverse the ordering of the two second-fan endpoints. -/
def LeftClaim10SecondArms.reverse
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (B : E.LeftClaim10SecondArms C) : E.LeftClaim10SecondArms C where
  s := B.t
  t := B.s
  s_target := B.t_target
  t_target := B.s_target
  s_ne_t := B.s_ne_t.symm
  left := B.right
  right := B.left
  left_isPath := B.right_isPath
  right_isPath := B.left_isPath
  tails_disjoint := B.tails_disjoint.symm
  left_attachment_not_mem_left := B.left_attachment_not_mem_right
  left_attachment_not_mem_right := B.left_attachment_not_mem_left
  target_clean_left := by
    intro w hw hwTarget
    rcases B.target_clean_right w hw hwTarget with h | h
    · exact Or.inr h
    · exact Or.inl h
  target_clean_right := by
    intro w hw hwTarget
    rcases B.target_clean_left w hw hwTarget with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- Exchange `y,z` in a second fan without changing its paths. -/
def LeftClaim10SecondArms.swapYZ
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (B : E.LeftClaim10SecondArms C) :
    E.LeftClaim10SecondArms C.swapYZ where
  s := B.s
  t := B.t
  s_target := by
    rcases B.s_target with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  t_target := by
    rcases B.t_target with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  s_ne_t := B.s_ne_t
  left := B.left
  right := B.right
  left_isPath := B.left_isPath
  right_isPath := B.right_isPath
  tails_disjoint := B.tails_disjoint
  left_attachment_not_mem_left := B.left_attachment_not_mem_left
  left_attachment_not_mem_right := B.left_attachment_not_mem_right
  target_clean_left := by
    intro w hw hwTarget
    apply B.target_clean_left w hw
    rcases hwTarget with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  target_clean_right := by
    intro w hw hwTarget
    apply B.target_clean_right w hw
    rcases hwTarget with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

/-- The six possible ordered endpoint pairs of a second fan.  The three
diagonal cases are excluded by `s_ne_t`. -/
theorem LeftClaim10SecondArms.endpoint_cases
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (B : E.LeftClaim10SecondArms C) :
    (B.s = C.x ∧ B.t = C.y) ∨
    (B.s = C.y ∧ B.t = C.x) ∨
    (B.s = C.x ∧ B.t = C.z) ∨
    (B.s = C.z ∧ B.t = C.x) ∨
    (B.s = C.y ∧ B.t = C.z) ∨
    (B.s = C.z ∧ B.t = C.y) := by
  rcases B.s_target with hs | hs | hs <;>
    rcases B.t_target with ht | ht | ht
  · exact False.elim (B.s_ne_t (hs.trans ht.symm))
  · exact Or.inl ⟨hs, ht⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hs, ht⟩))
  · exact Or.inr (Or.inl ⟨hs, ht⟩)
  · exact False.elim (B.s_ne_t (hs.trans ht.symm))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, ht⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, ht⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hs, ht⟩))))
  · exact False.elim (B.s_ne_t (hs.trans ht.symm))

/-- The first intersection, travelling from the right attachment along a
second-fan arm, with the normalized first-fan path.  The exact prefix and
its support inclusion are retained for the subsequent splice. -/
structure LeftClaim10FirstHit
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
  (F : E.LeftClaim10YZFan C) (B : E.LeftClaim10SecondArms C) where
  hit : {v : V // v ∈ E.verts}
  pref : E.torso.Walk ⟨E.b, E.right_mem_verts⟩ hit
  pref_isPath : pref.IsPath
  hit_mem_first : hit ∈ F.path.support
  hit_ne_y : hit ≠ C.y
  pref_subset_second_left : ∀ w, w ∈ pref.support →
    w ∈ B.left.support
  pref_meets_first_only_at_hit : ∀ w, w ∈ pref.support →
    w ∈ F.path.support → w = hit
  y_not_mem_pref : C.y ∉ pref.support

/-- Extract the exact first-hit prefix from any improper intersection of
the `y`-ending second arm with the normalized first fan. -/
theorem exists_leftClaim10FirstHit_of_left_crossing
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y)
    (hcross : ∃ w, w ∈ B.left.support ∧
      w ∈ F.path.support ∧ w ≠ C.y) :
    Nonempty (E.LeftClaim10FirstHit F B) := by
  let b : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  let R : E.torso.Walk b C.y := B.left.copy rfl hsy
  have hR : R.IsPath := (Walk.isPath_copy _ _ _).mpr B.left_isPath
  have hRSupport : R.support = B.left.support := by
    simp only [R, Walk.support_copy]
  let S : Finset {v : V // v ∈ E.verts} := F.path.support.toFinset
  have hbS : b ∉ S := by
    simpa only [S, List.mem_toFinset, b] using F.right_not_mem
  have hyS : C.y ∈ S := by simp [S]
  obtain ⟨w, hwR, hwS, hwPath, hfirst⟩ :=
    exists_firstHitPrefix_to_finset S hbS hyS R hR
  obtain ⟨u, huB, huF, huy⟩ := hcross
  have huR : u ∈ R.support := by simpa only [hRSupport] using huB
  have huS : u ∈ S := by simpa only [S, List.mem_toFinset] using huF
  have hwy : w ≠ C.y :=
    firstHit_ne_end_of_distinct_hit S R hR hwR hfirst huR huS huy
  let q : E.torso.Walk b w := R.takeUntil w hwR
  exact ⟨{
    hit := w
    pref := q
    pref_isPath := hwPath
    hit_mem_first := by simpa only [S, List.mem_toFinset] using hwS
    hit_ne_y := hwy
    pref_subset_second_left := by
      intro v hv
      have hvR : v ∈ R.support := R.support_takeUntil_subset_support hwR hv
      simpa only [hRSupport] using hvR
    pref_meets_first_only_at_hit := by
      intro v hvq hvF
      apply hfirst v hvq
      simpa only [S, List.mem_toFinset] using hvF
    y_not_mem_pref := by
      exact Walk.endpoint_notMem_support_takeUntil hR hwR hwy.symm }⟩

/-- First-hit extraction when the endpoint of the chosen second-fan arm is
outside the normalized first fan.  This is the form needed for the other
arm in the `y,x` and `y,z` endpoint cases.  The returned strict prefix does
not contain the endpoint of the full arm. -/
theorem exists_leftClaim10FirstHit_of_left_crossing_away
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (B : E.LeftClaim10SecondArms C)
    (hyNot : C.y ∉ B.left.support)
    (hendNot : B.s ∉ F.path.support)
    (hcross : ∃ w, w ∈ B.left.support ∧ w ∈ F.path.support) :
    ∃ H : E.LeftClaim10FirstHit F B, B.s ∉ H.pref.support := by
  let b : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  let S : Finset {v : V // v ∈ E.verts} := F.path.support.toFinset
  have hbS : b ∉ S := by
    simpa only [S, List.mem_toFinset, b] using F.right_not_mem
  obtain ⟨u, huB, huF⟩ := hcross
  have huS : u ∈ S := by
    simpa only [S, List.mem_toFinset] using huF
  have hus : u ≠ B.s := by
    intro h
    apply hendNot
    simpa only [h] using huF
  let R : E.torso.Walk b u := B.left.takeUntil u huB
  have hR : R.IsPath := B.left_isPath.takeUntil huB
  have hsNotR : B.s ∉ R.support := by
    exact Walk.endpoint_notMem_support_takeUntil B.left_isPath huB hus.symm
  obtain ⟨w, hwR, hwS, hwPath, hfirst⟩ :=
    exists_firstHitPrefix_to_finset S hbS huS R hR
  let q : E.torso.Walk b w := R.takeUntil w hwR
  have qSubsetLeft {v : {v : V // v ∈ E.verts}} (hv : v ∈ q.support) :
      v ∈ B.left.support := by
    apply B.left.support_takeUntil_subset_support huB
    apply R.support_takeUntil_subset_support hwR
    exact hv
  let H : E.LeftClaim10FirstHit F B := {
    hit := w
    pref := q
    pref_isPath := hwPath
    hit_mem_first := by simpa only [S, List.mem_toFinset] using hwS
    hit_ne_y := by
      intro hwy
      have hwq : w ∈ q.support := q.end_mem_support
      exact hyNot (qSubsetLeft (hwy ▸ hwq))
    pref_subset_second_left := by
      intro v hv
      exact qSubsetLeft hv
    pref_meets_first_only_at_hit := by
      intro v hvq hvF
      apply hfirst v hvq
      simpa only [S, List.mem_toFinset] using hvF
    y_not_mem_pref := by
      intro hyq
      exact hyNot (qSubsetLeft hyq) }
  refine ⟨H, ?_⟩
  change B.s ∉ q.support
  intro hsq
  apply hsNotR
  exact R.support_takeUntil_subset_support hwR hsq

/-- Splice a first-hit prefix to the appropriate side of the normalized
first fan.  The result is a genuine target-clean first fan with a boundary
endpoint, not merely a closed walk.  The two nonmembership assumptions are
properties of the `y`-ending second arm proved separately in each endpoint
case. -/
theorem LeftClaim10FirstHit.toBoundaryFirstFan
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    {F : E.LeftClaim10YZFan C} {B : E.LeftClaim10SecondArms C}
    (H : E.LeftClaim10FirstHit F B)
    (hxPrefix : C.x ∉ H.pref.support)
    (hzPrefix : C.z ∉ H.pref.support) :
    ∃ F' : E.LeftClaim10FirstFan C,
      F'.s = ⟨E.b, E.right_mem_verts⟩ ∨
      F'.t = ⟨E.b, E.right_mem_verts⟩ := by
  let b : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  have hbx : b ≠ C.x := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change E.b = C.x.1 at hv
    rw [hv]
    exact C.x_mem_side
  have hby : b ≠ C.y := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change E.b = C.y.1 at hv
    rw [hv]
    exact C.y_mem_side
  have hbz : b ≠ C.z := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change E.b = C.z.1 at hv
    rw [hv]
    exact C.z_mem_side
  rcases mem_dropUntil_or_mem_dropUntil F.path H.hit_mem_first F.next_mem with
      hnextAfter | hhitAfter
  · let D : E.torso.Walk H.hit C.z :=
      F.path.dropUntil H.hit H.hit_mem_first
    let q : E.torso.Walk b C.z := H.pref.append D
    have hD : D.IsPath := F.path_isPath.dropUntil H.hit_mem_first
    have hnextD : C.x' ∈ D.support := by
      simpa only [D] using hnextAfter
    have hinter : ∀ w, w ∈ H.pref.support →
        w ∈ D.support → w = H.hit := by
      intro w hwP hwD
      apply H.pref_meets_first_only_at_hit w hwP
      exact F.path.support_dropUntil_subset_support H.hit_mem_first hwD
    have hq : q.IsPath :=
      Walk.IsPath.append_of_meet_only_endpoint H.pref_isPath hD hinter
    have hyNotD : C.y ∉ D.support := by
      intro hyD
      have hstart := eq_start_of_mem_dropUntil F.path F.path_isPath
        H.hit_mem_first hyD
      exact H.hit_ne_y hstart
    let F' : E.LeftClaim10FirstFan C := {
      s := b
      t := C.z
      s_target := Or.inr (Or.inr rfl)
      t_target := Or.inr (Or.inl rfl)
      s_ne_t := hbz
      path := q
      path_isPath := hq
      next_mem := by
        dsimp only [q]
        rw [Walk.mem_support_append_iff]
        exact Or.inr hnextD
      deleted_not_mem := by
        intro hxq
        have hxCases : C.x ∈ H.pref.support ∨ C.x ∈ D.support := by
          simpa only [q, Walk.mem_support_append_iff] using hxq
        exact hxCases.elim hxPrefix (fun h ↦ F.deleted_not_mem
          (F.path.support_dropUntil_subset_support H.hit_mem_first h))
      target_clean := by
        intro w hwq hwTarget
        have hwCases : w ∈ H.pref.support ∨ w ∈ D.support := by
          simpa only [q, Walk.mem_support_append_iff] using hwq
        rcases hwTarget with hwy | hwz | hwb
        · subst w
          exact False.elim (hwCases.elim H.y_not_mem_pref hyNotD)
        · exact Or.inr hwz
        · exact Or.inl hwb }
    exact ⟨F', Or.inl rfl⟩
  · let L : E.torso.Walk C.y H.hit :=
      F.path.takeUntil H.hit H.hit_mem_first
    let q : E.torso.Walk C.y b := L.append H.pref.reverse
    have hL : L.IsPath := F.path_isPath.takeUntil H.hit_mem_first
    have hinter : ∀ w, w ∈ L.support →
        w ∈ H.pref.reverse.support → w = H.hit := by
      intro w hwL hwP
      have hwP' : w ∈ H.pref.support := by
        simpa [Walk.support_reverse] using hwP
      exact H.pref_meets_first_only_at_hit w hwP'
        (F.path.support_takeUntil_subset_support H.hit_mem_first hwL)
    have hq : q.IsPath :=
      Walk.IsPath.append_of_meet_only_endpoint hL H.pref_isPath.reverse hinter
    have hzNotL : C.z ∉ L.support :=
      Walk.endpoint_notMem_support_takeUntil F.path_isPath H.hit_mem_first
        (by
          intro h
          apply hzPrefix
          rw [h]
          exact H.pref.end_mem_support)
    let F' : E.LeftClaim10FirstFan C := {
      s := C.y
      t := b
      s_target := Or.inl rfl
      t_target := Or.inr (Or.inr rfl)
      s_ne_t := hby.symm
      path := q
      path_isPath := hq
      next_mem := by
        simp only [q, Walk.mem_support_append_iff]
        left
        rcases mem_takeUntil_or_mem_takeUntil_local F.path
            H.hit_mem_first F.next_mem with hnextTake | hhitTake
        · simpa only [L] using hnextTake
        · by_cases heq : H.hit = C.x'
          · rw [← heq]
            exact L.end_mem_support
          · have hhitTail : H.hit ∈
                (F.path.dropUntil C.x' F.next_mem).support.tail := by
              have hcases : H.hit = C.x' ∨ H.hit ∈
                  (F.path.dropUntil C.x' F.next_mem).support.tail := by
                apply List.mem_cons.mp
                rw [(F.path.dropUntil C.x' F.next_mem).cons_tail_support]
                exact hhitAfter
              exact hcases.resolve_left heq
            have hnd :
                ((F.path.takeUntil C.x' F.next_mem).support ++
                  (F.path.dropUntil C.x' F.next_mem).support.tail).Nodup := by
              simpa only [← Walk.support_append,
                F.path.take_spec F.next_mem] using F.path_isPath.support_nodup
            exact False.elim
              ((List.nodup_append.mp hnd).2.2 H.hit hhitTake
                H.hit hhitTail rfl)
      deleted_not_mem := by
        intro hxq
        have hxCases : C.x ∈ L.support ∨ C.x ∈ H.pref.support := by
          simpa [q, Walk.mem_support_append_iff, Walk.support_reverse] using hxq
        exact hxCases.elim (fun h ↦ F.deleted_not_mem
          (F.path.support_takeUntil_subset_support H.hit_mem_first h)) hxPrefix
      target_clean := by
        intro w hwq hwTarget
        have hwCases : w ∈ L.support ∨ w ∈ H.pref.support := by
          simpa [q, Walk.mem_support_append_iff, Walk.support_reverse] using hwq
        rcases hwTarget with hwy | hwz | hwb
        · exact Or.inl hwy
        · subst w
          exact False.elim (hwCases.elim hzNotL hzPrefix)
        · exact Or.inr hwb }
    exact ⟨F', Or.inr rfl⟩

/-- The two second-fan arms meet only at their common start, the right
attachment. -/
theorem LeftClaim10SecondArms.meet_only_boundary
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (A : E.LeftClaim10SecondArms C) {w : {v : V // v ∈ E.verts}}
    (hwL : w ∈ A.left.support) (hwR : w ∈ A.right.support) :
    w = ⟨E.b, E.right_mem_verts⟩ := by
  by_cases h : w = (⟨E.b, E.right_mem_verts⟩ :
      {v : V // v ∈ E.verts})
  · exact h
  have hwLTail : w ∈ A.left.support.tail := by
    rw [← A.left.cons_tail_support] at hwL
    exact (List.mem_cons.mp hwL).resolve_left h
  have hwRTail : w ∈ A.right.support.tail := by
    rw [← A.right.cons_tail_support] at hwR
    exact (List.mem_cons.mp hwR).resolve_left h
  exact False.elim (List.disjoint_left.mp A.tails_disjoint hwLTail hwRTail)

/-- In the `y,x` endpoint case, the `y`-arm contains neither of the other
two targets. -/
theorem LeftClaim10SecondArms.left_avoids_xz_of_yx
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htx : B.t = C.x) :
    C.x ∉ B.left.support ∧ C.z ∉ B.left.support := by
  have hxRight : C.x ∈ B.right.support := by
    simpa only [htx] using B.right.end_mem_support
  have hxb : C.x ≠
      (⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change C.x.1 = E.b at hv
    rw [← hv]
    exact C.x_mem_side
  constructor
  · intro hxLeft
    exact hxb (LeftClaim10SecondArms.meet_only_boundary E B
      hxLeft hxRight)
  · intro hzLeft
    rcases B.target_clean_left C.z hzLeft (Or.inr (Or.inr rfl)) with h | h
    · exact C.y_ne_z (h.trans hsy).symm
    · exact C.x_ne_z (h.trans htx).symm

/-- In the `y,z` endpoint case, the `y`-arm contains neither `x` nor the
other endpoint `z`. -/
theorem LeftClaim10SecondArms.left_avoids_xz_of_yz
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htz : B.t = C.z) :
    C.x ∉ B.left.support ∧ C.z ∉ B.left.support := by
  have hzRight : C.z ∈ B.right.support := by
    simpa only [htz] using B.right.end_mem_support
  have hzb : C.z ≠
      (⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change C.z.1 = E.b at hv
    rw [← hv]
    exact C.z_mem_side
  constructor
  · intro hxLeft
    rcases B.target_clean_left C.x hxLeft (Or.inl rfl) with h | h
    · exact C.x_ne_y (h.trans hsy)
    · exact C.x_ne_z (h.trans htz)
  · intro hzLeft
    exact hzb (LeftClaim10SecondArms.meet_only_boundary E B
      hzLeft hzRight)

/-- In the `y,x` endpoint case, the `x`-ending arm contains neither `y`
nor the unused target `z`. -/
theorem LeftClaim10SecondArms.right_avoids_yz_of_yx
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htx : B.t = C.x) :
    C.y ∉ B.right.support ∧ C.z ∉ B.right.support := by
  have hyLeft : C.y ∈ B.left.support := by
    simpa only [hsy] using B.left.end_mem_support
  have hyb : C.y ≠
      (⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change C.y.1 = E.b at hv
    rw [← hv]
    exact C.y_mem_side
  constructor
  · intro hyRight
    exact hyb (LeftClaim10SecondArms.meet_only_boundary E B
      hyLeft hyRight)
  · intro hzRight
    rcases B.target_clean_right C.z hzRight (Or.inr (Or.inr rfl)) with h | h
    · exact C.y_ne_z (h.trans hsy).symm
    · exact C.x_ne_z (h.trans htx).symm

/-- In the `y,z` endpoint case, the `z`-ending arm contains neither `x`
nor the other endpoint `y`. -/
theorem LeftClaim10SecondArms.right_avoids_xy_of_yz
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htz : B.t = C.z) :
    C.x ∉ B.right.support ∧ C.y ∉ B.right.support := by
  have hyLeft : C.y ∈ B.left.support := by
    simpa only [hsy] using B.left.end_mem_support
  have hyb : C.y ≠
      (⟨E.b, E.right_mem_verts⟩ : {v : V // v ∈ E.verts}) := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change C.y.1 = E.b at hv
    rw [← hv]
    exact C.y_mem_side
  constructor
  · intro hxRight
    rcases B.target_clean_right C.x hxRight (Or.inl rfl) with h | h
    · exact C.x_ne_y (h.trans hsy)
    · exact C.x_ne_z (h.trans htz)
  · intro hyRight
    exact hyb (LeftClaim10SecondArms.meet_only_boundary E B
      hyLeft hyRight)

/-- An improper intersection in the `y,x` case splices to the source's
forbidden first fan with a right-boundary endpoint. -/
theorem exists_boundaryFirstFan_of_left_crossing_yx
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htx : B.t = C.x)
    (hcross : ∃ w, w ∈ B.left.support ∧
      w ∈ F.path.support ∧ w ≠ C.y) :
    ∃ F' : E.LeftClaim10FirstFan C,
      F'.s = ⟨E.b, E.right_mem_verts⟩ ∨
      F'.t = ⟨E.b, E.right_mem_verts⟩ := by
  obtain ⟨H⟩ := E.exists_leftClaim10FirstHit_of_left_crossing F B hsy hcross
  obtain ⟨hx, hz⟩ := LeftClaim10SecondArms.left_avoids_xz_of_yx E B hsy htx
  exact LeftClaim10FirstHit.toBoundaryFirstFan E H
    (fun h ↦ hx (H.pref_subset_second_left C.x h))
    (fun h ↦ hz (H.pref_subset_second_left C.z h))

/-- The same first-hit splice for the `y,z` endpoint case. -/
theorem exists_boundaryFirstFan_of_left_crossing_yz
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htz : B.t = C.z)
    (hcross : ∃ w, w ∈ B.left.support ∧
      w ∈ F.path.support ∧ w ≠ C.y) :
    ∃ F' : E.LeftClaim10FirstFan C,
      F'.s = ⟨E.b, E.right_mem_verts⟩ ∨
      F'.t = ⟨E.b, E.right_mem_verts⟩ := by
  obtain ⟨H⟩ := E.exists_leftClaim10FirstHit_of_left_crossing F B hsy hcross
  obtain ⟨hx, hz⟩ := LeftClaim10SecondArms.left_avoids_xz_of_yz E B hsy htz
  exact LeftClaim10FirstHit.toBoundaryFirstFan E H
    (fun h ↦ hx (H.pref_subset_second_left C.x h))
    (fun h ↦ hz (H.pref_subset_second_left C.z h))

/-- A crossing of the other second arm in the `y,x` case is handled by
reversing the two arms and stopping at its first meeting with the normalized
first fan.  The endpoint `x` is absent from that fan, so the strict prefix
has exactly the avoidance needed by the splice. -/
theorem exists_boundaryFirstFan_of_right_crossing_yx
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htx : B.t = C.x)
    (hcross : ∃ w, w ∈ B.right.support ∧
      w ∈ F.path.support ∧ w ≠ C.x) :
    ∃ F' : E.LeftClaim10FirstFan C,
      F'.s = ⟨E.b, E.right_mem_verts⟩ ∨
      F'.t = ⟨E.b, E.right_mem_verts⟩ := by
  obtain ⟨hyRight, hzRight⟩ :=
    LeftClaim10SecondArms.right_avoids_yz_of_yx E B hsy htx
  obtain ⟨w, hwRight, hwF, -⟩ := hcross
  obtain ⟨H, hxPref⟩ :=
    E.exists_leftClaim10FirstHit_of_left_crossing_away F B.reverse
      (by simpa only [LeftClaim10SecondArms.reverse] using hyRight)
      (by simpa only [LeftClaim10SecondArms.reverse, htx] using
        F.deleted_not_mem)
      ⟨w, by simpa only [LeftClaim10SecondArms.reverse] using hwRight, hwF⟩
  apply LeftClaim10FirstHit.toBoundaryFirstFan E H
  · simpa only [LeftClaim10SecondArms.reverse, htx] using hxPref
  · intro hzPref
    apply hzRight
    exact H.pref_subset_second_left C.z hzPref

/-- In the `y,z` case, a crossing of the right arm becomes the preceding
left-arm crossing after exchanging `y,z` and reversing the two second arms. -/
theorem exists_boundaryFirstFan_of_right_crossing_yz
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (A : E.LeftClaim10YZArms C)
    (B : E.LeftClaim10SecondArms C)
    (hA : ∀ w, w ∈ A.left.support → w ∈ F.path.support)
    (hsy : B.s = C.y) (htz : B.t = C.z)
    (hcross : ∃ w, w ∈ B.right.support ∧
      w ∈ A.left.support ∧ w ≠ C.z) :
    ∃ F' : E.LeftClaim10FirstFan C.swapYZ,
      F'.s = ⟨E.b, E.right_mem_verts⟩ ∨
      F'.t = ⟨E.b, E.right_mem_verts⟩ := by
  obtain ⟨w, hwRight, hwA, hwz⟩ := hcross
  apply E.exists_boundaryFirstFan_of_left_crossing_yz
    F.swapYZ B.swapYZ.reverse
  · change B.t = C.z
    exact htz
  · change B.s = C.y
    exact hsy
  · refine ⟨w, ?_, ?_, ?_⟩
    · simpa only [LeftClaim10SecondArms.swapYZ,
        LeftClaim10SecondArms.reverse] using hwRight
    · change w ∈ F.path.reverse.support
      rw [Walk.support_reverse, List.mem_reverse]
      exact hA w hwA
    · exact hwz

/-- The two internally disjoint arms encoded by the second fan, together
with their inclusions in the original target-minimal path. -/
theorem LeftClaim10SecondFan.toArms_with_subsets
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10SecondFan C) :
    ∃ B : E.LeftClaim10SecondArms C,
      (∀ w, w ∈ B.left.support → w ∈ F.path.support) ∧
      (∀ w, w ∈ B.right.support → w ∈ F.path.support) := by
  let P : E.torso.Walk ⟨E.b, E.right_mem_verts⟩ F.s :=
    (F.path.takeUntil ⟨E.b, E.right_mem_verts⟩ F.right_mem).reverse
  let Q : E.torso.Walk ⟨E.b, E.right_mem_verts⟩ F.t :=
    F.path.dropUntil ⟨E.b, E.right_mem_verts⟩ F.right_mem
  have hP : P.IsPath :=
    (F.path_isPath.takeUntil F.right_mem).reverse
  have hQ : Q.IsPath := F.path_isPath.dropUntil F.right_mem
  have hdisj : P.support.tail.Disjoint Q.support.tail := by
    have hnd :
        ((F.path.takeUntil ⟨E.b, E.right_mem_verts⟩
            F.right_mem).support ++ Q.support.tail).Nodup := by
      simpa only [← Walk.support_append, Q,
        F.path.take_spec F.right_mem] using F.path_isPath.support_nodup
    rw [List.disjoint_left]
    intro w hwP hwQ
    have hwTake : w ∈
        (F.path.takeUntil ⟨E.b, E.right_mem_verts⟩
          F.right_mem).support := by
      have : w ∈ P.support := List.mem_of_mem_tail hwP
      simpa [P, Walk.support_reverse] using this
    exact ((List.nodup_append.mp hnd).2.2 w hwTake w hwQ) rfl
  have Psubset {w : {v : V // v ∈ E.verts}} (hw : w ∈ P.support) :
      w ∈ F.path.support := by
    apply F.path.support_takeUntil_subset_support F.right_mem
    simpa [P, Walk.support_reverse] using hw
  have Qsubset {w : {v : V // v ∈ E.verts}} (hw : w ∈ Q.support) :
      w ∈ F.path.support :=
    F.path.support_dropUntil_subset_support F.right_mem hw
  refine ⟨{
    s := F.s
    t := F.t
    s_target := F.s_target
    t_target := F.t_target
    s_ne_t := F.s_ne_t
    left := P
    right := Q
    left_isPath := hP
    right_isPath := hQ
    tails_disjoint := hdisj
    left_attachment_not_mem_left := fun h ↦ F.left_not_mem (Psubset h)
    left_attachment_not_mem_right := fun h ↦ F.left_not_mem (Qsubset h)
    target_clean_left := fun w hw hwT ↦ F.target_clean w (Psubset hw) hwT
    target_clean_right := fun w hw hwT ↦ F.target_clean w (Qsubset hw) hwT },
    ?_, ?_⟩
  · intro w hw
    exact Psubset hw
  · intro w hw
    exact Qsubset hw

/-- Convenience form retaining only the two-arm certificate. -/
theorem LeftClaim10SecondFan.toArms
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10SecondFan C) :
    Nonempty (E.LeftClaim10SecondArms C) := by
  obtain ⟨B, -, -⟩ := F.toArms_with_subsets
  exact ⟨B⟩

/-- The first of the two final wheel shapes in source Claim (10).  The
second fan ends at `y` and `x`.  If its two arms meet the normalized first
fan only at their indicated endpoints, and none of the paths contains the
putative centre `a'`, then the rim is

`y --(first fan)--> z -- a -- x --(second fan)--> b -- y`.

All its edges are actual end-torso edges (the virtual edge `ab` is not
used), and `a'` has the three spokes to `x,y,z`. -/
theorem hasWheelCenteredAt_twin_of_cleanCrossing_yx
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htx : B.t = C.x)
    (hfirstLeft : (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∉ F.path.support)
    (hfirstTwin : a' ∉ F.path.support)
    (hsecondTwinLeft : a' ∉ B.left.support)
    (hsecondTwinRight : a' ∉ B.right.support)
    (hcrossLeft : ∀ w, w ∈ B.left.support →
      w ∈ F.path.support → w = C.y)
    (hcrossRight : ∀ w, w ∈ B.right.support →
      w ∈ F.path.support → w = C.x) :
    HasWheelCenteredAt E.torso a' := by
  let a : {v : V // v ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  let b : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  let L : E.torso.Walk C.y b := B.left.reverse.copy hsy rfl
  let R : E.torso.Walk C.x b := B.right.reverse.copy htx rfl
  have hL : L.IsPath :=
    (Walk.isPath_copy _ _ _).mpr B.left_isPath.reverse
  have hR : R.IsPath :=
    (Walk.isPath_copy _ _ _).mpr B.right_isPath.reverse
  have hza : E.torso.Adj C.z a := by
    exact (show E.torso.Adj a C.z from Or.inl C.left_adj_z).symm
  have hax : E.torso.Adj a C.x := Or.inl C.left_adj_x
  let inside : E.torso.Walk C.y C.x :=
    (F.path.concat hza).concat hax
  have hinside1 : (F.path.concat hza).IsPath :=
    F.path_isPath.concat (by simpa only [a] using hfirstLeft) hza
  have hxa : C.x ≠ a := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change C.x.1 = E.a at hv
    rw [← hv]
    exact C.x_mem_side
  have hxNotInside1 : C.x ∉ (F.path.concat hza).support := by
    intro hx
    have hxCases : C.x ∈ F.path.support ∨ C.x = a := by
      simpa using hx
    exact hxCases.elim F.deleted_not_mem hxa
  have hinside : inside.IsPath :=
    hinside1.concat hxNotInside1 hax
  have hby : b ≠ C.y := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change E.b = C.y.1 at hv
    rw [hv]
    exact C.y_mem_side
  have hbx : b ≠ C.x := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change E.b = C.x.1 at hv
    rw [hv]
    exact C.x_mem_side
  have harms : ∀ w, w ∈ L.support → w ∈ R.support → w = b := by
    intro w hwL hwR
    have hwL' : w ∈ B.left.support := by
      simpa [L, Walk.support_copy, Walk.support_reverse] using hwL
    have hwR' : w ∈ B.right.support := by
      simpa [R, Walk.support_copy, Walk.support_reverse] using hwR
    simpa only [b] using
      LeftClaim10SecondArms.meet_only_boundary E B hwL' hwR'
  have hxRight : C.x ∈ B.right.support := by
    simpa only [htx] using B.right.end_mem_support
  have hleftInside : ∀ w, w ∈ L.support →
      w ∈ inside.support → w = C.y := by
    intro w hwL hwI
    have hwL' : w ∈ B.left.support := by
      simpa [L, Walk.support_copy, Walk.support_reverse] using hwL
    have hwCases : w ∈ F.path.support ∨ w = a ∨ w = C.x := by
      simpa [inside] using hwI
    rcases hwCases with hwF | hwa | hwx
    · exact hcrossLeft w hwL' hwF
    · subst w
      exact False.elim (B.left_attachment_not_mem_left (by simpa only [a] using hwL'))
    · subst w
      have hxb' :=
        LeftClaim10SecondArms.meet_only_boundary E B hwL' hxRight
      exact False.elim (hbx hxb'.symm)
  have hrightInside : ∀ w, w ∈ R.support →
      w ∈ inside.support → w = C.x := by
    intro w hwR hwI
    have hwR' : w ∈ B.right.support := by
      simpa [R, Walk.support_copy, Walk.support_reverse] using hwR
    have hwCases : w ∈ F.path.support ∨ w = a ∨ w = C.x := by
      simpa [inside] using hwI
    rcases hwCases with hwF | hwa | hwx
    · exact hcrossRight w hwR' hwF
    · subst w
      exact False.elim (B.left_attachment_not_mem_right (by simpa only [a] using hwR'))
    · exact hwx
  have hkL : a' ∉ L.support := by
    simpa [L, Walk.support_copy, Walk.support_reverse] using hsecondTwinLeft
  have hkR : a' ∉ R.support := by
    simpa [R, Walk.support_copy, Walk.support_reverse] using hsecondTwinRight
  have ha'a : a' ≠ a := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change a'.1 = E.a at hv
    rw [← hv]
    exact C.twin_mem_side
  have hka : a' ∉ inside.support := by
    intro hk
    have hkCases : a' ∈ F.path.support ∨ a' = a ∨ a' = C.x := by
      simpa [inside] using hk
    rcases hkCases with hkF | hka | hkx
    · exact hfirstTwin hkF
    · exact ha'a hka
    · exact C.twin_adj_x.ne hkx
  apply hasWheelCenteredAt_of_cleanTwoFan_inside_three
    L R inside hL hR hinside C.x_ne_y.symm hby hbx harms
      hleftInside hrightInside hkL hkR hka
  · exact (show E.torso.Adj a' C.x from Or.inl C.twin_adj_x)
  · exact (show E.torso.Adj a' C.y from Or.inl C.twin_adj_y)
  · exact (show E.torso.Adj a' C.z from Or.inl C.twin_adj_z)
  · simp [inside]
  · simp [inside]
  · simp [inside]
  · exact C.x_ne_y
  · exact C.x_ne_z
  · exact C.y_ne_z

/-- The second final wheel shape in source Claim (10).  When the second fan
ends at `y` and `z`, use only the first `x'`--`y` arm and close through
`x'-x-a-z`; the second fan supplies the other `y`--`z` route through `b`.
Again `a'` is the centre with spokes to `x,y,z`. -/
theorem hasWheelCenteredAt_twin_of_cleanCrossing_yz
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (A : E.LeftClaim10YZArms C) (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htz : B.t = C.z)
    (hfirstLeft : (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∉ A.left.support)
    (hfirstTwin : a' ∉ A.left.support)
    (hsecondTwinLeft : a' ∉ B.left.support)
    (hsecondTwinRight : a' ∉ B.right.support)
    (hcrossLeft : ∀ w, w ∈ B.left.support →
      w ∈ A.left.support → w = C.y)
    (hcrossRight : ∀ w, w ∈ B.right.support →
      w ∈ A.left.support → w = C.z) :
    HasWheelCenteredAt E.torso a' := by
  let a : {v : V // v ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  let b : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  let L : E.torso.Walk C.y b := B.left.reverse.copy hsy rfl
  let R : E.torso.Walk C.z b := B.right.reverse.copy htz rfl
  have hL : L.IsPath :=
    (Walk.isPath_copy _ _ _).mpr B.left_isPath.reverse
  have hR : R.IsPath :=
    (Walk.isPath_copy _ _ _).mpr B.right_isPath.reverse
  have hx'x : E.torso.Adj C.x' C.x := C.next_adj_x.symm
  have hxa : E.torso.Adj C.x a :=
    (show E.torso.Adj a C.x from Or.inl C.left_adj_x).symm
  have haz : E.torso.Adj a C.z := Or.inl C.left_adj_z
  let inside : E.torso.Walk C.y C.z :=
    ((A.left.reverse.concat hx'x).concat hxa).concat haz
  have hi1 : (A.left.reverse.concat hx'x).IsPath :=
    A.left_isPath.reverse.concat (by
      simpa [Walk.support_reverse] using A.deleted_not_mem_left) hx'x
  have hxaNe : C.x ≠ a := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change C.x.1 = E.a at hv
    rw [← hv]
    exact C.x_mem_side
  have haNotI1 : a ∉ (A.left.reverse.concat hx'x).support := by
    intro ha
    have haCases : a ∈ A.left.support ∨ a = C.x := by
      simpa [Walk.support_reverse] using ha
    exact haCases.elim (by simpa only [a] using hfirstLeft) hxaNe.symm
  have hi2 : ((A.left.reverse.concat hx'x).concat hxa).IsPath :=
    hi1.concat haNotI1 hxa
  have hzRight : C.z ∈ A.right.support := A.right.end_mem_support
  have hzNotLeft : C.z ∉ A.left.support := by
    intro hzL
    have hzEq := LeftClaim10YZArms.meet_only_next E A hzL hzRight
    exact C.next_ne_z hzEq.symm
  have hzaNe : C.z ≠ a := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change C.z.1 = E.a at hv
    rw [← hv]
    exact C.z_mem_side
  have hzNotI2 : C.z ∉ ((A.left.reverse.concat hx'x).concat hxa).support := by
    intro hz
    have hzCases : C.z ∈ A.left.support ∨ C.z = C.x ∨ C.z = a := by
      simpa [Walk.support_reverse] using hz
    rcases hzCases with hzL | hzx | hza
    · exact hzNotLeft hzL
    · exact C.x_ne_z hzx.symm
    · exact hzaNe hza
  have hinside : inside.IsPath := hi2.concat hzNotI2 haz
  have hby : b ≠ C.y := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change E.b = C.y.1 at hv
    rw [hv]
    exact C.y_mem_side
  have hbz : b ≠ C.z := by
    intro h
    apply E.right_not_mem_side
    have hv := congrArg Subtype.val h
    change E.b = C.z.1 at hv
    rw [hv]
    exact C.z_mem_side
  have harms : ∀ w, w ∈ L.support → w ∈ R.support → w = b := by
    intro w hwL hwR
    have hwL' : w ∈ B.left.support := by
      simpa [L, Walk.support_copy, Walk.support_reverse] using hwL
    have hwR' : w ∈ B.right.support := by
      simpa [R, Walk.support_copy, Walk.support_reverse] using hwR
    simpa only [b] using
      LeftClaim10SecondArms.meet_only_boundary E B hwL' hwR'
  have hxNotBLeft : C.x ∉ B.left.support := by
    intro hx
    rcases B.target_clean_left C.x hx (Or.inl rfl) with h | h
    · exact C.x_ne_y (h.trans hsy)
    · exact C.x_ne_z (h.trans htz)
  have hxNotBRight : C.x ∉ B.right.support := by
    intro hx
    rcases B.target_clean_right C.x hx (Or.inl rfl) with h | h
    · exact C.x_ne_y (h.trans hsy)
    · exact C.x_ne_z (h.trans htz)
  have hzBRight : C.z ∈ B.right.support := by
    simpa only [htz] using B.right.end_mem_support
  have hleftInside : ∀ w, w ∈ L.support →
      w ∈ inside.support → w = C.y := by
    intro w hwL hwI
    have hwL' : w ∈ B.left.support := by
      simpa [L, Walk.support_copy, Walk.support_reverse] using hwL
    have hwCases : w ∈ A.left.support ∨ w = C.x ∨ w = a ∨
        w = C.z := by
      simpa [inside, Walk.support_reverse] using hwI
    rcases hwCases with hwA | hwx | hwa | hwz
    · exact hcrossLeft w hwL' hwA
    · subst w
      exact False.elim (hxNotBLeft hwL')
    · subst w
      exact False.elim (B.left_attachment_not_mem_left (by simpa only [a] using hwL'))
    · subst w
      have hzb :=
        LeftClaim10SecondArms.meet_only_boundary E B hwL' hzBRight
      exact False.elim (hbz hzb.symm)
  have hrightInside : ∀ w, w ∈ R.support →
      w ∈ inside.support → w = C.z := by
    intro w hwR hwI
    have hwR' : w ∈ B.right.support := by
      simpa [R, Walk.support_copy, Walk.support_reverse] using hwR
    have hwCases : w ∈ A.left.support ∨ w = C.x ∨ w = a ∨
        w = C.z := by
      simpa [inside, Walk.support_reverse] using hwI
    rcases hwCases with hwA | hwx | hwa | hwz
    · exact hcrossRight w hwR' hwA
    · subst w
      exact False.elim (hxNotBRight hwR')
    · subst w
      exact False.elim (B.left_attachment_not_mem_right (by simpa only [a] using hwR'))
    · exact hwz
  have hkL : a' ∉ L.support := by
    simpa [L, Walk.support_copy, Walk.support_reverse] using hsecondTwinLeft
  have hkR : a' ∉ R.support := by
    simpa [R, Walk.support_copy, Walk.support_reverse] using hsecondTwinRight
  have ha'a : a' ≠ a := by
    intro h
    apply E.left_not_mem_side
    have hv := congrArg Subtype.val h
    change a'.1 = E.a at hv
    rw [← hv]
    exact C.twin_mem_side
  have hkInside : a' ∉ inside.support := by
    intro hk
    have hkCases : a' ∈ A.left.support ∨ a' = C.x ∨ a' = a ∨
        a' = C.z := by
      simpa [inside, Walk.support_reverse] using hk
    rcases hkCases with hkA | hkx | hka | hkz
    · exact hfirstTwin hkA
    · exact C.twin_adj_x.ne hkx
    · exact ha'a hka
    · exact C.twin_adj_z.ne hkz
  apply hasWheelCenteredAt_of_cleanTwoFan_inside_three
    L R inside hL hR hinside C.y_ne_z hby hbz harms
      hleftInside hrightInside hkL hkR hkInside
  · exact (show E.torso.Adj a' C.x from Or.inl C.twin_adj_x)
  · exact (show E.torso.Adj a' C.y from Or.inl C.twin_adj_y)
  · exact (show E.torso.Adj a' C.z from Or.inl C.twin_adj_z)
  · simp [inside]
  · simp [inside]
  · simp [inside]
  · exact C.x_ne_y
  · exact C.x_ne_z
  · exact C.y_ne_z

/-- The complete list of reasons why the `y,x` terminal splice may fail to
be clean.  This is an output predicate, not an additional hypothesis: the
next rerouting step in Claim (10) eliminates each of these alternatives.
Keeping the witnesses records exactly which two paths meet and at which
vertex. -/
def LeftClaim10YXObstruction
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (B : E.LeftClaim10SecondArms C) : Prop :=
  (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) ∈ F.path.support ∨
  a' ∈ F.path.support ∨
  a' ∈ B.left.support ∨
  a' ∈ B.right.support ∨
  (∃ w, w ∈ B.left.support ∧ w ∈ F.path.support ∧ w ≠ C.y) ∨
  (∃ w, w ∈ B.right.support ∧ w ∈ F.path.support ∧ w ≠ C.x)

/-- Honest reduction of the `y,x` endpoint case: either the displayed
source rim is already a wheel centred at the putative twin, or a concrete
collision/crossing witness remains for the rerouting argument. -/
theorem wheel_or_leftClaim10YXObstruction
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htx : B.t = C.x) :
    HasWheelCenteredAt E.torso a' ∨ E.LeftClaim10YXObstruction F B := by
  classical
  by_cases hfirstLeft : (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∈ F.path.support
  · exact Or.inr (Or.inl hfirstLeft)
  by_cases hfirstTwin : a' ∈ F.path.support
  · exact Or.inr (Or.inr (Or.inl hfirstTwin))
  by_cases hsecondTwinLeft : a' ∈ B.left.support
  · exact Or.inr (Or.inr (Or.inr (Or.inl hsecondTwinLeft)))
  by_cases hsecondTwinRight : a' ∈ B.right.support
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsecondTwinRight))))
  by_cases hcrossLeft : ∃ w, w ∈ B.left.support ∧
      w ∈ F.path.support ∧ w ≠ C.y
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcrossLeft)))))
  by_cases hcrossRight : ∃ w, w ∈ B.right.support ∧
      w ∈ F.path.support ∧ w ≠ C.x
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hcrossRight)))))
  left
  apply E.hasWheelCenteredAt_twin_of_cleanCrossing_yx F B hsy htx
  · exact hfirstLeft
  · exact hfirstTwin
  · exact hsecondTwinLeft
  · exact hsecondTwinRight
  · intro w hwB hwF
    by_contra hwy
    exact hcrossLeft ⟨w, hwB, hwF, hwy⟩
  · intro w hwB hwF
    by_contra hwx
    exact hcrossRight ⟨w, hwB, hwF, hwx⟩

/-- Every listed obstruction in the normalized `y,x` case is impossible at
exact attachment degree three.  Membership obstructions are excluded by the
exact-neighbourhood lemmas, and either crossing splices to a forbidden
boundary-ending first fan. -/
theorem not_leftClaim10YXObstruction_of_degree_eq_three
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htx : B.t = C.x)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hab : ¬G.Adj E.a E.b)
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3)
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a')
    (hsecondTwinLeft : a' ∉ B.left.support)
    (hsecondTwinRight : a' ∉ B.right.support) :
    ¬E.LeftClaim10YXObstruction F B := by
  obtain ⟨hfirstLeft, hfirstTwin⟩ :=
    F.avoids_left_and_twin_of_degree_eq_three (E := E) hab hdeg htwin
  intro hobs
  rcases hobs with h | h | h | h | h | h
  · exact hfirstLeft h
  · exact hfirstTwin h
  · exact hsecondTwinLeft h
  · exact hsecondTwinRight h
  · obtain ⟨F', hboundary⟩ :=
      E.exists_boundaryFirstFan_of_left_crossing_yx F B hsy htx h
    exact F'.not_boundary_of_degree_eq_three (E := E)
      hcentres hab hdeg htwin hboundary
  · obtain ⟨F', hboundary⟩ :=
      E.exists_boundaryFirstFan_of_right_crossing_yx F B hsy htx h
    exact F'.not_boundary_of_degree_eq_three (E := E)
      hcentres hab hdeg htwin hboundary

/-- The analogous explicit obstruction list for the `y,z` endpoint case.
Only the `x'`--`y` first arm is used by this rim. -/
def LeftClaim10YZObstruction
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (A : E.LeftClaim10YZArms C) (B : E.LeftClaim10SecondArms C) : Prop :=
  (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) ∈ A.left.support ∨
  a' ∈ A.left.support ∨
  a' ∈ B.left.support ∨
  a' ∈ B.right.support ∨
  (∃ w, w ∈ B.left.support ∧ w ∈ A.left.support ∧ w ≠ C.y) ∨
  (∃ w, w ∈ B.right.support ∧ w ∈ A.left.support ∧ w ≠ C.z)

/-- Honest reduction of the `y,z` endpoint case to its precise remaining
collision witnesses. -/
theorem wheel_or_leftClaim10YZObstruction
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (A : E.LeftClaim10YZArms C) (B : E.LeftClaim10SecondArms C)
    (hsy : B.s = C.y) (htz : B.t = C.z) :
    HasWheelCenteredAt E.torso a' ∨ E.LeftClaim10YZObstruction A B := by
  classical
  by_cases hfirstLeft : (⟨E.a, E.left_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ∈ A.left.support
  · exact Or.inr (Or.inl hfirstLeft)
  by_cases hfirstTwin : a' ∈ A.left.support
  · exact Or.inr (Or.inr (Or.inl hfirstTwin))
  by_cases hsecondTwinLeft : a' ∈ B.left.support
  · exact Or.inr (Or.inr (Or.inr (Or.inl hsecondTwinLeft)))
  by_cases hsecondTwinRight : a' ∈ B.right.support
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsecondTwinRight))))
  by_cases hcrossLeft : ∃ w, w ∈ B.left.support ∧
      w ∈ A.left.support ∧ w ≠ C.y
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcrossLeft)))))
  by_cases hcrossRight : ∃ w, w ∈ B.right.support ∧
      w ∈ A.left.support ∧ w ≠ C.z
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hcrossRight)))))
  left
  apply E.hasWheelCenteredAt_twin_of_cleanCrossing_yz A B hsy htz
  · exact hfirstLeft
  · exact hfirstTwin
  · exact hsecondTwinLeft
  · exact hsecondTwinRight
  · intro w hwB hwA
    by_contra hwy
    exact hcrossLeft ⟨w, hwB, hwA, hwy⟩
  · intro w hwB hwA
    by_contra hwz
    exact hcrossRight ⟨w, hwB, hwA, hwz⟩

/-- Every listed obstruction in the normalized `y,z` case is likewise
impossible.  The chosen `x'`--`y` arm is contained in the original normalized
fan, so its membership and crossing witnesses lift to the preceding
avoidance and first-hit lemmas. -/
theorem not_leftClaim10YZObstruction_of_degree_eq_three
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (A : E.LeftClaim10YZArms C)
    (B : E.LeftClaim10SecondArms C)
    (hA : ∀ w, w ∈ A.left.support → w ∈ F.path.support)
    (hsy : B.s = C.y) (htz : B.t = C.z)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hab : ¬G.Adj E.a E.b)
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3)
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a')
    (hsecondTwinLeft : a' ∉ B.left.support)
    (hsecondTwinRight : a' ∉ B.right.support) :
    ¬E.LeftClaim10YZObstruction A B := by
  obtain ⟨hfirstLeft, hfirstTwin⟩ :=
    F.avoids_left_and_twin_of_degree_eq_three (E := E) hab hdeg htwin
  intro hobs
  rcases hobs with h | h | h | h | h | h
  · exact hfirstLeft (hA _ h)
  · exact hfirstTwin (hA _ h)
  · exact hsecondTwinLeft h
  · exact hsecondTwinRight h
  · obtain ⟨w, hwB, hwA, hwy⟩ := h
    obtain ⟨F', hboundary⟩ :=
      E.exists_boundaryFirstFan_of_left_crossing_yz F B hsy htz
        ⟨w, hwB, hA w hwA, hwy⟩
    exact F'.not_boundary_of_degree_eq_three (E := E)
      hcentres hab hdeg htwin hboundary
  · obtain ⟨F', hboundary⟩ :=
      E.exists_boundaryFirstFan_of_right_crossing_yz F A B hA hsy htz h
    exact F'.not_boundary_of_degree_eq_three (E := E)
      hcentres hab hdeg htwin hboundary

/-- All obstruction shapes after using endpoint reversal and the `y,z`
symmetry.  Thus the subsequent first-hit argument can be written only for
the two normalized endpoint cases above. -/
def LeftClaim10EndpointObstruction
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (A : E.LeftClaim10YZArms C)
    (B : E.LeftClaim10SecondArms C) : Prop :=
  E.LeftClaim10YXObstruction F B ∨
  E.LeftClaim10YXObstruction F B.reverse ∨
  E.LeftClaim10YXObstruction F.swapYZ B.swapYZ ∨
  E.LeftClaim10YXObstruction F.swapYZ B.swapYZ.reverse ∨
  E.LeftClaim10YZObstruction A B ∨
  E.LeftClaim10YZObstruction A B.reverse

/-- Every second-fan endpoint choice is reduced, unconditionally, to a
wheel centred at `a'` or one of the explicit collision witnesses in the
two normalized cases. -/
theorem wheel_or_leftClaim10EndpointObstruction
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (A : E.LeftClaim10YZArms C)
    (B : E.LeftClaim10SecondArms C) :
    HasWheelCenteredAt E.torso a' ∨
      E.LeftClaim10EndpointObstruction F A B := by
  rcases LeftClaim10SecondArms.endpoint_cases E B with
      hxy | hyx | hxz | hzx | hyz | hzy
  · rcases E.wheel_or_leftClaim10YXObstruction F B.reverse
      (by simpa [LeftClaim10SecondArms.reverse] using hxy.2)
      (by simpa [LeftClaim10SecondArms.reverse] using hxy.1) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases E.wheel_or_leftClaim10YXObstruction F B hyx.1 hyx.2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases E.wheel_or_leftClaim10YXObstruction F.swapYZ B.swapYZ.reverse
      (by change B.t = C.z; exact hxz.2)
      (by change B.s = C.x; exact hxz.1) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases E.wheel_or_leftClaim10YXObstruction F.swapYZ B.swapYZ
      (by change B.s = C.z; exact hzx.1)
      (by change B.t = C.x; exact hzx.2) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases E.wheel_or_leftClaim10YZObstruction A B hyz.1 hyz.2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · rcases E.wheel_or_leftClaim10YZObstruction A B.reverse
      (by simpa [LeftClaim10SecondArms.reverse] using hzy.2)
      (by simpa [LeftClaim10SecondArms.reverse] using hzy.1) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-- The complete collision-obstruction elimination.  For every endpoint
pair of the second fan, the corresponding normalized wheel reduction has no
surviving obstruction at exact degree three. -/
theorem hasWheelCenteredAt_leftClaim10_of_degree_eq_three
    {a' : {v : V // v ∈ E.verts}} {C : E.LeftClaim10Initial a'}
    (F : E.LeftClaim10YZFan C) (A : E.LeftClaim10YZArms C)
    (B : E.LeftClaim10SecondArms C)
    (hA : ∀ w, w ∈ A.left.support → w ∈ F.path.support)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hab : ¬G.Adj E.a E.b)
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3)
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a')
    (hsecondTwinLeft : a' ∉ B.left.support)
    (hsecondTwinRight : a' ∉ B.right.support) :
    HasWheelCenteredAt E.torso a' := by
  rcases LeftClaim10SecondArms.endpoint_cases E B with
      hxy | hyx | hxz | hzx | hyz | hzy
  · rcases E.wheel_or_leftClaim10YXObstruction F B.reverse
      (by simpa only [LeftClaim10SecondArms.reverse] using hxy.2)
      (by simpa only [LeftClaim10SecondArms.reverse] using hxy.1) with h | h
    · exact h
    · exact False.elim <| E.not_leftClaim10YXObstruction_of_degree_eq_three
        F B.reverse
        (by simpa only [LeftClaim10SecondArms.reverse] using hxy.2)
        (by simpa only [LeftClaim10SecondArms.reverse] using hxy.1)
        hcentres hab hdeg htwin
        (by simpa only [LeftClaim10SecondArms.reverse] using hsecondTwinRight)
        (by simpa only [LeftClaim10SecondArms.reverse] using hsecondTwinLeft) h
  · rcases E.wheel_or_leftClaim10YXObstruction F B hyx.1 hyx.2 with h | h
    · exact h
    · exact False.elim <| E.not_leftClaim10YXObstruction_of_degree_eq_three
        F B hyx.1 hyx.2 hcentres hab hdeg htwin
          hsecondTwinLeft hsecondTwinRight h
  · rcases E.wheel_or_leftClaim10YXObstruction F.swapYZ B.swapYZ.reverse
      (by change B.t = C.z; exact hxz.2)
      (by change B.s = C.x; exact hxz.1) with h | h
    · exact h
    · exact False.elim <| E.not_leftClaim10YXObstruction_of_degree_eq_three
        F.swapYZ B.swapYZ.reverse
        (by change B.t = C.z; exact hxz.2)
        (by change B.s = C.x; exact hxz.1)
        hcentres hab hdeg htwin
        (by simpa only [LeftClaim10SecondArms.swapYZ,
          LeftClaim10SecondArms.reverse] using hsecondTwinRight)
        (by simpa only [LeftClaim10SecondArms.swapYZ,
          LeftClaim10SecondArms.reverse] using hsecondTwinLeft) h
  · rcases E.wheel_or_leftClaim10YXObstruction F.swapYZ B.swapYZ
      (by change B.s = C.z; exact hzx.1)
      (by change B.t = C.x; exact hzx.2) with h | h
    · exact h
    · exact False.elim <| E.not_leftClaim10YXObstruction_of_degree_eq_three
        F.swapYZ B.swapYZ
        (by change B.s = C.z; exact hzx.1)
        (by change B.t = C.x; exact hzx.2)
        hcentres hab hdeg htwin
        (by simpa only [LeftClaim10SecondArms.swapYZ] using hsecondTwinLeft)
        (by simpa only [LeftClaim10SecondArms.swapYZ] using hsecondTwinRight) h
  · rcases E.wheel_or_leftClaim10YZObstruction A B hyz.1 hyz.2 with h | h
    · exact h
    · exact False.elim <| E.not_leftClaim10YZObstruction_of_degree_eq_three
        F A B hA hyz.1 hyz.2 hcentres hab hdeg htwin
          hsecondTwinLeft hsecondTwinRight h
  · rcases E.wheel_or_leftClaim10YZObstruction A B.reverse
      (by simpa only [LeftClaim10SecondArms.reverse] using hzy.2)
      (by simpa only [LeftClaim10SecondArms.reverse] using hzy.1) with h | h
    · exact h
    · exact False.elim <| E.not_leftClaim10YZObstruction_of_degree_eq_three
        F A B.reverse hA
        (by simpa only [LeftClaim10SecondArms.reverse] using hzy.2)
        (by simpa only [LeftClaim10SecondArms.reverse] using hzy.1)
        hcentres hab hdeg htwin
        (by simpa only [LeftClaim10SecondArms.reverse] using hsecondTwinRight)
        (by simpa only [LeftClaim10SecondArms.reverse] using hsecondTwinLeft) h

/-- **AHT Claim (10), left attachment.**  In the actual end graph, a
degree-three left attachment has no false twin.  The two source fans and the
complete first-hit analysis above force a wheel centred at any putative
interior twin, contradicting the two-boundary centre confinement. -/
theorem not_falseTwins_inducedEnd_left_of_degree_eq_three
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b)
    (hdeg : E.inducedEnd.degree
      ⟨E.a, E.left_mem_verts⟩ = 3)
    {a' : {v : V // v ∈ E.verts}} :
    ¬AreFalseTwins E.inducedEnd
      ⟨E.a, E.left_mem_verts⟩ a' := by
  intro htwin
  obtain ⟨C⟩ := E.exists_leftClaim10Initial hthree hcentres hnoWheel hab
    (by omega) htwin
  obtain ⟨F₀⟩ := E.exists_leftClaim10FirstFan hthree C
  have hboundary₀ := F₀.not_boundary_of_degree_eq_three (E := E)
    hcentres hab hdeg htwin
  obtain ⟨F⟩ := F₀.toYZFan (E := E)
    (fun h ↦ hboundary₀ (Or.inl h))
    (fun h ↦ hboundary₀ (Or.inr h))
  obtain ⟨A, hA, -⟩ := F.toArms_with_subsets
  obtain ⟨S⟩ := E.exists_leftClaim10SecondFan hthree C
  have hSTwin : a' ∉ S.path.support :=
    S.twin_not_mem_of_degree_eq_three (E := E) hdeg htwin
  obtain ⟨B, hBLeft, hBRight⟩ := S.toArms_with_subsets
  have hBTwinLeft : a' ∉ B.left.support :=
    fun h ↦ hSTwin (hBLeft _ h)
  have hBTwinRight : a' ∉ B.right.support :=
    fun h ↦ hSTwin (hBRight _ h)
  have hwheel : HasWheelCenteredAt E.torso a' :=
    E.hasWheelCenteredAt_leftClaim10_of_degree_eq_three
      F A B hA hcentres hab hdeg htwin hBTwinLeft hBTwinRight
  have ha'Left : a' ≠
      (⟨E.a, E.left_mem_verts⟩ : {v : V // v ∈ E.verts}) := by
    intro h
    apply E.left_not_mem_side
    have hv : a'.1 = E.a := congrArg Subtype.val h
    rw [← hv]
    exact C.twin_mem_side
  exact hcentres a' ha'Left C.twin_ne_right hwheel

/-- The high-left branch of the pointed two-separator induction.  Recursing
on the actual induced end with the right attachment as exceptional produces
a degree-three pair avoiding the right attachment; Claim (10) excludes the
left attachment from both members, so the pair lifts to the ambient graph
and still avoids the distinguished vertex. -/
theorem hasFalseTwinsAway_of_inducedEnd_left_degree
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b)
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hleft : 3 ≤ E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩)
    (ih : AHTSection7.SmallerPointedInstancesHaveFalseTwins G) :
    AHTSection7.HasFalseTwinsAway G x₀ := by
  have hdata := E.inducedEnd_pointedData_right
    hdelete hminSide hnoWheel hleft
  obtain ⟨u, v, htwin, hdeg, huRight, hvRight⟩ :=
    ih _ E.inducedEnd ⟨E.b, E.right_mem_verts⟩ E.card_verts_lt
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2
  have huLeft : u ≠
      (⟨E.a, E.left_mem_verts⟩ : {w : V // w ∈ E.verts}) := by
    intro hu
    subst u
    exact E.not_falseTwins_inducedEnd_left_of_degree_eq_three
      hthree hcentres hnoWheel hab hdeg htwin
  have hvLeft : v ≠
      (⟨E.a, E.left_mem_verts⟩ : {w : V // w ∈ E.verts}) := by
    intro hv
    subst v
    have hdegLeft : E.inducedEnd.degree
        ⟨E.a, E.left_mem_verts⟩ = 3 := by
      calc
        E.inducedEnd.degree ⟨E.a, E.left_mem_verts⟩ =
            E.inducedEnd.degree u := htwin.degree_eq.symm
        _ = 3 := hdeg
    exact E.not_falseTwins_inducedEnd_left_of_degree_eq_three
      hthree hcentres hnoWheel hab hdegLeft htwin.symm
  have hua : u.1 ≠ E.a := fun h ↦ huLeft (Subtype.ext h)
  have hub : u.1 ≠ E.b := fun h ↦ huRight (Subtype.ext h)
  have hva : v.1 ≠ E.a := fun h ↦ hvLeft (Subtype.ext h)
  have hvb : v.1 ≠ E.b := fun h ↦ hvRight (Subtype.ext h)
  have huside : u.1 ∈ E.side := E.mem_side_of_mem_verts u.2 hua hub
  have hvside : v.1 ∈ E.side := E.mem_side_of_mem_verts v.2 hva hvb
  have hNu : G.neighborSet u.1 ⊆ E.verts :=
    E.neighborSet_subset_verts huside
  have hdegG : G.degree u.1 = 3 := by
    rw [← G.degree_induce_of_neighborSet_subset hNu]
    exact hdeg
  exact ⟨u.1, v.1, E.falseTwins_inducedEnd_lift hua hub hva hvb htwin,
    hdegG, hminimal.ne_exception_of_mem_side huside,
    hminimal.ne_exception_of_mem_side hvside⟩

/-- **AHT Claim (10), right attachment.**  This is the exact symmetric
statement, obtained by exchanging the two boundary labels of the same
minimal end and transporting the induced graph along the proof-only vertex
equivalence. -/
theorem not_falseTwins_inducedEnd_right_of_degree_eq_three
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b)
    (hdeg : E.inducedEnd.degree
      ⟨E.b, E.right_mem_verts⟩ = 3)
    {b' : {v : V // v ∈ E.verts}} :
    ¬AreFalseTwins E.inducedEnd
      ⟨E.b, E.right_mem_verts⟩ b' := by
  intro htwin
  let e := E.swapInducedEndIso
  let bS : {v : V // v ∈ E.swap.verts} :=
    ⟨E.b, E.swap.left_mem_verts⟩
  let bE : {v : V // v ∈ E.verts} :=
    ⟨E.b, E.right_mem_verts⟩
  have heb : e bS = bE := Subtype.ext rfl
  have hpre : e.symm bE = bS := by
    apply e.injective
    simpa only [e.apply_symm_apply] using heb.symm
  have htwinS : AreFalseTwins E.swap.inducedEnd bS (e.symm b') := by
    have hmap := areFalseTwins_mapIso e.symm htwin
    simpa only [hpre, bE] using hmap
  have hdegS : E.swap.inducedEnd.degree bS = 3 := by
    calc
      E.swap.inducedEnd.degree bS = E.inducedEnd.degree (e bS) :=
        (e.degree_eq bS).symm
      _ = E.inducedEnd.degree bE :=
        congrArg (fun w ↦ E.inducedEnd.degree w) heb
      _ = 3 := hdeg
  have hminSwap : ∀ v : V, v ∈ E.swap.side → 3 ≤ G.degree v := by
    intro v hv
    exact hminSide v (by simpa only [E.swap_side] using hv)
  have hstruct := E.swap.minimalEnd_torso_structure hminimal.swap
    hdelete hminSwap hnoWheel
  have habSwap : ¬G.Adj E.swap.a E.swap.b := by
    intro h
    exact hab h.symm
  exact E.swap.not_falseTwins_inducedEnd_left_of_degree_eq_three
    hstruct.1 hstruct.2 hnoWheel habSwap hdegS htwinS

/-- The symmetric high-right branch of the pointed two-separator induction.
The recursive pair avoids the left attachment, and the swapped form of Claim
(10) excludes the right attachment before lifting. -/
theorem hasFalseTwinsAway_of_inducedEnd_right_degree
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b)
    (hright : 3 ≤ E.inducedEnd.degree ⟨E.b, E.right_mem_verts⟩)
    (ih : AHTSection7.SmallerPointedInstancesHaveFalseTwins G) :
    AHTSection7.HasFalseTwinsAway G x₀ := by
  have hdata := E.inducedEnd_pointedData_left
    hdelete hminSide hnoWheel hright
  obtain ⟨u, v, htwin, hdeg, huLeft, hvLeft⟩ :=
    ih _ E.inducedEnd ⟨E.a, E.left_mem_verts⟩ E.card_verts_lt
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2
  have huRight : u ≠
      (⟨E.b, E.right_mem_verts⟩ : {w : V // w ∈ E.verts}) := by
    intro hu
    subst u
    exact E.not_falseTwins_inducedEnd_right_of_degree_eq_three
      hminimal hdelete hminSide hnoWheel hab hdeg htwin
  have hvRight : v ≠
      (⟨E.b, E.right_mem_verts⟩ : {w : V // w ∈ E.verts}) := by
    intro hv
    subst v
    have hdegRight : E.inducedEnd.degree
        ⟨E.b, E.right_mem_verts⟩ = 3 := by
      calc
        E.inducedEnd.degree ⟨E.b, E.right_mem_verts⟩ =
            E.inducedEnd.degree u := htwin.degree_eq.symm
        _ = 3 := hdeg
    exact E.not_falseTwins_inducedEnd_right_of_degree_eq_three
      hminimal hdelete hminSide hnoWheel hab hdegRight htwin.symm
  have hua : u.1 ≠ E.a := fun h ↦ huLeft (Subtype.ext h)
  have hub : u.1 ≠ E.b := fun h ↦ huRight (Subtype.ext h)
  have hva : v.1 ≠ E.a := fun h ↦ hvLeft (Subtype.ext h)
  have hvb : v.1 ≠ E.b := fun h ↦ hvRight (Subtype.ext h)
  have huside : u.1 ∈ E.side := E.mem_side_of_mem_verts u.2 hua hub
  have hvside : v.1 ∈ E.side := E.mem_side_of_mem_verts v.2 hva hvb
  have hNu : G.neighborSet u.1 ⊆ E.verts :=
    E.neighborSet_subset_verts huside
  have hdegG : G.degree u.1 = 3 := by
    rw [← G.degree_induce_of_neighborSet_subset hNu]
    exact hdeg
  exact ⟨u.1, v.1, E.falseTwins_inducedEnd_lift hua hub hva hvb htwin,
    hdegG, hminimal.ne_exception_of_mem_side huside,
    hminimal.ne_exception_of_mem_side hvside⟩

/-- The symmetric boundary-coincidence conclusion for the right
attachment. -/
theorem not_falseTwins_inducedEnd_boundaries_of_right_degree_three
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (_hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b)
    (hdeg : 3 ≤ E.inducedEnd.degree ⟨E.b, E.right_mem_verts⟩) :
    ¬AreFalseTwins E.inducedEnd
      ⟨E.b, E.right_mem_verts⟩ ⟨E.a, E.left_mem_verts⟩ := by
  intro htwin
  let a : {v : V // v ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  let b : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  obtain ⟨x, _y, _z, _hxy, _hxz, _hyz, hbx, _hby, _hbz, hax, _hay, _haz,
      hxa, hxb, _hya, _hyb, _hza, _hzb⟩ :=
    E.exists_three_interior_commonNeighbors_right hab hdeg htwin
  have habT : E.torso.Adj a b := E.torso_boundary_adj
  have haxT : E.torso.Adj a x := Or.inl hax
  have hbxT : E.torso.Adj b x := Or.inl hbx
  have hxC : HasWheelCenteredAt E.torso x :=
    hasWheelCenteredAt_of_triangle_of_isThreeConnected
      (isThreeConnected_of_vertexThreeConnected_local hthree)
      hbxT.symm habT.symm haxT
  exact hcentres x
    (fun h ↦ hxa (congrArg Subtype.val h))
    (fun h ↦ hxb (congrArg Subtype.val h)) hxC

/-- A high-degree false twin of the right attachment cannot be the left
attachment. -/
theorem right_falseTwin_ne_left_of_degree_three
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b)
    (hdeg : 3 ≤ E.inducedEnd.degree ⟨E.b, E.right_mem_verts⟩)
    {b' : {v : V // v ∈ E.verts}}
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.b, E.right_mem_verts⟩ b') :
    b' ≠ ⟨E.a, E.left_mem_verts⟩ := by
  intro h
  apply E.not_falseTwins_inducedEnd_boundaries_of_right_degree_three
    hthree hcentres hnoWheel hab hdeg
  simpa [h] using htwin

/-- In the symmetric surviving branch, the false twin of the right
attachment lies in the component side. -/
theorem right_falseTwin_mem_side_of_degree_three
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    (hnoWheel : ¬HasWheelWitness G) (hab : ¬G.Adj E.a E.b)
    (hdeg : 3 ≤ E.inducedEnd.degree ⟨E.b, E.right_mem_verts⟩)
    {b' : {v : V // v ∈ E.verts}}
    (htwin : AreFalseTwins E.inducedEnd
      ⟨E.b, E.right_mem_verts⟩ b') :
    b'.1 ∈ E.side := by
  apply E.mem_side_of_mem_verts b'.2
  · intro h
    apply E.right_falseTwin_ne_left_of_degree_three
      hthree hcentres hnoWheel hab hdeg htwin
    exact Subtype.ext h
  · intro h
    apply htwin.1
    exact (Subtype.ext h).symm

/-- Symmetric interior-third-neighbour extraction at the right
attachment. -/
theorem exists_side_thirdNeighbor_of_right_commonNeighbor
    (hthree : VertexThreeConnected E.torso)
    (hcentres : AlmostWheelFreeAt E.torso
      ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩)
    {x b' : {v : V // v ∈ E.verts}}
    (hbx : E.torso.Adj ⟨E.b, E.right_mem_verts⟩ x)
    (hb'x : E.torso.Adj b' x)
    (hbb' : (⟨E.b, E.right_mem_verts⟩ :
      {v : V // v ∈ E.verts}) ≠ b') :
    ∃ x' : {v : V // v ∈ E.verts},
      E.torso.Adj x x' ∧
        x' ≠ ⟨E.b, E.right_mem_verts⟩ ∧ x' ≠ b' ∧
        x'.1 ∈ E.side := by
  let a : {v : V // v ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  have hthree' := isThreeConnected_of_vertexThreeConnected_local hthree
  obtain ⟨x', hxx', hxb', hxother⟩ :=
    exists_third_neighbor_of_degree_ge_three
      (G := E.torso) (hthree'.degree_ge x) hbx.symm hb'x.symm hbb'
  have htri := E.torso_triangleFree_of_vertexThreeConnected_of_centres
    hthree hcentres
  have hxa' : x'.1 ≠ E.a := by
    intro h
    have hx'a : x' = a := Subtype.ext h
    subst x'
    exact htri E.torso_boundary_adj.symm hxx'.symm hbx.symm
  have hxbVal : x'.1 ≠ E.b := by
    intro h
    apply hxb'
    exact Subtype.ext h
  exact ⟨x', hxx', hxb', hxother,
    E.mem_side_of_mem_verts x'.2 hxa' hxbVal⟩

/-- The exact `K₃,₃-e` terminal from Section 7, discharged by AHT Lemma
6.2.  Its conclusion is already lifted from the end torso to the ambient
graph. -/
theorem falseTwins_lift_of_k33MinusEdge
    (hthree : VertexThreeConnected E.torso)
    (halmost : AlmostWheelFree E.torso)
    (hK : ContainsK33MinusEdge E.torso) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  obtain ⟨e⟩ := aht_isomorphic_k33_of_k33MinusEdge
    (isThreeConnected_of_vertexThreeConnected_local hthree) halmost hK
  exact E.falseTwins_lift_of_k33_torso e

/-- The explicit crossing-pairs calculation from AHT Section 7.  If the two
degree-three false-twin pairs are `{a,a'}` and `{b,b'}`, the virtual edge and
one third common neighbour for each pair give `K₃,₃-e`. -/
theorem containsK33MinusEdge_of_explicit_boundaryCrossing
    (hthree : VertexThreeConnected E.torso)
    (halmost : AlmostWheelFree E.torso)
    {a' b' : {v : V // v ∈ E.verts}}
    (hA : AreFalseTwins E.torso
      ⟨E.a, E.left_mem_verts⟩ a')
    (hB : AreFalseTwins E.torso
      ⟨E.b, E.right_mem_verts⟩ b')
    (hdegA : E.torso.degree ⟨E.a, E.left_mem_verts⟩ = 3)
    (hdegB : E.torso.degree ⟨E.b, E.right_mem_verts⟩ = 3) :
    ContainsK33MinusEdge E.torso := by
  classical
  let a : {v : V // v ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  let b : {v : V // v ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  have hdegA' : E.torso.degree a = 3 := by simpa [a] using hdegA
  have hdegB' : E.torso.degree b = 3 := by simpa [b] using hdegB
  have hab : E.torso.Adj a b := E.torso_boundary_adj
  have hab' : E.torso.Adj a' b := (hA.adj_iff b).mp hab
  have hab'' : E.torso.Adj a b' :=
    ((hB.adj_iff a).mp hab.symm).symm
  have ha'b' : E.torso.Adj a' b' := (hA.adj_iff b').mp hab''
  obtain ⟨c, hbc, hca, hca'⟩ :=
    exists_third_neighbor_of_degree_ge_three
      (G := E.torso) (by omega : 3 ≤ E.torso.degree b)
      hab.symm hab'.symm hA.1
  obtain ⟨d, had, hdb, hdb'⟩ :=
    exists_third_neighbor_of_degree_ge_three
      (G := E.torso) (by omega : 3 ≤ E.torso.degree a)
      hab hab'' hB.1
  have hcb' : E.torso.Adj c b' :=
    ((hB.adj_iff c).mp hbc).symm
  have ha'd : E.torso.Adj a' d := (hA.adj_iff d).mp had
  have hcd : c ≠ d := by
    intro h
    subst d
    have htri := aht_triangleFree_of_threeConnected_almostWheelFree
      (isThreeConnected_of_vertexThreeConnected_local hthree) halmost
    exact htri hab hbc had.symm
  have haa' : a ≠ a' := by simpa [a] using hA.1
  have hbb' : b ≠ b' := by simpa [b] using hB.1
  have hdistinct : [c, a, a', d, b, b'].Nodup := by
    simp [hca, hca', hcd, hbc.ne.symm, hcb'.ne,
      haa', had.ne, hab.ne, hab''.ne, ha'd.ne, hab'.ne,
      ha'b'.ne, hdb, hdb', hbb']
  have hK : ContainsK33MinusEdge E.torso := by
    refine ⟨c, a, a', d, b, b', hdistinct, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hbc.symm
    · exact hcb'
    · exact had
    · exact hab
    · exact hab''
    · exact ha'd
    · exact hab'
    · exact ha'b'
  exact hK

/-- The unpointed crossing terminal follows from the concrete
`K₃,₃-e` certificate. -/
theorem falseTwins_lift_of_explicit_boundaryCrossing
    (hthree : VertexThreeConnected E.torso)
    (halmost : AlmostWheelFree E.torso)
    {a' b' : {v : V // v ∈ E.verts}}
    (hA : AreFalseTwins E.torso
      ⟨E.a, E.left_mem_verts⟩ a')
    (hB : AreFalseTwins E.torso
      ⟨E.b, E.right_mem_verts⟩ b')
    (hdegA : E.torso.degree ⟨E.a, E.left_mem_verts⟩ = 3)
    (hdegB : E.torso.degree ⟨E.b, E.right_mem_verts⟩ = 3) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  exact E.falseTwins_lift_of_k33MinusEdge hthree halmost
    (E.containsK33MinusEdge_of_explicit_boundaryCrossing
      hthree halmost hA hB hdegA hdegB)

/-- Pointed crossing terminal.  Lemma 6.2 identifies the torso with
`K₃,₃`, after which the selected interior pair avoids `x₀`. -/
theorem falseTwinsAway_of_explicit_boundaryCrossing
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hthree : VertexThreeConnected E.torso)
    (halmost : AlmostWheelFree E.torso)
    {a' b' : {v : V // v ∈ E.verts}}
    (hA : AreFalseTwins E.torso
      ⟨E.a, E.left_mem_verts⟩ a')
    (hB : AreFalseTwins E.torso
      ⟨E.b, E.right_mem_verts⟩ b')
    (hdegA : E.torso.degree ⟨E.a, E.left_mem_verts⟩ = 3)
    (hdegB : E.torso.degree ⟨E.b, E.right_mem_verts⟩ = 3) :
    AHTSection7.HasFalseTwinsAway G x₀ := by
  have hK := E.containsK33MinusEdge_of_explicit_boundaryCrossing
    hthree halmost hA hB hdegA hdegB
  obtain ⟨e⟩ := aht_isomorphic_k33_of_k33MinusEdge
    (isThreeConnected_of_vertexThreeConnected_local hthree) halmost hK
  exact E.falseTwinsAway_of_k33_torso hminimal e

/-- The exact crossing-boundary configuration left when neither of the two
disjoint pairs lies wholly in the interior. -/
def BoundaryCrossing (T : TwoDisjointFalseTwinPairs E.torso) : Prop :=
  let a : {w : V // w ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  let b : {w : V // w ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  (a ∈ ({T.u, T.v} : Finset _) ∧ b ∈ ({T.x, T.y} : Finset _)) ∨
    (b ∈ ({T.u, T.v} : Finset _) ∧ a ∈ ({T.x, T.y} : Finset _))

/-- Every crossing two-pair output is the explicit `K₃,₃-e` configuration,
up to swapping the members and the two pairs. -/
theorem falseTwins_lift_of_boundaryCrossing
    (hthree : VertexThreeConnected E.torso)
    (halmost : AlmostWheelFree E.torso)
    (T : TwoDisjointFalseTwinPairs E.torso) (hcross : E.BoundaryCrossing T) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  classical
  rcases T with ⟨u, v, x, y, huv, hxy, hdu, hdx, hdisj⟩
  have hdv : E.torso.degree v = 3 := by
    rw [← huv.degree_eq]
    exact hdu
  have hdy : E.torso.degree y = 3 := by
    rw [← hxy.degree_eq]
    exact hdx
  simp only [BoundaryCrossing, Finset.mem_insert, Finset.mem_singleton] at hcross
  rcases hcross with ⟨hau | hav, hbx | hby⟩ |
      ⟨hbu | hbv, hax | hay⟩
  · subst u
    subst x
    exact E.falseTwins_lift_of_explicit_boundaryCrossing
      hthree halmost huv hxy hdu hdx
  · subst u
    subst y
    exact E.falseTwins_lift_of_explicit_boundaryCrossing
      hthree halmost huv hxy.symm hdu hdy
  · subst v
    subst x
    exact E.falseTwins_lift_of_explicit_boundaryCrossing
      hthree halmost huv.symm hxy hdv hdx
  · subst v
    subst y
    exact E.falseTwins_lift_of_explicit_boundaryCrossing
      hthree halmost huv.symm hxy.symm hdv hdy
  · subst u
    subst x
    exact E.falseTwins_lift_of_explicit_boundaryCrossing
      hthree halmost hxy huv hdx hdu
  · subst u
    subst y
    exact E.falseTwins_lift_of_explicit_boundaryCrossing
      hthree halmost hxy.symm huv hdy hdu
  · subst v
    subst x
    exact E.falseTwins_lift_of_explicit_boundaryCrossing
      hthree halmost hxy huv.symm hdx hdv
  · subst v
    subst y
    exact E.falseTwins_lift_of_explicit_boundaryCrossing
      hthree halmost hxy.symm huv.symm hdy hdv

/-- Pointed form of the crossing-pair terminal.  Every orientation produces
the same `K₃,₃-e` certificate, whose interior `K₃,₃` pair avoids `x₀`. -/
theorem falseTwinsAway_of_boundaryCrossing
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hthree : VertexThreeConnected E.torso)
    (halmost : AlmostWheelFree E.torso)
    (T : TwoDisjointFalseTwinPairs E.torso) (hcross : E.BoundaryCrossing T) :
    AHTSection7.HasFalseTwinsAway G x₀ := by
  classical
  rcases T with ⟨u, v, x, y, huv, hxy, hdu, hdx, hdisj⟩
  have hdv : E.torso.degree v = 3 := by
    rw [← huv.degree_eq]
    exact hdu
  have hdy : E.torso.degree y = 3 := by
    rw [← hxy.degree_eq]
    exact hdx
  simp only [BoundaryCrossing, Finset.mem_insert, Finset.mem_singleton] at hcross
  rcases hcross with ⟨hau | hav, hbx | hby⟩ |
      ⟨hbu | hbv, hax | hay⟩
  · subst u
    subst x
    exact E.falseTwinsAway_of_explicit_boundaryCrossing
      hminimal hthree halmost huv hxy hdu hdx
  · subst u
    subst y
    exact E.falseTwinsAway_of_explicit_boundaryCrossing
      hminimal hthree halmost huv hxy.symm hdu hdy
  · subst v
    subst x
    exact E.falseTwinsAway_of_explicit_boundaryCrossing
      hminimal hthree halmost huv.symm hxy hdv hdx
  · subst v
    subst y
    exact E.falseTwinsAway_of_explicit_boundaryCrossing
      hminimal hthree halmost huv.symm hxy.symm hdv hdy
  · subst u
    subst x
    exact E.falseTwinsAway_of_explicit_boundaryCrossing
      hminimal hthree halmost hxy huv hdx hdu
  · subst u
    subst y
    exact E.falseTwinsAway_of_explicit_boundaryCrossing
      hminimal hthree halmost hxy.symm huv hdy hdu
  · subst v
    subst x
    exact E.falseTwinsAway_of_explicit_boundaryCrossing
      hminimal hthree halmost hxy huv.symm hdx hdv
  · subst v
    subst y
    exact E.falseTwinsAway_of_explicit_boundaryCrossing
      hminimal hthree halmost hxy.symm huv.symm hdy hdv

/-- Two disjoint Section 6 pairs either lift immediately or cross the two
boundary vertices in opposite pairs.  This is the finite combinatorial split
used in both virtual-edge cases of AHT Section 7. -/
theorem interiorFalseTwins_or_boundaryCrossing
    (T : TwoDisjointFalseTwinPairs E.torso) :
    E.HasInteriorFalseTwins ∨ E.BoundaryCrossing T := by
  classical
  let a : {w : V // w ∈ E.verts} := ⟨E.a, E.left_mem_verts⟩
  let b : {w : V // w ∈ E.verts} := ⟨E.b, E.right_mem_verts⟩
  by_cases hfirst :
      T.u.1 ≠ E.a ∧ T.u.1 ≠ E.b ∧ T.v.1 ≠ E.a ∧ T.v.1 ≠ E.b
  · left
    exact E.interiorFalseTwins_of_firstPair T
      ⟨hfirst.1, hfirst.2.1⟩ ⟨hfirst.2.2.1, hfirst.2.2.2⟩
  by_cases hsecond :
      T.x.1 ≠ E.a ∧ T.x.1 ≠ E.b ∧ T.y.1 ≠ E.a ∧ T.y.1 ≠ E.b
  · left
    exact E.interiorFalseTwins_of_secondPair T
      ⟨hsecond.1, hsecond.2.1⟩ ⟨hsecond.2.2.1, hsecond.2.2.2⟩
  have hmeetFirst :
      a ∈ ({T.u, T.v} : Finset _) ∨ b ∈ ({T.u, T.v} : Finset _) := by
    by_contra hmeet
    simp only [not_or] at hmeet
    have ha := hmeet.1
    have hb := hmeet.2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
    apply hfirst
    exact ⟨
      (fun h ↦ ha.1 (Subtype.ext h.symm)),
      (fun h ↦ hb.1 (Subtype.ext h.symm)),
      (fun h ↦ ha.2 (Subtype.ext h.symm)),
      (fun h ↦ hb.2 (Subtype.ext h.symm))⟩
  have hmeetSecond :
      a ∈ ({T.x, T.y} : Finset _) ∨ b ∈ ({T.x, T.y} : Finset _) := by
    by_contra hmeet
    simp only [not_or] at hmeet
    have ha := hmeet.1
    have hb := hmeet.2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
    apply hsecond
    exact ⟨
      (fun h ↦ ha.1 (Subtype.ext h.symm)),
      (fun h ↦ hb.1 (Subtype.ext h.symm)),
      (fun h ↦ ha.2 (Subtype.ext h.symm)),
      (fun h ↦ hb.2 (Subtype.ext h.symm))⟩
  have hdisj := Finset.disjoint_left.mp T.disjoint
  right
  change
    (a ∈ ({T.u, T.v} : Finset _) ∧ b ∈ ({T.x, T.y} : Finset _)) ∨
      (b ∈ ({T.u, T.v} : Finset _) ∧ a ∈ ({T.x, T.y} : Finset _))
  rcases hmeetFirst with hFa | hFb <;>
    rcases hmeetSecond with hSa | hSb
  · exact False.elim (hdisj hFa hSa)
  · exact Or.inl ⟨hFa, hSb⟩
  · exact Or.inr ⟨hFb, hSa⟩
  · exact False.elim (hdisj hFb hSb)

/-- Unpointed wrapper for the interior-or-crossing classification. -/
theorem twoPairs_lift_or_boundaryCrossing
    (T : TwoDisjointFalseTwinPairs E.torso) :
    (∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3) ∨
      E.BoundaryCrossing T := by
  rcases E.interiorFalseTwins_or_boundaryCrossing T with hpair | hcross
  · exact Or.inl (E.interiorFalseTwins_lift hpair)
  · exact Or.inr hcross

/-- Complete Section 7 terminal for a two-pair output: an interior pair
lifts directly, while crossing pairs are resolved by `K₃,₃-e` rigidity. -/
theorem twoPairs_lift
    (hthree : VertexThreeConnected E.torso)
    (halmost : AlmostWheelFree E.torso)
    (T : TwoDisjointFalseTwinPairs E.torso) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  rcases E.twoPairs_lift_or_boundaryCrossing T with hpair | hcross
  · exact hpair
  · exact E.falseTwins_lift_of_boundaryCrossing hthree halmost T hcross

/-- Pointed Section 7 terminal for a concrete two-pair output.  Interior
pairs lift directly with side avoidance; crossing pairs pass through the
`K₃,₃-e` rigidity argument and select an interior `K₃,₃` pair. -/
theorem twoPairs_lift_away
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hthree : VertexThreeConnected E.torso)
    (halmost : AlmostWheelFree E.torso)
    (T : TwoDisjointFalseTwinPairs E.torso) :
    AHTSection7.HasFalseTwinsAway G x₀ := by
  rcases E.interiorFalseTwins_or_boundaryCrossing T with hpair | hcross
  · exact E.interiorFalseTwins_lift_away hminimal hpair
  · exact E.falseTwinsAway_of_boundaryCrossing
      hminimal hthree halmost T hcross

/-- Complete lifting conclusion for a minimal end once the source Theorem
6.6 two-pair output is supplied as concrete data.  No theorem principle is
assumed: all connectivity, centre confinement, and the exceptional crossing
case are discharged in this file. -/
theorem minimalEnd_twoPairs_lift
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G)
    (hdega : E.torso.degree ⟨E.a, E.left_mem_verts⟩ = 3)
    (hdegb : E.torso.degree ⟨E.b, E.right_mem_verts⟩ = 3)
    (T : TwoDisjointFalseTwinPairs E.torso) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  have hstruct := E.minimalEnd_torso_structure
    hminimal hdelete hminSide hnoWheel
  have halmost : AlmostWheelFree E.torso :=
    E.almostWheelFree_torso_of_centres_of_boundary_degrees
      hstruct.2 hdega hdegb
  exact E.twoPairs_lift hstruct.1 halmost T

/-- Pointed strengthening of the low-boundary nonedge terminal. -/
theorem minimalEnd_twoPairs_lift_away
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G)
    (hdega : E.torso.degree ⟨E.a, E.left_mem_verts⟩ = 3)
    (hdegb : E.torso.degree ⟨E.b, E.right_mem_verts⟩ = 3)
    (T : TwoDisjointFalseTwinPairs E.torso) :
    AHTSection7.HasFalseTwinsAway G x₀ := by
  have hstruct := E.minimalEnd_torso_structure
    hminimal hdelete hminSide hnoWheel
  have halmost : AlmostWheelFree E.torso :=
    E.almostWheelFree_torso_of_centres_of_boundary_degrees
      hstruct.2 hdega hdegb
  exact E.twoPairs_lift_away hminimal hstruct.1 halmost T

/-- The actual-attachment-edge branch of Section 7 needs no boundary-degree
calculation: the torso is an induced wheel-free subgraph. -/
theorem minimalEnd_actualEdge_twoPairs_lift
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G) (hab : G.Adj E.a E.b)
    (T : TwoDisjointFalseTwinPairs E.torso) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  have hthree := E.torso_vertexThreeConnected_of_minimalAvoiding
    hminimal hdelete hminSide
  exact E.twoPairs_lift hthree
    (E.almostWheelFree_torso_of_boundary_adj hnoWheel hab) T

/-- Pointed strengthening of the actual-attachment-edge terminal. -/
theorem minimalEnd_actualEdge_twoPairs_lift_away
    {x₀ : V} (hminimal : E.IsMinimalAvoiding x₀)
    (hdelete : ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G) (hab : G.Adj E.a E.b)
    (T : TwoDisjointFalseTwinPairs E.torso) :
    AHTSection7.HasFalseTwinsAway G x₀ := by
  have hthree := E.torso_vertexThreeConnected_of_minimalAvoiding
    hminimal hdelete hminSide
  exact E.twoPairs_lift_away hminimal hthree
    (E.almostWheelFree_torso_of_boundary_adj hnoWheel hab) T

/-- After completely resolving the `K₃,₃` terminal, the only possible
failure of lifting a two-pair output is an explicit crossing configuration in
a torso which is not isomorphic to `K₃,₃`.  Thus AHT Lemma 6.2 is exactly
the missing implication in this branch. -/
theorem twoPairs_lift_or_crossing_nonK33
    (T : TwoDisjointFalseTwinPairs E.torso) :
    (∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3) ∨
      (E.BoundaryCrossing T ∧
        ¬Nonempty (completeBipartiteGraph (Fin 3) (Fin 3) ≃g E.torso)) := by
  classical
  by_cases hk : Nonempty
      (completeBipartiteGraph (Fin 3) (Fin 3) ≃g E.torso)
  · obtain ⟨e⟩ := hk
    exact Or.inl (E.falseTwins_lift_of_k33_torso e)
  · rcases E.twoPairs_lift_or_boundaryCrossing T with hpair | hcross
    · exact Or.inl hpair
    · exact Or.inr ⟨hcross, hk⟩

end TwoCutEnd

/-! ## Connecting the cut reduction to the two-separation branch -/

/-- Every pointed counterexample produced by `AHTSection7` has at least four
vertices.  Hence, after the proved cut-vertex reduction, it is either already
vertex-three-connected or supplies a genuine two-cut component end. -/
theorem pointedCounterexample_threeConnected_or_twoCutEnd
    (x₀ : V) (hbad : AHTSection7.IsPointedFalseTwinCounterexample G x₀)
    (htwo : G.Connected ∧
      ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected) :
    VertexThreeConnected G ∨ Nonempty (TwoCutEnd G) := by
  have hone : 1 < Fintype.card V := by
    have htwoCard := hbad.1
    omega
  obtain ⟨z, hzx₀⟩ := Fintype.exists_ne_of_one_lt_card hone x₀
  have hdegz : 3 ≤ G.degree z := hbad.2.2.1 z hzx₀
  have hcard : 4 ≤ Fintype.card V := by
    have hlt := G.degree_lt_card_verts z
    omega
  by_cases hthree : VertexThreeConnected G
  · exact Or.inl hthree
  · exact Or.inr <|
      exists_twoCutEnd_of_not_vertexThreeConnected hcard htwo.1 hthree

/-- The source-exact minimal end selected in the two-separation branch of
AHT Section 7.  Besides minimality, this packages precisely the two facts
used downstream: all interior vertices retain ambient degree at least three,
and Lemma 4.4 makes the virtual-edge torso three-connected with every wheel
centre confined to its two attachments. -/
theorem exists_minimalEnd_structure_of_pointedCounterexample
    (x₀ : V) (hbad : AHTSection7.IsPointedFalseTwinCounterexample G x₀)
    (htwo : G.Connected ∧
      ∀ c : V, (G.induce (fun w : V ↦ w ≠ c)).Connected)
    (hnot : ¬VertexThreeConnected G) :
    ∃ E : TwoCutEnd G,
      E.IsMinimalAvoiding x₀ ∧
      (∀ v : V, v ∈ E.side → 3 ≤ G.degree v) ∧
      VertexThreeConnected E.torso ∧
      AlmostWheelFreeAt E.torso
        ⟨E.a, E.left_mem_verts⟩ ⟨E.b, E.right_mem_verts⟩ := by
  classical
  have hcard2 := hbad.1
  have hone : 1 < Fintype.card V := by omega
  obtain ⟨z, hzx₀⟩ := Fintype.exists_ne_of_one_lt_card hone x₀
  have hdegz : 3 ≤ G.degree z := hbad.2.2.1 z hzx₀
  have hcard : 4 ≤ Fintype.card V := by
    have hlt := G.degree_lt_card_verts z
    omega
  obtain ⟨E, hminimal⟩ :=
    exists_minimal_twoCutEnd_avoiding_of_not_vertexThreeConnected
      x₀ hcard htwo.1 hnot
  have hminSide : ∀ v : V, v ∈ E.side → 3 ≤ G.degree v := by
    intro v hv
    apply hbad.2.2.1 v
    intro hvx
    subst v
    rcases hminimal.1 with hxa | hxb | hxout
    · exact E.left_not_mem_side (hxa ▸ hv)
    · exact E.right_not_mem_side (hxb ▸ hv)
    · exact hxout hv
  have hstruct := E.minimalEnd_torso_structure hminimal htwo.2 hminSide
    hbad.2.2.2.1
  exact ⟨E, hminimal, hminSide, hstruct⟩

/-- The complete Section 7 reduction: the published three-connected
two-pair theorem implies the pointed vertex-two-connected principle.  The
proof performs strong induction directly over all smaller pointed graphs,
so the high-boundary induced-end calls receive the genuine induction
hypothesis rather than an obstruction surrogate. -/
theorem vertexTwoConnectedFalseTwinPrinciple_of_threeConnected
    (hcore : ThreeConnectedAlmostWheelFreeFalseTwinPrinciple.{u}) :
    VertexTwoConnectedFalseTwinPrinciple.{u} := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (x₀ : W),
      Fintype.card W = n →
      2 ≤ Fintype.card W →
      H.Connected →
      MinDegreeThreeExcept H x₀ →
      ¬HasWheelWitness H →
      AHTSection7.HasFalseTwinsAway H x₀
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp [P]
      intro W _ _ H _ x₀ hcardEq hcard hconn hdeg hnoWheel
      have hsmall : AHTSection7.SmallerPointedInstancesHaveFalseTwins H := by
        intro Z _ _ K _ z₀ hlt hcardZ hconnZ hdegZ hnoWheelZ
        exact (ih (Fintype.card Z) (by omega)) Z K z₀ rfl
          hcardZ hconnZ hdegZ hnoWheelZ
      by_cases htwins : AHTSection7.HasFalseTwinsAway H x₀
      · exact htwins
      have htwo := AHTSection7.vertexTwoConnected_of_minimal_pointed_counterexample
        x₀ hcard hconn hdeg hnoWheel htwins hsmall
      by_cases hthree : VertexThreeConnected H
      · obtain ⟨T⟩ := hcore W H hthree
          (almostWheelFree_of_noWheel hnoWheel)
        exact AHTSection7.hasFalseTwinsAway_of_twoDisjointPairs T x₀
      have hone : 1 < Fintype.card W := by omega
      obtain ⟨z, hzx₀⟩ := Fintype.exists_ne_of_one_lt_card hone x₀
      have hdegz : 3 ≤ H.degree z := hdeg z hzx₀
      have hcard4 : 4 ≤ Fintype.card W := by
        have hlt := H.degree_lt_card_verts z
        omega
      obtain ⟨E, hminimal⟩ :=
        exists_minimal_twoCutEnd_avoiding_of_not_vertexThreeConnected
          x₀ hcard4 htwo.1 hthree
      have hminSide : ∀ v : W, v ∈ E.side → 3 ≤ H.degree v := by
        intro v hv
        exact hdeg v (hminimal.ne_exception_of_mem_side hv)
      by_cases hab : H.Adj E.a E.b
      · have hthreeE := E.torso_vertexThreeConnected_of_minimalAvoiding
          hminimal htwo.2 hminSide
        have halmostE := E.almostWheelFree_torso_of_boundary_adj hnoWheel hab
        obtain ⟨T⟩ := hcore _ E.torso hthreeE halmostE
        exact E.minimalEnd_actualEdge_twoPairs_lift_away
          hminimal htwo.2 hminSide hnoWheel hab T
      · rcases E.minimalEnd_almostWheelFree_or_induced_boundary_degree
          hminimal htwo.2 hminSide hnoWheel hab with hlow | hhigh
        · obtain ⟨T⟩ := hcore _ E.torso hlow.1 hlow.2
          exact E.twoPairs_lift_away hminimal hlow.1 hlow.2 T
        · have hstruct := E.minimalEnd_torso_structure
              hminimal htwo.2 hminSide hnoWheel
          rcases hhigh with hleft | hright
          · exact E.hasFalseTwinsAway_of_inducedEnd_left_degree
              hminimal htwo.2 hminSide hnoWheel hab hstruct.1 hstruct.2
                hleft hsmall
          · exact E.hasFalseTwinsAway_of_inducedEnd_right_degree
              hminimal htwo.2 hminSide hnoWheel hab hright hsmall
  intro W _ _ H _ x₀ hcard htwo hdeg hnoWheel
  exact hP (Fintype.card W) W H x₀ rfl hcard htwo.1 hdeg hnoWheel

/-- Unconditional output of the complete component-and-cut-vertex reduction,
followed by the elementary two-cut extraction.  This theorem directly
consumes `AHTSection7.falseTwins_or_vertexTwoConnected_counterexample`: the
only counterexamples left are vertex-three-connected ones or explicit
two-cut ends with the torso lifting API above. -/
theorem falseTwins_or_threeConnected_counterexample_or_twoCutEnd
    [Nonempty V] (hdeg : ∀ w : V, 3 ≤ G.degree w)
    (hnoWheel : ¬HasWheelWitness G) :
    (∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3) ∨
      ∃ (W : Type u) (fW : Fintype W) (deqW : DecidableEq W)
        (H : SimpleGraph W) (dAdj : DecidableRel H.Adj) (y₀ : W),
        @AHTSection7.IsPointedFalseTwinCounterexample W fW deqW H dAdj y₀ ∧
          (H.Connected ∧
            ∀ c : W, (H.induce (fun w : W ↦ w ≠ c)).Connected) ∧
          ((@VertexThreeConnected W fW H) ∨
            Nonempty (@TwoCutEnd W H dAdj)) := by
  classical
  rcases AHTSection7.falseTwins_or_vertexTwoConnected_counterexample
      hdeg hnoWheel with hpair | hobs
  · exact Or.inl hpair
  · obtain ⟨W, fW, deqW, H, dAdj, y₀, hbad, htwo⟩ := hobs
    let : Fintype W := fW
    let : DecidableEq W := deqW
    let : DecidableRel H.Adj := dAdj
    have hterminal : VertexThreeConnected H ∨ Nonempty (TwoCutEnd H) :=
      pointedCounterexample_threeConnected_or_twoCutEnd y₀ hbad htwo
    exact Or.inr ⟨W, fW, deqW, H, dAdj, y₀, hbad, htwo, hterminal⟩

end AHTSection7TwoSeparation

end Erdos916
