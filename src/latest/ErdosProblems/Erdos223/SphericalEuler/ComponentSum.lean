import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open scoped BigOperators SimpleGraph

namespace SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance componentFintype (C : G.ConnectedComponent) : Fintype C :=
  Fintype.ofFinite C

noncomputable local instance componentAdjDecidable (C : G.ConnectedComponent) :
    DecidableRel C.toSimpleGraph.Adj := Classical.decRel _

noncomputable def componentVertexEquiv :
    (Σ C : G.ConnectedComponent, C) ≃ V :=
  Equiv.ofBijective (fun x ↦ x.2.1) ⟨by
    rintro ⟨C, u⟩ ⟨D, v⟩ huv
    have huvval : (u : V) = (v : V) := huv
    have hCD : C = D := ConnectedComponent.eq_of_common_vertex u.prop (by
      rw [huvval]
      exact v.prop)
    subst D
    have huv' : u = v := Subtype.ext huv
    subst v
    rfl, by
    intro v
    exact ⟨⟨G.connectedComponentMk v, ⟨v, rfl⟩⟩, rfl⟩⟩

lemma sum_card_connectedComponents :
    (∑ C : G.ConnectedComponent, Fintype.card C) = Fintype.card V := by
  rw [← Fintype.card_sigma, Fintype.card_congr (componentVertexEquiv G)]

noncomputable def componentDartEquiv :
    (Σ C : G.ConnectedComponent, C.toSimpleGraph.Dart) ≃ G.Dart :=
  Equiv.ofBijective (fun x ↦
    (⟨(x.2.fst.1, x.2.snd.1), x.2.adj⟩ : G.Dart)) ⟨by
    rintro ⟨C, d⟩ ⟨D, q⟩ hdq
    have hfst : (d.fst : V) = (q.fst : V) :=
      congrArg (fun r : G.Dart ↦ r.fst) hdq
    have hsnd : (d.snd : V) = (q.snd : V) :=
      congrArg (fun r : G.Dart ↦ r.snd) hdq
    have hCD : C = D := ConnectedComponent.eq_of_common_vertex d.fst.prop
      (hfst ▸ q.fst.prop)
    subst D
    have hdq' : d = q := SimpleGraph.Dart.ext d q
      (Prod.ext (Subtype.ext hfst) (Subtype.ext hsnd))
    subst q
    rfl, by
    intro d
    refine ⟨⟨G.connectedComponentMk d.fst,
      ⟨(⟨d.fst, rfl⟩,
        ⟨d.snd, (G.connectedComponentMk d.fst).mem_supp_of_adj_mem_supp rfl d.adj⟩),
          d.adj⟩⟩, ?_⟩
    exact SimpleGraph.Dart.ext _ _ rfl⟩

lemma sum_card_dart_connectedComponents :
    (∑ C : G.ConnectedComponent, Fintype.card C.toSimpleGraph.Dart) =
      Fintype.card G.Dart := by
  rw [← Fintype.card_sigma, Fintype.card_congr (componentDartEquiv G)]

lemma sum_card_edgeFinset_connectedComponents :
    (∑ C : G.ConnectedComponent, C.toSimpleGraph.edgeFinset.card) =
      G.edgeFinset.card := by
  have hd := sum_card_dart_connectedComponents G
  simp_rw [SimpleGraph.dart_card_eq_twice_card_edges] at hd
  rw [← Finset.mul_sum] at hd
  omega

theorem edge_add_four_le_two_mul_card_of_connectedComponent
    [Nonempty V]
    (hcomp : ∀ C : G.ConnectedComponent,
      C.toSimpleGraph.edgeFinset.card + 4 ≤ 2 * Fintype.card C) :
    G.edgeFinset.card + 4 ≤ 2 * Fintype.card V := by
  have hsum := Finset.sum_le_sum (fun C (_ : C ∈ (Finset.univ : Finset G.ConnectedComponent)) ↦
    hcomp C)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  rw [← Finset.mul_sum, sum_card_edgeFinset_connectedComponents G,
    sum_card_connectedComponents G] at hsum
  have hc : 0 < Fintype.card G.ConnectedComponent := Fintype.card_pos
  calc
    G.edgeFinset.card + 4 ≤
        G.edgeFinset.card + Fintype.card G.ConnectedComponent * 4 := by omega
    _ ≤ 2 * Fintype.card V := hsum

end SimpleGraph
