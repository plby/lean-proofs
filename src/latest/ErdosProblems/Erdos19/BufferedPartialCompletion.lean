import ErdosProblems.Erdos19.ActivePaletteRepair
import ErdosProblems.Erdos19.SaturatedPartialCompletion

/-! # Completing a buffered partial coloring with the exact fresh palette

This is a finite criterion: the block buffers repair every active color,
inactive colors already cover the required vertices except for one allowed
independent remainder, and the residual degree bound finishes the coloring.
-/

namespace Erdos19.SetHypergraph

variable {V I : Type*} [Fintype V]

attribute [local instance] Classical.propDecidable

theorem edgeColorable_of_buffered_partial_coloring (H J : SetHypergraph V)
    (hJH : J ⊆ H) (hlinear : H.IsLinear) (hmin : ∀ e : H, 2 ≤ e.1.ncard)
    (hpair : ∀ e ∈ H, e ∉ J → e.ncard = 2)
    (m D : ℕ) (hD : 0 < D) (hvertices : Fintype.card V = m + D)
    (color : J.EdgeColoring (Fin m)) (p : ℕ) (index : Fin p ↪ Fin m) (bad : Fin m)
    (U Y Z : Set V) (hUY : Disjoint U Y) (X : I → Set V)
    (hX : Pairwise fun i j ↦ Disjoint (X i) (X j)) (hXcover : ∀ v, ∃ i, v ∈ X i)
    (missing requests : ℕ) (B : Fin p → I → Set V)
    (hBY : ∀ i j, B i j ⊆ Y) (hBX : ∀ i j, B i j ⊆ X j)
    (hBavoid : ∀ i j, Disjoint (B i j) (J.coveredVertices {e | color e = index i}))
    (hBsize : ∀ i j, missing + requests ≤ (B i j).ncard)
    (hmissing : ∀ i j u, u ∈ (U \ J.coveredVertices {e | color e = index i}) ∩ X j →
      ((((U \ J.coveredVertices {e | color e = index i}) ∩ X j) ∪ B i j) \
        (H \ J).twoGraph.neighborSet u).ncard ≤ missing)
    (hrequests : ∀ v, (∑ i : Fin p,
      if v ∈ U \ J.coveredVertices {e | color e = index i} then 1 else 0) ≤ requests)
    (hinactive : ∀ a, a ∉ Set.range index → ∀ v ∈ U,
      v ∉ Z ∨ a ≠ bad → v ∈ J.coveredVertices {e | color e = a})
    (houtside : ∀ v, v ∉ U → (H \ J).twoGraph.degree v < D)
    (hindependent : ∀ x ∈ Z, ∀ y ∈ Z, ¬H.twoGraph.Adj x y) :
    H.EdgeColorable (m + D) := by
  classical
  obtain ⟨J', color', hJJ', hJ'H, _, hactive, hold⟩ :=
    H.exists_extension_covering_active_colors J hJH color p index U Y hUY X hX hXcover
      missing requests B hBY hBX hBavoid hBsize hmissing hrequests
  have hcolorCover (v : V) (hv : v ∈ U) (a : Fin m) (ha : v ∉ Z ∨ a ≠ bad) :
      v ∈ J'.coveredVertices {e | color' e = a} := by
    by_cases hactiveA : a ∈ Set.range index
    · obtain ⟨i, rfl⟩ := hactiveA
      exact hactive i hv
    · exact hold a (hinactive a hactiveA v hv ha)
  have hcover : ∀ v ∈ U, m ≤ (J'.incidentEdges v).ncard + if v ∈ Z then 1 else 0 := by
    intro v hv
    by_cases hvZ : v ∈ Z
    · rw [if_pos hvZ]
      apply J'.incident_degree_lower_of_one_color_exception m color' v bad
      intro a ha
      rw [J'.colorCovered_eq_coveredVertices color' a]
      exact hcolorCover v hv a (Or.inr ha)
    · rw [if_neg hvZ, Nat.add_zero]
      apply le_of_eq
      symm
      apply J'.incident_degree_eq_of_full_color_coverage m color' v
      intro a
      rw [J'.colorCovered_eq_coveredVertices color' a]
      exact hcolorCover v hv a (Or.inl hvZ)
  have houtside' : ∀ v, v ∉ U → (H \ J').twoGraph.degree v < D := by
    intro v hv
    have hgraph : (H \ J').twoGraph ≤ (H \ J).twoGraph := by
      intro x y hxy
      exact ⟨hxy.1, hxy.2.1, fun heJ ↦ hxy.2.2 (hJJ' heJ)⟩
    exact (_root_.SimpleGraph.degree_le_of_le hgraph).trans_lt (houtside v hv)
  exact H.edgeColorable_of_almost_saturated_partial_coloring J' hJ'H hlinear hmin
    (fun e he hnot ↦ hpair e he (fun heJ ↦ hnot (hJJ' heJ))) m D hD hvertices color'
    U Z hcover houtside' hindependent

#print axioms edgeColorable_of_buffered_partial_coloring

end Erdos19.SetHypergraph
