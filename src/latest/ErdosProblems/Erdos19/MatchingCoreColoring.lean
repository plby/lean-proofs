import ErdosProblems.Erdos19.VizingExtension

/-! # Degree-sized edge coloring when the maximum-degree core is a matching -/

namespace Erdos19.Vizing

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- Each vertex of degree `D` has at most one neighbor of degree `D`. This
includes an independent maximum-degree core. -/
def HasMatchingDegreeCore (G : SimpleGraph V) (D : ℕ) : Prop :=
  ∀ x y z, G.degree x = D → G.Adj x y → G.Adj x z →
    G.degree y = D → G.degree z = D → y = z

theorem HasMatchingDegreeCore.mono {G H : SimpleGraph V} {D : ℕ}
    (hcore : HasMatchingDegreeCore G D) (hdegree : ∀ v, G.degree v ≤ D) (hHG : H ≤ G) :
    HasMatchingDegreeCore H D := by
  have hhigh : ∀ v, H.degree v = D → G.degree v = D := by
    intro v hv
    have hle : H.degree v ≤ G.degree v := H.degree_le_of_le hHG
    have hupper := hdegree v
    omega
  intro x y z hx hxy hxz hy hz
  exact hcore x y z (hhigh x hx) (hHG hxy) (hHG hxz) (hhigh y hy) (hhigh z hz)

theorem exists_edge_with_low_other_neighbors (G : SimpleGraph V) (D : ℕ) (hD : 0 < D)
    (hdegree : ∀ v, G.degree v ≤ D) (hcore : HasMatchingDegreeCore G D) (hG : G ≠ ⊥) :
    ∃ x y, G.Adj x y ∧ ∀ z, G.Adj x z → z ≠ y → G.degree z < D := by
  classical
  by_cases hhigh : ∃ x, G.degree x = D
  · obtain ⟨x, hx⟩ := hhigh
    by_cases hneighbor : ∃ y, G.Adj x y ∧ G.degree y = D
    · obtain ⟨y, hxy, hy⟩ := hneighbor
      refine ⟨x, y, hxy, ?_⟩
      intro z hxz hzy
      by_contra hlt
      have hz : G.degree z = D := Nat.le_antisymm (hdegree z) (Nat.le_of_not_gt hlt)
      exact hzy (hcore x z y hx hxz hxy hz hy)
    · have hpos : 0 < (G.neighborFinset x).card := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree, hx] using hD
      obtain ⟨y, hy⟩ := card_pos.mp hpos
      have hxy : G.Adj x y := by simpa only [SimpleGraph.mem_neighborFinset] using hy
      refine ⟨x, y, hxy, ?_⟩
      intro z hxz _
      by_contra hlt
      exact hneighbor ⟨z, hxz, Nat.le_antisymm (hdegree z) (Nat.le_of_not_gt hlt)⟩
  · obtain ⟨x, y, hxy⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG
    refine ⟨x, y, hxy, ?_⟩
    intro z _ _
    by_contra hlt
    exact hhigh ⟨z, Nat.le_antisymm (hdegree z) (Nat.le_of_not_gt hlt)⟩

/-- The graph has a complete proper coloring with `D` colors if its
degree-`D` core is a matching. The proof is finite edge-count induction. -/
theorem exists_complete_coloring_of_matching_core (D : ℕ) (hD : 0 < D)
    (G : SimpleGraph V) (hdegree : ∀ v, G.degree v ≤ D)
    (hcore : HasMatchingDegreeCore G D) :
    ∃ C : PartialColoring V (Fin D), IsProper G C ∧
      ∀ x y, G.Adj x y → ∃ a, C s(x, y) = some a := by
  classical
  have hmain : ∀ m : ℕ, ∀ G : SimpleGraph V, G.edgeFinset.card = m →
      (∀ v, G.degree v ≤ D) → HasMatchingDegreeCore G D →
      ∃ C : PartialColoring V (Fin D), IsProper G C ∧
        ∀ x y, G.Adj x y → ∃ a, C s(x, y) = some a := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro G hcard hdegree hcore
      by_cases hG : G = ⊥
      · refine ⟨fun _ ↦ none, ?_, ?_⟩
        · intro u v w a _ _ hc _
          contradiction
        · intro x y hxy
          simp [hG] at hxy
      · obtain ⟨x, y, hxy, hlow⟩ := exists_edge_with_low_other_neighbors G D hD hdegree hcore hG
        let removed : Finset (Sym2 V) := {s(x, y)}
        let H := G.deleteEdges (removed : Set (Sym2 V))
        let : DecidableRel H.Adj := fun u v ↦ Classical.propDecidable (H.Adj u v)
        have hHG : H ≤ G := G.deleteEdges_le _
        have hHdegree : ∀ v, H.degree v ≤ D := fun v ↦
          (H.degree_le_of_le hHG).trans (hdegree v)
        have hHcore : HasMatchingDegreeCore H D := hcore.mono hdegree hHG
        have hHedges : H.edgeFinset = G.edgeFinset.erase s(x, y) := by
          ext e
          simp [H, removed, SimpleGraph.edgeSet_deleteEdges, and_comm]
        have hmem : s(x, y) ∈ G.edgeFinset := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxy
        have hHlt : H.edgeFinset.card < m := by
          rw [← hcard, hHedges]
          exact card_erase_lt_of_mem hmem
        obtain ⟨C₀, hC₀, hcomplete₀⟩ := ih H.edgeFinset.card hHlt H rfl hHdegree hHcore
        let C := maskToGraph H C₀
        have hC : IsProper G C := maskToGraph_proper G H C₀ hC₀
        have hzero : C s(x, y) = none := by
          apply maskToGraph_of_not_mem
          simp [H, removed, SimpleGraph.edgeSet_deleteEdges]
        have hother : ∀ e, e ∈ G.edgeSet → e ≠ s(x, y) → (C e).isSome := by
          intro e he hne
          have heH : e ∈ H.edgeSet := by
            simp [H, removed, SimpleGraph.edgeSet_deleteEdges, he, hne]
          change (maskToGraph H C₀ e).isSome
          rw [maskToGraph_of_mem H C₀ e heH]
          induction e using Sym2.inductionOn with
          | hf u v =>
            obtain ⟨a, ha⟩ := hcomplete₀ u v heH
            simp [ha]
        exact exists_complete_extension_of_single_uncolored G C hC x y hxy hzero hother
          (by simpa only [Fintype.card_fin] using hdegree)
          (by simpa only [Fintype.card_fin] using hlow)
  exact hmain G.edgeFinset.card G rfl hdegree hcore

theorem exists_edgeLabeling_of_matching_core (G : SimpleGraph V) (D : ℕ) (hD : 0 < D)
    (hdegree : ∀ v, G.degree v ≤ D) (hcore : HasMatchingDegreeCore G D) :
    ∃ c : G.EdgeLabeling (Fin D), ∀ x y z (hxy : G.Adj x y) (hxz : G.Adj x z),
      c.get x y hxy = c.get x z hxz → y = z := by
  obtain ⟨C, hC, hcomplete⟩ := exists_complete_coloring_of_matching_core D hD G hdegree hcore
  let c : G.EdgeLabeling (Fin D) := fun e ↦ (C e.val).getD ⟨0, hD⟩
  refine ⟨c, ?_⟩
  intro x y z hxy hxz hsame
  obtain ⟨a, ha⟩ := hcomplete x y hxy
  obtain ⟨b, hb⟩ := hcomplete x z hxz
  have hab : a = b := by simpa only [c, SimpleGraph.EdgeLabeling.get, ha, hb,
    Option.getD_some] using hsame
  exact hC hxy hxz ha (hab ▸ hb)

#print axioms exists_complete_coloring_of_matching_core
#print axioms exists_edgeLabeling_of_matching_core

end Erdos19.Vizing
