import ErdosProblems.Erdos547.GESaturationDegree

/-!
# Degree and saturation budgets on the reachable set
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem IsMaxSaturation.outside_reachable_covered {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) {u : V} (hu : u ∉ D.reachableVertices w c μ) :
    w.weight c u ≤ μ.load u := by
  classical
  by_contra hn
  have hdef := lt_of_not_ge hn
  exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, h.1.deficient_singleton hdef,
    hdef, Relation.ReflTransGen.refl⟩)

theorem IsMaxSaturation.reachable_degree_identity {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) :
    w.degreeOn (D.reachableVertices w c μ) c + w.saturation μ.load c =
      w.degree c + ∑ u ∈ D.reachableVertices w c μ, μ.load u := by
  classical
  let R := D.reachableVertices w c μ
  have hdeg : w.degreeOn R c + w.degreeOn Rᶜ c = w.degree c :=
    Finset.sum_add_sum_compl R (w.weight c)
  have hsat : (∑ u ∈ R, μ.load u) + w.degreeOn Rᶜ c = w.saturation μ.load c := by
    have he := Finset.sum_add_sum_compl R (fun u ↦ min (w.weight c u) (μ.load u))
    have hR : (∑ u ∈ R, min (w.weight c u) (μ.load u)) = ∑ u ∈ R, μ.load u :=
      Finset.sum_congr rfl fun _ hu ↦ min_eq_right (h.reachable_load_le hu)
    have hC : (∑ u ∈ Rᶜ, min (w.weight c u) (μ.load u)) = w.degreeOn Rᶜ c :=
      Finset.sum_congr rfl fun _ hu ↦
        min_eq_left (h.outside_reachable_covered (Finset.mem_compl.mp hu))
    rwa [hR, hC] at he
  change w.degreeOn R c + w.saturation μ.load c = w.degree c + ∑ u ∈ R, μ.load u
  linarith

theorem IsMaxSaturation.neighbour_not_reachable {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) {u v : V} (hu : u ∈ D.reachableVertices w c μ)
    (huv : G.Adj u v) : v ∉ D.reachableVertices w c μ := by
  intro hv
  exact D.singleton_not_separator (h.reachable_singleton hv)
    (D.neighbour_of_singleton_mem_separator (h.reachable_singleton hu) huv)

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.reachable_degree_identity
