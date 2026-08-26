import ErdosProblems.Erdos547.GESaturationDegree
import ErdosProblems.Erdos547.CappedIndependentRows
import ErdosProblems.Erdos547.ReservedAllocation

/-!
# A prescribed fractional piece between the separator and reachable vertices
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem IsMaxSaturation.exists_selected_piece {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) {d : V} (hd : d ∈ D.reachableVertices w c μ)
    (k : ℝ) (hk : 0 ≤ k) (hdegree : k ≤ w.degree d) :
    ∃ P : FractionalMatching G, (∀ u v, P.weight u v ≤ μ.weight u v) ∧
      P.RunsBetween D.separator (D.reachableVertices w c μ) ∧ P.total = k ∧
      (∀ u ∈ D.separator, P.load u ≤ w.weight d u) ∧
      (∀ u ∈ D.reachableVertices w c μ, P.load u ≤ w.weight c u) := by
  classical
  obtain ⟨r, hr, hrw, hrtotal⟩ := exists_capped_reservation (w.weight d) (w.nonnegative d)
    k hk hdegree
  have hzero : ∀ u ∈ D.separator, ∀ v ∈ D.separator, μ.weight u v = 0 :=
    fun _ hu _ hv ↦ h.1.2 _ _ (D.not_allowed_separator hu hv)
  let P := μ.capIndependent D.separator hzero r hr
  have hP (u v : V) : P.weight u v ≤ μ.weight u v :=
    μ.capIndependent_weight_le D.separator hzero r hr u v
  have hload (u : V) (hu : u ∈ D.separator) : P.load u = r u := by
    rw [show P.load u = min (r u) (μ.load u) from
      μ.capIndependent_load D.separator hzero r hr hu, h.1.load_separator hu]
    exact min_eq_left ((hrw u).trans (w.at_most_one d u))
  have hR (u v : V) (hu : u ∈ D.separator) (huv : 0 < P.weight u v) :
      v ∈ D.reachableVertices w c μ := by
    have hrpos : 0 < r u := by
      rw [← hload u hu]
      exact P.load_pos_of_weight_pos huv
    have hadj : G.Adj d u := by
      by_contra hn
      have hz := w.supported d u hn
      linarith [hrw u]
    have hN : u ∈ D.reachableNeighbours w c μ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, hd, hadj⟩
    exact D.reachable_partner_mem w c μ hN (huv.trans_le (hP u v))
  refine ⟨P, hP, ?_, ?_, fun u hu ↦ (hload u hu).le.trans (hrw u), ?_⟩
  · intro u v hp
    rcases μ.capIndependent_runsBetween D.separator hzero r hr u v hp with hu | hv
    · exact Or.inl ⟨hu.1, hR u v hu.1 hp⟩
    · exact Or.inr ⟨hR v u hv.2 (by rwa [P.symmetric v u]), hv.2⟩
  · rw [show P.total = ∑ u ∈ D.separator, min (r u) (μ.load u) from
      μ.capIndependent_total D.separator hzero r hr]
    calc
      _ = ∑ u ∈ D.separator, r u := Finset.sum_congr rfl fun u hu ↦ by
        rw [h.1.load_separator hu, min_eq_left ((hrw u).trans (w.at_most_one d u))]
      _ = ∑ u, r u := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro u _ hu
        have hz : w.weight d u = 0 := w.supported d u (fun hadj ↦
          hu (D.neighbour_of_singleton_mem_separator (h.reachable_singleton hd) hadj))
        exact le_antisymm ((hrw u).trans_eq hz) (hr u)
      _ = k := hrtotal
  · intro u hu
    exact (P.load_le_of_weight_le μ hP u).trans (h.reachable_load_le hu)

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.exists_selected_piece
