import ErdosProblems.Erdos547.GEReversePiece
import ErdosProblems.Erdos547.ReverseRegionNumbers
import ErdosProblems.Erdos547.NeighbourhoodOverlap

/-!
# Size estimates for the initial allocation in the avoiding case
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

open scoped Classical in
theorem IsGEPair.restricted_reverse_mass_gt {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d e : V} {μ ν : FractionalMatching G}
    (b₁ b₂ k : ℝ) (hb₁ : 0 < b₁) (hb₂ : b₁ ≤ b₂) (hbk : b₂ ≤ k)
    {σ : SkewMatching G (b₂ / b₁)}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (he : e ∈ D.reachableVertices w c μ) (hdegree : k / 2 ≤ w.degree e)
    (hoverlap : w.degreeOn (Finset.univ.filter (G.Adj d)) e < b₁ / 2) :
    w.degreeOn (Finset.univ.filter (G.Adj e)) d + k / 2 <
      ((1 + b₂ / b₁) / (b₂ / b₁)) *
        (ν.touching (Finset.univ.filter (G.Adj e) : Set V)).total +
          (σ.touching (Finset.univ.filter (G.Adj e) : Set V)).total := by
  classical
  let C := Finset.univ.filter (G.Adj e)
  have hC : C ⊆ D.reachableNeighbours w c μ := fun u hu ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, (Finset.mem_filter.mp hu).2⟩
  have hmass := h.restricted_cover_identity hm C hC
  have hcard : k / 2 ≤ (C.card : ℝ) := hdegree.trans
    (w.degree_le_card_of_neighbours_subset e C
      (fun _ hu ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩))
  have hbound : w.degreeOn C d + k / 2 - b₁ / 2 < (C.card : ℝ) := by
    have hh := w.neighbourhood_overlap_card_bound d e
    change w.degreeOn C d + w.degree e -
      w.degreeOn (Finset.univ.filter (G.Adj d)) e ≤ (C.card : ℝ) at hh
    linarith
  apply reverse_region_mass_bound _ _ (C.card : ℝ) b₁ b₂ k (w.degreeOn C d)
    _ hb₁ hb₂ hmass (by linarith) hbound
  exact Finset.sum_nonneg fun u _ ↦ Finset.sum_nonneg fun v _ ↦
    (σ.touching (C : Set V)).nonnegative u v

theorem IsGEPair.exists_reverse_piece_below_budget {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G}
    (b₁ b₂ : ℝ) (hb₁ : 0 < b₁) (hb₂ : b₁ ≤ b₂)
    {σ : SkewMatching G (b₂ / b₁)}
    (h : D.IsGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (C : Finset V) (hC : C ⊆ D.reachableNeighbours w c μ)
    (hR : ((D.reachableVertices w c μ).card : ℝ) < b₂) :
    ∃ ρ : SkewMatching G (b₂ / b₁),
      ρ.DominatedByFractional (ν.touching (C : Set V)) ∧
      ρ.total = (1 + b₂ / b₁) / (b₂ / b₁) * (ν.touching (C : Set V)).total ∧
      (∀ u ∉ D.reachableVertices w c μ, ρ.outLoad u = 0) ∧
      ∃ hc : ∀ u, σ.load u + ρ.load u ≤ 1, (σ.add ρ hc).Fits w c ∧
        σ.total + ρ.total < b₁ + b₂ := by
  have hγ : 1 ≤ b₂ / b₁ := (one_le_div hb₁).mpr hb₂
  have hgp : 0 < b₂ / b₁ := zero_lt_one.trans_le hγ
  obtain ⟨ρ, hρ, htρ, houtρ, hc, hfit, hsize⟩ := h.exists_reverse_piece hm hγ C hC
  refine ⟨ρ, hρ, htρ, houtρ, hc, hfit, ?_⟩
  have hh := (div_lt_iff₀ σ.denominator_pos).mp (hsize.trans_lt hR)
  have he : b₂ * (1 + b₂ / b₁) = (b₂ / b₁) * (b₁ + b₂) := by field_simp
  rw [he] at hh
  exact (mul_lt_mul_iff_right₀ hgp).mp hh

end GallaiEdmondsPartition

end Erdos547.DPRS

namespace Erdos547.DPRS.GallaiEdmondsPartition
#print axioms IsGEPair.restricted_reverse_mass_gt
#print axioms IsGEPair.exists_reverse_piece_below_budget
end Erdos547.DPRS.GallaiEdmondsPartition
