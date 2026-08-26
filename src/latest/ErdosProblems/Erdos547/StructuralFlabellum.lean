import ErdosProblems.Erdos547.GECoveredRegion
import ErdosProblems.Erdos547.FlabellumRegion
import ErdosProblems.Erdos547.NeighbourhoodOverlap

/-!
# The flabellum case of the structural matching theorem
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

open scoped Classical in
def flabellumExtra (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) (d : V) (b : ℝ) : Finset V := Finset.univ.filter
      (fun u ↦ 0 < w.weight c u ∧ u ∉ D.reachableVertices w c μ ∧ ¬ G.Adj d u ∧
        b / 2 ≤ w.degreeOn (Finset.univ.filter (G.Adj u)) d)

open scoped Classical in
theorem IsOptimalGEPair.anchoredTotals_of_flabellum_set {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d : V} {μ ν : FractionalMatching G}
    (a₁ a₂ b₁ : ℝ) (m : ℕ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁)
    {σ : SkewMatching G ((m : ℝ) / b₁)}
    (hm : D.IsMaxSaturation w c μ) (h : D.IsOptimalGEPair w c μ σ ν)
    (hd : d ∈ D.reachableVertices w c μ)
    (hdef : σ.load d + ν.load d < w.weight c d)
    (hσ : σ.total ≤ b₁ + m)
    (hhalf : (a₁ + a₂ + b₁ + m) / 2 ≤ (m : ℝ))
    (hhigh : a₁ + a₂ + b₁ + m ≤ w.degree c)
    (hdegree : ∀ x, (a₁ + a₂ + b₁ + m) / 2 ≤ w.degree x)
    (hoverlap : ∀ y ∈ D.reachableVertices w c μ,
      b₁ ≤ w.degreeOn (Finset.univ.filter (G.Adj y)) d)
    (X : Finset V)
    (hXprops : ∀ u ∈ X, u ∉ D.reachableVertices w c μ ∧ ¬ G.Adj d u ∧
      b₁ / 2 ≤ w.degreeOn (Finset.univ.filter (G.Adj u)) d)
    (hsize : (m : ℝ) ≤ ((D.reachableVertices w c μ ∪ X).card : ℝ)) :
    HasAnchoredTotals w (a₂ / a₁) ((m : ℝ) / b₁) (a₁ + a₂) (b₁ + m) := by
  classical
  let C := Finset.univ.filter (G.Adj d)
  let Z := D.saturatedSeparator w c σ
  let R := D.reachableVertices w c μ
  let W := D.coveredReachable w c μ σ ν C
  have hγ : 1 < (m : ℝ) / b₁ := (one_lt_div hb₁).mpr (by linarith)
  have hC : C ⊆ D.reachableNeighbours w c μ := fun u hu ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, hd, (Finset.mem_filter.mp hu).2⟩
  have hCZ : C ⊆ Z := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨hm.reachable_neighbour_separator (hC hu),
      IsOptimalGEPair.separation_one hm h hγ hd hdef (Finset.mem_filter.mp hu).2⟩
  have hZR : Disjoint Z R := Finset.disjoint_left.mpr fun u hu hv ↦
    D.singleton_not_separator (hm.reachable_singleton hv) (Finset.mem_filter.mp hu).1
  have hWR : W ⊆ R := Finset.filter_subset _ _
  have hX : Disjoint X (R ∪ C) := Finset.disjoint_left.mpr fun u hu hv ↦ by
    have hx := hXprops u hu
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hx.1 hv
    · exact hx.2.1 (Finset.mem_filter.mp hv).2
  have hW : (a₁ + a₂ + b₁ + m) / 2 ≤ (W.card : ℝ) := by
    calc
      _ ≤ w.degree d := hdegree d
      _ ≤ (C.card : ℝ) := w.degree_le_card_of_neighbours_subset d C
        (fun _ hu ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
      _ ≤ _ := h.1.coveredReachable_card_bound hm hγ.le C hC
  have hZ : w.degreeOn Z c ≤ b₁ := by
    calc
      _ ≤ σ.total / (1 + (m : ℝ) / b₁) := D.saturatedSeparator_degree_le w c σ
      _ ≤ (b₁ + m) / (1 + (m : ℝ) / b₁) :=
        div_le_div_of_nonneg_right hσ σ.denominator_pos.le
      _ = _ := (skew_parts_of_sum b₁ m hb₁ (Nat.cast_nonneg _)).1
  have hcd : G.Adj c d := by
    by_contra hn
    rw [w.supported c d hn] at hdef
    linarith [σ.load_nonneg d, ν.load_nonneg d]
  apply anchoredTotals_of_flabellum_region w hcd a₁ a₂ b₁ m ha₁ ha₂ hb₁ hhalf C Z R W X
    hCZ hZR hWR hX hW hsize
  · intro y hy
    rw [show C = Finset.univ.filter (G.Adj d) from rfl, w.degreeOn_common_neighbours]
    exact hoverlap y hy
  · intro y hy
    rw [show C = Finset.univ.filter (G.Adj d) from rfl, w.degreeOn_common_neighbours]
    exact (hXprops y hy).2.2
  · intro y hy x hxy
    exact h.coveredReachable_neighbours hm hγ hd hdef C
      (fun _ hu ↦ (Finset.mem_filter.mp hu).2) hy hxy
  · exact hZ
  · exact hhigh
  · exact hdegree

open scoped Classical in
theorem IsOptimalGEPair.anchoredTotals_of_flabellum {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d : V} {μ ν : FractionalMatching G}
    (a₁ a₂ b₁ : ℝ) (m : ℕ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁)
    {σ : SkewMatching G ((m : ℝ) / b₁)}
    (hm : D.IsMaxSaturation w c μ) (h : D.IsOptimalGEPair w c μ σ ν)
    (hd : d ∈ D.reachableVertices w c μ)
    (hdef : σ.load d + ν.load d < w.weight c d)
    (hσ : σ.total ≤ b₁ + m)
    (hhalf : (a₁ + a₂ + b₁ + m) / 2 ≤ (m : ℝ))
    (hhigh : a₁ + a₂ + b₁ + m ≤ w.degree c)
    (hdegree : ∀ x, (a₁ + a₂ + b₁ + m) / 2 ≤ w.degree x)
    (hoverlap : ∀ y ∈ D.reachableVertices w c μ,
      b₁ ≤ w.degreeOn (Finset.univ.filter (G.Adj y)) d)
    (hsize : (m : ℝ) ≤ ((D.reachableVertices w c μ ∪
      D.flabellumExtra w c μ d b₁).card : ℝ)) :
    HasAnchoredTotals w (a₂ / a₁) ((m : ℝ) / b₁) (a₁ + a₂) (b₁ + m) :=
  h.anchoredTotals_of_flabellum_set a₁ a₂ b₁ m ha₁ ha₂ hb₁ hm hd hdef hσ hhalf hhigh
    hdegree hoverlap _ (fun _ hu ↦ (Finset.mem_filter.mp hu).2.2) hsize

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.anchoredTotals_of_flabellum
