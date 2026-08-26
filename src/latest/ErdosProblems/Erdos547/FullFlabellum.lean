import ErdosProblems.Erdos547.StructuralFlabellum

/-!
# The flabellum argument also allows vertices outside the first anchor's neighbourhood

The completion proof only charges their total load. It does not require these
extra tail vertices to be adjacent to the first anchor.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

open scoped Classical in
def fullFlabellumExtra (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) (d : V) (b : ℝ) : Finset V := Finset.univ.filter
      (fun u ↦ u ∉ D.reachableVertices w c μ ∧ ¬ G.Adj d u ∧
        b / 2 ≤ w.degreeOn (Finset.univ.filter (G.Adj u)) d)

open scoped Classical in
theorem IsOptimalGEPair.anchoredTotals_of_full_flabellum {D : GallaiEdmondsPartition G}
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
      D.fullFlabellumExtra w c μ d b₁).card : ℝ)) :
    HasAnchoredTotals w (a₂ / a₁) ((m : ℝ) / b₁) (a₁ + a₂) (b₁ + m) :=
  h.anchoredTotals_of_flabellum_set a₁ a₂ b₁ m ha₁ ha₂ hb₁ hm hd hdef hσ hhalf hhigh
    hdegree hoverlap _ (fun _ hu ↦ (Finset.mem_filter.mp hu).2) hsize

open scoped Classical in
theorem degreeOn_lt_of_not_fullFlabellumExtra (D : GallaiEdmondsPartition G)
    (w : EdgeWeights G) (c : V) (μ : FractionalMatching G) (d : V) (b : ℝ) {u : V}
    (huR : u ∉ D.reachableVertices w c μ) (hdu : ¬ G.Adj d u)
    (huX : u ∉ D.fullFlabellumExtra w c μ d b) :
    w.degreeOn (Finset.univ.filter (G.Adj u)) d < b / 2 := by
  apply lt_of_not_ge
  exact fun h ↦ huX (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huR, hdu, h⟩)

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.anchoredTotals_of_full_flabellum
