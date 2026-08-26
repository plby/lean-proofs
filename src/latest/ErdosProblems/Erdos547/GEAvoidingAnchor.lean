import ErdosProblems.Erdos547.StructuralFlabellum
import ErdosProblems.Erdos547.AvoidingVertex

/-!
# An extremal avoiding anchor when the flabellum region is small
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

open scoped Classical in
theorem IsOptimalGEPair.exists_avoiding_anchor {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d₀ : V} {μ ν : FractionalMatching G}
    (a b₁ b₂ : ℝ) (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : b₁ < b₂)
    {σ : SkewMatching G (b₂ / b₁)}
    (hm : D.IsMaxSaturation w c μ) (h : D.IsOptimalGEPair w c μ σ ν)
    (hd₀ : d₀ ∈ D.reachableVertices w c μ)
    (hdef : σ.load d₀ + ν.load d₀ < w.weight c d₀)
    (hσ : σ.total ≤ b₁ + b₂) (hhigh : a + b₁ + b₂ ≤ w.degree c)
    (hsmall : ((D.reachableVertices w c μ ∪ D.flabellumExtra w c μ d₀ b₁).card : ℝ) < b₂) :
    ∃ d, d ∉ D.reachableVertices w c μ ∧ d ∉ D.flabellumExtra w c μ d₀ b₁ ∧
      ¬ G.Adj d₀ d ∧ σ.load d < w.weight c d ∧
      w.degreeOn (Finset.univ.filter (G.Adj d)) d₀ < b₁ / 2 ∧
      ∀ x, x ∉ D.reachableVertices w c μ → x ∉ D.flabellumExtra w c μ d₀ b₁ →
        ¬ G.Adj d₀ x → σ.load x < w.weight c x →
        w.degreeOn (Finset.univ.filter (G.Adj d₀)) x ≤
          w.degreeOn (Finset.univ.filter (G.Adj d₀)) d := by
  classical
  let R := D.reachableVertices w c μ
  let X := D.flabellumExtra w c μ d₀ b₁
  let C := Finset.univ.filter (G.Adj d₀)
  have hγ : 1 < b₂ / b₁ := (one_lt_div hb₁).mpr hb₂
  have hC : ∀ u ∈ C, w.weight c u = σ.outLoad u := by
    intro u hu
    exact (IsOptimalGEPair.separation_one hm h hγ hd₀ hdef (Finset.mem_filter.mp hu).2).symm
  have hs : σ.total / (1 + b₂ / b₁) ≤ b₁ := by
    calc
      _ ≤ (b₁ + b₂) / (1 + b₂ / b₁) :=
        div_le_div_of_nonneg_right hσ σ.denominator_pos.le
      _ = _ := (skew_parts_of_sum b₁ b₂ hb₁ (hb₁.le.trans hb₂.le)).1
  have hdeg : ((R ∪ X).card : ℝ) + σ.total / (1 + b₂ / b₁) < w.degree c := by
    change ((R ∪ X).card : ℝ) < b₂ at hsmall
    linarith
  obtain ⟨d, hd, hslack, hmax⟩ := exists_maximal_avoiding_vertex w c σ (R ∪ X) C hC hdeg
  have hdR : d ∉ R := fun hu ↦ hd (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  have hdX : d ∉ X := fun hu ↦ hd (Finset.mem_union_left _ (Finset.mem_union_right _ hu))
  have hdC : ¬ G.Adj d₀ d := fun hu ↦ hd
    (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩))
  have hdload : σ.load d < w.weight c d := by
    rw [h.1.load_eq_outLoad hdR]
    exact hslack
  refine ⟨d, hdR, hdX, hdC, hdload, ?_, ?_⟩
  · apply lt_of_not_ge
    intro hov
    exact hdX (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (σ.outLoad_nonneg d).trans_lt hslack, hdR, hdC, hov⟩)
  · intro x hxR hxX hxC hxslack
    apply hmax x
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_union.mp hx).elim hxR hxX
      · exact hxC (Finset.mem_filter.mp hx).2
    · rwa [← h.1.load_eq_outLoad hxR]

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.exists_avoiding_anchor
