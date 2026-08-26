import ErdosProblems.Erdos547.GEPairTransfer

/-!
# Second separation lemma for an optimal GE pair

If `d` is deficient, no neighbour of an unsaturated anchor can receive a
positive allocation from a neighbour of `d`. Both fractional and oriented
allocations are covered.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

namespace GallaiEdmondsPartition

theorem IsOptimalGEPair.obstruction_to_transfer {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hμ : D.IsMaxSaturation w c μ) (h : D.IsOptimalGEPair w c μ σ ν) (hγ : 1 < γ)
    {d y x : V} (hy : y ∈ D.reachableVertices w c μ) (hdy : d ≠ y)
    (hyx : G.Adj y x) (hslack : σ.outLoad x < w.weight c x)
    (t : ℝ) (ht : 0 < t) (hroom : σ.load d + ν.load d + t ≤ w.weight c d)
    (τ : SkewMatching G γ) (ξ : FractionalMatching G) (hp : D.IsGEPair w c μ τ ξ)
    (hout : τ.outLoad x = σ.outLoad x)
    (hl : ∀ u, τ.load u + ξ.load u = σ.load u + ν.load u +
      (if u = d then t else 0) - (if u = y then t else 0)) : False := by
  have hs := saturation_eq_of_load_transfer w c (fun u ↦ σ.load u + ν.load u)
    (fun u ↦ τ.load u + ξ.load u) hdy t ht.le hl hroom (h.1.reachable_upper y hy)
  have ho := h.of_equal_saturation hp hs
  have hdef : τ.load y + ξ.load y < w.weight c y := by
    rw [hl, if_neg (Ne.symm hdy), if_pos rfl, add_zero]
    linarith [h.1.reachable_upper y hy]
  have he := ho.separation_one hμ hγ hy hdef hyx
  rw [hout] at he
  exact (ne_of_lt hslack) he

theorem IsOptimalGEPair.separation_two_fractional {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hμ : D.IsMaxSaturation w c μ) (h : D.IsOptimalGEPair w c μ σ ν) (hγ : 1 < γ)
    {d z y x : V} (hd : d ∈ D.reachableVertices w c μ)
    (hdef : σ.load d + ν.load d < w.weight c d) (hdz : G.Adj d z)
    (hyx : G.Adj y x) (hslack : σ.outLoad x < w.weight c x) : ν.weight z y = 0 := by
  classical
  apply le_antisymm _ (ν.nonnegative z y)
  by_contra hn
  have hpos : 0 < ν.weight z y := lt_of_not_ge hn
  have hz : z ∈ D.reachableNeighbours w c μ :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, hd, hdz⟩
  have hy := h.1.partner_reachable hμ hz hpos
  have hdy : d ≠ y := by
    intro he
    subst y
    exact (ne_of_lt hslack) (h.separation_one hμ hγ hd hdef hyx)
  have hpos' : 0 < ν.weight y z := by rw [ν.symmetric y z]; exact hpos
  let t := min (ν.weight y z) (w.weight c d - (σ.load d + ν.load d))
  have ht : 0 < t := lt_min hpos' (sub_pos.mpr hdef)
  have he : t ≤ ν.weight y z := min_le_left _ _
  have hr : σ.load d + ν.load d + t ≤ w.weight c d := by
    have hh : t ≤ w.weight c d - (σ.load d + ν.load d) := min_le_right _ _
    linarith
  obtain ⟨ξ, hp, hl⟩ := h.1.shift_fractional hμ hd hy hz hdz
    (ν.adj_of_weight_pos hpos') hdy t ht.le he hr
  exact h.obstruction_to_transfer hμ hγ hy hdy hyx hslack t ht hr σ ξ hp rfl hl

theorem IsOptimalGEPair.separation_two_skew {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hμ : D.IsMaxSaturation w c μ) (h : D.IsOptimalGEPair w c μ σ ν) (hγ : 1 < γ)
    {d z y x : V} (hd : d ∈ D.reachableVertices w c μ)
    (hdef : σ.load d + ν.load d < w.weight c d) (hdz : G.Adj d z)
    (hyx : G.Adj y x) (hslack : σ.outLoad x < w.weight c x) : σ.weight z y = 0 := by
  classical
  apply le_antisymm _ (σ.nonnegative z y)
  by_contra hn
  have hpos : 0 < σ.weight z y := lt_of_not_ge hn
  have hsupport : z ∈ D.reachableNeighbours w c μ ∧ y ∈ D.reachableVertices w c μ := by
    by_contra hn
    rw [h.1.skew_supported z y hn] at hpos
    exact (lt_irrefl 0) hpos
  have hzy : G.Adj z y := by
    by_contra hn
    rw [σ.supported z y hn] at hpos
    exact (lt_irrefl 0) hpos
  have hdy : d ≠ y := by
    intro he
    subst y
    exact (ne_of_lt hslack) (h.separation_one hμ hγ hd hdef hyx)
  have hγpos : 0 < γ := by linarith
  let t := min (σ.weight z y / (1 + γ))
    ((w.weight c d - (σ.load d + ν.load d)) / γ)
  have ht : 0 < t := lt_min (div_pos hpos σ.denominator_pos)
    (div_pos (sub_pos.mpr hdef) hγpos)
  have he : (1 + γ) * t ≤ σ.weight z y := by
    have hh := (le_div_iff₀ σ.denominator_pos).mp (show t ≤ _ from min_le_left _ _)
    simpa only [mul_comm] using hh
  have hr : σ.load d + ν.load d + γ * t ≤ w.weight c d := by
    have hh := (le_div_iff₀ hγpos).mp (show t ≤ _ from min_le_right _ _)
    nlinarith only [hh]
  obtain ⟨τ, hp, hout, hl⟩ := h.1.shift_skew hμ hd hsupport.2 hsupport.1 hdz.symm hzy
    (Ne.symm hdy) t ht.le he hr
  exact h.obstruction_to_transfer hμ hγ hsupport.2 hdy hyx hslack (γ * t)
    (mul_pos hγpos ht) hr τ ν hp (hout x) hl

theorem IsOptimalGEPair.separation_two {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ ν : FractionalMatching G} {σ : SkewMatching G γ}
    (hμ : D.IsMaxSaturation w c μ) (h : D.IsOptimalGEPair w c μ σ ν) (hγ : 1 < γ)
    {d z y x : V} (hd : d ∈ D.reachableVertices w c μ)
    (hdef : σ.load d + ν.load d < w.weight c d) (hdz : G.Adj d z)
    (hyx : G.Adj y x) (hslack : σ.outLoad x < w.weight c x) :
    σ.weight z y = 0 ∧ ν.weight z y = 0 :=
  ⟨h.separation_two_skew hμ hγ hd hdef hdz hyx hslack,
    h.separation_two_fractional hμ hγ hd hdef hdz hyx hslack⟩

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.separation_two
