import ErdosProblems.Erdos19.FiniteModel
import ErdosProblems.Erdos19.ApproximateCoveredColoring
import ErdosProblems.Erdos19.CoveredColorParameters

/-! # Sparse lists and small covered classes for bounded-rank linear hypergraphs

The palette degree parameter is `floor(n/s)`, while the actual maximum degree
is at most `floor(n/(16*a*s))`. This slack supplies a dummy pool of `floor(n/a)`
vertices. Every numerical prerequisite of the capacity theorem is discharged.
-/

namespace Erdos19.SetHypergraph

open Erdos76 Erdos76.FiniteHypergraph

theorem eventually_bounded_rank_covered_lists (R s a : ℕ)
    (hR : 0 < R) (hs : 0 < s) (ha : 0 < a) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 16 * a * s + 1 ≤ e.1.ncard) → (∀ e : H, e.1.ncard ≤ R) →
      ∀ (P : Type) [Fintype P] [DecidableEq P], ∀ F : H → Finset P,
        (∀ e, ((F e).card : ℝ) ≤ delta * ((n / s : ℕ) : ℝ)) →
        2 * (n / s) ≤ Fintype.card P →
        ∃ c : H.EdgeColoring P, (∀ e, c.color e ∉ F e) ∧
          ∀ x, (H.coveredVertices {e : H | c.color e = x}).ncard ≤ n / a := by
  classical
  obtain ⟨delta, hdelta, D₀, hround⟩ :=
    bounded_approximate_covered_coloring R (4 * s) hR 1 (by norm_num)
  obtain ⟨M, D₁, hcodegree⟩ := exists_codegree_parameter delta hdelta
  let Dmin := max D₀ (max D₁ 1)
  let B := 2 * R + (2 * R) * (2 * R * M)
  let N := max (s * Dmin) (a * (2 * B + 2))
  refine ⟨delta, hdelta, N, ?_⟩
  intro n hn H hlinear hmin hmax P _ _ F hF hpalette
  let D := n / s
  let d := n / (16 * a * s)
  let p := n / a
  have hDmin : Dmin ≤ D := by
    apply (Nat.le_div_iff_mul_le hs).mpr
    have h : s * Dmin ≤ n := (le_max_left _ _).trans hn
    simpa only [Nat.mul_comm] using h
  have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hDmin
  have hD₁ : D₁ ≤ D := ((le_max_left _ _).trans (le_max_right _ _)).trans hDmin
  have hDpos : 0 < D := ((le_max_right _ _).trans (le_max_right _ _)).trans hDmin
  have hp : 2 * B + 2 ≤ p := by
    apply (Nat.le_div_iff_mul_le ha).mpr
    have h : a * (2 * B + 2) ≤ n := (le_max_right _ _).trans hn
    simpa only [Nat.mul_comm] using h
  obtain ⟨L, hL, hLsmall, hDM⟩ := hcodegree D hD₁ hDpos
  have hvertices : H.finiteModel.vertexSet.card + p ≤ (4 * s) * D := by
    rw [H.finiteModel_vertex_card, Fintype.card_fin]
    have hfloor : n < s * (D + 1) := Nat.lt_mul_div_succ n hs
    have hscale := Nat.mul_le_mul_left s (show D + 1 ≤ 2 * D by omega)
    have hp' : p ≤ n := Nat.div_le_self _ _
    nlinarith only [hfloor, hscale, hp']
  have hbound : H.finiteModel.IsBounded R := by
    intro e
    simpa only [H.finiteModel_support_card] using hmax e
  have hden : s ≤ 16 * a * s := by nlinarith only [ha]
  have hd : d ≤ D := Nat.div_le_div_left hden hs
  have hdegree : ∀ v ∈ H.finiteModel.vertexSet, H.finiteModel.edgeDegree v ≤ d := by
    intro v _
    have h := H.finiteModel_edgeDegree_le_div hlinear (16 * a * s + 1)
      (by nlinarith only [ha, hs]) hmin v
    simp only [Fintype.card_fin, Nat.add_sub_cancel] at h
    exact h.trans (Nat.div_le_div_right (Nat.sub_le n 1))
  have hpair : ∀ u ∈ H.finiteModel.vertexSet, ∀ v ∈ H.finiteModel.vertexSet, u ≠ v →
      H.finiteModel.edgePairDegree u v ≤ L := by
    intro u _ v _ huv
    exact (H.finiteModel_edgePairDegree_le_one hlinear huv).trans hL
  have hroom : H.finiteModel.vertexSet.card * d / D + 2 * R +
      (2 * R) * ((2 * R) * D / L) < p := by
    rw [H.finiteModel_vertex_card, Fintype.card_fin]
    exact capacity_pool_room n s a R D L M hs ha rfl hDpos hDM hp
  have hpalette' : (1 + (1 : ℝ)) * D ≤ Fintype.card P := by
    norm_num
    exact_mod_cast hpalette
  obtain ⟨c, hcF, hcCover⟩ := hround (Fin n) H P H.finiteModel D L d p F
    hD₀ hL hLsmall hbound hvertices hd hdegree hpair hroom hF hpalette'
  refine ⟨H.edgeColoringOfFiniteModel c, hcF, ?_⟩
  intro x
  simpa only [H.finiteModel_covered_card, edgeColoringOfFiniteModel, p] using hcCover x

#print axioms eventually_bounded_rank_covered_lists

end Erdos19.SetHypergraph
