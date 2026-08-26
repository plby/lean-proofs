import ErdosProblems.Erdos19.FiniteModel
import ErdosProblems.Erdos19.ApproximateListColoring

/-! # Sparse-list coloring for bounded-rank linear hypergraphs -/

namespace Erdos19.SetHypergraph

open Erdos76 Erdos76.FiniteHypergraph

theorem eventually_bounded_rank_sparse_lists (R s : ℕ) (hR : 0 < R) (hs : 0 < s) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, s + 1 ≤ e.1.ncard) → (∀ e : H, e.1.ncard ≤ R) →
      ∀ (P : Type) [Fintype P] [DecidableEq P], ∀ F : H → Finset P,
        (∀ e, ((F e).card : ℝ) ≤ delta * ((n / s : ℕ) : ℝ)) →
        2 * (n / s) ≤ Fintype.card P →
        ∃ c : H.EdgeColoring P, ∀ e, c.color e ∉ F e := by
  classical
  obtain ⟨delta, hdelta, D₀, hround⟩ :=
    bounded_approximate_coloring_avoiding_sparse R (2 * s) hR 1 (by norm_num)
  obtain ⟨D₁, hD₁⟩ := exists_nat_gt (1 / delta)
  let Dmin := max D₀ (max D₁ 1)
  refine ⟨delta, hdelta, s * Dmin, ?_⟩
  intro n hn H hlinear hmin hmax P _ _ F hF hpalette
  let D := n / s
  have hDmin : Dmin ≤ D := by
    apply (Nat.le_div_iff_mul_le hs).mpr
    simpa only [Nat.mul_comm] using hn
  have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hDmin
  have hD₁le : D₁ ≤ D := ((le_max_left _ _).trans (le_max_right _ _)).trans hDmin
  have hDpos : 1 ≤ D := ((le_max_right _ _).trans (le_max_right _ _)).trans hDmin
  have hdeltaD : 1 < delta * (D : ℝ) := by
    have hratio : 1 / delta < (D : ℝ) := hD₁.trans_le (by exact_mod_cast hD₁le)
    have h := (div_lt_iff₀ hdelta).mp hratio
    nlinarith only [h]
  have hvertices : H.finiteModel.vertexSet.card ≤ (2 * s) * D := by
    rw [H.finiteModel_vertex_card, Fintype.card_fin]
    have hfloor : n < s * (D + 1) := Nat.lt_mul_div_succ n hs
    have hscale := Nat.mul_le_mul_left s (show D + 1 ≤ 2 * D by omega)
    nlinarith only [hfloor, hscale]
  have hbound : H.finiteModel.IsBounded R := by
    intro e
    simpa only [H.finiteModel_support_card] using hmax e
  have hdegree : ∀ v ∈ H.finiteModel.vertexSet, H.finiteModel.edgeDegree v ≤ D := by
    intro v _
    have h := H.finiteModel_edgeDegree_le_div hlinear (s + 1) (by omega) hmin v
    simp only [Fintype.card_fin, Nat.add_sub_cancel] at h
    exact h.trans (Nat.div_le_div_right (Nat.sub_le n 1))
  have hpair : ∀ u ∈ H.finiteModel.vertexSet, ∀ v ∈ H.finiteModel.vertexSet, u ≠ v →
      (H.finiteModel.edgePairDegree u v : ℝ) < delta * D := by
    intro u _ v _ huv
    have h : (H.finiteModel.edgePairDegree u v : ℝ) ≤ 1 := by
      exact_mod_cast H.finiteModel_edgePairDegree_le_one hlinear huv
    exact h.trans_lt hdeltaD
  have hpalette' : (1 + (1 : ℝ)) * D ≤ Fintype.card P := by
    norm_num
    exact_mod_cast hpalette
  obtain ⟨c, hc⟩ := hround (Fin n) H P H.finiteModel D F hD₀ hbound hvertices
    hdegree hpair hF hpalette'
  exact ⟨H.edgeColoringOfFiniteModel c, hc⟩

#print axioms eventually_bounded_rank_sparse_lists

end Erdos19.SetHypergraph
