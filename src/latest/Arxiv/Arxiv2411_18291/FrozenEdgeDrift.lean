import Arxiv.Arxiv2411_18291.ExcludedEdgeNeighborhood
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # The frozen edge-degree drift, with an explicit codegree error -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem frozenEdgeLoss_total_bounds (hqr : r < q) (H : Finset (Block V q)) (e : Block V r) :
    (∑ Q ∈ H, frozenEdgeLoss H e Q) ≤
        (∑ P ∈ H.filter (fun P => e.val ⊆ P.val),
          ∑ f ∈ (cliqueEdges r P).erase e, (H.filter fun Q => f.val ⊆ Q.val).card) ∧
      (∑ P ∈ H.filter (fun P => e.val ⊆ P.val),
          ∑ f ∈ (cliqueEdges r P).erase e, (H.filter fun Q => f.val ⊆ Q.val).card) ≤
        (∑ Q ∈ H, frozenEdgeLoss H e Q) + (H.filter fun P => e.val ⊆ P.val).card *
          (((q.choose r) ^ 2 + q.choose r) * (Fintype.card V) ^ (q - r - 1)) := by
  rw [sum_frozenEdgeLoss]
  constructor
  · apply sum_le_sum
    intro P hP
    exact (excludedEdge_neighborhood_bounds hqr H e P (mem_filter.mp hP).2).1
  · calc
      _ ≤ ∑ P ∈ H.filter (fun P => e.val ⊆ P.val),
          ((cliqueNeighborhood r (H.filter fun Q => ¬e.val ⊆ Q.val) P).card +
            ((q.choose r) ^ 2 + q.choose r) * (Fintype.card V) ^ (q - r - 1)) := by
        apply sum_le_sum
        intro P hP
        exact (excludedEdge_neighborhood_bounds hqr H e P (mem_filter.mp hP).2).2
      _ = _ := by rw [sum_add_distrib]; simp

theorem frozenEdgeLoss_average_bounds (hqr : r < q) (H : Finset (Block V q))
    (hH : H.Nonempty) (e : Block V r) :
    let A := ∑ P ∈ H.filter (fun P => e.val ⊆ P.val),
      ∑ f ∈ (cliqueEdges r P).erase e, ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ)
    let L := (∑ Q ∈ H, (frozenEdgeLoss H e Q : ℝ)) / H.card
    A / H.card - ((H.filter fun P => e.val ⊆ P.val).card : ℝ) / H.card *
        (((q.choose r : ℝ) ^ 2 + q.choose r) * (Fintype.card V : ℝ) ^ (q - r - 1)) ≤ L ∧
      L ≤ A / H.card := by
  obtain ⟨hlo, hhi⟩ := frozenEdgeLoss_total_bounds hqr H e
  have hcard : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  have hlo' : (∑ Q ∈ H, (frozenEdgeLoss H e Q : ℝ)) ≤
      ∑ P ∈ H.filter (fun P => e.val ⊆ P.val),
        ∑ f ∈ (cliqueEdges r P).erase e, ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ) := by
    exact_mod_cast hlo
  have hhi' : (∑ P ∈ H.filter (fun P => e.val ⊆ P.val),
      ∑ f ∈ (cliqueEdges r P).erase e, ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ)) ≤
        (∑ Q ∈ H, (frozenEdgeLoss H e Q : ℝ)) + (H.filter fun P => e.val ⊆ P.val).card *
          (((q.choose r : ℝ) ^ 2 + q.choose r) * (Fintype.card V : ℝ) ^ (q - r - 1)) := by
    exact_mod_cast hhi
  dsimp only
  constructor
  · apply sub_le_iff_le_add.mpr
    have h := div_le_div_of_nonneg_right hhi' hcard.le
    rw [add_div] at h
    simpa only [mul_div_right_comm] using h
  · exact div_le_div_of_nonneg_right hlo' hcard.le

end Arxiv2411_18291
