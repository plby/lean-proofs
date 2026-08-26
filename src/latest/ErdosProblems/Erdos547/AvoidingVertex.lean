import ErdosProblems.Erdos547.WeightedHost

/-!
# Selecting a vertex that avoids a small region and has unused anchor capacity
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

open scoped Classical in
def slackRegion (w : EdgeWeights G) (c : V) (σ : SkewMatching G γ) (L C : Finset V) :
    Finset V := Finset.univ.filter (fun u ↦ u ∉ L ∪ C ∧ σ.outLoad u < w.weight c u)

theorem degreeOn_slack_region_lower (w : EdgeWeights G) (c : V)
    (σ : SkewMatching G γ) (L C : Finset V)
    (hC : ∀ u ∈ C, w.weight c u = σ.outLoad u) :
    w.degree c - (L.card : ℝ) - σ.total / (1 + γ) +
      (∑ u ∈ slackRegion w c σ L C, σ.outLoad u) ≤
        w.degreeOn (slackRegion w c σ L C) c := by
  classical
  let H := slackRegion w c σ L C
  have hp (u : V) : w.weight c u ≤
      (if u ∈ H then w.weight c u - σ.outLoad u else 0) +
      (if u ∈ L then 1 else 0) + σ.outLoad u := by
    by_cases huH : u ∈ H
    · rw [if_pos huH]
      split_ifs <;> linarith
    · rw [if_neg huH]
      by_cases huL : u ∈ L
      · rw [if_pos huL]
        linarith [w.at_most_one c u, σ.outLoad_nonneg u]
      · rw [if_neg huL, zero_add, zero_add]
        by_cases huC : u ∈ C
        · exact (hC u huC).le
        · exact le_of_not_gt fun hs ↦ huH (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (fun hh ↦ (Finset.mem_union.mp hh).elim huL huC), hs⟩)
  have hs := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) ↦ hp u)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_mem_eq, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_one, σ.sum_outLoad] at hs
  change w.degree c ≤ w.degreeOn H c - (∑ u ∈ H, σ.outLoad u) +
    (L.card : ℝ) + σ.total / (1 + γ) at hs
  linarith

theorem exists_maximal_avoiding_vertex (w : EdgeWeights G) (c : V)
    (σ : SkewMatching G γ) (L C : Finset V)
    (hC : ∀ u ∈ C, w.weight c u = σ.outLoad u)
    (hdegree : (L.card : ℝ) + σ.total / (1 + γ) < w.degree c) :
    ∃ d, d ∉ L ∪ C ∧ σ.outLoad d < w.weight c d ∧
      ∀ x, x ∉ L ∪ C → σ.outLoad x < w.weight c x → w.degreeOn C x ≤ w.degreeOn C d := by
  classical
  let Y := Finset.univ.filter (fun u ↦ u ∉ L ∪ C ∧ σ.outLoad u < w.weight c u)
  have hY : Y.Nonempty := by
    by_contra hn
    have hbound (u : V) (hu : u ∉ L) : w.weight c u ≤ σ.outLoad u := by
      by_cases huC : u ∈ C
      · exact (hC u huC).le
      · apply le_of_not_gt
        intro hp
        exact hn ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          not_or.mpr ⟨hu, huC⟩ ∘ Finset.mem_union.mp, hp⟩⟩
    have hL : w.degreeOn L c ≤ (L.card : ℝ) := by
      calc
        _ ≤ ∑ _u ∈ L, (1 : ℝ) := Finset.sum_le_sum fun u _ ↦ w.at_most_one c u
        _ = _ := by simp
    have hLc : w.degreeOn Lᶜ c ≤ σ.total / (1 + γ) := by
      calc
        _ ≤ ∑ u ∈ Lᶜ, σ.outLoad u := Finset.sum_le_sum fun u hu ↦ hbound u (Finset.mem_compl.mp hu)
        _ ≤ ∑ u, σ.outLoad u := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (fun u _ _ ↦ σ.outLoad_nonneg u)
        _ = _ := σ.sum_outLoad
    have he : w.degreeOn L c + w.degreeOn Lᶜ c = w.degree c :=
      Finset.sum_add_sum_compl L (w.weight c)
    linarith
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image Y (fun x ↦ w.degreeOn C x) hY
  refine ⟨d, (Finset.mem_filter.mp hd).2.1, (Finset.mem_filter.mp hd).2.2, ?_⟩
  intro x hx hslack
  exact hmax x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hslack⟩)

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_maximal_avoiding_vertex
