import ErdosProblems.Erdos547.GreedyAnchored
import ErdosProblems.Erdos547.StructuralCover
import ErdosProblems.Erdos547.BudgetIdentities

/-!
# Completing an anchored pair beside a fully occupied isolated tail
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem finish_from_isolated_tail (w : EdgeWeights G) {c d : V} (hcd : G.Adj c d)
    (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 ≤ b₂)
    (β : SkewMatching G (b₂ / b₁)) (hfit : β.Fits w d) (htotal : β.total = b₁ + b₂)
    (Z Q : Finset V) (hdis : Disjoint Z Q)
    (hhead : ∀ u ∉ Z, β.outLoad u = 0)
    (hQ : (∑ u ∈ Q, β.load u) = (Q.card : ℝ))
    (hQlarge : (a₁ + a₂ + b₁ + b₂) / 2 ≤ (Q.card : ℝ))
    (hno : ∀ y ∈ Q, ∀ x, G.Adj x y → x ∈ Z)
    (hZ : w.degreeOn Z c ≤ b₁)
    (hhigh : a₁ + a₂ + b₁ + b₂ ≤ w.degree c)
    (hdegree : ∀ x, (a₁ + a₂ + b₁ + b₂) / 2 ≤ w.degree x) :
    HasAnchoredTotals w (a₂ / a₁) (b₂ / b₁) (a₁ + a₂) (b₁ + b₂) := by
  classical
  let A := (Z ∪ Q)ᶜ
  let B := Qᶜ
  let α₀ := SkewMatching.zero G (a₂ / a₁) (div_nonneg ha₂.le ha₁.le)
  have hz (u : V) : α₀.load u = 0 := by
    simp only [α₀, SkewMatching.load, SkewMatching.outLoad, SkewMatching.inLoad,
      SkewMatching.zero, Finset.sum_const_zero, mul_zero, zero_div, add_zero]
  have hp : AnchoredPair α₀ β w c d :=
    (AnchoredPair.single_left β (a₂ / a₁) (div_nonneg ha₂.le ha₁.le) w hcd.symm hfit).swap
  have hAQ : Disjoint A Q := Finset.disjoint_left.mpr fun _ hu hv ↦
    Finset.mem_compl.mp hu (Finset.mem_union_right _ hv)
  have hnA {u : V} (hu : u ∈ A) : u ∉ Z := fun hv ↦
    Finset.mem_compl.mp hu (Finset.mem_union_left _ hv)
  have hnQ {u : V} (hu : u ∈ Q) : u ∉ Z := fun hv ↦ Finset.disjoint_left.mp hdis hv hu
  have hparts := skew_parts_of_sum b₁ b₂ hb₁ hb₂
  have hin : (∑ u, β.inLoad u) = b₂ := by
    rw [β.sum_inLoad, htotal, mul_div_assoc, hparts.2]
  have hloadAQ : (∑ u ∈ A, β.load u) + (Q.card : ℝ) ≤ b₂ := by
    rw [← hQ]
    calc
      _ = (∑ u ∈ A, β.inLoad u) + ∑ u ∈ Q, β.inLoad u := by
        congr 1
        · exact Finset.sum_congr rfl fun u hu ↦ by
            rw [SkewMatching.load, hhead u (hnA hu), zero_add]
        · exact Finset.sum_congr rfl fun u hu ↦ by
            rw [SkewMatching.load, hhead u (hnQ hu), zero_add]
      _ = ∑ u ∈ A ∪ Q, β.inLoad u := (Finset.sum_union hAQ).symm
      _ ≤ ∑ u, β.inLoad u := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun u _ _ ↦ β.inLoad_nonneg u)
      _ = _ := hin
  have hdegreeA : w.degree c ≤ w.degreeOn A c + w.degreeOn Z c + (Q.card : ℝ) := by
    have hsplit : w.degreeOn A c + (w.degreeOn Z c + w.degreeOn Q c) = w.degree c := by
      rw [← show w.degreeOn (Z ∪ Q) c = w.degreeOn Z c + w.degreeOn Q c from
        Finset.sum_union hdis]
      exact Finset.sum_compl_add_sum (Z ∪ Q) (w.weight c)
    have hbound : w.degreeOn Q c ≤ (Q.card : ℝ) := by
      calc
        _ ≤ ∑ _u ∈ Q, (1 : ℝ) := Finset.sum_le_sum fun u _ ↦ w.at_most_one c u
        _ = _ := by simp
    linarith
  have hA : a₁ + (∑ u ∈ A, (α₀.load u + β.load u)) ≤ w.degreeOn A c := by
    simp only [hz, zero_add]
    linarith
  have hloadB : (∑ u ∈ B, β.load u) + (Q.card : ℝ) = b₁ + b₂ := by
    rw [← hQ]
    exact (Finset.sum_compl_add_sum Q β.load).trans (β.sum_load.trans htotal)
  have hB : ∀ x ∈ A, (1 + a₂ / a₁) * a₁ + (∑ u ∈ B, (α₀.load u + β.load u)) ≤
      ((B.filter (G.Adj x)).card : ℝ) := by
    intro x hx
    have hneigh : ∀ y, G.Adj x y → y ∈ B := by
      intro y hy
      exact Finset.mem_compl.mpr fun hyQ ↦ hnA hx (hno y hyQ x hy)
    have hd : w.degree x ≤ ((B.filter (G.Adj x)).card : ℝ) :=
      w.degree_le_card_of_neighbours_subset x _ fun y hy ↦ Finset.mem_filter.mpr ⟨hneigh y hy, hy⟩
    have he : (1 + a₂ / a₁) * a₁ = a₁ + a₂ := by field_simp
    simp only [hz, zero_add, he]
    linarith [hdegree x]
  obtain ⟨α, hs, hpair, ht, _⟩ := hp.second_greedy A B a₁ ha₁.le (div_pos ha₂ ha₁) hA hB
  refine ⟨c, d, α₀.add α hs, β, hpair, ?_, htotal⟩
  rw [SkewMatching.add_total, ht]
  have hzero : α₀.total = 0 := by
    simp only [α₀, SkewMatching.total, SkewMatching.zero, Finset.sum_const_zero]
  rw [hzero, zero_add]
  field_simp

end Erdos547.DPRS

#print axioms Erdos547.DPRS.finish_from_isolated_tail
