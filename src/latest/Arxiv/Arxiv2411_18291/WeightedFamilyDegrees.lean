import Arxiv.Arxiv2411_18291.EdgeFamilyBoundedness
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Face degrees of families with fixed natural weights

Expanding each index into its weight many copies is a counting device.
It does not introduce additional random choices or assert independence.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype I] [DecidableEq V] {q r : ℕ}

def weightedFamilyDegree (E : I → Block V q) (w : I → ℕ) (S : Finset V) : ℕ :=
  ∑ i, if S ⊆ (E i).val then w i else 0

def IsWeightedFamilyBounded [Fintype V] (r : ℕ) (E : I → Block V q)
    (w : I → ℕ) (θ : ℝ) : Prop :=
  ∀ S : Block V r, (weightedFamilyDegree E w S.val : ℝ) < θ * Fintype.card V

abbrev WeightedIndices (w : I → ℕ) := Σ i : I, Fin (w i)

theorem weightedIndices_degree (E : I → Block V q) (w : I → ℕ) (S : Finset V) :
    familyDegree (fun i : WeightedIndices w => E i.1) S = weightedFamilyDegree E w S := by
  classical
  rw [familyDegree, card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  change (∑ _j : Fin (w i), if S ⊆ (E i).val then 1 else 0) = _
  by_cases hS : S ⊆ (E i).val <;> simp [hS]

theorem sum_weightedIndices (w : I → ℕ) (f : I → ℝ) :
    (∑ i : WeightedIndices w, f i.1) = ∑ i, (w i : ℝ) * f i := by
  rw [Fintype.sum_sigma]
  simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin]

theorem weightedFamilyDegree_mono (E : I → Block V q) {w w' : I → ℕ}
    (hw : ∀ i, w i ≤ w' i) (S : Finset V) :
    weightedFamilyDegree E w S ≤ weightedFamilyDegree E w' S := by
  apply sum_le_sum
  intro i _
  split_ifs
  · exact hw i
  · exact le_rfl

theorem weightedFamilyDegree_reindex {J : Type*} [Fintype J] (e : J ≃ I)
    (E : I → Block V q) (w : I → ℕ) (S : Finset V) :
    weightedFamilyDegree (fun j => E (e j)) (fun j => w (e j)) S =
      weightedFamilyDegree E w S :=
  e.sum_comp (fun i => if S ⊆ (E i).val then w i else 0)

theorem familyDegree_le_weighted (E : I → Block V q) (w : I → ℕ)
    (hw : ∀ i, 1 ≤ w i) (S : Finset V) :
    familyDegree E S ≤ weightedFamilyDegree E w S := by
  classical
  rw [familyDegree, card_eq_sum_ones, sum_filter]
  apply sum_le_sum
  intro i _
  split_ifs
  · exact hw i
  · exact le_rfl

variable [Fintype V]

theorem IsWeightedFamilyBounded.expanded {E : I → Block V (r + 1)} {w : I → ℕ} {θ : ℝ}
    (hE : IsWeightedFamilyBounded r E w θ) :
    IsEdgeFamilyBounded (fun i : WeightedIndices w => E i.1) θ := by
  intro S
  simpa only [weightedIndices_degree] using hE S

theorem IsWeightedFamilyBounded.unweighted {E : I → Block V (r + 1)}
    {w : I → ℕ} {θ : ℝ} (hE : IsWeightedFamilyBounded r E w θ) (hw : ∀ i, 1 ≤ w i) :
    IsEdgeFamilyBounded E θ := by
  intro S
  have hle : (familyDegree E S.val : ℝ) ≤ weightedFamilyDegree E w S.val := by
    exact_mod_cast familyDegree_le_weighted E w hw S.val
  exact hle.trans_lt (hE S)

end Arxiv2411_18291
