import Arxiv.Arxiv2411_18291.GraphBoundedness
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Bounded edge families with multiplicities

The prescribed root edges may repeat. Face degrees therefore count indices,
not just distinct edges. Boundedness at codimension one also bounds degrees
at every smaller vertex set and the number of family members with a large
intersection with a fixed target edge.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {r : ℕ}

def familyDegree (E : I → Block V r) (S : Finset V) : ℕ :=
  (univ.filter fun i => S ⊆ (E i).val).card

def IsEdgeFamilyBounded (E : I → Block V (r + 1)) (θ : ℝ) : Prop :=
  ∀ S : Block V r, (familyDegree E S.val : ℝ) < θ * Fintype.card V

theorem familyDegree_le_sum_faceDegrees (E : I → Block V (r + 1))
    (S : Finset V) (hS : S.card ≤ r) :
    familyDegree E S ≤
      ∑ T ∈ univ.filter (fun T : Block V r => S ⊆ T.val), familyDegree E T.val := by
  classical
  let faces := univ.filter fun T : Block V r => S ⊆ T.val
  have hsub : (univ.filter fun i => S ⊆ (E i).val) ⊆
      faces.biUnion (fun T => univ.filter fun i => T.val ⊆ (E i).val) := by
    intro i hi
    obtain ⟨T, hST, hTE, hT⟩ := exists_subsuperset_card_eq (mem_filter.mp hi).2 hS
      (by rw [(E i).property]; omega)
    exact mem_biUnion.mpr ⟨⟨T, hT⟩, mem_filter.mpr ⟨mem_univ _, hST⟩,
      mem_filter.mpr ⟨mem_univ _, hTE⟩⟩
  exact (card_le_card hsub).trans card_biUnion_le

theorem IsEdgeFamilyBounded.degree_le {E : I → Block V (r + 1)} {θ : ℝ}
    (hE : IsEdgeFamilyBounded E θ) (hθ : 0 ≤ θ) (S : Finset V) (hS : S.card ≤ r) :
    (familyDegree E S : ℝ) ≤ θ * (Fintype.card V : ℝ) ^ (r + 1 - S.card) := by
  have hc : (univ.filter fun T : Block V r => S ⊆ T.val).card =
      (Fintype.card V - S.card).choose (r - S.card) := by
    simpa only [subset_univ, and_true, card_univ] using
      card_blocks_between S univ (subset_univ _) hS
  have hp : (univ.filter fun T : Block V r => S ⊆ T.val).card ≤
      Fintype.card V ^ (r - S.card) := by
    rw [hc]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
  calc
    _ ≤ ∑ T ∈ univ.filter (fun T : Block V r => S ⊆ T.val), (familyDegree E T.val : ℝ) := by
      exact_mod_cast familyDegree_le_sum_faceDegrees E S hS
    _ ≤ ∑ _T ∈ univ.filter (fun T : Block V r => S ⊆ T.val), θ * Fintype.card V :=
      sum_le_sum fun T _ => (hE T).le
    _ = (univ.filter fun T : Block V r => S ⊆ T.val).card * (θ * Fintype.card V) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card V : ℝ) ^ (r - S.card) * (θ * Fintype.card V) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hp) (mul_nonneg hθ (Nat.cast_nonneg _))
    _ = _ := by
      rw [show r + 1 - S.card = (r - S.card) + 1 by omega, pow_succ]
      ring

theorem IsEdgeFamilyBounded.card_le {E : I → Block V (r + 1)} {θ : ℝ}
    (hE : IsEdgeFamilyBounded E θ) (hθ : 0 ≤ θ) :
    (Fintype.card I : ℝ) ≤ θ * (Fintype.card V : ℝ) ^ (r + 1) := by
  simpa [familyDegree] using hE.degree_le hθ ∅ (by simp)

def familyOverlapIndices (E : I → Block V (r + 1)) (g : Block V (r + 1))
    (j : ℕ) : Finset I := univ.filter fun i => j ≤ (g.val ∩ (E i).val).card

theorem IsEdgeFamilyBounded.overlap_card_le {E : I → Block V (r + 1)} {θ : ℝ}
    (hE : IsEdgeFamilyBounded E θ) (hθ : 0 ≤ θ) (g : Block V (r + 1))
    (j : ℕ) (hj : j ≤ r) :
    ((familyOverlapIndices E g j).card : ℝ) ≤
      (r + 1).choose j * θ * (Fintype.card V : ℝ) ^ (r + 1 - j) := by
  classical
  have hsub : familyOverlapIndices E g j ⊆
      (g.val.powersetCard j).biUnion (fun S => univ.filter fun i => S ⊆ (E i).val) := by
    intro i hi
    obtain ⟨S, hS, hc⟩ := exists_subset_card_eq (mem_filter.mp hi).2
    exact mem_biUnion.mpr ⟨S, mem_powersetCard.mpr ⟨hS.trans inter_subset_left, hc⟩,
      mem_filter.mpr ⟨mem_univ _, hS.trans inter_subset_right⟩⟩
  calc
    _ ≤ ∑ S ∈ g.val.powersetCard j, (familyDegree E S : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _S ∈ g.val.powersetCard j,
        θ * (Fintype.card V : ℝ) ^ (r + 1 - j) := by
      apply sum_le_sum
      intro S hS
      have hc := (mem_powersetCard.mp hS).2
      simpa only [hc] using hE.degree_le hθ S (by omega)
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, card_powersetCard, g.property]
      ring

end Arxiv2411_18291
