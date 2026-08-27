import Arxiv.Arxiv2411_18291.CliqueFamilyBoundedness
import Arxiv.Arxiv2411_18291.EdgeFamilyBoundedness

/-! # Lower degrees of bounded clique families

Retaining the factor q-r in the boundary degree avoids paying an extra
clique multiplicity when a whole input clique shares one decoder region.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {q r : ℕ}

omit [Fintype V] in
theorem familyDegree_subtype_eq (D : Finset (Block V q)) (S : Finset V) :
    familyDegree (fun Q : D => Q.val) S = (D.filter fun Q => S ⊆ Q.val).card := by
  classical
  apply card_bij (fun Q _ => Q.val)
  · intro Q hQ
    exact mem_filter.mpr ⟨Q.property, (mem_filter.mp hQ).2⟩
  · intro Q _ R _ h
    exact Subtype.ext h
  · intro Q hQ
    exact ⟨⟨Q, (mem_filter.mp hQ).1⟩,
      mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hQ).2⟩, rfl⟩

theorem familyDegree_le_sum_larger_faces (E : I → Block V q) (hrq : r ≤ q)
    (S : Finset V) (hS : S.card ≤ r) :
    familyDegree E S ≤
      ∑ T ∈ univ.filter (fun T : Block V r => S ⊆ T.val), familyDegree E T.val := by
  classical
  let faces := univ.filter fun T : Block V r => S ⊆ T.val
  have hsub : (univ.filter fun i => S ⊆ (E i).val) ⊆
      faces.biUnion (fun T => univ.filter fun i => T.val ⊆ (E i).val) := by
    intro i hi
    obtain ⟨T, hST, hTE, hT⟩ := exists_subsuperset_card_eq (mem_filter.mp hi).2 hS
      (by rw [(E i).property]; exact hrq)
    exact mem_biUnion.mpr ⟨⟨T, hT⟩, mem_filter.mpr ⟨mem_univ _, hST⟩,
      mem_filter.mpr ⟨mem_univ _, hTE⟩⟩
  exact (card_le_card hsub).trans card_biUnion_le

theorem familyDegree_le_of_face_bound (E : I → Block V q) (hrq : r ≤ q)
    {b : ℝ} (hb : 0 ≤ b)
    (hE : ∀ T : Block V r, (familyDegree E T.val : ℝ) ≤ b * Fintype.card V)
    (S : Finset V) (hS : S.card ≤ r) :
    (familyDegree E S : ℝ) ≤ b * (Fintype.card V : ℝ) ^ (r + 1 - S.card) := by
  have hc : (univ.filter fun T : Block V r => S ⊆ T.val).card =
      (Fintype.card V - S.card).choose (r - S.card) := by
    simpa only [subset_univ, and_true, card_univ] using
      card_blocks_between S univ (subset_univ _) hS
  have hp : (univ.filter fun T : Block V r => S ⊆ T.val).card ≤
      Fintype.card V ^ (r - S.card) := by
    rw [hc]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
  calc
    _ ≤ ∑ T ∈ univ.filter (fun T : Block V r => S ⊆ T.val),
        (familyDegree E T.val : ℝ) := by
      exact_mod_cast familyDegree_le_sum_larger_faces E hrq S hS
    _ ≤ ∑ _T ∈ univ.filter (fun T : Block V r => S ⊆ T.val), b * Fintype.card V :=
      sum_le_sum fun T _ => hE T
    _ = (univ.filter fun T : Block V r => S ⊆ T.val).card * (b * Fintype.card V) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card V : ℝ) ^ (r - S.card) * (b * Fintype.card V) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hp) (mul_nonneg hb (Nat.cast_nonneg _))
    _ = _ := by
      rw [show r + 1 - S.card = (r - S.card) + 1 by omega, pow_succ]
      ring

theorem IsCliqueFamilyBounded.clique_degree_le {D : Finset (Block V q)} {θ : ℝ}
    (hD : IsCliqueFamilyBounded r D θ) (hrq : r < q) (hθ : 0 ≤ θ)
    (S : Finset V) (hS : S.card ≤ r) :
    ((D.filter fun Q => S ⊆ Q.val).card : ℝ) ≤
      (θ / (q - r : ℕ)) * (Fintype.card V : ℝ) ^ (r + 1 - S.card) := by
  have hqr : (0 : ℝ) < (q - r : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hrq
  have hE : ∀ T : Block V r, (familyDegree (fun Q : D => Q.val) T.val : ℝ) ≤
      (θ / (q - r : ℕ)) * Fintype.card V := by
    intro T
    have h := hD T
    rw [degree_boundary _ T.val (by rw [T.property]; omega), degree_indicator,
      T.property, Nat.add_sub_cancel_left, Nat.choose_one_right] at h
    rw [familyDegree_subtype_eq]
    push_cast at h
    calc
      _ ≤ θ * Fintype.card V / (q - r : ℕ) :=
        (le_div_iff₀ hqr).mpr (by nlinarith only [h.le])
      _ = _ := by ring
  rw [← familyDegree_subtype_eq]
  exact familyDegree_le_of_face_bound _ hrq.le (div_nonneg hθ hqr.le) hE S hS

end Arxiv2411_18291
