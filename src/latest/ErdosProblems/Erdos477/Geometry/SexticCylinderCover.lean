/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Bounded-degree plane cylinders covering almost all nonnegative-first-coordinate sextic points.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SexticPlaneClasses
import ErdosProblems.Erdos477.Geometry.RefinementTree
import ErdosProblems.Erdos477.Geometry.PositiveProjection

namespace Erdos477.Geometry

open Counting
open scoped BigOperators

lemma refinement_edge_cost (p L Q : ℝ) (hp : p ≠ 0) (t : ℕ) :
    (3 * p ^ 3 * (p ^ (t + 1)) ^ 2) * (L * Q / p ^ t) *
      (L * Q / p ^ (t + 1)) = 3 * p ^ 4 * L ^ 2 * Q ^ 2 := by
  rw [pow_succ]
  field_simp
  ring

lemma square_rpow_forty_one (B : ℝ) (hB : 0 ≤ B) :
    (B ^ ((41 : ℝ) / 100)) ^ 2 = B ^ ((82 : ℝ) / 100) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
  norm_num

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Except for `O_c(B^(82/100) log B)` points, the sextic points with
nonnegative first coordinate lie in `O_c(B^(41/100))` plane cylinders of
bounded degree. The remaining integral-curve bound is not part of this theorem. -/
theorem exists_sextic_cylinder_cover (c : ℤ) (hc : c ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ B : ℝ, 1 ≤ B →
      ∀ S : Finset (Fin 3 → ℤ), S ⊆ sexticBox c B → (∀ z ∈ S, 0 ≤ z 0) →
      ∃ C : Finset (MvPolynomial (Fin 2) K), ∃ E : Finset (Fin 3 → ℤ),
        (∀ F ∈ C, Irreducible F ∧ F.totalDegree ≤ N) ∧
        (C.card : ℝ) ≤ M * B ^ ((41 : ℝ) / 100) ∧ E ⊆ S ∧
        (∀ z ∈ S, z ∈ E ∨ ∃ F ∈ C, MvPolynomial.eval ![(z 1 : K), (z 2 : K)] F = 0) ∧
        (E.card : ℝ) ≤ M * B ^ ((82 : ℝ) / 100) * Real.log B := by
  classical
  obtain ⟨p, hp, L, hL, hclasses⟩ := exists_sextic_plane_classes (K := K) c hc
  let A : ℝ := 3 * (p : ℝ) ^ 4 * L ^ 2
  let M : ℝ := max L (A * ((41 : ℝ) / 100) / Real.log p)
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hLM : L ≤ M := le_max_left _ _
  have hAM : A * ((41 : ℝ) / 100) / Real.log p ≤ M := le_max_right _ _
  refine ⟨M, hL.trans_le hLM, ⌈L * p⌉₊, ?_⟩
  intro B hB S hS hnonneg
  have hB0 : 0 < B := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  let Q : ℝ := B ^ ((41 : ℝ) / 100)
  have hQ : 0 < Q := Real.rpow_pos_of_pos hB0 _
  obtain ⟨r, hdepth, hlast, hcount, P, hP0, hPdeg, hPzero⟩ := hclasses B hB
  let d : ℕ → ℝ := fun t => L * Q / (p : ℝ) ^ t
  have hd (t : ℕ) : 0 ≤ d t := le_of_lt (by dsimp only [d]; positivity)
  obtain ⟨C, E, hC, hCcard, hES, hcover, hE⟩ := exists_pruned_plane_cover S
    (integerPlaneProjection (K := K))
    (integerPlaneProjection_injOn c S (fun z hz =>
      ⟨hnonneg z hz, ((mem_sexticBox c B z).mp (hS hz)).1⟩))
    r (residueCode p) (fun t => residueCode p t) 0 (fun z _ => residueCode_zero p z)
    (fun t _ z _ => (residueCode_refines p t z).symm) P (hP0 0 0) d
    (fun t _ => hd t) (fun t ht z hz =>
      ⟨hP0 t _, hPdeg t ht _, hPzero t ht z (hS hz)⟩)
  refine ⟨C, E, ?_, ?_, hES, hcover, ?_⟩
  · intro F hF
    have hdeg := (hC F hF).2.2
    have hceil : (F.totalDegree : ℝ) ≤ ⌈L * p⌉₊ :=
      (hdeg.trans hlast.le).trans (Nat.le_ceil _)
    exact ⟨(hC F hF).1, Nat.cast_le.mp hceil⟩
  · calc
      (C.card : ℝ) ≤ (P 0 0).totalDegree := Nat.cast_le.mpr hCcard
      _ ≤ L * Q := by simpa using hPdeg 0 (Nat.zero_le r) 0
      _ ≤ M * Q := mul_le_mul_of_nonneg_right hLM hQ.le
  · have heach (t : ℕ) (ht : t ∈ Finset.range r) :
        (((S.image (residueCode p (t + 1))).card : ℝ) * d t * d (t + 1)) ≤ A * Q ^ 2 := by
      have hct := (Finset.card_le_card (Finset.image_subset_image hS)).trans
        (hcount (t + 1) (Finset.mem_range.mp ht))
      have hct' : ((S.image (residueCode p (t + 1))).card : ℝ) ≤
          3 * (p : ℝ) ^ 3 * ((p : ℝ) ^ (t + 1)) ^ 2 := by exact_mod_cast hct
      calc
        _ ≤ (3 * (p : ℝ) ^ 3 * ((p : ℝ) ^ (t + 1)) ^ 2) * d t * d (t + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hct' (hd t)) (hd (t + 1))
        _ = _ := refinement_edge_cost p L Q hp0.ne' t
    calc
      (E.card : ℝ) ≤ ∑ t ∈ Finset.range r,
          ((S.image (residueCode p (t + 1))).card : ℝ) * d t * d (t + 1) := hE
      _ ≤ ∑ _t ∈ Finset.range r, A * Q ^ 2 := Finset.sum_le_sum heach
      _ = (r : ℝ) * (A * Q ^ 2) := by simp
      _ ≤ ((41 : ℝ) / 100 * Real.log B / Real.log p) * (A * Q ^ 2) :=
        mul_le_mul_of_nonneg_right hdepth (mul_nonneg hA (sq_nonneg Q))
      _ = (A * ((41 : ℝ) / 100) / Real.log p) * Q ^ 2 * Real.log B := by ring
      _ ≤ M * Q ^ 2 * Real.log B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAM (sq_nonneg Q)) hlogB
      _ = _ := by rw [show Q ^ 2 = B ^ ((82 : ℝ) / 100) from square_rpow_forty_one B hB0.le]

#print axioms exists_sextic_cylinder_cover
-- 'Erdos477.Geometry.exists_sextic_cylinder_cover' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
