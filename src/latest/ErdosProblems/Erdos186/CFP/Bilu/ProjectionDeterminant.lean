/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The determinant of a projection between subspaces

This is the Euclidean linear-algebra estimate used as Lemma 6.9 in
Bilu's proof of Freiman's theorem.  If `W` is a hyperplane, `w` is a
nonzero normal to `W`, and `l` is a nonzero vector orthogonal to `L`,
then orthogonal projection from `L` to `W` decreases volume by at most
the cosine of the angle between `w` and `l`.
-/

namespace Erdos186.CFP.Bilu

open Module Submodule
open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Orthogonal projection to `W`, restricted to vectors in `L`. -/
noncomputable def projectionRestrict (W L : Submodule ℝ E) : L →ₗ[ℝ] W :=
  W.orthogonalProjectionOnto.toLinearMap.comp L.subtype

@[simp]
theorem projectionRestrict_apply (W L : Submodule ℝ E) (x : L) :
    projectionRestrict W L x = W.orthogonalProjectionOnto (x : E) :=
  rfl

private theorem orthogonal_eq_span_of_codim_one
    (W : Submodule ℝ E) (w : E)
    (hcodim : finrank ℝ W + 1 = finrank ℝ E)
    (hw : w ∈ Wᗮ) (hw0 : w ≠ 0) :
    Wᗮ = ℝ ∙ w := by
  exact eq_span_singleton_of_mem_of_finrank_eq_one
    (Submodule.finrank_add_finrank_orthogonal' hcodim) hw hw0

private theorem starProjection_eq_sub_normalProjection
    (W : Submodule ℝ E) (w x : E)
    (hcodim : finrank ℝ W + 1 = finrank ℝ E)
    (hw : w ∈ Wᗮ) (hw0 : w ≠ 0) :
    W.starProjection x = x - (inner ℝ w x / ‖w‖ ^ 2) • w := by
  have hsum := congrArg (fun f : E →L[ℝ] E ↦ f x)
    (Submodule.id_eq_sum_starProjection_self_orthogonalComplement (K := W))
  have hfirst : W.starProjection x = x - Wᗮ.starProjection x := by
    apply (eq_sub_iff_add_eq).2
    simpa using hsum.symm
  have horth := orthogonal_eq_span_of_codim_one W w hcodim hw hw0
  have hproj : Wᗮ.starProjection x = (inner ℝ w x / ‖w‖ ^ 2) • w := by
    have hs := Submodule.starProjection_singleton ℝ (v := w) x
    simpa only [horth, RCLike.ofReal_real_eq_id, id_eq] using hs
  rw [hfirst, hproj]

private theorem inner_starProjection_eq_sub
    (W : Submodule ℝ E) (w x y : E)
    (hcodim : finrank ℝ W + 1 = finrank ℝ E)
    (hw : w ∈ Wᗮ) (hw0 : w ≠ 0) :
    inner ℝ (W.starProjection x) (W.starProjection y) =
      inner ℝ x y - inner ℝ w x * inner ℝ w y / ‖w‖ ^ 2 := by
  rw [starProjection_eq_sub_normalProjection W w x hcodim hw hw0,
    starProjection_eq_sub_normalProjection W w y hcodim hw hw0]
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  simp only [inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, real_inner_comm x w, real_inner_self_eq_norm_sq,
    starRingEnd_apply]
  field_simp
  ring

private theorem normDet_projectionRestrict_sq
    (W L : Submodule ℝ E) (w : E)
    (hcodim : finrank ℝ W + 1 = finrank ℝ E)
    (hw : w ∈ Wᗮ) (hw0 : w ≠ 0) :
    (projectionRestrict W L).normDet ^ 2 =
      1 - ‖L.orthogonalProjectionOnto w‖ ^ 2 / ‖w‖ ^ 2 := by
  let b : OrthonormalBasis (Fin (finrank ℝ L)) ℝ L :=
    stdOrthonormalBasis ℝ L
  let a : Fin (finrank ℝ L) → ℝ := fun i ↦
    inner ℝ w (b i : E) / ‖w‖
  let A : Matrix (Fin (finrank ℝ L)) Unit ℝ := Matrix.replicateCol Unit a
  let B : Matrix Unit (Fin (finrank ℝ L)) ℝ := Matrix.replicateRow Unit a
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hb (i j : Fin (finrank ℝ L)) :
      inner ℝ (b i) (b j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal i j
  have hbE (i j : Fin (finrank ℝ L)) :
      inner ℝ (b i : E) (b j : E) = if i = j then 1 else 0 := by
    simpa using hb i j
  have hgram :
      Matrix.gram ℝ (fun i ↦ projectionRestrict W L (b i)) = 1 - A * B := by
    ext i j
    rw [Matrix.gram_apply]
    change inner ℝ (W.starProjection (b i : E)) (W.starProjection (b j : E)) = _
    rw [inner_starProjection_eq_sub W w (b i : E) (b j : E) hcodim hw hw0,
      hbE i j]
    have hAB : (A * B) i j = a i * a j := by
      simp [A, B, Matrix.mul_apply]
    rw [Matrix.sub_apply, Matrix.one_apply, hAB]
    simp only [a]
    split_ifs <;> field_simp
  have hdet : (Matrix.gram ℝ (fun i ↦ projectionRestrict W L (b i))).det =
      1 - ∑ i, a i ^ 2 := by
    rw [hgram, Matrix.det_one_sub_mul_comm A B]
    rw [Matrix.det_unique]
    change 1 - (B * A) default default = 1 - ∑ i, a i ^ 2
    have hBA : (B * A) default default = ∑ i, a i ^ 2 := by
      simp [B, A, Matrix.replicateRow_mul_replicateCol_apply, dotProduct, pow_two]
    rw [hBA]
  have hsum : ∑ i, a i ^ 2 = ‖L.orthogonalProjectionOnto w‖ ^ 2 / ‖w‖ ^ 2 := by
    rw [← b.sum_sq_inner_left (L.orthogonalProjectionOnto w)]
    simp only [a]
    have hinner (i : Fin (finrank ℝ L)) :
        inner ℝ (L.orthogonalProjectionOnto w) (b i) = inner ℝ w (b i : E) :=
      by simpa [real_inner_comm] using
        L.inner_orthogonalProjectionOnto_eq_of_mem_left (b i) w
    simp_rw [hinner]
    simp_rw [div_pow]
    rw [Finset.sum_div]
  have hsquare := (projectionRestrict W L).normDet_sq_eq_det_gram b
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hsquare
  rw [hsquare, hdet, hsum]

private theorem inner_sq_le_projection_defect_mul
    (L : Submodule ℝ E) (w l : E) (hl : l ∈ Lᗮ) :
    inner ℝ w l ^ 2 ≤
      (‖w‖ ^ 2 - ‖L.orthogonalProjectionOnto w‖ ^ 2) * ‖l‖ ^ 2 := by
  let r : E := w - L.starProjection w
  have hproj_inner : inner ℝ (L.starProjection w) l = 0 :=
    Submodule.inner_right_of_mem_orthogonal (L.starProjection_apply_mem w) hl
  have hinner : inner ℝ r l = inner ℝ w l := by
    simp [r, inner_sub_left, hproj_inner]
  have hcs : |inner ℝ r l| ≤ ‖r‖ * ‖l‖ := abs_real_inner_le_norm r l
  have hsq : |inner ℝ r l| ^ 2 ≤ (‖r‖ * ‖l‖) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hcs
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection w L
  rw [L.starProjection_orthogonal_val] at hpyth
  have hnorm : ‖L.orthogonalProjectionOnto w‖ = ‖L.starProjection w‖ := rfl
  have hr_sq : ‖r‖ ^ 2 = ‖w‖ ^ 2 - ‖L.orthogonalProjectionOnto w‖ ^ 2 := by
    change ‖w - L.starProjection w‖ ^ 2 =
      ‖w‖ ^ 2 - ‖L.orthogonalProjectionOnto w‖ ^ 2
    rw [hnorm]
    nlinarith
  rw [sq_abs, hinner, mul_pow, hr_sq] at hsq
  exact hsq

/-- **Bilu's projection-determinant lemma.**  Let `W` be a hyperplane,
let `w` be a nonzero normal to it, and let `l` be a nonzero vector
orthogonal to `L`.  The volume factor of orthogonal projection from
`L` to `W` is at least the absolute cosine between `w` and `l`. -/
theorem normDet_projectionRestrict_lower_bound
    (W L : Submodule ℝ E) (w l : E)
    (hcodim : finrank ℝ W + 1 = finrank ℝ E)
    (hw : w ∈ Wᗮ) (hw0 : w ≠ 0)
    (hl : l ∈ Lᗮ) (hl0 : l ≠ 0) :
    |inner ℝ w l| / (‖w‖ * ‖l‖) ≤ (projectionRestrict W L).normDet := by
  have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hnl : ‖l‖ ≠ 0 := norm_ne_zero_iff.mpr hl0
  have hnw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hnl_pos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
  have hdet := normDet_projectionRestrict_sq W L w hcodim hw hw0
  have hdet_mul :
      (projectionRestrict W L).normDet ^ 2 * ‖w‖ ^ 2 =
        ‖w‖ ^ 2 - ‖L.orthogonalProjectionOnto w‖ ^ 2 := by
    rw [hdet]
    field_simp
  have hinner := inner_sq_le_projection_defect_mul L w l hl
  have hden_pos : 0 < (‖w‖ * ‖l‖) ^ 2 := sq_pos_of_pos (mul_pos hnw_pos hnl_pos)
  have hsq :
      (|inner ℝ w l| / (‖w‖ * ‖l‖)) ^ 2 ≤
        (projectionRestrict W L).normDet ^ 2 := by
    rw [div_pow, sq_abs]
    apply (div_le_iff₀ hden_pos).2
    calc
      inner ℝ w l ^ 2 ≤
          (‖w‖ ^ 2 - ‖L.orthogonalProjectionOnto w‖ ^ 2) * ‖l‖ ^ 2 := hinner
      _ = (projectionRestrict W L).normDet ^ 2 * (‖w‖ * ‖l‖) ^ 2 := by
        rw [← hdet_mul]
        ring
  exact (sq_le_sq₀
    (div_nonneg (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (projectionRestrict W L).normDet_nonneg).1 hsq

end Erdos186.CFP.Bilu

#print axioms Erdos186.CFP.Bilu.normDet_projectionRestrict_lower_bound
