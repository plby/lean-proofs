/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.ProjectionDeterminant
import ErdosProblems.Erdos186.CFP.Bilu.SubspaceLattice

/-!
# The projection/covolume bridge in Bilu's Section 8

This file combines the two arithmetic-geometric inputs occurring next to
one another in Bilu's proof.  `ProjectionDeterminant.lean` gives the cosine
lower bound for the determinant of an orthogonal projection (Lemma 6.9),
while `SubspaceLattice.lean` supplies a short integral normal vector to a
rational subspace (Lemma 6.10).

The coordinate norm estimate below records the dimension factor explicitly.
The final theorem is deliberately division-free, so it remains useful in
degenerate ambient dimension and does not hide positivity side conditions.
-/

namespace Erdos186.CFP.Bilu.ProjectionCovolume

open Module Submodule
open scoped BigOperators RealInnerProductSpace
open SubspaceLattice
open MeasureTheory

variable {n r : ℕ}

/-- A vector whose `n` real coordinates are bounded by `D` has Euclidean
norm at most `sqrt n * D`. -/
theorem norm_integralReal_le_sqrt_mul
    (x : Fin n → ℤ) {D : ℝ} (hD : 0 ≤ D)
    (hx : ∀ j, ((|x j| : ℤ) : ℝ) ≤ D) :
    ‖integralReal x‖ ≤ Real.sqrt n * D := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hD)).1
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ j, (integralReal x j) ^ 2 ≤ ∑ _j : Fin n, D ^ 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      have habs : |(x j : ℝ)| ≤ D := by
        simpa using hx j
      simpa [integralReal_apply, sq_abs] using
        (sq_le_sq₀ (abs_nonneg (x j : ℝ)) hD).2 habs
    _ = (n : ℝ) * D ^ 2 := by simp
    _ = (Real.sqrt n * D) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]

/-- The Euclidean inner product of two integral vectors is the real cast of
their integral dot product. -/
theorem inner_integralReal_eq_int_sum (u x : Fin n → ℤ) :
    ⟪integralReal u, integralReal x⟫ =
      ((∑ j, u j * x j : ℤ) : ℝ) := by
  simp [PiLp.inner_apply, integralReal_apply, mul_comm]

/-- A nonzero inner product of integral vectors has absolute value at least
one. -/
theorem one_le_abs_inner_integralReal (u x : Fin n → ℤ)
    (hinner : ⟪integralReal u, integralReal x⟫ ≠ 0) :
    (1 : ℝ) ≤ |⟪integralReal u, integralReal x⟫| := by
  rw [inner_integralReal_eq_int_sum]
  exact_mod_cast Int.one_le_abs (by
    intro h
    apply hinner
    rw [inner_integralReal_eq_int_sum, h]
    simp)

/-- In codimension one, every nonzero normal detects every vector outside
the subspace.  This is the linear-algebraic transversality used after
Bilu's short-normal lemma. -/
theorem inner_ne_zero_of_mem_orthogonal_codim_one
    {L : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (hcodim : finrank ℝ L + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    {u l : EuclideanSpace ℝ (Fin n)}
    (hl : l ∈ Lᗮ) (hl0 : l ≠ 0) (hu : u ∉ L) :
    ⟪u, l⟫ ≠ 0 := by
  have hfinrank : finrank ℝ Lᗮ = 1 :=
    finrank_add_finrank_orthogonal' hcodim
  have heq : Lᗮ = ℝ ∙ l :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfinrank hl hl0
  intro hinner
  apply hu
  have huorth : u ∈ (ℝ ∙ l)ᗮ :=
    mem_orthogonal_singleton_iff_inner_left.mpr hinner
  have huorthorth : u ∈ Lᗮᗮ := by
    rwa [heq]
  simpa using huorthorth

/-- Bilu's projection estimate (6.9), converted into the exact
cross-multiplied volume inequality used in equation (8.10).

The set is viewed intrinsically inside `L`.  Its image under orthogonal
projection is measured by Hausdorff measure in the source dimension; this
form remains correct even when the projection is singular. -/
theorem projection_volume_crossmultiplied
    {L W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (u l : EuclideanSpace ℝ (Fin n))
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0)
    (hlL : l ∈ Lᗮ) (hl0 : l ≠ 0)
    (S : Set L) :
    ENNReal.ofReal |⟪u, l⟫| * volume S ≤
      ENNReal.ofReal (‖u‖ * ‖l‖) *
        μHE[finrank ℝ L] (projectionRestrict W L '' S) := by
  let f : L →ₗ[ℝ] W := projectionRestrict W L
  have hdet : |⟪u, l⟫| / (‖u‖ * ‖l‖) ≤ f.normDet :=
    normDet_projectionRestrict_lower_bound W L u l
      hcodim huW hu0 hlL hl0
  have hden_pos : 0 < ‖u‖ * ‖l‖ :=
    mul_pos (norm_pos_iff.mpr hu0) (norm_pos_iff.mpr hl0)
  have hreal : |⟪u, l⟫| ≤ (‖u‖ * ‖l‖) * f.normDet :=
    by simpa [mul_comm] using (div_le_iff₀ hden_pos).mp hdet
  have hennreal : ENNReal.ofReal |⟪u, l⟫| ≤
      ENNReal.ofReal (‖u‖ * ‖l‖) * ENNReal.ofReal f.normDet := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact ENNReal.ofReal_le_ofReal hreal
  calc
    ENNReal.ofReal |⟪u, l⟫| * volume S ≤
        (ENNReal.ofReal (‖u‖ * ‖l‖) * ENNReal.ofReal f.normDet) * volume S :=
      by gcongr
    _ = ENNReal.ofReal (‖u‖ * ‖l‖) *
        (ENNReal.ofReal f.normDet * volume S) := by ac_rfl
    _ = ENNReal.ofReal (‖u‖ * ‖l‖) *
        μHE[finrank ℝ L] (f '' S) := by
      rw [f.euclideanHausdorffMeasure_image_eq_normDet_mul_volume]

/-- Lemmas 6.9 and 6.10 together supply an integral normal for which
equation (8.10) holds, while retaining the coordinate bound required in
Bilu's subsequent estimate. -/
theorem exists_integral_normal_projection_volume_bound
    {L W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (P : Presentation (r := r) L) (hSat : P.IsSaturated)
    (u : Fin n → ℤ)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : integralReal u ∈ Wᗮ) (hu0 : integralReal u ≠ 0)
    (S : Set L) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      (∀ y ∈ L, ⟪y, integralReal x⟫ = 0) ∧
      (∀ j, ((|x j| : ℤ) : ℝ) ≤ ZLattice.covolume (integralPoints L)) ∧
      ENNReal.ofReal |⟪integralReal u, integralReal x⟫| * volume S ≤
        ENNReal.ofReal (‖integralReal u‖ * ‖integralReal x‖) *
          μHE[finrank ℝ L] (projectionRestrict W L '' S) := by
  obtain ⟨x, hx0, hxnormal, hxcoord⟩ :=
    P.exists_integral_normal_abs_le_integralPoints_covolume hSat
  refine ⟨x, hx0, hxnormal, hxcoord, ?_⟩
  exact projection_volume_crossmultiplied
    (integralReal u) (integralReal x) hcodim huW hu0
    ((L.mem_orthogonal (integralReal x)).2 hxnormal) (by simpa using hx0) S

/-- **Bilu 6.9 + 6.10, in the form used in Section 8.**

For a saturated integral presentation of `L`, choose the short integral
normal supplied by Bombieri--Vaaler.  If the integral normal `u` to the
target hyperplane is transverse to every such nonzero normal to `L`, then
the determinant of projection from `L` to that hyperplane satisfies the
displayed division-free covolume bound.

The transversality hypothesis is kept explicit because for a subspace of
codimension greater than one an arbitrary nonzero vector of `Lᗮ` need not
pair nontrivially with `u`; Bilu verifies it from the particular affine
subspace chosen in Proposition 8.3. -/
theorem exists_integral_normal_projection_covolume_bound
    {L W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (P : Presentation (r := r) L) (hSat : P.IsSaturated)
    (u : Fin n → ℤ)
    (hcodim : finrank ℝ W + 1 = finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : integralReal u ∈ Wᗮ) (hu0 : integralReal u ≠ 0)
    (htransverse : ∀ x : Fin n → ℤ, x ≠ 0 →
      (∀ y ∈ L, ⟪y, integralReal x⟫ = 0) →
      ⟪integralReal u, integralReal x⟫ ≠ 0) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      (∀ y ∈ L, ⟪y, integralReal x⟫ = 0) ∧
      (∀ j, ((|x j| : ℤ) : ℝ) ≤ ZLattice.covolume (integralPoints L)) ∧
      (1 : ℝ) ≤
        (projectionRestrict W L).normDet *
          (‖integralReal u‖ *
            (Real.sqrt n * ZLattice.covolume (integralPoints L))) := by
  obtain ⟨x, hx0, hxnormal, hxcoord⟩ :=
    P.exists_integral_normal_abs_le_integralPoints_covolume hSat
  have hl0 : integralReal x ≠ 0 := by
    simpa using hx0
  have hl : integralReal x ∈ Lᗮ :=
    (L.mem_orthogonal (integralReal x)).2 hxnormal
  have hinner : ⟪integralReal u, integralReal x⟫ ≠ 0 :=
    htransverse x hx0 hxnormal
  have hprojection := normDet_projectionRestrict_lower_bound
    W L (integralReal u) (integralReal x) hcodim huW hu0 hl hl0
  have hnorm : ‖integralReal x‖ ≤
      Real.sqrt n * ZLattice.covolume (integralPoints L) :=
    norm_integralReal_le_sqrt_mul x ENNReal.toReal_nonneg hxcoord
  have hdenom_pos : 0 < ‖integralReal u‖ * ‖integralReal x‖ :=
    mul_pos (norm_pos_iff.mpr hu0) (norm_pos_iff.mpr hl0)
  have hshort :
      (1 : ℝ) ≤ (projectionRestrict W L).normDet *
        (‖integralReal u‖ * ‖integralReal x‖) := by
    calc
      (1 : ℝ) ≤ |⟪integralReal u, integralReal x⟫| :=
        one_le_abs_inner_integralReal u x hinner
      _ = (|⟪integralReal u, integralReal x⟫| /
            (‖integralReal u‖ * ‖integralReal x‖)) *
            (‖integralReal u‖ * ‖integralReal x‖) := by
        symm
        exact div_mul_cancel₀ _ hdenom_pos.ne'
      _ ≤ (projectionRestrict W L).normDet *
            (‖integralReal u‖ * ‖integralReal x‖) :=
        mul_le_mul_of_nonneg_right hprojection hdenom_pos.le
  refine ⟨x, hx0, hxnormal, hxcoord, hshort.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
    (projectionRestrict W L).normDet_nonneg

/-- Codimension-one specialization of
`exists_integral_normal_projection_covolume_bound`.  Here transversality is
automatic as soon as the target normal is not in `L`. -/
theorem exists_integral_normal_projection_covolume_bound_of_codim_one
    {L W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (P : Presentation (r := r) L) (hSat : P.IsSaturated)
    (u : Fin n → ℤ)
    (hLcodim : finrank ℝ L + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (hWcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : integralReal u ∈ Wᗮ) (hu0 : integralReal u ≠ 0)
    (huL : integralReal u ∉ L) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      (∀ y ∈ L, ⟪y, integralReal x⟫ = 0) ∧
      (∀ j, ((|x j| : ℤ) : ℝ) ≤ ZLattice.covolume (integralPoints L)) ∧
      (1 : ℝ) ≤
        (projectionRestrict W L).normDet *
          (‖integralReal u‖ *
            (Real.sqrt n * ZLattice.covolume (integralPoints L))) := by
  apply exists_integral_normal_projection_covolume_bound
    P hSat u hWcodim huW hu0
  intro x hx0 hxnormal
  exact inner_ne_zero_of_mem_orthogonal_codim_one hLcodim
    ((L.mem_orthogonal (integralReal x)).2 hxnormal) (by simpa using hx0) huL

end Erdos186.CFP.Bilu.ProjectionCovolume

#print axioms Erdos186.CFP.Bilu.ProjectionCovolume.exists_integral_normal_projection_covolume_bound
#print axioms Erdos186.CFP.Bilu.ProjectionCovolume.exists_integral_normal_projection_covolume_bound_of_codim_one
#print axioms Erdos186.CFP.Bilu.ProjectionCovolume.exists_integral_normal_projection_volume_bound
