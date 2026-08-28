import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCusp

/-!
# A genuine radial cutoff on the entire punctured cusp

The actual height-times-mapping-torus homeomorphism retains the original
parameter norm.  Increasing height by a continuous cutoff therefore
decreases that norm.  The cutoff is exactly the identity sufficiently
near the central fibre, which permits a continuous extension across it.
No bound comparing the fixed filling radius to a retraction radius is
assumed.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCusp

open ThreefoldOverlapMappingTorus.Cusp SpecialPeriods.CuspFamily CuspUniformization

abbrev FullSpace (D : Data) := CuspQuotient.QuotientSpace D.correction D.radius

/-- The norm of the literal original cusp parameter on the full quotient. -/
def parameterNorm (D : Data) : C(FullSpace D, ℝ) :=
  ⟨fun x => ‖CuspQuotient.projection D.correction D.radius x‖,
    (CuspQuotient.projection_continuous D.correction D.radius).norm⟩

theorem parameterNorm_nonneg (D : Data) (x : FullSpace D) : 0 ≤ parameterNorm D x := by
  change 0 ≤ ‖CuspQuotient.projection D.correction D.radius x‖
  exact norm_nonneg _

private theorem exponential_norm (s : ℂ) :
    ‖exponential s‖ = Real.exp (-2 * Real.pi * s.im) :=
  (Real.exp_log (norm_pos_iff.mpr (exponential_ne_zero s))).symm.trans
    (congrArg Real.exp (log_norm_exponential s))

/-- The whole punctured product model has the original exponential radius. -/
theorem parameterNorm_product_symm (D : Data) (p : Height D.radius × Boundary) :
    parameterNorm D ((puncturedProductHomeomorph D).symm p) =
      Real.exp (-2 * Real.pi * (p.1 : ℝ)) := by
  rcases p with ⟨h, y⟩
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective monodromy y
  change ‖CuspQuotient.projection D.correction D.radius
    (puncturedFamilyHomeomorph D
      ((familyProductHomeomorph D).symm (h, MappingTorus.mk monodromy (t, x))))‖ = _
  rw [familyProductHomeomorph_symm_mk, puncturedFamilyHomeomorph_base, D.projection_quotient]
  change ‖exponential (logPoint D.radius D.radius_pos t h)‖ = _
  rw [exponential_norm, logPoint_im]

/-- The height coordinate determines the actual parameter norm of every point. -/
theorem parameterNorm_punctured (D : Data)
    (x : PuncturedQuotient D.correction D.radius) :
    parameterNorm D x =
      Real.exp (-2 * Real.pi * ((puncturedProductHomeomorph D x).1 : ℝ)) := by
  have h := parameterNorm_product_symm D (puncturedProductHomeomorph D x)
  rwa [Homeomorph.symm_apply_apply] at h

/-- A continuous increasing height cutoff, fixed on the upper half-line. -/
def heightCutoff (r H : ℝ) : C(unitInterval × Height r, Height r) where
  toFun p := ⟨(p.2 : ℝ) + (p.1 : ℝ) * (max (p.2 : ℝ) H - (p.2 : ℝ)),
    lt_of_lt_of_le p.2.property
      (le_add_of_nonneg_right (mul_nonneg p.1.property.1
        (sub_nonneg.mpr (le_max_left _ _))))⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (((continuous_subtype_val.comp continuous_snd).max continuous_const).sub
          (continuous_subtype_val.comp continuous_snd)))).subtype_mk _

@[simp] theorem heightCutoff_zero (r H : ℝ) (h : Height r) :
    heightCutoff r H (0, h) = h := by
  apply Subtype.ext
  change (h : ℝ) + 0 * (max (h : ℝ) H - (h : ℝ)) = (h : ℝ)
  simp

theorem heightCutoff_one (r H : ℝ) (h : Height r) :
    (heightCutoff r H (1, h) : ℝ) = max (h : ℝ) H := by
  change (h : ℝ) + 1 * (max (h : ℝ) H - (h : ℝ)) = _
  ring

theorem heightCutoff_ge (r H : ℝ) (t : unitInterval) (h : Height r) :
    (h : ℝ) ≤ (heightCutoff r H (t, h) : ℝ) :=
  le_add_of_nonneg_right (mul_nonneg t.property.1
    (sub_nonneg.mpr (le_max_left _ _)))

theorem heightCutoff_fixed (r H : ℝ) (t : unitInterval) (h : Height r)
    (hh : H ≤ (h : ℝ)) : heightCutoff r H (t, h) = h := by
  apply Subtype.ext
  change (h : ℝ) + (t : ℝ) * (max (h : ℝ) H - (h : ℝ)) = (h : ℝ)
  rw [max_eq_left hh, sub_self, mul_zero, add_zero]

/-- Transport the cutoff through the actual entire punctured-cusp homeomorphism. -/
def puncturedHeightCutoff (D : Data) (H : ℝ) :
    C(unitInterval × PuncturedQuotient D.correction D.radius,
      PuncturedQuotient D.correction D.radius) where
  toFun p := (puncturedProductHomeomorph D).symm
    (heightCutoff D.radius H (p.1, (puncturedProductHomeomorph D p.2).1),
      (puncturedProductHomeomorph D p.2).2)
  continuous_toFun := (puncturedProductHomeomorph D).symm.continuous.comp
    (((heightCutoff D.radius H).continuous.comp
      (continuous_fst.prodMk (continuous_fst.comp
        ((puncturedProductHomeomorph D).continuous.comp continuous_snd)))).prodMk
      (continuous_snd.comp ((puncturedProductHomeomorph D).continuous.comp continuous_snd)))

theorem puncturedHeightCutoff_product (D : Data) (H : ℝ) (t : unitInterval)
    (x : PuncturedQuotient D.correction D.radius) :
    puncturedProductHomeomorph D (puncturedHeightCutoff D H (t, x)) =
      (heightCutoff D.radius H (t, (puncturedProductHomeomorph D x).1),
        (puncturedProductHomeomorph D x).2) :=
  (puncturedProductHomeomorph D).apply_symm_apply _

@[simp] theorem puncturedHeightCutoff_zero (D : Data) (H : ℝ)
    (x : PuncturedQuotient D.correction D.radius) :
    puncturedHeightCutoff D H (0, x) = x := by
  apply (puncturedProductHomeomorph D).injective
  rw [puncturedHeightCutoff_product, heightCutoff_zero]

theorem puncturedHeightCutoff_parameterNorm (D : Data) (H : ℝ) (t : unitInterval)
    (x : PuncturedQuotient D.correction D.radius) :
    parameterNorm D (puncturedHeightCutoff D H (t, x)) =
      Real.exp (-2 * Real.pi *
        (heightCutoff D.radius H (t, (puncturedProductHomeomorph D x).1) : ℝ)) := by
  exact parameterNorm_product_symm D _

/-- The original parameter norm never increases under the actual deformation. -/
theorem puncturedHeightCutoff_norm_nonincrease (D : Data) (H : ℝ) (t : unitInterval)
    (x : PuncturedQuotient D.correction D.radius) :
    parameterNorm D (puncturedHeightCutoff D H (t, x)) ≤ parameterNorm D x := by
  rw [puncturedHeightCutoff_parameterNorm, parameterNorm_punctured]
  apply Real.exp_le_exp.mpr
  have hh := heightCutoff_ge D.radius H t (puncturedProductHomeomorph D x).1
  nlinarith [Real.pi_pos]

/-- The positive radius below which the deformation is exactly the identity. -/
def cutoffRadius (H : ℝ) : ℝ := Real.exp (-2 * Real.pi * H)

theorem cutoffRadius_pos (H : ℝ) : 0 < cutoffRadius H := Real.exp_pos _

/-- At the last time every original point has entered the controlled radius. -/
theorem puncturedHeightCutoff_one_norm_le (D : Data) (H : ℝ)
    (x : PuncturedQuotient D.correction D.radius) :
    parameterNorm D (puncturedHeightCutoff D H (1, x)) ≤ cutoffRadius H := by
  rw [puncturedHeightCutoff_parameterNorm, heightCutoff_one]
  apply Real.exp_le_exp.mpr
  have hh := le_max_right ((puncturedProductHomeomorph D x).1 : ℝ) H
  nlinarith [Real.pi_pos]

/-- The deformation fixes a full open neighborhood of the missing central fibre. -/
theorem puncturedHeightCutoff_fixed (D : Data) (H : ℝ) (t : unitInterval)
    (x : PuncturedQuotient D.correction D.radius)
    (hx : parameterNorm D x < cutoffRadius H) :
    puncturedHeightCutoff D H (t, x) = x := by
  have hh : H ≤ ((puncturedProductHomeomorph D x).1 : ℝ) := by
    rw [parameterNorm_punctured] at hx
    have he := Real.exp_lt_exp.mp hx
    nlinarith [Real.pi_pos]
  apply (puncturedProductHomeomorph D).injective
  rw [puncturedHeightCutoff_product, heightCutoff_fixed D.radius H t _ hh]

/-- Choosing one height unit above the target threshold gives a strictly
smaller positive radius, for every positive target radius. -/
theorem cutoffRadius_threshold_lt {δ : ℝ} (hδ : 0 < δ) :
    cutoffRadius (heightThreshold δ + 1) < δ := by
  apply (Real.log_lt_log_iff (cutoffRadius_pos _) hδ).mp
  change Real.log (Real.exp (-2 * Real.pi * (heightThreshold δ + 1))) < Real.log δ
  rw [Real.log_exp]
  have ht : 2 * Real.pi * heightThreshold δ = -Real.log δ := by
    unfold heightThreshold
    exact mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))
  nlinarith [Real.pi_pos]

end Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCusp
