import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCuspHeight
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessRetraction
import Wikipedia.HopfProblem.CuspCentralHomologyOpenRetraction

/-!
# The entire actual cusp cap has the central-fibre homotopy type

First shrink the full native quotient to any chosen positive-radius open
sub-tube by a height cutoff fixed near the central fibre.  Then choose a
radius for the already constructed controlled central retraction.  The
resulting homotopy equivalence has forward map exactly the original
central-fibre inclusion.  No unproved smallness condition on the fixed
gluing radius is used.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCusp

open ThreefoldOverlapMappingTorus.Cusp SpecialPeriods.CuspFamily CuspUniformization
open ThreefoldHomologyFinitenessRetraction CuspCentralHomology

/-- Positivity of the actual parameter norm is the native punctured locus. -/
def positivePuncturedHomeomorph (D : Data) :
    Positive (parameterNorm D) ≃ₜ PuncturedQuotient D.correction D.radius where
  toFun x := ⟨x.val, norm_pos_iff.mp (show 0 < ‖CuspQuotient.projection
    D.correction D.radius x.val‖ from x.property)⟩
  invFun x := ⟨x.val, norm_pos_iff.mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The actual punctured height cutoff in the positive-norm coordinates. -/
def positiveHeightCutoff (D : Data) (H : ℝ) :
    C(unitInterval × Positive (parameterNorm D), Positive (parameterNorm D)) where
  toFun p := (positivePuncturedHomeomorph D).symm
    (puncturedHeightCutoff D H (p.1, positivePuncturedHomeomorph D p.2))
  continuous_toFun := (positivePuncturedHomeomorph D).symm.continuous.comp
    ((puncturedHeightCutoff D H).continuous.comp
      (continuous_fst.prodMk ((positivePuncturedHomeomorph D).continuous.comp continuous_snd)))

@[simp] theorem positiveHeightCutoff_zero (D : Data) (H : ℝ)
    (x : Positive (parameterNorm D)) : positiveHeightCutoff D H (0, x) = x := by
  change (positivePuncturedHomeomorph D).symm
    (puncturedHeightCutoff D H (0, positivePuncturedHomeomorph D x)) = x
  rw [puncturedHeightCutoff_zero, Homeomorph.symm_apply_apply]

theorem positiveHeightCutoff_norm_nonincrease (D : Data) (H : ℝ) (t : unitInterval)
    (x : Positive (parameterNorm D)) :
    parameterNorm D (positiveHeightCutoff D H (t, x)).val ≤ parameterNorm D x.val :=
  puncturedHeightCutoff_norm_nonincrease D H t (positivePuncturedHomeomorph D x)

theorem positiveHeightCutoff_one_norm_le (D : Data) (H : ℝ)
    (x : Positive (parameterNorm D)) :
    parameterNorm D (positiveHeightCutoff D H (1, x)).val ≤ cutoffRadius H :=
  puncturedHeightCutoff_one_norm_le D H (positivePuncturedHomeomorph D x)

theorem positiveHeightCutoff_fixed (D : Data) (H : ℝ) (t : unitInterval)
    (x : Positive (parameterNorm D)) (hx : parameterNorm D x.val < cutoffRadius H) :
    positiveHeightCutoff D H (t, x) = x := by
  change (positivePuncturedHomeomorph D).symm
    (puncturedHeightCutoff D H (t, positivePuncturedHomeomorph D x)) = x
  rw [puncturedHeightCutoff_fixed D H t _ hx, Homeomorph.symm_apply_apply]

/-- Every positive open sub-tube is genuinely homotopy equivalent to the
whole fixed-radius cusp cap; the reverse map is its literal inclusion. -/
def fullSublevelHomotopyEquiv (D : Data) (δ : ℝ) (hδ : 0 < δ) :
    FullSpace D ≃ₕ OpenQuotient D.correction D.radius δ :=
  sublevelHomotopyEquiv (parameterNorm D) (positiveHeightCutoff D (heightThreshold δ + 1))
    (cutoffRadius (heightThreshold δ + 1)) (cutoffRadius_pos _)
    (positiveHeightCutoff_fixed D _) (positiveHeightCutoff_zero D _)
    (positiveHeightCutoff_norm_nonincrease D _) δ (cutoffRadius_threshold_lt hδ).le
    (fun x => (positiveHeightCutoff_one_norm_le D _ x).trans_lt (cutoffRadius_threshold_lt hδ))

@[simp] theorem fullSublevelHomotopyEquiv_symm_apply (D : Data) (δ : ℝ) (hδ : 0 < δ)
    (x : OpenQuotient D.correction D.radius δ) :
    (fullSublevelHomotopyEquiv D δ hδ).symm x = x.val := rfl

/-- The original central fibre included in the original full native cusp quotient. -/
def fullCentralInclusion (D : Data) :
    C(CuspRetraction.QuotientCentralFibre D.correction D.radius, FullSpace D) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The genuine central inclusion is a homotopy equivalence for the
entire fixed-radius cap, without assuming the radius is controlled. -/
theorem exists_fullCentralHomotopyEquiv (D : Data) :
    ∃ e : CuspRetraction.QuotientCentralFibre D.correction D.radius ≃ₕ FullSpace D,
      e.toFun = fullCentralInclusion D := by
  obtain ⟨δ, hδ, hδr, _hδ1, he⟩ :=
    exists_centralHomotopyEquiv D.correction D.radius D.radius_pos D.holomorphic
  obtain ⟨e, he⟩ := he δ hδ le_rfl hδr.le
  let eR := openQuotientRadiusHomeomorph D.correction hδr.le D.holomorphic
  let eF := fullSublevelHomotopyEquiv D δ hδ
  refine ⟨(e.trans eR.toHomotopyEquiv).trans eF.symm, ?_⟩
  apply ContinuousMap.ext
  intro x
  change (eR (e x)).val = x.val
  have hx := ContinuousMap.congr_fun he x
  change e x = eR.symm (centralIntoOpen D.correction D.radius δ hδ x) at hx
  rw [hx, Homeomorph.apply_symm_apply]
  rfl

/-- The constructed homotopy equivalence, preserving the actual central inclusion. -/
def fullCentralHomotopyEquiv (D : Data) :
    CuspRetraction.QuotientCentralFibre D.correction D.radius ≃ₕ FullSpace D :=
  Classical.choose (exists_fullCentralHomotopyEquiv D)

@[simp] theorem fullCentralHomotopyEquiv_toFun (D : Data) :
    (fullCentralHomotopyEquiv D).toFun = fullCentralInclusion D :=
  Classical.choose_spec (exists_fullCentralHomotopyEquiv D)

end Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCusp
