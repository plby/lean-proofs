import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreIdentification
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertSectionsAnalytic

/-!
# Genuine scalar coordinates over a chosen covering point

The native cocycle bundle is identified with its diagonal quotient by the
previously constructed analytic identification.  At a covering point `z`,
the scalar coordinate is a proved linear equivalence of the actual fibre.
The scalar coordinate of any holomorphic lifted-base map is holomorphic;
no global trivialization or gauge is assumed.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness

open PeriodTorusAppellHumbert

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)

/-- The actual lattice displacement from a covering point to the preferred
lift of its image. -/
def coverShift (p : PeriodDomain) (z : ComplexPlane₂) : p.lattice :=
  ⟨Core.lift p (p.lattice.mkQ z) (p.lattice.mkQ z) - z,
    (Submodule.Quotient.eq p.lattice).mp
      (Core.lift_project p _ (Core.mem_baseSet p _))⟩

theorem coverShift_spec (p : PeriodDomain) (z : ComplexPlane₂) :
    Core.lift p (p.lattice.mkQ z) (p.lattice.mkQ z) = z + coverShift p z := by
  dsimp [coverShift]
  abel

/-- The actual fibre over the image of `z`, in the scalar quotient coordinate
based at `z`. -/
def coverFiberEquiv (z : ComplexPlane₂) :
    ℂ ≃ₗ[ℂ] (Core.data F).core.Fiber (p.lattice.mkQ z) where
  toFun c := (F.factor (coverShift p z) z : ℂ) * c
  invFun c := (F.factor (coverShift p z) z : ℂ)⁻¹ * id (α := ℂ) c
  left_inv c := by
    change (F.factor (coverShift p z) z : ℂ)⁻¹ *
      ((F.factor (coverShift p z) z : ℂ) * c) = c
    rw [← mul_assoc, inv_mul_cancel₀ (F.factor_ne_zero _ _), one_mul]
  right_inv c := by
    change (F.factor (coverShift p z) z : ℂ) *
      ((F.factor (coverShift p z) z : ℂ)⁻¹ * id (α := ℂ) c) = id (α := ℂ) c
    rw [← mul_assoc, mul_inv_cancel₀ (F.factor_ne_zero _ _), one_mul]
  map_add' c d := mul_add _ c d
  map_smul' a c := mul_left_comm _ a c

@[simp] theorem coverFiberEquiv_apply (z : ComplexPlane₂) (c : ℂ) :
    id (α := ℂ) (coverFiberEquiv F z c) = (F.factor (coverShift p z) z : ℂ) * c := rfl

/-- This is the original quotient point, not an independently labelled fibre. -/
theorem toAssociated_coverFiberEquiv (z : ComplexPlane₂) (c : ℂ) :
    Core.toAssociated F ⟨p.lattice.mkQ z, coverFiberEquiv F z c⟩ =
      associatedMap F (z, c) := by
  change associatedMap F
    (Core.lift p (p.lattice.mkQ z) (p.lattice.mkQ z),
      (F.factor (coverShift p z) z : ℂ) * c) = associatedMap F (z, c)
  rw [coverShift_spec]
  exact associatedMap_diagonal F (coverShift p z) (z, c)

theorem fromAssociated_map (z : ComplexPlane₂) (c : ℂ) :
    Core.fromAssociated F (associatedMap F (z, c)) =
      ⟨p.lattice.mkQ z, coverFiberEquiv F z c⟩ := by
  apply Core.toAssociated_injective F
  rw [Core.toAssociated_fromAssociated, toAssociated_coverFiberEquiv]

theorem toAssociated_fibre_coordinate (z : ComplexPlane₂)
    (c : (Core.data F).core.Fiber (p.lattice.mkQ z)) :
    Core.toAssociated F ⟨p.lattice.mkQ z, c⟩ =
      associatedMap F (z, (coverFiberEquiv F z).symm c) := by
  simpa only [LinearEquiv.apply_symm_apply] using
    toAssociated_coverFiberEquiv F z ((coverFiberEquiv F z).symm c)

/-- The genuine scalar coordinate of a map over the covering projection. -/
def liftCoordinate (f : ComplexPlane₂ → AssociatedSpace F)
    (hf : ∀ z, projection F (f z) = p.lattice.mkQ z) (z : ComplexPlane₂) : ℂ :=
  fibreCoordinate F z (f z) (hf z)

@[simp] theorem associatedMap_liftCoordinate (f : ComplexPlane₂ → AssociatedSpace F)
    (hf : ∀ z, projection F (f z) = p.lattice.mkQ z) (z : ComplexPlane₂) :
    associatedMap F (z, liftCoordinate F f hf z) = f z :=
  associatedMap_fibreCoordinate F z (f z) (hf z)

/-- Local inverse uniqueness for the existing quotient atlas proves that
the scalar coordinate is entire analytic. -/
theorem liftCoordinate_contDiff (f : ComplexPlane₂ → AssociatedSpace F)
    (hf : ∀ z, projection F (f z) = p.lattice.mkQ z)
    (hhol : letI := associatedChartedSpace F; ContMDiff IC IP ω f) :
    ContDiff ℂ ω (liftCoordinate F f hf) := by
  let := associatedChartedSpace F
  let := diagonalAction F
  apply ContMDiff.contDiff
  intro z
  let u : ComplexPlane₂ × ℂ := (z, liftCoordinate F f hf z)
  let hP := associatedMap_isQuotientCoveringMap F
  let e := CoveringQuotient.localInverse hP u
  let l : ComplexPlane₂ → ComplexPlane₂ × ℂ := fun y => e (f y)
  have huz : associatedMap F u = f z := associatedMap_liftCoordinate F f hf z
  have hsrc : f z ∈ e.source := by
    rw [← huz]
    exact hP.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
  have hl : ContMDiffAt IC IP ω l z :=
    ((associatedLocalInverse_holomorphic F u).contMDiffAt
      (e.open_source.mem_nhds hsrc)).comp z hhol.contMDiffAt
  have hlz : l z = u := by
    change e (f z) = u
    rw [← huz]
    exact hP.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self
  have hsource : ∀ᶠ y in 𝓝 z, f y ∈ e.source :=
    hhol.continuous.continuousAt (e.open_source.mem_nhds hsrc)
  have hfirst : (fun y => (l y).1) =ᶠ[𝓝 z] (fun y => y) := by
    apply eventuallyEq_of_localHomeomorph_comp_eq
      p.quotientCovering.isCoveringMap.isLocalHomeomorph
      (continuous_fst.continuousAt.comp hl.continuousAt) continuousAt_id
      (congrArg Prod.fst hlz)
    filter_upwards [hsource] with y hy
    calc
      p.lattice.mkQ (l y).1 = projection F (associatedMap F (l y)) := rfl
      _ = projection F (f y) := congrArg (projection F)
        (CoveringQuotient.project_localInverse hP u hy)
      _ = p.lattice.mkQ y := hf y
  have heq : liftCoordinate F f hf =ᶠ[𝓝 z] (fun y => (l y).2) := by
    filter_upwards [hsource, hfirst] with y hy hfy
    apply associatedMap_fibre_injective F y
    calc
      associatedMap F (y, liftCoordinate F f hf y) = f y :=
        associatedMap_liftCoordinate F f hf y
      _ = associatedMap F (l y) := (CoveringQuotient.project_localInverse hP u hy).symm
      _ = associatedMap F (y, (l y).2) :=
        congrArg (associatedMap F) (Prod.ext hfy rfl)
  have hsnd : ContMDiff IP I₁ ω (Prod.snd : ComplexPlane₂ × ℂ → ℂ) :=
    (contDiff_snd : ContDiff ℂ ω (Prod.snd : ComplexPlane₂ × ℂ → ℂ)).contMDiff
  exact (hsnd.contMDiffAt.comp z hl).congr_of_eventuallyEq heq

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness
