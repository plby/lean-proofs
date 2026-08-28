import Wikipedia.HopfProblem.DegreeCollapseRadialSphereRelation
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Actual radial coordinates on the once-punctured sphere cylinder

The map (t,u) ↦ exp(t) u is a homeomorphism onto the punctured vector
space. Removing the actual crossing parameter removes exactly one more
point. The original endpoint spheres keep their radial parametrizations.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.PassageHomology

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialCylinderHomeomorph :
    (ℝ × sphere (0 : E) 1) ≃ₜ ({0}ᶜ : Set E) :=
  ((Homeomorph.prodComm ℝ (sphere (0 : E) 1)).trans
    ((Homeomorph.refl (sphere (0 : E) 1)).prodCongr Real.expOrderIso.toHomeomorph)).trans
      (homeomorphUnitSphereProd E).symm

theorem radialCylinderHomeomorph_apply (p : ℝ × sphere (0 : E) 1) :
    (radialCylinderHomeomorph E p).val = Real.exp p.1 • p.2.val := rfl

variable {E}

def cylinderPuncture (τ : ℝ) (u : sphere (0 : E) 1) : E := Real.exp τ • u.val

theorem norm_cylinderPuncture (τ : ℝ) (u : sphere (0 : E) 1) :
    ‖cylinderPuncture τ u‖ = Real.exp τ := by
  rw [cylinderPuncture, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos τ),
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

def puncturedCylinderHomeomorph (τ : ℝ) (u : sphere (0 : E) 1) :
    ({(τ, u)}ᶜ : Set (ℝ × sphere (0 : E) 1)) ≃ₜ twoPunctureSet 0 (cylinderPuncture τ u) where
  toFun p := by
    refine ⟨(radialCylinderHomeomorph E p.val).val,
      (radialCylinderHomeomorph E p.val).property, ?_⟩
    intro h
    have he : radialCylinderHomeomorph E p.val = radialCylinderHomeomorph E (τ, u) :=
      Subtype.ext h
    exact p.property ((radialCylinderHomeomorph E).injective he)
  invFun z := ⟨(radialCylinderHomeomorph E).symm ⟨z.val, z.property.1⟩, by
    intro h
    have hh := congrArg (radialCylinderHomeomorph E) h
    rw [(radialCylinderHomeomorph E).apply_symm_apply] at hh
    exact z.property.2 (congrArg Subtype.val hh)⟩
  left_inv p := by
    apply Subtype.ext
    change (radialCylinderHomeomorph E).symm (radialCylinderHomeomorph E p.val) = p.val
    exact (radialCylinderHomeomorph E).symm_apply_apply p.val
  right_inv z := by
    apply Subtype.ext
    change ((radialCylinderHomeomorph E)
      ((radialCylinderHomeomorph E).symm ⟨z.val, z.property.1⟩)).val = z.val
    exact congrArg (fun w : ({0}ᶜ : Set E) => w.val)
      ((radialCylinderHomeomorph E).apply_symm_apply ⟨z.val, z.property.1⟩)
  continuous_toFun := (continuous_subtype_val.comp
    ((radialCylinderHomeomorph E).continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    have hc : Continuous (fun z : twoPunctureSet 0 (cylinderPuncture τ u) =>
        (⟨z.val, z.property.1⟩ : ({0}ᶜ : Set E))) := continuous_subtype_val.subtype_mk _
    exact ((radialCylinderHomeomorph E).symm.continuous.comp hc).subtype_mk _

theorem puncturedCylinderHomeomorph_apply (τ : ℝ) (u : sphere (0 : E) 1)
    (p : ({(τ, u)}ᶜ : Set (ℝ × sphere (0 : E) 1))) :
    (puncturedCylinderHomeomorph τ u p).val = Real.exp p.val.1 • p.val.2.val := rfl

def cylinderSlice (τ : ℝ) (u : sphere (0 : E) 1) (t : ℝ) (ht : t ≠ τ) :
    C(sphere (0 : E) 1, ({(τ, u)}ᶜ : Set (ℝ × sphere (0 : E) 1))) where
  toFun v := ⟨(t, v), fun h => ht (congrArg Prod.fst h)⟩
  continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk _

def cylinderLink (τ : ℝ) (u : sphere (0 : E) 1) (ε : ℝ)
    (hε : 0 < ε) (hεu : ε < Real.exp τ) :
    C(sphere (0 : E) 1, ({(τ, u)}ᶜ : Set (ℝ × sphere (0 : E) 1))) :=
  ((puncturedCylinderHomeomorph τ u).symm : C(_, _)).comp
    (linkingSphere (cylinderPuncture τ u) ε hε (by rwa [norm_cylinderPuncture]))

end Wikipedia.HopfProblem.DegreeCollapse.PassageHomology
