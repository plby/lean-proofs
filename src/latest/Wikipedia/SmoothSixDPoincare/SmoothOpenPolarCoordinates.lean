import Wikipedia.SmoothSixDPoincare.PuncturedHandleCoordinates
import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Native smooth polar coordinates on the punctured open disk

The actual radius and direction maps give a diffeomorphism, with both
inverse identities proved in the original vector coordinates. These are
the open transition coordinates used to glue a surgery boundary.
-/

noncomputable section

open Set Metric Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.PuncturedHandle

def openRadius : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩

def openPuncturedDisk (E : Type*) [NormedAddCommGroup E] : Opens E :=
  ⟨{x | x ≠ 0 ∧ ‖x‖ < 1},
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)⟩

section Topological

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def openPoint (u : UnitSphere E) (r : openRadius) : openPuncturedDisk E := by
  have hn : ‖r.val • u.val‖ = r.val := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.property.1,
      mem_sphere_zero_iff_norm.mp u.property, mul_one]
  refine ⟨r.val • u.val, ?_, ?_⟩
  · apply norm_pos_iff.mp
    rw [hn]
    exact r.property.1
  · rw [hn]
    exact r.property.2

theorem norm_openPoint (u : UnitSphere E) (r : openRadius) : ‖(openPoint u r).val‖ = r.val := by
  change ‖r.val • u.val‖ = r.val
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.property.1,
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

def openPolarEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    openPuncturedDisk E ≃ (UnitSphere E × openRadius) where
  toFun x := (RadialExtension.direction x.val x.property.1,
    ⟨‖x.val‖, norm_pos_iff.mpr x.property.1, x.property.2⟩)
  invFun p := openPoint p.1 p.2
  left_inv x := by
    apply Subtype.ext
    exact smul_inv_smul₀ (norm_ne_zero_iff.mpr x.property.1) x.val
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change ‖(openPoint p.1 p.2).val‖⁻¹ • (p.2.val • p.1.val) = p.1.val
      rw [norm_openPoint, inv_smul_smul₀ p.2.property.1.ne']
    · apply Subtype.ext
      exact norm_openPoint p.1 p.2

end Topological

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem contMDiff_openDisk_norm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
    (fun x : openPuncturedDisk E => ‖x.val‖) := by
  intro x
  exact (contDiffAt_norm ℝ x.property.1).contMDiffAt.comp x contMDiff_subtype_val.contMDiffAt

def openPolarDiffeomorph (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)] :
    Diffeomorph 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ))
      (openPuncturedDisk E) (UnitSphere E × openRadius) ∞ := by
  have hn := contMDiff_openDisk_norm (E := E)
  have hd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun x : openPuncturedDisk E => ‖x.val‖⁻¹ • x.val) :=
    (hn.inv₀ (fun x => norm_ne_zero_iff.mpr x.property.1)).smul contMDiff_subtype_val
  have hs : ContMDiff 𝓘(ℝ, E) (𝓡 n) ∞
      (fun x : openPuncturedDisk E => (openPolarEquiv E x).1) :=
    hd.codRestrict_sphere (fun x => (RadialExtension.direction x.val x.property.1).property)
  have hr : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x : openPuncturedDisk E => (openPolarEquiv E x).2) :=
    (ContMDiff.subtypeVal_comp_iff openRadius _).mp hn
  refine { toEquiv := openPolarEquiv E, contMDiff_toFun := hs.prodMk hr, contMDiff_invFun := ?_ }
  apply (ContMDiff.subtypeVal_comp_iff (openPuncturedDisk E) _).mp
  have hu : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val : UnitSphere E → E) :=
    contMDiff_coe_sphere (n := n)
  have ht : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (Subtype.val : openRadius → ℝ) :=
    contMDiff_subtype_val
  exact (ht.comp contMDiff_snd).smul (hu.comp contMDiff_fst)

omit [FiniteDimensional ℝ E] in
theorem openPolarDiffeomorph_direction (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (x : openPuncturedDisk E) :
    ((openPolarDiffeomorph (E := E) n x).1 : E) = ‖x.val‖⁻¹ • x.val := rfl

omit [FiniteDimensional ℝ E] in
theorem openPolarDiffeomorph_radius (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (x : openPuncturedDisk E) : (openPolarDiffeomorph (E := E) n x).2.val = ‖x.val‖ := rfl

end Wikipedia.SmoothSixDPoincare.PuncturedHandle
