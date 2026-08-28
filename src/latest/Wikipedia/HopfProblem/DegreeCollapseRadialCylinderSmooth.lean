import Wikipedia.HopfProblem.DegreeCollapseLowerPassageHomology
import Wikipedia.SmoothSixDPoincare.OpenSubtypePartialDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smoothness of the actual radial cylinder coordinates

The previously constructed homeomorphism has the actual inverse formulas
log norm and normalized direction. Both are smooth away from zero in the
original Euclidean and sphere atlases. The same radial homeomorphism is
therefore upgraded to a native diffeomorphism.
-/

noncomputable section

open Set Function Metric Manifold TopologicalSpace
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.PassageHomology

open Wikipedia.SmoothSixDPoincare

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def puncturedVectorSpace : Opens E := ⟨({0}ᶜ : Set E), isOpen_compl_singleton⟩

theorem radialCylinderHomeomorph_symm_fst (x : ({0}ᶜ : Set E)) :
    ((radialCylinderHomeomorph E).symm x).1 = Real.log ‖x.val‖ := by
  have hn : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property
  change Real.expOrderIso.symm ((homeomorphUnitSphereProd E) x).2 = _
  rw [Real.log_of_pos hn]
  congr 1
  apply Subtype.ext
  exact homeomorphUnitSphereProd_apply_snd_coe E x

theorem radialCylinderHomeomorph_symm_snd_coe (x : ({0}ᶜ : Set E)) :
    (((radialCylinderHomeomorph E).symm x).2 : E) = ‖x.val‖⁻¹ • x.val := by
  change (((homeomorphUnitSphereProd E) x).1 : E) = _
  exact homeomorphUnitSphereProd_apply_fst_coe E x

variable [FiniteDimensional ℝ E]

def radialCylinderDiffeomorph (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)] :
    Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
      (ℝ × sphere (0 : E) 1) (puncturedVectorSpace E) ∞ where
  toEquiv := (radialCylinderHomeomorph E).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (puncturedVectorSpace E) _).mp
    change ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × sphere (0 : E) 1 => Real.exp p.1 • p.2.val)
    exact (Real.contDiff_exp.contMDiff.comp contMDiff_fst).smul
      ((contMDiff_coe_sphere (n := n)).comp contMDiff_snd)
  contMDiff_invFun := by
    have hn : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        (fun x : puncturedVectorSpace E => ‖x.val‖) := by
      intro x
      exact (contDiffAt_norm ℝ x.property).contMDiffAt.comp x contMDiff_subtype_val.contMDiffAt
    have hl : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        (fun x : puncturedVectorSpace E => Real.log ‖x.val‖) := by
      intro x
      exact (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr x.property)).contMDiffAt.comp x
        hn.contMDiffAt
    have hraw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (fun x : puncturedVectorSpace E => ‖x.val‖⁻¹ • x.val) :=
      (hn.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul contMDiff_subtype_val
    have hfst : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        (fun x : puncturedVectorSpace E => ((radialCylinderHomeomorph E).symm x).1) := by
      have heq : (fun x : puncturedVectorSpace E => ((radialCylinderHomeomorph E).symm x).1) =
          (fun x => Real.log ‖x.val‖) := funext (fun x => radialCylinderHomeomorph_symm_fst E x)
      rw [heq]
      exact hl
    have hval : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (fun x : puncturedVectorSpace E => (((radialCylinderHomeomorph E).symm x).2 : E)) := by
      have heq : (fun x : puncturedVectorSpace E =>
          (((radialCylinderHomeomorph E).symm x).2 : E)) =
          (fun x => ‖x.val‖⁻¹ • x.val) :=
        funext (fun x => radialCylinderHomeomorph_symm_snd_coe E x)
      rw [heq]
      exact hraw
    have hsnd : ContMDiff 𝓘(ℝ, E) (𝓡 n) ∞
        (fun x : puncturedVectorSpace E => ((radialCylinderHomeomorph E).symm x).2) :=
      hval.codRestrict_sphere (fun x => ((radialCylinderHomeomorph E).symm x).2.property)
    exact hfst.prodMk hsnd

theorem radialCylinderDiffeomorph_apply (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (p : ℝ × sphere (0 : E) 1) :
    (radialCylinderDiffeomorph E n p).val = Real.exp p.1 • p.2.val := rfl

def radialCylinderChart (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : sphere (0 : E) 1) :
    PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (ℝ × sphere (0 : E) 1) E ∞ := by
  let _ : Nonempty (puncturedVectorSpace E) :=
    ⟨⟨u.val, ne_of_mem_sphere u.property one_ne_zero⟩⟩
  exact (radialCylinderDiffeomorph E n).toPartialDiffeomorph.trans
    (PartialChart.openInclusion (I := 𝓘(ℝ, E)) (puncturedVectorSpace E))

theorem radialCylinderChart_apply (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : sphere (0 : E) 1) (p : ℝ × sphere (0 : E) 1) :
    radialCylinderChart E n u p = Real.exp p.1 • p.2.val := rfl

theorem radialCylinderChart_mem_source (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : sphere (0 : E) 1) (p : ℝ × sphere (0 : E) 1) :
    p ∈ (radialCylinderChart E n u).source := ⟨mem_univ _, mem_univ _⟩

theorem radialCylinderChart_mem_target (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : sphere (0 : E) 1) (z : E) : z ∈ (radialCylinderChart E n u).target ↔ z ≠ 0 := by
  let _ : Nonempty (puncturedVectorSpace E) :=
    ⟨⟨u.val, ne_of_mem_sphere u.property one_ne_zero⟩⟩
  change (z ∈ (PartialChart.openInclusion (I := 𝓘(ℝ, E)) (puncturedVectorSpace E)).target ∧
    (PartialChart.openInclusion (I := 𝓘(ℝ, E)) (puncturedVectorSpace E)).symm z ∈ univ) ↔ z ≠ 0
  rw [PartialChart.openInclusion_target]
  exact ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩

theorem radialCylinderChart_symm_eq (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : sphere (0 : E) 1) (z : E) (hz : z ≠ 0) :
    (radialCylinderChart E n u).symm z = (radialCylinderHomeomorph E).symm ⟨z, hz⟩ := by
  let _ : Nonempty (puncturedVectorSpace E) :=
    ⟨⟨u.val, ne_of_mem_sphere u.property one_ne_zero⟩⟩
  change (radialCylinderDiffeomorph E n).symm
    ((PartialChart.openInclusion (I := 𝓘(ℝ, E)) (puncturedVectorSpace E)).symm z) = _
  have heq : (PartialChart.openInclusion (I := 𝓘(ℝ, E)) (puncturedVectorSpace E)).symm z =
      (⟨z, hz⟩ : puncturedVectorSpace E) :=
    Subtype.ext (PartialChart.openInclusion_symm_coe (I := 𝓘(ℝ, E)) (puncturedVectorSpace E) hz)
  rw [heq]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.PassageHomology
