import Wikipedia.HopfProblem.DegreeCollapsePuncturedCylinderCoordinates

/-!
# The endpoint-plus-link relation in the original punctured parameter cylinder

Radial coordinates transport the proved two-point-complement relation back
to the actual slices at time zero and one. The linking sphere may have any
sufficiently small positive radius. Postcomposition gives the relation for
every continuous trace defined on the original punctured cylinder.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.PassageHomology

open SingularMayerVietoris PeriodTorusHigherHomology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem punctured_cylinder_endpoint_relation {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (u : sphere (0 : E) 1) {ε : ℝ} (hε : 0 < ε) (hεu : ε < Real.exp τ)
    (n : ℕ) (hn : n ≠ 0) :
    singularHomologyMap (cylinderSlice τ u 1 hτ.2.ne') n =
      singularHomologyMap (cylinderSlice τ u 0 hτ.1.ne) n +
        singularHomologyMap (cylinderLink τ u ε hε hεu) n := by
  let b := cylinderPuncture τ u
  have hrb : (1 : ℝ) < ‖b‖ := by
    rw [norm_cylinderPuncture]
    exact Real.one_lt_exp_iff.mpr hτ.1
  have hbR : ‖b‖ < Real.exp 1 := by
    rw [norm_cylinderPuncture]
    exact Real.exp_lt_exp.mpr hτ.2
  have hεb : ε < ‖b‖ := by rwa [norm_cylinderPuncture]
  let inner := innerSphere b 1 zero_lt_one hrb
  let outer := outerSphere b (Real.exp 1) hbR
  let link := linkingSphere b ε hε hεb
  let e := puncturedCylinderHomeomorph τ u
  let e' : C(twoPunctureSet 0 b, ({(τ, u)}ᶜ : Set (ℝ × sphere (0 : E) 1))) := e.symm
  have hinner : e'.comp inner = cylinderSlice τ u 0 hτ.1.ne := by
    apply ContinuousMap.ext
    intro v
    apply e.injective
    change e (e.symm (inner v)) = e (cylinderSlice τ u 0 hτ.1.ne v)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (0 : E) + 1 • v.val = Real.exp 0 • v.val
    rw [Real.exp_zero, one_smul, zero_add]
  have houter : e'.comp outer = cylinderSlice τ u 1 hτ.2.ne' := by
    apply ContinuousMap.ext
    intro v
    apply e.injective
    change e (e.symm (outer v)) = e (cylinderSlice τ u 1 hτ.2.ne' v)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (0 : E) + Real.exp 1 • v.val = Real.exp 1 • v.val
    rw [zero_add]
  have H : singularHomologyMap (e'.comp outer) n =
      singularHomologyMap (e'.comp inner) n + singularHomologyMap (e'.comp link) n := by
    rw [singularHomologyMap_comp, singularHomologyMap_comp, singularHomologyMap_comp]
    have hrel := radial_sphere_homology_relation b zero_lt_one hrb hbR hε hεb n hn
    change (singularHomologyMap e' n).comp (singularHomologyMap outer n) = _
    rw [hrel, LinearMap.comp_add]
  rw [hinner, houter] at H
  exact H

theorem punctured_cylinder_trace_relation {Y : Type} [TopologicalSpace Y]
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (u : sphere (0 : E) 1)
    {ε : ℝ} (hε : 0 < ε) (hεu : ε < Real.exp τ)
    (F : C(({(τ, u)}ᶜ : Set (ℝ × sphere (0 : E) 1)), Y)) (n : ℕ) (hn : n ≠ 0) :
    singularHomologyMap (F.comp (cylinderSlice τ u 1 hτ.2.ne')) n =
      singularHomologyMap (F.comp (cylinderSlice τ u 0 hτ.1.ne)) n +
        singularHomologyMap (F.comp (cylinderLink τ u ε hε hεu)) n := by
  rw [singularHomologyMap_comp, singularHomologyMap_comp, singularHomologyMap_comp,
    punctured_cylinder_endpoint_relation hτ u hε hεu n hn, LinearMap.comp_add]

end Wikipedia.HopfProblem.DegreeCollapse.PassageHomology
