import Wikipedia.HopfProblem.DegreeCollapseRadialSphereAction

/-!
# The canonical radial extension of an actual sphere map

The extension preserves norms, is continuous at the origin, and is
positively homogeneous. These are actual function identities, used to
compare adding Euclidean coordinates with the original suspensions.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere Set Filter

namespace Wikipedia.HopfProblem.DegreeCollapse.RadialSphereMap

open RadialSphereAction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def extend (f : C(UnitSphere E, UnitSphere F)) (x : E) : F := by
  classical
  exact if hx : x = 0 then 0 else ‖x‖ • (f (direction x hx)).val

theorem extend_zero (f : C(UnitSphere E, UnitSphere F)) : extend f 0 = 0 := by
  simp [extend]

theorem extend_of_ne_zero (f : C(UnitSphere E, UnitSphere F)) (x : E) (hx : x ≠ 0) :
    extend f x = ‖x‖ • (f (direction x hx)).val := by
  simp only [extend, dif_neg hx]

theorem extend_norm (f : C(UnitSphere E, UnitSphere F)) (x : E) : ‖extend f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [extend_zero, norm_zero]
  · rw [extend_of_ne_zero f x hx, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x), mem_sphere_zero_iff_norm.mp (f (direction x hx)).property,
      mul_one]

theorem continuous_extend (f : C(UnitSphere E, UnitSphere F)) : Continuous (extend f) := by
  let U : Set E := {x | x ≠ 0}
  have hU : IsOpen U := isOpen_ne
  have ha : ContinuousOn (extend f) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    let d : U → UnitSphere E := fun x ↦ direction x.val x.property
    have hd : Continuous d := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.norm.inv₀
        (fun x : U ↦ norm_ne_zero_iff.mpr x.property)).smul continuous_subtype_val
    have hf : Continuous (fun x : U ↦ (f (d x)).val) :=
      continuous_subtype_val.comp (f.continuous.comp hd)
    convert continuous_subtype_val.norm.smul hf using 1
    funext x
    exact extend_of_ne_zero f x.val x.property
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    change Tendsto _ (𝓝 0) (𝓝 (extend f 0))
    rw [extend_zero]
    apply squeeze_zero_norm (fun y : E ↦ (extend_norm f y).le)
    have ht : Tendsto (norm : E → ℝ) (𝓝 0) (𝓝 ‖(0 : E)‖) := continuous_norm.continuousAt
    simpa only [norm_zero] using ht
  · exact ha.continuousAt (hU.mem_nhds hx)

def extension (f : C(UnitSphere E, UnitSphere F)) : C(E, F) := ⟨extend f, continuous_extend f⟩

theorem extend_unit (f : C(UnitSphere E, UnitSphere F)) (x : UnitSphere E) :
    extend f x.val = (f x).val := by
  have hx : x.val ≠ 0 := ne_zero_of_mem_unit_sphere x
  rw [extend_of_ne_zero f x.val hx]
  have hd : direction x.val hx = x :=
    Subtype.ext (NormedSpace.normalize_eq_self_of_norm_eq_one
      (mem_sphere_zero_iff_norm.mp x.property))
  rw [hd, mem_sphere_zero_iff_norm.mp x.property, one_smul]

theorem extend_smul_nonneg (f : C(UnitSphere E, UnitSphere F))
    (c : ℝ) (hc : 0 ≤ c) (x : E) : extend f (c • x) = c • extend f x := by
  by_cases hc0 : c = 0
  · subst c
    rw [zero_smul, extend_zero, zero_smul]
  by_cases hx : x = 0
  · subst x
    rw [smul_zero, extend_zero, smul_zero]
  have hcx : c • x ≠ 0 := smul_ne_zero hc0 hx
  have hd : direction (c • x) hcx = direction x hx :=
    Subtype.ext (NormedSpace.normalize_smul_of_pos (lt_of_le_of_ne hc (Ne.symm hc0)) x)
  rw [extend_of_ne_zero f (c • x) hcx, extend_of_ne_zero f x hx, hd, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hc, smul_smul]

theorem extend_smul_unit (f : C(UnitSphere E, UnitSphere F))
    (c : ℝ) (hc : 0 ≤ c) (x : UnitSphere E) :
    extend f (c • x.val) = c • (f x).val := by
  rw [extend_smul_nonneg f c hc, extend_unit]

theorem extend_unique (f : C(UnitSphere E, UnitSphere F)) (v : E → F)
    (hzero : v 0 = 0) (hhom : ∀ (c : ℝ), 0 ≤ c → ∀ x, v (c • x) = c • v x)
    (hunit : ∀ x : UnitSphere E, v x.val = (f x).val) (x : E) : extend f x = v x := by
  by_cases hx : x = 0
  · subst x
    rw [extend_zero, hzero]
  · rw [extend_of_ne_zero f x hx, ← hunit (direction x hx),
      ← hhom ‖x‖ (norm_nonneg x)]
    exact congrArg v (NormedSpace.norm_smul_normalize x)

end Wikipedia.HopfProblem.DegreeCollapse.RadialSphereMap
