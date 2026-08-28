import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

/-!
# Extending a sphere homeomorphism over the disk

The radial extension fixes zero and preserves the norm. Its continuity at
zero follows from this norm identity; no differentiability at zero is claimed.
This is the topological extension used after a two-disk decomposition.
-/

noncomputable section

open Set Metric Topology

namespace Wikipedia.SmoothSixDPoincare
namespace RadialExtension

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The unit direction of a nonzero vector. -/
def direction (x : E) (hx : x ≠ 0) : sphere (0 : E) 1 :=
  ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩

open Classical in
/-- The radial extension of a function between unit spheres. -/
def radial (f : sphere (0 : E) 1 → sphere (0 : F) 1) (x : E) : F :=
  if hx : x = 0 then 0 else ‖x‖ • (f (direction x hx) : F)

@[simp] theorem radial_zero (f : sphere (0 : E) 1 → sphere (0 : F) 1) :
    radial f 0 = 0 := by
  simp [radial]

theorem radial_of_ne_zero (f : sphere (0 : E) 1 → sphere (0 : F) 1)
    {x : E} (hx : x ≠ 0) : radial f x = ‖x‖ • (f (direction x hx) : F) := by
  simp [radial, hx]

@[simp] theorem norm_radial (f : sphere (0 : E) 1 → sphere (0 : F) 1) (x : E) :
    ‖radial f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp
  rw [radial_of_ne_zero f hx, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x), mem_sphere_zero_iff_norm.mp (f (direction x hx)).property,
    mul_one]

@[simp] theorem radial_eq_zero_iff (f : sphere (0 : E) 1 → sphere (0 : F) 1)
    (x : E) : radial f x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero, norm_radial, norm_eq_zero]

theorem direction_radial (f : sphere (0 : E) 1 → sphere (0 : F) 1)
    {x : E} (hx : x ≠ 0) :
    direction (radial f x) (fun h => hx ((radial_eq_zero_iff f x).mp h)) =
      f (direction x hx) := by
  apply Subtype.ext
  change ‖radial f x‖⁻¹ • radial f x = (f (direction x hx) : F)
  rw [norm_radial, radial_of_ne_zero f hx, inv_smul_smul₀ (norm_ne_zero_iff.mpr hx)]

@[simp] theorem radial_id (x : E) : radial id x = x := by
  by_cases hx : x = 0
  · subst x
    simp
  rw [radial_of_ne_zero id hx]
  exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) x

theorem radial_comp (g : sphere (0 : F) 1 → sphere (0 : G) 1)
    (f : sphere (0 : E) 1 → sphere (0 : F) 1) (x : E) :
    radial g (radial f x) = radial (g ∘ f) x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hy : radial f x ≠ 0 := fun h => hx ((radial_eq_zero_iff f x).mp h)
  rw [radial_of_ne_zero g hy, norm_radial, direction_radial f hx,
    radial_of_ne_zero (g ∘ f) hx]
  rfl

@[simp] theorem radial_on_sphere (f : sphere (0 : E) 1 → sphere (0 : F) 1)
    (x : sphere (0 : E) 1) : radial f x = (f x : F) := by
  have hn : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hx : (x : E) ≠ 0 := by
    intro h
    simp [h] at hn
  have hd : direction (x : E) hx = x := by
    apply Subtype.ext
    simp [direction, hn]
  rw [radial_of_ne_zero f hx, hn, hd, one_smul]

theorem continuous_radial {f : sphere (0 : E) 1 → sphere (0 : F) 1}
    (hf : Continuous f) : Continuous (radial f) := by
  have haway : ContinuousOn (radial f) ({0}ᶜ : Set E) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : ({0}ᶜ : Set E).domRestrict (radial f) =
        fun (x : ({0}ᶜ : Set E)) =>
          ‖(x : E)‖ • (f ((homeomorphUnitSphereProd E x).1) : F) := by
      funext x
      rw [Set.domRestrict_apply, radial_of_ne_zero f x.property]
      have hd : direction (x : E) x.property = (homeomorphUnitSphereProd E x).1 := by
        apply Subtype.ext
        simp [direction]
      rw [hd]
    rw [heq]
    exact continuous_subtype_val.norm.smul
      (continuous_subtype_val.comp (hf.comp (homeomorphUnitSphereProd E).continuous.fst))
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    simpa only [radial_zero, dist_zero_right, norm_radial] using hy
  exact (haway x hx).continuousAt (isOpen_compl_singleton.mem_nhds hx)

/-- A sphere homeomorphism extends to a norm-preserving ambient homeomorphism. -/
def homeomorph (e : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) : E ≃ₜ F where
  toFun := radial e
  invFun := radial e.symm
  left_inv x := by
    rw [radial_comp]
    have h : (e.symm : sphere (0 : F) 1 → sphere (0 : E) 1) ∘ e = id := by
      funext y
      exact e.symm_apply_apply y
    rw [h, radial_id]
  right_inv x := by
    rw [radial_comp]
    have h : (e : sphere (0 : E) 1 → sphere (0 : F) 1) ∘ e.symm = id := by
      funext y
      exact e.apply_symm_apply y
    rw [h, radial_id]
  continuous_toFun := continuous_radial e.continuous
  continuous_invFun := continuous_radial e.symm.continuous

/-- Restrict the radial homeomorphism to the actual closed unit balls. -/
def closedBallHomeomorph (e : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) :
    closedBall (0 : E) 1 ≃ₜ closedBall (0 : F) 1 :=
  (homeomorph e).sets (by
    ext x
    simp [homeomorph])

@[simp] theorem closedBallHomeomorph_apply_coe
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : closedBall (0 : E) 1) :
    (closedBallHomeomorph e x : F) = radial e x := rfl

@[simp] theorem closedBallHomeomorph_on_sphere
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : sphere (0 : E) 1) :
    closedBallHomeomorph e ⟨x, sphere_subset_closedBall x.property⟩ =
      ⟨e x, sphere_subset_closedBall (e x).property⟩ := by
  apply Subtype.ext
  exact radial_on_sphere e x

end RadialExtension
end Wikipedia.SmoothSixDPoincare
