import Wikipedia.NoExoticSixSphere.CircleCylinderSeam

/-!
# Regularity of the circle seam and the retained cylinder differential

At a seam point the rotation tangent has nonzero second coordinate.
The original endpoint germ makes every circle tangent invisible to
the doubled cylinder map. These are the two differential facts needed
to make seam time regular on the native compact fiber.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

local instance : Fact (Module.finrank ℝ V = 1 + 1) := ⟨finrank_euclideanSpace_fin⟩

theorem mfderiv_seam (c : Sphere 1) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) seam c =
      seamLinear.comp (mfderiv (𝓡 1) 𝓘(ℝ, V) (Subtype.val : Sphere 1 → V) c) := by
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, V) ∞ (Subtype.val : Sphere 1 → V) :=
    contMDiff_coe_sphere
  change mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (seamLinear ∘ Subtype.val) c = _
  rw [mfderiv_comp c seamLinear.differentiableAt.mdifferentiableAt
    (hc.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, seamLinear.fderiv]
  rfl

theorem surjective_mfderiv_seam (c : Sphere 1) (hc : seam c = 0) :
    Surjective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) seam c) := by
  let D : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := mfderiv (𝓡 1) 𝓘(ℝ, ℝ) seam c
  let A : EuclideanSpace ℝ (Fin 1) →L[ℝ] V :=
    mfderiv (𝓡 1) 𝓘(ℝ, V) (Subtype.val : Sphere 1 → V) c
  have hD : D = seamLinear.comp A := mfderiv_seam c
  have hA : A.range = (ℝ ∙ c.val)ᗮ := inclusion_range c
  have hh : c.val 0 ≠ 0 := by
    rcases (seam_eq_zero_iff c).mp hc with rfl | rfl <;>
      norm_num [SphereCylinder.endPole_head]
  have hv := tangent_orthogonal c
  rw [← hA] at hv
  obtain ⟨u, hu⟩ := hv
  change A u = tangent c at hu
  have hd : D u = c.val 0 := by
    rw [hD, ContinuousLinearMap.comp_apply, hu]
    rfl
  change Surjective D
  intro z
  refine ⟨(z / c.val 0) • u, ?_⟩
  rw [map_smul, hd]
  exact div_mul_cancel₀ z hh

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem mfderiv_map_circle_zero (p : Sphere 1 × Sphere m) (hp : seam p.1 = 0)
    (u : EuclideanSpace ℝ (Fin 1)) :
    mfderiv ((𝓡 1).prod (𝓡 m)) (𝓡 n) (map d) p (u, 0) = 0 := by
  rcases (seam_eq_zero_iff p.1).mp hp with hl | hr
  · have he := left_germ d p (hl ▸ clock_left)
    rw [he.mfderiv_eq]
    change mfderiv ((𝓡 1).prod (𝓡 m)) (𝓡 n) (d.leftMap ∘ Prod.snd) p (u, 0) = 0
    rw [mfderiv_comp p (d.smooth_left.mdifferentiableAt (by simp))
      mdifferentiableAt_snd, mfderiv_snd]
    change mfderiv (𝓡 m) (𝓡 n) d.leftMap p.2 0 = 0
    exact map_zero _
  · have he := right_germ d p (hr ▸ clock_right)
    rw [he.mfderiv_eq]
    change mfderiv ((𝓡 1).prod (𝓡 m)) (𝓡 n) (d.rightMap ∘ Prod.snd) p (u, 0) = 0
    rw [mfderiv_comp p (d.smooth_right.mdifferentiableAt (by simp))
      mdifferentiableAt_snd, mfderiv_snd]
    change mfderiv (𝓡 m) (𝓡 n) d.rightMap p.2 0 = 0
    exact map_zero _

end NoExoticSixSphere.CircleCylinder
