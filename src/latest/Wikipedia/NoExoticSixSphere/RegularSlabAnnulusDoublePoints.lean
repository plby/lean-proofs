import Wikipedia.NoExoticSixSphere.AnnulusDoublePointCompactness
import Wikipedia.NoExoticSixSphere.RegularSlabAnnulusCollars

/-!
# No boundary ends for the original slab-cylinder double points

The radius-one and radius-two spheres retain their actual left and right
endpoint values. Their time coordinates are the original slab endpoints,
whereas all interior values have strictly intermediate time. This gives
the separation needed to keep the actual double-point closure inside the
open annulus product, using injectivity of the union of both end collars.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularSlabCylinderCollar

open GLOrthonormalization CylinderFiberSlab SphereAnnulus

variable {m n p : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  {f₀ f₁ : C(NoExoticSixSphere.Sphere p, slab d.map z s t)}

theorem interior_image_ne_either_boundary_image
    (g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (hboundary₀ : ∀ q : NoExoticSixSphere.Sphere p, g q.val = (f₀ q).val)
    (hboundary₁ : ∀ q : NoExoticSixSphere.Sphere p, g ((2 : ℝ) • q.val) = (f₁ q).val)
    (h₀ : ∀ q, (f₀ q).val.val.1 = s) (h₁ : ∀ q, (f₁ q).val.val.1 = t)
    (hinterior : ∀ x, 1 < ‖x‖ → ‖x‖ < 2 → (g x).val.1 ∈ Ioo s t) :
    ∀ x ∈ openDomain p, ∀ y, ‖y‖ = 1 ∨ ‖y‖ = 2 → g x ≠ g y := by
  intro x hx y hy he
  have hxt := hinterior x hx.1 hx.2
  rcases hy with hy | hy
  · let q : NoExoticSixSphere.Sphere p := ⟨y, mem_sphere_zero_iff_norm.mpr hy⟩
    have heq : g x = (f₀ q).val := he.trans (hboundary₀ q)
    have htime := congrArg
      (fun v : {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} ↦ v.val.1) heq
    exact (htime.trans (h₀ q)).not_gt hxt.1
  · let q : NoExoticSixSphere.Sphere p := ⟨(1 / 2 : ℝ) • y, by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul, hy]
      norm_num⟩
    have hq : (2 : ℝ) • q.val = y := by
      change (2 : ℝ) • ((1 / 2 : ℝ) • y) = y
      rw [smul_smul]
      norm_num
    have hb : g y = (f₁ q).val := by simpa only [hq] using hboundary₁ q
    have heq : g x = (f₁ q).val := he.trans hb
    have htime := congrArg
      (fun v : {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} ↦ v.val.1) heq
    exact (htime.trans (h₁ q)).not_lt hxt.2

theorem doublePointClosure_subset_interior
    (g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (hg : ContinuousOn g (domain p))
    (hboundary₀ : ∀ q : NoExoticSixSphere.Sphere p, g q.val = (f₀ q).val)
    (hboundary₁ : ∀ q : NoExoticSixSphere.Sphere p, g ((2 : ℝ) • q.val) = (f₁ q).val)
    (h₀ : ∀ q, (f₀ q).val.val.1 = s) (h₁ : ∀ q, (f₁ q).val.val.1 = t)
    (r₀ r₁ : ℝ) (hr₀ : 1 < r₀) (hr₁ : r₁ < 2)
    (hi : InjOn g {x | x ∈ domain p ∧ (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖)})
    (hinterior : ∀ x, 1 < ‖x‖ → ‖x‖ < 2 → (g x).val.1 ∈ Ioo s t) :
    closure (AnnulusDoublePoints.points g) ⊆ openDomain p ×ˢ openDomain p := by
  apply AnnulusDoublePoints.closure_subset_interior g hg r₀ r₁ hr₀ hr₁ hi
  exact interior_image_ne_either_boundary_image g hboundary₀ hboundary₁ h₀ h₁ hinterior

end NoExoticSixSphere.RegularSlabCylinderCollar
