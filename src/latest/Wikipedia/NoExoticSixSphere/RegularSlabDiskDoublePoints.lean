import Wikipedia.NoExoticSixSphere.DiskDoublePointCompactness
import Wikipedia.NoExoticSixSphere.RegularSlabDiskCollarInjectivity

/-!
# No boundary ends for the original regular-slab disk double points

The original boundary values lie in the actual endpoint fibers, whereas
every interior value has strictly intermediate time. This separates their
images. Together with the retained injective outer collar, it places the
entire double-point closure in the product of the open source disks.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularSlabDiskCollar

open GLOrthonormalization CylinderFiberSlab
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {m n p : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  {f : C(NoExoticSixSphere.Sphere p, slab d.map z s t)}

theorem interior_image_ne_boundary_image
    (g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (hboundary : ∀ q : NoExoticSixSphere.Sphere p, g q.val = (f q).val)
    (hends : ∀ q, f q ∈ BoundaryPush.ends d.map z s t)
    (hinterior : ∀ x ∈ ball 0 1, (g x).val.1 ∈ Ioo s t) :
    ∀ x ∈ ball 0 1, ∀ y ∈ sphere 0 1, g x ≠ g y := by
  intro x hx y hy he
  let q : NoExoticSixSphere.Sphere p := ⟨y, hy⟩
  have heq : g x = (f q).val := he.trans (hboundary q)
  have htime := congrArg
    (fun v : {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} ↦ v.val.1) heq
  have hxt := hinterior x hx
  rcases hends q with hl | hr
  · exact (htime.trans hl).not_gt hxt.1
  · exact (htime.trans hr).not_lt hxt.2

theorem doublePointClosure_subset_interior (D : d.CollaredDiskExtension p f)
    (b : NoExoticSixSphere.Sphere p) (hi : Injective f)
    (hend : (∀ q, (f q).val.val.1 = s) ∨ ∀ q, (f q).val.val.1 = t)
    (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1)
    (g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (hg : ContinuousOn g (closedBall 0 1))
    (hboundary : ∀ q : NoExoticSixSphere.Sphere p, g q.val = (f q).val)
    (hfix : ∀ x : Disk (E := Vector (p + 1)), ρ ≤ ‖x.val‖ → g x.val = (D.map x).val)
    (hinterior : ∀ x ∈ ball 0 1, (g x).val.1 ∈ Ioo s t) :
    closure (DiskDoublePoints.points g) ⊆ ball 0 1 ×ˢ ball 0 1 := by
  apply DiskDoublePoints.closure_subset_interior g hg ρ hρ1
    (injOn_of_eq_outer_collar D b hi hend ρ hρ g hfix)
  apply interior_image_ne_boundary_image g hboundary _ hinterior
  intro q
  rcases hend with hl | hr
  · exact Or.inl (hl q)
  · exact Or.inr (hr q)

end NoExoticSixSphere.RegularSlabDiskCollar
