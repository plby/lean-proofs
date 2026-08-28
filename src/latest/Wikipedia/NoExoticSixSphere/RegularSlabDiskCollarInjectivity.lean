import Wikipedia.NoExoticSixSphere.RegularSlabDiskCollar
import Wikipedia.NoExoticSixSphere.SignedSphereCollarInjectivity

/-!
# Actual injectivity of the prescribed regular-slab disk collar

An injective boundary sphere in one endpoint has injective spatial part.
The exact signed collar formula then proves injectivity of the original
disk on its outer half-annulus. Any map retaining a smaller outer collar
inherits this injectivity, with no claim about its interior.
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

theorem injective_spatial_of_one_end (hi : Injective f)
    (hend : (∀ q, (f q).val.val.1 = s) ∨ ∀ q, (f q).val.val.1 = t) :
    Injective (spatial f) := by
  intro q r hqr
  apply hi
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rcases hend with hl | hr
    · exact (hl q).trans (hl r).symm
    · exact (hr q).trans (hr r).symm
  · exact Subtype.ext hqr

theorem injOn_disk_outer_collar (D : d.CollaredDiskExtension p f)
    (b : NoExoticSixSphere.Sphere p) (hi : Injective f)
    (hend : (∀ q, (f q).val.val.1 = s) ∨ ∀ q, (f q).val.val.1 = t) :
    InjOn (fun x : Disk (E := Vector (p + 1)) ↦ (D.map x).val)
      {x | 1 / 2 ≤ ‖x.val‖} := by
  have hsp := injective_spatial_of_one_end hi hend
  intro x hx y hy hxy
  have he : ambient D x = ambient D y :=
    congrArg (fun v : {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} ↦
      (v.val.1, v.val.2.val)) hxy
  apply Subtype.ext
  rcases hend with hl | hr
  · rw [ambient_eq_leftCollar D b hl x hx, ambient_eq_leftCollar D b hl y hy] at he
    exact SignedSphereCollar.injOn_outer_half b (spatial f) s (s - D.leftCut)
      (sub_ne_zero.mpr D.left_lt.ne) hsp hx hy he
  · rw [ambient_eq_rightCollar D b hr x hx, ambient_eq_rightCollar D b hr y hy] at he
    exact SignedSphereCollar.injOn_outer_half b (spatial f) t (t - D.rightCut)
      (sub_ne_zero.mpr D.right_lt.ne') hsp hx hy he

theorem injOn_of_eq_outer_collar (D : d.CollaredDiskExtension p f)
    (b : NoExoticSixSphere.Sphere p) (hi : Injective f)
    (hend : (∀ q, (f q).val.val.1 = s) ∨ ∀ q, (f q).val.val.1 = t)
    (ρ : ℝ) (hρ : 1 / 2 ≤ ρ)
    (g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (hfix : ∀ x : Disk (E := Vector (p + 1)), ρ ≤ ‖x.val‖ → g x.val = (D.map x).val) :
    InjOn g (closedBall 0 1 ∩ {x | ρ ≤ ‖x‖}) := by
  intro x hx y hy hxy
  let x' : Disk (E := Vector (p + 1)) := ⟨x, hx.1⟩
  let y' : Disk (E := Vector (p + 1)) := ⟨y, hy.1⟩
  have hx' : 1 / 2 ≤ ‖x'.val‖ := hρ.trans hx.2
  have hy' : 1 / 2 ≤ ‖y'.val‖ := hρ.trans hy.2
  have he : (D.map x').val = (D.map y').val := by
    rw [← hfix x' hx.2, ← hfix y' hy.2]
    exact hxy
  have heq : x' = y' := injOn_disk_outer_collar D b hi hend hx' hy' he
  exact congrArg (fun v : Disk (E := Vector (p + 1)) ↦ v.val) heq

end NoExoticSixSphere.RegularSlabDiskCollar
