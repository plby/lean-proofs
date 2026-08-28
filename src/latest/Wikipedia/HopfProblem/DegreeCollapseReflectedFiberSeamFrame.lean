import Wikipedia.HopfProblem.DegreeCollapseReflectedFiberManifold
import Wikipedia.NoExoticSixSphere.CylinderFrameCollar

/-!
# The native reflected fiber retains the original frame on its seam collar

The time preimage of the actual left collar is an open neighborhood of the
seam. On this whole collar the constructed normal frame is exactly the
original endpoint-fiber frame with zero time component.
-/

noncomputable section

open Function Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def seamCollarTimes : Opens ℝ :=
  ⟨foldTime ⁻¹' d.leftTimes, d.leftTimes.isOpen.preimage continuous_foldTime⟩

theorem zero_mem_seamCollarTimes : (0 : ℝ) ∈ seamCollarTimes d := by
  change foldTime 0 ∈ d.leftTimes
  rw [foldTime_zero]
  exact d.left_mem

theorem map_on_seamCollar (t : ℝ) (ht : t ∈ seamCollarTimes d) (x : Sphere m) :
    map d (t, x) = d.leftMap x := d.left_eq (foldTime t) ht x

def seamCollarPoint (t : ℝ) (ht : t ∈ seamCollarTimes d)
    (x : {x : Sphere m // d.leftMap x = b}) : Fiber d :=
  ⟨(t, x.val), (map_on_seamCollar d t ht x.val).trans x.property⟩

theorem seamCollarPoint_ambient (t : ℝ) (ht : t ∈ seamCollarTimes d)
    (x : {x : Sphere m // d.leftMap x = b}) :
    ambientInclusion d (seamCollarPoint d t ht x) = WithLp.toLp 2 (t, x.val.val) := rfl

theorem normalFrame_seamCollar (k : ℕ) (hd : m = n + k) (a : Sphere m)
    (t : ℝ) (ht : t ∈ seamCollarTimes d) (x : {x : Sphere m // d.leftMap x = b}) :
    letI := fiberAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (normalFrame d k hd a).ambient (seamCollarPoint d t ht x) =
      CylinderNormalFrame.liftFrame
        ((SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b
          d.regular_left k hd a).ambient x) :=
  CylinderFiberNormalFrame.normalFrame_ambient_on_collar (map d) d.leftMap b a
    (map_on_seamCollar d) (contMDiff_map d) d.smooth_left (regular_map d) d.regular_left
    k hd (seamCollarTimes d).isOpen t ht x

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
