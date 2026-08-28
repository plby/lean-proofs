import Wikipedia.NoExoticSixSphere.FramedSlabData

/-!
# A framed slab with an empty outgoing fiber

If the right endpoint map misses the regular value, the actual manifold
boundary is just the left fiber, with its original regular-fiber atlas.
The boundary diffeomorphism retains the exact endpoint and normal-frame formulas.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData

variable {m n k : ℕ} {b : Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b s t}
  {hd : m = n + k} {a : Sphere m} (A : d.FramedSlabData k hd a)
  (hmiss : ∀ x, d.rightMap x ≠ b)

include hmiss in
theorem time_ne_right (p : CylinderFiberSlab.slab d.map b s t) : p.val.val.1 ≠ t := by
  intro hp
  exact hmiss p.val.val.2 (d.rightMap_eq_value_of_time p hp)

include hmiss in
theorem boundary_iff_left :
    letI := A.atlas;
    ∀ p : CylinderFiberSlab.slab d.map b s t,
      ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p ↔ p.val.val.1 = s := by
  let := A.atlas
  intro p
  rw [A.boundary_iff p, or_iff_left (time_ne_right hmiss p)]

noncomputable def leftBoundaryDiffeomorph :
    letI := A.atlas;
    letI := A.boundaryAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    {x : Sphere m // d.leftMap x = b} ≃ₘ⟮𝓡 k, 𝓡 k⟯
      {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p} := by
  letI := A.atlas
  letI := A.boundaryAtlas
  letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  letI : IsEmpty {x : Sphere m // d.rightMap x = b} := ⟨fun x ↦ hmiss x.val x.property⟩
  exact (Diffeomorph.sumEmpty (𝓡 k) {x : Sphere m // d.leftMap x = b}
    (M' := {x : Sphere m // d.rightMap x = b}) ∞).symm.trans A.boundaryDiffeomorph

theorem leftBoundaryDiffeomorph_val (x : {x : Sphere m // d.leftMap x = b}) :
    letI := A.atlas;
    letI := A.boundaryAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (A.leftBoundaryDiffeomorph hmiss x).val = (d.leftEndpoint x).val := by
  exact A.boundary_left x

theorem leftBoundaryDiffeomorph_frame (x : {x : Sphere m // d.leftMap x = b}) :
    letI := A.atlas;
    letI := A.boundaryAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    A.frame.ambient (A.leftBoundaryDiffeomorph hmiss x).val =
      CylinderNormalFrame.liftFrame
        ((SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b
          d.regular_left k hd a).ambient x) := by
  let := A.atlas
  let := A.boundaryAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  rw [A.leftBoundaryDiffeomorph_val hmiss x]
  exact A.frame_left x

end NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData
