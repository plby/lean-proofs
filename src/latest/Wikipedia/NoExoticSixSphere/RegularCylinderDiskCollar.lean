import Wikipedia.NoExoticSixSphere.RegularCylinderFiberCollarCoordinates
import Wikipedia.NoExoticSixSphere.RegularSlabDiskCollar
import Wikipedia.NoExoticSixSphere.ClosedDiskCollarDerivative

/-!
# Actual disk derivatives in height-last regular-cylinder coordinates

Translate the chosen endpoint time to zero and move height to the last
coordinate. Smoothness is inherited from the original regular-fiber atlas.
The exact retained closed-disk collar determines the ordinary derivative
at every boundary point. Its height derivative has the actual endpoint
sign, without any assertion of immersion in the disk interior.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularSlabDiskCollar

open GLOrthonormalization CylinderFiberSlab RegularCylinderFiber
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {m n : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}

def collarDisk (c : ℝ)
    (g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z}) :
    Vector 4 → Vector (m + 1) × ℝ :=
  fun x ↦ ((g x).val.2.val, (g x).val.1 - c)

theorem collarDisk_eq (hd : m = n + 6) (c : ℝ)
    (g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z}) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
      (CylinderFiberNormalFrame.dimension_eq hd)
    collarDisk c g = fun x ↦ collarTargetCoordinates m
      ((embedding d.map d.smooth_map z d.regular_map 6 hd).toFun (g x)) - (0, c) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  funext x
  rw [embedding_apply, collarTargetCoordinates_coordinates]
  exact Prod.ext (sub_zero _).symm rfl

theorem contDiffAt_collarDisk (hd : m = n + 6) (c : ℝ)
    (g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (x : Vector 4) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
      (CylinderFiberNormalFrame.dimension_eq hd)
    ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x → ContDiffAt ℝ ∞ (collarDisk c g) x := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  intro hg
  rw [collarDisk_eq hd]
  have he := (embedding d.map d.smooth_map z d.regular_map 6 hd).smooth.contMDiffAt.comp x hg
  exact ((collarTargetCoordinates m).contDiff.contDiffAt.comp x
    he.contDiffAt).sub contDiffAt_const

theorem fderiv_collarDisk (hd : m = n + 6) (c : ℝ)
    (g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (x : Vector 4) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
      (CylinderFiberNormalFrame.dimension_eq hd)
    ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x →
      fderiv ℝ (collarDisk c g) x = (collarTargetCoordinates m).toContinuousLinearMap.comp
        (fderiv ℝ ((embedding d.map d.smooth_map z d.regular_map 6 hd).toFun ∘ g) x) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  intro hg
  rw [collarDisk_eq hd, fderiv_sub_const]
  have he := (embedding d.map d.smooth_map z d.regular_map 6 hd).smooth.contMDiffAt.comp x hg
  exact ((collarTargetCoordinates m).hasFDerivAt.comp x
    (he.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv

variable {f : C(NoExoticSixSphere.Sphere 3, slab d.map z s t)}
  (D : d.CollaredDiskExtension 3 f) (b : NoExoticSixSphere.Sphere 3)

def shiftedCollar (c : ℝ) (H : Vector 4 → ℝ × Vector (m + 1)) :
    Vector 4 → Vector (m + 1) × ℝ := fun x ↦ ((H x).2, (H x).1 - c)

theorem shiftedCollar_eq (c : ℝ) (H : Vector 4 → ℝ × Vector (m + 1)) :
    shiftedCollar c H = fun x ↦
      ContinuousLinearEquiv.prodComm ℝ ℝ (Vector (m + 1)) (H x) - (0, c) := by
  funext x
  exact Prod.ext (sub_zero _).symm rfl

theorem contDiff_shiftedCollar (c : ℝ) (H : Vector 4 → ℝ × Vector (m + 1))
    (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (shiftedCollar c H) := by
  rw [shiftedCollar_eq]
  exact ((ContinuousLinearEquiv.prodComm ℝ ℝ (Vector (m + 1))).contDiff.comp hH).sub
    contDiff_const

theorem fderiv_shiftedCollar (c : ℝ) (H : Vector 4 → ℝ × Vector (m + 1))
    {x : Vector 4} (hH : DifferentiableAt ℝ H x) (v : Vector 4) :
    fderiv ℝ (shiftedCollar c H) x v =
      ((fderiv ℝ H x v).2, (fderiv ℝ H x v).1) := by
  rw [shiftedCollar_eq, fderiv_sub_const]
  change fderiv ℝ ((ContinuousLinearEquiv.prodComm ℝ ℝ (Vector (m + 1))) ∘ H) x v = _
  rw [((ContinuousLinearEquiv.prodComm ℝ ℝ (Vector (m + 1))).hasFDerivAt.comp x
    hH.hasFDerivAt).fderiv]
  rfl

theorem fderiv_collarDisk_eq_left (c : ℝ)
    (g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (hgs : ∀ x ∈ closedBall 0 1, ContDiffAt ℝ ∞ (collarDisk c g) x)
    (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1)
    (hgc : ∀ x : Disk (E := Vector 4), ρ ≤ ‖x.val‖ → g x.val = (D.map x).val)
    (hf : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f))
    (hend : ∀ q, (f q).val.val.1 = s) (q : NoExoticSixSphere.Sphere 3) :
    fderiv ℝ (collarDisk c g) q.val = fderiv ℝ (shiftedCollar c (leftCollar D b)) q.val := by
  apply fderiv_eq_of_closedBall_collar _ _ ρ
  · intro x hx hxr
    have he := ambient_eq_leftCollar D b hend ⟨x, hx⟩ (hρ.trans hxr)
    have hg := hgc ⟨x, hx⟩ hxr
    change ((g x).val.2.val, (g x).val.1 - c) =
      ((leftCollar D b x).2, (leftCollar D b x).1 - c)
    rw [hg, ← he]
    rfl
  · exact sphere_subset_closedBall q.property
  · simpa only [ClosedHemisphere.unit_norm] using hρ1
  · exact (hgs q.val (sphere_subset_closedBall q.property)).differentiableAt (by simp)
  · exact (contDiff_shiftedCollar c _ (contDiff_leftCollar D b hf)).differentiable
      (by simp) q.val

theorem fderiv_collarDisk_eq_right (c : ℝ)
    (g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (hgs : ∀ x ∈ closedBall 0 1, ContDiffAt ℝ ∞ (collarDisk c g) x)
    (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1)
    (hgc : ∀ x : Disk (E := Vector 4), ρ ≤ ‖x.val‖ → g x.val = (D.map x).val)
    (hf : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f))
    (hend : ∀ q, (f q).val.val.1 = t) (q : NoExoticSixSphere.Sphere 3) :
    fderiv ℝ (collarDisk c g) q.val = fderiv ℝ (shiftedCollar c (rightCollar D b)) q.val := by
  apply fderiv_eq_of_closedBall_collar _ _ ρ
  · intro x hx hxr
    have he := ambient_eq_rightCollar D b hend ⟨x, hx⟩ (hρ.trans hxr)
    have hg := hgc ⟨x, hx⟩ hxr
    change ((g x).val.2.val, (g x).val.1 - c) =
      ((rightCollar D b x).2, (rightCollar D b x).1 - c)
    rw [hg, ← he]
    rfl
  · exact sphere_subset_closedBall q.property
  · simpa only [ClosedHemisphere.unit_norm] using hρ1
  · exact (hgs q.val (sphere_subset_closedBall q.property)).differentiableAt (by simp)
  · exact (contDiff_shiftedCollar c _ (contDiff_rightCollar D b hf)).differentiable
      (by simp) q.val

include b in
theorem collarDisk_left_height_negative (c : ℝ)
    (g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (hgs : ∀ x ∈ closedBall 0 1, ContDiffAt ℝ ∞ (collarDisk c g) x)
    (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1)
    (hgc : ∀ x : Disk (E := Vector 4), ρ ≤ ‖x.val‖ → g x.val = (D.map x).val)
    (hf : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f))
    (hend : ∀ q, (f q).val.val.1 = s) (q : NoExoticSixSphere.Sphere 3) :
    (fderiv ℝ (collarDisk c g) q.val q.val).2 < 0 := by
  rw [fderiv_collarDisk_eq_left D b c g hgs ρ hρ hρ1 hgc hf hend q,
    fderiv_shiftedCollar c _ ((contDiff_leftCollar D b hf).differentiable (by simp) q.val),
    fderiv_leftCollar_radial D b hf]
  change 2 * (s - D.leftCut) < 0
  linarith [D.left_lt]

include b in
theorem collarDisk_right_height_positive (c : ℝ)
    (g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (hgs : ∀ x ∈ closedBall 0 1, ContDiffAt ℝ ∞ (collarDisk c g) x)
    (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1)
    (hgc : ∀ x : Disk (E := Vector 4), ρ ≤ ‖x.val‖ → g x.val = (D.map x).val)
    (hf : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f))
    (hend : ∀ q, (f q).val.val.1 = t) (q : NoExoticSixSphere.Sphere 3) :
    0 < (fderiv ℝ (collarDisk c g) q.val q.val).2 := by
  rw [fderiv_collarDisk_eq_right D b c g hgs ρ hρ hρ1 hgc hf hend q,
    fderiv_shiftedCollar c _ ((contDiff_rightCollar D b hf).differentiable (by simp) q.val),
    fderiv_rightCollar_radial D b hf]
  change 0 < 2 * (t - D.rightCut)
  linarith [D.right_lt]

end NoExoticSixSphere.RegularSlabDiskCollar
