import Wikipedia.NoExoticSixSphere.ImmersedDiskNormalObstruction
import Wikipedia.NoExoticSixSphere.SmoothDiskFrameExtension

/-!
# Normal-disk parity detects smooth extension with the original boundary frame

The normal spaces come from the actual derivative of the supplied smooth
immersed disk. For smooth boundary frame data the previously proved
continuous extension criterion is equivalent to smooth extension near the
closed disk, with exact boundary values and normality everywhere on the disk.
-/

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.Stiefel.ImmersedDisk

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable (r : ℕ) (f : Vector 4 → Vector (r + 9))

def ambientNormalProjection (x : Vector 4) : Vector (r + 9) →L[ℝ] Vector (r + 9) :=
  (fderiv ℝ f x).rangeᗮ.starProjection

theorem ambientNormalProjection_range (x : Vector 4) :
    (ambientNormalProjection r f x).range = (fderiv ℝ f x).rangeᗮ :=
  (fderiv ℝ f x).rangeᗮ.range_starProjection

theorem ambientNormalProjection_idempotent (x : Vector 4) :
    IsIdempotentElem (ambientNormalProjection r f x) :=
  (fderiv ℝ f x).rangeᗮ.isIdempotentElem_starProjection

theorem contDiffAt_ambientNormalProjection (x : Vector 4) (hf : ContDiffAt ℝ ∞ f x)
    (hi : Function.Injective (fderiv ℝ f x)) :
    ContDiffAt ℝ ∞ (ambientNormalProjection r f) x := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hg : ContDiffAt ℝ ∞ (fun y ↦ gramProjection (fderiv ℝ f y)) x :=
    (contMDiffAt_gramProjection (I := 𝓘(ℝ, Vector 4)) hd.contMDiffAt hi).contDiffAt
  have hnear : ∀ᶠ y in 𝓝 x, Function.Injective (fderiv ℝ f y) :=
    hd.continuousAt (ContinuousLinearMap.isOpen_injective.mem_nhds hi)
  have he : ambientNormalProjection r f =ᶠ[𝓝 x]
      (fun y ↦ 1 - gramProjection (fderiv ℝ f y)) := by
    filter_upwards [hnear] with y hy
    rw [ambientNormalProjection, Submodule.starProjection_orthogonal',
      gramProjection_eq_starProjection _ hy]
  exact (contDiffAt_const.sub hg).congr_of_eventuallyEq he

variable (hf : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ f x)
variable (hi : ∀ x ∈ closedBall (0 : Vector 4) 1, Function.Injective (fderiv ℝ f x))
variable (a : C(NoExoticSixSphere.Sphere 3, Space (r + 9) (r + 2)))
variable (ha : ∀ s, (a s).val.range ≤ (fderiv ℝ f s.val).rangeᗮ)

theorem parity_zero_iff_smooth_extension
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector (r + 2) →L[ℝ] Vector (r + 9)) ∞
      (fun s ↦ (a s).val)) :
    parity r f hf hi a ha = 0 ↔
      ∃ T : Vector 4 → Vector (r + 2) →L[ℝ] Vector (r + 9),
        (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, (T x).range ≤ (fderiv ℝ f x).rangeᗮ) ∧
        ∀ s, T s.val = (a s).val := by
  rw [parity_zero_iff_extension]
  constructor
  · rintro ⟨A, hAr, hAb⟩
    have hP (x : Vector 4) (_hx : x ∈ closedBall (0 : Vector 4) 1) :
        IsIdempotentElem (ambientNormalProjection r f x) :=
      ambientNormalProjection_idempotent r f x
    have hPs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
        ContDiffAt ℝ ∞ (ambientNormalProjection r f) x :=
      contDiffAt_ambientNormalProjection r f x (hf x hx) (hi x hx)
    have hrange (x : Disk (E := Vector 4)) :
        (A x).val.range ≤ (ambientNormalProjection r f x.val).range := by
      rw [ambientNormalProjection_range]
      exact hAr x
    obtain ⟨T, hTs, hTn, hTr, hTb⟩ := exists_smoothDiskFrame_extension
      (ambientNormalProjection r f) hP hPs a has A hrange hAb
    refine ⟨T, hTs, hTn, ?_, hTb⟩
    intro x hx
    simpa only [ambientNormalProjection_range] using hTr x hx
  · rintro ⟨T, hTs, hTn, hTr, hTb⟩
    have hc : Continuous (fun x : Disk (E := Vector 4) ↦ T x.val) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact (hTs x.val x.property).continuousAt.comp continuous_subtype_val.continuousAt
    let A : C(Disk (E := Vector 4), Space (r + 9) (r + 2)) :=
      ⟨fun x ↦ ⟨T x.val, hTn x.val x.property⟩, hc.subtype_mk _⟩
    exact ⟨A, fun x ↦ hTr x.val x.property, fun s ↦ Subtype.ext (hTb s)⟩

end NoExoticSixSphere.Stiefel.ImmersedDisk
