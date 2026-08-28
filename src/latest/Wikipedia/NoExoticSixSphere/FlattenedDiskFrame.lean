import Wikipedia.NoExoticSixSphere.FlattenedDiskData
import Wikipedia.NoExoticSixSphere.SpanningDiskDimension

/-!
# Extending the original disk's normal frame over the flattened spanning disk

The old normal columns are evaluated at the radially flattened point and
the five unused graph directions are constant columns. This is an explicit
smooth frame in the normal spaces of the actual constructed disk derivative.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.FlattenedSpanningDisk

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {N k : ℕ}

def frameExtension (W : Vector 4 → Space N k) (x : Vector 4) :
    Vector (k + 5) →L[ℝ] Vector (N + 6) :=
  boundaryFrameOperator (W (DiskRadialFlattening.map 3 x)).val

theorem contDiff_frameExtension (W : Vector 4 → Space N k)
    (hW : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ (fun y ↦ (W y).val) x) :
    ContDiff ℝ ∞ (frameExtension W) := by
  have hs : ContDiff ℝ ∞ (fun x : Vector 4 ↦ (W (DiskRadialFlattening.map 3 x)).val) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hW _ (DiskRadialFlattening.map_mem_closedBall 3 x)).comp x
      (DiskRadialFlattening.contDiff_map 3).contDiffAt
  exact (contMDiff_boundaryFrameOperator hs.contMDiff).contDiff

theorem norm_frameExtension (W : Vector 4 → Space N k) (x : Vector 4) (w : Vector (k + 5)) :
    ‖frameExtension W x w‖ = ‖w‖ :=
  norm_boundaryFrameOperator (W (DiskRadialFlattening.map 3 x)) w

theorem frameExtension_normal (F : Vector 4 → Vector N) (W : Vector 4 → Space N k)
    (x : Vector 4) (hF : ContDiffAt ℝ ∞ F (DiskRadialFlattening.map 3 x))
    (hW : (W (DiskRadialFlattening.map 3 x)).val.range ≤
      (fderiv ℝ F (DiskRadialFlattening.map 3 x)).rangeᗮ) :
    (frameExtension W x).range ≤ (fderiv ℝ (map F) x).rangeᗮ := by
  rintro _ ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ (fderiv ℝ (map F) x v)
    (boundaryFrameOperator (W (DiskRadialFlattening.map 3 x)).val w) = 0
  rw [fderiv_map_apply F x v hF, boundaryFrameOperator_apply, inner_coordinates]
  simp only [inner_zero_right, inner_zero_left, add_zero, Prod.fst_zero, Prod.snd_zero]
  exact Submodule.inner_right_of_mem_orthogonal
    (K := (fderiv ℝ F (DiskRadialFlattening.map 3 x)).range) ⟨_, rfl⟩ (hW ⟨_, rfl⟩)

theorem frameExtension_coe (W : Vector 4 → Space N k) (s : Sphere 3) :
    frameExtension W s.val = boundaryFrameOperator (W s.val).val := by
  rw [frameExtension, DiskRadialFlattening.map_coe]

theorem parityOfDimension_zero_of_disk_frame (hN : N = k + 6)
    (F : Vector 4 → Vector N) (b : Sphere 3) (f : Sphere 3 → Vector N)
    (hext : ∀ s : Sphere 3, F s.val = f s)
    (hF : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hi : InjOn F (closedBall (0 : Vector 4) 1))
    (hd : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ F x))
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (a : Sphere 3 → Space N k)
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ)
    (W : Vector 4 → Space N k)
    (hWs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ (fun y ↦ (W y).val) x)
    (hWn : ∀ x ∈ closedBall (0 : Vector 4) 1, (W x).val.range ≤ (fderiv ℝ F x).rangeᗮ)
    (hWb : ∀ s : Sphere 3, W s.val = a s) :
    (diskData F b f hext hF hi hd).parityOfDimension hN hf a has ha = 0 := by
  apply ((diskData F b f hext hF hi hd).parityOfDimension_zero_iff_smooth_extension
    hN hf a has ha).mpr
  refine ⟨frameExtension W, fun _ _ ↦ (contDiff_frameExtension W hWs).contDiffAt,
    fun x _ w ↦ norm_frameExtension W x w, ?_, ?_⟩
  · intro x _
    exact frameExtension_normal F W x (hF _ (DiskRadialFlattening.map_mem_closedBall 3 x))
      (hWn _ (DiskRadialFlattening.map_mem_closedBall 3 x))
  · intro s
    rw [frameExtension_coe, hWb]

end NoExoticSixSphere.FlattenedSpanningDisk
