import Wikipedia.NoExoticSixSphere.RadialHeightEmbedding
import Wikipedia.NoExoticSixSphere.StabilizedSpanningDisk

/-!
# A spanning disk from an existing embedded disk, without supported graph terms

Radial flattening keeps all evaluations inside the given closed disk. The
normal height restores immersion and injectivity, while all five additional
graph coordinates stay zero. Smoothness of the original disk is needed only
near its closed ball.
-/

noncomputable section

open Function Set Metric Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.FlattenedSpanningDisk

open GLOrthonormalization StabilizedSpanningDisk

variable {N : ℕ} (F : Vector 4 → Vector N)

def map (x : Vector 4) : Vector (N + 6) :=
  coordinates N 4 ((F (DiskRadialFlattening.map 3 x), definingFunction x), 0)

theorem contDiff_base
    (hF : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x) :
    ContDiff ℝ ∞ (F ∘ DiskRadialFlattening.map 3) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (hF _ (DiskRadialFlattening.map_mem_closedBall 3 x)).comp x
    (DiskRadialFlattening.contDiff_map 3).contDiffAt

theorem contDiff_map
    (hF : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x) :
    ContDiff ℝ ∞ (map F) :=
  (coordinates N 4).contDiff.comp
    (((contDiff_base F hF).prodMk contDiff_definingFunction).prodMk contDiff_const)

theorem fderiv_map_apply (x v : Vector 4)
    (hF : ContDiffAt ℝ ∞ F (DiskRadialFlattening.map 3 x)) :
    fderiv ℝ (map F) x v = coordinates N 4
      ((fderiv ℝ F (DiskRadialFlattening.map 3 x) (fderiv ℝ (DiskRadialFlattening.map 3) x v),
        fderiv ℝ (definingFunction (E := Vector 4)) x v), 0) := by
  have hψ := ((DiskRadialFlattening.contDiff_map 3).differentiable (by simp) x).hasFDerivAt
  have hb := (hF.differentiableAt (by simp)).hasFDerivAt.comp x hψ
  have hρ := ((contDiff_definingFunction (E := Vector 4)).differentiable (by simp) x).hasFDerivAt
  have hd := (coordinates N 4).hasFDerivAt.comp x
    ((hb.prodMk hρ).prodMk (hasFDerivAt_const (0 : ℝ × Vector 4) x))
  rw [show fderiv ℝ (map F) x = _ from hd.fderiv]
  rfl

theorem injective_map (hF : InjOn F (closedBall (0 : Vector 4) 1)) : Injective (map F) := by
  intro x y h
  have he := (coordinates N 4).injective h
  have hb : F (DiskRadialFlattening.map 3 x) = F (DiskRadialFlattening.map 3 y) :=
    congrArg (fun p : (Vector N × ℝ) × (ℝ × Vector 4) ↦ p.1.1) he
  have hρ : definingFunction x = definingFunction y :=
    congrArg (fun p : (Vector N × ℝ) × (ℝ × Vector 4) ↦ p.1.2) he
  apply DiskRadialFlattening.injective_heightMap 3
  exact Prod.ext (hF (DiskRadialFlattening.map_mem_closedBall 3 x)
    (DiskRadialFlattening.map_mem_closedBall 3 y) hb) hρ

theorem injective_fderiv_map (x : Vector 4)
    (hF : ContDiffAt ℝ ∞ F (DiskRadialFlattening.map 3 x))
    (hi : Injective (fderiv ℝ F (DiskRadialFlattening.map 3 x))) :
    Injective (fderiv ℝ (map F) x) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [fderiv_map_apply F x v hF] at hv
  have he : ((fderiv ℝ F (DiskRadialFlattening.map 3 x)
      (fderiv ℝ (DiskRadialFlattening.map 3) x v),
        fderiv ℝ (definingFunction (E := Vector 4)) x v), (0 : ℝ × Vector 4)) = 0 :=
    (coordinates N 4).injective (by simpa only [map_zero] using hv)
  have hψ := (injective_iff_map_eq_zero _).mp hi _
    (congrArg (fun p : (Vector N × ℝ) × (ℝ × Vector 4) ↦ p.1.1) he)
  exact DiskRadialFlattening.common_kernel 3 x v hψ
    (congrArg (fun p : (Vector N × ℝ) × (ℝ × Vector 4) ↦ p.1.2) he)

theorem isClosedEmbedding_disk
    (hF : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hi : InjOn F (closedBall (0 : Vector 4) 1)) :
    IsClosedEmbedding (fun x : closedBall (0 : Vector 4) 1 ↦ map F x.val) := by
  let : CompactSpace (closedBall (0 : Vector 4) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  apply ((contDiff_map F hF).continuous.comp continuous_subtype_val).isClosedEmbedding
  intro x y h
  exact Subtype.ext (injective_map F hi h)

end NoExoticSixSphere.FlattenedSpanningDisk
