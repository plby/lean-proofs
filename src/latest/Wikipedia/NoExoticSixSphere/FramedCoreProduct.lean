import Wikipedia.NoExoticSixSphere.ThickeningNormalFrame
import Wikipedia.NoExoticSixSphere.ClosedProductRestriction

/-!
# A framed embedded product for an actual general product map

This records an actual map and its full normal frame on a thin closed
product of arbitrary finite transverse dimension. The normal frame retains the prescribed disk-core
frame. No affine formula, attaching identification, or surgery trace is built
into this structure.
-/

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.DiskThickening

open GLOrthonormalization

structure FramedCoreProduct {N k q : ℕ} (H : Vector 4 × Vector q → Vector N)
    (T : Vector 4 → Vector k →L[ℝ] Vector N) where
  radius : ℝ
  radius_pos : 0 < radius
  embedded : IsClosedEmbedding
    (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector q) radius ↦ H (p.1.val, p.2.val))
  smooth : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) radius,
    ContDiffAt ℝ ∞ H (x, v)
  immersive : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) radius,
    Injective (fderiv ℝ H (x, v))
  normalFrame : Vector 4 × Vector q → Vector k →L[ℝ] Vector N
  normalFrame_smooth : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector q) radius, ContDiffAt ℝ ∞ normalFrame (x, v)
  normalFrame_norm : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector q) radius, ∀ w, ‖normalFrame (x, v) w‖ = ‖w‖
  normalFrame_range : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector q) radius,
      (normalFrame (x, v)).range = (fderiv ℝ H (x, v)).rangeᗮ
  normalFrame_core : ∀ x ∈ closedBall (0 : Vector 4) 1, normalFrame (x, 0) = T x

theorem exists_framedCoreProduct {N k : ℕ} (H : Vector 4 × Vector q → Vector N)
    (T : Vector 4 → Vector k →L[ℝ] Vector N) (r : ℝ) (hr : 0 < r)
    (hemb : IsClosedEmbedding
      (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector q) r ↦ H (p.1.val, p.2.val)))
    (hHs : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) r,
      ContDiffAt ℝ ∞ H (x, v))
    (hHi : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) r,
      Injective (fderiv ℝ H (x, v)))
    (hTs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x)
    (hTn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖)
    (hTr : ∀ x ∈ closedBall (0 : Vector 4) 1, (T x).range = (fderiv ℝ H (x, 0)).rangeᗮ)
    (hN : k + 4 + q = N) : ∃ B : FramedCoreProduct H T, B.radius ≤ r := by
  obtain ⟨ε, hε, hεr, R, hR, hRcore⟩ :=
    exists_normalFrame_product H T r hr hHs hHi hTs hTn hTr hN
  refine ⟨{
    radius := ε
    radius_pos := hε
    embedded := restrict_closedProduct_embedding
      (fun p : closedBall (0 : Vector 4) 1 × Vector q ↦ H (p.1.val, p.2)) hεr hemb
    smooth := fun x hx v hv ↦ hHs x hx v ((closedBall_subset_closedBall hεr) hv)
    immersive := fun x hx v hv ↦ hHi x hx v ((closedBall_subset_closedBall hεr) hv)
    normalFrame := R
    normalFrame_smooth := fun x hx v hv ↦ (hR x hx v hv).1
    normalFrame_norm := fun x hx v hv ↦ (hR x hx v hv).2.1
    normalFrame_range := fun x hx v hv ↦ (hR x hx v hv).2.2
    normalFrame_core := hRcore }, hεr⟩

end NoExoticSixSphere.DiskThickening
