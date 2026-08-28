import Wikipedia.NoExoticSixSphere.FramedSphereFamily

/-!
# Framed sphere parity comparison through immersed intermediate disks

Only the two endpoint disks are required to be embedded. The intermediate
spheres and disks can have self-intersections; injectivity of their actual
derivatives and exact varying collars suffice for the parity comparison.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel ProjectionHomotopy

theorem parity_eq_of_regular_sphere_family {k : ℕ} (b : Sphere 3)
    (f : ℝ → Sphere 3 → Vector (k + 6))
    (hf : ∀ t, ContMDiff (𝓡 3) (𝓡 (k + 6)) ∞ (f t))
    (a : ℝ → Sphere 3 → Space (k + 6) k)
    (has : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3))
      𝓘(ℝ, Vector k →L[ℝ] Vector (k + 6)) ∞ (fun q : ℝ × Sphere 3 ↦ (a q.1 q.2).val))
    (ha : ∀ t : unitInterval, ∀ s,
      (a (t : ℝ) s).val.range ≤ (mfderiv (𝓡 3) (𝓡 (k + 6)) (f (t : ℝ)) s).rangeᗮ)
    (D₀ : DiskData b (f 0)) (D₁ : DiskData b (f 1))
    (G : ℝ → Vector 4 → Vector (k + 12)) (hG : ContDiff ℝ ∞ (uncurry G))
    (hi : ∀ t : unitInterval, ∀ x ∈ closedBall (0 : Vector 4) 1,
      Injective (fderiv ℝ (G (t : ℝ)) x))
    (hD₀ : D₀.toFun = G 0) (hD₁ : D₁.toFun = G 1)
    {V : Set (Vector 4)} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
    (heq : ∀ t : unitInterval, EqOn (G (t : ℝ)) (collar b (f (t : ℝ))) V) :
    D₀.parity (hf 0) (a 0) (has.comp (contMDiff_const.prodMk contMDiff_id)) (ha 0) =
      D₁.parity (hf 1) (a 1) (has.comp (contMDiff_const.prodMk contMDiff_id)) (ha 1) := by
  have hs (t : ℝ) : ContMDiff (𝓡 3)
      𝓘(ℝ, Vector k →L[ℝ] Vector (k + 6)) ∞ (fun s ↦ (a t s).val) :=
    has.comp (contMDiff_const.prodMk contMDiff_id)
  let A := boundaryFrameFamily a has
  have hA (q : unitInterval × Sphere 3) :
      (A q).val.range ≤ (fderiv ℝ (G (q.1 : ℝ)) q.2.val).rangeᗮ :=
    boundaryFrame_normal_disk b (f q.1) (hf q.1) (a q.1) (ha q.1) hV hSV (heq q.1) q.2
  have hAt (t : unitInterval) : slice A t = boundaryFrameMap (a (t : ℝ)) (hs t) :=
    boundaryFrameFamily_slice a has t
  have h := DiskHomotopy.parity_endpoints (k + 3) G hG hi A hA
  have h₀ := D₀.parity_eq_of_map_and_frame (hf 0) (a 0) (hs 0) (ha 0) (G 0)
    (fun _ _ ↦ (DiskHomotopy.contDiff_slice (k + 3) G hG 0).contDiffAt)
    (hi 0) (slice A 0) (fun s ↦ hA (0, s)) hD₀ (hAt 0).symm
  have h₁ := D₁.parity_eq_of_map_and_frame (hf 1) (a 1) (hs 1) (ha 1) (G 1)
    (fun _ _ ↦ (DiskHomotopy.contDiff_slice (k + 3) G hG 1).contDiffAt)
    (hi 1) (slice A 1) (fun s ↦ hA (1, s)) hD₁ (hAt 1).symm
  exact h₀.trans (h.trans h₁.symm)

theorem parityOfDimension_eq_of_regular_sphere_family {N k : ℕ} (hN : N = k + 6)
    (b : Sphere 3) (f : ℝ → Sphere 3 → Vector N)
    (hf : ∀ t, ContMDiff (𝓡 3) (𝓡 N) ∞ (f t)) (a : ℝ → Sphere 3 → Space N k)
    (has : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3))
      𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun q : ℝ × Sphere 3 ↦ (a q.1 q.2).val))
    (ha : ∀ t : unitInterval, ∀ s,
      (a (t : ℝ) s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) (f (t : ℝ)) s).rangeᗮ)
    (D₀ : DiskData b (f 0)) (D₁ : DiskData b (f 1))
    (G : ℝ → Vector 4 → Vector (N + 6)) (hG : ContDiff ℝ ∞ (uncurry G))
    (hi : ∀ t : unitInterval, ∀ x ∈ closedBall (0 : Vector 4) 1,
      Injective (fderiv ℝ (G (t : ℝ)) x))
    (hD₀ : D₀.toFun = G 0) (hD₁ : D₁.toFun = G 1)
    {V : Set (Vector 4)} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
    (heq : ∀ t : unitInterval, EqOn (G (t : ℝ)) (collar b (f (t : ℝ))) V) :
    D₀.parityOfDimension hN (hf 0) (a 0)
        (has.comp (contMDiff_const.prodMk contMDiff_id)) (ha 0) =
      D₁.parityOfDimension hN (hf 1) (a 1)
        (has.comp (contMDiff_const.prodMk contMDiff_id)) (ha 1) := by
  subst N
  exact parity_eq_of_regular_sphere_family b f hf a has ha D₀ D₁ G hG hi hD₀ hD₁ hV hSV heq

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
