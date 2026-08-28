import Wikipedia.NoExoticSixSphere.FlattenedSpanningDisk
import Wikipedia.NoExoticSixSphere.FramedSpanningDisk

/-!
# The flattened disk has the exact prescribed boundary collar

Near the sphere the radial flattening agrees exactly with the retraction used
in the existing spanning-disk definition. The normal height keeps the open
disk disjoint from the entire original ambient space.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.FlattenedSpanningDisk

open GLOrthonormalization StabilizedSpanningDisk

variable {N : ℕ} (F : Vector 4 → Vector N) (b : Sphere 3) (f : Sphere 3 → Vector N)
  (hext : ∀ s : Sphere 3, F s.val = f s)

include hext in
theorem base_eq_extension_on_outer {x : Vector 4} (hx : 1 / 2 < ‖x‖) :
    F (DiskRadialFlattening.map 3 x) = SmoothSphereAmbient.extension b f x := by
  have hx₀ : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have hψ : DiskRadialFlattening.map 3 x = (SphereRadialRetraction.retract b x).val := by
    rw [DiskRadialFlattening.map_eq_normalize 3 hx.le]
    simp only [SphereRadialRetraction.retract, dif_neg hx₀]
  have hχ : SmoothSphereAmbient.cutoff 3 x = 0 :=
    (SmoothSphereAmbient.cutoff 3).zero_of_le_dist (by
      change (1 / 2 : ℝ) ≤ dist x 0
      simpa only [dist_zero_right] using hx.le)
  rw [hψ, hext]
  simp only [SmoothSphereAmbient.extension, hχ, sub_zero, one_smul]

include hext in
theorem map_eq_collar {x : Vector 4} (hx : 1 / 2 < ‖x‖) : map F x = collar b f x := by
  unfold map collar SphereExtensionWithHeight.map
  rw [base_eq_extension_on_outer F b f hext hx]

include hext in
theorem map_coe (s : Sphere 3) : map F s.val = appendZeroMap N 6 (f s) := by
  rw [map, DiskRadialFlattening.map_coe, hext,
    (definingFunction_eq_zero_iff s.val).mpr s.property, coordinates_old]

omit b f hext in
theorem avoids_oldAmbient {x : Vector 4} (hx : x ∈ ball 0 1) :
    map F x ∉ range (appendZeroMap N 6) := by
  rintro ⟨y, hy⟩
  have he : ((F (DiskRadialFlattening.map 3 x), definingFunction x), (0 : ℝ × Vector 4)) =
      ((y, 0), 0) := (coordinates N 4).injective (by
    rw [coordinates_old]
    exact hy.symm)
  have hρ : definingFunction x = 0 :=
    congrArg (fun p : (Vector N × ℝ) × (ℝ × Vector 4) ↦ p.1.2) he
  have hn : ‖x‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (definingFunction_eq_zero_iff x).mp hρ
  have hlt : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
  exact (ne_of_lt hlt) hn

def diskData
    (hF : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hi : InjOn F (closedBall (0 : Vector 4) 1))
    (hd : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ F x)) : DiskData b f where
  toFun := map F
  smooth := contDiff_map F hF
  embedded := isClosedEmbedding_disk F hF hi
  immersive x _ := injective_fderiv_map F x
    (hF _ (DiskRadialFlattening.map_mem_closedBall 3 x))
    (hd _ (DiskRadialFlattening.map_mem_closedBall 3 x))
  boundary := map_coe F f hext
  avoids _ hx := avoids_oldAmbient F hx
  collar_eq := by
    refine ⟨{x : Vector 4 | 1 / 2 < ‖x‖}, isOpen_lt continuous_const continuous_norm, ?_, ?_⟩
    · intro x hx
      have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
      change (1 / 2 : ℝ) < ‖x‖
      rw [hn]
      norm_num
    · intro x hx
      exact map_eq_collar F b f hext hx

end NoExoticSixSphere.FlattenedSpanningDisk
