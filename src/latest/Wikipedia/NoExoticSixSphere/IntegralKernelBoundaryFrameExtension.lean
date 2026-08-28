import Wikipedia.NoExoticSixSphere.GenericIntegralKernelDisk
import Wikipedia.NoExoticSixSphere.RegularCylinderFiberFourDiskFrame
import Wikipedia.NoExoticSixSphere.ManifoldFourDiskBoundaryExtension
import Wikipedia.NoExoticSixSphere.ManifoldFourDiskRawFrame

/-!
# Exact original boundary-frame extensions for integral-kernel disks

In an actually two-connected original regular slab, an injective immersed
boundary sphere representing an integral kernel class has a smooth proper
collared disk. The same disk's actual normal-plus-derivative boundary
operator extends through injective operators. Its normal frame is supplied
by the original regular-fiber equations, and the needed singularity parity
is proved for the constructed disk, not assumed.

This does not assert immersion of that disk, two-connectivity of arbitrary
fillings, or vanishing of the original boundary quadratic value. The last
comparison with the prescribed boundary frame and collar is still needed.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSlabDiskCollar

open GLOrthonormalization CylinderFiberSlab Stiefel
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {m n : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  [SimplyConnectedSpace (slab d.map z s t)] (w : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w)]

include w hW₂ in
theorem exists_disk_frame_extension_of_integral_kernel (hd : m = n + 6)
    (U : Set (slab d.map z s t)) (hU : U ⊆ BoundaryPush.ends d.map z s t)
    (f : C(NoExoticSixSphere.Sphere 3, U))
    (hker : singularHomologyMap (subtypeInclusion U) 3 (SmoothCube.integralSphereClass f) = 0)
    (hf : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial ((subtypeInclusion U).comp f)))
    (hi : ∀ q, Injective
      (mfderiv (𝓡 3) (𝓡 (m + 1)) (spatial ((subtypeInclusion U).comp f)) q))
    (hfinj : Injective f) (a : NoExoticSixSphere.Sphere m) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
      (CylinderFiberNormalFrame.dimension_eq hd)
    let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map 6 hd
    let aN := RegularCylinderFiber.normalFrame d.map d.smooth_map z d.regular_map 6 hd a
    ∃ D : d.CollaredDiskExtension 3 ((subtypeInclusion U).comp f),
      ∃ ρ : ℝ, 3 / 4 < ρ ∧ ρ < 1 ∧
        ∃ g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z},
          (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) ∧
          (∀ q : NoExoticSixSphere.Sphere 3, g q.val = (f q).val.val) ∧
          (∀ x : Disk (E := Vector 4), ρ ≤ ‖x.val‖ → g x.val = (D.map x).val) ∧
          (∀ x ∈ ball 0 1, (g x).val.1 ∈ Ioo s t) ∧
          ∃ F : C(Disk (E := Vector 4),
              Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)),
            ∀ q : NoExoticSixSphere.Sphere 3,
              (F (boundaryToDisk q)).val = e.normalFourDiskOperator aN g q.val := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map 6 hd
  let aN := RegularCylinderFiber.normalFrame d.map d.smooth_map z d.regular_map 6 hd a
  obtain ⟨D, ρ, hρ, hρ1, g, hgs, hgb, hgc, hgV, -, -, C, -, -, -, ⟨P⟩, -, hfull⟩ :=
    exists_generic_disk_of_integral_kernel w hd U hU f hker hf hi
  have heven : Even (DiskDoublePoints.singularSet g).ncard := (hfull hfinj).2.2.2.1
  obtain ⟨F, hF⟩ := e.exists_fourDiskOperator_extension aN g hgs P heven
  exact ⟨D, ρ, hρ, hρ1, g, hgs, hgb, hgc, hgV, F, hF⟩

include w hW₂ in
theorem exists_disk_raw_frame_extension_of_integral_kernel (hd : m = n + 6)
    (U : Set (slab d.map z s t)) (hU : U ⊆ BoundaryPush.ends d.map z s t)
    (f : C(NoExoticSixSphere.Sphere 3, U))
    (hker : singularHomologyMap (subtypeInclusion U) 3 (SmoothCube.integralSphereClass f) = 0)
    (hf : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial ((subtypeInclusion U).comp f)))
    (hi : ∀ q, Injective
      (mfderiv (𝓡 3) (𝓡 (m + 1)) (spatial ((subtypeInclusion U).comp f)) q))
    (hfinj : Injective f) (a : NoExoticSixSphere.Sphere m) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
      (CylinderFiberNormalFrame.dimension_eq hd)
    let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map 6 hd
    let aN := RegularCylinderFiber.normalFrame d.map d.smooth_map z d.regular_map 6 hd a
    ∃ D : d.CollaredDiskExtension 3 ((subtypeInclusion U).comp f),
      ∃ ρ : ℝ, 3 / 4 < ρ ∧ ρ < 1 ∧
        ∃ g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z},
          (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) ∧
          (∀ q : NoExoticSixSphere.Sphere 3, g q.val = (f q).val.val) ∧
          (∀ x : Disk (E := Vector 4), ρ ≤ ‖x.val‖ → g x.val = (D.map x).val) ∧
          (∀ x ∈ ball 0 1, (g x).val.1 ∈ Ioo s t) ∧
          ∃ F : C(Disk (E := Vector 4),
              Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)),
            ∀ q : NoExoticSixSphere.Sphere 3,
              (F (boundaryToDisk q)).val = e.rawNormalFourDiskOperator aN g q.val := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map 6 hd
  let aN := RegularCylinderFiber.normalFrame d.map d.smooth_map z d.regular_map 6 hd a
  obtain ⟨D, ρ, hρ, hρ1, g, hgs, hgb, hgc, hgV, -, -, C, -, -, -, ⟨P⟩, -, hfull⟩ :=
    exists_generic_disk_of_integral_kernel w hd U hU f hker hf hi
  have heven : Even (DiskDoublePoints.singularSet g).ncard := (hfull hfinj).2.2.2.1
  obtain ⟨F, hF⟩ := e.exists_rawFourDiskOperator_extension aN g hgs P heven
  exact ⟨D, ρ, hρ, hρ1, g, hgs, hgb, hgc, hgV, F, hF⟩

end NoExoticSixSphere.RegularSlabDiskCollar
