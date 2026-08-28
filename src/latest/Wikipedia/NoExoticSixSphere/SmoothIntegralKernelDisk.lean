import Wikipedia.NoExoticSixSphere.SmoothRegularSlabDisk
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# Actual smooth integral-kernel disks with retained immersive boundary collars

A continuous three-sphere in the slab boundary lies entirely at one endpoint;
this follows from its proved connectivity and the original time coordinate.
An integral kernel class in a two-connected slab therefore has a constructed
smooth disk, with exact boundary values, unchanged outer collar, interior
avoidance, and injective ambient derivative on the boundary when the original
spatial sphere is immersive. Interior immersion is still a separate theorem.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSlabDiskCollar

open GLOrthonormalization CylinderFiberSlab
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {m n : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}

theorem boundarySphere_one_end (f : C(NoExoticSixSphere.Sphere 3, slab d.map z s t))
    (hf : ∀ q, f q ∈ BoundaryPush.ends d.map z s t) :
    (∀ q, (f q).val.val.1 = s) ∨ ∀ q, (f q).val.val.1 = t := by
  let : SimplyConnectedSpace (NoExoticSixSphere.Sphere 3) :=
    EuclideanSphere.simplyConnectedSpace 1
  let T : C(NoExoticSixSphere.Sphere 3, ℝ) :=
    ⟨fun q ↦ (f q).val.val.1,
      continuous_fst.comp ((continuous_subtype_val.comp continuous_subtype_val).comp f.continuous)⟩
  have hmid : ∀ q ∈ (univ : Set (NoExoticSixSphere.Sphere 3)), T q ≠ (s + t) / 2 := by
    intro q _ hq
    change (f q).val.val.1 = (s + t) / 2 at hq
    rcases hf q with he | he <;> linarith [d.time_lt]
  rcases isPreconnected_univ.mapsTo_Ioi_or_Iio T.continuous.continuousOn hmid with ht | hs
  · right
    intro q
    have hq : (s + t) / 2 < (f q).val.val.1 := ht (mem_univ q)
    rcases hf q with he | he
    · exfalso
      linarith [d.time_lt]
    · exact he
  · left
    intro q
    have hq : (f q).val.val.1 < (s + t) / 2 := hs (mem_univ q)
    rcases hf q with he | he
    · exact he
    · exfalso
      linarith [d.time_lt]

variable [SimplyConnectedSpace (slab d.map z s t)] (w : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w)]

include w hW₂ in
theorem exists_smooth_disk_of_integral_kernel (hd : m = n + 6)
    (U : Set (slab d.map z s t)) (hU : U ⊆ BoundaryPush.ends d.map z s t)
    (f : C(NoExoticSixSphere.Sphere 3, U))
    (hker : singularHomologyMap (subtypeInclusion U) 3 (SmoothCube.integralSphereClass f) = 0)
    (hf : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial ((subtypeInclusion U).comp f)))
    (hi : ∀ q, Injective
      (mfderiv (𝓡 3) (𝓡 (m + 1)) (spatial ((subtypeInclusion U).comp f)) q)) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
      (CylinderFiberNormalFrame.dimension_eq hd)
    let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map 6 hd
    ∃ D : d.CollaredDiskExtension 3 ((subtypeInclusion U).comp f),
      ∃ g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z},
        (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) ∧
        (∀ q, g q.val = (f q).val.val) ∧
        (∀ x : Disk (E := Vector 4), 3 / 4 ≤ ‖x.val‖ → g x.val = (D.map x).val) ∧
        (∀ x ∈ ball 0 1, (g x).val.1 ∈ Ioo s t) ∧
        ∀ q : NoExoticSixSphere.Sphere 3, Injective (fderiv ℝ (e.toFun ∘ g) q.val) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  obtain ⟨D⟩ := d.nonempty_collaredDiskExtension_of_integral_kernel w U f hker
  have hend := boundarySphere_one_end ((subtypeInclusion U).comp f)
    (fun q ↦ hU (f q).property)
  exact ⟨D, exists_smooth_with_immersive_boundary D 6 hd (spherePole 3) hf hi hend⟩

end NoExoticSixSphere.RegularSlabDiskCollar
