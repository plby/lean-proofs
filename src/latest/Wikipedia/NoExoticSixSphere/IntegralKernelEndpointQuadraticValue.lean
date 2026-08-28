import Wikipedia.NoExoticSixSphere.RegularCylinderDiskBoundaryFrame
import Wikipedia.NoExoticSixSphere.IntegralKernelBoundaryFrameExtension
import Wikipedia.NoExoticSixSphere.ExtendedBoundaryOperatorQuadraticValue

/-!
# Original endpoint sphere parity on the actual integral boundary kernel

An embedded smooth three-sphere in either original endpoint fiber, whose
integral class dies in an actually two-connected slab, has zero original
sphere parity. Construct the generic disk and its raw operator extension,
retain its actual collar, and compare with the prescribed equation frame.
Neither interior immersion nor a frame-extension hypothesis is required.

The quadratic-form corollary uses the original endpoint's two-connectivity.
This does not assert that arbitrary fillings have these connectivity
properties, or replace the integral kernel by the mod-two kernel.
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

theorem endpointTime_mem_Icc (hst : s < t) (c : ℝ) (hc : c = s ∨ c = t) : c ∈ Icc s t := by
  rcases hc with rfl | rfl
  · exact ⟨le_rfl, hst.le⟩
  · exact ⟨hst.le, le_rfl⟩

theorem endpointFiber_dimension_eq (hd : m = n + 6) :
    Module.finrank ℝ (Vector m) = Module.finrank ℝ (Vector n) + 6 := by
  simpa only [finrank_euclideanSpace_fin] using hd

def constantEndpointBoundaryMap
    (f₀ : C(NoExoticSixSphere.Sphere m, NoExoticSixSphere.Sphere n))
    (c : ℝ) (hc : c = s ∨ c = t) (he : ∀ x, d.map (c, x) = f₀ x) :
    C({x : NoExoticSixSphere.Sphere m // f₀ x = z}, BoundaryPush.ends d.map z s t) where
  toFun x := ⟨⟨⟨(c, x.val), (he x.val).trans x.property⟩,
    endpointTime_mem_Icc d.time_lt c hc⟩, hc⟩
  continuous_toFun :=
    (((continuous_const.prodMk continuous_subtype_val).subtype_mk _).subtype_mk _).subtype_mk _

theorem constantEndpointBoundaryMap_injective
    (f₀ : C(NoExoticSixSphere.Sphere m, NoExoticSixSphere.Sphere n))
    (c : ℝ) (hc : c = s ∨ c = t) (he : ∀ x, d.map (c, x) = f₀ x) :
    Injective (constantEndpointBoundaryMap f₀ c hc he) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun p : BoundaryPush.ends d.map z s t ↦ p.val.val.val.2) h

def constantEndpointSlabMap
    (f₀ : C(NoExoticSixSphere.Sphere m, NoExoticSixSphere.Sphere n))
    (c : ℝ) (hc : c = s ∨ c = t) (he : ∀ x, d.map (c, x) = f₀ x) :
    C({x : NoExoticSixSphere.Sphere m // f₀ x = z}, slab d.map z s t) :=
  (subtypeInclusion (BoundaryPush.ends d.map z s t)).comp
    (constantEndpointBoundaryMap f₀ c hc he)

variable [SimplyConnectedSpace (slab d.map z s t)] (w : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w)]

include w hW₂ in
theorem sphereParity_zero_of_integral_endpoint_kernel (hd : m = n + 6)
    (f₀ : C(NoExoticSixSphere.Sphere m, NoExoticSixSphere.Sphere n))
    (hf₀ : ContMDiff (𝓡 m) (𝓡 n) ∞ f₀)
    (hreg₀ : ∀ x, f₀ x = z → Surjective (mfderiv (𝓡 m) (𝓡 n) f₀ x))
    (U : Set ℝ) (hU : IsOpen U)
    (hconstant : ∀ c ∈ U, ∀ x, d.map (c, x) = f₀ x)
    (c : ℝ) (hc : c ∈ U) (hcend : c = s ∨ c = t) (a : NoExoticSixSphere.Sphere m)
    (f : C(NoExoticSixSphere.Sphere 3, {x : NoExoticSixSphere.Sphere m // f₀ x = z})) :
    letI := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (by simpa using hd)
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hdf : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 6) f q)),
      singularHomologyMap (constantEndpointSlabMap f₀ c hcend (hconstant c hc)) 3
        (SmoothCube.integralSphereClass f) = 0 →
      (RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd).sphereParity
        (RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a) f hf hi hdf = 0 := by
  let := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (by simpa using hd)
  intro hf hi hdf hker
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  let e := RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd
  let a₀ := RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a
  let B := BoundaryPush.ends d.map z s t
  let j := constantEndpointBoundaryMap f₀ c hcend (hconstant c hc)
  let fB := j.comp f
  let fW := (subtypeInclusion B).comp fB
  have hkerB : singularHomologyMap (subtypeInclusion B) 3
      (SmoothCube.integralSphereClass fB) = 0 := by
    rw [SmoothCube.integralSphereClass_comp, ← LinearMap.comp_apply,
      ← singularHomologyMap_comp]
    exact hker
  have hfS : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial fW) := e.smooth.comp hf
  have hiS : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 (m + 1)) (spatial fW) q) := by
    intro q
    change Injective (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) q)
    rw [mfderiv_comp q (e.smooth.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
    exact (e.injective_mfderiv (f q)).comp (hdf q)
  have hiB : Injective fB := (constantEndpointBoundaryMap_injective f₀ c hcend
    (hconstant c hc)).comp hi
  obtain ⟨D, ρ, hρ, hρ1, g, hgs, hgb, hgc, -, G, hG⟩ :=
    exists_disk_raw_frame_extension_of_integral_kernel w hd B (fun _ hx ↦ hx)
      fB hkerB hfS hiS hiB a
  have hF : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ (collarDisk c g) x :=
    fun x hx ↦ contDiffAt_collarDisk hd c g x (hgs x hx)
  have hgb' : ∀ q, g q.val =
      ⟨(c, (f q).val), (hconstant c hc (f q).val).trans (f q).property⟩ := by
    intro q
    rw [hgb]
    rfl
  have hb : ∀ q : NoExoticSixSphere.Sphere 3, collarDisk c g q.val = (e.toFun (f q), 0) := by
    intro q
    change ((g q.val).val.2.val, (g q.val).val.1 - c) = (e.toFun (f q), 0)
    rw [hgb']
    change ((f q).val.val, c - c) = ((f q).val.val, 0)
    rw [sub_self]
  obtain ⟨H, hH⟩ := exists_endpoint_boundary_frame_extension hd f₀ hf₀ hreg₀ U hU hconstant
    c hc a f g (fun q ↦ hgs q.val (sphere_subset_closedBall q.property)) hgb' G hG
  rcases hcend with hleft | hright
  · exact e.sphereParity_zero_of_extended_boundary_operator_negative a₀ f hf hi hdf
      (collarDisk c g) hF hb H hH
        (collarDisk_left_height_negative D (spherePole 3) c g hF ρ (by linarith) hρ1 hgc hfS
          (fun _ ↦ hleft))
  · exact e.sphereParity_zero_of_extended_boundary_operator a₀ f hf hi hdf
      (collarDisk c g) hF hb H hH
        (collarDisk_right_height_positive D (spherePole 3) c g hF ρ (by linarith) hρ1 hgc hfS
          (fun _ ↦ hright))

include w hW₂ in
theorem quadraticValue_zero_of_integral_endpoint_kernel (hd : m = n + 6)
    (f₀ : C(NoExoticSixSphere.Sphere m, NoExoticSixSphere.Sphere n))
    (hf₀ : ContMDiff (𝓡 m) (𝓡 n) ∞ f₀)
    (hreg₀ : ∀ x, f₀ x = z → Surjective (mfderiv (𝓡 m) (𝓡 n) f₀ x))
    [SimplyConnectedSpace {x : NoExoticSixSphere.Sphere m // f₀ x = z}]
    (x₀ : {x : NoExoticSixSphere.Sphere m // f₀ x = z})
    [Subsingleton (π_ 2 {x : NoExoticSixSphere.Sphere m // f₀ x = z} x₀)]
    (U : Set ℝ) (hU : IsOpen U)
    (hconstant : ∀ c ∈ U, ∀ x, d.map (c, x) = f₀ x)
    (c : ℝ) (hc : c ∈ U) (hcend : c = s ∨ c = t) (a : NoExoticSixSphere.Sphere m)
    (f : C(NoExoticSixSphere.Sphere 3, {x : NoExoticSixSphere.Sphere m // f₀ x = z})) :
    letI := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (by simpa using hd)
    letI := regularFiber_isManifold f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
    letI := RegularSphereFiber.fiber_compact f₀ z
    ∀ (r : EuclideanEmbedding.TubularRetraction
        (RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd))
      (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hdf : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 6) f q)),
      singularHomologyMap (constantEndpointSlabMap f₀ c hcend (hconstant c hc)) 3
        (SmoothCube.integralSphereClass f) = 0 →
      (RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd).modTwoHomologyQuadraticForm
        (RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a) r x₀
          (SixSphereMiddleParity.sphereClass f) = 0 := by
  let := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (by simpa using hd)
  let := regularFiber_isManifold f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
  let := RegularSphereFiber.fiber_compact f₀ z
  intro r hf hi hdf hker
  let e := RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd
  let a₀ := RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a
  rw [e.modTwoHomologyQuadraticForm_sphereClass,
    e.geometricSphereParity_eq_of_embedding a₀ r f hf hi hdf]
  exact sphereParity_zero_of_integral_endpoint_kernel w hd f₀ hf₀ hreg₀ U hU hconstant
    c hc hcend a f hf hi hdf hker

end NoExoticSixSphere.RegularSlabDiskCollar
