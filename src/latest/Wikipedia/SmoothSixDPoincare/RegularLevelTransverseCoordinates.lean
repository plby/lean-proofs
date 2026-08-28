import Wikipedia.SmoothSixDPoincare.RegularLevelTangent
import Wikipedia.SmoothSixDPoincare.NativeSmoothRetraction
import Wikipedia.SmoothSixDPoincare.LocalInverseIntoManifold
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smooth transverse coordinates from the original manifold and its retraction

Push a native transverse vector into a Euclidean embedding, make a short
linear displacement there, and retract to the original manifold. This is an
actual smooth map near the regular level, equal to its inclusion at time zero.
Its differential is the proved level-tangent/transverse-direction splitting.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

namespace NativeEuclideanEmbedding

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (e : NativeEuclideanEmbedding E M)

/-- A smooth native field has a smooth vector-valued realization in the Euclidean embedding. -/
theorem contMDiff_embeddedField {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, E) (𝓡 e.ambientDimension) ∞
      (fun x => mvfderiv 𝓘(ℝ, E) e.toFun x (V x)) := by
  have ht := (e.smooth.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  have hp := (contMDiff_tangentBundleModelSpaceHomeomorph
    (I := 𝓡 e.ambientDimension) (n := ∞)).comp ht
  rw [← modelWithCornersSelf_prod] at hp
  convert contDiff_snd.contMDiff.comp hp using 1 <;> rfl

end NativeEuclideanEmbedding

namespace RegularLevel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
  {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
  (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)

/-- The explicit Euclidean displacement of the actual level. -/
def levelDisplacement (z : {x : M // f x = b} × ℝ) : EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.toFun z.1 + z.2 • mvfderiv 𝓘(ℝ, E) e.toFun z.1 (V z.1)

/-- The displacement stays in the genuine smooth-retraction domain. -/
def transverseCoordinateDomain : Set ({x : M // f x = b} × ℝ) :=
  levelDisplacement V ⁻¹' r.domain

/-- Retraction produces a map into the original manifold, not its Euclidean realization. -/
def transverseCoordinates : ({x : M // f x = b} × ℝ) → M :=
  r.toFun ∘ levelDisplacement V

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem transverseCoordinates_zero (x : {x : M // f x = b}) :
    transverseCoordinates r V (x, 0) = x := by
  simp only [transverseCoordinates, comp_apply, levelDisplacement, zero_smul, add_zero]
  exact r.retract x

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem zero_mem_transverseCoordinateDomain (x : {x : M // f x = b}) :
    (x, 0) ∈ transverseCoordinateDomain r V := by
  change e.toFun x + (0 : ℝ) • _ ∈ r.domain
  simp only [zero_smul, add_zero]
  exact r.contains ⟨x, rfl⟩

variable (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
  (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
    (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))

include hV in
theorem contMDiff_levelDisplacement :
    letI := chartedSpace hf hreg
    ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) (𝓡 e.ambientDimension) ∞
      (levelDisplacement (e := e) (f := f) (b := b) V) := by
  let _ := chartedSpace hf hreg
  have hi : ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun z : {x : M // f x = b} × ℝ => (z.1 : M)) :=
    (contMDiff_inclusion hf hreg).comp contMDiff_fst
  have hfirst := e.smooth.comp hi
  have hfield := (e.contMDiff_embeddedField hV).comp hi
  have htime : ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : {x : M // f x = b} × ℝ → ℝ) := contMDiff_snd
  exact hfirst.add (htime.smul hfield)

include hf hreg hV in
theorem isOpen_transverseCoordinateDomain :
    IsOpen (transverseCoordinateDomain (f := f) (b := b) r V) := by
  let _ := chartedSpace hf hreg
  exact r.open_domain.preimage (contMDiff_levelDisplacement (e := e) V hf hreg hV).continuous

include hV in
theorem contMDiffOn_transverseCoordinates :
    letI := chartedSpace hf hreg
    ContMDiffOn (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (transverseCoordinates r V) (transverseCoordinateDomain (f := f) (b := b) r V) := by
  let _ := chartedSpace hf hreg
  exact r.smooth.comp (contMDiff_levelDisplacement (e := e) V hf hreg hV).contMDiffOn
    (fun _ hz => hz)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The time derivative at zero is the original native vector, by differentiating the retraction. -/
theorem mfderiv_transverseCoordinates_time_zero (x : {x : M // f x = b}) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0 =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (V x) := by
  let A := mvfderiv 𝓘(ℝ, E) e.toFun (x : M) (V x)
  let line : ℝ → EuclideanSpace ℝ (Fin e.ambientDimension) := fun t => e.toFun x + t • A
  have hline : HasFDerivAt line ((ContinuousLinearMap.id ℝ ℝ).smulRight A) 0 :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight A).hasFDerivAt.const_add (e.toFun x)
  have hzero : line 0 = e.toFun x := by simp [line]
  have hr : MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (line 0) := by
    rw [hzero]
    exact (r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨x, rfl⟩))).mdifferentiableAt
      (by simp)
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (r.toFun ∘ line) 0 = _
  rw [mfderiv_comp 0 hr hline.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, hline.fderiv, hzero]
  apply ContinuousLinearMap.ext
  intro t
  change ℝ at t
  let R : EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] E :=
    mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun x)
  change R (t • A) = t • (V x : E)
  rw [map_smul]
  congr 1
  exact congrArg (fun L => L (V x)) (r.mfderiv_retract_comp (x : M))

include hV in
/-- The full native differential is precisely the actual tangent-plus-transverse map. -/
theorem mfderiv_transverseCoordinates_zero (x : {x : M // f x = b}) :
    letI := chartedSpace hf hreg
    mfderiv (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
      (transverseCoordinates r V) (x, 0) = transverseTangentMap hf hreg x (V x) := by
  let _ := chartedSpace hf hreg
  have hs := (contMDiffOn_transverseCoordinates r V hf hreg hV).contMDiffAt
    ((isOpen_transverseCoordinateDomain r V hf hreg hV).mem_nhds
      (zero_mem_transverseCoordinateDomain r V x))
  have hbase : (fun y : {x : M // f x = b} => transverseCoordinates r V (y, 0)) =
      Subtype.val := funext (transverseCoordinates_zero r V)
  apply ContinuousLinearMap.ext
  intro w
  rw [mfderiv_prod_eq_add_apply (hs.mdifferentiableAt (by simp)), hbase,
    mfderiv_transverseCoordinates_time_zero r V x]
  rfl

include hV in
/-- A unit-height field gives a genuine local diffeomorphism at every original level point. -/
theorem isLocalDiffeomorphAt_transverseCoordinates_zero (x : {x : M // f x = b})
    (hunit : mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1) :
    letI := chartedSpace hf hreg
    IsLocalDiffeomorphAt (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (transverseCoordinates r V) (x, 0) := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  have hs := contMDiffOn_transverseCoordinates r V hf hreg hV
  have hi : (mfderiv (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
      (transverseCoordinates r V) (x, 0)).IsInvertible := by
    rw [mfderiv_transverseCoordinates_zero r V hf hreg hV x]
    let A := transverseTangentMap hf hreg x (V x)
    exact ⟨(LinearEquiv.ofBijective A.toLinearMap
      (bijective_transverseTangentMap hf hreg x (V x) hunit)).toContinuousLinearEquiv, rfl⟩
  exact isLocalDiffeomorphAt_between_manifolds (isOpen_transverseCoordinateDomain r V hf hreg hV)
    (zero_mem_transverseCoordinateDomain r V x) hs hi

include hf hreg hV in
/-- The original height increases at unit speed at the zero section of these coordinates. -/
theorem hasDerivAt_height_transverseCoordinates_zero (x : {x : M // f x = b})
    (hunit : mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1) :
    HasDerivAt (fun t : ℝ => f (transverseCoordinates r V (x, t))) 1 0 := by
  let _ := chartedSpace hf hreg
  have hs := (contMDiffOn_transverseCoordinates r V hf hreg hV).contMDiffAt
    ((isOpen_transverseCoordinateDomain r V hf hreg hV).mem_nhds
      (zero_mem_transverseCoordinateDomain r V x))
  have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ => (x, t)) 0 := contMDiffAt_const.prodMk contMDiffAt_id
  have hcurve := ((hs.comp 0 hpair).mdifferentiableAt (by simp)).hasMFDerivAt
  change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0) at hcurve
  rw [mfderiv_transverseCoordinates_time_zero r V x] at hcurve
  have hc := (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp 0 hcurve
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hc.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro t
  change ℝ at t
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  have hd : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (transverseCoordinates r V (x, 0)) : E →L[ℝ] ℝ) =
      L := by
    rw [transverseCoordinates_zero r V x]
    rfl
  change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (transverseCoordinates r V (x, 0)) : E →L[ℝ] ℝ)
    (t • (V x : E)) = t • (1 : ℝ)
  exact (congrArg (fun T : E →L[ℝ] ℝ => T (t • (V x : E))) hd).trans
    ((L.map_smul t (V x)).trans (congrArg (fun a : ℝ => t • a) hunit))

end RegularLevel

end Wikipedia.SmoothSixDPoincare
