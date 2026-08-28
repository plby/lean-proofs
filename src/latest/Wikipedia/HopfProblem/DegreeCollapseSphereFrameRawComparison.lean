import Wikipedia.HopfProblem.DegreeCollapseNormalColumnOrthonormalization
import Wikipedia.NoExoticSixSphere.ImmersedSphereFrameParity

/-!
# Comparing the actual geometric sphere operator with its raw normal columns

Only the normal Gram--Schmidt step is replaced by a proved homotopy.
The source tangent columns remain the original global quaternionic framed
derivative. The geometric parity comparison retains the entire original
twisted stabilization.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereFrameRawComparison

open NoExoticSixSphere GLOrthonormalization Stiefel SpanningDiskFrameCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M)

def rawNormal (s : Sphere 3) : Vector (e.ambientDimension - 6) →L[ℝ] Vector e.ambientDimension :=
  a.ambient (f s)

def tangent (s : Sphere 3) : Vector 3 →L[ℝ] Vector e.ambientDimension :=
  SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s

variable (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

include hf in
theorem contMDiff_rawNormal :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vector (e.ambientDimension - 6) →L[ℝ] Vector e.ambientDimension)
      ∞ (rawNormal e a f) := a.contMDiff_ambient.comp hf

include hf in
theorem contMDiff_tangent :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] Vector e.ambientDimension) ∞ (tangent e f) := by
  have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞
      (Function.uncurry (fun _ : ℝ ↦ f)) := hf.comp contMDiff_snd
  exact (e.contMDiff_familyTangentOperator (fun _ : ℝ ↦ f) hg).comp
    ((contMDiff_const (c := (0 : ℝ))).prodMk contMDiff_id)

include hf hd in
theorem tangent_injective (s : Sphere 3) : Injective (tangent e f s) := by
  have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞
      (Function.uncurry (fun _ : ℝ ↦ f)) := hf.comp contMDiff_snd
  exact e.injective_familyTangentOperator (fun _ : ℝ ↦ f) hg (0, s) (hd s)

include hf in
theorem rawNormal_disjoint (s : Sphere 3) :
    Disjoint (rawNormal e a f s).range (tangent e f s).range := by
  have hN : (rawNormal e a f s).range ≤ (tangent e f s).rangeᗮ := by
    change (a.ambient (f s)).range ≤
      (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s).rangeᗮ
    rw [SphereThreeTangentFrame.range_framedDerivative _ (e.smooth.comp hf),
      a.ambient_range, ← a.orthonormal_range (f s)]
    exact e.normalFrameOnSphere_normal a f hf s
  exact (tangent e f s).range.orthogonal_disjoint.symm.mono_left hN

def rawMap : C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)) :=
  NormalColumnOrthonormalization.rawMap (rawNormal e a f) (tangent e f)
    (contMDiff_rawNormal e a f hf).continuous (contMDiff_tangent e f hf).continuous
    (fun s ↦ a.ambient_injective (f s)) (tangent_injective e f hf hd)
    (rawNormal_disjoint e a f hf)

theorem rawMap_value (s : Sphere 3) :
    (rawMap e a f hf hd s).val = OperatorSum.operator (a.ambient (f s))
      (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s) := rfl

theorem normalizedMap_eq :
    NormalColumnOrthonormalization.normalizedMap (rawNormal e a f) (tangent e f)
      (contMDiff_rawNormal e a f hf).continuous (contMDiff_tangent e f hf).continuous
      (fun s ↦ a.ambient_injective (f s)) (tangent_injective e f hf hd)
      (rawNormal_disjoint e a f hf) = e.sphereFrameOperatorMap a f hf hd := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  rfl

theorem rawMap_homotopic :
    (rawMap e a f hf hd).Homotopic (e.sphereFrameOperatorMap a f hf hd) := by
  have h : (rawMap e a f hf hd).Homotopic
      (NormalColumnOrthonormalization.normalizedMap (rawNormal e a f) (tangent e f)
        (contMDiff_rawNormal e a f hf).continuous (contMDiff_tangent e f hf).continuous
        (fun s ↦ a.ambient_injective (f s)) (tangent_injective e f hf hd)
        (rawNormal_disjoint e a f hf)) :=
    ⟨NormalColumnOrthonormalization.homotopy (rawNormal e a f) (tangent e f)
      (contMDiff_rawNormal e a f hf).continuous (contMDiff_tangent e f hf).continuous
      (fun s ↦ a.ambient_injective (f s)) (tangent_injective e f hf hd)
      (rawNormal_disjoint e a f hf)⟩
  rwa [normalizedMap_eq] at h

theorem parity_eq_raw : e.immersedSphereFrameParity a f hf hd =
    Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 7)
      (by have h := e.dimension_le_ambient (f (Stiefel.pole 3)); omega) (by omega)
      (twistedBlockMap (rawMap e a f hf hd)) :=
  (Monomorphism.sphereParityOfDimension_homotopic _ _ _
    (twistedBlockMap_homotopic (rawMap_homotopic e a f hf hd))).symm

end Wikipedia.HopfProblem.DegreeCollapse.SphereFrameRawComparison
