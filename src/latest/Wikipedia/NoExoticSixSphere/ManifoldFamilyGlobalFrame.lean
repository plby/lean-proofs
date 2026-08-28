import Wikipedia.NoExoticSixSphere.SphereThreeFramedDerivative
import Wikipedia.NoExoticSixSphere.ManifoldSphereDisk
import Wikipedia.NoExoticSixSphere.ManifoldPuncturedCylinder
import Wikipedia.NoExoticSixSphere.RectangularOrthonormalization
import Wikipedia.NoExoticSixSphere.PartialFrameDimensionCoordinates

/-!
# The actual global partial-frame map of a nonsingular punctured family

Combine the original manifold's normal frame with the actual spatial
derivative in the quaternionic source frame. The two ranges are orthogonal,
so the combined operator is injective wherever the original spatial
derivative is injective. Gram--Schmidt therefore gives a continuous genuine
partial-frame map on the actual punctured cylinder.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (g : ℝ → Sphere 3 → M)

def familyTangentOperator (p : ℝ × Sphere 3) : Vector 3 →L[ℝ] Vector e.ambientDimension :=
  SphereThreeTangentFrame.framedDerivative (e.toFun ∘ g p.1) p.2

def familyNormalOperator (p : ℝ × Sphere 3) :
    Vector (e.ambientDimension - 6) →L[ℝ] Vector e.ambientDimension :=
  (e.normalFrameOnSphere a (g p.1) p.2).val

def normalSpatialOperator (p : ℝ × Sphere 3) :
    Vector ((e.ambientDimension - 6) + 3) →L[ℝ] Vector e.ambientDimension :=
  (((e.familyNormalOperator a g p).comp (ContinuousLinearMap.fst ℝ _ _)) +
    ((e.familyTangentOperator g p).comp (ContinuousLinearMap.snd ℝ _ _))).comp
      EuclideanSpace.finAddEquivProd.toContinuousLinearMap

theorem normalSpatialOperator_apply (p : ℝ × Sphere 3)
    (v : Vector ((e.ambientDimension - 6) + 3)) :
    e.normalSpatialOperator a g p v =
      e.familyNormalOperator a g p (EuclideanSpace.finAddEquivProd v).1 +
        e.familyTangentOperator g p (EuclideanSpace.finAddEquivProd v).2 := rfl

variable (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

include hg

theorem contMDiff_familyTangentOperator :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3))
      𝓘(ℝ, Vector 3 →L[ℝ] Vector e.ambientDimension) ∞ (e.familyTangentOperator g) :=
  SphereThreeTangentFrame.contMDiff_framedDerivative_family
    (fun t x ↦ e.toFun (g t x)) (e.smooth.comp hg)

theorem contMDiff_familyNormalOperator :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3))
      𝓘(ℝ, Vector (e.ambientDimension - 6) →L[ℝ] Vector e.ambientDimension) ∞
        (e.familyNormalOperator a g) :=
  a.contMDiff_orthonormal.comp hg

theorem contMDiff_normalSpatialOperator :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3))
      𝓘(ℝ, Vector ((e.ambientDimension - 6) + 3) →L[ℝ] Vector e.ambientDimension) ∞
        (e.normalSpatialOperator a g) :=
  (((e.contMDiff_familyNormalOperator a g hg).clm_comp contMDiff_const).add
    ((e.contMDiff_familyTangentOperator g hg).clm_comp contMDiff_const)).clm_comp contMDiff_const

theorem familyNormalOperator_orthogonal (p : ℝ × Sphere 3) :
    (e.familyNormalOperator a g p).range ≤ (e.familyTangentOperator g p).rangeᗮ := by
  have hs : ContMDiff (𝓡 3) (𝓡 6) ∞ (g p.1) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  change (e.normalFrameOnSphere a (g p.1) p.2).val.range ≤
    (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ g p.1) p.2).rangeᗮ
  rw [SphereThreeTangentFrame.range_framedDerivative _ (e.smooth.comp hs)]
  exact e.normalFrameOnSphere_normal a (g p.1) hs p.2

theorem injective_familyTangentOperator (p : ℝ × Sphere 3)
    (hi : Injective (mfderiv (𝓡 3) (𝓡 6) (g p.1) p.2)) :
    Injective (e.familyTangentOperator g p) := by
  have hs : ContMDiff (𝓡 3) (𝓡 6) ∞ (g p.1) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  apply SphereThreeTangentFrame.injective_framedDerivative _ (e.smooth.comp hs)
  rw [mfderiv_comp p.2 (e.smooth.mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp))]
  exact (e.injective_mfderiv (g p.1 p.2)).comp hi

theorem injective_normalSpatialOperator (p : ℝ × Sphere 3)
    (hi : Injective (mfderiv (𝓡 3) (𝓡 6) (g p.1) p.2)) :
    Injective (e.normalSpatialOperator a g p) := by
  let A := e.familyNormalOperator a g p
  let B := e.familyTangentOperator g p
  have hA : Injective A := Stiefel.injective (e.normalFrameOnSphere a (g p.1) p.2)
  have hB : Injective B := e.injective_familyTangentOperator g hg p hi
  have hd : Disjoint A.range B.range :=
    B.range.orthogonal_disjoint.symm.mono_left (e.familyNormalOperator_orthogonal a g hg p)
  have hc : Injective (A.toLinearMap.coprod B.toLinearMap) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_coprod_of_disjoint_range _ _ hd,
      LinearMap.ker_eq_bot.mpr hA, LinearMap.ker_eq_bot.mpr hB, Submodule.prod_bot]
  exact hc.comp EuclideanSpace.finAddEquivProd.injective

variable (P : SphereFamily.ParityBallSystem g)

def puncturedFamilyFrameMap :
    C(P.puncturedCylinder, Space e.ambientDimension ((e.ambientDimension - 6) + 3)) :=
  Orthonormalization.map (fun q : P.puncturedCylinder ↦ e.normalSpatialOperator a g q.val)
    (fun q ↦ e.injective_normalSpatialOperator a g hg q.val
      (P.injective_mfderiv_on_puncturedCylinder q.val q.property))
    ((e.contMDiff_normalSpatialOperator a g hg).continuous.comp continuous_subtype_val)

theorem puncturedFamilyFrameMap_value (q : P.puncturedCylinder) :
    (e.puncturedFamilyFrameMap a g hg P q).val =
      (Orthonormalization.linearMap (e.normalSpatialOperator a g) q.val).toContinuousLinearMap :=
  rfl

theorem puncturedFamilyFrameMap_range (q : P.puncturedCylinder) :
    (e.puncturedFamilyFrameMap a g hg P q).val.range =
      (e.normalSpatialOperator a g q.val).range :=
  Orthonormalization.frame_range (fun q : P.puncturedCylinder ↦ e.normalSpatialOperator a g q.val)
    (fun q ↦ e.injective_normalSpatialOperator a g hg q.val
      (P.injective_mfderiv_on_puncturedCylinder q.val q.property)) q

def puncturedGlobalFrameMap :
    C(P.puncturedCylinder,
      Space (3 + (((e.ambientDimension - 6) + 1) + 2)) (((e.ambientDimension - 6) + 1) + 2)) := by
  have hd := e.dimension_le_ambient (g 0 (pole 3))
  have hN : e.ambientDimension = 3 + (((e.ambientDimension - 6) + 1) + 2) := by omega
  have hk : (e.ambientDimension - 6) + 3 = ((e.ambientDimension - 6) + 1) + 2 := by omega
  let H : C(Space e.ambientDimension ((e.ambientDimension - 6) + 3),
      Space (3 + (((e.ambientDimension - 6) + 1) + 2)) (((e.ambientDimension - 6) + 1) + 2)) :=
    dimensionHomeomorph hN hk
  exact H.comp (e.puncturedFamilyFrameMap a g hg P)

end NoExoticSixSphere.EuclideanEmbedding
