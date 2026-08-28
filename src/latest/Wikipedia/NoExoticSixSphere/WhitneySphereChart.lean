import Wikipedia.NoExoticSixSphere.WhitneySphereTransversality
import Wikipedia.NoExoticSixSphere.SphereNativeDerivativeCoordinates

/-!
# A chart-contained Whitney sphere in the original six-manifold

The polynomial model lies in the product of closed unit balls. An actual
partial diffeomorphism containing that product preserves its immersion,
unique double point, and native self-transversality.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.WhitneySphere

open GLOrthonormalization SphereCylinder SphereSumNeck

theorem norm_tail_le_one (x : Sphere 3) : ‖tail 2 x.val‖ ≤ 1 := by
  have h := norm_join_sq 2 (head x.val) (tail 2 x.val)
  rw [WhitneySphere.join_head_tail, ClosedHemisphere.unit_norm] at h
  nlinarith [norm_nonneg (tail 2 x.val), sq_nonneg (head x.val)]

theorem abs_head_le_one (x : Sphere 3) : |head x.val| ≤ 1 := by
  have h := norm_join_sq 2 (head x.val) (tail 2 x.val)
  rw [WhitneySphere.join_head_tail, ClosedHemisphere.unit_norm] at h
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg ‖tail 2 x.val‖],
    by nlinarith [sq_nonneg ‖tail 2 x.val‖]⟩

theorem map_mem_product (x : Sphere 3) :
    map x ∈ closedBall (0 : Vector 3) 1 ×ˢ closedBall (0 : Vector 3) 1 := by
  refine ⟨?_, ?_⟩
  · simpa only [map, ambientMap, mem_closedBall, dist_zero_right] using norm_tail_le_one x
  change dist (head x.val • tail 2 x.val) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul (abs_head_le_one x) (norm_tail_le_one x)
    (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (hprod : closedBall (0 : Vector 3) 1 ×ˢ closedBall (0 : Vector 3) 1 ⊆ Φ.source)

def chartMap (x : Sphere 3) : M := Φ (map x)

include hprod

theorem localDiffeomorph_chart (x : Sphere 3) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) ∞ Φ (map x) :=
  ⟨Φ, hprod (map_mem_product x), fun _ _ ↦ rfl⟩

theorem contMDiff_chartMap : ContMDiff (𝓡 3) (𝓡 6) ∞ (chartMap Φ) := by
  intro x
  exact (localDiffeomorph_chart Φ hprod x).contMDiffAt.comp x (contMDiff_map x)

def chartContinuousMap : C(Sphere 3, M) := ⟨chartMap Φ, (contMDiff_chartMap Φ hprod).continuous⟩

def chartTargetDerivative (z : Vector 3 × Vector 3) :
    (Vector 3 × Vector 3) →L[ℝ] Vector 6 :=
  mfderiv 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) Φ z

theorem nativeDerivative_chartMap (x : Sphere 3) :
    nativeSphereDerivative (chartMap Φ) x =
      (chartTargetDerivative Φ (map x)).comp (modelDerivative x) :=
  mfderiv_comp (f := map) (g := Φ) x
    ((localDiffeomorph_chart Φ hprod x).mdifferentiableAt (by simp))
    (contMDiff_map.mdifferentiableAt (by simp))

theorem injective_mfderiv_chartMap (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (chartMap Φ) x) := by
  change Injective (nativeSphereDerivative (chartMap Φ) x)
  rw [nativeDerivative_chartMap Φ hprod]
  exact ((localDiffeomorph_chart Φ hprod x).mfderivToContinuousLinearEquiv
    (by simp)).injective.comp (injective_mfderiv_map x)

theorem chartMap_eq_iff (x y : Sphere 3) : chartMap Φ x = chartMap Φ y ↔ map x = map y := by
  constructor
  · exact Φ.toOpenPartialHomeomorph.injOn (hprod (map_mem_product x)) (hprod (map_mem_product y))
  · exact congrArg Φ

theorem selfTransverse_chartMap : NativeSphereSelfTransverse (chartMap Φ) := by
  intro x y hne he
  have hxy := (chartMap_eq_iff Φ hprod x y).mp he
  have hD : Surjective (chartTargetDerivative Φ (map x)) :=
    ((localDiffeomorph_chart Φ hprod x).mfderivToContinuousLinearEquiv (by simp)).surjective
  unfold NativeSphereTransverseAt
  rw [nativeDerivative_chartMap Φ hprod, nativeDerivative_chartMap Φ hprod, ← hxy]
  intro w
  obtain ⟨z, hz⟩ := hD w
  obtain ⟨p, hp⟩ := selfTransverse_map x y hne hxy z
  refine ⟨p, ?_⟩
  change chartTargetDerivative Φ (map x) (modelDerivative x p.1) +
    chartTargetDerivative Φ (map x) (modelDerivative y p.2) = w
  rw [← map_add]
  exact (congrArg (chartTargetDerivative Φ (map x)) hp).trans hz

theorem pairs_chartMap : SphereSelfIntersections.pairs (chartMap Φ) =
    SphereSelfIntersections.pairs map := by
  ext p
  exact and_congr_right (fun _ ↦ chartMap_eq_iff Φ hprod p.1 p.2)

theorem unordered_ncard_chartMap :
    Nat.card (SphereSelfIntersections.Unordered (chartMap Φ)) = 1 := by
  have hfin : (SphereSelfIntersections.pairs (chartMap Φ)).Finite := by
    rw [pairs_chartMap Φ hprod]
    exact finite_pairs
  have h := SphereSelfIntersections.ordered_ncard_eq_twice_unordered (chartMap Φ) hfin
  rw [pairs_chartMap Φ hprod, ordered_ncard] at h
  omega

theorem unorderedParity_chartMap : SphereSelfIntersections.unorderedParity (chartMap Φ) = 1 := by
  simp only [SphereSelfIntersections.unorderedParity, unordered_ncard_chartMap Φ hprod,
    Nat.cast_one]

end NoExoticSixSphere.WhitneySphere
