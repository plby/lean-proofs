import Wikipedia.NoExoticSixSphere.ProductTubeCollapse
import Wikipedia.NoExoticSixSphere.OnePointProductHomotopy
import Wikipedia.NoExoticSixSphere.SphereSuspensionCylinder
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart

/-!
# The actual sphere suspension and the product compactification quotient

The latitude cylinder and the original finite stereographic chart give an
open product chart in the suspended sphere. Collapsing its complement
constructs a continuous map to the actual product compactification. This
map commutes exactly with suspension of every infinity-preserving map.

The quotient collapses the meridian over the old infinity point as well as
the two poles. It is not asserted to be a homeomorphism or a homotopy
equivalence here. Those comparisons remain separate proof obligations.
-/

noncomputable section

open Set Function Topology
open scoped OnePoint

namespace NoExoticSixSphere.SuspensionProductComparison

local notation "V" n => EuclideanSpace ℝ (Fin n)

def finitePoint (n : ℕ) (p : ℝ × V n) : Sphere (n + 1) :=
  SphereCylinder.point n (p.1, euclideanOnePointSphere n (p.2 : OnePoint (V n)))

theorem isOpenEmbedding_finitePoint (n : ℕ) : IsOpenEmbedding (finitePoint n) := by
  have hc : IsOpenEmbedding (SphereCylinder.point n) :=
    (SphereCylinder.chart n).toOpenPartialHomeomorph.isOpenEmbedding rfl
  exact hc.comp ((Homeomorph.refl ℝ).isOpenEmbedding.prodMap
    ((euclideanOnePointSphere n).isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe))

def finiteTube (n : ℕ) (p : Unit × (ℝ × V n)) : Sphere (n + 1) := finitePoint n p.2

theorem isOpenEmbedding_finiteTube (n : ℕ) : IsOpenEmbedding (finiteTube n) :=
  (isOpenEmbedding_finitePoint n).comp (Homeomorph.uniqueProd Unit (ℝ × V n)).isOpenEmbedding

def quotient (n : ℕ) : C(Sphere (n + 1), OnePoint (ℝ × V n)) :=
  ⟨OpenFiberCollapse.collapse (finiteTube n),
    OpenFiberCollapse.continuous_collapse (finiteTube n) (isOpenEmbedding_finiteTube n)⟩

@[simp]
theorem quotient_finitePoint (n : ℕ) (p : ℝ × V n) :
    quotient n (finitePoint n p) = (p : OnePoint (ℝ × V n)) :=
  OpenFiberCollapse.collapse_apply (finiteTube n) (isOpenEmbedding_finiteTube n).injective ((), p)

theorem quotient_eq_coe_iff (n : ℕ) (y : Sphere (n + 1)) (p : ℝ × V n) :
    quotient n y = (p : OnePoint (ℝ × V n)) ↔ finitePoint n p = y := by
  change OpenFiberCollapse.collapse (finiteTube n) y = (p : OnePoint (ℝ × V n)) ↔ _
  rw [OpenFiberCollapse.collapse_eq_coe_iff (finiteTube n)
    (isOpenEmbedding_finiteTube n).injective]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨(), h⟩⟩

theorem quotient_of_not_mem_band (n : ℕ) {y : Sphere (n + 1)}
    (hy : y ∉ SphereCylinder.band n) : quotient n y = ∞ := by
  apply OpenFiberCollapse.collapse_of_not_mem
  rintro ⟨p, rfl⟩
  exact hy (SphereCylinder.tail_point_ne_zero n _)

theorem quotient_point_compactification (n : ℕ) (t : ℝ) (x : OnePoint (V n)) :
    quotient n (SphereCylinder.point n (t, euclideanOnePointSphere n x)) =
      OnePointProduct.map ((t : OnePoint ℝ), x) := by
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePointProduct.map_infty_right]
    apply OpenFiberCollapse.collapse_of_not_mem
    rintro ⟨p, hp⟩
    change SphereCylinder.point n (p.2.1, euclideanOnePointSphere n (p.2.2 : OnePoint (V n))) =
      SphereCylinder.point n (t, euclideanOnePointSphere n ∞) at hp
    have hh := congrArg (SphereCylinder.inverse n) hp
    rw [SphereCylinder.inverse_point, SphereCylinder.inverse_point] at hh
    have he := congrArg (fun q : ℝ × Sphere n ↦ q.2) hh
    exact OnePoint.coe_ne_infty p.2.2 ((euclideanOnePointSphere n).injective he)
  | coe x =>
    change quotient n (finitePoint n (t, x)) = OnePointProduct.map (↑t, ↑x)
    rw [quotient_finitePoint, OnePointProduct.map_coe]

theorem quotient_point (n : ℕ) (p : ℝ × Sphere n) :
    quotient n (SphereCylinder.point n p) =
      OnePointProduct.map ((p.1 : OnePoint ℝ), (euclideanOnePointSphere n).symm p.2) := by
  simpa only [Homeomorph.apply_symm_apply] using
    quotient_point_compactification n p.1 ((euclideanOnePointSphere n).symm p.2)

variable {m n : ℕ}

def sphereMap (f : C(OnePoint (V m), OnePoint (V n))) : C(Sphere m, Sphere n) :=
  (euclideanOnePointSphere n : C(_, _)).comp
    (f.comp ((euclideanOnePointSphere m).symm : C(_, _)))

theorem quotient_suspension_point
    (f : C(OnePoint (V m), OnePoint (V n))) (hf : f ∞ = ∞) (p : ℝ × Sphere m) :
    quotient n (SphereMapSuspension.map (sphereMap f) (SphereCylinder.point m p)) =
      OnePointProduct.productMap (ContinuousMap.id (OnePoint ℝ)) f
        (ContinuousMap.id_apply ∞) hf (quotient m (SphereCylinder.point m p)) := by
  rw [SphereMapSuspension.map_cylinder_point, quotient_point, quotient_point,
    OnePointProduct.productMap_apply]
  change OnePointProduct.map ((p.1 : OnePoint ℝ),
      (euclideanOnePointSphere n).symm
        (euclideanOnePointSphere n (f ((euclideanOnePointSphere m).symm p.2)))) =
    OnePointProduct.map ((p.1 : OnePoint ℝ), f ((euclideanOnePointSphere m).symm p.2))
  rw [Homeomorph.symm_apply_apply]

/-- A commuting diagram of the original maps, including both poles and the collapsed meridian. -/
theorem quotient_suspension (f : C(OnePoint (V m), OnePoint (V n)))
    (hf : f ∞ = ∞) (y : Sphere (m + 1)) :
    quotient n (SphereMapSuspension.map (sphereMap f) y) =
      OnePointProduct.productMap (ContinuousMap.id (OnePoint ℝ)) f
        (ContinuousMap.id_apply ∞) hf (quotient m y) := by
  by_cases hy : y ∈ SphereCylinder.band m
  · have h := quotient_suspension_point f hf (SphereCylinder.inverse m y)
    rwa [SphereCylinder.point_inverse m y hy] at h
  · have hn : SphereMapSuspension.map (sphereMap f) y ∉ SphereCylinder.band n :=
      fun h ↦ hy ((SphereMapSuspension.map_mem_band_iff (sphereMap f) y).mp h)
    rw [quotient_of_not_mem_band n hn, quotient_of_not_mem_band m hy,
      OnePointProduct.productMap_infty]

/-- The same actual quotient, with the added normal coordinate placed last. -/
def rightQuotient (n : ℕ) : C(Sphere (n + 1), OnePoint ((V n) × ℝ)) :=
  ((Homeomorph.prodComm ℝ (V n)).onePointCongr : C(_, _)).comp (quotient n)

theorem rightQuotient_suspension (f : C(OnePoint (V m), OnePoint (V n)))
    (hf : f ∞ = ∞) (y : Sphere (m + 1)) :
    rightQuotient n (SphereMapSuspension.map (sphereMap f) y) =
      OnePointProduct.productMap f (ContinuousMap.id (OnePoint ℝ)) hf
        (ContinuousMap.id_apply ∞) (rightQuotient m y) := by
  change (Homeomorph.prodComm ℝ (V n)).onePointCongr
      (quotient n (SphereMapSuspension.map (sphereMap f) y)) =
    OnePointProduct.productMap f (ContinuousMap.id (OnePoint ℝ)) hf
      (ContinuousMap.id_apply ∞)
      ((Homeomorph.prodComm ℝ (V m)).onePointCongr (quotient m y))
  rw [quotient_suspension, OnePointProduct.productMap_swap]

end NoExoticSixSphere.SuspensionProductComparison
