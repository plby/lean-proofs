import Wikipedia.NoExoticSixSphere.EuclideanFactorProduct
import Wikipedia.NoExoticSixSphere.SphereRepresentativeCoordinates
import Wikipedia.NoExoticSixSphere.CubicalStableSixVanishing

/-!
# Every finite product factor matches the actual ordinary suspensions

The direct compactification product with a Euclidean q-space is compared
with q literal sphere suspensions. Exact coordinate squares make the
comparison persist after every further finite suspension. Neither map is
assumed or asserted to be nullhomotopic.
-/

noncomputable section

open scoped OnePoint

namespace NoExoticSixSphere.SphereMapSuspension

theorem finite_map_nullhomotopic_iff {m n : ℕ} (f : C(Sphere m, Sphere n)) :
    (∃ r : ℕ, (iterate (map f) r).Nullhomotopic) ↔
      ∃ r : ℕ, (iterate f r).Nullhomotopic := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r + 1, (iterate_map_nullhomotopic_iff f r).mp hr⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, (iterate_map_nullhomotopic_iff f r).mpr ?_⟩
    exact map_nullhomotopic hr

theorem finite_iterate_nullhomotopic_iff {m n : ℕ} (f : C(Sphere m, Sphere n)) (q : ℕ) :
    (∃ r : ℕ, (iterate (iterate f q) r).Nullhomotopic) ↔
      ∃ r : ℕ, (iterate f r).Nullhomotopic := by
  induction q with
  | zero => rfl
  | succ q ih => exact (finite_map_nullhomotopic_iff (iterate f q)).trans ih

end NoExoticSixSphere.SphereMapSuspension

namespace NoExoticSixSphere.EuclideanFactorProduct

open OnePointProduct SphereMapSuspension SuspensionProductComparison

variable {m n : ℕ} (f : C(OnePoint (V m), OnePoint (V n))) (hf : f ∞ = ∞)

def sphereProductMap (q : ℕ) : C(Sphere (m + q), Sphere (n + q)) :=
  sphereMap (compactMap f hf q)

theorem iterate_zero_nullhomotopic_iff (r : ℕ) :
    (iterate (sphereProductMap f hf 0) r).Nullhomotopic ↔
      (iterate (sphereMap f) r).Nullhomotopic :=
  SphereRepresentative.iterate_nullhomotopic_iff
    (euclideanOnePointSphere (m + 0)) (euclideanOnePointSphere (n + 0))
    (euclideanOnePointSphere m) (euclideanOnePointSphere n)
    (zeroCoordinates m).onePointCongr (zeroCoordinates n).onePointCongr
    (compactMap f hf 0) f (zero_square f hf) r

theorem iterate_step_nullhomotopic_iff (q r : ℕ) :
    (iterate (productSphereMap (compactMap f hf q) (compactMap_infty f hf q)) r).Nullhomotopic ↔
      (iterate (sphereProductMap f hf (q + 1)) r).Nullhomotopic :=
  SphereRepresentative.iterate_nullhomotopic_iff
    (productSphereHomeomorph (m + q)) (productSphereHomeomorph (n + q))
    (euclideanOnePointSphere (m + (q + 1))) (euclideanOnePointSphere (n + (q + 1)))
    (stepCoordinates m q).onePointCongr (stepCoordinates n q).onePointCongr
    (addFactor (compactMap f hf q) (compactMap_infty f hf q) ℝ)
    (compactMap f hf (q + 1)) (step_square f hf q) r

theorem iterate_nullhomotopic_iff_product (q r : ℕ) :
    (iterate (iterate (sphereMap f) q) r).Nullhomotopic ↔
      (iterate (sphereProductMap f hf q) r).Nullhomotopic := by
  induction q generalizing r with
  | zero => exact (iterate_zero_nullhomotopic_iff f hf r).symm
  | succ q ih =>
    change (iterate (SphereMapSuspension.map (iterate (sphereMap f) q)) r).Nullhomotopic ↔ _
    exact (iterate_map_nullhomotopic_iff (iterate (sphereMap f) q) r).trans
      ((ih (r + 1)).trans
        ((iterate_map_nullhomotopic_iff (sphereProductMap f hf q) r).symm.trans
          ((iterate_suspension_nullhomotopic_iff_product
            (compactMap f hf q) (compactMap_infty f hf q) r).trans
              (iterate_step_nullhomotopic_iff f hf q r))))

theorem product_nullhomotopic_iff (q : ℕ) :
    (sphereProductMap f hf q).Nullhomotopic ↔ (iterate (sphereMap f) q).Nullhomotopic :=
  (iterate_nullhomotopic_iff_product f hf q 0).symm

theorem finite_product_nullhomotopic_iff (q : ℕ) :
    (∃ r : ℕ, (iterate (sphereProductMap f hf q) r).Nullhomotopic) ↔
      ∃ r : ℕ, (iterate (sphereMap f) r).Nullhomotopic :=
  (exists_congr (fun r ↦ (iterate_nullhomotopic_iff_product f hf q r).symm)).trans
    (finite_iterate_nullhomotopic_iff (sphereMap f) q)

end NoExoticSixSphere.EuclideanFactorProduct
