import Wikipedia.NoExoticSixSphere.CubicalStableSixStages
import Wikipedia.NoExoticSixSphere.NativeSixSphereCollapse

/-!
# Native cubical-group vanishing is the original finite-suspension condition

The homomorphic product suspensions and the original ordinary suspensions
have the same vanishing criterion at every stage, even after any specified
number of further ordinary suspensions. Thus the constructed group's
identity criterion applies to the original framed collapse. This is not
a computation of the group and does not assert that a candidate is zero.
-/

noncomputable section

namespace NoExoticSixSphere.SphereMapSuspension

theorem iterate_map_heq {m n : ℕ} (f : C(Sphere m, Sphere n)) (r : ℕ) :
    HEq (iterate (map f) r) (iterate f (r + 1)) := by
  induction r with
  | zero => rfl
  | succ r ih => exact map_heq (Nat.add_right_comm m 1 r) (Nat.add_right_comm n 1 r) ih

theorem iterate_map_nullhomotopic_iff {m n : ℕ} (f : C(Sphere m, Sphere n)) (r : ℕ) :
    (iterate (map f) r).Nullhomotopic ↔ (iterate f (r + 1)).Nullhomotopic :=
  nullhomotopic_iff_of_heq (Nat.add_right_comm m 1 r) (Nat.add_right_comm n 1 r)
    (iterate_map_heq f r)

end NoExoticSixSphere.SphereMapSuspension

namespace NoExoticSixSphere.CubicalStableSix

open StableSixSphereMaps SmoothCube SphereMapSuspension

theorem basedLift_iterate_nullhomotopic_iff {k l : ℕ} (h : k ≤ l) (f : BasedStage k) :
    ∀ r : ℕ, (iterate (basedLift h f).val r).Nullhomotopic ↔
      (iterate (StableSixSphereMaps.liftMap h f.val) r).Nullhomotopic := by
  induction l, h using Nat.le_induction with
  | base =>
    intro r
    rw [basedLift_self, StableSixSphereMaps.liftMap_self]
  | succ l h ih =>
    intro r
    rw [basedLift_succ h, StableSixSphereMaps.liftMap_succ h]
    exact (CubicalSphereSuspension.iterate_product_nullhomotopic_iff (basedLift h f) r).trans
      ((iterate_map_nullhomotopic_iff (basedLift h f).val r).trans
        ((ih (r + 1)).trans
          (iterate_map_nullhomotopic_iff (StableSixSphereMaps.liftMap h f.val) r).symm))

theorem ofNative_sphereClass_eq_one_iff {k : ℕ} (f : BasedStage k) :
    ofNative (sphereClass f) = 1 ↔ ofMap f.val = nullClass := by
  rw [ofNative_eq_one_iff, ofMap_eq_nullClass_iff_lift]
  apply exists_congr
  intro l
  apply exists_congr
  intro h
  rw [transition_sphereClass, sphereClass_eq_one_iff_nullhomotopic (by omega)]
  exact basedLift_iterate_nullhomotopic_iff h f 0

end NoExoticSixSphere.CubicalStableSix

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a) (hd : 8 ≤ e.ambientDimension)

def cubicalStableClass : CubicalStableSix.Group :=
  CubicalStableSix.ofNative (d.nativeSixthStageClass hd)

theorem cubicalStableClass_eq_one_iff :
    d.cubicalStableClass hd = 1 ↔ d.sixthStableClass hd = StableSixSphereMaps.nullClass :=
  CubicalStableSix.ofNative_sphereClass_eq_one_iff
    ⟨d.sixthStageMap hd, d.sixthStageMap_pole hd⟩

theorem cubicalStableClass_eq_one_iff_finite :
    d.cubicalStableClass hd = 1 ↔
      ∃ r : ℕ, (SphereMapSuspension.iterate d.sphereMap r).Nullhomotopic := by
  rw [d.cubicalStableClass_eq_one_iff, d.sixthStableClass_eq_null_iff]

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
