import Wikipedia.NoExoticSixSphere.JamesSphereHopf
import Wikipedia.NoExoticSixSphere.CubicalProductSuspension
import Wikipedia.NoExoticSixSphere.MooreTimedFamily

/-!
# The actual James map from sphere words to sphere loops

The one-letter loop is the product-compactification suspension adjoint.
Its duration is the distance of the letter from the sphere pole. The
basepoint letter therefore gives the exact Moore-loop identity. The
pointed free-monoid extension is continuous, and normalization gives a
map into Mathlib's native path space.

This constructs the comparison map; it does not assert that the map is
a homotopy equivalence, nor that the James--Hopf sequence is exact.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere

def loopEvaluation (n : ℕ) : C(Sphere n × I, Sphere (n + 1)) :=
  ⟨fun p ↦ euclideanOnePointSphere (n + 1)
    ((EuclideanFactorProduct.productCoordinates n 1).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm p.1,
        CubicalProductSuspension.clock p.2))),
    (euclideanOnePointSphere (n + 1)).continuous.comp
      ((EuclideanFactorProduct.productCoordinates n 1).onePointCongr.continuous.comp
        (OnePointProduct.continuous_map.comp
          (((euclideanOnePointSphere n).symm.continuous.comp continuous_fst).prodMk
            (CubicalProductSuspension.clock.continuous.comp continuous_snd))))⟩

theorem loopEvaluation_zero (n : ℕ) (x : Sphere n) :
    loopEvaluation n (x, 0) = spherePole (n + 1) := by
  change euclideanOnePointSphere (n + 1)
    ((EuclideanFactorProduct.productCoordinates n 1).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm x,
        CubicalProductSuspension.clock 0))) = _
  rw [CubicalProductSuspension.clock_zero, OnePointProduct.map_infty_right]
  exact euclideanOnePointSphere_infty (n + 1)

theorem loopEvaluation_one (n : ℕ) (x : Sphere n) :
    loopEvaluation n (x, 1) = spherePole (n + 1) := by
  change euclideanOnePointSphere (n + 1)
    ((EuclideanFactorProduct.productCoordinates n 1).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm x,
        CubicalProductSuspension.clock 1))) = _
  rw [CubicalProductSuspension.clock_one, OnePointProduct.map_infty_right]
  exact euclideanOnePointSphere_infty (n + 1)

theorem loopEvaluation_pole (n : ℕ) (t : I) :
    loopEvaluation n (spherePole n, t) = spherePole (n + 1) := by
  change euclideanOnePointSphere (n + 1)
    ((EuclideanFactorProduct.productCoordinates n 1).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm (spherePole n),
        CubicalProductSuspension.clock t))) = _
  rw [← euclideanOnePointSphere_infty n, Homeomorph.symm_apply_apply,
    OnePointProduct.map_infty_left]
  exact euclideanOnePointSphere_infty (n + 1)

def unitLoop (n : ℕ) (x : Sphere n) : Path (spherePole (n + 1)) (spherePole (n + 1)) where
  toFun t := loopEvaluation n (x, t)
  continuous_toFun := (loopEvaluation n).continuous.comp (continuous_const.prodMk continuous_id)
  source' := loopEvaluation_zero n x
  target' := loopEvaluation_one n x

theorem continuous_unitLoop (n : ℕ) : Continuous (unitLoop n) :=
  Path.continuous_uncurry_iff.mp (loopEvaluation n).continuous

theorem unitLoop_pole (n : ℕ) : unitLoop n (spherePole n) = Path.refl (spherePole (n + 1)) := by
  apply Path.ext
  funext t
  exact loopEvaluation_pole n t

def mooreGenerator (n : ℕ) (x : Sphere n) : Moore.Loop (spherePole (n + 1)) :=
  Moore.Loop.timed (unitLoop n) (fun x ↦ dist x (spherePole n)) (fun _ ↦ dist_nonneg) x

theorem mooreGenerator_pole (n : ℕ) : mooreGenerator n (spherePole n) = 1 :=
  Moore.Loop.timed_eq_one_of_zero _ _ _ _ (dist_self _)

theorem continuous_mooreGenerator (n : ℕ) : Continuous (mooreGenerator n) := by
  apply Moore.Loop.continuous_timed (unitLoop n) (continuous_unitLoop n)
    (fun x ↦ dist x (spherePole n)) (continuous_id.dist continuous_const)
    (fun _ ↦ dist_nonneg)
  intro x hx
  have he : x = spherePole n := dist_eq_zero.mp hx
  rw [he, unitLoop_pole]

theorem toPath_mooreGenerator (n : ℕ) (x : Sphere n) :
    Moore.Loop.toPath (mooreGenerator n x) = unitLoop n x := by
  apply Moore.Loop.toPath_timed
  intro hx
  have he : x = spherePole n := dist_eq_zero.mp hx
  rw [he, unitLoop_pole]

def mooreComparison (n : ℕ) :
    C(James.Space (Sphere n) (spherePole n), Moore.Loop (spherePole (n + 1))) :=
  ⟨James.lift (spherePole n) (mooreGenerator n),
    James.continuous_lift (spherePole n) (mooreGenerator n) (mooreGenerator_pole n)
      (continuous_mooreGenerator n)⟩

theorem mooreComparison_one (n : ℕ) : mooreComparison n 1 = 1 :=
  map_one (James.lift (spherePole n) (mooreGenerator n))

theorem mooreComparison_mul (n : ℕ) (v w : James.Space (Sphere n) (spherePole n)) :
    mooreComparison n (v * w) = mooreComparison n v * mooreComparison n w :=
  map_mul (James.lift (spherePole n) (mooreGenerator n)) v w

theorem mooreComparison_letter (n : ℕ) (x : Sphere n) :
    mooreComparison n (James.letter (spherePole n) x) = mooreGenerator n x :=
  James.lift_letter (spherePole n) (mooreGenerator n) (mooreGenerator_pole n) x

def loopComparison (n : ℕ) : C(James.Space (Sphere n) (spherePole n),
    Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  ⟨fun w ↦ Moore.Loop.toPath (mooreComparison n w),
    Moore.Loop.continuous_toPath.comp (mooreComparison n).continuous⟩

theorem loopComparison_one (n : ℕ) : loopComparison n 1 = Path.refl (spherePole (n + 1)) := by
  change Moore.Loop.toPath (mooreComparison n 1) = _
  rw [mooreComparison_one, Moore.Loop.toPath_one]

theorem loopComparison_letter (n : ℕ) (x : Sphere n) :
    loopComparison n (James.letter (spherePole n) x) = unitLoop n x := by
  change Moore.Loop.toPath (mooreComparison n (James.letter (spherePole n) x)) = _
  rw [mooreComparison_letter, toPath_mooreGenerator]

end NoExoticSixSphere.JamesSphere
