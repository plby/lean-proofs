import Wikipedia.NoExoticSixSphere.JamesSecondHopfMap
import Wikipedia.NoExoticSixSphere.EuclideanFactorProduct

/-!
# The second James--Hopf map for the actual standard spheres

The pairing is the actual product-compactification quotient, written in
the standard Euclidean sphere coordinates. It sends either sphere pole
to the target pole. The induced continuous James--Hopf map kills the
one-letter inclusion and has exactly this pairing as its two-letter value.

No loop-space equivalence, fibration theorem, or EHP exactness is assumed.
-/

noncomputable section

namespace NoExoticSixSphere.JamesSphere

def pairing (n : ℕ) : C(Sphere n × Sphere n, Sphere (n + n)) :=
  ⟨fun p ↦ euclideanOnePointSphere (n + n)
    ((EuclideanFactorProduct.productCoordinates n n).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm p.1,
        (euclideanOnePointSphere n).symm p.2))),
    (euclideanOnePointSphere (n + n)).continuous.comp
      ((EuclideanFactorProduct.productCoordinates n n).onePointCongr.continuous.comp
        (OnePointProduct.continuous_map.comp
          (((euclideanOnePointSphere n).symm.continuous.comp continuous_fst).prodMk
            ((euclideanOnePointSphere n).symm.continuous.comp continuous_snd))))⟩

theorem pairing_left_pole (n : ℕ) (x : Sphere n) :
    pairing n (spherePole n, x) = spherePole (n + n) := by
  change euclideanOnePointSphere (n + n)
    ((EuclideanFactorProduct.productCoordinates n n).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm (spherePole n),
        (euclideanOnePointSphere n).symm x))) = _
  rw [← euclideanOnePointSphere_infty n, Homeomorph.symm_apply_apply,
    OnePointProduct.map_infty_left]
  exact euclideanOnePointSphere_infty (n + n)

theorem pairing_right_pole (n : ℕ) (x : Sphere n) :
    pairing n (x, spherePole n) = spherePole (n + n) := by
  change euclideanOnePointSphere (n + n)
    ((EuclideanFactorProduct.productCoordinates n n).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm x,
        (euclideanOnePointSphere n).symm (spherePole n)))) = _
  rw [← euclideanOnePointSphere_infty n, Homeomorph.symm_apply_apply,
    OnePointProduct.map_infty_right]
  exact euclideanOnePointSphere_infty (n + n)

def hopf (n : ℕ) :
    C(James.Space (Sphere n) (spherePole n), James.Space (Sphere (n + n)) (spherePole (n + n))) :=
  James.secondHopfMap (spherePole n) (spherePole (n + n)) (fun x y ↦ pairing n (x, y))
    (pairing_left_pole n) (pairing_right_pole n) (pairing n).continuous

theorem hopf_one (n : ℕ) : hopf n 1 = 1 := rfl

theorem hopf_letter (n : ℕ) (x : Sphere n) : hopf n (James.letter (spherePole n) x) = 1 :=
  James.secondHopf_letter (spherePole n) (spherePole (n + n)) (fun x y ↦ pairing n (x, y))
    (pairing_left_pole n) (pairing_right_pole n) x

theorem hopf_two_letters (n : ℕ) (x y : Sphere n) :
    hopf n (James.letter (spherePole n) x * James.letter (spherePole n) y) =
      James.letter (spherePole (n + n)) (pairing n (x, y)) :=
  James.secondHopf_two_letters (spherePole n) (spherePole (n + n))
    (fun x y ↦ pairing n (x, y)) (pairing_left_pole n) (pairing_right_pole n) x y

def inclusion (n : ℕ) : C(Sphere n, James.Space (Sphere n) (spherePole n)) :=
  ⟨James.letter (spherePole n), James.continuous_letter (spherePole n)⟩

theorem hopf_inclusion (n : ℕ) : (hopf n).comp (inclusion n) = ContinuousMap.const _ 1 := by
  apply ContinuousMap.ext
  intro x
  exact hopf_letter n x

end NoExoticSixSphere.JamesSphere
