import Wikipedia.NoExoticSixSphere.JamesSpherePairingSixSigns
import Wikipedia.NoExoticSixSphere.JamesSphereCommutatorFourLetters
import Wikipedia.NoExoticSixSphere.JamesSphereSixthWordSum

/-!
# The six actual pair terms in the meridian commutator's Hopf image

The self-variable terms factor through S3 and vanish on H6. The four
mixed terms have coefficients 1, 1, -1, 1 on the original product
generator, by the proved cubical reflection and block-exchange formulas.
These are statements about the actual sphere-pairing maps.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomology PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.HopfPairTerms

abbrev Source := Fin 2 → Sphere 3

def first : C(Source, Sphere 3) := ContinuousMap.eval 0

def second : C(Source, Sphere 3) := ContinuousMap.eval 1

def reflectedFirst : C(Source, Sphere 3) := PairingSixSigns.reflection.comp first

def reflectedSecond : C(Source, Sphere 3) := PairingSixSigns.reflection.comp second

def term (i : Fin 6) : C(Source, Sphere 6) :=
  ![(pairing 3).comp (first.prodMk second),
    (pairing 3).comp (first.prodMk reflectedFirst),
    (pairing 3).comp (second.prodMk reflectedFirst),
    (pairing 3).comp (first.prodMk reflectedSecond),
    (pairing 3).comp (second.prodMk reflectedSecond),
    (pairing 3).comp (reflectedFirst.prodMk reflectedSecond)] i

def pairsMap : C(Source, SixthWordSum.Letters 6) := ContinuousMap.pi term

theorem hopf_word_square :
    (hopf 3).comp (MeridianCommutator.fourWordMap 3 (by decide) 0) =
      (SixthWordSum.wordMap 6).comp pairsMap := by
  apply ContinuousMap.ext
  intro v
  exact MeridianCommutator.hopf_fourWordMap 3 (by decide) 0 v

def selfPair : C(Sphere 3, Sphere 6) :=
  (pairing 3).comp ((ContinuousMap.id _).prodMk PairingSixSigns.reflection)

theorem through_three_zero {X : Type} [TopologicalSpace X]
    (f : C(X, Sphere 3)) (g : C(Sphere 3, Sphere 6)) (a : SingularHomology X 6) :
    singularHomologyMap (g.comp f) 6 a = 0 := by
  let : Subsingleton (SingularHomology (Sphere 3) 6) :=
    unitSphere_homology_subsingleton 2 6 (by decide) (by decide)
  have ha : singularHomologyMap f 6 a = 0 := Subsingleton.elim _ _
  rw [singularHomologyMap_comp, LinearMap.comp_apply, ha, map_zero]

theorem term_zero : term 0 = SecondStage.arrayPairing 3 := rfl

theorem term_one : term 1 = selfPair.comp first := rfl

theorem term_two : term 2 = (SmoothCube.reflection 6 (by decide) 3).comp
    ((SphereSixCube.permutation SphereSixCube.blockSwap).comp (SecondStage.arrayPairing 3)) := by
  apply ContinuousMap.ext
  intro v
  exact PairingSixSigns.pairing_reverse_reflection (v 0) (v 1)

theorem term_three : term 3 =
    (SmoothCube.reflection 6 (by decide) 3).comp (SecondStage.arrayPairing 3) := by
  apply ContinuousMap.ext
  intro v
  exact PairingSixSigns.pairing_reflection_right (v 0) (v 1)

theorem term_four : term 4 = selfPair.comp second := rfl

theorem term_five : term 5 = (SmoothCube.reflection 6 (by decide) 0).comp
    ((SmoothCube.reflection 6 (by decide) 3).comp (SecondStage.arrayPairing 3)) := by
  apply ContinuousMap.ext
  intro v
  exact PairingSixSigns.pairing_reflection_both (v 0) (v 1)

theorem term_productGenerator (i : Fin 6) :
    singularHomologyMap (term i) 6 TwoLetterHomology.productGenerator =
      ![unitSphereTopClass 5, 0, unitSphereTopClass 5, -unitSphereTopClass 5,
        0, unitSphereTopClass 5] i := by
  fin_cases i
  · exact TwoLetterHomology.pairing_productGenerator
  · exact through_three_zero first selfPair _
  · change singularHomologyMap (term 2) 6 TwoLetterHomology.productGenerator = unitSphereTopClass 5
    rw [term_two]
    simp only [singularHomologyMap_comp, LinearMap.comp_apply]
    rw [SphereSixCube.reflection_homology, SphereSixCube.blockSwap_homology, neg_neg]
    exact TwoLetterHomology.pairing_productGenerator
  · change singularHomologyMap (term 3) 6 TwoLetterHomology.productGenerator = -unitSphereTopClass 5
    rw [term_three]
    simp only [singularHomologyMap_comp, LinearMap.comp_apply]
    rw [SphereSixCube.reflection_homology, TwoLetterHomology.pairing_productGenerator]
  · exact through_three_zero second selfPair _
  · change singularHomologyMap (term 5) 6 TwoLetterHomology.productGenerator = unitSphereTopClass 5
    rw [term_five]
    simp only [singularHomologyMap_comp, LinearMap.comp_apply]
    rw [SphereSixCube.reflection_homology, SphereSixCube.reflection_homology, neg_neg]
    exact TwoLetterHomology.pairing_productGenerator

theorem pairsMap_coordinate (i : Fin 6) (a : SingularHomology Source 6) :
    singularHomologyMap (SixthWordSum.coordinate 6 i) 6
      (singularHomologyMap pairsMap 6 a) = singularHomologyMap (term i) 6 a := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

theorem hopf_word_sum (a : SingularHomology Source 6) :
    singularHomologyMap ((hopf 3).comp (MeridianCommutator.fourWordMap 3 (by decide) 0)) 6 a =
      ∑ i : Fin 6, singularHomologyMap (inclusion 6) 6 (singularHomologyMap (term i) 6 a) := by
  rw [hopf_word_square, singularHomologyMap_comp, LinearMap.comp_apply,
    SixthWordSum.wordMap_homology]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (singularHomologyMap (inclusion 6) 6) (pairsMap_coordinate i a)

theorem hopf_word_productGenerator :
    singularHomologyMap ((hopf 3).comp (MeridianCommutator.fourWordMap 3 (by decide) 0)) 6
      TwoLetterHomology.productGenerator =
        (2 : ℤ) • singularHomologyMap (inclusion 6) 6 (unitSphereTopClass 5) := by
  rw [hopf_word_sum]
  simp only [term_productGenerator, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, map_zero, map_neg, add_zero, zero_add]
  change _ = (2 : ℤ) • singularHomologyMap (inclusion 6) 6 (unitSphereTopClass 5)
  abel

end NoExoticSixSphere.JamesSphere.HopfPairTerms
