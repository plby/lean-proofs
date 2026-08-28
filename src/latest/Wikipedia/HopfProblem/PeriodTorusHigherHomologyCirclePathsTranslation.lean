import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# Circle translations preserve actual singular homology classes

Translation by a real number on the actual additive circle is homotopic
to the identity by scaling that number to zero. Homotopy invariance proves
that the induced map on actual integral singular homology is the identity
in every degree. Hurewicz naturality specializes this to arbitrary loops,
without requiring the original and translated basepoints to agree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology.CirclePaths

open CircleTopology FirstHurewicz SingularMayerVietoris

/-- Actual translation on the quotient circle by a chosen real representative. -/
def circleTranslation (a : ℝ) : C(Circle, Circle) :=
  ⟨fun z => (a : Circle) + z, by
    exact (continuous_const : Continuous (fun _ : Circle => (a : Circle))).add continuous_id⟩

@[simp] theorem circleTranslation_apply (a : ℝ) (z : Circle) :
    circleTranslation a z = (a : Circle) + z := rfl

/-- Scale the translation parameter to zero, giving an actual homotopy to the identity. -/
def circleTranslationHomotopy (a : ℝ) :
    (circleTranslation a).Homotopy (ContinuousMap.id Circle) where
  toFun p := ((((1 - (p.1 : ℝ)) * a : ℝ) : Circle) + p.2)
  continuous_toFun := ((AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul continuous_const)).add
      continuous_snd
  map_zero_left z := by simp
  map_one_left z := by simp

/-- Exact real-lift formula for the translation homotopy. -/
@[simp] theorem circleTranslationHomotopy_apply (a : ℝ) (t : unitInterval) (z : Circle) :
    circleTranslationHomotopy a (t, z) =
      (((1 - (t : ℝ)) * a : ℝ) : Circle) + z := rfl

/-- Circle translations induce the identity on actual singular homology in every degree. -/
@[simp] theorem circleTranslation_singularHomologyMap (a : ℝ) (n : ℕ) :
    singularHomologyMap (circleTranslation a) n = LinearMap.id := by
  rw [homotopy_homologyMap (circleTranslationHomotopy a) n, singularHomologyMap_id]

/-- The same identity with the first-Hurewicz singular-homology API. -/
@[simp] theorem circleTranslation_inducedHomology (a : ℝ) :
    inducedHomology (circleTranslation a) = LinearMap.id :=
  circleTranslation_singularHomologyMap a 1

/-- Translating an arbitrary loop preserves its actual first singular-homology class,
even though translation changes its basepoint. -/
theorem loopHomologyClass_map_circleTranslation (a : ℝ) {x : Circle} (p : Path x x) :
    loopHomologyClass (p.map (circleTranslation a).continuous) = loopHomologyClass p := by
  rw [← inducedHomology_loopHomologyClass (circleTranslation a) x p,
    circleTranslation_inducedHomology]
  rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology.CirclePaths
