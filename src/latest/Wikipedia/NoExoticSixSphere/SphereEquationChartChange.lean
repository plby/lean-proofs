import Wikipedia.NoExoticSixSphere.CenteredChartDifferentialChange
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Wikipedia.NoExoticSixSphere.SphereEquationDifferentialChange
import Wikipedia.NoExoticSixSphere.RegularSphereFiberEmbedding
import Wikipedia.NoExoticSixSphere.OrthogonalRightInverseCoordinates

/-!
# Exact target-chart comparison for the actual sphere-fiber normal operator

Form the original radial equations using either genuine target chart.
Their derivatives differ by one fixed equivalence on the full equation
space. Uniqueness of the orthogonal right inverse gives the exact normal
operator comparison, without any isometry or orientation assumption.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFiberNormalFrame

open GLOrthonormalization CenteredChartCoordinates

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
  (c c' : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞)
  (hb : b ∈ c.source) (hb' : b ∈ c'.source)

local instance : Fact (Module.finrank ℝ (Vector (m + 1)) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def equationsWithTargetChart (a : Sphere m) : Vector (m + 1) → WithLp 2 (ℝ × Vector n) :=
  SphereLevelEquations.equations a (coordinates f c b)

theorem equationsWithTargetChart_default (a : Sphere m) :
    equationsWithTargetChart f b (modelChartPartialDiffeomorph (I := 𝓡 n) b) a =
      equations f b a := rfl

include hf hb in
theorem contDiffAt_equationsWithTargetChart (a x : Sphere m) (hx : f x = b) :
    ContDiffAt ℝ ∞ (equationsWithTargetChart f b c a) x.val :=
  SphereLevelEquations.contDiffAt_equations a
    (contMDiffAt_coordinates f c b (hf x) (hx.symm ▸ hb))

include hf hb in
theorem surjective_fderiv_equationsWithTargetChart (a x : Sphere m) (hx : f x = b)
    (hreg : Surjective (mfderiv (𝓡 m) (𝓡 n) f x)) :
    Surjective (fderiv ℝ (equationsWithTargetChart f b c a) x.val) :=
  SphereLevelEquations.surjective_fderiv_equations a
    (contMDiffAt_coordinates f c b (hf x) (hx.symm ▸ hb))
    (surjective_mfderiv_coordinates f c b (hf x) (hx.symm ▸ hb) hreg)

include hf in
theorem fderiv_equations_targetChart (a x : Sphere m) (hx : f x = b) :
    fderiv ℝ (equationsWithTargetChart f b c' a) x.val =
      (SphereLevelEquations.equationChange (differentialChange c c' b hb hb')
        ).toContinuousLinearMap.comp (fderiv ℝ (equationsWithTargetChart f b c a) x.val) :=
  SphereLevelEquations.fderiv_equations_change a (coordinates f c b) (coordinates f c' b) x
    (contMDiffAt_coordinates f c b (hf x) (hx.symm ▸ hb))
    (contMDiffAt_coordinates f c' b (hf x) (hx.symm ▸ hb'))
    (differentialChange c c' b hb hb') (mfderiv_coordinates_change f c c' b hb hb' (hf x) hx)

include hf in
theorem normalOperator_targetChart (a x : Sphere m) (hx : f x = b)
    (hreg : Surjective (mfderiv (𝓡 m) (𝓡 n) f x)) :
    orthogonalRightInverse (fderiv ℝ (equationsWithTargetChart f b c' a) x.val) =
      (orthogonalRightInverse (fderiv ℝ (equationsWithTargetChart f b c a) x.val)).comp
        (SphereLevelEquations.equationChange (differentialChange c c' b hb hb')
          ).symm.toContinuousLinearMap := by
  rw [fderiv_equations_targetChart f hf b c c' hb hb' a x hx]
  exact orthogonalRightInverse_target_coordinates _
    (surjective_fderiv_equationsWithTargetChart f hf b c hb a x hx hreg) _

end NoExoticSixSphere.SphereFiberNormalFrame
