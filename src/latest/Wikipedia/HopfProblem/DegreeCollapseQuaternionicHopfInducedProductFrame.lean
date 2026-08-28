import Wikipedia.HopfProblem.DegreeCollapseSphereFiberEquationGerm
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfProductDiffeomorph

/-!
# The actual Hopf-square induced frame on the original smooth product

The ambient inclusion is the literal map into R17. The centered target
equations and radial sphere equation supply a full smooth normal frame.
Its values agree exactly with the original regular-fiber frame under the
proved product diffeomorphism, and with the unsmoothed map's equation
right inverse. This does not yet identify the quaternionic product frame.
-/

noncomputable section

open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfInducedProductFrame

open NoExoticSixSphere QuaternionicHopf
open QuaternionicHopfProductImmersion QuaternionicHopfProductDiffeomorph

abbrev Normal := WithLp 2 (ℝ × V 10)

def ambientInclusion : Sphere 3 × Sphere 3 → V 17 :=
  fun p ↦ (fiberInclusion p).val

theorem contMDiff_ambientInclusion :
    ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, V 17) ∞ ambientInclusion := by
  let : Fact (Module.finrank ℝ (V 17) = 16 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact (contMDiff_coe_sphere (n := 16) (m := ∞)).comp contMDiff_fiberInclusion

theorem ambientDifferential_injective (p : Sphere 3 × Sphere 3) :
    Function.Injective (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) ambientInclusion p) := by
  let : Fact (Module.finrank ℝ (V 17) = 16 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hc := (contMDiff_coe_sphere (n := 16) (m := ∞)).mdifferentiable (by simp)
    (fiberInclusion p)
  change Function.Injective (mfderiv ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, V 17)
    ((Subtype.val : Sphere 16 → V 17) ∘ fiberInclusion) p)
  rw [mfderiv_comp p hc (contMDiff_fiberInclusion.mdifferentiable (by simp) p)]
  have hi : Function.Injective
      (mfderiv (𝓡 16) 𝓘(ℝ, V 17) (Subtype.val : Sphere 16 → V 17) (fiberInclusion p)) := by
    convert! injective_mvfderiv_subtypeVal_sphere (n := 16) (fiberInclusion p)
  exact hi.comp (fiberInclusion_mfderiv_injective p)

def equations (a : Sphere 16) : V 17 → Normal :=
  SphereFiberNormalFrame.equations smoothMap QuaternionicHopfProductFiber.point a

theorem equations_zero (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    equations a (ambientInclusion p) = 0 :=
  SphereFiberNormalFrame.equations_zero smoothMap QuaternionicHopfProductFiber.point a
    (fiberInclusion p) (smoothMap_fiberInclusion p)

theorem contDiffAt_equations (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    ContDiffAt ℝ ∞ (equations a) (ambientInclusion p) :=
  SphereFiberNormalFrame.contDiffAt_equations smoothMap smoothMap_contMDiff
    QuaternionicHopfProductFiber.point a (fiberInclusion p) (smoothMap_fiberInclusion p)

theorem equations_fderiv_surjective (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    Function.Surjective (fderiv ℝ (equations a) (ambientInclusion p)) :=
  SphereFiberNormalFrame.surjective_fderiv_equations smoothMap smoothMap_contMDiff
    QuaternionicHopfProductFiber.point a (fiberInclusion p) (smoothMap_fiberInclusion p)
    (smoothMap_regular (fiberInclusion p) (smoothMap_fiberInclusion p))

theorem dimension_eq :
    Module.finrank ℝ (V 17) = Module.finrank ℝ Normal + Module.finrank ℝ (V 3 × V 3) := by
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V 10)).toLinearEquiv.finrank_eq
  change Module.finrank ℝ (V 17) =
    Module.finrank ℝ (WithLp 2 (ℝ × V 10)) + Module.finrank ℝ (V 3 × V 3)
  rw [h]
  simp [Module.finrank_prod]

theorem tangent_range_eq_kernel (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) ambientInclusion p).range =
      (fderiv ℝ (equations a) (ambientInclusion p)).ker :=
  NormalFrameOfEquations.range_ambientDifferential_eq_kernel contMDiff_ambientInclusion
    (contDiffAt_equations a) (equations_zero a) (equations_fderiv_surjective a)
    ambientDifferential_injective dimension_eq p

def normalFrame (a : Sphere 16) :
    SmoothRangeFrame ((𝓡 3).prod (𝓡 3))
      (fun p ↦ (NormalFrameOfEquations.ambientDifferential
        ((𝓡 3).prod (𝓡 3)) ambientInclusion p).rangeᗮ.starProjection) Normal :=
  NormalFrameOfEquations.inducedFrame contMDiff_ambientInclusion
    (contDiffAt_equations a) (equations_zero a) (equations_fderiv_surjective a)
    ambientDifferential_injective dimension_eq

theorem normalFrame_ambient (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    (normalFrame a).ambient p =
      orthogonalRightInverse (fderiv ℝ (equations a) (ambientInclusion p)) := rfl

theorem normalFrame_rightInverse (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    (fderiv ℝ (equations a) (ambientInclusion p)).comp ((normalFrame a).ambient p) =
      ContinuousLinearMap.id ℝ Normal := by
  rw [normalFrame_ambient]
  exact comp_orthogonalRightInverse _ (equations_fderiv_surjective a p)

theorem normalFrame_range (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    ((normalFrame a).ambient p).range =
      (NormalFrameOfEquations.ambientDifferential
        ((𝓡 3).prod (𝓡 3)) ambientInclusion p).rangeᗮ := by
  rw [normalFrame_ambient, range_orthogonalRightInverse _ (equations_fderiv_surjective a p),
    tangent_range_eq_kernel a p]

theorem normalFrame_original_equations (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    (normalFrame a).ambient p = orthogonalRightInverse
      (fderiv ℝ (SphereFiberNormalFrame.equations (SphereSmash.squareMap suspendedMap)
        QuaternionicHopfProductFiber.point a) (ambientInclusion p)) :=
  (normalFrame_ambient a p).trans
    (SphereFiberEquationGerm.equations_rightInverse_eq smoothMap
      (SphereSmash.squareMap suspendedMap) QuaternionicHopfProductFiber.point a
      (fiberInclusion p)
      (smoothMap_eventuallyEq_square (fiberInclusion p) (smoothMap_fiberInclusion p)))

theorem normalFrame_fiberDiffeomorph (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    letI := fiberAtlas;
    (normalFrame a).ambient p =
      (SphereFiberNormalFrame.normalFrame smoothMap smoothMap_contMDiff
        QuaternionicHopfProductFiber.point smoothMap_regular 6 (by decide) a).ambient
          (fiberDiffeomorph p) := by
  let := fiberAtlas
  rw [SphereFiberNormalFrame.normalFrame_ambient, normalFrame_ambient]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfInducedProductFrame

