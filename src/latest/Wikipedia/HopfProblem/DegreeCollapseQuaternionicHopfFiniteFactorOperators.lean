import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFactorFrameComparison
import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteFramedCoordinates
import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteChartContraction

/-!
# Removing the actual inverse chart from both original Hopf factor operators

Factor the explicit lifted normal and quaternionic tangent columns through
the proved invertible radial/chart operator. The remaining finite operator
is injective because its actual lift is injective. Contracting the chart
coordinate changes yields exact parity comparisons with fixed ambient
coordinates. The original source twist is retained throughout.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteFactorOperators

open NoExoticSixSphere QuaternionicHopf GLOrthonormalization Stiefel SpanningDiskFrameCoordinates
open QuaternionicHopfProductDiffeomorph QuaternionicHopfFramedFiber QuaternionicHopfFiberFactors
open QuaternionicHopfFactorFrameComparison QuaternionicHopfFiniteProductFrame
open SphereFiniteRadialCoordinates SphereFiniteChartContraction

local instance : ChartedSpace (V 6) Fiber := fiberAtlas
local instance : IsManifold (𝓡 6) ∞ Fiber := fiber_isManifold

variable (f : Sphere 3 → Fiber) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)

def coordinatePoint (s : Sphere 3) : V 16 := squarePoint (parameter f s)

include hf in
theorem contMDiff_coordinatePoint : ContMDiff (𝓡 3) 𝓘(ℝ, V 16) ∞ (coordinatePoint f) :=
  contMDiff_squarePoint.comp (contMDiff_parameter f hf)

theorem ambient_coordinatePoint (s : Sphere 3) :
    SphereFiniteAmbientPoint.ambientPoint 16 (coordinatePoint f s) = embedding.toFun (f s) := by
  rw [coordinatePoint, QuaternionicHopfProductLift.ambientPoint_squarePoint, parameter,
    ambient_parameter]

def finiteRightInverse (s : Sphere 3) : V 10 →L[ℝ] V 16 :=
  squareRightInverse (parameter f s)

include hf in
theorem contMDiff_finiteRightInverse :
    ContMDiff (𝓡 3) 𝓘(ℝ, V 10 →L[ℝ] V 16) ∞ (finiteRightInverse f) :=
  contMDiff_squareRightInverse.comp (contMDiff_parameter f hf)

def finiteTangent (s : Sphere 3) : V 3 →L[ℝ] V 16 :=
  SphereThreeTangentFrame.framedDerivative (coordinatePoint f) s

include hf in
theorem contMDiff_finiteTangent :
    ContMDiff (𝓡 3) 𝓘(ℝ, V 3 →L[ℝ] V 16) ∞ (finiteTangent f) :=
  SphereFiniteFramedCoordinates.contMDiff_framedDerivative
    (coordinatePoint f) (contMDiff_coordinatePoint f hf)

include hf in
theorem tangent_factorization (s : Sphere 3) :
    SphereFrameRawComparison.tangent embedding f s =
      (fderiv ℝ (SphereFiniteAmbientPoint.ambientPoint 16) (coordinatePoint f s)).comp
        (finiteTangent f s) := by
  have he : SphereFiniteAmbientPoint.ambientPoint 16 ∘ coordinatePoint f =
      embedding.toFun ∘ f := funext (ambient_coordinatePoint f)
  have h := SphereFiniteFramedCoordinates.framedDerivative_ambientPoint
    (coordinatePoint f) (contMDiff_coordinatePoint f hf) s
  exact (congrArg (fun g : Sphere 3 → V 17 ↦ SphereThreeTangentFrame.framedDerivative g s)
    he).symm.trans h

def finiteOperator (s : Sphere 3) : V 14 →L[ℝ] V 17 :=
  SphereFiniteFramedCoordinates.finiteOperator (finiteRightInverse f s) (finiteTangent f s)

variable (a : Sphere 16) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

theorem operator_factorization (s : Sphere 3) :
    (frameOperator (coordinatePoint f s)).comp (finiteOperator f s) =
      (liftedMap a f hf hd s).val := by
  change (frameOperator (coordinatePoint f s)).comp
    (SphereFiniteFramedCoordinates.finiteOperator (finiteRightInverse f s) (finiteTangent f s)) = _
  rw [SphereFiniteFramedCoordinates.coordinate_finiteOperator, liftedMap_value]
  have hN : (SphereFiniteEquationLift.lift (coordinatePoint f s) (finiteRightInverse f s)).comp
      (EuclideanTailCoordinates.split 10).toContinuousLinearMap =
        (QuaternionicHopfProductLift.fullRightInverse (parameter f s)).comp
          normalCoordinates.toContinuousLinearMap := rfl
  exact congrArg₂ (fun (A : V 11 →L[ℝ] V 17) (B : V 3 →L[ℝ] V 17) ↦
    OperatorSum.operator A B) hN (tangent_factorization f hf s).symm

include hf a hd in
theorem finiteOperator_injective (s : Sphere 3) : Injective (finiteOperator f s) := by
  intro v w h
  apply (liftedMap a f hf hd s).property
  have he := congrArg (frameOperator (coordinatePoint f s)) h
  change ((frameOperator (coordinatePoint f s)).comp (finiteOperator f s)) v =
    ((frameOperator (coordinatePoint f s)).comp (finiteOperator f s)) w at he
  rw [operator_factorization f hf a hd s] at he
  exact he

def finiteMap : C(Sphere 3, Monomorphism.Space 17 14) where
  toFun s := ⟨finiteOperator f s, finiteOperator_injective f hf a hd s⟩
  continuous_toFun := (SphereFiniteFramedCoordinates.continuous_finiteOperator
    (finiteRightInverse f) (finiteTangent f) (contMDiff_finiteRightInverse f hf).continuous
    (contMDiff_finiteTangent f hf).continuous).subtype_mk _

def coordinateMap : C(Sphere 3, V 16) :=
  ⟨coordinatePoint f, (contMDiff_coordinatePoint f hf).continuous⟩

theorem liftedMap_eq_transport : liftedMap a f hf hd =
    transport (coordinateMap f hf) (finiteMap f hf a hd) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  exact (operator_factorization f hf a hd s).symm

theorem liftedMap_homotopic_fixed : (liftedMap a f hf hd).Homotopic
    ((fixedCoordinates (0 : V 16)).comp (finiteMap f hf a hd)) := by
  rw [liftedMap_eq_transport]
  exact homotopic_fixed (coordinateMap f hf) (finiteMap f hf a hd)

theorem parity_eq_fixed : embedding.immersedSphereFrameParity (framing a) f hf hd =
    Monomorphism.sphereParityOfDimension 18 (by decide) (by decide)
      (twistedBlockMap ((fixedCoordinates (0 : V 16)).comp (finiteMap f hf a hd))) :=
  (parity_eq_lifted a f hf hd).trans
    (Monomorphism.sphereParityOfDimension_homotopic _ _ _
      (twistedBlockMap_homotopic (liftedMap_homotopic_fixed f hf a hd)))

theorem leftParity_eq_fixed (r : Sphere 3) : leftParity a r =
    Monomorphism.sphereParityOfDimension 18 (by decide) (by decide)
      (twistedBlockMap ((fixedCoordinates (0 : V 16)).comp
        (finiteMap (left r) (contMDiff_left r) a (left_mfderiv_injective r)))) :=
  parity_eq_fixed (left r) (contMDiff_left r) a (left_mfderiv_injective r)

theorem rightParity_eq_fixed (q : Sphere 3) : rightParity a q =
    Monomorphism.sphereParityOfDimension 18 (by decide) (by decide)
      (twistedBlockMap ((fixedCoordinates (0 : V 16)).comp
        (finiteMap (right q) (contMDiff_right q) a (right_mfderiv_injective q)))) :=
  parity_eq_fixed (right q) (contMDiff_right q) a (right_mfderiv_injective q)

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteFactorOperators
