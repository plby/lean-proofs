import Wikipedia.NoExoticSixSphere.OpenCoverHomologyExchange
import Wikipedia.NoExoticSixSphere.PartialFrameSphereHomology
import Wikipedia.NoExoticSixSphere.InjectiveOperatorDimensionParity

/-!
# Frame-obstruction cut-and-paste from actual open-cover agreement

The four original maps satisfy explicit equalities on the open pieces.
The proved singular-chain exchange identity gives their homology relation,
and the actual frame obstruction evaluates that relation modulo two.
This does not assert that particular geometric frame maps meet the hypotheses.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.Stiefel

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

theorem sphereThirdObstruction_exchange (r : ℕ)
    (f₀₀ f₀₁ f₁₀ f₁₁ : C(Sphere 3, Space (3 + (r + 2)) (r + 2)))
    (U V : Set (Sphere 3)) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hU₀ : EqOn f₀₀ f₀₁ U) (hU₁ : EqOn f₁₀ f₁₁ U)
    (hV₀ : EqOn f₀₀ f₁₀ V) (hV₁ : EqOn f₀₁ f₁₁ V) :
    sphereThirdObstruction r f₀₀ + sphereThirdObstruction r f₁₁ =
      sphereThirdObstruction r f₀₁ + sphereThirdObstruction r f₁₀ := by
  have h := LinearMap.congr_fun
    (OpenCoverExchange.homologyMap_exchange f₀₀ f₀₁ f₁₀ f₁₁ U V
      hU₀ hU₁ hV₀ hV₁ hU hV hcover 3) sphereThirdClass
  have he := congrArg (stableThirdHomologyEquivZModTwo r) h
  simpa only [LinearMap.add_apply, map_add, ← sphereThirdObstruction_eq_homology] using he

namespace Monomorphism

variable {N n : ℕ} (r : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)

theorem sphereParityOfDimension_exchange (f₀₀ f₀₁ f₁₀ f₁₁ : C(Sphere 3, Space N n))
    (U V : Set (Sphere 3)) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hU₀ : EqOn f₀₀ f₀₁ U) (hU₁ : EqOn f₁₀ f₁₁ U)
    (hV₀ : EqOn f₀₀ f₁₀ V) (hV₁ : EqOn f₀₁ f₁₁ V) :
    sphereParityOfDimension r hN hn f₀₀ + sphereParityOfDimension r hN hn f₁₁ =
      sphereParityOfDimension r hN hn f₀₁ + sphereParityOfDimension r hN hn f₁₀ := by
  let T : C(Space N n, Stiefel.Space (3 + (r + 2)) (r + 2)) :=
    (Stiefel.dimensionHomeomorph hN hn :
      C(Stiefel.Space N n, Stiefel.Space (3 + (r + 2)) (r + 2))).comp (normalize N n)
  exact sphereThirdObstruction_exchange r (T.comp f₀₀) (T.comp f₀₁)
    (T.comp f₁₀) (T.comp f₁₁) U V hU hV hcover
    (fun _ hx ↦ congrArg T (hU₀ hx)) (fun _ hx ↦ congrArg T (hU₁ hx))
    (fun _ hx ↦ congrArg T (hV₀ hx)) (fun _ hx ↦ congrArg T (hV₁ hx))

end Monomorphism
end NoExoticSixSphere.Stiefel
