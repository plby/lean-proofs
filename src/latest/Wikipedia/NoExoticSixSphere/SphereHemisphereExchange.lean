import Wikipedia.NoExoticSixSphere.SphereEquatorialFlattening
import Wikipedia.NoExoticSixSphere.OpenCoverFrameExchange

/-!
# Actual homology and frame exchange across closed hemispheres

The four maps need only agree on the indicated closed hemispheres. The
constructed equatorial flattening makes these agreements hold on an open
cover without changing any induced homology map. Small-chain exchange then
proves the relation, with no extra collar or assumed cycle identity.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere
namespace HemisphereExchange

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {Y : Type} [TopologicalSpace Y]

theorem homologyMap_comp_flattening (f : C(Sphere 3, Y)) (n : ℕ) :
    singularHomologyMap (f.comp SphereEquatorialFlattening.map) n = singularHomologyMap f n := by
  have h := homotopy_homologyMap SphereEquatorialFlattening.homotopy n
  rw [singularHomologyMap_id] at h
  rw [singularHomologyMap_comp, ← h, LinearMap.comp_id]

theorem homologyMap_exchange (f₀₀ f₀₁ f₁₀ f₁₁ : C(Sphere 3, Y))
    (hN₀ : ∀ x : Sphere 3, 0 ≤ x.val 0 → f₀₀ x = f₀₁ x)
    (hN₁ : ∀ x : Sphere 3, 0 ≤ x.val 0 → f₁₀ x = f₁₁ x)
    (hS₀ : ∀ x : Sphere 3, x.val 0 ≤ 0 → f₀₀ x = f₁₀ x)
    (hS₁ : ∀ x : Sphere 3, x.val 0 ≤ 0 → f₀₁ x = f₁₁ x) (n : ℕ) :
    singularHomologyMap f₀₀ n + singularHomologyMap f₁₁ n =
      singularHomologyMap f₀₁ n + singularHomologyMap f₁₀ n := by
  have h := OpenCoverExchange.homologyMap_exchange
    (f₀₀.comp SphereEquatorialFlattening.map) (f₀₁.comp SphereEquatorialFlattening.map)
    (f₁₀.comp SphereEquatorialFlattening.map) (f₁₁.comp SphereEquatorialFlattening.map)
    SphereEquatorialFlattening.northOpen SphereEquatorialFlattening.southOpen
    (fun _ hx ↦ hN₀ _ (SphereEquatorialFlattening.map_head_nonneg hx))
    (fun _ hx ↦ hN₁ _ (SphereEquatorialFlattening.map_head_nonneg hx))
    (fun _ hx ↦ hS₀ _ (SphereEquatorialFlattening.map_head_nonpos hx))
    (fun _ hx ↦ hS₁ _ (SphereEquatorialFlattening.map_head_nonpos hx))
    SphereEquatorialFlattening.isOpen_north SphereEquatorialFlattening.isOpen_south
    SphereEquatorialFlattening.open_cover n
  simpa only [homologyMap_comp_flattening] using h

end HemisphereExchange

namespace Stiefel

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

theorem sphereThirdObstruction_hemisphere_exchange (r : ℕ)
    (f₀₀ f₀₁ f₁₀ f₁₁ : C(Sphere 3, Space (3 + (r + 2)) (r + 2)))
    (hN₀ : ∀ x : Sphere 3, 0 ≤ x.val 0 → f₀₀ x = f₀₁ x)
    (hN₁ : ∀ x : Sphere 3, 0 ≤ x.val 0 → f₁₀ x = f₁₁ x)
    (hS₀ : ∀ x : Sphere 3, x.val 0 ≤ 0 → f₀₀ x = f₁₀ x)
    (hS₁ : ∀ x : Sphere 3, x.val 0 ≤ 0 → f₀₁ x = f₁₁ x) :
    sphereThirdObstruction r f₀₀ + sphereThirdObstruction r f₁₁ =
      sphereThirdObstruction r f₀₁ + sphereThirdObstruction r f₁₀ := by
  have h := LinearMap.congr_fun
    (HemisphereExchange.homologyMap_exchange f₀₀ f₀₁ f₁₀ f₁₁ hN₀ hN₁ hS₀ hS₁ 3)
    sphereThirdClass
  have he := congrArg (stableThirdHomologyEquivZModTwo r) h
  simpa only [LinearMap.add_apply, map_add, ← sphereThirdObstruction_eq_homology] using he

namespace Monomorphism

theorem sphereParityOfDimension_hemisphere_exchange {N n : ℕ}
    (r : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)
    (f₀₀ f₀₁ f₁₀ f₁₁ : C(Sphere 3, Space N n))
    (hN₀ : ∀ x : Sphere 3, 0 ≤ x.val 0 → f₀₀ x = f₀₁ x)
    (hN₁ : ∀ x : Sphere 3, 0 ≤ x.val 0 → f₁₀ x = f₁₁ x)
    (hS₀ : ∀ x : Sphere 3, x.val 0 ≤ 0 → f₀₀ x = f₁₀ x)
    (hS₁ : ∀ x : Sphere 3, x.val 0 ≤ 0 → f₀₁ x = f₁₁ x) :
    sphereParityOfDimension r hN hn f₀₀ + sphereParityOfDimension r hN hn f₁₁ =
      sphereParityOfDimension r hN hn f₀₁ + sphereParityOfDimension r hN hn f₁₀ := by
  let T : C(Space N n, Stiefel.Space (3 + (r + 2)) (r + 2)) :=
    (Stiefel.dimensionHomeomorph hN hn :
      C(Stiefel.Space N n, Stiefel.Space (3 + (r + 2)) (r + 2))).comp (normalize N n)
  exact sphereThirdObstruction_hemisphere_exchange r (T.comp f₀₀) (T.comp f₀₁)
    (T.comp f₁₀) (T.comp f₁₁)
    (fun x hx ↦ congrArg T (hN₀ x hx)) (fun x hx ↦ congrArg T (hN₁ x hx))
    (fun x hx ↦ congrArg T (hS₀ x hx)) (fun x hx ↦ congrArg T (hS₁ x hx))

end Monomorphism
end Stiefel
end NoExoticSixSphere
