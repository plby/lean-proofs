import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfRegularArf
import Wikipedia.HopfProblem.DegreeCollapseSixthStemTwoValues
import Wikipedia.NoExoticSixSphere.RegularFiberStableArfObstruction
import Wikipedia.NoExoticSixSphere.CubicalStableSixVanishing

/-!
# The actual polynomial Hopf square is nonzero in the stable sixth stem

The original regular-fiber Arf invariant obstructs every finite ordinary
suspension nullhomotopy of the actual smooth representative. Its original
homotopy to the polynomial smash square and the native direct-limit
vanishing criterion transfer nonvanishing to the specified stable class.
Combined with the proved whole-stem upper bound, this gives exactly two
classes. It does not yet exclude the nonzero class for the threefold.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfStableNonzero

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfProductDiffeomorph
open QuaternionicHopfFramedFiber QuaternionicHopfFiberQuadratic
open QuaternionicHopfFiberArf QuaternionicHopfRegularArf SphereMapSuspension

local instance : ChartedSpace (V 6) Fiber := fiberAtlas
local instance : IsManifold (𝓡 6) ∞ Fiber := fiber_isManifold
attribute [local instance] fiber_compact fiber_simplyConnected fiber_piTwo

theorem smoothMap_not_finitely_stably_nullhomotopic :
    ¬ ∃ j : ℕ, (iterate smoothMap j).Nullhomotopic := by
  let a := spherePole 16
  exact RegularSphereFiber.not_finitely_stably_nullhomotopic_of_geometricArf_ne_zero
    smoothMap smoothMap_contMDiff QuaternionicHopfProductFiber.point smoothMap_regular
    (by decide) (by decide) a basepoint (tubularRetraction a) (by
      rw [originalRegularFiberArf_one]
      exact one_ne_zero)

theorem squareMap_not_finitely_stably_nullhomotopic :
    ¬ ∃ j : ℕ, (iterate (SphereSmash.squareMap suspendedMap) j).Nullhomotopic := by
  rintro ⟨j, c, hc⟩
  exact smoothMap_not_finitely_stably_nullhomotopic
    ⟨j, c, (iterate_homotopic smoothMap_homotopic j).symm.trans hc⟩

theorem polynomial_square_stable_ne_one :
    CubicalStableSix.ofNative suspendedSmashClass ≠ 1 := by
  intro h
  have hmap := (CubicalStableSix.ofNative_sphereClass_eq_one_iff
    (SphereSmash.basedSquare suspendedMap)).mp h
  exact squareMap_not_finitely_stably_nullhomotopic
    ((StableSixSphereMaps.ofMap_eq_nullClass_iff _).mp hmap)

theorem suspendedSmashClass_ne_one : suspendedSmashClass ≠ 1 := by
  intro h
  apply polynomial_square_stable_ne_one
  rw [h, CubicalStableSix.ofNative_one]

theorem stableSquare_ne_one : StableThirdComposition.stableSquare ≠ 1 := by
  rw [← SixthStemTwoValues.polynomial_square_stable]
  exact polynomial_square_stable_ne_one

theorem twoValues_injective : Function.Injective SixthStemTwoValues.twoValues := by
  intro x y h
  cases x <;> cases y
  · rfl
  · exact (stableSquare_ne_one h.symm).elim
  · exact (stableSquare_ne_one h).elim
  · rfl

def twoValuesEquiv : Bool ≃ CubicalStableSix.Group :=
  Equiv.ofBijective SixthStemTwoValues.twoValues
    ⟨twoValues_injective, SixthStemTwoValues.twoValues_surjective⟩

theorem stable_card_eq_two : Nat.card CubicalStableSix.Group = 2 := by
  rw [← Nat.card_congr twoValuesEquiv]
  exact Nat.card_eq_fintype_card

theorem native_card_eq_two (k : ℕ) (hk : 6 ≤ k) :
    Nat.card (StableSixSphereMaps.NativeStage k) = 2 :=
  (Nat.card_congr (CubicalStableSix.stableMulEquiv k hk).toEquiv).trans stable_card_eq_two

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfStableNonzero
