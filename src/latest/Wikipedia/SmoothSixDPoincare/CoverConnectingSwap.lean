import Wikipedia.SmoothSixDPoincare.SmallChainCoverSwap
import Wikipedia.SmoothSixDPoincare.CoverConnectingNaturality
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The actual connecting homomorphism changes sign under cover interchange

Transport the signed short-exact-sequence morphism through the original
small-chain inclusions. A continuous map reversing the two cover members
therefore contributes precisely one minus sign to naturality.
-/

noncomputable section

open Set CategoryTheory

namespace Wikipedia.SmoothSixDPoincare.CoverNaturality

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem connecting_swap (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hc : U ∪ V = univ) (hc' : V ∪ U = univ) (n : ℕ)
    (a : SingularHomology X (n + 1)) :
    connectingHomomorphism V U hV hU hc' n a =
      -singularHomologyMap (intersectionSwap U V) n
        (connectingHomomorphism U V hU hV hc n a) := by
  obtain ⟨b, hb⟩ := (smallHomologyEquiv U V hU hV hc (n + 1)).surjective a
  have hb' : smallHomologyComparison U V (n + 1) b = a := hb
  rw [← hb', connectingHomomorphism_comparison]
  rw [← comparison_swap U V (n + 1) b, connectingHomomorphism_comparison]
  exact smallConnecting_swap U V n b

def reversingIntersectionMap (U V : Set X) (U' V' : Set Y) (f : C(X, Y))
    (hU : MapsTo f U V') (hV : MapsTo f V U') : C(↥(U ∩ V), ↥(U' ∩ V')) :=
  mapOn f _ _ (fun _ hx => ⟨hV hx.2, hU hx.1⟩)

/-- Signed naturality for a continuous map interchanging the actual cover members. -/
theorem connecting_reversing_naturality (U V : Set X) (U' V' : Set Y) (f : C(X, Y))
    (hfU : MapsTo f U V') (hfV : MapsTo f V U')
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = univ)
    (n : ℕ) (a : SingularHomology X (n + 1)) :
    connectingHomomorphism U' V' hU' hV' hc' n (singularHomologyMap f (n + 1) a) =
      -singularHomologyMap (reversingIntersectionMap U V U' V' f hfU hfV) n
        (connectingHomomorphism U V hU hV hc n a) := by
  have hswap : V' ∪ U' = univ := (union_comm V' U').trans hc'
  rw [connecting_swap V' U' hV' hU' hswap hc']
  rw [← connecting_naturality_apply U V V' U' f hfU hfV hU hV hc hV' hU' hswap]
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

end Wikipedia.SmoothSixDPoincare.CoverNaturality
