import Wikipedia.SmoothSixDPoincare.SmallChainCoverNaturality

/-!
# Naturality of the actual open-cover connecting homomorphism

The chain-level cover morphism commutes with the literal small-chain
inclusions. Transport through the proved open-cover homology equivalences
therefore gives naturality on the ambient singular homology objects.
-/

noncomputable section

open Set CategoryTheory

namespace Wikipedia.SmoothSixDPoincare.CoverNaturality

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (U V : Set X) (U' V' : Set Y) (f : C(X, Y))
  (hfU : MapsTo f U U') (hfV : MapsTo f V V')
  (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)
  (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = univ)

/-- The genuine Mayer–Vietoris connecting map is natural for a continuous cover map. -/
theorem connecting_naturality (n : ℕ) :
    (singularHomologyMap
      (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hfU hfV)) n).comp
        (connectingHomomorphism U V hU hV hc n) =
      (connectingHomomorphism U' V' hU' hV' hc' n).comp
        (singularHomologyMap f (n + 1)) := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, hb⟩ := (smallHomologyEquiv U V hU hV hc (n + 1)).surjective a
  have hb' : smallHomologyComparison U V (n + 1) b = a := hb
  rw [← hb']
  change singularHomologyMap _ n
      (connectingHomomorphism U V hU hV hc n (smallHomologyComparison U V (n + 1) b)) =
    connectingHomomorphism U' V' hU' hV' hc' n
      (singularHomologyMap f (n + 1) (smallHomologyComparison U V (n + 1) b))
  rw [connectingHomomorphism_comparison]
  have hcomp := LinearMap.congr_fun
    (comparison_naturality U V U' V' f hfU hfV (n + 1)) b
  change smallHomologyComparison U' V' (n + 1)
      (homologyLinearMap (smallMap U V U' V' f hfU hfV) (n + 1) b) =
    singularHomologyMap f (n + 1) (smallHomologyComparison U V (n + 1) b) at hcomp
  rw [← hcomp, connectingHomomorphism_comparison]
  exact LinearMap.congr_fun (smallConnecting_naturality U V U' V' f hfU hfV n) b

theorem connecting_naturality_apply (n : ℕ) (a : SingularHomology X (n + 1)) :
    singularHomologyMap
      (mapOn f (U ∩ V) (U' ∩ V') (map_intersection U V U' V' f hfU hfV)) n
        (connectingHomomorphism U V hU hV hc n a) =
      connectingHomomorphism U' V' hU' hV' hc' n (singularHomologyMap f (n + 1) a) :=
  LinearMap.congr_fun (connecting_naturality U V U' V' f hfU hfV hU hV hc hU' hV' hc' n) a

end Wikipedia.SmoothSixDPoincare.CoverNaturality
