import Wikipedia.HopfProblem.SingularMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturality

/-!
# Detection by the actual Mayer–Vietoris connecting homomorphism

If the two members of an open cover have zero homology in degree `n + 1`,
the actual connecting homomorphism detects ambient classes in that degree.
Naturality then detects classes under a cover-preserving continuous map
whose intersection map is injective in degree `n`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero

open SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Vanishing of the two local groups makes the actual connecting map injective. -/
theorem connecting_injective_of_local_homology_zero
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))] :
    Function.Injective (connectingHomomorphism U V hU hV hcover n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← exact_at_ambient U V hU hV hcover n]
  have hz : rightHomologyMap U V (n + 1) = 0 := by
    apply LinearMap.ext
    intro a
    rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
  rw [hz, LinearMap.range_zero]

/-- Actual connecting naturality detects a cover-preserving map on ambient homology. -/
theorem connecting_comp_homologyMap_injective
    (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ)
    (n : ℕ) [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))]
    (hIntersection : Function.Injective
      (singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n)) :
    Function.Injective
      ((connectingHomomorphism U' V' hU' hV' hcover' n).comp
        (singularHomologyMap f (n + 1))) := by
  rw [← connectingHomomorphism_naturality f U V U' V' hfU hfV
    hU hV hcover hU' hV' hcover' n]
  exact hIntersection.comp
    (connecting_injective_of_local_homology_zero U V hU hV hcover n)

/-- The ambient induced homology map is itself injective under the detection hypotheses. -/
theorem homologyMap_injective_of_intersection
    (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ)
    (n : ℕ) [Subsingleton (SingularHomology U (n + 1))]
    [Subsingleton (SingularHomology V (n + 1))]
    (hIntersection : Function.Injective
      (singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n)) :
    Function.Injective (singularHomologyMap f (n + 1)) := by
  intro a b hab
  apply connecting_comp_homologyMap_injective f U V U' V' hfU hfV
    hU hV hcover hU' hV' hcover' n hIntersection
  exact congrArg (connectingHomomorphism U' V' hU' hV' hcover' n) hab

end Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero
