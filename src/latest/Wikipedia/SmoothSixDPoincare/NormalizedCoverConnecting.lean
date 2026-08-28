import Wikipedia.SmoothSixDPoincare.CoverConnectingNaturality
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Naturality in the actual homotopy coordinates of two cover overlaps

Transport native connecting classes through genuine overlap homotopy
equivalences. The induced coordinate map is the literal composite of the
source parametrization, the restricted original map, and the target inverse
parametrization. No orientation or degree is assigned by this definition.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CoverNaturality

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {X Y S T : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace S] [TopologicalSpace T]
  (U V : Set X) (U' V' : Set Y) (f : C(X, Y))
  (hfU : MapsTo f U U') (hfV : MapsTo f V V')
  (eS : S ≃ₕ ↥(U ∩ V)) (eT : T ≃ₕ ↥(U' ∩ V'))

def overlapCoordinateMap : C(S, T) :=
  eT.invFun.comp ((mapOn f (U ∩ V) (U' ∩ V')
    (map_intersection U V U' V' f hfU hfV)).comp eS.toFun)

theorem normalized_connecting_naturality
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = univ)
    (k : ℕ) (a : SingularHomology X (k + 1)) :
    singularHomologyMap (overlapCoordinateMap U V U' V' f hfU hfV eS eT) k
      ((homotopyEquivHomologyEquiv eS k).symm (connectingHomomorphism U V hU hV hc k a)) =
        (homotopyEquivHomologyEquiv eT k).symm
          (connectingHomomorphism U' V' hU' hV' hc' k (singularHomologyMap f (k + 1) a)) := by
  have hS : singularHomologyMap eS.toFun k
      ((homotopyEquivHomologyEquiv eS k).symm (connectingHomomorphism U V hU hV hc k a)) =
        connectingHomomorphism U V hU hV hc k a :=
    (homotopyEquivHomologyEquiv eS k).apply_symm_apply _
  unfold overlapCoordinateMap
  rw [singularHomologyMap_comp, LinearMap.comp_apply,
    singularHomologyMap_comp, LinearMap.comp_apply, hS,
    connecting_naturality_apply U V U' V' f hfU hfV hU hV hc hU' hV' hc',
    homotopyEquivHomologyEquiv_symm_apply]
  rfl

end Wikipedia.SmoothSixDPoincare.CoverNaturality
