import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturalitySequence
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturalityTransport

/-!
# Naturality of the actual singular Mayer–Vietoris connecting map

A continuous map carrying each member of an actual two-set open cover into
the corresponding member of another cover induces the usual connecting
square in every degree. All maps are the actual singular homology maps or
the connecting maps of the actual Mayer–Vietoris sequences. The small-chain
map, its short-sequence morphism, and both comparison isomorphisms are proved
constructions; none is supplied as an additional hypothesis.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
  (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')

/-- The actual small-chain homology map commutes with the actual ambient comparison. -/
theorem smallHomologyComparison_naturality (n : ℕ) :
    (smallHomologyComparison U' V' n).comp
        (homologyLinearMap (smallMapOfMapsTo f U V U' V' hfU hfV) n) =
      (singularHomologyMap f n).comp (smallHomologyComparison U V n) := by
  apply LinearMap.ext
  intro a
  exact smallHomologyComparison_naturality_of_comm f U V U' V'
    (smallMapOfMapsTo f U V U' V' hfU hfV)
    (smallMapOfMapsTo_inclusion f U V U' V' hfU hfV) n a

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
  (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ)

/-- The all-degree naturality square of the actual integral singular
Mayer–Vietoris connecting homomorphisms for a cover-preserving continuous map. -/
theorem connectingHomomorphism_naturality (n : ℕ) :
    (singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n).comp
        (connectingHomomorphism U V hU hV hcover n) =
      (connectingHomomorphism U' V' hU' hV' hcover' n).comp
        (singularHomologyMap f (n + 1)) :=
  connectingHomomorphism_naturality_of_sequenceMap f U V U' V'
    hU hV hcover hU' hV' hcover'
    (chainSequenceMapOfMapsTo f U V U' V' hfU hfV)
    (smallMapOfMapsTo_inclusion f U V U' V' hfU hfV) n

/-- Pointwise form of actual Mayer–Vietoris connecting naturality. -/
theorem connectingHomomorphism_naturality_apply (n : ℕ)
    (a : SingularHomology X (n + 1)) :
    singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n
        (connectingHomomorphism U V hU hV hcover n a) =
      connectingHomomorphism U' V' hU' hV' hcover' n
        (singularHomologyMap f (n + 1) a) :=
  LinearMap.congr_fun (connectingHomomorphism_naturality f U V U' V' hfU hfV
    hU hV hcover hU' hV' hcover' n) a

end Wikipedia.HopfProblem.SingularMayerVietoris
