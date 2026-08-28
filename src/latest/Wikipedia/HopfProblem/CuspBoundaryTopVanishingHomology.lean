import Wikipedia.HopfProblem.CuspCentralHomologyTopDegrees
import Wikipedia.HopfProblem.CuspBoundaryTopVanishingHomologyNaturality

/-!
# Detecting top homology in the actual central cusp fibre

The radial outer collar and inner region are the already constructed
open subsets of the literal central quotient.  Their actual degree-four
singular homology vanishes, so the actual Mayer--Vietoris connecting map
detects degree four of that quotient.  At the half-radius threshold this
is precisely the connecting map used by the existing top-coordinate
isomorphism.

No cellular replacement or unspecified degree-four detector is used.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open ToricSpace CuspRetraction CuspCentralHomology SingularMayerVietoris

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The actual degree-four connecting map for the genuine radial open cover. -/
def centralH4Connecting (a : ℝ) (ha1 : a < 1) :
    SingularHomology (QuotientCentralFibre C ε) 4 →ₗ[ℤ]
      SingularHomology (overlapRegion C ε hε a) 3 :=
  connectingHomomorphism (outerRegion C ε hε a) (innerRegion C ε hε)
    (outerRegion_isOpen C ε hε hε1 hC hR a)
    (innerRegion_isOpen C ε hε hε1 hC hR)
    (outerRegion_union_innerRegion C ε hε a ha1) 3

/-- The actual connecting map is injective because both actual pieces
have zero fourth homology, not merely because the target has rank one. -/
theorem centralH4Connecting_injective (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Function.Injective (centralH4Connecting C ε hε hε1 hC hR a ha1) := by
  let : Subsingleton (SingularHomology (outerRegion C ε hε a) 4) :=
    outerRegion_homology_subsingleton C ε hε hε1 hC hR a ha ha1 1
  let : Subsingleton (SingularHomology (innerRegion C ε hε) 4) :=
    innerRegion_homology_subsingleton C ε hε hε1 hC hR 1
  exact coverConnecting_injective_of_vanishing
    (outerRegion C ε hε a) (innerRegion C ε hε)
    (outerRegion_isOpen C ε hε hε1 hC hR a)
    (innerRegion_isOpen C ε hε hε1 hC hR)
    (outerRegion_union_innerRegion C ε hε a ha1) 3

/-- Vanishing under this exact connecting map detects zero in actual
fourth singular homology of the central fibre. -/
theorem centralH4Connecting_eq_zero_iff (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (z : SingularHomology (QuotientCentralFibre C ε) 4) :
    centralH4Connecting C ε hε hε1 hC hR a ha1 z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply centralH4Connecting_injective C ε hε hε1 hC hR a ha ha1
    simpa only [map_zero] using hz
  · intro hz
    rw [hz, map_zero]

variable {X : Type} [TopologicalSpace X]

/-- The literal restriction of an actual map to the intersection of
the preimages of the two radial open sets. -/
def centralPullbackIntersectionMap (a : ℝ) (f : C(X, QuotientCentralFibre C ε)) :
    C(((f ⁻¹' outerRegion C ε hε a) ∩ (f ⁻¹' innerRegion C ε hε) : Set X),
      overlapRegion C ε hε a) :=
  pullbackIntersectionMap f (outerRegion C ε hε a) (innerRegion C ε hε)

@[simp] theorem centralPullbackIntersectionMap_coe (a : ℝ)
    (f : C(X, QuotientCentralFibre C ε))
    (x : ((f ⁻¹' outerRegion C ε hε a) ∩ (f ⁻¹' innerRegion C ε hε) : Set X)) :
    (centralPullbackIntersectionMap C ε hε a f x : QuotientCentralFibre C ε) = f x := rfl

include hε1 hC hR

/-- Vanishing on the actual overlap in degree three forces the whole
actual map to induce zero in degree four.  The source cover is its
literal pullback, so no extra cover-preservation data are assumed. -/
theorem central_homologyFourMap_eq_zero_of_intersection
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (f : C(X, QuotientCentralFibre C ε))
    (hzero : singularHomologyMap (centralPullbackIntersectionMap C ε hε a f) 3 = 0) :
    singularHomologyMap f 4 = 0 :=
  singularHomologyMap_eq_zero_of_pullback_connecting f
    (outerRegion C ε hε a) (innerRegion C ε hε)
    (outerRegion_isOpen C ε hε hε1 hC hR a)
    (innerRegion_isOpen C ε hε hε1 hC hR)
    (outerRegion_union_innerRegion C ε hε a ha1) 3
    (centralH4Connecting_injective C ε hε hε1 hC hR a ha ha1) hzero

/-- The same conclusion applies to any actual source open cover
carried into the radial cover, using its actual intersection restriction. -/
theorem central_homologyFourMap_eq_zero_of_cover
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (f : C(X, QuotientCentralFibre C ε))
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hfU : Set.MapsTo f U (outerRegion C ε hε a))
    (hfV : Set.MapsTo f V (innerRegion C ε hε))
    (hzero : singularHomologyMap
      (intersectionRestriction f U V (outerRegion C ε hε a) (innerRegion C ε hε) hfU hfV)
      3 = 0) :
    singularHomologyMap f 4 = 0 :=
  singularHomologyMap_eq_zero_of_connecting f U V
    (outerRegion C ε hε a) (innerRegion C ε hε) hfU hfV hU hV hcover
    (outerRegion_isOpen C ε hε hε1 hC hR a)
    (innerRegion_isOpen C ε hε hε1 hC hR)
    (outerRegion_union_innerRegion C ε hε a ha1) 3
    (centralH4Connecting_injective C ε hε hε1 hC hR a ha ha1) hzero

/-- Any genuine factorization of the overlap restriction through a
space with zero third homology gives zero on the fourth homology of the
actual central quotient. -/
theorem central_homologyFourMap_eq_zero_of_factor
    {Y : Type} [TopologicalSpace Y] [Subsingleton (SingularHomology Y 3)]
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (f : C(X, QuotientCentralFibre C ε))
    (g : C(((f ⁻¹' outerRegion C ε hε a) ∩ (f ⁻¹' innerRegion C ε hε) : Set X), Y))
    (k : C(Y, overlapRegion C ε hε a))
    (hfactor : centralPullbackIntersectionMap C ε hε a f = k.comp g) :
    singularHomologyMap f 4 = 0 := by
  apply central_homologyFourMap_eq_zero_of_intersection C ε hε hε1 hC hR a ha ha1 f
  exact singularHomologyMap_eq_zero_of_factor
    (centralPullbackIntersectionMap C ε hε a f) g k hfactor 3

/-- A proved homotopy to such a factorization suffices; the factor
space may be any actual topological space with vanishing third homology. -/
theorem central_homologyFourMap_eq_zero_of_homotopic_factor
    {Y : Type} [TopologicalSpace Y] [Subsingleton (SingularHomology Y 3)]
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (f : C(X, QuotientCentralFibre C ε))
    (g : C(((f ⁻¹' outerRegion C ε hε a) ∩ (f ⁻¹' innerRegion C ε hε) : Set X), Y))
    (k : C(Y, overlapRegion C ε hε a))
    (hfactor : (centralPullbackIntersectionMap C ε hε a f).Homotopic (k.comp g)) :
    singularHomologyMap f 4 = 0 := by
  apply central_homologyFourMap_eq_zero_of_intersection C ε hε hε1 hC hR a ha ha1 f
  exact singularHomologyMap_eq_zero_of_homotopic_factor
    (centralPullbackIntersectionMap C ε hε a f) g k hfactor 3

/-- In particular, factoring through the literal compact phase
two-torus uses its already proved vanishing third singular homology. -/
theorem central_homologyFourMap_eq_zero_of_phase_factor
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (f : C(X, QuotientCentralFibre C ε))
    (g : C(((f ⁻¹' outerRegion C ε hε a) ∩ (f ⁻¹' innerRegion C ε hε) : Set X),
      CompactFibreTorus))
    (k : C(CompactFibreTorus, overlapRegion C ε hε a))
    (hfactor : centralPullbackIntersectionMap C ε hε a f = k.comp g) :
    singularHomologyMap f 4 = 0 := by
  let : Subsingleton (SingularHomology CompactFibreTorus 3) :=
    compactFibreTorus_homology_subsingleton 0
  exact central_homologyFourMap_eq_zero_of_factor C ε hε hε1 hC hR
    a ha ha1 f g k hfactor

/-- The unchanged phase coordinate and an actual contraction of the
remaining overlap coordinate therefore give fourth-degree vanishing. -/
theorem central_homologyFourMap_eq_zero_of_phase_homotopic_factor
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (f : C(X, QuotientCentralFibre C ε))
    (g : C(((f ⁻¹' outerRegion C ε hε a) ∩ (f ⁻¹' innerRegion C ε hε) : Set X),
      CompactFibreTorus))
    (k : C(CompactFibreTorus, overlapRegion C ε hε a))
    (hfactor : (centralPullbackIntersectionMap C ε hε a f).Homotopic (k.comp g)) :
    singularHomologyMap f 4 = 0 := by
  let : Subsingleton (SingularHomology CompactFibreTorus 3) :=
    compactFibreTorus_homology_subsingleton 0
  exact central_homologyFourMap_eq_zero_of_homotopic_factor C ε hε hε1 hC hR
    a ha ha1 f g k hfactor

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
