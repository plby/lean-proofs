import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturality
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Detecting vanishing through the actual Mayer--Vietoris connecting map

For a map preserving two actual open covers, injectivity of the target
connecting map detects vanishing one degree above a vanishing map on the
intersection.  The argument uses the proved naturality of the genuine
singular Mayer--Vietoris sequence.

The pullback-cover variants use the original subspace topologies and
the literal restriction of the given continuous map, with no separate
cover-preservation hypotheses.
-/

noncomputable section

open Set
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

section Factor

variable {Z : Type} [TopologicalSpace Z]

/-- A composite of actual homology maps is zero if its intermediate
homology group is trivial. -/
theorem homologyLinearMap_comp_eq_zero_of_subsingleton
    (g : C(X, Z)) (h : C(Z, Y)) (n : ℕ) [Subsingleton (SingularHomology Z n)] :
    (singularHomologyMap h n).comp (singularHomologyMap g n) = 0 := by
  apply LinearMap.ext
  intro a
  change singularHomologyMap h n (singularHomologyMap g n a) = 0
  rw [Subsingleton.elim (singularHomologyMap g n a) 0, map_zero]

/-- The homology map of the literal continuous composite is zero. -/
theorem singularHomologyMap_comp_eq_zero_of_subsingleton
    (g : C(X, Z)) (h : C(Z, Y)) (n : ℕ) [Subsingleton (SingularHomology Z n)] :
    singularHomologyMap (h.comp g) n = 0 := by
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact homologyLinearMap_comp_eq_zero_of_subsingleton g h n

/-- A proved factorization through a space with trivial degree-`n`
homology makes the given actual homology map zero. -/
theorem singularHomologyMap_eq_zero_of_factor
    (f : C(X, Y)) (g : C(X, Z)) (h : C(Z, Y))
    (hfac : f = h.comp g) (n : ℕ) [Subsingleton (SingularHomology Z n)] :
    singularHomologyMap f n = 0 := by
  rw [hfac]
  exact singularHomologyMap_comp_eq_zero_of_subsingleton g h n

/-- It suffices that the actual factorization holds up to homotopy. -/
theorem singularHomologyMap_eq_zero_of_homotopic_factor
    (f : C(X, Y)) (g : C(X, Z)) (h : C(Z, Y))
    (hfac : f.Homotopic (h.comp g)) (n : ℕ) [Subsingleton (SingularHomology Z n)] :
    singularHomologyMap f n = 0 := by
  rw [PeriodTorusHigherHomology.homotopic_homologyMap hfac n]
  exact singularHomologyMap_comp_eq_zero_of_subsingleton g h n

end Factor

/-- Actual connecting-map naturality detects a vanishing homology map
whenever the target connecting map is injective. -/
theorem singularHomologyMap_eq_zero_of_connecting
    (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : MapsTo f U U') (hfV : MapsTo f V V')
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = univ)
    (n : ℕ)
    (hinj : Function.Injective (connectingHomomorphism U' V' hU' hV' hcover' n))
    (hzero : singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n = 0) :
    singularHomologyMap f (n + 1) = 0 := by
  apply LinearMap.ext
  intro a
  apply hinj
  simpa only [hzero, LinearMap.zero_apply, map_zero] using
    (connectingHomomorphism_naturality_apply f U V U' V' hfU hfV
      hU hV hcover hU' hV' hcover' n a).symm

/-- The canonical continuous restriction from the intersection of the
two pullback sets to the target intersection. -/
def pullbackIntersectionMap (f : C(X, Y)) (U' V' : Set Y) :
    C(((f ⁻¹' U') ∩ (f ⁻¹' V') : Set X), (U' ∩ V' : Set Y)) :=
  intersectionRestriction f (f ⁻¹' U') (f ⁻¹' V') U' V'
    (fun _ hx => hx) (fun _ hx => hx)

@[simp] theorem pullbackIntersectionMap_coe (f : C(X, Y)) (U' V' : Set Y)
    (x : ((f ⁻¹' U') ∩ (f ⁻¹' V') : Set X)) :
    (pullbackIntersectionMap f U' V' x : Y) = f x := rfl

/-- The literal preimages of a two-set cover cover the original source. -/
theorem pullback_cover (f : C(X, Y)) (U' V' : Set Y)
    (hcover' : U' ∪ V' = univ) :
    (f ⁻¹' U') ∪ (f ⁻¹' V') = univ := by
  rw [← preimage_union, hcover', preimage_univ]

/-- Continuity gives the actual open pullback cover, in the original topology. -/
theorem pullback_open_cover (f : C(X, Y)) (U' V' : Set Y)
    (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = univ) :
    IsOpen (f ⁻¹' U') ∧ IsOpen (f ⁻¹' V') ∧
      (f ⁻¹' U') ∪ (f ⁻¹' V') = univ :=
  ⟨hU'.preimage f.continuous, hV'.preimage f.continuous,
    pullback_cover f U' V' hcover'⟩

/-- The same vanishing criterion on the canonical pullback cover,
without separate `MapsTo` inputs. -/
theorem singularHomologyMap_eq_zero_of_pullback_connecting
    (f : C(X, Y)) (U' V' : Set Y)
    (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = univ)
    (n : ℕ)
    (hinj : Function.Injective (connectingHomomorphism U' V' hU' hV' hcover' n))
    (hzero : singularHomologyMap (pullbackIntersectionMap f U' V') n = 0) :
    singularHomologyMap f (n + 1) = 0 :=
  singularHomologyMap_eq_zero_of_connecting f (f ⁻¹' U') (f ⁻¹' V') U' V'
    (fun _ hx => hx) (fun _ hx => hx)
    (hU'.preimage f.continuous) (hV'.preimage f.continuous)
    (pullback_cover f U' V' hcover') hU' hV' hcover' n hinj hzero

/-- A literal factorization of the canonical intersection restriction
through trivial degree-`n` homology gives vanishing in degree `n + 1`. -/
theorem singularHomologyMap_eq_zero_of_pullback_factor
    {Z : Type} [TopologicalSpace Z]
    (f : C(X, Y)) (U' V' : Set Y)
    (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = univ)
    (n : ℕ) [Subsingleton (SingularHomology Z n)]
    (hinj : Function.Injective (connectingHomomorphism U' V' hU' hV' hcover' n))
    (g : C(((f ⁻¹' U') ∩ (f ⁻¹' V') : Set X), Z))
    (h : C(Z, (U' ∩ V' : Set Y)))
    (hfac : pullbackIntersectionMap f U' V' = h.comp g) :
    singularHomologyMap f (n + 1) = 0 :=
  singularHomologyMap_eq_zero_of_pullback_connecting f U' V' hU' hV' hcover' n hinj
    (singularHomologyMap_eq_zero_of_factor (pullbackIntersectionMap f U' V') g h hfac n)

/-- The canonical intersection restriction may instead factor up to
homotopy through a space with trivial degree-`n` homology. -/
theorem singularHomologyMap_eq_zero_of_pullback_homotopic_factor
    {Z : Type} [TopologicalSpace Z]
    (f : C(X, Y)) (U' V' : Set Y)
    (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = univ)
    (n : ℕ) [Subsingleton (SingularHomology Z n)]
    (hinj : Function.Injective (connectingHomomorphism U' V' hU' hV' hcover' n))
    (g : C(((f ⁻¹' U') ∩ (f ⁻¹' V') : Set X), Z))
    (h : C(Z, (U' ∩ V' : Set Y)))
    (hfac : (pullbackIntersectionMap f U' V').Homotopic (h.comp g)) :
    singularHomologyMap f (n + 1) = 0 :=
  singularHomologyMap_eq_zero_of_pullback_connecting f U' V' hU' hV' hcover' n hinj
    (singularHomologyMap_eq_zero_of_homotopic_factor
      (pullbackIntersectionMap f U' V') g h hfac n)

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
