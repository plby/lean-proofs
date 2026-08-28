import Wikipedia.SmoothSixDPoincare.CoverOverlapHomology
import Wikipedia.SmoothSixDPoincare.CoverConnectingNaturality

/-!
# Naturality of the actual separated-overlap homology coordinates

Literal component inclusions are coordinate singles in the proved native
homology decomposition. A continuous map preserving the indexed open
neighborhoods therefore acts componentwise in those actual coordinates.
-/

noncomputable section

open Set Function ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CoverOverlapHomology

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

section Coordinates

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]
  (U : Set X) (V : ι → Set X)
  (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V))

theorem homologyEquiv_symm_single (k : ℕ) (i : ι)
    (a : SingularHomology (↥(U ∩ V i)) k) :
    (homologyEquiv U V hU hV hd k).symm (Pi.single i a) =
      singularHomologyMap (componentInclusion U V i) k a := by
  rw [homologyEquiv_symm_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

theorem homologyEquiv_inclusion (k : ℕ) (i : ι)
    (a : SingularHomology (↥(U ∩ V i)) k) :
    homologyEquiv U V hU hV hd k (singularHomologyMap (componentInclusion U V i) k a) =
      Pi.single i a := by
  apply (homologyEquiv U V hU hV hd k).symm.injective
  rw [LinearEquiv.symm_apply_apply, homologyEquiv_symm_single]

end Coordinates

section Maps

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {ι : Type}
  (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y)
  (f : C(X, Y)) (hfU : MapsTo f U U') (hfV : ∀ i, MapsTo f (V i) (V' i))

def componentMap (i : ι) : C(↥(U ∩ V i), ↥(U' ∩ V' i)) :=
  CoverNaturality.mapOn f _ _ (fun _ hx => ⟨hfU hx.1, hfV i hx.2⟩)

def overlapMap : C(↥(U ∩ ⋃ i, V i), ↥(U' ∩ ⋃ i, V' i)) :=
  CoverNaturality.mapOn f _ _ (by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx.2
    exact ⟨hfU hx.1, mem_iUnion.mpr ⟨i, hfV i hi⟩⟩)

theorem overlapMap_component (i : ι) :
    (overlapMap U V U' V' f hfU hfV).comp (componentInclusion U V i) =
      (componentInclusion U' V' i).comp (componentMap U V U' V' f hfU hfV i) := rfl

variable [Fintype ι]
  (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V))
  (hU' : IsOpen U') (hV' : ∀ i, IsOpen (V' i)) (hd' : Pairwise (Disjoint on V'))

/-- The actual homology coordinates commute with the actual restricted component maps. -/
theorem homologyEquiv_map (k : ℕ) (a : SingularHomology (↥(U ∩ ⋃ i, V i)) k) :
    homologyEquiv U' V' hU' hV' hd' k
      (singularHomologyMap (overlapMap U V U' V' f hfU hfV) k a) =
        fun i => singularHomologyMap (componentMap U V U' V' f hfU hfV i) k
          (homologyEquiv U V hU hV hd k a i) := by
  apply (homologyEquiv U' V' hU' hV' hd' k).symm.injective
  rw [LinearEquiv.symm_apply_apply, homologyEquiv_symm_apply,
    homology_map_out U V hU hV hd]
  apply Finset.sum_congr rfl
  intro i _
  rw [overlapMap_component, singularHomologyMap_comp, LinearMap.comp_apply]

end Maps

end Wikipedia.SmoothSixDPoincare.CoverOverlapHomology
