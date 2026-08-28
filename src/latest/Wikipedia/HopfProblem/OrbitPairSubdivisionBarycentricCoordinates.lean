import Wikipedia.HopfProblem.OrbitPairSubdivisionGeometry
import Wikipedia.HopfProblem.OrbitPairSimplexPositiveSupport

/-!
# Explicit barycentric coordinates of subdivided simplex points

A chain vertex contributes the reciprocal of its cardinality on its
support and zero elsewhere. These formulas concern the actual barycentric
map on mathlib's realized subdivided standard simplex.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder
open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz RealizationSimplex AffineCoordinates

theorem chainBarycentre_apply (n : ℕ)
    (A : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) (i : Fin (n + 1)) :
    chainBarycentre n A i =
      if ULift.up i ∈ A.finset then (A.finset.card : ℝ)⁻¹ else 0 := by
  classical
  let : Nonempty A.finset := A.nonempty.to_subtype
  let f : A.finset → Fin (n + 1) := fun a ↦ a.val.down
  change stdSimplex.map f stdSimplex.barycenter i = _
  by_cases hi : ULift.up i ∈ A.finset
  · rw [if_pos hi]
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact ULift.ext _ _ hab
    have h := SimplexSupport.map_coordinate_injective f hf
      (stdSimplex.barycenter : stdSimplex ℝ A.finset) ⟨ULift.up i, hi⟩
    change stdSimplex.map f stdSimplex.barycenter i = (Fintype.card A.finset : ℝ)⁻¹ at h
    simpa only [Fintype.card_coe] using h
  · rw [if_neg hi]
    apply le_antisymm
    · apply le_of_not_gt
      intro hpos
      obtain ⟨a, ha, _⟩ := (SimplexSupport.map_pos_iff f stdSimplex.barycenter i).mp hpos
      have he : a.val = ULift.up i := ULift.ext _ _ ha
      exact hi (he ▸ a.property)
    · exact stdSimplex.zero_le _ _

def chainWeight {n k : ℕ}
    (A : Fin (k + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (t : Simplex k) (j : Fin (k + 1)) : ℝ :=
  t j / (A j).finset.card

theorem chainWeight_nonneg {n k : ℕ}
    (A : Fin (k + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (t : Simplex k) (j : Fin (k + 1)) : 0 ≤ chainWeight A t j :=
  div_nonneg (stdSimplex.zero_le t j) (Nat.cast_nonneg _)

theorem chainWeight_pos {n k : ℕ}
    (A : Fin (k + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (t : Simplex k) (ht : ∀ j, 0 < t j) (j : Fin (k + 1)) :
    0 < chainWeight A t j :=
  div_pos (ht j) (Nat.cast_pos.mpr (A j).nonempty.card_pos)

def chainCoordinate {n k : ℕ}
    (A : Fin (k + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (t : Simplex k) (i : Fin (n + 1)) : ℝ :=
  ∑ j, if ULift.up i ∈ (A j).finset then chainWeight A t j else 0

theorem weighted_chainBarycentre_apply {n k : ℕ}
    (A : Fin (k + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (t : Simplex k) (i : Fin (n + 1)) :
    weighted (fun j ↦ chainBarycentre n (A j)) t i = chainCoordinate A t i := by
  classical
  change (∑ j, t j * chainBarycentre n (A j) i) = _
  unfold chainCoordinate
  apply Finset.sum_congr rfl
  intro j hj
  rw [chainBarycentre_apply]
  split_ifs <;> simp [chainWeight, div_eq_mul_inv]

theorem barycentricMap_characteristic_apply (n k : ℕ)
    (x : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋k⦌) (t : Simplex k) (i : Fin (n + 1)) :
    barycentricMap n (characteristic (SimplexCategory.sd.obj ⦋n⦌) k x t) i =
      chainCoordinate (fun j ↦ x.obj j) t i := by
  classical
  have h := nerveInterpolation_characteristic
    (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) (chainBarycentre n) k x t
  have hi := congrArg (fun s : Simplex n ↦ s i) h
  exact hi.trans (weighted_chainBarycentre_apply (fun j ↦ x.obj j) t i)

end Wikipedia.HopfProblem.OrbitPair.Subdivision
