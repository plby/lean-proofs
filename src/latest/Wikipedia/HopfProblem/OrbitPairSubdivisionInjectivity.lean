import Wikipedia.HopfProblem.OrbitPairSubdivisionWeightRecovery
import Wikipedia.HopfProblem.OrbitPairRealizationNondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.Data.Set.Card

/-!
# Injectivity of the native barycentric subdivision map

The positive coordinate levels recover the number of faces, their ordered
thresholds, the faces themselves, and finally the simplex weights. Applied
to positive nondegenerate representatives of native realization points,
this proves injectivity of the actual continuous barycentric map.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz RealizationSimplex

variable {n k l : ℕ}
variable (A : Fin (k + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
variable (B : Fin (l + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))

theorem tailWeight_range_eq (hA : StrictMono A) (hB : StrictMono B)
    (t : Simplex k) (s : Simplex l) (ht : ∀ j, 0 < t j) (hs : ∀ j, 0 < s j)
    (h : chainCoordinate A t = chainCoordinate B s) :
    Set.range (tailWeight A t) = Set.range (tailWeight B s) := by
  rw [tailWeight_range A t hA ht, tailWeight_range B s hB hs, h]

theorem chain_dimension_eq (hA : StrictMono A) (hB : StrictMono B)
    (t : Simplex k) (s : Simplex l) (ht : ∀ j, 0 < t j) (hs : ∀ j, 0 < s j)
    (h : chainCoordinate A t = chainCoordinate B s) : k = l := by
  have hr := congrArg Set.ncard (tailWeight_range_eq A B hA hB t s ht hs h)
  rw [Set.ncard_range_of_injective (tailWeight_strictAnti A t ht).injective,
    Set.ncard_range_of_injective (tailWeight_strictAnti B s hs).injective] at hr
  simpa using hr

variable (C : Fin (k + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))

theorem tailWeight_eq (hA : StrictMono A) (hC : StrictMono C)
    (t s : Simplex k) (ht : ∀ j, 0 < t j) (hs : ∀ j, 0 < s j)
    (h : chainCoordinate A t = chainCoordinate C s) : tailWeight A t = tailWeight C s :=
  ((tailWeight_strictAnti A t ht).range_inj (tailWeight_strictAnti C s hs)).mp
    (tailWeight_range_eq A C hA hC t s ht hs h)

theorem chain_eq_of_coordinates (hA : StrictMono A) (hC : StrictMono C)
    (t s : Simplex k) (ht : ∀ j, 0 < t j) (hs : ∀ j, 0 < s j)
    (h : chainCoordinate A t = chainCoordinate C s) : A = C := by
  have hw := tailWeight_eq A C hA hC t s ht hs h
  funext j
  apply NonemptyFiniteChains.ext
  apply Finset.ext
  rintro ⟨i⟩
  rw [mem_face_iff_threshold A t hA.monotone ht j i,
    mem_face_iff_threshold C s hC.monotone hs j i, congrFun hw j, congrFun h i]

theorem barycentricMap_injective (n : ℕ) : Function.Injective (barycentricMap.{u} n) := by
  intro z w hzw
  let P := NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))
  let S := SimplexCategory.sd.{u}.obj ⦋n⦌
  obtain ⟨k, x, t, ht, rfl⟩ := exists_positive_nonDegenerate S z
  obtain ⟨l, y, s, hs, rfl⟩ := exists_positive_nonDegenerate S w
  have hx : StrictMono (fun i ↦ x.val.obj i) :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono (X := P) x.val).mp x.property
  have hy : StrictMono (fun i ↦ y.val.obj i) :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono (X := P) y.val).mp y.property
  have hcoord : chainCoordinate (fun j ↦ x.val.obj j) t =
      chainCoordinate (fun j ↦ y.val.obj j) s := by
    funext i
    exact (barycentricMap_characteristic_apply n k x.val t i).symm.trans
      ((congrArg (fun a : Simplex n ↦ a i) hzw).trans
        (barycentricMap_characteristic_apply n l y.val s i))
  have hkl := chain_dimension_eq (fun j ↦ x.val.obj j) (fun j ↦ y.val.obj j)
    hx hy t s ht hs hcoord
  change k = l at hkl
  subst l
  have hfaces := chain_eq_of_coordinates (fun j ↦ x.val.obj j) (fun j ↦ y.val.obj j)
    hx hy t s ht hs hcoord
  have hweights := tailWeight_eq (fun j ↦ x.val.obj j) (fun j ↦ y.val.obj j)
    hx hy t s ht hs hcoord
  have hxy : x.val = y.val := nerve.ext_of_isThin (C := P) hfaces
  have hts : t = s := by
    rw [← hfaces] at hweights
    exact simplex_eq_of_tailWeight_eq (fun j ↦ x.val.obj j) t s hweights
  exact congrArg₂ (fun (a : S _⦋k⦌) (b : Simplex k) ↦ characteristic S k a b) hxy hts

end Wikipedia.HopfProblem.OrbitPair.Subdivision
