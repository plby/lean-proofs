import Wikipedia.HopfProblem.CuspNormalizationGermsSeparatorsCoordinates
import Wikipedia.HopfProblem.CuspNormalizationGermsFractionsSeparators

/-!
# Actual coordinate cofactors separating the analytic branches

For a selected coordinate branch, multiply the actual ambient coordinate
germs belonging to all the other selected branches. The resulting germ
restricts nontrivially to that branch and vanishes on every other branch.
Its actual image under simultaneous branch restriction supplies the
separating elements required for the fraction-ring construction.
-/

noncomputable section

open Set Filter Topology
open scoped BigOperators

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

/-- A product of actual ambient coordinate germs, omitting the coordinate
of the distinguished branch. -/
def ambientCofactor (s : Finset (Fin 3)) (i : Fin 3) : AmbientGerm :=
  ∏ j ∈ s.erase i, coordinateGerm j

@[simp] theorem toBranch_ambientCofactor (s : Finset (Fin 3)) (i k : Fin 3) :
    toBranch k (ambientCofactor s i) = ∏ j ∈ s.erase i, toBranch k (coordinateGerm j) :=
  map_prod (toBranch k) _ _

/-- Every factor on the distinguished branch is a genuine nonzero
analytic coordinate germ; the actual branch germ ring is a domain. -/
theorem toBranch_ambientCofactor_self_ne_zero (s : Finset (Fin 3)) (i : Fin 3) :
    toBranch i (ambientCofactor s i) ≠ 0 := by
  rw [toBranch_ambientCofactor]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact toBranch_coordinateGerm_ne_zero (Finset.mem_erase.mp hj).1

/-- On any other selected branch, its own coordinate occurs as a zero
factor of the actual cofactor product. -/
theorem toBranch_ambientCofactor_other (s : Finset (Fin 3)) (i j : Fin 3)
    (hj : j ∈ s) (hji : j ≠ i) : toBranch j (ambientCofactor s i) = 0 := by
  rw [toBranch_ambientCofactor]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, hj⟩)
    (toBranch_coordinateGerm_self j)

/-- The separator belongs to the actual simultaneous restriction image,
with the actual cofactor as its ambient preimage. -/
def separator (s : Finset (Fin 3)) (i : s) : BranchImage s :=
  (toBranches s).rangeRestrict (ambientCofactor s i)

@[simp] theorem separator_apply (s : Finset (Fin 3)) (i j : s) :
    (separator s i : s → BranchGerm) j = toBranch j (ambientCofactor s i) := rfl

theorem separator_diagonal_ne_zero (s : Finset (Fin 3)) (i : s) :
    (separator s i : s → BranchGerm) i ≠ 0 :=
  toBranch_ambientCofactor_self_ne_zero s i

theorem separator_off_diagonal (s : Finset (Fin 3)) (i j : s) (hji : j ≠ i) :
    (separator s i : s → BranchGerm) j = 0 :=
  toBranch_ambientCofactor_other s i j j.property (fun h => hji (Subtype.ext h))

/-- The separating family has now been constructed for the actual image
of analytic branch restriction, with every hypothesis discharged. -/
def separatingFamily (s : Finset (Fin 3)) :
    GermsFractions.SeparatingFamily (BranchImage s) where
  element := separator s
  diagonal_ne_zero := separator_diagonal_ne_zero s
  off_diagonal := separator_off_diagonal s

/-- Actual extension by a coordinate projection makes the actual branch
restriction image surject onto each individual analytic branch germ ring. -/
theorem branchImage_coordinate_surjective (s : Finset (Fin 3)) (i : s) :
    Function.Surjective (fun a : BranchImage s => (a : s → BranchGerm) i) :=
  GermsFinite.range_coordinate_surjective (toBranches s)
    (toBranches_coordinate_surjective s) i

end Wikipedia.HopfProblem.CuspNormalization.Germs
