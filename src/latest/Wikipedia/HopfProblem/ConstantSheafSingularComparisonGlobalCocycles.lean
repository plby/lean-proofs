import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalComplex
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalKernelSmall
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSmallCochainCocycles

/-!
# Actual global cocycle lifts and boundary detection

Global sheaf sections have genuine original cochain representatives. The
kernel of their native comparison is detected on small chains for an
actual open cover. The proved small-cochain homotopy equivalence then
lifts positive cocycles and detects their actual global primitives.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- Every positive global sheaf cocycle is the exact image of an original
closed singular cochain, not only of an abstract cohomology class. -/
theorem globalCochainComparison_cycle_lift [NormalSpace X] [ParacompactSpace X]
    (n : ℕ) (s : (globalSheafCochainComplex X A).X (n + 1))
    (hs : (globalSheafCochainComplex X A).d (n + 1) (n + 2) s = 0) :
    ∃ φ : Cochains X A (n + 1),
      (singularCochainComplex X A).d (n + 1) (n + 2) φ = 0 ∧
        globalCochainUnit X A (n + 1) φ = s := by
  obtain ⟨α, rfl⟩ := globalCochainUnit_surjective X A (n + 1) s
  have hδα : globalCochainUnit X A (n + 2)
      ((singularCochainComplex X A).d (n + 1) (n + 2) α) = 0 :=
    (globalCochainComparison_d_apply X A (n + 1) (n + 2) α).trans hs
  obtain ⟨U, hxU, hU⟩ := exists_cover_smallRestriction_eq_zero X A (n + 2) _ hδα
  let r := smallCochainRestriction A (fun x => (U x : Set X))
  have hcover : (⋃ x : X, (U x : Set X)) = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨x, hxU x⟩
  have hsmall : (smallCochainComplex (fun x => (U x : Set X)) A).d
      (n + 1) (n + 2) (r.f (n + 1) α) = 0 :=
    (congrArg (fun g => g α) (r.comm (n + 1) (n + 2))).trans hU
  obtain ⟨φ, hφ, hφr⟩ := smallCochain_cocycle_lift_exact A
    (fun x => (U x : Set X)) (fun x => (U x).isOpen) hcover n (r.f (n + 1) α) hsmall
  have hdiff : r.f (n + 1) (φ - α) = 0 := by rw [map_sub, hφr, sub_self]
  have hunit := globalCochainUnit_eq_zero_of_smallRestriction X A (n + 1) U
    (fun x => ⟨x, hxU x⟩) (φ - α) hdiff
  refine ⟨φ, hφ, ?_⟩
  exact sub_eq_zero.mp
    ((map_sub (globalCochainUnit X A (n + 1)).hom φ α).symm.trans hunit)

/-- If the actual image of an original closed cochain is a global sheaf
boundary, the original singular cochain has a genuine global primitive. -/
theorem globalCochainComparison_boundary_detect [NormalSpace X] [ParacompactSpace X]
    (n : ℕ) (φ : Cochains X A (n + 1))
    (hφ : (singularCochainComplex X A).d (n + 1) (n + 2) φ = 0)
    (s : (globalSheafCochainComplex X A).X n)
    (hs : (globalSheafCochainComplex X A).d n (n + 1) s =
      globalCochainUnit X A (n + 1) φ) :
    ∃ ψ : Cochains X A n, (singularCochainComplex X A).d n (n + 1) ψ = φ := by
  obtain ⟨β, rfl⟩ := globalCochainUnit_surjective X A n s
  have hδβ : globalCochainUnit X A (n + 1)
      ((singularCochainComplex X A).d n (n + 1) β) =
      globalCochainUnit X A (n + 1) φ :=
    (globalCochainComparison_d_apply X A n (n + 1) β).trans hs
  have hdiff : globalCochainUnit X A (n + 1)
      (φ - (singularCochainComplex X A).d n (n + 1) β) = 0 := by
    rw [map_sub, hδβ, sub_self]
  obtain ⟨U, hxU, hU⟩ := exists_cover_smallRestriction_eq_zero X A (n + 1) _ hdiff
  let r := smallCochainRestriction A (fun x => (U x : Set X))
  have hcover : (⋃ x : X, (U x : Set X)) = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨x, hxU x⟩
  have hr : r.f (n + 1) ((singularCochainComplex X A).d n (n + 1) β) =
      r.f (n + 1) φ :=
    (sub_eq_zero.mp ((map_sub (r.f (n + 1)).hom φ
      ((singularCochainComplex X A).d n (n + 1) β)).symm.trans hU)).symm
  have hb : (smallCochainComplex (fun x => (U x : Set X)) A).d n (n + 1)
      (r.f n β) = r.f (n + 1) φ :=
    (congrArg (fun g => g β) (r.comm n (n + 1))).trans hr
  exact smallCochain_boundary_of_restriction_boundary A
    (fun x => (U x : Set X)) (fun x => (U x).isOpen) hcover n φ hφ (r.f n β) hb

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
