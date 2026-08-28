import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSmallCochainPrimitives

/-!
# Exact lifting of small cocycles

Combining the actual homotopy comparison with degreewise extension removes
the small coboundary correction.  Thus every positive-degree small cocycle
is the exact restriction of a global cocycle, not merely cohomologous to it.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {ι : Type*}
variable (A : AddCommGrpCat.{0}) (U : ι → Set X)
  (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ)

include hU hcover

/-- Every positive-degree small cocycle extends to an actual global cocycle. -/
theorem smallCochain_cocycle_lift_exact (n : ℕ) (φ : SmallCochains U A (n + 1))
    (hφ : (smallCochainComplex U A).d (n + 1) (n + 2) φ = 0) :
    ∃ ψ : Cochains X A (n + 1),
      (singularCochainComplex X A).d (n + 1) (n + 2) ψ = 0 ∧
      (smallCochainRestriction A U).f (n + 1) ψ = φ := by
  obtain ⟨ψ, hψ, χ, hχ⟩ := smallCochain_cocycle_lift A U hU hcover n φ hφ
  let η := smallCochainExtend A U n χ
  refine ⟨ψ - (singularCochainComplex X A).d n (n + 1) η, ?_, ?_⟩
  · rw [map_sub, hψ]
    have hz := congrArg
      (fun f : (singularCochainComplex X A).X n ⟶
        (singularCochainComplex X A).X (n + 2) => f η)
      ((singularCochainComplex X A).d_comp_d n (n + 1) (n + 2))
    change (singularCochainComplex X A).d (n + 1) (n + 2)
      ((singularCochainComplex X A).d n (n + 1) η) = 0 at hz
    rw [hz, sub_self]
  · rw [map_sub, ← SmallCochainComparison.map_d (smallCochainRestriction A U) n (n + 1) η,
      smallCochainRestriction_extend A U n χ, hχ, add_sub_cancel_left]

/-- A global positive-degree cocycle is a coboundary exactly when its actual
small restriction is one. -/
theorem smallCochain_restriction_boundary_iff (n : ℕ) (φ : Cochains X A (n + 1))
    (hφ : (singularCochainComplex X A).d (n + 1) (n + 2) φ = 0) :
    (∃ χ : SmallCochains U A n, (smallCochainComplex U A).d n (n + 1) χ =
      (smallCochainRestriction A U).f (n + 1) φ) ↔
    ∃ ψ : Cochains X A n, (singularCochainComplex X A).d n (n + 1) ψ = φ := by
  constructor
  · rintro ⟨χ, hχ⟩
    exact smallCochain_boundary_of_restriction_boundary A U hU hcover n φ hφ χ hχ
  · rintro ⟨ψ, hψ⟩
    refine ⟨(smallCochainRestriction A U).f n ψ, ?_⟩
    rw [SmallCochainComparison.map_d, hψ]

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
