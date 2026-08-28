import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariantsTriangle

/-!
# The actual deck-coinvariant comparison is injective

The computed triangular maps have first diagonal entry one and second
diagonal entry equal to a positive covering norm index.  They are therefore
injective.  The top-degree map is positive multiplication by the covering
order.  Consequently, in every positive degree through four, the kernel
of the original covering map is exactly the actual inverse deck difference
image.  No rational comparison or injectivity hypothesis is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology

theorem periodCoverCoinvariantH1Map_injective (j : Kind) (p : FixedPeriod j) :
    Function.Injective (periodCoverCoinvariantH1Map j p) :=
  triangularFinTwo_injective _ _ (periodCoverCoinvariantH1Map_firstAxis j p 1)
    (periodCoverCoinvariantH1Map_second j p) (by exact_mod_cast j.order_pos.ne')

theorem periodCoverCoinvariantH2Map_injective (j : Kind) (p : FixedPeriod j) :
    Function.Injective (periodCoverCoinvariantH2Map j p) :=
  triangularFinTwo_injective _ _ (periodCoverCoinvariantH2Map_firstAxis j p 1)
    (periodCoverCoinvariantH2Map_second j p) (by exact_mod_cast (fibreNormIndex_pos j).ne')

theorem periodCoverCoinvariantH3Map_injective (j : Kind) (p : FixedPeriod j) :
    Function.Injective (periodCoverCoinvariantH3Map j p) :=
  triangularFinTwo_injective _ _ (periodCoverCoinvariantH3Map_firstAxis j p 1)
    (periodCoverCoinvariantH3Map_second j p) (by exact_mod_cast (fibreNormIndex_pos j).ne')

/-- Injectivity of the genuine induced degree-one covering map. -/
theorem periodCoverFromDeckCoinvariants_h1_injective (j : Kind) (p : FixedPeriod j) :
    Function.Injective (periodCoverFromDeckCoinvariants j p 1) := by
  intro a b h
  apply (periodDeckCoinvariantsH1Equiv j p).injective
  apply periodCoverCoinvariantH1Map_injective j p
  change surfaceH1Equiv j p (periodCoverFromDeckCoinvariants j p 1
    ((periodDeckCoinvariantsH1Equiv j p).symm (periodDeckCoinvariantsH1Equiv j p a))) =
    surfaceH1Equiv j p (periodCoverFromDeckCoinvariants j p 1
      ((periodDeckCoinvariantsH1Equiv j p).symm (periodDeckCoinvariantsH1Equiv j p b)))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, h]

/-- Injectivity holds integrally for the actual degree-two map. -/
theorem periodCoverFromDeckCoinvariants_h2_injective (j : Kind) (p : FixedPeriod j) :
    Function.Injective (periodCoverFromDeckCoinvariants j p 2) := by
  intro a b h
  apply (periodDeckCoinvariantsH2Equiv j p).injective
  apply periodCoverCoinvariantH2Map_injective j p
  change surfaceH2Equiv j p (periodCoverFromDeckCoinvariants j p 2
    ((periodDeckCoinvariantsH2Equiv j p).symm (periodDeckCoinvariantsH2Equiv j p a))) =
    surfaceH2Equiv j p (periodCoverFromDeckCoinvariants j p 2
      ((periodDeckCoinvariantsH2Equiv j p).symm (periodDeckCoinvariantsH2Equiv j p b)))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, h]

/-- The actual degree-three coinvariant comparison is also injective. -/
theorem periodCoverFromDeckCoinvariants_h3_injective (j : Kind) (p : FixedPeriod j) :
    Function.Injective (periodCoverFromDeckCoinvariants j p 3) := by
  intro a b h
  apply (periodDeckCoinvariantsH3Equiv j p).injective
  apply periodCoverCoinvariantH3Map_injective j p
  change surfaceH3Equiv j p (periodCoverFromDeckCoinvariants j p 3
    ((periodDeckCoinvariantsH3Equiv j p).symm (periodDeckCoinvariantsH3Equiv j p a))) =
    surfaceH3Equiv j p (periodCoverFromDeckCoinvariants j p 3
      ((periodDeckCoinvariantsH3Equiv j p).symm (periodDeckCoinvariantsH3Equiv j p b)))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, h]

/-- The established positive orientation markings give the positive sheet count in top degree. -/
theorem periodCoverFromDeckCoinvariants_h4_coordinate (j : Kind) (p : FixedPeriod j)
    (a : PeriodDeckCoinvariants j p 4) :
    surfaceH4Equiv j p (periodCoverFromDeckCoinvariants j p 4 a) =
      (j.order : ℤ) * periodDeckCoinvariantsH4Equiv j p a := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (periodDeckDifference j p 4)) a
  rw [periodCoverFromDeckCoinvariants_mk, periodDeckCoinvariantsH4Equiv_mk]
  change surfacePeriodCoverH4Coordinates j p b =
    (j.order : ℤ) * torusH3Coordinates (surfacePeriodCoverCircleBoundary j p 3 b)
  exact surfacePeriodCoverH4Coordinates_apply j p b

def periodCoverCoinvariantH4Map (j : Kind) (p : FixedPeriod j) : ℤ →ₗ[ℤ] ℤ :=
  (surfaceH4Equiv j p).toLinearMap.comp
    ((periodCoverFromDeckCoinvariants j p 4).comp
      (periodDeckCoinvariantsH4Equiv j p).symm.toLinearMap)

@[simp] theorem periodCoverCoinvariantH4Map_apply (j : Kind) (p : FixedPeriod j) (t : ℤ) :
    periodCoverCoinvariantH4Map j p t = (j.order : ℤ) * t := by
  change surfaceH4Equiv j p (periodCoverFromDeckCoinvariants j p 4
    ((periodDeckCoinvariantsH4Equiv j p).symm t)) = _
  rw [periodCoverFromDeckCoinvariants_h4_coordinate, LinearEquiv.apply_symm_apply]

theorem periodCoverFromDeckCoinvariants_h4_injective (j : Kind) (p : FixedPeriod j) :
    Function.Injective (periodCoverFromDeckCoinvariants j p 4) := by
  intro a b h
  apply (periodDeckCoinvariantsH4Equiv j p).injective
  apply mul_left_cancel₀ (show (j.order : ℤ) ≠ 0 by exact_mod_cast j.order_pos.ne')
  rw [← periodCoverFromDeckCoinvariants_h4_coordinate,
    ← periodCoverFromDeckCoinvariants_h4_coordinate, h]

private theorem periodCover_ker_eq_deckDifference_range_of_injective
    (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (h : Function.Injective (periodCoverFromDeckCoinvariants j p n)) :
    LinearMap.ker (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) n) =
      LinearMap.range (periodDeckDifference j p n) := by
  apply le_antisymm _ (periodDeckDifference_range_le_periodCover_ker j p n)
  intro a ha
  apply (Submodule.Quotient.mk_eq_zero (LinearMap.range (periodDeckDifference j p n))).mp
  apply h
  rw [periodCoverFromDeckCoinvariants_mk, map_zero]
  exact ha

theorem periodCover_h1_ker_eq_deckDifference_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.ker (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 1) =
      LinearMap.range (periodDeckDifference j p 1) :=
  periodCover_ker_eq_deckDifference_range_of_injective j p 1
    (periodCoverFromDeckCoinvariants_h1_injective j p)

theorem periodCover_h2_ker_eq_deckDifference_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.ker (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 2) =
      LinearMap.range (periodDeckDifference j p 2) :=
  periodCover_ker_eq_deckDifference_range_of_injective j p 2
    (periodCoverFromDeckCoinvariants_h2_injective j p)

theorem periodCover_h3_ker_eq_deckDifference_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.ker (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 3) =
      LinearMap.range (periodDeckDifference j p 3) :=
  periodCover_ker_eq_deckDifference_range_of_injective j p 3
    (periodCoverFromDeckCoinvariants_h3_injective j p)

theorem periodCover_h4_ker_eq_deckDifference_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.ker (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 4) =
      LinearMap.range (periodDeckDifference j p 4) :=
  periodCover_ker_eq_deckDifference_range_of_injective j p 4
    (periodCoverFromDeckCoinvariants_h4_injective j p)

theorem periodCoverFromDeckCoinvariants_h1_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverFromDeckCoinvariants j p 1)).toAddSubgroup.index =
      j.order := by
  rw [periodCoverFromDeckCoinvariants_range, surfacePeriodCover_h1_range_index]

theorem periodCoverFromDeckCoinvariants_h2_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverFromDeckCoinvariants j p 2)).toAddSubgroup.index =
      fibreNormIndex j := by
  rw [periodCoverFromDeckCoinvariants_range, surfacePeriodCover_h2_range_index]

theorem periodCoverFromDeckCoinvariants_h3_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverFromDeckCoinvariants j p 3)).toAddSubgroup.index =
      fibreNormIndex j := by
  rw [periodCoverFromDeckCoinvariants_range, surfacePeriodCover_h3_range_index]

theorem periodCoverFromDeckCoinvariants_h4_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverFromDeckCoinvariants j p 4)).toAddSubgroup.index =
      j.order := by
  rw [periodCoverFromDeckCoinvariants_range, surfacePeriodCover_h4_range_index]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
