import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingSection

/-!
# The inverse-overlap section contracts inside the actual cusp piece

The inverse of the genuine gluing map, restricted to regular vector zero,
is the toric section over the full disc.  Its based contraction already
exists in the native cusp quotient, before inclusion in the threefold.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching

attribute [local instance] specialCuspPieceChartedSpace specialRegularFamilyChartedSpace

/-- The regular zero section expressed in the actual cusp piece. -/
def inverseSection : OverlapBase → SpecialCuspPiece := cuspZeroSection ∘ overlapCoordinate

theorem inverseSection_continuous : Continuous inverseSection :=
  cuspZeroSection_continuous.comp overlapCoordinate_continuous

/-- This continuous section is exactly the inverse actual overlap map on zero. -/
theorem inverseSection_eq (b : OverlapBase) :
    inverseSection b = specialCuspOverlap.symm (regularZeroSection b.val) :=
  (overlap_regularZeroSection_inverse b).symm

/-- Every inverse-overlap zero-section loop contracts already in the native
cusp quotient, with its basepoint fixed throughout. -/
def inverseSectionLoopContraction {b : OverlapBase} (p : Path b b) :
    (p.map inverseSection_continuous).Homotopy (Path.refl (inverseSection b)) :=
  (CuspQuotient.zeroSectionLoopContraction specialCuspData.correction
    (p.map overlapCoordinate_continuous)).cast (by ext t; rfl) rfl

@[simp] theorem inverseSectionLoopContraction_apply {b : OverlapBase}
    (p : Path b b) (u : I × I) :
    inverseSectionLoopContraction p u =
      cuspZeroSection (CuspQuotient.discLoopContraction
        (p.map overlapCoordinate_continuous) u) := rfl

theorem inverseSection_loop_nullhomotopic {b : OverlapBase} (p : Path b b) :
    Path.Homotopic (p.map inverseSection_continuous) (Path.refl (inverseSection b)) :=
  ⟨inverseSectionLoopContraction p⟩

/-- The induced map to the actual cusp fundamental group is trivial. -/
theorem inverseSection_fundamentalGroup_map_eq_one (b : OverlapBase)
    (γ : FundamentalGroup OverlapBase b) :
    FundamentalGroup.map ⟨inverseSection, inverseSection_continuous⟩ b γ = 1 := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk p => exact Path.Homotopic.Quotient.eq.mpr (inverseSection_loop_nullhomotopic p)

theorem inclusion_inverseSection (b : OverlapBase) :
    inclusion (some none) (inverseSection b) = attachedRegularSection b :=
  (attachedRegularSection_eq_extended b).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching
