import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionMultiplicative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedElliptic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedCusp
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspFibreGeometryStrata

/-!
# The actual fixed-point locus of the constructed multiplicative action

The fixed locus is precisely the one native cusp double curve with edge
direction `(0,1)`. The result is for the already constructed action on the
actual threefold; no identification with an automorphism-group component
is used. Non-cusp pieces have no point fixed by all complex times.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction

/-- The curve called `D₀` in the fixed-locus proposition: native
double-curve index one, whose toric edge direction is `(0,1)`. -/
def D₀ : Set Space := CuspGeometry.doubleCurve 1

@[simp] theorem D₀_eq_doubleCurve : D₀ = CuspGeometry.doubleCurve 1 := rfl

/-- The actual global additive flow has exactly this fixed locus. -/
theorem flow_fixed_iff (x : Space) : (∀ s : ℂ, flow s x = x) ↔ x ∈ D₀ := by
  constructor
  · intro hx
    obtain ⟨i, y, rfl⟩ := gluingData.inclusion_jointly_surjective x
    have hy : ∀ s : ℂ, localFlow i s y = y := by
      intro s
      exact (gluingData.inclusion_openEmbedding i).injective
        ((flow_inclusion s i y).symm.trans (hx s))
    cases i with
    | none => exact (Regular.not_forall_flow_eq_self y hy).elim
    | some i =>
        cases i with
        | none =>
            exact ⟨y, (FixedCusp.specialFlow_fixed_iff_doubleCurve y).mp hy, rfl⟩
        | some j => exact (Elliptic.not_forall_specialFlow_eq_self j y hy).elim
  · rintro ⟨y, hy, rfl⟩ s
    rw [flow_cusp, (FixedCusp.specialFlow_fixed_iff_doubleCurve y).mpr hy s]

/-- Passing through the actual surjective normalized exponential does
not change the condition of being fixed by every parameter. -/
theorem action_fixed_iff_flow_fixed (x : Space) :
    letI := action
    (∀ u : ℂˣ, u • x = x) ↔ ∀ s : ℂ, flow s x = x := by
  let := action
  constructor
  · intro h s
    rw [← action_normalizedExponential]
    exact h _
  · intro h u
    obtain ⟨s, rfl⟩ := Exponential.normalizedExponential_surjective u
    rw [action_normalizedExponential]
    exact h s

/-- Pointwise fixed-locus characterization for the genuine constructed
`ℂˣ` action on the original threefold. -/
theorem action_fixed_iff (x : Space) :
    letI := action
    (∀ u : ℂˣ, u • x = x) ↔ x ∈ D₀ :=
  (action_fixed_iff_flow_fixed x).trans (flow_fixed_iff x)

/-- The native group-action fixed-point set is the single named cusp curve. -/
theorem fixedPoints_eq_D₀ :
    letI := action
    MulAction.fixedPoints ℂˣ Space = D₀ := by
  let := action
  ext x
  exact action_fixed_iff x

theorem D₀_isClosed : IsClosed D₀ := CuspGeometry.doubleCurve_isClosed 1

theorem D₀_isCompact : IsCompact D₀ := CuspGeometry.doubleCurve_compact 1

theorem D₀_subset_cuspFibre : D₀ ⊆ CuspGeometry.sphereCuspFibre :=
  CuspGeometry.doubleCurve_subset_sphereCuspFibre 1

/-- Both actual triple points belong to the fixed curve. -/
theorem lowerTriplePoint_mem_D₀ : CuspGeometry.lowerTriplePoint ∈ D₀ :=
  CuspGeometry.lowerTriplePoint_mem_doubleCurve 1

theorem upperTriplePoint_mem_D₀ : CuspGeometry.upperTriplePoint ∈ D₀ :=
  CuspGeometry.upperTriplePoint_mem_doubleCurve 1

theorem tripleStratum_subset_D₀ : CuspGeometry.tripleStratum ⊆ D₀ :=
  CuspGeometry.tripleStratum_subset_doubleCurve 1

theorem lowerTriplePoint_fixed (u : ℂˣ) :
    letI := action
    u • CuspGeometry.lowerTriplePoint = CuspGeometry.lowerTriplePoint :=
  (action_fixed_iff _).mpr lowerTriplePoint_mem_D₀ u

theorem upperTriplePoint_fixed (u : ℂˣ) :
    letI := action
    u • CuspGeometry.upperTriplePoint = CuspGeometry.upperTriplePoint :=
  (action_fixed_iff _).mpr upperTriplePoint_mem_D₀ u

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction
