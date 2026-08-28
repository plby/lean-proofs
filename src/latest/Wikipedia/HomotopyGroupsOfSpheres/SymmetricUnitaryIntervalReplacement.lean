import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryLocalReplacement
import Wikipedia.NoExoticSixSphere.OrthogonalIntervalReplacement

/-! # Local path replacement on a time interval preserves symmetric determinant-one matrices -/

noncomputable section

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
namespace IntervalReplacement

open NoExoticSixSphere.IntervalCoordinates ComplexMatrixRealRepresentation

variable {N : Type*} [Fintype N] [DecidableEq N] {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, SpecialSpace N)) (s u : I)

def restricted : C(I × X, SpecialSpace N) :=
  H.comp ⟨fun p ↦ (Icc.convexComb s u p.1, p.2),
    ((Icc.continuous_convexComb s u).comp continuous_fst).prodMk continuous_snd⟩

theorem orthogonalFamily_restricted : orthogonalFamily (restricted H s u) =
    NoExoticSixSphere.OrthogonalExponential.IntervalReplacement.restricted
      (orthogonalFamily H) s u := rfl

variable (hsu : s ≤ u)
  (hsmall : ∀ t ∈ Icc s u, ∀ x, (H (s, x), H (t, x)) ∈ ShortLog.domain N)

include hsu hsmall in
theorem localCondition (p : I × X) :
    (restricted H s u (0, p.2), restricted H s u p) ∈ ShortLog.domain N := by
  change (H (Icc.convexComb s u 0, p.2), H (Icc.convexComb s u p.1, p.2)) ∈ ShortLog.domain N
  rw [Icc.convexComb_zero]
  exact hsmall (Icc.convexComb s u p.1)
    ⟨Icc.le_convexComb hsu p.1, Icc.convexComb_le hsu p.1⟩ p.2

include hsmall in
theorem groupCondition (t : I) (ht : t ∈ Icc s u) (x : X) :
    (orthogonalFamily H (s, x))⁻¹ * orthogonalFamily H (t, x) ∈
      (NoExoticSixSphere.OrthogonalExponential.logarithmChart (2 * Fintype.card N)).source := by
  change (specialOrthogonal (H (s, x)))⁻¹ * specialOrthogonal (H (t, x)) ∈ _
  rw [← ShortLog.orthogonal_relative]
  exact ComplexSkewMatrices.CompatibleLog.orthogonal_mem_source _ (hsmall t ht x)

def lifted : C(I × (I × X), SpecialSpace N) :=
  (LocalReplacement.replacement (restricted H s u) (localCondition H s u hsu hsmall)).comp
    ⟨fun q ↦ (q.1, (NoExoticSixSphere.IntervalCoordinates.normalize s u q.2.1, q.2.2)),
      continuous_fst.prodMk
        (((NoExoticSixSphere.IntervalCoordinates.continuous_normalize s u).comp
        (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd))⟩

theorem lifted_toOrthogonal (q : I × (I × X)) :
    specialOrthogonal (lifted H s u hsu hsmall q) =
      NoExoticSixSphere.OrthogonalExponential.IntervalReplacement.lifted
        (orthogonalFamily H) s u hsu
        (groupCondition H s u hsmall) q := by
  change specialOrthogonal (LocalReplacement.replacement (restricted H s u)
    (localCondition H s u hsu hsmall)
      (q.1, (NoExoticSixSphere.IntervalCoordinates.normalize s u q.2.1, q.2.2))) = _
  rw [LocalReplacement.replacement_toOrthogonal]
  rfl

end IntervalReplacement
end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
