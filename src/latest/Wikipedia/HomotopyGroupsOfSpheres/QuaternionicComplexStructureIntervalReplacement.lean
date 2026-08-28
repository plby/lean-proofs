import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureLocalReplacement
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicIntervalReplacement

/-! # Local path replacement on a time interval preserves complex structures -/

noncomputable section

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
namespace IntervalReplacement

open NoExoticSixSphere.IntervalCoordinates

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, Space n)) (s u : I)

def restricted : C(I × X, Space n) :=
  H.comp ⟨fun p ↦ (Icc.convexComb s u p.1, p.2),
    ((Icc.continuous_convexComb s u).comp continuous_fst).prodMk continuous_snd⟩

theorem symplecticFamily_restricted : symplecticFamily (restricted H s u) =
    Exponential.IntervalReplacement.restricted (symplecticFamily H) s u := rfl

variable (hsu : s ≤ u)
  (hsmall : ∀ t ∈ Icc s u, ∀ x, (H (s, x), H (t, x)) ∈ ShortLog.domain n)

include hsu hsmall in
theorem localCondition (p : I × X) :
    (restricted H s u (0, p.2), restricted H s u p) ∈ ShortLog.domain n := by
  change (H (Icc.convexComb s u 0, p.2), H (Icc.convexComb s u p.1, p.2)) ∈ ShortLog.domain n
  rw [Icc.convexComb_zero]
  exact hsmall (Icc.convexComb s u p.1)
    ⟨Icc.le_convexComb hsu p.1, Icc.convexComb_le hsu p.1⟩ p.2

include hsmall in
theorem groupCondition (t : I) (ht : t ∈ Icc s u) (x : X) :
    (symplecticFamily H (s, x))⁻¹ * symplecticFamily H (t, x) ∈
      Exponential.compatibleDomain n :=
  ShortLog.relative_mem_compatibleDomain (hsmall t ht x)

def lifted : C(I × (I × X), Space n) :=
  (LocalReplacement.replacement (restricted H s u) (localCondition H s u hsu hsmall)).comp
    ⟨fun q ↦ (q.1, (normalize s u q.2.1, q.2.2)),
      continuous_fst.prodMk (((continuous_normalize s u).comp
        (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd))⟩

theorem lifted_toSymplectic (q : I × (I × X)) :
    toSymplectic (lifted H s u hsu hsmall q) =
      Exponential.IntervalReplacement.lifted (symplecticFamily H) s u hsu
        (groupCondition H s u hsmall) q := by
  change toSymplectic (LocalReplacement.replacement (restricted H s u)
    (localCondition H s u hsu hsmall) (q.1, (normalize s u q.2.1, q.2.2))) = _
  rw [LocalReplacement.replacement_toSymplectic]
  rfl

end IntervalReplacement
end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
