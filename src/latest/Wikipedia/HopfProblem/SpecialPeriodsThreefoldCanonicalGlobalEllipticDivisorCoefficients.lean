import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorNative

/-!
# Actual local equations for twice the elliptic central surface

Only the genuine canonical section on the order-four elliptic patch is
used here.  Its extension by zero is a convenient total function; no
holomorphicity outside that patch is asserted.  The local defining
functions are its coefficients in the original global canonical charts.
Their coordinate changes are the actual inverse-Jacobian transitions,
including at points where the defining functions vanish.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor

open TrianglePeriodFamily.Canonical

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace

local instance coefficientsManifold : IsManifold I ω Threefold.Space :=
  Threefold.space_isManifold

/-- A total extension of the actual patch section, used only on its
original domain when proving holomorphicity or local equations. -/
def extendedSection (x : Threefold.Space) : Threefold.Canonical.bundle.Fiber x := by
  classical
  exact if hx : x ∈ patch then Sections.patchSection .four ⟨x, hx⟩ else 0

theorem extendedSection_of_mem {x : Threefold.Space} (hx : x ∈ patch) :
    extendedSection x = Sections.patchSection .four ⟨x, hx⟩ := by
  simp only [extendedSection, dif_pos hx]

def extendedSectionMap (x : Threefold.Space) : Threefold.Canonical.bundle.TotalSpace :=
  ⟨x, extendedSection x⟩

theorem extendedSectionMap_restrict (x : patch) :
    extendedSectionMap x.val = Sections.patchSectionMap .four x := by
  rw [extendedSectionMap, extendedSection_of_mem x.property]
  rfl

/-- The original patch section gives holomorphicity on precisely its
actual open domain, with the original global bundle topology. -/
theorem extendedSectionMap_holomorphicOn :
    ContMDiffOn I Iᴷ ω extendedSectionMap patch := by
  have h : ContMDiff I Iᴷ ω (fun x : patch => extendedSectionMap x.val) := by
    have he : (fun x : patch => extendedSectionMap x.val) = Sections.patchSectionMap .four :=
      funext extendedSectionMap_restrict
    rw [he]
    exact Sections.patchSectionMap_holomorphic .four
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (h ⟨x, hx⟩)).contMDiffWithinAt

/-- The actual global canonical coefficient of the elliptic patch section. -/
def patchCoefficient (i : atlas Model Threefold.Space) (x : Threefold.Space) : ℂ :=
  (Threefold.Canonical.bundle.localTriv i ⟨x, extendedSection x⟩).2

theorem patchCoefficient_holomorphicOn (i : atlas Model Threefold.Space) :
    ContMDiffOn I I₁ ω (patchCoefficient i) ((patch : Set Threefold.Space) ∩ i.val.source) :=
  (Threefold.Canonical.bundle.localTriv i).contMDiffOn_section_iff
    (patch.isOpen.inter i.val.open_source) inter_subset_right |>.mp
      (extendedSectionMap_holomorphicOn.mono inter_subset_left)

/-- The local defining function vanishes exactly on the literal global
central sphere fibre, wherever its chart is valid in the patch. -/
theorem patchCoefficient_eq_zero_iff (i : atlas Model Threefold.Space)
    {x : Threefold.Space} (hx : x ∈ patch) (hi : x ∈ i.val.source) :
    patchCoefficient i x = 0 ↔ x ∈ support := by
  change Atlas.jacobian Threefold.Space i (achart Model x) x *
    id (α := ℂ) (extendedSection x) = 0 ↔ x ∈ support
  rw [mul_eq_zero]
  simp only [Atlas.jacobian_ne_zero Threefold.Space i (achart Model x)
    hi (mem_chart_source Model x), false_or]
  rw [extendedSection_of_mem hx]
  exact Sections.patchSection_four_eq_zero_iff ⟨x, hx⟩

theorem patchCoefficient_ne_zero (i : atlas Model Threefold.Space)
    {x : Threefold.Space} (hx : x ∈ patch) (hi : x ∈ i.val.source) (hg : x ∈ outside) :
    patchCoefficient i x ≠ 0 := by
  intro hzero
  exact hg ((patchCoefficient_eq_zero_iff i hx hi).mp hzero)

/-- These transition-ratio equations are obtained from the actual
canonical bundle atlas, so remain valid across the zero set. -/
theorem patchCoefficient_change (i j : atlas Model Threefold.Space)
    {x : Threefold.Space} (hi : x ∈ i.val.source) (hj : x ∈ j.val.source) :
    (NativeTransitions.transition Threefold.Space i j x : ℂ) * patchCoefficient i x =
      patchCoefficient j x :=
  NativeTransitions.coefficient_change Threefold.Space i j ⟨hi, hj⟩ (extendedSection x)

/-- The scalar defining function is the coefficient of the genuine
alternating top covector, rather than a separately assigned equation. -/
theorem patchCoefficient_eq_topCovector (i : atlas Model Threefold.Space)
    (x : patch) :
    patchCoefficient i x.val = coefficient
      (Threefold.Canonical.inCoordinates i x.val (Sections.patchSection .four x)) := by
  rw [patchCoefficient, extendedSection_of_mem x.property]
  change _ = coefficient (coefficientEquiv _)
  simp only [coefficientEquiv_apply, coefficient_smul, coefficient_volume, mul_one]
  rfl

/-- On the actual transverse line, the local defining coefficient is
exactly the previously computed genuine canonical-section coefficient. -/
theorem patchCoefficient_transverse (y : patch) (z : ℂ) :
    patchCoefficient (Sections.patchSectionChart .four y)
      (Sections.patchTransversePoint .four y z).val =
        Sections.patchTransverseCoefficient .four y z :=
  patchCoefficient_eq_topCovector _ (Sections.patchTransversePoint .four y z)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor
