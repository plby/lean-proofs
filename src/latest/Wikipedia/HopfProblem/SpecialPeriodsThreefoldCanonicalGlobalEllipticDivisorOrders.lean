import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisor

/-!
# Exact order two for the constructed effective Cartier section

The transverse coefficient is extracted from the actual local
trivialization of the independently clutched divisor bundle, along the
actual global inverse-chart transverse line.  Its germ agrees with the
already proved native canonical-section coefficient.  This proves exact
multiplicity two at every point of the actual central support, rather
than attaching a multiplicity to a merely named line bundle.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor

open TrianglePeriodFamily.Canonical

local notation "I" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace specialEllipticPieceChartedSpace

local instance divisorOrdersManifold : IsManifold I ω Threefold.Space :=
  Threefold.space_isManifold

/-- The actual divisor-bundle section coefficient in an actual adapted
global chart, restricted to that chart's actual transverse line. -/
def transverseCoefficient (y : patch) (z : ℂ) : ℂ :=
  transitions.localCoefficient canonicalSection (some (Sections.patchSectionChart .four y))
    (Sections.patchTransversePoint .four y z).val

/-- Actual bundle-chart compatibility identifies the defining germ with
the genuine order-four canonical-section germ. -/
theorem transverseCoefficient_eventuallyEq (y : patch) :
    transverseCoefficient y =ᶠ[
      𝓝 (chartAt Model (Sections.nativePatchPoint .four y) (Sections.nativePatchPoint .four y)).1]
        Sections.patchTransverseCoefficient .four y := by
  filter_upwards [Sections.patchTransversePoint_mem_source_eventually .four y] with z hz
  change transitions.localCoefficient canonicalSection
    (some (Sections.patchSectionChart .four y))
      (Sections.patchTransversePoint .four y z).val = _
  rw [canonicalSection_localCoefficient (some (Sections.patchSectionChart .four y))
    (x := (Sections.patchTransversePoint .four y z).val)
    ⟨(Sections.patchTransversePoint .four y z).property, hz⟩]
  exact patchCoefficient_transverse y z

theorem transverseCoefficient_eventuallyEq_zero (y : patch) (hy : y.val ∈ support) :
    transverseCoefficient y =ᶠ[𝓝 (0 : ℂ)] Sections.patchTransverseCoefficient .four y := by
  have hc := Sections.nativePatchPoint_chart_first_eq_zero .four y
    (((mem_support y.val).mp hy).trans EllipticGeometry.sphereValue_four.symm)
  simpa only [hc] using transverseCoefficient_eventuallyEq y

/-- The actual divisor-bundle germ is a square times the actual period
unit, so the claimed multiplicity is witnessed by a proved factorization. -/
theorem transverseCoefficient_factorization (y : patch) (hy : y.val ∈ support) :
    transverseCoefficient y =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ => z ^ 2 * SectionsUnit.discExtension (SectionsUnit.specialUnit .four) z) :=
  (transverseCoefficient_eventuallyEq_zero y hy).trans
    (Sections.patchTransverseCoefficient_factorization .four y
      (((mem_support y.val).mp hy).trans EllipticGeometry.sphereValue_four.symm))

theorem transverseUnit_analyticAt :
    AnalyticAt ℂ (SectionsUnit.discExtension (SectionsUnit.specialUnit .four)) 0 :=
  SectionsUnit.discExtension_analyticAt (SectionsUnit.specialUnit_holomorphic .four)

theorem transverseUnit_ne_zero :
    SectionsUnit.discExtension (SectionsUnit.specialUnit .four) 0 ≠ 0 := by
  rw [SectionsUnit.discExtension_zero]
  exact SectionsUnit.specialUnit_ne_zero .four discZero

/-- The coefficient of the constructed divisor bundle's actual section
is analytic, including at every point of its zero set. -/
theorem transverseCoefficient_analyticAt (y : patch) (hy : y.val ∈ support) :
    AnalyticAt ℂ (transverseCoefficient y) 0 :=
  (Sections.patchTransverseCoefficient_analyticAt .four y
    (((mem_support y.val).mp hy).trans EllipticGeometry.sphereValue_four.symm)).congr
      (transverseCoefficient_eventuallyEq_zero y hy).symm

/-- The effective Cartier section has exactly multiplicity two at every
point of the actual reduced elliptic support. -/
theorem transverseCoefficient_order_two (y : patch) (hy : y.val ∈ support) :
    analyticOrderAt (transverseCoefficient y) 0 = 2 :=
  (analyticOrderAt_congr (transverseCoefficient_eventuallyEq_zero y hy)).trans
    (Sections.patchTransverseCoefficient_four_order y ((mem_support y.val).mp hy))

/-- Every global support point is covered, so no central point is omitted
from the exact order-two statement. -/
theorem canonicalSection_order_two (x : Threefold.Space) (hx : x ∈ support) :
    analyticOrderAt (transverseCoefficient ⟨x, support_subset_patch hx⟩) 0 = 2 :=
  transverseCoefficient_order_two ⟨x, support_subset_patch hx⟩ hx

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor
