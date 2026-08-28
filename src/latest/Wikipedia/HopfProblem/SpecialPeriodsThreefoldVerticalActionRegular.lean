import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionTriangle
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionKernel
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry

/-!
# The effective vertical flow on the actual regular threefold family

The constructed special periods instantiate the genuine triangle-family
action.  Its kernel is proved to be exactly the integer translations,
using the actual fixed-period lattice criterion and the proved linear
independence of the special period functions.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Regular

open TrianglePeriodFamily

abbrev data : TrianglePeriodFamily.Data ℂ TriangleRegularPoint :=
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

theorem baseCovering : IsQuotientCoveringMap data.baseQuotient TriangleGroup :=
  regularCovering specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The original regular-family flow, with no remaining period inputs. -/
def flow (s : ℂ) : SpecialRegularFamily → SpecialRegularFamily := Triangle.flow data s

@[simp] theorem flow_quotient (s : ℂ) (x : data.TotalSpace) :
    flow s (data.quotient x) = data.quotient (Period.flow data.periods s x) := rfl

/-- On the original vector coordinates the flow is exactly `ζ + s e₂`. -/
theorem flow_vectorCover (s : ℂ) (x : TriangleRegularPoint × ComplexPlane₂) :
    flow s (data.quotient (data.periods.quotientMap x)) =
      data.quotient (data.periods.quotientMap (Period.vectorFlow s x)) := by
  rw [flow_quotient, Period.flow_quotientMap]

@[simp] theorem flow_projection (s : ℂ) (x : SpecialRegularFamily) :
    specialRegularFamilyProjectionToBase (flow s x) =
      specialRegularFamilyProjectionToBase x := by
  change regularInclusion (data.projection (Triangle.flow data s x)) =
    regularInclusion (data.projection x)
  rw [Triangle.flow_projection]

@[simp] theorem flow_zero (x : SpecialRegularFamily) : flow 0 x = x :=
  Triangle.flow_zero data x

theorem flow_add (s t : ℂ) (x : SpecialRegularFamily) :
    flow (s + t) x = flow s (flow t x) := Triangle.flow_add data s t x

@[simp] theorem flow_int_cast (n : ℤ) (x : SpecialRegularFamily) : flow (n : ℂ) x = x :=
  Triangle.flow_int_cast data n x

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] specialRegularFamilyChartedSpace

theorem jointFlow_holomorphic :
    ContMDiff ((IF).prod I₁) IF ω
      (fun x : SpecialRegularFamily × ℂ => flow x.2 x.1) :=
  Triangle.jointFlow_holomorphic data baseCovering

theorem flow_holomorphic (s : ℂ) : ContMDiff IF IF ω (flow s) :=
  Triangle.flow_holomorphic data baseCovering s

def flowBiholomorph (s : ℂ) : Diffeomorph IF IF SpecialRegularFamily SpecialRegularFamily ω :=
  Triangle.flowBiholomorph data baseCovering s

@[simp] theorem flowBiholomorph_apply (s : ℂ) (x : SpecialRegularFamily) :
    flowBiholomorph s x = flow s x := rfl

/-- The kernel is exactly the original integral period line, not a
potentially larger lattice of complex times. -/
theorem flow_eq_id_iff (s : ℂ) : flow s = id ↔ ∃ n : ℤ, s = (n : ℂ) := by
  constructor
  · intro h
    apply (VerticalActionKernel.vertical_mem_all_regular_lattices_iff s).mp
    intro z
    have he := congrFun h (data.quotient (data.periods.zeroSection z))
    have hm := (Triangle.flow_quotient_eq_self_iff data baseCovering s
      (data.periods.zeroSection z)).mp he
    rw [Period.vector_eq_smul] at hm
    exact hm
  · rintro ⟨n, rfl⟩
    funext x
    exact flow_int_cast n x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Regular
