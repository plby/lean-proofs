import Wikipedia.HopfProblem.CuspExponentials
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Local normalized logarithms for the elliptic gauge

At any nonzero centre, divide by the centre to place the varying logarithm
near `1`. This gives a genuine local holomorphic branch, while its difference
from the principal normalized logarithm is always an integer.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

def localLog (z0 z : ℂ) : ℂ := logarithm z0 + logarithm (z / z0)

theorem localLog_contDiffAt_of_mem_slitPlane {z0 z : ℂ}
    (hz : z / z0 ∈ Complex.slitPlane) : ContDiffAt ℂ ω (localLog z0) z := by
  change ContDiffAt ℂ ω
    (fun w : ℂ => logarithm z0 + Complex.log (w / z0) / (2 * Real.pi * Complex.I)) z
  exact contDiffAt_const.add
    (((Complex.contDiffAt_log hz).comp z (contDiffAt_id.div_const z0)).div_const _)

theorem localLog_contDiffAt {z0 : ℂ} (hz0 : z0 ≠ 0) :
    ContDiffAt ℂ ω (localLog z0) z0 :=
  localLog_contDiffAt_of_mem_slitPlane (by simp [hz0])

theorem localLog_contDiffOn (z0 : ℂ) :
    ContDiffOn ℂ ω (localLog z0) ((fun z : ℂ => z / z0) ⁻¹' Complex.slitPlane) :=
  fun _ hz => (localLog_contDiffAt_of_mem_slitPlane hz).contDiffWithinAt

theorem exponential_localLog {z0 z : ℂ} (hz0 : z0 ≠ 0) (hz : z ≠ 0) :
    exponential (localLog z0 z) = z := by
  rw [localLog, exponential_add, exponential_logarithm hz0,
    exponential_logarithm (div_ne_zero hz hz0), mul_div_cancel₀ _ hz0]

@[simp] theorem localLog_at_self {z0 : ℂ} (hz0 : z0 ≠ 0) :
    localLog z0 z0 = logarithm z0 := by
  simp [localLog, logarithm, hz0]

theorem logarithm_eq_localLog_add_int {z0 z : ℂ} (hz0 : z0 ≠ 0) (hz : z ≠ 0) :
    ∃ n : ℤ, logarithm z = localLog z0 z + n := by
  apply (exponential_eq_iff (logarithm z) (localLog z0 z)).mp
  rw [exponential_logarithm hz, exponential_localLog hz0 hz]

end Wikipedia.HopfProblem.CuspUniformization
