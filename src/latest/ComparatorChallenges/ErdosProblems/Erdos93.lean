import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.cases false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
open Real Metric Set InnerProductSpace Complex
open scoped InnerProductSpace Pointwise Complex
attribute [local instance] Classical.propDecidable
namespace Erdos93
section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [Fact (Module.finrank ℝ V = 2)]

noncomputable def distinctDistances (s : Finset V) : Finset ℝ :=
  (s.product s).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [Fact (Module.finrank ℝ V = 2)]

open EuclideanGeometry
open scoped EuclideanGeometry

theorem altman_erdos (s : Finset V) (n : ℕ)
    (h_n : 3 ≤ n)
    (h_card : s.card = n)
    (h_conv : ConvexIndependent ℝ (Subtype.val : s → V)) :
    (distinctDistances s).card ≥ n / 2 := by
  sorry

end
end Erdos93
