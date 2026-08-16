import Mathlib

open scoped BigOperators Topology
open Polynomial

namespace Erdos990b

def nu (f : ℂ[X]) : ℕ :=
  f.support.card

noncomputable def coeffL1 (f : ℂ[X]) : ℝ :=
  f.support.sum fun n => ‖f.coeff n‖

noncomputable def M (f : ℂ[X]) : ℝ :=
  coeffL1 f / Real.sqrt (‖f.coeff 0‖ * ‖f.leadingCoeff‖)

noncomputable def principalArg (z : ℂ) : ℝ :=
  if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z

noncomputable def argRootCount (f : ℂ[X]) (I : Set ℝ) : ℕ := by
  classical
  letI : Semiring ℂ := DivisionSemiring.toSemiring
  letI : IsDomain ℂ := instIsDomain
  exact f.roots.countP (fun z : ℂ => principalArg z ∈ I)

noncomputable def expectedRootCount (d : ℕ) (α β : ℝ) : ℝ :=
  ((β - α) / (2 * Real.pi)) * (d : ℝ)

noncomputable def angularDiscrepancy (f : ℂ[X]) (α β : ℝ) : ℝ :=
  |(argRootCount f (Set.Ico α β) : ℝ) - expectedRootCount f.natDegree α β|

def SparseErdosTuranBound (C : ℝ) : Prop :=
  ∀ (f : ℂ[X]) {α β : ℝ},
    f.coeff 0 ≠ 0 →
    f.leadingCoeff ≠ 0 →
    0 ≤ α →
    α < β →
    β ≤ 2 * Real.pi →
    angularDiscrepancy f α β ≤ C * Real.sqrt ((nu f : ℝ) * Real.log (M f))

end Erdos990b

attribute [local instance] Classical.propDecidable

open scoped BigOperators Topology
open Polynomial

namespace Erdos990b

theorem erdos990_no_absolute_constant_sparseErdosTuran :
    ¬ ∃ C : ℝ, 0 < C ∧ SparseErdosTuranBound C := by
  sorry

end Erdos990b
