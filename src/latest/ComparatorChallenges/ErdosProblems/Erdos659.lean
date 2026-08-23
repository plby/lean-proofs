/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib
import ErdosProblems.Axioms

open Nat Finset Real Filter Asymptotics Topology
open scoped Pointwise
namespace Erdos659

set_option linter.style.setOption false
set_option linter.flexible false
set_option maxHeartbeats 50000000

open scoped Real

open Filter

open Asymptotics

open Finset Real

notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

notation g " ≪ " f => Asymptotics.IsBigO Filter.atTop (g : ℕ → ℝ) (f : ℕ → ℝ)

noncomputable def distinctDistances (points : Finset ℝ²) : ℕ :=
  (points.offDiag.image fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2).card
end Erdos659


open scoped Real
open Filter
open Asymptotics
open EuclideanGeometry Finset Real

namespace Erdos659

open scoped Classical in
theorem erdos_659 : ∃ A : ℕ → Finset ℝ²,
   (∀ n, #(A n) = n ∧ ∀ S ⊆ A n, #S = 4 → 3 ≤ distinctDistances S) ∧
    (fun n ↦ distinctDistances (A n)) ≪ fun n ↦ n / sqrt (log n) := by
  sorry

end Erdos659
