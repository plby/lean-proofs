/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1105.Triangles
import ErdosProblems.Erdos1105.Paths
import ErdosProblems.Erdos1105.Blocks
import ErdosProblems.Erdos1105.PathConstructions
import ErdosProblems.Erdos1105.CycleUpperReduction
import ErdosProblems.Erdos1105.CycleBoundary
import ErdosProblems.Erdos1105.CycleComponents
import ErdosProblems.Erdos1105.RainbowWalks
import ErdosProblems.Erdos1105.CrossPrivateColors
import ErdosProblems.Erdos1105.CycleUpper
import ErdosProblems.Erdos1105.DenseBipartite
import ErdosProblems.Erdos1105.DegreeObstruction
import ErdosProblems.Erdos1105.Disintegration
import ErdosProblems.Erdos1105.CycleSaturation
import ErdosProblems.Erdos1105.PathNeighborCounts
import ErdosProblems.Erdos1105.SetPath
import ErdosProblems.Erdos1105.UniversalPath
import ErdosProblems.Erdos1105.PathEar
import ErdosProblems.Erdos1105.PathSegments
import ErdosProblems.Erdos1105.ConnectedOddUpper
import ErdosProblems.Erdos1105.GoodColoring
import ErdosProblems.Erdos1105.ComponentSumBound
import ErdosProblems.Erdos1105.SeparatedRepresentative
import ErdosProblems.Erdos1105.OddPathUpper
import ErdosProblems.Erdos1105.EvenSplitBound
import ErdosProblems.Erdos1105.EvenPendant
import ErdosProblems.Erdos1105.EvenThreeClique
import ErdosProblems.Erdos1105.LongCoreNeighborPattern
import ErdosProblems.Erdos1105.ShortCoreNeighborPattern
import ErdosProblems.Erdos1105.PendantBlock
import ErdosProblems.Erdos1105.ThreePetalRainbow
import ErdosProblems.Erdos1105.LowCorePathReduction
import ErdosProblems.Erdos1105.ShortCoreStructure
import ErdosProblems.Erdos1105.ShortCoreBoundary
import ErdosProblems.Erdos1105.EvenNoncliqueCore
import ErdosProblems.Erdos1105.EvenCliqueCore
import ErdosProblems.Erdos1105.PathUpper

/-!
# Erdős Problem 1105

The corrected anti-Ramsey number counts only colors used on actual edges and
excludes rainbow non-induced copies. The historical counterexamples to the
incorrect diagonal-inclusive definition are isolated in `Erdos1105/UpstreamAudit.lean`.

Both affirmative statements are proved: the cycle asymptotic for every
`k ≥ 3`, and the exact path formula for every `5 ≤ k ≤ n`.
-/

namespace Erdos1105

open SimpleGraph Asymptotics Filter

/-- The affirmative cycle asymptotic from Erdős Problem 1105. -/
def CycleStatement : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ((fun n : ℕ ↦ (antiRamseyNum (cycleGraph k) n : ℝ) -
        (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n) =O[atTop]
      (fun _ : ℕ ↦ (1 : ℝ)))

/-- The affirmative exact path formula from Erdős Problem 1105. -/
def PathStatement : Prop :=
  ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n =
      max ((k - 2).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)

/-- The full affirmative cycle asymptotic. -/
theorem erdos_1105 : (∀ k : ℕ, 3 ≤ k →
  ((fun n : ℕ ↦ (Erdos1105.antiRamseyNum (SimpleGraph.cycleGraph k) n : ℝ) -
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n) =O[Filter.atTop]
    (fun _ : ℕ ↦ (1 : ℝ)))) := cycle_asymptotic

/-- The full affirmative exact path formula. -/
theorem erdos_1105_paths : (∀ (k n : ℕ), 5 ≤ k → k ≤ n →
  let ℓ := (k - 1) / 2
  let ε := if Odd k then 1 else 2
  Erdos1105.antiRamseyNum (SimpleGraph.pathGraph k) n =
    Max.max ((k - 2).choose 2 + 1)
      ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)) := by
  intro k n hk hn
  exact antiRamseyNum_pathGraph hk hn

/-- The `k = 3` case of the cycle asymptotic. -/
theorem erdos_1105_parts_i_triangle :
    ((fun n : ℕ ↦ (antiRamseyNum (cycleGraph 3) n : ℝ) -
        (((3 : ℝ) - 2) / 2 + 1 / ((3 : ℝ) - 1)) * n) =O[atTop]
      (fun _ : ℕ ↦ (1 : ℝ))) := by
  rw [isBigO_one_nat_atTop_iff]
  refine ⟨1, fun n ↦ ?_⟩
  rw [antiRamseyNum_cycleGraph_three]
  cases n with
  | zero => norm_num
  | succ n =>
    norm_num

/-- The general lower-bound side of the cycle asymptotic. -/
theorem erdos_1105_parts_i_lower (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, ∀ n : ℕ,
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n - C ≤
        (antiRamseyNum (cycleGraph k) n : ℝ) :=
  ⟨((k - 1).choose 2 + 2 : ℕ), cycle_lower_bound_real k hk⟩

/-- The general lower-bound side of the exact path formula. -/
theorem erdos_1105_parts_ii_lower (k n : ℕ) (hk : 5 ≤ k) (hn : k ≤ n) :
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    max ((k - 2).choose 2 + 1)
      ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) ≤
        antiRamseyNum (pathGraph k) n :=
  path_formula_lower_bound k n hk hn

/-- The exact affirmative path formula for every odd path order. -/
theorem erdos_1105_parts_ii_odd (k n : ℕ) (hk : 5 ≤ k) (hodd : Odd k) (hn : k ≤ n) :
    let ℓ := (k - 1) / 2
    antiRamseyNum (pathGraph k) n =
      max ((k - 2).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + 1) := by
  simpa only [pathFormula, if_pos hodd] using antiRamseyNum_pathGraph_odd hk hodd hn

end Erdos1105

#print axioms Erdos1105.antiRamseyNum_cycleGraph_three
#print axioms Erdos1105.erdos_1105
#print axioms Erdos1105.erdos_1105_paths
#print axioms Erdos1105.erdos_1105_parts_i_triangle
#print axioms Erdos1105.self_le_antiRamseyNum_pathGraph_five
#print axioms Erdos1105.erdos_1105_parts_i_lower
#print axioms Erdos1105.erdos_1105_parts_ii_lower
#print axioms Erdos1105.erdos_1105_parts_ii_odd
#print axioms Erdos1105.weak_blocks_upper_bound
#print axioms Erdos1105.private_representative_cycle_boundary
#print axioms Erdos1105.private_cycle_component_contained
#print axioms Erdos1105.private_component_hamiltonian_and_card
#print axioms Erdos1105.cross_component_color_not_private

alias _root_.Erdos1105.erdos_1105_parts_i := _root_.Erdos1105.erdos_1105

alias _root_.Erdos1105.erdos_1105_parts_ii := _root_.Erdos1105.erdos_1105_paths
