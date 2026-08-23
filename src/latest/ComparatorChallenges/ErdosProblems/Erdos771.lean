/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 771

The detailed mathematical proof and Leanization map are in tex/771.tex.
-/

open Filter Finset Nat Real
open scoped BigOperators Topology

namespace Erdos771

noncomputable section

/-- A finite set has no subset whose sum is the positive target m. -/
def AvoidsSubsetSum (m : ℕ) (S : Finset ℕ) : Prop :=
  m ∉ S.subsetSum

/-- The exact quantifier order in Problem 771. -/
def AdmissibleCard (n k : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ S : Finset ℕ,
      S ⊆ Finset.Icc 1 n ∧ S.card = k ∧ AvoidsSubsetSum m S

local instance decidableAdmissibleCard (n : ℕ) : DecidablePred (AdmissibleCard n) :=
  fun _ => Classical.propDecidable _

/-- The largest cardinality that works simultaneously for every positive target. -/
noncomputable def erdosF (n : ℕ) : ℕ :=
  Nat.findGreatest (AdmissibleCard n) n


theorem erdos_771 :
    True ↔
      Tendsto (fun n : ℕ =>
        (erdosF n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)))
        atTop (𝓝 (1 / 2 : ℝ)) := by
  sorry

end

end Erdos771
