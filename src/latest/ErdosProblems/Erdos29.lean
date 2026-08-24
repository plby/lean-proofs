/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 29.
https://www.erdosproblems.com/forum/thread/29

Informal authors:
- Paul Erdős

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos29.md
-/
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.NatAntidiagonal
import ErdosProblems.Erdos29.Modular
import ErdosProblems.Erdos29.Assembly

/-!
  Erdős Problem 29

  Construct an additive basis of the natural numbers whose ordered
  representation function grows more slowly than every positive power.
-/

namespace Erdos29

open Filter
open scoped Pointwise Real

/-- The ordered number of representations of `n` as a sum of two members of `A`. -/
noncomputable def addRepCount (A : Set ℕ) (n : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.HasAntidiagonal.antidiagonal
      (self := Finset.Nat.instHasAntidiagonal) n : Finset (ℕ × ℕ)).filter
      fun ab : ℕ × ℕ => ab.1 ∈ A ∧ ab.2 ∈ A).card

/-- The exact assertion in Erdős Problem 29, with ordered representations. -/
def SolvesErdos29 (A : Set ℕ) : Prop :=
  A + A = Set.univ ∧
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsLittleO Filter.atTop
        (fun n : ℕ => (addRepCount A n : ℝ))
        (fun n : ℕ => (n : ℝ) ^ ε)

/-! ## The explicit construction -/

/-- At position `i`, use the finite additive basis modulo the square of the
least prime strictly larger than `i + 11`.  Every search occurring in this
definition is bounded. -/
def explicitDigits (i : ℕ) : Finset ℕ :=
  Modular.digitSet (primeAt i)

theorem explicitDigits_lt (i d : ℕ) (hd : d ∈ explicitDigits i) :
    d < radix i := by
  exact Modular.digitSet_mem_lt (primeAt_prime i) hd

theorem explicitDigits_cover (i r : ℕ) (hr : r < radix i) :
    ∃ x ∈ explicitDigits i, ∃ y ∈ explicitDigits i,
      (x + y) % radix i = r := by
  exact Modular.digitSet_cover (primeAt_prime i)
    (le_trans (by omega) (primeAt_ge i)) hr

/-- The concrete mixed-radix system underlying the answer. -/
def explicitSystem : MixedRadix.LocalSystem :=
  Assembly.scheduleSystem explicitDigits explicitDigits_lt explicitDigits_cover

/-- The explicit additive basis: all non-leading mixed-radix digits belong to
`explicitDigits`, while the leading digit is unrestricted. -/
def explicitBasis : Set ℕ :=
  MixedRadix.basis explicitSystem

theorem explicitDigits_flat (i r : ℕ) :
    Assembly.localRepCount explicitDigits i r ≤ 144 := by
  have hp := primeAt_prime i
  have hp11 : 11 ≤ primeAt i := le_trans (by omega) (primeAt_ge i)
  have hr : r % radix i < primeAt i ^ 2 := by
    exact Nat.mod_lt _ (radix_pos i)
  change (Modular.digitModRepresentations (primeAt i) (r % radix i)).card ≤ 144
  exact Modular.digitModRepresentations_card_le hp hp11 (r % radix i) hr

theorem addRepCount_explicitBasis (n : ℕ) :
    addRepCount explicitBasis n = MixedRadix.basisRepCount explicitSystem n := by
  rfl

theorem explicitBasis_solves : SolvesErdos29 explicitBasis := by
  have h := Assembly.assemble_schedule explicitDigits explicitDigits_lt
    explicitDigits_cover 144 (by norm_num) explicitDigits_flat
  rcases h with ⟨hcover, hsmall⟩
  constructor
  · exact hcover
  · intro ε hε
    simpa only [addRepCount_explicitBasis, explicitSystem] using hsmall ε hε

theorem exists_solvesErdos29 : ∃ A : Set ℕ, SolvesErdos29 A :=
  ⟨explicitBasis, explicitBasis_solves⟩

/-- Erdős Problem 29 has an explicit affirmative solution. -/
theorem erdos_29 :
    ∃ A : Set ℕ, A + A = Set.univ ∧
      ∀ ε : ℝ, 0 < ε →
        Asymptotics.IsLittleO Filter.atTop
          (fun n : ℕ => (addRepCount A n : ℝ))
          (fun n : ℕ => (n : ℝ) ^ ε) :=
  exists_solvesErdos29

end Erdos29

#print axioms Erdos29.erdos_29
