import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos862

set_option maxHeartbeats 1000000
open scoped BigOperators

noncomputable section

open Real Filter Asymptotics

def Sidon {α : Type} [AddCommMonoid α] (S : Set α) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S → a + b = c + d → ({a, b} : Set α) = {c, d}
section ErdosTuran

end ErdosTuran

section BoseChowla

variable {Fq Fqh : Type*} [Field Fq] [Fintype Fq]

variable [Field Fqh] [Fintype Fqh]

variable [Algebra Fq Fqh]

end BoseChowla

section Construction

end Construction

def MaximalSidonSubset (U : Finset ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ U ∧ Sidon (S : Set ℕ) ∧ ∀ S' : Finset ℕ, S' ⊆ U → Sidon (S' : Set ℕ) → S ⊆ S' → S = S'
attribute [local instance] Classical.propDecidable

noncomputable def A1 (N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter (fun S => MaximalSidonSubset (Finset.range N) S)).card
noncomputable def eta : ℝ := 1 / 2 * Real.log (5 / 4)
end

end Erdos862

attribute [local instance] Classical.propDecidable

theorem Erdos862.erdos_862 :
    ∀ (c : Real),
      @LT.lt.{0} Real Real.instLT c Erdos862.eta →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) ↦
            @GE.ge.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (Real.log (@Nat.cast.{0} Real Real.instNatCast (Erdos862.A1 N)))
                (@Nat.cast.{0} Real Real.instNatCast N).sqrt)
              c)
          (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry
