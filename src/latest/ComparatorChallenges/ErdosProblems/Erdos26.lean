import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos26

attribute [local instance] Classical.propDecidable

variable {β : Type*} [Preorder β]

variable (S : Set β) (a b : β)

abbrev Set.interIio (S : Set β) (b : β) : Set β :=
  S ∩ Set.Iio b
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  (Set.interIio (S ∩ A) b).ncard / (Set.interIio A b).ncard
open scoped Topology

open Filter

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Filter.Tendsto (fun (b : β) => partialDensity S A b) Filter.atTop (𝓝 α)

def IsThick {ι : Type*} (A : ι → ℕ) : Prop := ¬Summable (fun i ↦ (1 : ℝ) / A i)

def MultiplesOf {ι : Type*} (A : ι → ℕ) : Set ℕ := Set.range fun (n, i) ↦ n * A i

def IsBehrend {ι : Type*} (A : ι → ℕ) : Prop := HasDensity (MultiplesOf A) 1
end Erdos26

attribute [local instance] Classical.propDecidable

universe u_2

theorem Erdos26.erdos_26.variants.rusza :
    @Exists.{1} (Nat → Nat) fun (A : Nat → Nat) ↦
      And (@StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder A)
        (And (Not (@Erdos26.IsThick.{0} Nat A))
          (∀ (k : Nat),
            Not
              (@Erdos26.IsBehrend.{0} Nat fun (x : Nat) ↦
                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (A x) k)))
  := by
  sorry
