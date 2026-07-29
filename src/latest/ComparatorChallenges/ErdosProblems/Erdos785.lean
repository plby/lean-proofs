import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos785

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.cases false
set_option maxHeartbeats 1000000
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

set_option autoImplicit false

section

open Pointwise

def is_additive_complement (A B : Set ℕ) : Prop :=
  (Set.univ \ (A + B)).Finite
noncomputable def counting_function (A : Set ℕ) (x : ℝ) : ℕ :=
  Nat.card {n ∈ A | n ≤ x}
def exact_complements (A B : Set ℕ) : Prop :=
  is_additive_complement A B ∧
  Filter.Tendsto (fun x : ℝ => (counting_function A x * counting_function B x : ℝ) / x) Filter.atTop (nhds 1)

end

end Erdos785

attribute [local instance] Classical.propDecidable

theorem Erdos785.corollary_erdos_785 :
    ∀ (A B : Set.{0} Nat),
      @Set.Infinite.{0} Nat A →
        @Set.Infinite.{0} Nat B →
          (∀ (a : Nat),
              @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A a →
                @Ne.{1} Nat a (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
            (∀ (b : Nat),
                @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) B b →
                  @Ne.{1} Nat b (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
              Erdos785.exact_complements A B →
                @Filter.Tendsto.{0, 0} Real Real
                  (fun (x : Real) ↦
                    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast (Erdos785.counting_function A x))
                        (@Nat.cast.{0} Real Real.instNatCast (Erdos785.counting_function B x)))
                      x)
                  (@Filter.atTop.{0} Real Real.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder)
  := by
  sorry
