import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace Harmonic.GeneralizeProofs
open Lean Meta Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
end Harmonic

namespace Erdos1036

set_option linter.style.setOption false
set_option linter.style.cases false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

def hom_num {V : Type*} (G : SimpleGraph V) : ℕ := max G.cliqueNum G.indepNum
def induced_iso_rel {V : Type*} (G : SimpleGraph V) (s t : Set V) : Prop :=
  Nonempty (G.induce s ≃g G.induce t)
def I_num {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  Fintype.card (Quotient (Setoid.mk (induced_iso_rel G) (by
  constructor;
  · intro x
    use Equiv.refl x
    simp
  · rintro x y ⟨ f, hf ⟩;
    refine ⟨ f.symm, ?_ ⟩;
    grind;
  · rintro x y z ⟨ f, hf ⟩ ⟨ g, hg ⟩;
    exact ⟨ f.trans g, by aesop ⟩)))
end

end Erdos1036

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos1036.erdos_1036 :
    ∀ (c : Real),
      @GT.gt.{0} Real Real.instLT c
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Exists.{1} Real fun (ε : Real) ↦
          And
            (@GT.gt.{0} Real Real.instLT ε
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
            (@Exists.{1} Nat fun (n₀ : Nat) ↦
              ∀ (n : Nat),
                @GE.ge.{0} Nat instLENat n n₀ →
                  ∀ {V : Type u_1} [inst : Fintype.{u_1} V] [inst_1 : DecidableEq.{u_1 + 1} V]
                    (G : SimpleGraph.{u_1} V)
                    [@DecidableRel.{u_1 + 1, u_1 + 1} V V (@SimpleGraph.Adj.{u_1} V G)],
                    @Eq.{1} Nat (@Fintype.card.{u_1} V inst) n →
                      @LE.le.{0} Real Real.instLE
                          (@Nat.cast.{0} Real Real.instNatCast (@Erdos1036.hom_num.{u_1} V G))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                            (Real.logb
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                              (@Nat.cast.{0} Real Real.instNatCast n))) →
                        @GE.ge.{0} Real Real.instLE
                          (@Nat.cast.{0} Real Real.instNatCast (@Erdos1036.I_num.{u_1} V inst inst_1 G))
                          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
                              (@Nat.cast.{0} Real Real.instNatCast n))))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
