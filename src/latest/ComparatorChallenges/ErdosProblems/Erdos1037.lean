import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1037

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

def NumDistinctDegrees {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image (fun v => G.degree v)).card
end Erdos1037

open Erdos1037

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos1037.not_erdos_1037 :
    Not
      (∀ (ε : Real),
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
          ∀ (C : Real),
            @LT.lt.{0} Real Real.instLT
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
              @Exists.{1} Nat fun (n₀ : Nat) ↦
                ∀ (n : Nat),
                  @GE.ge.{0} Nat instLENat n n₀ →
                    ∀ (G : SimpleGraph.{0} (Fin n)),
                      @GE.ge.{0} Real Real.instLE
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@Erdos1037.NumDistinctDegrees.{0} (Fin n) (Fin.fintype n)
                              (instDecidableEqFin n) G fun (a b : Fin n) ↦
                              Classical.propDecidable (@SimpleGraph.Adj.{0} (Fin n) G a b)))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real
                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                  (@One.toOfNat1.{0} Real Real.instOne))
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                          (instOfNatNat (nat_lit 0))))))))
                              ε)
                            (@Nat.cast.{0} Real Real.instNatCast n)) →
                        Or
                          (@LE.le.{0} Real Real.instLE
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                              (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
                            (@Nat.cast.{0} Real Real.instNatCast
                              (@SimpleGraph.cliqueNum.{0} (Fin n) G)))
                          (@LE.le.{0} Real Real.instLE
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                              (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
                            (@Nat.cast.{0} Real Real.instNatCast
                              (@SimpleGraph.indepNum.{0} (Fin n) G))))
  := by
  sorry
