import Mathlib.Data.Finset.Sym
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1028

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable Classical.decEq

set_option maxHeartbeats 20000000
open Nat Real ENNReal
open Finset Sym2
open BigOperators
open Matrix

def inducedSum (n : ℕ) (f : Sym2 (Fin n) → ℤ) (X : Finset (Fin n)) : ℤ :=
  ∑ e ∈ X.sym2.filter (fun e => ¬e.IsDiag), f e
def coloringToInt {n : ℕ} (c : Sym2 (Fin n) → Bool) (e : Sym2 (Fin n)) : ℤ :=
  if c e then 1 else -1
noncomputable def H (n : ℕ) : ℤ :=
  let colorings := (Finset.univ : Finset (Sym2 (Fin n) → Bool))
  let subsets := (Finset.univ : Finset (Finset (Fin n)))
  let max_induced (c : Sym2 (Fin n) → Bool) : ℤ :=
    subsets.image (fun X => abs (inducedSum n (coloringToInt c) X)) |>.max' (by

    simp [subsets])
  colorings.image max_induced |>.min' (by
  bound)
open Filter

end Erdos1028

open Erdos1028

attribute [local instance] Classical.propDecidable

theorem Erdos1028.erdos_1028 :
    @Exists.{1} Real fun (c : Real) ↦
      @Exists.{1} Real fun (C : Real) ↦
        And
          (@LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
          (And (@LT.lt.{0} Real Real.instLT c C)
            (@Filter.Eventually.{0} Nat
              (fun (n : Nat) ↦
                And
                  (@LE.le.{0} Real Real.instLE
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast n)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                    (@Int.cast.{0} Real Real.instIntCast (Erdos1028.H n)))
                  (@LE.le.{0} Real Real.instLE (@Int.cast.{0} Real Real.instIntCast (Erdos1028.H n))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast n)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))))
              (@Filter.atTop.{0} Nat Nat.instPreorder)))
  := by
  sorry
