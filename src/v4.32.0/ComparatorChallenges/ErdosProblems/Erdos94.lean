import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open scoped BigOperators
open Finset

namespace Erdos94

abbrev Point := EuclideanSpace ℝ (Fin 2)
noncomputable section

def DistSet (P : Finset Point) : Finset ℝ :=
  (P.offDiag.image (fun pq => dist pq.1 pq.2))
def distSym2 (z : Sym2 Point) : ℝ :=
  Sym2.lift ⟨fun a b => dist a b, by
    intro a b
    simp [dist_comm]⟩ z
def f (P : Finset Point) (u : ℝ) : ℕ :=
  ((P.sym2.filter (fun z => ¬ Sym2.IsDiag z ∧ distSym2 z = u)).card)
def S (P : Finset Point) : ℝ :=
  ∑ u ∈ DistSet P, ((f P u : ℝ)^2)
syntax "S(" term ")=O(n^3)" : term
def NoThreeCollinear (P : Finset Point) : Prop :=
  ∀ ⦃x y z : Point⦄, x ∈ P → y ∈ P → z ∈ P →
    x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set Point)
def ConvexPosition (P : Finset Point) : Prop :=
  (P : Set Point) ⊆ (convexHull ℝ (P : Set Point)).extremePoints ℝ
end
end Erdos94

attribute [local instance] Classical.propDecidable

theorem Erdos94.erdos94_convex_no3collinear :
    ∀ (P : Finset.{0} Erdos94.Point),
      Erdos94.ConvexPosition P →
        Erdos94.NoThreeCollinear P →
          @LE.le.{0} Real Real.instLE (Erdos94.S P)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 4)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Nat.instNeZeroSucc
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat
                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Erdos94.Point P))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Erdos94.Point P))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  := by
  sorry
