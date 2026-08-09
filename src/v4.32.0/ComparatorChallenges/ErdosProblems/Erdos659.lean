import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open Nat Finset Real Filter Asymptotics Topology
open scoped Pointwise

structure BinQuadForm where
  a : ℤ
  b : ℤ
  c : ℤ
namespace BinQuadForm

def eval (f : BinQuadForm) (x y : ℤ) : ℤ :=
  f.a * x * x + f.b * x * y + f.c * y * y

def discr (f : BinQuadForm) : ℤ :=
  f.b * f.b - 4 * f.a * f.c

def Primitive (f : BinQuadForm) : Prop :=
  Int.gcd f.a (Int.gcd f.b f.c) = 1

def PosDef (f : BinQuadForm) : Prop :=
  0 < f.a ∧ f.discr < 0

noncomputable def B (f : BinQuadForm) (x : ℝ) : ℕ :=
  Nat.card {n : ℕ | (n : ℝ) ≤ x ∧ ∃ u v : ℤ, f.eval u v = (n : ℤ)}
end BinQuadForm

axiom bernays
    (Δ : ℤ) (hΔnonsq : ¬ ∃ z : ℤ, z * z = Δ) :
    ∃ CΔ : ℝ, 0 < CΔ ∧
      ∀ f : BinQuadForm,
        f.Primitive →
        f.PosDef →
        f.discr = Δ →
        (fun x : ℝ => (f.B x : ℝ))
          ~[Filter.atTop]
          (fun x : ℝ => CΔ * x / Real.sqrt (Real.log x))

namespace Erdos659

set_option linter.style.setOption false
set_option linter.flexible false
set_option maxHeartbeats 50000000

open scoped Real

open Filter

open Asymptotics

open Finset Real

notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

notation g " ≪ " f => Asymptotics.IsBigO Filter.atTop (g : ℕ → ℝ) (f : ℕ → ℝ)

noncomputable def distinctDistances (points : Finset ℝ²) : ℕ :=
  (points.offDiag.image fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2).card
end Erdos659

attribute [local instance] Classical.propDecidable

theorem Erdos659.erdos_659 :
    @Exists.{1}
      (Nat →
        Finset.{0}
          (EuclideanSpace.{0, 0} Real
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      fun
        (A :
          Nat →
            Finset.{0}
              (EuclideanSpace.{0, 0} Real
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) ↦
      And
        (∀ (n : Nat),
          And
            (@Eq.{1} Nat
              (@Finset.card.{0}
                (EuclideanSpace.{0, 0} Real
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (A n))
              n)
            (∀
              (S :
                Finset.{0}
                  (EuclideanSpace.{0, 0} Real
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))),
              @LE.le.{0}
                  (Finset.{0}
                    (EuclideanSpace.{0, 0} Real
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                  (@Preorder.toLE.{0}
                    (Finset.{0}
                      (EuclideanSpace.{0, 0} Real
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    (@PartialOrder.toPreorder.{0}
                      (Finset.{0}
                        (EuclideanSpace.{0, 0} Real
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                      (@Finset.instPartialOrder.{0}
                        (EuclideanSpace.{0, 0} Real
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  S (A n) →
                @Eq.{1} Nat
                    (@Finset.card.{0}
                      (EuclideanSpace.{0, 0} Real
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      S)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (Erdos659.distinctDistances S)))
        (@Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm
          (@Filter.atTop.{0} Nat Nat.instPreorder)
          (fun (n : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (Erdos659.distinctDistances (A n)))
          fun (n : Nat) ↦
          @HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast n)
            (Real.log (@Nat.cast.{0} Real Real.instNatCast n)).sqrt)
  := by
  sorry
