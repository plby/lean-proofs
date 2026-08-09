import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos618

noncomputable def maxDegreeFin {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact Finset.univ.sup (fun v : Fin n =>
    @SimpleGraph.degree (Fin n) G v inferInstance)

open scoped Classical in
noncomputable def h2 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  exact sInf {k : ℕ |
    ∃ H : SimpleGraph (Fin n),
      G ≤ H ∧
      H.CliqueFree 3 ∧
      (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
      ((H.edgeFinset \ G.edgeFinset).card = k)}
end Erdos618

attribute [local instance] Classical.propDecidable

theorem Erdos618.erdos_618 :
    ∀ (G : (n : Nat) → SimpleGraph.{0} (Fin n)),
      (∀ (n : Nat),
          @SimpleGraph.CliqueFree.{0} (Fin n) (G n)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
        (@Asymptotics.IsLittleO.{0, 0, 0} Nat Real Real Real.norm Real.norm
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (fun (n : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (@Erdos618.maxDegreeFin n (G n)))
            fun (n : Nat) ↦
            (@Nat.cast.{0} Real Real.instNatCast n).rpow
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
          @Asymptotics.IsLittleO.{0, 0, 0} Nat Real Real Real.norm Real.norm
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (fun (n : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (@Erdos618.h2 n (G n))) fun (n : Nat) ↦
            @HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat
                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast n)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
  := by
  sorry
