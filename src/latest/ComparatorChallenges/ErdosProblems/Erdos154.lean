import Mathlib.Analysis.Real.Sqrt
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos154

def IsSidonSetNat (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d
end Erdos154

attribute [local instance] Classical.propDecidable

theorem Erdos154.sidon_density_limit :
    ∀ (m : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
        ∀ (n_seq : Nat → Nat) (A_seq : Nat → Finset.{0} Nat),
          @Filter.Tendsto.{0, 0} Nat Real
              (fun (k : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (n_seq k))
              (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder) →
            (∀ (k x : Nat),
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (A_seq k) x →
                  @LE.le.{0} Nat instLENat x (n_seq k)) →
              (∀ (k : Nat),
                  Erdos154.IsSidonSetNat
                    (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)
                      (A_seq k))) →
                @Filter.Tendsto.{0, 0} Nat Real
                    (fun (k : Nat) ↦
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat (A_seq k)))
                        (@Nat.cast.{0} Real Real.instNatCast (n_seq k)).sqrt)
                    (@Filter.atTop.{0} Nat Nat.instPreorder)
                    (@nhds.{0} Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                  ∀ (i : Nat),
                    @LT.lt.{0} Nat instLTNat i m →
                      @Filter.Tendsto.{0, 0} Nat Real
                        (fun (k : Nat) ↦
                          @HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@Nat.cast.{0} Real Real.instNatCast
                              (@Finset.card.{0} Nat
                                (@Finset.filter.{0} Nat
                                  (fun (a : Nat) ↦
                                    @Eq.{1} Nat
                                      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
                                        a m)
                                      i)
                                  (fun (a : Nat) ↦
                                    instDecidableEqNat
                                      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
                                        a m)
                                      i)
                                  (A_seq k))))
                            (@Nat.cast.{0} Real Real.instNatCast (n_seq k)).sqrt)
                        (@Filter.atTop.{0} Nat Nat.instPreorder)
                        (@nhds.{0} Real
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@Nat.cast.{0} Real Real.instNatCast m)))
  := by
  sorry
