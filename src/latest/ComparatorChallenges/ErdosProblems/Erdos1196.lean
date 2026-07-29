import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1196

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

def PrimitiveSet (A : Set ℕ) : Prop :=
  ∀ ⦃m n : ℕ⦄, m ∈ A → n ∈ A → m ∣ n → m = n
end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators Topology
open Filter

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators Topology
open Filter

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open Filter
open scoped Asymptotics BigOperators

def IsPrimitive {M : Type*} [CommMonoid M] (A : Set M) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → Associated x y
end Erdos1196

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos1196.PrimitiveSetsAboveX.mainTheorem :
    @Exists.{1} Real fun (C : Real) ↦
      @Exists.{1} Nat fun (x₀ : Nat) ↦
        ∀ ⦃x : Nat⦄,
          @LE.le.{0} Nat instLENat x₀ x →
            ∀ {A : Set.{0} Nat},
              Erdos1196.PrimitiveSetsAboveX.PrimitiveSet A →
                @LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat) A (@Set.Ici.{0} Nat Nat.instPreorder x) →
                  And
                    (@Summable.{0, 0} Real Nat Real.instAddCommMonoid
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Set.indicator.{0, 0} Nat Real Real.instZero A fun (m : Nat) ↦
                        @HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast m)
                            (Real.log (@Nat.cast.{0} Real Real.instNatCast m))))
                      (SummationFilter.unconditional.{0} Nat))
                    (@LE.le.{0} Real Real.instLE
                      (@tsum.{0, 0} Real Nat Real.instAddCommMonoid
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (fun (m : Nat) ↦
                          @Set.indicator.{0, 0} Nat Real Real.instZero A
                            (fun (k : Nat) ↦
                              @HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real
                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                  (@One.toOfNat1.{0} Real Real.instOne))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@Nat.cast.{0} Real Real.instNatCast k)
                                  (Real.log (@Nat.cast.{0} Real Real.instNatCast k))))
                            m)
                        (SummationFilter.unconditional.{0} Nat))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) C
                          (Real.log (@Nat.cast.{0} Real Real.instNatCast x)))))
  := by
  sorry
theorem Erdos1196.erdos_1196 :
    @Exists.{1} (Nat → Real) fun (o : Nat → Real) ↦
      And
        (@Asymptotics.IsLittleO.{0, 0, 0} Nat Real Real Real.norm Real.norm
          (@Filter.atTop.{0} Nat Nat.instPreorder) o
          (@OfNat.ofNat.{0} (Nat → Real) (nat_lit 1)
            (@One.toOfNat1.{0} (Nat → Real)
              (@Pi.instOne.{0, 0} Nat (fun (a : Nat) ↦ Real) fun (i : Nat) ↦ Real.instOne))))
        (∀ (x : Nat),
          @GT.gt.{0} Nat instLTNat x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            ∀ (A : Set.{0} Nat),
              @LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat) A (@Set.Ici.{0} Nat Nat.instPreorder x) →
                @Erdos1196.IsPrimitive.{0} Nat Nat.instCommMonoid A →
                  @LT.lt.{0} Real Real.instLT
                    (@tsum.{0, 0} Real (@Set.Elem.{0} Nat A) Real.instAddCommMonoid
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (fun (a : @Set.Elem.{0} Nat A) ↦
                        @HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (Real.log
                              (@Nat.cast.{0} Real Real.instNatCast
                                (@Subtype.val.{1} Nat
                                  (fun (x : Nat) ↦
                                    @Membership.mem.{0, 0} Nat (Set.{0} Nat)
                                      (@Set.instMembership.{0} Nat) A x)
                                  a)))
                            (@Nat.cast.{0} Real Real.instNatCast
                              (@Subtype.val.{1} Nat
                                (fun (x : Nat) ↦
                                  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                                    A x)
                                a))))
                      (SummationFilter.unconditional.{0} (@Set.Elem.{0} Nat A)))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (o x)))
  := by
  sorry
