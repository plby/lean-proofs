import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

namespace Erdos38

open scoped Pointwise
open Finset Real Filter

attribute [local instance] Classical.propDecidable

noncomputable section

def countIn (A : Set ℕ) (N : ℕ) : ℕ :=
  #{a ∈ Ioc 0 N | a ∈ A}

def hSumset : ℕ → Set ℕ → Set ℕ
  | 0, _ => {0}
  | h + 1, B => hSumset h B + B

def IsAdditiveBasis (B : Set ℕ) : Prop :=
  ∃ h : ℕ, ∀ᶠ n in Filter.atTop, n ∈ hSumset h B

def translateSet (A : Set ℕ) (b : ℕ) : Set ℕ := (· + b) '' A

def unionTranslateCount (A : Set ℕ) (b : ℕ) (N : ℕ) : ℕ :=
  countIn (A ∪ translateSet A b) N
end

section CountIn

end CountIn

section SchnirelmannProps

end SchnirelmannProps

section ErdosF

end ErdosF

noncomputable section

end

noncomputable section

end

noncomputable section

end

noncomputable section

end

noncomputable section

end

noncomputable section

end

noncomputable section

end

end Erdos38

attribute [local instance] Classical.propDecidable

theorem Erdos38.erdos_problem_38 :
    @Exists.{1} (Set.{0} Nat) fun (B : Set.{0} Nat) ↦
      @Exists.{1} (Real → Real) fun (f : Real → Real) ↦
        And (Not (Erdos38.IsAdditiveBasis B))
          (And
            (∀ (α : Real),
              @LT.lt.{0} Real Real.instLT
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) α →
                @LT.lt.{0} Real Real.instLT α
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                  @LT.lt.{0} Real Real.instLT
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (f α))
            (∀ (A : Set.{0} Nat),
              @LT.lt.{0} Real Real.instLT
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (@schnirelmannDensity A fun (a : Nat) ↦
                    Classical.propDecidable
                      (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A a)) →
                @LT.lt.{0} Real Real.instLT
                    (@schnirelmannDensity A fun (a : Nat) ↦
                      Classical.propDecidable
                        (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A a))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                  ∀ (N : Nat),
                    @LT.lt.{0} Nat instLTNat
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
                      @Exists.{1} Nat fun (b : Nat) ↦
                        And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) B b)
                          (@LE.le.{0} Real Real.instLE
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@schnirelmannDensity A fun (a : Nat) ↦
                                  Classical.propDecidable
                                    (@Membership.mem.{0, 0} Nat (Set.{0} Nat)
                                      (@Set.instMembership.{0} Nat) A a))
                                (f
                                  (@schnirelmannDensity A fun (a : Nat) ↦
                                    Classical.propDecidable
                                      (@Membership.mem.{0, 0} Nat (Set.{0} Nat)
                                        (@Set.instMembership.{0} Nat) A a))))
                              (@Nat.cast.{0} Real Real.instNatCast N))
                            (@Nat.cast.{0} Real Real.instNatCast (Erdos38.unionTranslateCount A b N)))))
  := by
  sorry
