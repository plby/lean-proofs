import Mathlib

set_option autoImplicit false

namespace Erdos202

open Filter
open Asymptotics
open scoped BigOperators

def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}

abbrev ResidueAssignment (Q : Finset ℕ) : Type :=
  {q : ℕ // q ∈ Q} → ℤ

def PairwiseDisjointResidues
    (Q : Finset ℕ) (a : ResidueAssignment Q) : Prop :=
  ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
    Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))

def Admissible (N : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) ∧
  ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

def PossibleCard (N r : ℕ) : Prop :=
  ∃ Q : Finset ℕ, Admissible N Q ∧ Q.card = r

noncomputable def f (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (PossibleCard N) N

noncomputable def Zscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))

noncomputable def Lscale (α : ℝ) (N : ℕ) : ℝ :=
  Real.exp (α * Zscale N)

noncomputable def Mscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)))

def HasErdos202Asymptotic (F : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * Lscale (-(1 + ε)) N ≤ (F N : ℝ) ∧
    (F N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N

def Erdos202Statement : Prop :=
  HasErdos202Asymptotic f
end Erdos202

namespace Erdos202

open Finset
open scoped BigOperators

def primeSupport (n : ℕ) : Finset ℕ :=
  n.factorization.support

def omega (n : ℕ) : ℕ :=
  (primeSupport n).card

def rad (n : ℕ) : ℕ :=
  ∏ p ∈ primeSupport n, p

def hExp (n : ℕ) : ℕ :=
  ∏ p ∈ primeSupport n, n.factorization p
end Erdos202

namespace Erdos202

open Finset
open scoped BigOperators

def UniformFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ S ∈ A, S.card = k

def SpreadFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (κ : ℝ) : Prop :=
  ∀ T : Finset α, T.Nonempty →
    ((A.filter fun S => T ⊆ S).card : ℝ) ≤
      (A.card : ℝ) / κ ^ T.card

def PairwiseDisjointMembers {α : Type*} [DecidableEq α]
    (B : Finset (Finset α)) : Prop :=
  ∀ S ∈ B, ∀ T ∈ B, S ≠ T → Disjoint S T
end Erdos202

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

def IncreasingIn (X : Finset α) (U : Finset (Finset α)) : Prop :=
  ∀ S ∈ U, ∀ T : Finset α, T ⊆ X → S ⊆ T → T ∈ U

def minimalMembersIn (_X : Finset α) (U : Finset (Finset α)) : Finset (Finset α) :=
  U.filter fun S => ∀ T ∈ U, ¬ T ⊂ S

noncomputable def ell (X : Finset α) (U : Finset (Finset α)) : ℕ :=
  max 2 ((minimalMembersIn X U).sup Finset.card)
end

end ParkPham
end Erdos202

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

noncomputable def bernoulliMass (X S : Finset α) (p : ℝ) : ℝ :=
  p ^ S.card * (1 - p) ^ (X.card - S.card)

noncomputable def muP (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ S ∈ X.powerset.filter (· ∈ U), bernoulliMass X S p
end

end ParkPham
end Erdos202

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

def CoversIn (_X : Finset α) (G U : Finset (Finset α)) : Prop :=
  ∀ S ∈ U, ∃ T ∈ G, T ⊆ S

def pSmall (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : Prop :=
  ∃ G : Finset (Finset α),
    CoversIn X G U ∧ (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ)
end

end ParkPham
end Erdos202

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

end

end ParkPham
end Erdos202

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

end

end ParkPham
end Erdos202

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

end

end ParkPham
end Erdos202

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

end

end ParkPham
end Erdos202

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

universe u

section ThresholdDefinitions

variable {α : Type*} [DecidableEq α]

end ThresholdDefinitions

end ParkPham
end Erdos202

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

end

end ParkPham
end Erdos202

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

section

variable {α : Type*} [DecidableEq α]

end

section

variable {α : Type*} [DecidableEq α]

end

end ParkPham
end Erdos202

namespace Erdos202

open Finset
open scoped BigOperators

universe u

end Erdos202

namespace Erdos202

open Filter Finset
open scoped BigOperators

end Erdos202

namespace Erdos202

open Filter Finset
open scoped BigOperators

end Erdos202

namespace Erdos202

open Filter Finset
open scoped BigOperators

end Erdos202

namespace Erdos202

open Filter Finset
open scoped BigOperators

end Erdos202

namespace Erdos202

open Filter Finset

end Erdos202

namespace Erdos202

open Filter Finset

end Erdos202

namespace Erdos202

open Filter Finset
open Asymptotics
open scoped BigOperators

end Erdos202

namespace Erdos202

open Filter Finset
open scoped BigOperators

end Erdos202

namespace Erdos202

open Filter

end Erdos202

namespace Erdos202

open Filter Finset
open scoped BigOperators

structure PrunedData (N : ℕ) where
  Q : Finset ℕ
  Q_nonempty : Q.Nonempty
  a : ResidueAssignment Q
  admissible : Admissible N Q
  pairwise_disjoint : PairwiseDisjointResidues Q a
  K : ℕ
  K_pos : 1 ≤ K
  modulus_lower : ∀ q ∈ Q, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ)
  modulus_upper : ∀ q ∈ Q, q ≤ N
  hExp_bound : ∀ q ∈ Q, (hExp q : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))
  omega_eq : ∀ q ∈ Q, omega q = K
  K_bound : (K : ℝ) ≤ 3 * Mscale N
  rad_injective : ∀ q ∈ Q, ∀ r ∈ Q, rad q = rad r → q = r
end Erdos202

namespace Erdos202

open Filter Finset
open scoped BigOperators

end Erdos202

namespace Erdos202

open Finset
open scoped BigOperators

end Erdos202

namespace Erdos202

open Finset
open scoped BigOperators

end Erdos202

namespace Erdos202

open Filter Finset
open scoped BigOperators

end Erdos202

namespace Erdos202

open Filter Finset

end Erdos202

namespace Erdos202

open Filter
open Asymptotics
open scoped BigOperators

end Erdos202

namespace Erdos202

open Filter
open scoped BigOperators

end Erdos202

attribute [local instance] Classical.propDecidable

universe u_1 u_2

theorem Erdos202.ParkPham.park_pham_threshold_not_small_lt_exists :
    @Exists.{1} Real fun (CKK : Real) ↦
      And
        (@LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) CKK)
        (∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (X : Finset.{u_1} α)
          (U : Finset.{u_1} (Finset.{u_1} α)) (q : Real),
          @LT.lt.{0} Real Real.instLT
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) q →
            @LE.le.{0} Real Real.instLE q
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
              @LT.lt.{0} Real Real.instLT
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) CKK q)
                    (Real.log
                      (@Nat.cast.{0} Real Real.instNatCast (@Erdos202.ParkPham.ell.{u_1} α inst X U))))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                (∀ (S : Finset.{u_1} α),
                    @Membership.mem.{u_1, u_1} (Finset.{u_1} α) (Finset.{u_1} (Finset.{u_1} α))
                        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Finset.{u_1} α))
                          (Finset.{u_1} α) (@Finset.instSetLike.{u_1} (Finset.{u_1} α)))
                        U S →
                      @LE.le.{u_1} (Finset.{u_1} α)
                        (@Preorder.toLE.{u_1} (Finset.{u_1} α)
                          (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} α)
                            (@Finset.instPartialOrder.{u_1} α)))
                        S X) →
                  @Erdos202.ParkPham.IncreasingIn.{u_1} α X U →
                    Not (@Erdos202.ParkPham.pSmall.{u_1} α X U q) →
                      @GE.ge.{0} Real Real.instLE
                        (@Erdos202.ParkPham.muP.{u_1} α inst X U
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) CKK
                              q)
                            (Real.log
                              (@Nat.cast.{0} Real Real.instNatCast
                                (@Erdos202.ParkPham.ell.{u_1} α inst X U)))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
theorem Erdos202.ParkPham.spread_disjointness_theorem :
    @Exists.{1} Real fun (Csp : Real) ↦
      And
        (@LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Csp)
        (∀ {α : Type u_2} [inst : DecidableEq.{u_2 + 1} α] (A : Finset.{u_2} (Finset.{u_2} α))
          (r k : Nat) (κ : Real),
          @Finset.Nonempty.{u_2} (Finset.{u_2} α) A →
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r →
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
                @Erdos202.UniformFamily.{u_2} α inst A k →
                  @Erdos202.SpreadFamily.{u_2} α inst A κ →
                    @LE.le.{0} Real Real.instLE
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Csp
                            (@Nat.cast.{0} Real Real.instNatCast r))
                          (Real.log
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (Real.exp
                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                  (@One.toOfNat1.{0} Real Real.instOne)))
                              (@Nat.cast.{0} Real Real.instNatCast k))))
                        κ →
                      @Exists.{u_2 + 1} (Finset.{u_2} (Finset.{u_2} α))
                        fun (B : Finset.{u_2} (Finset.{u_2} α)) ↦
                        And
                          (@LE.le.{u_2} (Finset.{u_2} (Finset.{u_2} α))
                            (@Preorder.toLE.{u_2} (Finset.{u_2} (Finset.{u_2} α))
                              (@PartialOrder.toPreorder.{u_2} (Finset.{u_2} (Finset.{u_2} α))
                                (@Finset.instPartialOrder.{u_2} (Finset.{u_2} α))))
                            B A)
                          (And (@Eq.{1} Nat (@Finset.card.{u_2} (Finset.{u_2} α) B) r)
                            (@Erdos202.PairwiseDisjointMembers.{u_2} α inst B)))
  := by
  let _ := ULift.{u_2, 0} PUnit
  sorry
theorem Erdos202.bfv_omega_count_theorem :
    ∀ (ε : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) ↦
            ∀ (y K W : Nat),
              @LE.le.{0} Nat instLENat y N →
                @LE.le.{0} Nat instLENat W K →
                  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast K)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 3)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (Erdos202.Mscale N)) →
                    have d :=
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@Nat.cast.{0} Real Real.instNatCast K) (Erdos202.Mscale N);
                    @LE.le.{0} Nat instLENat
                      (@Finset.card.{0} Nat
                        (@Finset.filter.{0} Nat
                          (fun (n : Nat) ↦
                            @Eq.{1} Nat (Erdos202.omega n)
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) K W))
                          (fun (a : Nat) ↦
                            instDecidableEqNat (Erdos202.omega a)
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) K W))
                          (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y)))
                      (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                          Real.instFloorRing)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast y)
                            (Real.exp
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real
                                      (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@Neg.neg.{0} Real Real.instNeg d)
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                              (instOfNatNat (nat_lit 0))))))))
                                  ε)
                                (Erdos202.Zscale N))))
                          (Real.exp
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real
                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@Nat.cast.{0} Real Real.instNatCast W)
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                          (instOfNatNat (nat_lit 0))))))))
                              (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast N))))))))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry
theorem Erdos202.bfv_lower_bound_theorem :
    ∀ (ε : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) ↦
            @LE.le.{0} Real Real.instLE
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast N)
                (Erdos202.Lscale
                  (@Neg.neg.{0} Real Real.instNeg
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε))
                  N))
              (@Nat.cast.{0} Real Real.instNatCast (Erdos202.f N)))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry
namespace Erdos202

end Erdos202

theorem Erdos202.bfv_pruning_theorem :
    ∀ (ε : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) ↦
            ∀ (Q : Finset.{0} Nat) (a : Erdos202.ResidueAssignment Q),
              (∀ (q : Nat),
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                        (@Finset.instSetLike.{0} Nat))
                      Q q →
                    And
                      (@LE.le.{0} Nat instLENat
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) q)
                      (@LE.le.{0} Nat instLENat q N)) →
                Erdos202.PairwiseDisjointResidues Q a →
                  @GE.ge.{0} Real Real.instLE
                      (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat Q))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast (Erdos202.f N))
                        (Erdos202.Lscale (@Neg.neg.{0} Real Real.instNeg ε) N)) →
                    @Exists.{1} (Erdos202.PrunedData N) fun (D : Erdos202.PrunedData N) ↦
                      @GE.ge.{0} Real Real.instLE
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0} Nat (@Erdos202.PrunedData.Q N D)))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat Q))
                          (Erdos202.Lscale (@Neg.neg.{0} Real Real.instNeg ε) N)))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry
theorem Erdos202.erdos202_main :
    Erdos202.Erdos202Statement
  := by
  sorry
