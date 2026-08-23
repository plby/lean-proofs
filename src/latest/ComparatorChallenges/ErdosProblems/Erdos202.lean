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



open Filter
open Asymptotics
open scoped BigOperators
open Finset
open Filter Finset

namespace Erdos202.ParkPham

open scoped Classical in
theorem park_pham_threshold_not_small_lt_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  sorry

section

variable {α : Type*} [DecidableEq α]

open scoped Classical in
theorem spread_disjointness_theorem :
    ∃ Csp : ℝ, 0 < Csp ∧
      ∀ {α : Type*} [DecidableEq α]
        (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
        A.Nonempty →
        2 ≤ r →
        1 ≤ k →
        Erdos202.UniformFamily A k →
        Erdos202.SpreadFamily A κ →
        Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
        ∃ B : Finset (Finset α),
          B ⊆ A ∧ B.card = r ∧ Erdos202.PairwiseDisjointMembers B := by
  sorry

end

end Erdos202.ParkPham
namespace Erdos202

open scoped Classical in
theorem bfv_omega_count_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
  sorry


open scoped Classical in
theorem bfv_lower_bound_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  sorry


end Erdos202

namespace Erdos202

open scoped Classical in
theorem bfv_pruning_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N := by
  sorry

end Erdos202
open scoped Classical in
theorem Erdos202.erdos202_main :
    Erdos202.Erdos202Statement
  := by
  sorry
