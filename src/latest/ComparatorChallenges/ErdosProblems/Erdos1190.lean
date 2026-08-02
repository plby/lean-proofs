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

namespace Erdos1190

open Filter Finset
open Erdos202
open scoped BigOperators

noncomputable def reciprocalSum (Q : Finset ℕ) : ℝ :=
  ∑ q ∈ Q, (q : ℝ)⁻¹

def TailAdmissible (m : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, m < q) ∧
  ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

noncomputable def reciprocalSums1190 (m : ℕ) : Set ℝ :=
  {s : ℝ | ∃ Q : Finset ℕ, TailAdmissible m Q ∧ reciprocalSum Q = s}

noncomputable def epsilon1190 (m : ℕ) : ℝ :=
  sSup (reciprocalSums1190 m)

def HasErdos1190Asymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    Lscale (-(1 + ε)) m ≤ epsilon1190 m ∧
    epsilon1190 m ≤ Lscale (-(1 - ε)) m

noncomputable def tailCountingFunction (Q : Finset ℕ) (N : ℕ) : ℕ :=
  (Q.filter fun q => q ≤ N).card

def Erdos1190BridgeReady : Prop :=
  ∀ m N : ℕ, ∀ Q : Finset ℕ,
    TailAdmissible m Q →
    tailCountingFunction Q N ≤ f N
end Erdos1190

attribute [local instance] Classical.propDecidable

theorem Erdos1190.erdos1190_bridge_ready :
    Erdos1190.Erdos1190BridgeReady
  := by
  sorry
theorem Erdos1190.erdos1190_main :
    Erdos1190.HasErdos1190Asymptotic
  := by
  sorry
