import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos281

open Filter Topology

variable {n : ℕ → ℕ} (hmono : StrictMono n) (hnpos : ∀ i, 0 < n i)

def Choice (n : ℕ → ℕ) := ∀ i : ℕ, ZMod (n i)
def avoidPrefix (n : ℕ → ℕ) (a : Choice n) (k : ℕ) : Set ℤ :=
  {m | ∀ i : ℕ, i < k → (m : ZMod (n i)) ≠ a i}
def avoidAll (n : ℕ → ℕ) (a : Choice n) : Set ℤ :=
  {m | ∀ i : ℕ, (m : ZMod (n i)) ≠ a i}

open Classical in
noncomputable def densSeqZ (S : Set ℤ) (N : ℕ) : ℝ :=
  (((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (· ∈ S)).card : ℝ) / (2 * (N : ℝ) + 1)

def HasIntDensity (S : Set ℤ) (d : ℝ) : Prop :=
  Tendsto (densSeqZ S) atTop (𝓝 d)
def Erdos281Hyp (n : ℕ → ℕ) (_hmono : StrictMono n) (_hnpos : ∀ i, 0 < n i) : Prop :=
  ∀ a : Choice n, HasIntDensity (avoidAll n a) 0
def Erdos281Concl (n : ℕ → ℕ) (_hmono : StrictMono n) (_hnpos : ∀ i, 0 < n i) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ k : ℕ, ∀ a : Choice n,
      ∃ d : ℝ, HasIntDensity (avoidPrefix n a k) d ∧ d < ε
end Erdos281

attribute [local instance] Classical.propDecidable

theorem Erdos281.Erdos_281 :
    ∀ (n : Nat → Nat) (hmono : @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder n)
      (hnpos :
        ∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (n i)),
      Erdos281.Erdos281Hyp n hmono hnpos → Erdos281.Erdos281Concl n hmono hnpos
  := by
  sorry
