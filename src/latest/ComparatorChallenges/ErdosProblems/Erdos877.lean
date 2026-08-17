import Mathlib

open Filter
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos877

def interval (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 n

end Erdos877

namespace Erdos877

def SumFree (A : Finset ℕ) : Prop :=
  ∀ ⦃b c : ℕ⦄, b ∈ A → c ∈ A → b + c ∉ A

end Erdos877

namespace Erdos877

def MaximalSumFreeIn (U A : Finset ℕ) : Prop :=
  A ⊆ U ∧ SumFree A ∧
    ∀ B : Finset ℕ, B ⊆ U → SumFree B → A ⊆ B → A = B

noncomputable instance instDecidableMaximalSumFreeIn (U A : Finset ℕ) :
    Decidable (MaximalSumFreeIn U A) :=
  Classical.propDecidable _

end Erdos877

namespace Erdos877

noncomputable def maximalSumFreeSets (n : ℕ) : Finset (Finset ℕ) :=
  (interval n).powerset.filter (MaximalSumFreeIn (interval n))

end Erdos877

namespace Erdos877

noncomputable def maximalSumFreeCount (n : ℕ) : ℕ :=
  (maximalSumFreeSets n).card

end Erdos877

namespace Erdos877

theorem erdos_877 :
    (fun n : ℕ ↦ (maximalSumFreeCount n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ Real.rpow 2 ((n : ℝ) / 2)) := by
  sorry

end Erdos877

end
