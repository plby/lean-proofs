/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

noncomputable section

namespace Erdos877

open scoped Classical in
def interval (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 n

end Erdos877

namespace Erdos877

open scoped Classical in
def SumFree (A : Finset ℕ) : Prop :=
  ∀ ⦃b c : ℕ⦄, b ∈ A → c ∈ A → b + c ∉ A

end Erdos877

namespace Erdos877

open scoped Classical in
def MaximalSumFreeIn (U A : Finset ℕ) : Prop :=
  A ⊆ U ∧ SumFree A ∧
    ∀ B : Finset ℕ, B ⊆ U → SumFree B → A ⊆ B → A = B

open scoped Classical in
noncomputable instance instDecidableMaximalSumFreeIn (U A : Finset ℕ) :
    Decidable (MaximalSumFreeIn U A) :=
  Classical.propDecidable _

end Erdos877

namespace Erdos877

open scoped Classical in
noncomputable def maximalSumFreeSets (n : ℕ) : Finset (Finset ℕ) :=
  (interval n).powerset.filter (MaximalSumFreeIn (interval n))

end Erdos877

namespace Erdos877

open scoped Classical in
noncomputable def maximalSumFreeCount (n : ℕ) : ℕ :=
  (maximalSumFreeSets n).card

end Erdos877

namespace Erdos877

open scoped Classical in
theorem erdos_877 :
    (fun n : ℕ ↦ (maximalSumFreeCount n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ Real.rpow 2 ((n : ℝ) / 2)) := by
  sorry

end Erdos877

end
