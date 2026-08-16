import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.multiGoal false
set_option linter.style.cases false
set_option linter.style.whitespace false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 50000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

noncomputable section

namespace Erdos355

open Set Filter Topology
open scoped BigOperators

def IsLambdaLacunary (lambda : ℝ) (seq : ℕ → ℝ) : Prop :=
  ∀ i, seq (i + 1) / seq i ≥ lambda
def IsLacunary (a : ℕ → ℕ) : Prop :=
  ∃ lambda_val > 1, ∀ i ≥ 1, (a (i + 1) : ℝ) / a i ≥ lambda_val
def SubsetSums (seq : ℕ → ℝ) : Set ℝ :=
  { s | ∃ t : Finset ℕ, s = ∑ i ∈ t, seq i }
def FillsInterval (lambda : ℝ) (alpha beta : ℝ) : Prop :=
  ∃ n : ℕ → ℕ,
    (∀ i, 0 < n i) ∧
    IsLambdaLacunary lambda (fun i => n i) ∧
    Set.Ioo alpha beta ∩ {x | ∃ q : ℚ, x = q} ⊆ SubsetSums (fun i => (1 : ℝ) / n i)
noncomputable def R_lambda (lambda : ℝ) : ℝ :=
  sSup {len | ∃ alpha beta, beta - alpha = len ∧ FillsInterval lambda alpha beta}
def S_cond (S : Set ℕ) : Prop :=
  (∀ s ∈ S, s > 0) ∧ (∀ s ∈ S, 2 * s ∈ S) ∧ (∀ k, Odd k → ∃ s ∈ S, k ∣ s)
noncomputable def TargetInterval (f : ℕ → ℝ) : Set ℝ :=
  if Summable f then Set.Ico 0 (∑' i, f i) else Set.Ici 0
noncomputable def a_seq (lambda : ℝ) : ℕ → ℕ
| 0 => 1
| (n + 1) => Nat.ceil (lambda * (a_seq lambda n))
end Erdos355

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Set Filter Topology

namespace Erdos355

theorem Theorem_1 (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  ∃ n : ℕ → ℕ,
    (∀ i, 0 < n i) ∧
    IsLambdaLacunary lambda (fun i => n i) ∧
    Filter.Tendsto (fun i => (n (i + 1) : ℝ) / n i) Filter.atTop (nhds 2) ∧
    Set.Icc 0 2 ∩ {x : ℝ | ∃ q : ℚ, x = q} ⊆ SubsetSums (fun i => (1 : ℝ) / n i) := by
  sorry


theorem Theorem_2 (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  R_lambda lambda = ∑' i, (1 : ℝ) / a_seq lambda i := by
  sorry


theorem Theorem_3 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) :
  ∃ n : ℕ → ℕ,
    IsLambdaLacunary lambda (fun i => n i) ∧
    (∀ i, 0 < n i) ∧
    (Set.Infinite {i | (n (i + 1) : ℝ) > Lambda * n i}) ∧
    SubsetSums (fun i => (1 : ℝ) / n i) ⊇ (TargetInterval (fun i => (1 : ℝ) / n i)) ∩ {x | ∃ q : ℚ, x = q} := by
  sorry


theorem Theorem_4 (S : Set ℕ) (hS : S_cond S) :
  SubsetSums (fun i => (1 : ℝ) / (Nat.nth (· ∈ S) i)) =
    (TargetInterval (fun i => (1 : ℝ) / (Nat.nth (· ∈ S) i))) ∩ {x | ∃ q : ℚ, x = q} := by
  sorry


theorem erdos_355 :
    ∃ A : ℕ → ℕ, IsLacunary A ∧ ∃ u v : ℝ, u < v ∧ ∀ q : ℚ, ↑q ∈ Set.Ioo u v →
      q ∈ {∑ a ∈ A', (1 / a : ℚ) | (A' : Finset ℕ)
        (_ : (A' : Set ℕ) ⊆ Set.range A)} := by
  sorry

end Erdos355
