import Mathlib

/-!
# Finite extremal quantities for Erdős problem 856

These definitions preserve the distinctness requirement in both forbidden configurations.
The ground set `Fin n` is a relabelling of the set `{1, ..., n}` in the informal question.
-/

namespace Erdos856b

open scoped BigOperators

/-- No `k` distinct members of `A` have the same pairwise least common multiple. -/
def LcmFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a : Fin k → ℕ, Function.Injective a → (∀ i, a i ∈ A) →
    ¬ ∃ m : ℕ, ∀ i j, i ≠ j → Nat.lcm (a i) (a j) = m

/-- The reciprocal weight, using nonnegative reals so that finite suprema include zero. -/
noncomputable def reciprocalWeight (A : Finset ℕ) : NNReal :=
  ∑ a ∈ A, (a : NNReal)⁻¹

/-- All admissible subsets of the positive interval `[1, N]`. -/
noncomputable def admissibleSets (k N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter (LcmFree k)

/-- The extremal reciprocal sum in the original question. -/
noncomputable def f (k N : ℕ) : ℝ :=
  ((admissibleSets k N).sup reciprocalWeight : NNReal)

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- No `k` distinct members of a finite set family have identical pairwise unions. -/
def UnionFree (k : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ a : Fin k → Finset α, Function.Injective a → (∀ i, a i ∈ F) →
    ¬ ∃ u : Finset α, ∀ i j, i ≠ j → a i ∪ a j = u

/-- Every member of a family has cardinality `r`. -/
def Uniform (r : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ s ∈ F, s.card = r

/-- The uniform, union-free families on an `n`-element ground set. -/
noncomputable def admissibleFamilies (k n r : ℕ) : Finset (Finset (Finset (Fin n))) := by
  classical
  exact (Finset.univ.powersetCard r).powerset.filter (UnionFree k)

/-- The finite-block extremal quantity from the selected claim. -/
noncomputable def M (k n r : ℕ) : ℕ :=
  (admissibleFamilies k n r).sup Finset.card

theorem mem_admissibleSets {k N : ℕ} {A : Finset ℕ} :
    A ∈ admissibleSets k N ↔ A ⊆ Finset.Icc 1 N ∧ LcmFree k A := by
  classical
  simp [admissibleSets]

theorem reciprocalWeight_le_f {k N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hfree : LcmFree k A) :
    (reciprocalWeight A : ℝ) ≤ f k N := by
  exact_mod_cast (Finset.le_sup (f := reciprocalWeight)
    (mem_admissibleSets.mpr ⟨hA, hfree⟩))

theorem f_nonneg (k N : ℕ) : 0 ≤ f k N := NNReal.coe_nonneg _

theorem f_le_intervalWeight (k N : ℕ) :
    f k N ≤ reciprocalWeight (Finset.Icc 1 N) := by
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro A hA
  apply Finset.sum_le_sum_of_subset_of_nonneg (mem_admissibleSets.mp hA).1
  intro a _ _
  exact zero_le

theorem mem_admissibleFamilies {k n r : ℕ} {F : Finset (Finset (Fin n))} :
    F ∈ admissibleFamilies k n r ↔ Uniform r F ∧ UnionFree k F := by
  classical
  simp [admissibleFamilies, Finset.subset_iff, Uniform]

theorem card_le_M {k n r : ℕ} {F : Finset (Finset (Fin n))}
    (hU : Uniform r F) (hF : UnionFree k F) : F.card ≤ M k n r :=
  Finset.le_sup (mem_admissibleFamilies.mpr ⟨hU, hF⟩)

theorem M_le_choose (k n r : ℕ) : M k n r ≤ n.choose r := by
  apply Finset.sup_le
  intro F hF
  have hsub : F ⊆ Finset.univ.powersetCard r := by
    intro s hs
    simpa using (mem_admissibleFamilies.mp hF).1 s hs
  simpa using Finset.card_le_card hsub

end Erdos856b
