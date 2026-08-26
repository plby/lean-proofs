import ErdosProblems.Erdos69.JointResidues
import ErdosProblems.Erdos69.CategoricalJoint

/-! # The categorical model of distinct residue classes -/

open scoped BigOperators

namespace Erdos69.Elementary

noncomputable def residueOutcome {ι : Type*} (d : ℕ) (r : ι → ℕ) (t : ℕ) : Option ι := by
  classical
  exact if h : ∃ i, t ≡ r i [MOD d] then some h.choose else none

theorem residueOutcome_eq_some_iff {ι : Type*} (d : ℕ) (r : ι → ℕ)
    (hr : ∀ i j, r i ≡ r j [MOD d] → i = j) (t : ℕ) (i : ι) :
    residueOutcome d r t = some i ↔ t ≡ r i [MOD d] := by
  classical
  unfold residueOutcome
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro heq
      simpa only [heq] using h.choose_spec
    · intro ht
      exact hr _ _ (h.choose_spec.symm.trans ht)
  · constructor
    · intro heq
      cases heq
    · intro ht
      exact (h ⟨i, ht⟩).elim

theorem card_le_of_distinct_residues {ι : Type*} [Fintype ι]
    (d : ℕ) (hd : 0 < d) (r : ι → ℕ)
    (hr : ∀ i j, r i ≡ r j [MOD d] → i = j) : Fintype.card ι ≤ d := by
  let f : ι → Fin d := fun i ↦ ⟨r i % d, Nat.mod_lt _ hd⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact hr i j (congrArg Fin.val hij)
  simpa using Fintype.card_le_of_injective f hf

def assignedResidue {ι : Type*} (r : ι → ℕ) : Option ι → ℕ
  | none => 0
  | some i => r i

theorem residueOutcome_eq_assignment_iff {ι : Type*} (d : ℕ) (r : ι → ℕ)
    (hr : ∀ i j, r i ≡ r j [MOD d] → i = j) (t : ℕ)
    (a : Option ι) (ha : a ≠ none) :
    residueOutcome d r t = a ↔ t ≡ assignedResidue r a [MOD d] := by
  cases a with
  | none => exact (ha rfl).elim
  | some i => exact residueOutcome_eq_some_iff d r hr t i

namespace FiniteLaw

variable {ρ ι : Type*} [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]

theorem uniform_residue_partial_assignment_error (p : ρ → ℕ)
    (hp : ∀ j, 0 < p j) (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j)))
    (r : ρ → ι → ℕ) (hr : ∀ j i k, r j i ≡ r j k [MOD p j] → i = k)
    (T : ℕ) (hT : 0 < T) (s : Finset ρ) (a : ρ → Option ι)
    (ha : ∀ j ∈ s, a j ≠ none) :
    |(uniform T hT).mean (fun t ↦ if ∀ j ∈ s, residueOutcome (p j) (r j) t = a j
      then (1 : ℝ) else 0) - ∏ j ∈ s, (1 : ℝ) / p j| ≤ (1 : ℝ) / T := by
  classical
  have heq (t : ℕ) : (∀ j ∈ s, residueOutcome (p j) (r j) t = a j) ↔
      ∀ j ∈ s, t ≡ assignedResidue (r j) (a j) [MOD p j] := by
    apply forall₂_congr
    intro j hj
    exact residueOutcome_eq_assignment_iff _ _ (hr j) _ _ (ha j hj)
  simp_rw [heq]
  have h := uniform_mean_joint_residue_error s p (fun j ↦ assignedResidue (r j) (a j))
    (fun j _ ↦ hp j) (fun i _ j _ hij ↦ hcop hij) T hT
  simp_rw [Finset.prod_boole] at h
  simp only [Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const_one] at h ⊢
  convert h using 2
  congr 2
  funext t
  split_ifs <;> rfl

theorem uniform_residue_tuple_error (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j)))
    (r : ρ → ι → ℕ) (hr : ∀ j i k, r j i ≡ r j k [MOD p j] → i = k)
    (T : ℕ) (hT : 0 < T) (m : ℕ) (f : Fin m → ρ × ι) :
    |(uniform T hT).mean (fun t ↦
      ∏ k, (if t.val ≡ r (f k).1 (f k).2 [MOD p (f k).1] then (1 : ℝ) else 0)) -
      (independentProduct (fun j ↦ categorical ι (p j) (hp j)
        (card_le_of_distinct_residues _ (hp j) (r j) (hr j)))).mean
        (fun x ↦ ∏ k, (if x (f k).1 = some (f k).2 then (1 : ℝ) else 0))| ≤
          (1 : ℝ) / T := by
  have h := categorical_tuple_comparison (uniform T hT)
    (fun t j ↦ residueOutcome (p j) (r j) t) p hp
    (fun j ↦ card_le_of_distinct_residues _ (hp j) (r j) (hr j))
    (1 / T) (by positivity)
    (uniform_residue_partial_assignment_error p hp hcop r hr T hT) m f
  simpa only [residueOutcome_eq_some_iff _ _ (hr _)] using h

theorem optionalValue_eq_sum_indicators (c : ι → ℝ) (a : Option ι) :
    optionalValue c a = ∑ i, c i * (if a = some i then (1 : ℝ) else 0) := by
  cases a with
  | none => simp [optionalValue]
  | some i => simp [optionalValue, eq_comm]

theorem residue_moment_error (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j)))
    (r : ρ → ι → ℕ) (hr : ∀ j i k, r j i ≡ r j k [MOD p j] → i = k)
    (c : ι → ℝ) (T : ℕ) (hT : 0 < T) (m : ℕ) :
    |(uniform T hT).mean (fun t ↦
        (∑ j, ∑ i, c i * (if t.val ≡ r j i [MOD p j] then (1 : ℝ) else 0)) ^ m) -
      (independentProduct (fun j ↦ categorical ι (p j) (hp j)
        (card_le_of_distinct_residues _ (hp j) (r j) (hr j)))).mean
          (fun x ↦ (∑ j, optionalValue c (x j)) ^ m)| ≤
        (1 : ℝ) / T * ((Fintype.card ρ : ℝ) * ∑ i, |c i|) ^ m := by
  let μ := uniform T hT
  let ν := independentProduct (fun j ↦ categorical ι (p j) (hp j)
    (card_le_of_distinct_residues _ (hp j) (r j) (hr j)))
  let X : (ρ × ι) → Fin T → ℝ := fun a t ↦
    if t.val ≡ r a.1 a.2 [MOD p a.1] then 1 else 0
  let Y : (ρ × ι) → (ρ → Option ι) → ℝ := fun a x ↦
    if x a.1 = some a.2 then 1 else 0
  have h := moment_error_le μ ν (fun a : ρ × ι ↦ c a.2) X Y m (1 / T)
    (uniform_residue_tuple_error p hp hcop r hr T hT m)
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  simpa only [μ, ν, X, Y, ← optionalValue_eq_sum_indicators] using h

end FiniteLaw

end Erdos69.Elementary
