import ErdosProblems.Erdos69.ResidueAverages
import ErdosProblems.Erdos69.FiniteExpectation
import Mathlib.Data.Nat.ChineseRemainder

/-! # Joint residue events and their finite averages -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem modEq_finset_prod_iff {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (h : Set.Pairwise (s : Set ι) (fun i j ↦ (d i).Coprime (d j))) (a b : ℕ) :
    a ≡ b [MOD ∏ i ∈ s, d i] ↔ ∀ i ∈ s, a ≡ b [MOD d i] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | @insert i s hi ih =>
    have hs : Set.Pairwise (s : Set ι) (fun i j ↦ (d i).Coprime (d j)) :=
      h.mono (by simp)
    have hcop : (d i).Coprime (∏ j ∈ s, d j) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro j hj
      exact h (by simp) (by simp [hj]) (by intro hij; subst j; exact hi hj)
    rw [Finset.prod_insert hi, ← Nat.modEq_and_modEq_iff_modEq_mul hcop, ih hs]
    simp

theorem exists_joint_residue {ι : Type*} (s : Finset ι) (d r : ι → ℕ)
    (hd : ∀ i ∈ s, 0 < d i)
    (hcop : Set.Pairwise (s : Set ι) (fun i j ↦ (d i).Coprime (d j))) :
    ∃ v : ℕ, ∀ t : ℕ,
      (∀ i ∈ s, t ≡ r i [MOD d i]) ↔ t ≡ v [MOD ∏ i ∈ s, d i] := by
  classical
  let c := Nat.chineseRemainderOfFinset r d s (fun i hi ↦ (hd i hi).ne') hcop
  refine ⟨c.val, fun t ↦ ?_⟩
  rw [modEq_finset_prod_iff s d hcop]
  constructor
  · intro ht i hi
    exact (ht i hi).trans (c.property i hi).symm
  · intro ht i hi
    exact (ht i hi).trans (c.property i hi)

namespace FiniteLaw

theorem uniform_mean_indicator (T : ℕ) (hT : 0 < T)
    (P : ℕ → Prop) [DecidablePred P] :
    (uniform T hT).mean (fun t ↦ if P t.val then (1 : ℝ) else 0) =
      (T.count P : ℝ) / T := by
  simp only [mean, uniform, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun t ↦ if P t then (1 : ℝ) else 0) T]
  rw [Nat.count_eq_card_filter_range]
  simp [Finset.sum_boole, div_eq_mul_inv, mul_comm]

theorem uniform_mean_residue_error (T d v : ℕ) (hT : 0 < T) (hd : 0 < d) :
    |(uniform T hT).mean (fun t ↦ if t.val ≡ v [MOD d] then (1 : ℝ) else 0) -
      (1 : ℝ) / d| ≤ (1 : ℝ) / T := by
  rw [uniform_mean_indicator T hT (fun t ↦ t ≡ v [MOD d])]
  exact residueFrequency_error T d v hT hd

theorem uniform_mean_joint_residue_error {ι : Type*} (s : Finset ι)
    (d r : ι → ℕ) (hd : ∀ i ∈ s, 0 < d i)
    (hcop : Set.Pairwise (s : Set ι) (fun i j ↦ (d i).Coprime (d j)))
    (T : ℕ) (hT : 0 < T) :
    |(uniform T hT).mean (fun t ↦
      ∏ i ∈ s, (if t.val ≡ r i [MOD d i] then (1 : ℝ) else 0)) -
        (1 : ℝ) / (∏ i ∈ s, d i : ℕ)| ≤ (1 : ℝ) / T := by
  classical
  obtain ⟨v, hv⟩ := exists_joint_residue s d r hd hcop
  simp_rw [Finset.prod_boole, hv]
  exact uniform_mean_residue_error T _ v hT (Finset.prod_pos hd)

end FiniteLaw

end Erdos69.Elementary
