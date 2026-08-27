import ErdosProblems.Erdos4.FGKMTSourceChernoff
import ErdosProblems.Erdos4.FGKMTInitialEdgeGeometry
import ErdosProblems.Erdos4.FGKMTThinning

/-! Partition source primes into disjoint dyadic covering rounds while preserving degree lower bounds. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

theorem dyadic_round_total (m : ℕ) :
    (1 / 2 : ℝ) ^ m + ∑ j : Fin m, (1 / 2 : ℝ) ^ (j.val + 1) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, pow_succ]
      simp only [pow_succ] at ih
      nlinarith

noncomputable def dyadicRoundLaw (m : ℕ) : FiniteLaw (Option (Fin m)) where
  weight o := match o with
    | none => (1 / 2 : ℝ) ^ m
    | some j => (1 / 2 : ℝ) ^ (j.val + 1)
  nonneg o := by cases o <;> dsimp <;> positivity
  total := by
    rw [Fintype.sum_option]
    exact dyadic_round_total m

theorem dyadicRoundLaw_prob_some (m : ℕ) (j : Fin m) :
    (dyadicRoundLaw m).prob (fun o => o = some j) = (1 / 2 : ℝ) ^ (j.val + 1) := by
  simp [FiniteLaw.prob, dyadicRoundLaw]

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

theorem exists_dyadic_source_partition (μ : I → FiniteLaw (Finset V)) (m : ℕ)
    {δ : ℝ} (hδ : 0 < δ)
    (hdegree : ∀ v, (∑ i, (μ i).prob (fun e => v ∈ e)) = 4)
    (hmarginal : ∀ i v, (μ i).prob (fun e => v ∈ e) ≤ δ)
    (hbudget : (m : ℝ) * Fintype.card V * Real.exp (-((1 / 2 : ℝ) ^ m) / (6 * δ)) < 1) :
    ∃ a : I → Option (Fin m), ∀ j : Fin m, ∀ v : V,
      (1 / 2 : ℝ) ^ j.val ≤ ∑ i, if a i = some j then (μ i).prob (fun e => v ∈ e) else 0 := by
  let ν := FiniteLaw.independent (fun _ : I => dyadicRoundLaw m)
  let F := fun (a : I → Option (Fin m)) (j : Fin m) (v : V) =>
    (∑ i, if a i = some j then (μ i).prob (fun e => v ∈ e) else 0) < (1 / 2 : ℝ) ^ j.val
  have htail : ∀ j : Fin m, ∀ v : V,
      ν.prob (fun a => F a j v) ≤ Real.exp (-((1 / 2 : ℝ) ^ m) / (6 * δ)) := by
    intro j v
    have ht := FiniteLaw.independent_weighted_lower_tail (fun _ : I => dyadicRoundLaw m)
      (fun _ o => o = some j) (fun i => (μ i).prob (fun e => v ∈ e)) hδ
      (fun i => (μ i).prob_nonneg _) (fun i => hmarginal i v)
    have hM : (∑ i : I, (dyadicRoundLaw m).prob (fun o => o = some j) *
        (μ i).prob (fun e => v ∈ e)) = 2 * (1 / 2 : ℝ) ^ j.val := by
      simp only [dyadicRoundLaw_prob_some]
      rw [← Finset.mul_sum, hdegree, pow_succ]
      ring
    dsimp only at ht
    rw [hM, show 2 * (1 / 2 : ℝ) ^ j.val / 2 = (1 / 2 : ℝ) ^ j.val by ring,
      show -(2 * (1 / 2 : ℝ) ^ j.val) / (12 * δ) =
        -((1 / 2 : ℝ) ^ j.val) / (6 * δ) by ring] at ht
    have ht' : ν.prob (fun a => F a j v) ≤ Real.exp (-((1 / 2 : ℝ) ^ j.val) / (6 * δ)) := by
      simpa only [ν, F] using ht
    apply ht'.trans
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (neg_le_neg (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) j.isLt.le)) (by positivity)
  have hunion : ν.prob (fun a => ∃ j : Fin m, ∃ v : V, F a j v) ≤
      ∑ j : Fin m, ∑ v : V, ν.prob (fun a => F a j v) := by
    calc
      _ ≤ ∑ j : Fin m, ν.prob (fun a => ∃ v : V, F a j v) := by
        simpa only [Finset.mem_univ, true_and] using
          ν.prob_exists_finset_le Finset.univ (fun j a => ∃ v : V, F a j v)
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [Finset.mem_univ, true_and] using
          ν.prob_exists_finset_le Finset.univ (fun v a => F a j v)
  have hbad : ν.prob (fun a => ∃ j : Fin m, ∃ v : V, F a j v) < 1 := by
    apply lt_of_le_of_lt hunion
    calc
      _ ≤ ∑ _j : Fin m, ∑ _v : V, Real.exp (-((1 / 2 : ℝ) ^ m) / (6 * δ)) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun v _ => htail j v))
      _ = (m : ℝ) * Fintype.card V * Real.exp (-((1 / 2 : ℝ) ^ m) / (6 * δ)) := by simp; ring
      _ < 1 := hbudget
  have hgood : 0 < ν.prob (fun a => ¬ ∃ j : Fin m, ∃ v : V, F a j v) := by
    rw [ν.prob_compl]
    linarith
  obtain ⟨a, ha, _⟩ := ν.exists_pos_of_prob_pos _ hgood
  refine ⟨a, ?_⟩
  intro j v
  exact le_of_not_gt (fun hh => ha ⟨j, v, hh⟩)

end Erdos4.FGKMT
