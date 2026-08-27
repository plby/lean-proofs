import ErdosProblems.Erdos4.FGKMTLawOperations

/-!
# Survival products and reweighted edge normalizers

These are exact identities for one round of the probabilistic covering
induction. Edge sizes may vary. The survival-product correction is kept
explicit, so conditioning does not preferentially discard large edges.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def setProduct (p : V → ℝ) (e : Finset V) : ℝ := ∏ v ∈ e, p v

omit [Fintype V] [DecidableEq V] in
theorem setProduct_empty (p : V → ℝ) : setProduct p ∅ = 1 := by simp [setProduct]

omit [Fintype V] [DecidableEq V] in
theorem setProduct_pos (p : V → ℝ) (hp : ∀ v, 0 < p v) (e : Finset V) :
    0 < setProduct p e := Finset.prod_pos (fun v _hv => hp v)

omit [Fintype V] [DecidableEq V] in
theorem setProduct_le_one (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1)
    (e : Finset V) : setProduct p e ≤ 1 :=
  Finset.prod_le_one (fun v _hv => hp0 v) (fun v _hv => hp1 v)

omit [Fintype V] in
theorem setProduct_union_inter (p : V → ℝ) (e f : Finset V) :
    setProduct p (e ∪ f) * setProduct p (e ∩ f) = setProduct p e * setProduct p f :=
  Finset.prod_union_inter

omit [Fintype V] [DecidableEq V] in
theorem setProduct_lower (p : V → ℝ) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hp : ∀ v, κ ≤ p v) {e : Finset V} {r : ℕ} (he : e.card ≤ r) :
    κ ^ r ≤ setProduct p e := by
  calc
    _ ≤ κ ^ e.card := pow_le_pow_of_le_one hκ0 hκ1 he
    _ = ∏ _v ∈ e, κ := (Finset.prod_const κ).symm
    _ ≤ _ := Finset.prod_le_prod (fun _v _hv => hκ0) (fun v _hv => hp v)

omit [Fintype V] in
theorem union_denominator (p : V → ℝ) (e f : Finset V) (z : ℝ) :
    z / (setProduct p e * setProduct p f) =
      (z / setProduct p (e ∪ f)) / setProduct p (e ∩ f) := by
  rw [div_div, setProduct_union_inter]

noncomputable def survival (ν : FiniteLaw (Finset V)) (e : Finset V) : ℝ :=
  ν.prob (fun W => e ⊆ W)

def SurvivalAccurate (ν : FiniteLaw (Finset V)) (p : V → ℝ) (A : ℕ) (ε : ℝ) : Prop :=
  ∀ e : Finset V, e.card ≤ A → |survival ν e / setProduct p e - 1| ≤ ε

noncomputable def reweighted (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    (W e : Finset V) : ℝ := if e ⊆ W then μ.weight e / setProduct p e else 0

noncomputable def normalizer (μ : FiniteLaw (Finset V)) (p : V → ℝ) (W : Finset V) : ℝ :=
  ∑ e, reweighted μ p W e

theorem reweighted_nonneg (μ : FiniteLaw (Finset V)) (p : V → ℝ) (hp : ∀ v, 0 < p v)
    (W e : Finset V) : 0 ≤ reweighted μ p W e := by
  unfold reweighted
  split_ifs
  · exact div_nonneg (μ.nonneg e) (setProduct_pos p hp e).le
  · rfl

theorem normalizer_nonneg (μ : FiniteLaw (Finset V)) (p : V → ℝ) (hp : ∀ v, 0 < p v)
    (W : Finset V) : 0 ≤ normalizer μ p W :=
  Finset.sum_nonneg (fun e _he => reweighted_nonneg μ p hp W e)

theorem mean_reweighted (ν μ : FiniteLaw (Finset V)) (p : V → ℝ) (e : Finset V) :
    ν.mean (fun W => reweighted μ p W e) = μ.weight e * (survival ν e / setProduct p e) := by
  classical
  have hh : ν.mean (fun W => reweighted μ p W e) =
      ν.mean (fun W => (μ.weight e / setProduct p e) * (if e ⊆ W then 1 else 0)) := by
    apply ν.mean_congr
    intro W
    by_cases he : e ⊆ W <;> simp [reweighted, he]
  rw [hh, FiniteLaw.mean_const_mul, ← FiniteLaw.prob_eq_mean]
  unfold survival
  ring

theorem mean_normalizer (ν μ : FiniteLaw (Finset V)) (p : V → ℝ) :
    ν.mean (normalizer μ p) = μ.mean (fun e => survival ν e / setProduct p e) := by
  unfold normalizer
  rw [FiniteLaw.mean_finset_sum]
  change (∑ e : Finset V, ν.mean (fun W => reweighted μ p W e)) =
    ∑ e : Finset V, μ.weight e * (survival ν e / setProduct p e)
  exact Finset.sum_congr rfl (fun e _he => mean_reweighted ν μ p e)

open Classical in
theorem reweighted_mul (μ : FiniteLaw (Finset V)) (p : V → ℝ) (W e f : Finset V) :
    reweighted μ p W e * reweighted μ p W f =
      (μ.weight e * μ.weight f / (setProduct p e * setProduct p f)) *
        (if e ∪ f ⊆ W then 1 else 0) := by
  by_cases he : e ⊆ W <;> by_cases hf : f ⊆ W <;>
    simp only [reweighted, Finset.union_subset_iff, he, hf, and_self, and_false, false_and,
      if_true, if_false, mul_one, mul_zero, zero_mul]
  ring

theorem mean_normalizer_sq (ν μ : FiniteLaw (Finset V)) (p : V → ℝ) :
    ν.mean (fun W => normalizer μ p W ^ 2) =
      μ.mean (fun e => μ.mean (fun f =>
        survival ν (e ∪ f) / (setProduct p e * setProduct p f))) := by
  classical
  have hpoint (W : Finset V) : normalizer μ p W ^ 2 =
      ∑ e : Finset V, ∑ f : Finset V,
        (μ.weight e * μ.weight f / (setProduct p e * setProduct p f)) *
          (if e ∪ f ⊆ W then 1 else 0) := by
    rw [pow_two, normalizer, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun e _he => Finset.sum_congr rfl
      (fun f _hf => reweighted_mul μ p W e f))
  calc
    _ = ν.mean (fun W => ∑ e : Finset V, ∑ f : Finset V,
        (μ.weight e * μ.weight f / (setProduct p e * setProduct p f)) *
          (if e ∪ f ⊆ W then 1 else 0)) := ν.mean_congr hpoint
    _ = ∑ e : Finset V, ∑ f : Finset V,
        (μ.weight e * μ.weight f / (setProduct p e * setProduct p f)) * survival ν (e ∪ f) := by
      rw [FiniteLaw.mean_finset_sum]
      apply Finset.sum_congr rfl
      intro e _he
      rw [FiniteLaw.mean_finset_sum]
      apply Finset.sum_congr rfl
      intro f _hf
      rw [FiniteLaw.mean_const_mul, ← FiniteLaw.prob_eq_mean]
      rfl
    _ = _ := by
      unfold FiniteLaw.mean
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      apply Finset.sum_congr rfl
      intro f _hf
      ring

end Erdos4.FGKMT
