import ErdosProblems.Erdos4.FGKMTNormalizerMoments

/-!
# The actual edge-selection law in one covering round

If the reweighting normalizer is close to one, normalize the surviving
edge weights. Otherwise choose the empty edge. All positive-probability
outcomes are legal old edges or empty, and are contained in the current
survivor set.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def selectLaw (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) (t : ℝ) (W : Finset V) : FiniteLaw (Finset V) :=
  if |normalizer μ p W - 1| ≤ t then
    FiniteLaw.normalize (reweighted μ p W) (reweighted_nonneg μ p hp W) ∅
  else FiniteLaw.dirac ∅

theorem good_normalizer_pos (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {t : ℝ} (ht : t < 1) {W : Finset V} (hgood : |normalizer μ p W - 1| ≤ t) :
    0 < normalizer μ p W := by
  have hh := (abs_le.mp hgood).1
  linarith

theorem selectLaw_support (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) (t : ℝ) (W e : Finset V)
    (he : 0 < (selectLaw μ p hp t W).weight e) :
    e ⊆ W ∧ (e = ∅ ∨ 0 < μ.weight e) := by
  classical
  by_cases hgood : |normalizer μ p W - 1| ≤ t
  · rw [selectLaw, if_pos hgood] at he
    obtain heq | hraw := FiniteLaw.normalize_support (reweighted μ p W)
      (reweighted_nonneg μ p hp W) ∅ e he
    · subst e
      exact ⟨Finset.empty_subset W, Or.inl rfl⟩
    · by_cases hsub : e ⊆ W
      · refine ⟨hsub, Or.inr ?_⟩
        rw [reweighted, if_pos hsub] at hraw
        have hh := (div_pos_iff.mp hraw).resolve_right
          (fun hh => (not_lt_of_ge (setProduct_pos p hp e).le) hh.2)
        exact hh.1
      · simp only [reweighted, if_neg hsub] at hraw
        linarith
  · rw [selectLaw, if_neg hgood] at he
    by_cases heq : e = ∅
    · subst e
      exact ⟨Finset.empty_subset W, Or.inl rfl⟩
    · simp only [FiniteLaw.dirac, if_neg heq] at he
      linarith

noncomputable def eventNumerator (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    (W : Finset V) (E : Finset V → Prop) : ℝ := by
  classical
  exact ∑ e, if E e then reweighted μ p W e else 0

theorem selectLaw_event (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) {t : ℝ} (ht : t < 1) (W : Finset V)
    (E : Finset V → Prop) (hE : ¬E ∅) :
    (selectLaw μ p hp t W).prob E =
      if |normalizer μ p W - 1| ≤ t then eventNumerator μ p W E / normalizer μ p W else 0 := by
  classical
  by_cases hgood : |normalizer μ p W - 1| ≤ t
  · rw [selectLaw, if_pos hgood, if_pos hgood]
    have hZ : (∑ e, reweighted μ p W e) ≠ 0 := (good_normalizer_pos μ p ht hgood).ne'
    unfold FiniteLaw.prob eventNumerator
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _he
    rw [FiniteLaw.normalize_weight _ _ _ _ hZ]
    by_cases he : E e <;> simp [he, normalizer]
  · rw [selectLaw, if_neg hgood, if_neg hgood, FiniteLaw.prob_eq_mean, FiniteLaw.mean_dirac]
    exact if_neg hE

theorem eventNumerator_nonneg (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) (W : Finset V) (E : Finset V → Prop) :
    0 ≤ eventNumerator μ p W E := by
  classical
  unfold eventNumerator
  apply Finset.sum_nonneg
  intro e _he
  split_ifs
  · exact reweighted_nonneg μ p hp W e
  · rfl

theorem eventNumerator_le (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {κ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hp : ∀ v, κ ≤ p v)
    (hsize : ∀ e, 0 < μ.weight e → e.card ≤ r) (W : Finset V) (E : Finset V → Prop) :
    eventNumerator μ p W E ≤ μ.prob E / κ ^ r := by
  classical
  unfold eventNumerator FiniteLaw.prob
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro e _he
  by_cases hevent : E e
  · simp only [if_pos hevent]
    by_cases hw : μ.weight e = 0
    · simp [reweighted, hw]
    · have hpos : 0 < μ.weight e := lt_of_le_of_ne (μ.nonneg e) (Ne.symm hw)
      by_cases hsub : e ⊆ W
      · rw [reweighted, if_pos hsub]
        exact div_le_div_of_nonneg_left (μ.nonneg e) (pow_pos hκ0 r)
          (setProduct_lower p hκ0.le hκ1 hp (hsize e hpos))
      · rw [reweighted, if_neg hsub]
        positivity
  · simp only [if_neg hevent, zero_div, le_refl]

end Erdos4.FGKMT
