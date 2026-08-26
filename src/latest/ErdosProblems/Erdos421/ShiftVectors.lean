import ErdosProblems.Erdos421.DirichletGram

/-! # Finite shifted vectors and their exact correlations -/

namespace Erdos421

def shiftedSequence (N : ℕ) (u : ℕ → ℂ) (h n : ℕ) : ℂ :=
  if h ≤ n ∧ n < h + N then u (n - h) else 0

theorem sum_range_Ico_indicator {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    {a b L : ℕ} (hb : b ≤ L) :
    (∑ n ∈ Finset.range L, if a ≤ n ∧ n < b then f n else 0) =
      ∑ n ∈ Finset.Ico a b, f n := by
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

theorem sum_shiftedSequence (N H : ℕ) (u : ℕ → ℂ) {h : ℕ} (hh : h ≤ H) :
    (∑ n ∈ Finset.range (N + H), shiftedSequence N u h n) =
      ∑ n ∈ Finset.range N, u n := by
  unfold shiftedSequence
  rw [sum_range_Ico_indicator (fun n ↦ u (n - h)) (by omega),
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]

theorem shiftedSequence_inner_eq (N : ℕ) (u : ℕ → ℂ) {i j : ℕ} (hij : i ≤ j) (n : ℕ) :
    inner ℂ (shiftedSequence N u i n) (shiftedSequence N u j n) =
      if j ≤ n ∧ n < i + N then inner ℂ (u (n - i)) (u (n - j)) else 0 := by
  unfold shiftedSequence
  by_cases hi : i ≤ n ∧ n < i + N
  · by_cases hj : j ≤ n ∧ n < j + N
    · have hboth : j ≤ n ∧ n < i + N := ⟨hj.1, hi.2⟩
      simp only [if_pos hi, if_pos hj, if_pos hboth]
    · have hnot : ¬ (j ≤ n ∧ n < i + N) := by omega
      simp only [if_pos hi, if_neg hj, if_neg hnot, inner_zero_right]
  · have hnot : ¬ (j ≤ n ∧ n < i + N) := by omega
    simp only [if_neg hi, if_neg hnot, inner_zero_left]

theorem sum_shiftedSequence_inner (N H : ℕ) (u : ℕ → ℂ) {i j : ℕ}
    (hij : i ≤ j) (hiH : i ≤ H) :
    (∑ n ∈ Finset.range (N + H),
      inner ℂ (shiftedSequence N u i n) (shiftedSequence N u j n)) =
        ∑ n ∈ Finset.range (N - (j - i)), inner ℂ (u (n + (j - i))) (u n) := by
  simp_rw [shiftedSequence_inner_eq N u hij]
  rw [sum_range_Ico_indicator _ (by omega), Finset.sum_Ico_eq_sum_range]
  have hlen : i + N - j = N - (j - i) := by omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro n _
  have hleft : j + n - i = n + (j - i) := by omega
  rw [hleft, Nat.add_sub_cancel_left]

noncomputable def shiftedVector (N H : ℕ) (u : ℕ → ℂ) (h : ℕ) :
    EuclideanSpace ℂ (Fin (N + H)) := WithLp.toLp 2 (fun n ↦ shiftedSequence N u h n)

noncomputable def constantVector (L : ℕ) : EuclideanSpace ℂ (Fin L) :=
  WithLp.toLp 2 (fun _ ↦ 1)

theorem constantVector_norm_sq (L : ℕ) : ‖constantVector L‖ ^ 2 = L := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ _n : Fin L, ‖(1 : ℂ)‖ ^ 2) = L
  simp

theorem constantVector_inner_shiftedVector (N H : ℕ) (u : ℕ → ℂ) {h : ℕ} (hh : h ≤ H) :
    inner ℂ (constantVector (N + H)) (shiftedVector N H u h) =
      ∑ n ∈ Finset.range N, u n := by
  rw [PiLp.inner_apply]
  change (∑ n : Fin (N + H), inner ℂ (1 : ℂ) (shiftedSequence N u h n)) = _
  simp only [RCLike.inner_apply, map_one, mul_one]
  rw [Fin.sum_univ_eq_sum_range (fun n ↦ shiftedSequence N u h n)]
  exact sum_shiftedSequence N H u hh

theorem shiftedVector_inner_constantVector_norm (N H : ℕ) (u : ℕ → ℂ) {h : ℕ} (hh : h ≤ H) :
    ‖inner ℂ (shiftedVector N H u h) (constantVector (N + H))‖ =
      ‖∑ n ∈ Finset.range N, u n‖ := by
  rw [← inner_conj_symm, Complex.norm_conj, constantVector_inner_shiftedVector N H u hh]

theorem shiftedVector_inner (N H : ℕ) (u : ℕ → ℂ) {i j : ℕ}
    (hij : i ≤ j) (hiH : i ≤ H) :
    inner ℂ (shiftedVector N H u i) (shiftedVector N H u j) =
      ∑ n ∈ Finset.range (N - (j - i)), inner ℂ (u (n + (j - i))) (u n) := by
  rw [PiLp.inner_apply]
  change (∑ n : Fin (N + H),
    inner ℂ (shiftedSequence N u i n) (shiftedSequence N u j n)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun n ↦ inner ℂ (shiftedSequence N u i n) (shiftedSequence N u j n))]
  exact sum_shiftedSequence_inner N H u hij hiH

theorem shiftedVector_inner_self_bound (N H : ℕ) (u : ℕ → ℂ)
    (hu : ∀ n < N, ‖u n‖ ≤ 1) {h : ℕ} (hh : h ≤ H) :
    ‖inner ℂ (shiftedVector N H u h) (shiftedVector N H u h)‖ ≤ N := by
  rw [shiftedVector_inner N H u le_rfl hh]
  simp only [Nat.sub_self, Nat.sub_zero, Nat.add_zero]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖inner ℂ (u n) (u n)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hbound := norm_inner_le_norm (𝕜 := ℂ) (u n) (u n)
      have hun := hu n (Finset.mem_range.mp hn)
      nlinarith [norm_nonneg (u n)]
    _ = _ := by simp

end Erdos421
