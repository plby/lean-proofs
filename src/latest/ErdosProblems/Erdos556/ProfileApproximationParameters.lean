import ErdosProblems.Erdos556.ProfileNormalization

/-! Uniform choices of the decomposition error and the large-order threshold. -/

namespace Erdos556

open SimpleGraph Finset

theorem exists_profile_approximation_parameters (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (c : ThreeColouring V) (n : ℕ), n₀ ≤ n → Fintype.card V = 4 * n - 3 →
      (∀ i, ¬ cycleGraph n ⊑ c.graph i) →
      ∀ h : ThreeColourDecomposition c (ε * (Fintype.card V : ℝ) ^ 2)
        ((n : ℝ) / 2 + ε * Fintype.card V), ApproxCubeWeight (h.profileWeight n) δ := by
  let t : ℝ := min δ (min (δ ^ 2) 1)
  have ht : 0 < t := lt_min hδ (lt_min (sq_pos_of_pos hδ) zero_lt_one)
  have htδ : t ≤ δ := min_le_left _ _
  have htδsq : t ≤ δ ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
  let ε : ℝ := t / 100000
  have hε : 0 < ε := div_pos ht (by norm_num)
  have hεδ : ε ≤ δ := by
    have hεt : ε ≤ t := by dsimp only [ε]; nlinarith
    exact hεt.trans htδ
  obtain ⟨m, hm⟩ := exists_nat_ge (100000 / t)
  refine ⟨ε, hε, hεδ, max 8 m, ?_⟩
  intro V _ _ c n hn hN hno h
  have hn8 : 8 ≤ n := (le_max_left _ _).trans hn
  have hmn : m ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htn : 100000 ≤ t * n := by
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hh := (div_le_iff₀ ht).mp (hm.trans hmnR)
    nlinarith
  have hNR : (Fintype.card V : ℝ) = 4 * n - 3 := by
    have hh : Fintype.card V + 3 = 4 * n := by omega
    have hhR : (Fintype.card V : ℝ) + 3 = 4 * n := by exact_mod_cast hh
    linarith
  have hNnonneg : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hNle : (Fintype.card V : ℝ) ≤ 4 * n := by linarith
  have hNsq : (Fintype.card V : ℝ) ^ 2 ≤ 16 * (n : ℝ) ^ 2 := by nlinarith
  have heq : 100000 * ε = t := by dsimp only [ε]; ring
  have hlarge : 100000 * (n : ℝ) ≤ t * (n : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right htn hnpos.le]
  have hcommon : (Fintype.card V : ℝ) + 48 * (ε * (Fintype.card V : ℝ) ^ 2) ≤
      t * (n : ℝ) ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hNsq hε.le
    have heqscaled : 100000 * ε * (n : ℝ) ^ 2 = t * (n : ℝ) ^ 2 := by rw [heq]
    nlinarith [mul_nonneg ht.le (sq_nonneg (n : ℝ))]
  have htδn := mul_le_mul_of_nonneg_right htδ (sq_nonneg (n : ℝ))
  have htδsqn := mul_le_mul_of_nonneg_right htδsq (sq_nonneg (n : ℝ))
  have hE : 0 ≤ ε * (Fintype.card V : ℝ) ^ 2 := mul_nonneg hε.le (sq_nonneg _)
  apply h.approximate_profileWeight n hn8 hno δ hδ.le
  · rw [hNR]
    have habs : |4 * (n : ℝ) - 3 - 4 * n| = 3 := by ring_nf; norm_num
    rw [habs]
    have hh := mul_le_mul_of_nonneg_right htδ hnpos.le
    linarith
  · linarith
  · linarith
  · linarith
  · have hW := h.free_coordinate_mass_le
    have hmul := mul_le_mul_of_nonneg_left hW (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ε) hNnonneg)
    nlinarith

#print axioms exists_profile_approximation_parameters

end Erdos556
