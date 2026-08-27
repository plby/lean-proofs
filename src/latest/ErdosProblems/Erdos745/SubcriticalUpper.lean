import ErdosProblems.Erdos745.ComponentUpper
import ErdosProblems.Erdos745.SupercriticalAssembly

/-! # Subcritical susceptibility and logarithmic upper bounds -/

open Filter
open scoped BigOperators Topology

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

theorem vertexPath_length_lt_card {n h : ℕ} {G : SimpleGraph (Fin n)}
    {S : Finset (Fin n)} {r v : Fin n} (hp : VertexPath G S r v h) : h < S.card := by
  induction h generalizing S r with
  | zero => exact Finset.card_pos.mpr ⟨r, hp.1⟩
  | succ h ih =>
    obtain ⟨hr, u, _, _, ht⟩ := hp
    have hh := ih ht
    rw [Finset.card_erase_of_mem hr] at hh
    omega

theorem not_vertexPathFrom_card {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n) :
    ¬ VertexPathFrom G Finset.univ r n := by
  rintro ⟨v, hv⟩
  have h := vertexPath_length_lt_card hv
  simp at h

theorem sum_probability_vertexPath_le_pow {n : ℕ} (hn : 0 < n)
    {lam : ℝ} (hlam : 0 ≤ lam) (hln : lam ≤ n) (h : ℕ)
    (S : Finset (Fin n)) (r : Fin n) :
    (∑ v : Fin n, probability lam n (fun G ↦ VertexPath G S r v h)) ≤ lam ^ h := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  induction h generalizing S r with
  | zero =>
    by_cases hr : r ∈ S
    · simp only [VertexPath, hr, true_and, probability_const, pow_zero]
      rw [Finset.sum_eq_single r]
      · simp
      · intro v _ hvr
        exact if_neg hvr.symm
      · simp
    · simp [VertexPath, hr]
  | succ h ih =>
    have hrow (v : Fin n) :
        probability lam n (fun G ↦ VertexPath G S r v (h + 1)) ≤
          ∑ u ∈ S.erase r, (lam / (n : ℝ)) *
            probability lam n (fun G ↦ VertexPath G (S.erase r) u v h) := by
      calc
        _ ≤ probability lam n (fun G ↦ ∃ u ∈ S.erase r,
            G.Adj r u ∧ VertexPath G (S.erase r) u v h) := probability_mono (fun _ hp ↦ hp.2)
        _ ≤ ∑ u ∈ S.erase r, probability lam n
            (fun G ↦ G.Adj r u ∧ VertexPath G (S.erase r) u v h) :=
          probability_exists_finset_le _ _ _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [probability_vertexPath_branch _ _ _ _ _ _ _
            (Finset.ne_of_mem_erase hu).symm, coe_edgeProbability hlam hn hln]
    calc
      _ ≤ ∑ v : Fin n, ∑ u ∈ S.erase r, (lam / (n : ℝ)) *
          probability lam n (fun G ↦ VertexPath G (S.erase r) u v h) :=
        Finset.sum_le_sum (fun v _ ↦ hrow v)
      _ = ∑ u ∈ S.erase r, (lam / (n : ℝ)) *
          ∑ v : Fin n, probability lam n (fun G ↦ VertexPath G (S.erase r) u v h) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ ∑ _u ∈ S.erase r, (lam / (n : ℝ)) * lam ^ h :=
        Finset.sum_le_sum (fun u _ ↦ mul_le_mul_of_nonneg_left (ih _ u) (by positivity))
      _ = ((S.erase r).card : ℝ) * (lam / (n : ℝ) * lam ^ h) := by simp
      _ ≤ (n : ℝ) * (lam / (n : ℝ) * lam ^ h) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (show (S.erase r).card ≤ n by simpa using Finset.card_le_univ (S.erase r))
      _ = lam ^ (h + 1) := by rw [pow_succ]; field_simp

theorem expectation_shortPathCount_le_geometric {n : ℕ} (hn : 0 < n)
    {lam : ℝ} (hlam : 0 ≤ lam) (hln : lam ≤ n) (h : ℕ)
    (S : Finset (Fin n)) (r : Fin n) :
    expectation lam n (fun G ↦ (shortPathCount G S r h : ℝ)) ≤
      ∑ j ∈ Finset.range h, lam ^ j := by
  have hcount : expectation lam n (fun G ↦ (shortPathCount G S r h : ℝ)) =
      ∑ v : Fin n, probability lam n (fun G ↦ ∃ j ∈ Finset.range h, VertexPath G S r v j) := by
    convert! expectation_card_filter lam n Finset.univ
      (fun v G ↦ ∃ j ∈ Finset.range h, VertexPath G S r v j) using 1
    congr 1
    funext G
    unfold shortPathCount
    congr 2
    ext v
    simp only [Finset.mem_filter]
  rw [hcount]
  calc
    _ ≤ ∑ v : Fin n, ∑ j ∈ Finset.range h,
        probability lam n (fun G ↦ VertexPath G S r v j) :=
      Finset.sum_le_sum (fun v _ ↦ probability_exists_finset_le _ _ _ _)
    _ = ∑ j ∈ Finset.range h, ∑ v : Fin n,
        probability lam n (fun G ↦ VertexPath G S r v j) := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun j _ ↦ sum_probability_vertexPath_le_pow hn hlam hln j S r)

theorem subcritical_root_mean_le {n : ℕ} (hn : 0 < n) {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) (r : Fin n) :
    expectation lam n (fun G ↦ (rootComponentOrder G r : ℝ)) ≤ 1 / (1 - lam) := by
  have hln : lam ≤ n := hlam1.le.trans (by exact_mod_cast hn)
  calc
    _ ≤ expectation lam n (fun G ↦ (shortPathCount G Finset.univ r n : ℝ)) := by
      apply expectation_mono
      intro G
      exact_mod_cast rootComponentOrder_le_shortPathCount G r (not_vertexPathFrom_card G r)
    _ ≤ ∑ j ∈ Finset.range n, lam ^ j :=
      expectation_shortPathCount_le_geometric hn hlam hln n Finset.univ r
    _ ≤ _ := by
      simpa only [Finset.range_eq_Ico, pow_zero] using
        (geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hlam hlam1)

theorem subcritical_large_vertex_mean_le {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    expectation lam n (fun G ↦ (largeComponentVertexCount G k : ℝ)) ≤
      (n : ℝ) / ((1 - lam) * k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcount : expectation lam n (fun G ↦ (largeComponentVertexCount G k : ℝ)) =
      ∑ r : Fin n, probability lam n (fun G ↦ k ≤ rootComponentOrder G r) := by
    convert! expectation_card_filter lam n Finset.univ
      (fun r G ↦ k ≤ rootComponentOrder G r) using 1
    congr 1
    funext G
    unfold largeComponentVertexCount
    congr 2
    ext r
    simp only [Finset.mem_filter]
  rw [hcount]
  calc
    _ ≤ ∑ _r : Fin n, (1 / (1 - lam)) / k := by
      apply Finset.sum_le_sum
      intro r _
      have hmark := probability_ge_le_expectation_div (lam := lam) hkR
        (fun G ↦ Nat.cast_nonneg (rootComponentOrder G r))
      have hprob : (fun G : SimpleGraph (Fin n) ↦ k ≤ rootComponentOrder G r) =
          (fun G ↦ (k : ℝ) ≤ (rootComponentOrder G r : ℝ)) := by
        funext G
        apply propext
        exact_mod_cast Iff.rfl
      rw [hprob]
      exact hmark.trans
        (div_le_div_of_nonneg_right (subcritical_root_mean_le hn hlam hlam1 r) hkR.le)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [div_div, mul_one_div]

theorem subcritical_secondLargest_tail {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    probability lam n (fun G ↦ k ≤ secondLargestComponentOrder G) ≤
      (n : ℝ) / ((1 - lam) * (k : ℝ) ^ 2) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    _ ≤ probability lam n (fun G ↦ (k : ℝ) ≤ (largeComponentVertexCount G k : ℝ)) := by
      apply probability_mono
      intro G hG
      exact_mod_cast le_largeComponentVertexCount_of_le_second G hk hG
    _ ≤ expectation lam n (fun G ↦ (largeComponentVertexCount G k : ℝ)) / k :=
      probability_ge_le_expectation_div hkR (fun _ ↦ Nat.cast_nonneg _)
    _ ≤ ((n : ℝ) / ((1 - lam) * k)) / k :=
      div_le_div_of_nonneg_right (subcritical_large_vertex_mean_le hn hk hlam hlam1) hkR.le
    _ = _ := by rw [div_div]; congr 1; ring

theorem subcritical_macroscopic_uniqueness {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) : MacroscopicUniqueness lam := by
  intro δ hδ
  have hden : 0 < 1 - lam := sub_pos.mpr hlam1
  have ht := tendsto_const_div_atTop_nhds_zero_nat (1 / ((1 - lam) * δ ^ 2))
  apply squeeze_zero' (Eventually.of_forall fun n ↦ probability_nonneg _ _ _) _ ht
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let k : ℕ := ⌈δ * (n : ℝ)⌉₊
  have hkn : δ * (n : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  have hkR : (0 : ℝ) < k := (mul_pos hδ hnR).trans_le hkn
  have hk : 0 < k := by exact_mod_cast hkR
  calc
    _ ≤ probability lam n (fun G ↦ k ≤ secondLargestComponentOrder G) := by
      apply probability_mono
      intro G hG
      exact Nat.ceil_le.mpr hG.le
    _ ≤ (n : ℝ) / ((1 - lam) * (k : ℝ) ^ 2) :=
      subcritical_secondLargest_tail (by omega) hk hlam hlam1
    _ ≤ (n : ℝ) / ((1 - lam) * (δ * n) ^ 2) := by
      apply div_le_div_of_nonneg_left hnR.le (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hkn 2) hden.le
    _ = _ := by field_simp

theorem subcritical_logarithmic_upper {lam A : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (hA : logarithmicConstant lam < A) :
    WithHighProbabilityAt lam (fun n G ↦ secondOrder n G ≤ A * Real.log (n : ℝ)) :=
  logarithmic_upper_of_macroscopic_uniqueness_of_ne_one hlam (ne_of_lt hlam1)
    (subcritical_macroscopic_uniqueness hlam.le hlam1) hA

end

end Erdos745
