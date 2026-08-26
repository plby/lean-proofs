import ErdosProblems.Erdos421.DyadicDirichlet

/-! # A Halász estimate for full finite Dirichlet polynomials -/

namespace Erdos421

theorem dirichletBlock_halasz_energy_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (S : Finset ℕ) (c : ℕ → ℂ) (t : ℕ → ℝ) {A B V G : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 < V) (hlarge : ∀ i ∈ S, V ≤ ‖dirichletBlock M N c (t i)‖)
    (henergy : coefficientEnergy N c ≤ G) :
    (S.card : ℝ) ≤ 10240 * M * Real.log (M + 2 : ℝ) *
      (G / V ^ 2 + 1280 ^ 2 * G ^ 3 * (B - A) / V ^ 6) := by
  have hE := coefficientEnergy_nonneg N c
  have hG := hE.trans henergy
  have hT := sub_nonneg.mpr hAB
  have hlog : 0 ≤ Real.log (M + 2 : ℝ) :=
    Real.log_nonneg (by have := (Nat.cast_nonneg M : (0 : ℝ) ≤ M); linarith)
  refine (dirichletBlock_halasz_log_bound hM hN S c t hAB ht hsep hV hlarge).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  gcongr

theorem finite_dirichlet_halasz_energy_bound {K : ℕ} (hK : 0 < K)
    (S : Finset ℕ) (c : ℕ → ℂ) (t : ℕ → ℝ) {A B V G : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 < V)
    (hlarge : ∀ i ∈ S, V ≤ ‖exponentialSum (Finset.Ico 1 (2 ^ K)) c (fun n ↦ Real.log n) (t i)‖)
    (henergy : (∑ n ∈ Finset.Ico 1 (2 ^ K), ‖c n‖ ^ 2) ≤ G) :
    (S.card : ℝ) ≤ 10240 * K * (2 ^ K : ℕ) * Real.log ((2 ^ K : ℕ) + 2 : ℝ) *
      (G / (V / K) ^ 2 + 1280 ^ 2 * G ^ 3 * (B - A) / (V / K) ^ 6) := by
  classical
  let E : ℕ → Finset ℕ := fun j ↦ S.filter fun i ↦
    V / K ≤ ‖dirichletBlock (2 ^ j) (2 ^ j) (fun n ↦ c (2 ^ j + n)) (t i)‖
  have hcover : S ⊆ (Finset.range K).biUnion E := by
    intro i hi
    obtain ⟨j, hj, hbig⟩ := exists_large_dyadic_block c hK (hlarge i hi)
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, Finset.mem_filter.mpr ⟨hi, hbig⟩⟩
  have hG : 0 ≤ G := (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)).trans henergy
  have hT : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hthreshold : 0 < V / K := div_pos hV hKpos
  let Q := G / (V / K) ^ 2 + 1280 ^ 2 * G ^ 3 * (B - A) / (V / K) ^ 6
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hcard : ∀ j ∈ Finset.range K,
      ((E j).card : ℝ) ≤ 10240 * (2 ^ K : ℕ) * Real.log ((2 ^ K : ℕ) + 2 : ℝ) * Q := by
    intro j hj
    have hjK : j < K := Finset.mem_range.mp hj
    have hlocalEnergy : coefficientEnergy (2 ^ j) (fun n ↦ c (2 ^ j + n)) ≤ G :=
      (dyadic_coefficientEnergy_le c hjK).trans henergy
    have h := dirichletBlock_halasz_energy_bound (M := 2 ^ j) (N := 2 ^ j)
      (by positivity) le_rfl (E j) (fun n ↦ c (2 ^ j + n)) t hAB
      (fun i hi ↦ ht i (Finset.mem_filter.mp hi).1)
      (fun i hi l hl hil ↦ hsep i (Finset.mem_filter.mp hi).1 l (Finset.mem_filter.mp hl).1 hil)
      hthreshold (fun i hi ↦ (Finset.mem_filter.mp hi).2) hlocalEnergy
    change ((E j).card : ℝ) ≤ 10240 * (2 ^ j : ℕ) * Real.log ((2 ^ j : ℕ) + 2 : ℝ) * Q at h
    have hsize : ((2 ^ j : ℕ) : ℝ) ≤ (2 ^ K : ℕ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hjK.le
    have hlogj : 0 ≤ Real.log ((2 ^ j : ℕ) + 2 : ℝ) :=
      Real.log_nonneg (by have := (Nat.cast_nonneg (2 ^ j) : (0 : ℝ) ≤ (2 ^ j : ℕ)); linarith)
    have hlog : Real.log ((2 ^ j : ℕ) + 2 : ℝ) ≤ Real.log ((2 ^ K : ℕ) + 2 : ℝ) :=
      Real.log_le_log (by positivity) (by linarith)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hQ)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsize (by norm_num)) hlog hlogj (by positivity)
  calc
    (S.card : ℝ) ≤ ∑ j ∈ Finset.range K, ((E j).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range K,
        10240 * (2 ^ K : ℕ) * Real.log ((2 ^ K : ℕ) + 2 : ℝ) * Q :=
      Finset.sum_le_sum hcard
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Erdos421
