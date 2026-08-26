import ErdosProblems.Erdos421.DyadicProductWindows
import ErdosProblems.Erdos421.LogarithmicPrimeMinorant

/-! # Only product rectangles at the observation scale contribute -/

namespace Erdos421

theorem scaledProductWindow_nonzero_factors (S T : Finset ℕ) (a b : ℕ → ℂ)
    (hS : ∀ m ∈ S, 0 < m) (hT : ∀ n ∈ T, 0 < n) {δ y : ℝ} (hδ : 0 < δ)
    (hne : scaledProductWindow S T a b 1 oneSidedSchwartzWindow δ y ≠ 0) :
    ∃ m ∈ S, ∃ n ∈ T, Real.exp y < (m * n : ℕ) ∧ (m * n : ℕ) < Real.exp (y + δ) := by
  rw [scaledProductWindow_sigma_one S T a b hS hT] at hne
  obtain ⟨m, hm, hrow⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrow
  exact ⟨m, hm, n, hn, logarithmicIntegerWeight_nonzero hδ
    (Nat.mul_pos (hS m hm) (hT n hn)) (mul_ne_zero_iff.mp hterm).2⟩

theorem scaledProductWindow_product_scale (S T : Finset ℕ) (a b : ℕ → ℂ)
    {M H : ℕ} (hM : 0 < M) (hH : 0 < H)
    (hS : ∀ m ∈ S, M ≤ m ∧ m ≤ 2 * M) (hT : ∀ n ∈ T, H ≤ n ∧ n ≤ 2 * H)
    {δ y : ℝ} (hδ : 0 < δ)
    (hne : scaledProductWindow S T a b 1 oneSidedSchwartzWindow δ y ≠ 0) :
    Real.exp y < 4 * (M * H : ℕ) ∧ (M * H : ℕ) < Real.exp (y + δ) := by
  obtain ⟨m, hm, n, hn, hlo, hhi⟩ := scaledProductWindow_nonzero_factors S T a b
    (fun m hm ↦ hM.trans_le (hS m hm).1) (fun n hn ↦ hH.trans_le (hT n hn).1) hδ hne
  have hlow : M * H ≤ m * n := Nat.mul_le_mul (hS m hm).1 (hT n hn).1
  have hupp : m * n ≤ 4 * (M * H) := by
    apply (Nat.mul_le_mul (hS m hm).2 (hT n hn).2).trans_eq
    ring
  exact ⟨hlo.trans_le (by exact_mod_cast hupp), (by exact_mod_cast hlow :
    ((M * H : ℕ) : ℝ) ≤ (m * n : ℕ)).trans_lt hhi⟩

theorem scaledProductWindow_eq_zero_of_inactive (S T : Finset ℕ) (a b : ℕ → ℂ)
    {M H : ℕ} (hM : 0 < M) (hH : 0 < H)
    (hS : ∀ m ∈ S, M ≤ m ∧ m ≤ 2 * M) (hT : ∀ n ∈ T, H ≤ n ∧ n ≤ 2 * H)
    {X δ y : ℝ} (hX : 0 < X) (hδ : 0 < δ) (hδmax : δ ≤ Real.log (3 / 2))
    (hylo : Real.log X ≤ y) (hyhi : y ≤ Real.log (2 * X))
    (hinactive : 4 * (M * H : ℕ) ≤ X ∨ 3 * X ≤ (M * H : ℕ)) :
    scaledProductWindow S T a b 1 oneSidedSchwartzWindow δ y = 0 := by
  by_contra hne
  obtain ⟨hlo, hhi⟩ := scaledProductWindow_product_scale S T a b hM hH hS hT hδ hne
  have hleft : X ≤ Real.exp y := by
    simpa only [Real.exp_log hX] using Real.exp_le_exp.mpr hylo
  have hright : Real.exp (y + δ) ≤ 3 * X := by
    calc
      _ ≤ Real.exp (Real.log (2 * X) + Real.log (3 / 2)) :=
        Real.exp_le_exp.mpr (add_le_add hyhi hδmax)
      _ = _ := by
        rw [Real.exp_add, Real.exp_log (by positivity : 0 < 2 * X),
          Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
        ring
  rcases hinactive with hinactive | hinactive <;> linarith

end Erdos421
