import Arxiv.Arxiv2411_18291.NormalizedChooseMonotonicity

/-! # Preserving clique-degree and leave scales under rank-one restriction -/

noncomputable section

namespace Arxiv2411_18291

theorem rankOne_restricted_degree_scale {m n d : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (hd : 0 < d) (hdm : d ≤ m) {τ : ℝ} (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ) :
    ∃ τ' : ℝ, (m : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ' ∧
      τ' * (m.choose d : ℝ) = τ * (n.choose d : ℝ) := by
  have hchoose : (0 : ℝ) < m.choose d := by exact_mod_cast Nat.choose_pos hdm
  have hscaled : (m : ℝ) ^ (-(1 / 3 : ℝ)) * (m.choose d : ℝ) ≤
      τ * (n.choose d : ℝ) :=
    (normalized_choose_mono hm hmn hd (by norm_num : (1 / 3 : ℝ) ≤ 1)).trans
      (mul_le_mul_of_nonneg_right hτ (Nat.cast_nonneg _))
  refine ⟨τ * (n.choose d : ℝ) / (m.choose d : ℝ),
    (le_div_iff₀ hchoose).mpr hscaled, ?_⟩
  exact div_mul_cancel₀ _ hchoose.ne'

theorem rankOne_restricted_degree_error {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {ε D x : ℝ} (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (h : |x - D| ≤ (n : ℝ) ^ (-ε) * D) :
    |x - D| ≤ (m : ℝ) ^ (-ε) * D := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  exact h.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hm0 (by exact_mod_cast hmn) (neg_nonpos.mpr hε)) hD)

theorem rankOne_leave_scale_mono {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {β : ℝ} (hβ : β ≤ 1) :
    (m : ℝ) ^ (-β) * m ≤ (n : ℝ) ^ (-β) * n := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hm.trans_le hmn
  have heq (x : ℝ) (hx : 0 < x) : x ^ (-β) * x = x ^ (1 - β) := by
    rw [show 1 - β = -β + 1 by ring, Real.rpow_add hx, Real.rpow_one]
  rw [heq _ hm0, heq _ hn0]
  exact Real.rpow_le_rpow hm0.le (by exact_mod_cast hmn) (by linarith only [hβ])

end Arxiv2411_18291
