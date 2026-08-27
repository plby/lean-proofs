import Arxiv.Arxiv2411_18291.TypicalCliqueCount
import Arxiv.Arxiv2411_18291.GraphBoundedness

/-!
# A numerical reserve criterion

Choosing density between `z/8` and `z/2` leaves enough margin to obtain
strict `z`-boundedness, as required by the absorber. The small extra factor
`z` in the target clique count absorbs all fixed powers of two and factorials.
-/

noncomputable section

namespace Arxiv2411_18291

theorem reserve_count_scale {N d z : ℝ} (hN : 0 ≤ N) (hz : 0 < z)
    {K t : ℕ} (hK : 1 ≤ K) (hd : z / 8 ≤ d)
    (hsmall : z * 2 ^ t * 8 ^ (K - 1) * t.factorial ≤ 1) :
    z ^ K * N ^ t ≤ (N / 2) ^ t * d ^ (K - 1) / (t.factorial : ℝ) := by
  have hf : (0 : ℝ) < t.factorial := by exact_mod_cast Nat.factorial_pos t
  apply (le_div_iff₀ hf).mpr
  have hpow : z ^ K = z ^ (K - 1) * z := by
    rw [← pow_succ, Nat.sub_add_cancel hK]
  have hn : 0 ≤ (N / 2) ^ t * (z / 8) ^ (K - 1) := by positivity
  calc
    _ = ((N / 2) ^ t * (z / 8) ^ (K - 1)) *
        (z * 2 ^ t * 8 ^ (K - 1) * t.factorial) := by
      rw [hpow, div_pow, div_pow]
      field_simp
    _ ≤ (N / 2) ^ t * (z / 8) ^ (K - 1) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall hn
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hd _)
      (pow_nonneg (by positivity) _)

variable {V : Type*} [Fintype V] [DecidableEq V] {r q h : ℕ}

/-- A typical graph with these numerical bounds is a reserve. The conclusion
uses strict `z`-boundedness, stronger than the printed reserve lemma. -/
theorem reserve_of_typical {G : Hypergraph V (r + 1)} {c z : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hc : c ≤ 1 / 4)
    (hqr : r + 1 ≤ q) (hn : 0 < Fintype.card V) (hz : 0 < z)
    (hdlo : z / 8 ≤ density G) (hdhi : density G ≤ z / 2)
    (hsize : (q : ℝ) ≤ Fintype.card V * (z / 8) ^ q.choose (r + 1) / 4)
    (hsmall : z * 2 ^ (q - (r + 1)) * 8 ^ (q.choose (r + 1) - 1) *
      (q - (r + 1)).factorial ≤ 1) :
    IsGraphBounded G z ∧ ∀ e : Block V (r + 1),
      z ^ q.choose (r + 1) * (Fintype.card V : ℝ) ^ (q - (r + 1)) ≤
        (puncturedCliques G e q).card := by
  have hK : 1 ≤ q.choose (r + 1) := Nat.choose_pos hqr
  have hθ : (1 + c) * density G < z := by
    have hmul := mul_le_mul (show 1 + c ≤ 1 + 1 / 4 by linarith) hdhi
      (density_nonneg G) (by norm_num : (0 : ℝ) ≤ 1 + 1 / 4)
    linarith
  refine ⟨hT.graphBounded (hK.trans hqh) hn hθ, fun e => ?_⟩
  have hsize' : (q : ℝ) ≤ Fintype.card V * density G ^ q.choose (r + 1) / 4 := by
    exact hsize.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hdlo _) (Nat.cast_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 4))
  exact (reserve_count_scale (Nat.cast_nonneg _) hz hK hdlo hsmall).trans
    (hT.puncturedCliques_lower hqh hc hsize' hqr e)

end Arxiv2411_18291
