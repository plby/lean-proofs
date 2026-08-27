import Arxiv.Arxiv2411_18291.NibbleFaceComparisons

/-! # Uniform average face loss before a comparison bound fails -/

namespace Arxiv2411_18291.NibbleComparisonParameters

theorem face_average_loss_le {k : ℕ} {a g D p₀ L : ℝ}
    (P : NibbleComparisonParameters k a g D p₀ L) {p n F d h : ℝ}
    (hp : p₀ ≤ p) (hp1 : p ≤ 1) (hn : 0 ≤ n) (hFn : F ≤ n) (hd : 0 ≤ d)
    (hhalf : nibbleCliqueMain k g D p / 2 ≤ h)
    (hface : d ≤ nibbleFaceUpper k a n F p) :
    d * (nibbleDegreeMain k D p + nibbleDegreeError k a D p) / h ≤
      4 * (1 + 128 * (k : ℝ)) * k * n / g := by
  have hk : 0 < k := by have h := P.rank; omega
  have hp0 := P.floor_pos.trans_le hp
  obtain ⟨hm, _, _, _, _, hum, _, hh₀, _, _, _⟩ := P.edge_conditions hp hp1
  have hh : 0 < h := (half_pos hh₀).trans_le hhalf
  let C := (1 + 128 * (k : ℝ)) * p * n
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hdC : d ≤ C := hface.trans
    (nibbleFaceUpper_le_density k hn hp0.le hFn (P.error_le_floor.trans hp))
  have hdegree : nibbleDegreeMain k D p + nibbleDegreeError k a D p ≤
      2 * nibbleDegreeMain k D p := by linarith only [hum]
  have hN : d * (nibbleDegreeMain k D p + nibbleDegreeError k a D p) ≤
      C * (2 * nibbleDegreeMain k D p) :=
    (mul_le_mul_of_nonneg_left hdegree hd).trans
      (mul_le_mul_of_nonneg_right hdC (mul_nonneg (by norm_num) hm.le))
  have hN' := mul_le_mul_of_nonneg_right hN hh₀.le
  have hh' := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hC hm.le)
  calc
    _ ≤ 4 * C * nibbleDegreeMain k D p / nibbleCliqueMain k g D p := by
      apply (div_le_div_iff₀ hh hh₀).mpr
      nlinarith only [hN', hh']
    _ = 4 * C * (nibbleDegreeMain k D p / nibbleCliqueMain k g D p) := by ring
    _ = _ := by
      rw [nibbleDegreeMain_clique_ratio hk P.graph_pos.ne' P.degree_pos.ne' hp0.ne']
      dsimp only [C]
      field_simp

end Arxiv2411_18291.NibbleComparisonParameters
