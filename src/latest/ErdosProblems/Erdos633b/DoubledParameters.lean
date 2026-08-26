import ErdosProblems.Erdos633b.DoubledLayout
import Mathlib.Tactic.FieldSimp

/-! The actual side parameters satisfy every geometric layout hypothesis. -/

namespace Erdos633b.DoubledParameters

noncomputable def layout (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) : DoubledPartition.Layout := by
  have hb : 0 < b := ha.trans hab
  have hP : 0 < a + 2 * b := by linarith
  have hQ : 0 < 2 * a + b := by linarith
  have hZ : 0 < a + b := add_pos ha hb
  have hC : 0 < c ^ 2 := sq_pos_of_pos hc
  let u := a / (2 * a + b)
  let v := c ^ 2 / ((a + 2 * b) * (2 * a + b))
  let r := c ^ 2 / (b * (2 * a + b))
  let ε := 2 * a / (a + b)
  let μ := 2 * c ^ 2 / ((a + b) * (a + 2 * b))
  have hu : 0 < u := div_pos ha hQ
  have hv : 0 < v := div_pos hC (mul_pos hP hQ)
  have hr : 0 < r := div_pos hC (mul_pos hb hQ)
  have hr1 : r < 1 := by
    apply (div_lt_one (mul_pos hb hQ)).mpr
    nlinarith [mul_pos ha (sub_pos.mpr hab)]
  have hUV : u + v = 1 - b / (a + 2 * b) := by
    dsimp only [u, v]
    field_simp
    nlinarith only [hrel]
  have huv : u + v < 1 := by
    rw [hUV]
    linarith [div_pos hb hP]
  have hδ : DoubledPartition.delta u v r = a * c ^ 2 / (b * (a + 2 * b) * (2 * a + b)) := by
    dsimp only [DoubledPartition.delta]
    rw [hUV]
    dsimp only [r, v]
    field_simp
    ring
  have hδpos : 0 < DoubledPartition.delta u v r := by
    rw [hδ]
    exact div_pos (mul_pos ha hC) (mul_pos (mul_pos hb hP) hQ)
  have hε : 0 < ε := div_pos (mul_pos (by norm_num) ha) hZ
  have hε1 : ε < 1 := by
    apply (div_lt_one hZ).mpr
    linarith
  have hμ : 0 < μ := div_pos (mul_pos (by norm_num) hC) (mul_pos hZ hP)
  have hμ1 : μ < 1 := by
    apply (div_lt_one (mul_pos hZ hP)).mpr
    nlinarith [mul_pos ha (sub_pos.mpr hab)]
  have hdiag : u + r - 1 = a ^ 2 / (b * (2 * a + b)) := by
    dsimp only [u, r]
    field_simp
    nlinarith only [hrel]
  have hcut : (u + r - 1) * μ = ε * DoubledPartition.delta u v r := by
    rw [hdiag, hδ]
    dsimp only [ε, μ]
    field_simp
  exact { u := u
          v := v
          r := r
          ε := ε
          μ := μ
          u_pos := hu
          v_pos := hv
          r_pos := hr
          r_lt_one := hr1
          uv_lt_one := huv
          delta_pos := hδpos
          ε_pos := hε
          ε_lt_one := hε1
          μ_pos := hμ
          μ_lt_one := hμ1
          cut := hcut }

end Erdos633b.DoubledParameters
