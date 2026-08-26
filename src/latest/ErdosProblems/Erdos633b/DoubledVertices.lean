import ErdosProblems.Erdos633b.DoubledLayout
import Mathlib.Data.Fin.VecNotation

/-! Every vertex of each proposed triangular piece lies in its closed region. -/

namespace Erdos633b.DoubledPartition.Layout

theorem abd_vertices (L : Layout) (i : Fin 3) :
    closed L.u L.v L.r L.μ L.height (![0, 1, L.u] i) (![0, 0, L.v] i) .abd := by
  fin_cases i
  · change closed L.u L.v L.r L.μ L.height 0 0 .abd
    simp [closed, outer, constraints, ad, bd, L.v_pos.le]
  · change closed L.u L.v L.r L.μ L.height 1 0 .abd
    simp [closed, outer, constraints, ad, bd, L.v_pos.le]
  · change closed L.u L.v L.r L.μ L.height L.u L.v .abd
    refine ⟨L.outer_D, ?_⟩
    change 0 ≤ ad L.u L.v L.u L.v ∧ bd L.u L.v L.u L.v ≤ 0
    have ha : ad L.u L.v L.u L.v = 0 := by dsimp only [ad]; ring
    have hb : bd L.u L.v L.u L.v = 0 := by dsimp only [bd]; ring
    rw [ha, hb]
    exact ⟨le_rfl, le_rfl⟩

theorem bdg_vertices (L : Layout) (i : Fin 3) :
    closed L.u L.v L.r L.μ L.height (![1, L.u, 1 - L.r] i) (![0, L.v, L.r] i) .bdg := by
  have hA : 0 ≤ L.r * (1 - L.u - L.v) :=
    mul_nonneg L.r_pos.le (by linarith [L.uv_lt_one])
  fin_cases i
  · change closed L.u L.v L.r L.μ L.height 1 0 .bdg
    refine ⟨by norm_num [outer], ?_⟩
    change 0 ≤ bd L.u L.v 1 0 ∧ 0 ≤ dg L.u L.v L.r 1 0
    rw [L.dg_B]
    simpa only [bd, sub_self, mul_zero, add_zero] using And.intro (le_refl (0 : ℝ)) hA
  · change closed L.u L.v L.r L.μ L.height L.u L.v .bdg
    refine ⟨L.outer_D, ?_⟩
    change 0 ≤ bd L.u L.v L.u L.v ∧ 0 ≤ dg L.u L.v L.r L.u L.v
    have hb : bd L.u L.v L.u L.v = 0 := by dsimp only [bd]; ring
    rw [hb, L.dg_D]
    exact ⟨le_rfl, le_rfl⟩
  · change closed L.u L.v L.r L.μ L.height (1 - L.r) L.r .bdg
    refine ⟨L.outer_G, ?_⟩
    change 0 ≤ bd L.u L.v (1 - L.r) L.r ∧ 0 ≤ dg L.u L.v L.r (1 - L.r) L.r
    rw [L.bd_G, L.dg_G]
    exact ⟨hA, le_rfl⟩

theorem aef_vertices (L : Layout) (i : Fin 3) :
    closed L.u L.v L.r L.μ L.height (![0, L.ε * L.u, 0] i)
      (![0, L.ε * L.v, L.μ] i) .aef := by
  fin_cases i
  · change closed L.u L.v L.r L.μ L.height 0 0 .aef
    refine ⟨by norm_num [outer], ?_⟩
    change ad L.u L.v 0 0 ≤ 0 ∧ dg L.u L.v L.r 0 0 ≤ L.height ∧ 0 ≤ fg L.r L.μ 0 0
    rw [L.dg_A]
    refine ⟨by simp [ad], ?_, ?_⟩
    · dsimp only [height]
      nlinarith [mul_pos L.ε_pos L.delta_pos]
    · dsimp only [fg]
      nlinarith [mul_pos (sub_pos.mpr L.r_lt_one) L.μ_pos]
  · change closed L.u L.v L.r L.μ L.height (L.ε * L.u) (L.ε * L.v) .aef
    refine ⟨L.outer_E, ?_⟩
    change ad L.u L.v (L.ε * L.u) (L.ε * L.v) ≤ 0 ∧
      dg L.u L.v L.r (L.ε * L.u) (L.ε * L.v) ≤ L.height ∧
        0 ≤ fg L.r L.μ (L.ε * L.u) (L.ε * L.v)
    rw [L.dg_E, L.fg_E]
    refine ⟨?_, le_rfl, mul_nonneg (mul_pos L.μ_pos L.u_pos).le (sub_nonneg.mpr L.ε_lt_one.le)⟩
    dsimp only [ad]
    nlinarith
  · change closed L.u L.v L.r L.μ L.height 0 L.μ .aef
    refine ⟨L.outer_F, ?_⟩
    change ad L.u L.v 0 L.μ ≤ 0 ∧ dg L.u L.v L.r 0 L.μ ≤ L.height ∧ 0 ≤ fg L.r L.μ 0 L.μ
    rw [L.dg_F]
    refine ⟨?_, le_rfl, by simp [fg]⟩
    dsimp only [ad]
    nlinarith [mul_pos L.u_pos L.μ_pos]

theorem cfg_vertices (L : Layout) (i : Fin 3) :
    closed L.u L.v L.r L.μ L.height (![0, 0, 1 - L.r] i) (![1, L.μ, L.r] i) .cfg := by
  fin_cases i
  · change closed L.u L.v L.r L.μ L.height 0 1 .cfg
    refine ⟨by norm_num [outer], ?_⟩
    change fg L.r L.μ 0 1 ≤ 0 ∧ ad L.u L.v 0 1 ≤ 0 ∧ dg L.u L.v L.r 0 1 ≤ 0
    rw [L.dg_C]
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [fg]
      nlinarith [mul_pos (sub_pos.mpr L.r_lt_one) (sub_pos.mpr L.μ_lt_one)]
    · simpa only [ad, mul_zero, mul_one, zero_sub, neg_nonpos] using L.u_pos.le
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [L.r_lt_one]) (by linarith [L.uv_lt_one])
  · change closed L.u L.v L.r L.μ L.height 0 L.μ .cfg
    refine ⟨L.outer_F, ?_⟩
    change fg L.r L.μ 0 L.μ ≤ 0 ∧ ad L.u L.v 0 L.μ ≤ 0 ∧ dg L.u L.v L.r 0 L.μ ≤ 0
    rw [L.dg_F]
    refine ⟨by simp [fg], ?_, L.height_neg.le⟩
    dsimp only [ad]
    nlinarith [mul_pos L.u_pos L.μ_pos]
  · change closed L.u L.v L.r L.μ L.height (1 - L.r) L.r .cfg
    refine ⟨L.outer_G, ?_⟩
    change fg L.r L.μ (1 - L.r) L.r ≤ 0 ∧ ad L.u L.v (1 - L.r) L.r ≤ 0 ∧
      dg L.u L.v L.r (1 - L.r) L.r ≤ 0
    rw [L.ad_G, L.dg_G]
    refine ⟨?_, by linarith [L.delta_pos], le_rfl⟩
    dsimp only [fg]
    nlinarith

theorem trapezoid_vertices (L : Layout) (i : Fin 4) :
    closed L.u L.v L.r L.μ L.height (![0, L.ε * L.u, L.u, 1 - L.r] i)
      (![L.μ, L.ε * L.v, L.v, L.r] i) .trapezoid := by
  fin_cases i
  · change closed L.u L.v L.r L.μ L.height 0 L.μ .trapezoid
    refine ⟨L.outer_F, ?_⟩
    change ad L.u L.v 0 L.μ ≤ 0 ∧ L.height ≤ dg L.u L.v L.r 0 L.μ ∧
      dg L.u L.v L.r 0 L.μ ≤ 0 ∧ 0 ≤ fg L.r L.μ 0 L.μ
    rw [L.dg_F]
    refine ⟨?_, le_rfl, L.height_neg.le, by simp [fg]⟩
    dsimp only [ad]
    nlinarith [mul_pos L.u_pos L.μ_pos]
  · change closed L.u L.v L.r L.μ L.height (L.ε * L.u) (L.ε * L.v) .trapezoid
    refine ⟨L.outer_E, ?_⟩
    change ad L.u L.v (L.ε * L.u) (L.ε * L.v) ≤ 0 ∧
      L.height ≤ dg L.u L.v L.r (L.ε * L.u) (L.ε * L.v) ∧
      dg L.u L.v L.r (L.ε * L.u) (L.ε * L.v) ≤ 0 ∧
      0 ≤ fg L.r L.μ (L.ε * L.u) (L.ε * L.v)
    rw [L.dg_E, L.fg_E]
    refine ⟨?_, le_rfl, L.height_neg.le,
      (mul_pos (mul_pos L.μ_pos L.u_pos) (sub_pos.mpr L.ε_lt_one)).le⟩
    dsimp only [ad]
    nlinarith
  · change closed L.u L.v L.r L.μ L.height L.u L.v .trapezoid
    refine ⟨L.outer_D, ?_⟩
    change ad L.u L.v L.u L.v ≤ 0 ∧ L.height ≤ dg L.u L.v L.r L.u L.v ∧
      dg L.u L.v L.r L.u L.v ≤ 0 ∧ 0 ≤ fg L.r L.μ L.u L.v
    rw [L.dg_D, L.fg_D]
    refine ⟨?_, L.height_neg.le, le_rfl,
      (mul_pos (sub_pos.mpr L.ε_lt_one) L.delta_pos).le⟩
    dsimp only [ad]
    nlinarith
  · change closed L.u L.v L.r L.μ L.height (1 - L.r) L.r .trapezoid
    refine ⟨L.outer_G, ?_⟩
    change ad L.u L.v (1 - L.r) L.r ≤ 0 ∧ L.height ≤ dg L.u L.v L.r (1 - L.r) L.r ∧
      dg L.u L.v L.r (1 - L.r) L.r ≤ 0 ∧ 0 ≤ fg L.r L.μ (1 - L.r) L.r
    rw [L.ad_G, L.dg_G]
    refine ⟨by linarith [L.delta_pos], L.height_neg.le, le_rfl, ?_⟩
    dsimp only [fg]
    nlinarith

end Erdos633b.DoubledPartition.Layout
