import ErdosProblems.Erdos587.SqrtPhaseBounds

/-! A middle quarter of a unit-step fiber has a uniform square-root scale. -/

namespace Erdos587

lemma middle_quarter_length {M : ℕ} (hM : 8 ≤ M) :
    0 < M / 4 ∧ 2 * (M / 4) ≤ M ∧ M ≤ 8 * (M / 4) := by omega

theorem unit_fiber_sqrt_geometry {u v t M n T C : ℝ}
    (hu : 0 < u) (hv : 0 ≤ v) (ht : 0 ≤ t) (hn : 0 < n) (hT : 0 < T)
    (hC : 1 ≤ C) (hnM : 2 * n ≤ M) (hMn : M ≤ 8 * n)
    (hambient : u * (t + v * M) ≤ T) (hspan : T ≤ C * u * v * M) :
    let L := Real.sqrt T / u
    let a := (t + v * n) / u
    let b := v / u
    L ^ 2 / ((8 * C) * n) ≤ b ∧ b ≤ L ^ 2 / n ∧
      ∀ x ∈ Set.Icc (0 : ℝ) n, L ^ 2 / (8 * C) ≤ a + b * x ∧ a + b * x ≤ L ^ 2 := by
  let L := Real.sqrt T / u
  let a := (t + v * n) / u
  let b := v / u
  have hCpos : 0 < C := by linarith
  have hL2 : L ^ 2 * u ^ 2 = T := by
    dsimp only [L]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hu.ne'), Real.sq_sqrt hT.le]
  have hb : 0 ≤ b := div_nonneg hv hu.le
  have hbscale : b * n * u ^ 2 = u * v * n := by
    dsimp only [b]
    field_simp
  have hphase (x : ℝ) : (a + b * x) * u ^ 2 = u * (t + v * (n + x)) := by
    dsimp only [a, b]
    field_simp
    ring
  have hupper (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) n) : a + b * x ≤ L ^ 2 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hu)).mp
    rw [hphase, hL2]
    calc
      u * (t + v * (n + x)) ≤ u * (t + v * M) := by gcongr; linarith [hx.2]
      _ ≤ T := hambient
  have hlower : L ^ 2 ≤ (8 * C) * (b * n) := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hu)).mp
    rw [hL2, mul_assoc, hbscale]
    calc
      T ≤ C * u * v * M := hspan
      _ ≤ C * u * v * (8 * n) := mul_le_mul_of_nonneg_left hMn (by positivity)
      _ = _ := by ring
  have hbn : b * n ≤ a := by
    have heq : a = t / u + b * n := by dsimp only [a, b]; ring
    rw [heq]
    have hh : 0 ≤ t / u := div_nonneg ht hu.le
    linarith
  have hblo : L ^ 2 / ((8 * C) * n) ≤ b := by
    apply (div_le_iff₀ (by positivity : 0 < (8 * C) * n)).mpr
    nlinarith [hlower]
  have hbhi : b ≤ L ^ 2 / n := by
    apply (le_div_iff₀ hn).mpr
    have hh := hupper 0 ⟨le_rfl, hn.le⟩
    simp only [mul_zero, add_zero] at hh
    exact hbn.trans hh
  refine ⟨hblo, hbhi, ?_⟩
  intro x hx
  refine ⟨?_, hupper x hx⟩
  have hbase : L ^ 2 / (8 * C) ≤ b * n := (div_le_iff₀ (by positivity)).mpr (by
    simpa only [mul_comm (8 * C)] using hlower)
  exact hbase.trans (hbn.trans (le_add_of_nonneg_right (mul_nonneg hb hx.1)))

end Erdos587
