import ErdosProblems.Erdos587.SqrtLocator
import ErdosProblems.Erdos587.UnitFiberGeometry
import ErdosProblems.Erdos587.UnitFiberBudget
import ErdosProblems.Erdos587.SquareGapLift

/-! A square in a unit-step fiber under explicit scale and polynomial budgets. -/

namespace Erdos587

theorem exists_unit_fiber_square {C : ℝ} (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (u t v H M : ℕ) (T : ℝ),
      0 < u → 0 < H → 8 ≤ M → 0 < T →
      (H : ℝ) ≤ 4 * Real.sqrt T →
      (u : ℝ) * ((t : ℝ) + H + v * M) ≤ T →
      T ≤ C * u * v * M →
      (M : ℝ) ≤ Real.sqrt T / (8 * (8 * C) ^ 3 * u) →
      K * T ^ 4 < (u : ℝ) * (H : ℝ) ^ 7 * (M : ℝ) ^ 3 →
      ∃ x ≤ H, ∃ j ≤ M, ∃ z : ℕ, 0 < z ∧ z ^ 2 = u * (t + x + v * j) := by
  have hA : 1 ≤ 8 * C := by linarith
  obtain ⟨K, hK, hlocator⟩ := exists_sqrtAffinePhase_locator hA
  refine ⟨K * 8 ^ 10, by positivity, ?_⟩
  intro u t v H M T hu hH hM hT hHroot hambient hspan hratio hbudget
  let N := M / 4
  let L := Real.sqrt T / u
  let a := ((t : ℝ) + v * N) / u
  let b := (v : ℝ) / u
  let δ := (H : ℝ) / (8 * Real.sqrt T)
  obtain ⟨hN, h2N, h8N⟩ := middle_quarter_length hM
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < L := div_pos (Real.sqrt_pos.mpr hT) huR
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one₀ (by positivity : 0 < 8 * Real.sqrt T)).mpr
    nlinarith [Real.sqrt_pos.mpr hT]
  have hambient' : (u : ℝ) * ((t : ℝ) + v * M) ≤ T := by
    have hh : (u : ℝ) * ((t : ℝ) + v * M) ≤ (u : ℝ) * ((t : ℝ) + H + v * M) := by
      apply mul_le_mul_of_nonneg_left _ huR.le
      linarith
    exact hh.trans hambient
  have hgeom := unit_fiber_sqrt_geometry huR (Nat.cast_nonneg v) (Nat.cast_nonneg t)
    hNR hT hC (by exact_mod_cast h2N) (by exact_mod_cast h8N) hambient' hspan
  change L ^ 2 / ((8 * C) * N) ≤ b ∧ b ≤ L ^ 2 / N ∧
    ∀ x ∈ Set.Icc (0 : ℝ) N, L ^ 2 / (8 * C) ≤ a + b * x ∧ a + b * x ≤ L ^ 2 at hgeom
  have hNF : (N : ℝ) ≤ L / (8 * (8 * C) ^ 3) := by
    calc
      (N : ℝ) ≤ M := by exact_mod_cast (show N ≤ M by dsimp only [N]; omega)
      _ ≤ Real.sqrt T / (8 * (8 * C) ^ 3 * u) := hratio
      _ = L / (8 * (8 * C) ^ 3) := by dsimp only [L]; ring
  have hsmall : K * L < (N : ℝ) ^ 3 * δ ^ 7 := by
    apply unit_fiber_locator_budget huR hHR (Nat.cast_nonneg M) hT _ hbudget
    have hh : (M : ℝ) ≤ 8 * N := by exact_mod_cast h8N
    linarith
  obtain ⟨n, hn, k, hk0, hk1⟩ := hlocator a b L δ N hN hL hδ hδ1
    hgeom.1 hgeom.2.1 hgeom.2.2 hNF hsmall
  have hj : N + n ≤ M := by omega
  have hphase : sqrtAffinePhase a b n =
      Real.sqrt (((t : ℝ) + v * (N + n : ℕ)) / u) := by
    unfold sqrtAffinePhase
    congr 1
    dsimp only [a, b]
    push_cast
    ring
  rw [hphase] at hk0 hk1
  have hwidth : (u : ℝ) * H ≤ T := by
    have hh : (u : ℝ) * H ≤ (u : ℝ) * ((t : ℝ) + H + v * M) := by
      apply mul_le_mul_of_nonneg_left _ huR.le
      have ht0 := Nat.cast_nonneg (α := ℝ) t
      have hvM0 : (0 : ℝ) ≤ v * M := by positivity
      linarith
    exact hh.trans hambient
  have hambientj : (u : ℝ) * ((t : ℝ) + v * (N + n : ℕ)) ≤ T := by
    apply le_trans _ hambient'
    gcongr
  obtain ⟨x, hx, z, hz, heq⟩ := unit_fiber_square_of_sqrt_gap hu hH hT hwidth hambientj hk0 hk1
  exact ⟨x, hx, N + n, hj, z, hz, heq⟩

end Erdos587
