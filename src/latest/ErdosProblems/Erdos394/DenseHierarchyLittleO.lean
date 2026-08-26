import ErdosProblems.Erdos394.DenseHierarchyComparison
import ErdosProblems.Erdos394.Defs

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# All-cutoff adjacent little-o theorem
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace Erdos394

/-- The uniform dense-grid comparison implies the required little-o relation
for real cutoffs. -/
theorem dense_adjacent_isLittleO (K : ℕ) (hK : 2 ≤ K) :
    (fun x : ℝ ↦ Tsum (K + 1) x) =o[atTop]
      (fun x : ℝ ↦ Tsum K x) := by
  have hcomp := eventually_dense_adjacent_three_mul_bound_uniform K hK
  rw [eventually_atTop] at hcomp
  obtain ⟨N0, hcomp⟩ := hcomp
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  obtain ⟨H : ℕ, hH⟩ := exists_nat_gt (3 / c)
  have hHpos : 0 < H := by
    have hthree : (0 : ℝ) < 3 / c := by positivity
    exact_mod_cast hthree.trans hH
  have hthreecH : (3 : ℝ) ≤ c * (H : ℝ) := by
    have := (div_lt_iff₀ hc).mp hH
    nlinarith
  let A := max N0 (2 ^ H)
  filter_upwards [eventually_ge_atTop (((16 ^ A : ℕ) : ℝ))] with x hx
  let X := ⌊x⌋₊
  let N := Nat.log 16 X
  let h := denseHierarchyLog N
  have hAX : 16 ^ A ≤ X := by
    dsimp [X]
    exact Nat.le_floor hx
  have hXpos : 0 < X := (pow_pos (by norm_num) A).trans_le hAX
  have hAN : A ≤ N := by
    dsimp [N]
    exact Nat.le_log_of_pow_le (by norm_num) hAX
  have hN0 : N0 ≤ N := (le_max_left N0 (2 ^ H)).trans hAN
  have hHN : 2 ^ H ≤ N := (le_max_right N0 (2 ^ H)).trans hAN
  have hHh : H ≤ h := by
    dsimp [h, denseHierarchyLog]
    exact Nat.le_log_of_pow_le (by norm_num) hHN
  have hhpos : 0 < h := hHpos.trans_le hHh
  have hgridLower : denseHierarchyX N ≤ X := by
    dsimp [denseHierarchyX, N]
    exact Nat.pow_log_le_self 16 hXpos.ne'
  have hgridUpper : X ≤ denseHierarchyX (N + 1) := by
    dsimp [denseHierarchyX, N]
    exact (Nat.lt_pow_succ_log_self (by norm_num) X).le
  have hfinite := hcomp N hN0 X hgridLower hgridUpper
  let F : ℝ := ∑ n ∈ Finset.Icc 1 X, (t (K + 1) n : ℝ)
  let G : ℝ := ∑ n ∈ Finset.Icc 1 X, (t K n : ℝ)
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hfinite' : (h : ℝ) * F ≤ 3 * G := by
    simpa [h, F, G] using hfinite
  have hscale : (3 : ℝ) ≤ c * (h : ℝ) := by
    have hcast : (H : ℝ) ≤ h := by exact_mod_cast hHh
    exact hthreecH.trans (mul_le_mul_of_nonneg_left hcast hc.le)
  have hright : 3 * G ≤ (c * (h : ℝ)) * G :=
    mul_le_mul_of_nonneg_right hscale hG0
  have hmul : (h : ℝ) * F ≤ (h : ℝ) * (c * G) := by
    calc
      (h : ℝ) * F ≤ 3 * G := hfinite'
      _ ≤ (c * (h : ℝ)) * G := hright
      _ = (h : ℝ) * (c * G) := by ring
  have hFG : F ≤ c * G :=
    le_of_mul_le_mul_left hmul (show (0 : ℝ) < h by exact_mod_cast hhpos)
  dsimp [Tsum]
  change ‖F‖ ≤ c * ‖G‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hF0, abs_of_nonneg hG0]
  exact hFG

/-- The affirmative second assertion of Erdős Problem 394. -/
theorem erdos394_second_target_proved : SecondQuestion := by
  intro K hK
  exact dense_adjacent_isLittleO K hK

end Erdos394
