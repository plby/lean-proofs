/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim617DistinctSwitch
import ErdosProblems.Erdos547b.SourceParameterSchedule

/-!
# Integer switching scale, including the two root-cluster exclusions

The floor never increases the sparse-case count. Its lower bound uses
`rho*k >= 10`; no divisibility of a real scale is imposed.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoClaim617SwitchNumerics

open Finset SimpleGraph Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoClaim617 Erdos547b.ZhaoClaim617DistinctSwitch Erdos547b.ZhaoStability

def switchCount (rho : ℝ) (k : ℕ) : ℕ := ⌊5 * rho * k⌋₊

theorem switchCount_bounds {rho : ℝ} {k : ℕ} (hk : 10 ≤ rho * k) :
    (49 / 10 : ℝ) * rho * k < (switchCount rho k : ℝ) ∧
      (switchCount rho k : ℝ) ≤ 5 * rho * k := by
  have hnonneg : 0 ≤ 5 * rho * k := by linarith only [hk]
  have hfloor : 5 * rho * k < (switchCount rho k : ℝ) + 1 := Nat.lt_floor_add_one _
  exact ⟨by linarith only [hk, hfloor], Nat.floor_le hnonneg⟩

theorem parameter_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    80 * rho α * eta α + 4 * fourthRoot α ≤ rho α / 2 := by
  obtain ⟨_, hr0, he0, _, _, _, _, _⟩ := parameter_pos hα
  obtain ⟨hr11, hrr1, her, hte3, _, _, _⟩ := parameter_upper_bounds hα hα1
  have hr1 : rho α ≤ 1 := hrr1.trans hr11
  have heSmall : eta α ≤ 1 / 1000000 := by linarith only [her, hr1]
  have he1 : eta α ≤ 1 := by linarith only [heSmall]
  have he3 : eta α ^ 3 ≤ eta α := pow_succ_le_self he0.le he1 2
  have hprod := mul_le_mul_of_nonneg_left heSmall hr0.le
  linarith only [hprod, hte3, he3, her, hr0]

theorem sparse_count_lt {rho eta t : ℝ} {k r s v b : ℕ}
    (hrho : 0 < rho) (heta : 0 ≤ eta) (ht : 0 ≤ t)
    (hk : 10 ≤ rho * k) (hr : (r : ℝ) ≤ 5 * rho * k)
    (hs : s ≤ k) (hv : (v : ℝ) ≤ (1 + 8 * eta) * k)
    (hb : (b : ℝ) ≤ 4 * t * k + 2)
    (hmargin : 80 * rho * eta + 4 * t ≤ rho / 2) :
    ((2 * r * v + s * (r + b) : ℕ) : ℝ) < 16 * rho * (k : ℝ) ^ 2 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkpos : (0 : ℝ) < k := by
    by_contra h
    have hz : (k : ℝ) = 0 := le_antisymm (le_of_not_gt h) hk0
    rw [hz, mul_zero] at hk
    norm_num at hk
  have hsR : (s : ℝ) ≤ k := by exact_mod_cast hs
  have hfirst := mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2)) hv
    (Nat.cast_nonneg v : (0 : ℝ) ≤ v) (by positivity : 0 ≤ 2 * (5 * rho * k))
  have hsecond := mul_le_mul hsR (add_le_add hr hb)
    (by positivity : (0 : ℝ) ≤ (r : ℝ) + b) hk0
  have hm := mul_le_mul_of_nonneg_right hmargin (sq_nonneg (k : ℝ))
  have hround := mul_le_mul_of_nonneg_right hk hk0
  have hpos : 0 < rho * (k : ℝ) ^ 2 := mul_pos hrho (sq_pos_of_pos hkpos)
  push_cast
  nlinarith only [hfirst, hsecond, hm, hround, hpos]

theorem exists_distinctSwitch_of_dense
    {K : Type*} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (hM : M.IsMatching) (L S V B : Finset K)
    (rho eta t : ℝ) (k : ℕ)
    (hrho : 0 < rho) (heta : 0 ≤ eta) (ht : 0 ≤ t)
    (hk : 10 ≤ rho * k) (hS : S ⊆ matchingSupport M)
    (hs : S.card ≤ k) (hv : (V.card : ℝ) ≤ (1 + 8 * eta) * k)
    (hb : (B.card : ℝ) ≤ 4 * t * k + 2)
    (hmargin : 80 * rho * eta + 4 * t ≤ rho / 2)
    (hdense : 16 * rho * (k : ℝ) ^ 2 ≤ (R.interedges S V).card) :
    Nonempty (DistinctSwitch M L S (V \ B) (switchCount rho k)) := by
  apply exists_distinctSwitch_of_many_heavy M L hM S (V \ B) _ hS
  by_contra hmany
  have hcount := interedges_le_of_crossHeavy_card_le (R := R) S V B (switchCount rho k)
    (2 * switchCount rho k) (by omega)
  have hcountR : ((R.interedges S V).card : ℝ) ≤
      ((2 * switchCount rho k * V.card + S.card * (switchCount rho k + B.card) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hlt := sparse_count_lt hrho heta ht hk (switchCount_bounds hk).2 hs hv hb hmargin
  exact (hcountR.trans_lt hlt).not_ge hdense

end Erdos547b.ZhaoClaim617SwitchNumerics

#print axioms Erdos547b.ZhaoClaim617SwitchNumerics.switchCount_bounds
#print axioms Erdos547b.ZhaoClaim617SwitchNumerics.exists_distinctSwitch_of_dense
