/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMaximalGap
import ErdosProblems.Erdos4b.FGKMTScaleMonotonicity

/-! # Infinitely many gaps at the exact stronger prime-index scale -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem exists_strong_index_gaps : ∃ c : ℝ, 0 < c ∧ StrongErdos4For c := by
  obtain ⟨c, hc, hmax⟩ := exists_eventual_maximal_gap
  refine ⟨c / 2, by positivity, ?_⟩
  apply infinite_natSet_of_forall_exists_ge
  intro N
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((hloglog.eventually_ge_atTop (Real.exp 2)).and
      ((eventually_ge_atTop N).and (eventually_ge_atTop (2 : ℕ))))
  have hlarge : ∀ᶠ X : ℝ in atTop,
      (Nat.nth Nat.Prime N₀ : ℝ) < c * fgkmtScale X :=
    (tendsto_fgkmtScale_atTop.const_mul_atTop hc).eventually_gt_atTop _
  obtain ⟨X, hgapX, hlargeX⟩ := (hmax.and hlarge).exists
  obtain ⟨n, hright, hgap⟩ := hgapX
  have hn : N₀ ≤ n := by
    by_contra hn
    have hnext : Nat.nth Nat.Prime (n + 1) ≤ Nat.nth Nat.Prime N₀ :=
      Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)
    have hnextR : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ Nat.nth Nat.Prime N₀ := by
      exact_mod_cast hnext
    have hp0 : (0 : ℝ) ≤ Nat.nth Nat.Prime n := Nat.cast_nonneg _
    linarith
  have hndata := hN₀ n hn
  have hnX : (n : ℝ) ≤ X := by
    have hsmall : n ≤ Nat.nth Nat.Prime (n + 1) := by
      have hh := Nat.add_two_le_nth_prime (n + 1)
      omega
    exact (show (n : ℝ) ≤ Nat.nth Nat.Prime (n + 1) by exact_mod_cast hsmall).trans hright
  have hmono := fgkmtScale_mono (by exact_mod_cast (show 1 < n by omega)) hndata.1 hnX
  have hscalePos : 0 < fgkmtScale X := by
    have hp0 : (0 : ℝ) ≤ Nat.nth Nat.Prime N₀ := Nat.cast_nonneg _
    have hh : 0 < c * fgkmtScale X := hp0.trans_lt hlargeX
    exact (mul_pos_iff_of_pos_left hc).mp hh
  refine ⟨n, hndata.2.1, ?_⟩
  change strongThreshold (c / 2) n < _
  rw [strongThreshold_eq_fgkmtScale]
  calc
    _ ≤ (c / 2) * fgkmtScale X := mul_le_mul_of_nonneg_left hmono (by positivity)
    _ < c * fgkmtScale X := mul_lt_mul_of_pos_right (by linarith) hscalePos
    _ ≤ _ := hgap

end

end Erdos4b.FGKMT
