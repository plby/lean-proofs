/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.Eventual

/-!
# The analytic rate conversion in Hunter's theorem

Hunter obtains finite colorings whose forbidden red length is at most
`exp (C * sqrt (log N * log (log N)))` for sufficiently large `N`.
This file proves, without asymptotic notation, that this rate supplies the
eventual subpower field used by `EventualOffDiagonalData`.
-/

open Filter Asymptotics

namespace Erdos984

/-- The exponent in Hunter's quantitative estimate is eventually at most
`ε log x`. -/
lemma hunter_exponent_eventually_le {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      C * √(Real.log x * Real.log (Real.log x)) ≤ ε * Real.log x := by
  have hll : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
      (fun x : ℝ => Real.log x) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  let q : ℝ := ε / C
  have hq : 0 < q := div_pos hε hC
  have hsmall := hll.bound (sq_pos_of_pos hq)
  have hlog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hsmall, hlog] with x hx hL
  have hL0 : 0 ≤ Real.log x := le_trans zero_le_one hL
  have hLL0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL
  rw [Real.norm_eq_abs, abs_of_nonneg hLL0, Real.norm_eq_abs,
    abs_of_nonneg hL0] at hx
  have hprod :
      Real.log x * Real.log (Real.log x) ≤ (q * Real.log x) ^ 2 := by
    calc
      Real.log x * Real.log (Real.log x) ≤
          Real.log x * (q ^ 2 * Real.log x) :=
        mul_le_mul_of_nonneg_left hx hL0
      _ = (q * Real.log x) ^ 2 := by ring
  have hsqrt :
      √(Real.log x * Real.log (Real.log x)) ≤ q * Real.log x :=
    (Real.sqrt_le_iff).2 ⟨mul_nonneg hq.le hL0, hprod⟩
  calc
    C * √(Real.log x * Real.log (Real.log x)) ≤
        C * (q * Real.log x) := mul_le_mul_of_nonneg_left hsqrt hC.le
    _ = ε * Real.log x := by
      dsimp [q]
      field_simp [hC.ne']

/-- A threshold form of `hunter_exponent_eventually_le`, convenient for
natural interval lengths. -/
lemma exists_hunter_exponent_threshold {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      C * √(Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) ≤
        ε * Real.log (N : ℝ) := by
  obtain ⟨x₀, hx₀⟩ :=
    eventually_atTop.1 (hunter_exponent_eventually_le hC hε)
  let N₀ : ℕ := ⌈max x₀ 1⌉₊
  refine ⟨N₀, ?_⟩
  intro N hN
  apply hx₀
  have hxceil : max x₀ 1 ≤ (N₀ : ℝ) := by
    dsimp [N₀]
    exact Nat.le_ceil _
  have hcast : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact le_trans (le_max_left _ _) (le_trans hxceil hcast)

/-- The exact data supplied by the quantitative conclusion of Hunter's
finite construction.  The hard combinatorial-geometric theorem is the
construction of a value of this structure. -/
structure HunterRateData where
  C : ℝ
  C_pos : 0 < C
  threshold : ℕ
  H : ℕ → ℕ
  three_le_H : ∀ N, 3 ≤ H N
  coloring : ℕ → ℕ → Bool
  good : ∀ N, GoodOffDiagonal (coloring N) N (H N)
  rate : ∀ N : ℕ, threshold ≤ N → 0 < N →
    (H N : ℝ) ≤
      Real.exp (C * √(Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))))

/-- Hunter's displayed quantitative rate is subpower. -/
def HunterRateData.toEventualOffDiagonalData
    (D : HunterRateData) : EventualOffDiagonalData where
  H := D.H
  three_le_H := D.three_le_H
  coloring := D.coloring
  good := D.good
  eventually_subpower := by
    intro ε hε
    obtain ⟨Nε, hNε⟩ := exists_hunter_exponent_threshold D.C_pos hε
    refine ⟨max D.threshold Nε, ?_⟩
    intro N hN hNpos
    have hthreshold : D.threshold ≤ N := le_trans (le_max_left _ _) hN
    have hNth : Nε ≤ N := le_trans (le_max_right _ _) hN
    calc
      (D.H N : ℝ) ≤
          Real.exp (D.C * √(Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) :=
        D.rate N hthreshold hNpos
      _ ≤ Real.exp (ε * Real.log (N : ℝ)) :=
        Real.exp_le_exp.mpr (hNε N hNth)
      _ = (N : ℝ) ^ ε := by
        rw [Real.rpow_def_of_pos (Nat.cast_pos.2 hNpos)]
        congr 1
        ring

/-- The quantitative Hunter data in the exact form consumed by the block
assembly. -/
def HunterRateData.toOffDiagonalData (D : HunterRateData) : OffDiagonalData :=
  D.toEventualOffDiagonalData.toOffDiagonalData

end Erdos984
