import Mathlib

/-!
# A separated switching subsequence

This file isolates the elementary deterministic selection argument used in the
proof of Erdős Problem 636.  The integer-budget formulation below avoids any
rounding convention: `m` is the requested number of separated transitions.
-/

namespace Erdos636

namespace Switching

/-- The part of the `i`-th increment which is discarded when it is larger than
`ρ`.  Such a discarded increment is necessarily nonnegative when `0 < ρ`. -/
noncomputable def largeIncrement (p : ℕ → ℝ) (ρ : ℝ) (i : ℕ) : ℝ :=
  if ρ < p (i + 1) - p i then p (i + 1) - p i else 0

/-- Cumulative contribution of the positive increments larger than `ρ`. -/
noncomputable def largeIncrementSum (p : ℕ → ℝ) (ρ : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i, largeIncrement p ρ j

lemma largeIncrement_nonneg {p : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (i : ℕ) :
    0 ≤ largeIncrement p ρ i := by
  rw [largeIncrement]
  split_ifs with h
  · linarith
  · exact le_rfl

lemma largeIncrementSum_mono {p : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Monotone (largeIncrementSum p ρ) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [largeIncrementSum, largeIncrementSum, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (largeIncrement_nonneg hρ i)

/-- First-crossing selection for a path whose positive one-step increments are
bounded by `ρ`.  The hypothesis asks for `m` whole level spacings `ρ + σ` of
net rise.  The selected map includes both endpoints and has exactly `m`
transitions, each gaining at least `σ` in value. -/
theorem boundedRise_separated_subsequence
    {τ m : ℕ} (q : ℕ → ℝ) {ρ σ : ℝ}
    (hm : 1 ≤ m) (hρ : 0 ≤ ρ) (hσ : 0 < σ)
    (hstep : ∀ i < τ, q (i + 1) - q i ≤ ρ)
    (hrise : (m : ℝ) * (ρ + σ) ≤ q τ - q 0) :
    ∃ idx : Fin (m + 1) → ℕ,
      StrictMono idx ∧ idx 0 = 0 ∧ idx (Fin.last m) = τ ∧
        ∀ j : Fin m, σ ≤ q (idx j.succ) - q (idx j.castSucc) := by
  classical
  let d : ℝ := ρ + σ
  let P : ℕ → ℕ → Prop := fun j i ↦ i ≤ τ ∧ q 0 + (j : ℝ) * d ≤ q i
  have hd : 0 < d := by dsimp [d]; linarith
  have hP : ∀ j ≤ m, ∃ i, P j i := by
    intro j hj
    refine ⟨τ, le_rfl, ?_⟩
    have hjcast : (j : ℝ) ≤ m := by exact_mod_cast hj
    dsimp [d] at hrise ⊢
    nlinarith
  let hit : ℕ → ℕ := fun j ↦ if hj : j ≤ m then Nat.find (hP j hj) else 0
  have hit_spec (j : ℕ) (hj : j ≤ m) : P j (hit j) := by
    simp only [hit, dif_pos hj]
    exact Nat.find_spec (hP j hj)
  have hit_le (j : ℕ) (hj : j ≤ m) : hit j ≤ τ := (hit_spec j hj).1
  have hit_lower (j : ℕ) (hj : j ≤ m) :
      q 0 + (j : ℝ) * d ≤ q (hit j) := (hit_spec j hj).2
  have hit_min (j : ℕ) (hj : j ≤ m) {i : ℕ} (hi : P j i) : hit j ≤ i := by
    simp only [hit, dif_pos hj]
    exact Nat.find_min' (hP j hj) hi
  have hit_pos (j : ℕ) (hj : j ≤ m) (hj0 : 0 < j) : 0 < hit j := by
    by_contra h
    have hz : hit j = 0 := Nat.eq_zero_of_not_pos h
    have hlo := hit_lower j hj
    rw [hz] at hlo
    have hjcast : (0 : ℝ) < j := by exact_mod_cast hj0
    nlinarith
  have hit_upper (j : ℕ) (hj : j ≤ m) (hj0 : 0 < j) :
      q (hit j) < q 0 + (j : ℝ) * d + ρ := by
    have hp := hit_pos j hj hj0
    have hleτ := hit_le j hj
    have hpred : hit j - 1 < τ := by omega
    have hnot : ¬P j (hit j - 1) := by
      intro hbad
      have hle := hit_min j hj hbad
      omega
    have hpredlt : q (hit j - 1) < q 0 + (j : ℝ) * d := by
      exact lt_of_not_ge fun hge ↦ hnot ⟨by omega, hge⟩
    have hs := hstep (hit j - 1) hpred
    have heq : hit j - 1 + 1 = hit j := by omega
    rw [heq] at hs
    linarith
  have hit_strict (j : ℕ) (hj0 : 0 < j) (hjs : j + 1 ≤ m) :
      hit j < hit (j + 1) := by
    have hjm : j ≤ m := by omega
    have hlow := hit_lower (j + 1) hjs
    have hupp := hit_upper j hjm hj0
    have hnot : ¬P (j + 1) (hit j) := by
      intro hbad
      have := hbad.2
      norm_num [d] at this hupp
      nlinarith
    have hmono : hit j ≤ hit (j + 1) := by
      exact hit_min j hjm ⟨(hit_le (j + 1) hjs), by
        have h := hit_lower (j + 1) hjs
        have hlevel : q 0 + (j : ℝ) * d ≤ q 0 + ((j + 1 : ℕ) : ℝ) * d := by
          rw [Nat.cast_add, Nat.cast_one]
          nlinarith [hd]
        exact hlevel.trans h⟩
    exact lt_of_le_of_ne hmono (Ne.symm (fun heq ↦ hnot (heq ▸ hit_spec (j + 1) hjs)))
  let idxNat : ℕ → ℕ := fun j ↦
    if j = 0 then 0 else if j = m then τ else hit j
  have idxNat_le (j : ℕ) (hj : j ≤ m) : idxNat j ≤ τ := by
    dsimp [idxNat]
    split_ifs with h0 hm'
    · exact Nat.zero_le _
    · exact le_rfl
    · exact hit_le j hj
  have idxNat_succ_lt (j : ℕ) (hj : j < m) : idxNat j < idxNat (j + 1) := by
    by_cases h0 : j = 0
    · subst j
      simp only [idxNat, if_pos, zero_add, if_false, Nat.one_ne_zero]
      by_cases hm1 : 1 = m
      · simp only [if_pos hm1]
        have hend : 0 < τ := by
          by_contra hτ
          have : τ = 0 := Nat.eq_zero_of_not_pos hτ
          rw [this, sub_self] at hrise
          have : (0 : ℝ) < (m : ℝ) * (ρ + σ) :=
            mul_pos (by exact_mod_cast hm) hd
          linarith
        exact hend
      · simp only [if_neg hm1]
        exact hit_pos 1 (by omega) (by omega)
    · have hjpos : 0 < j := Nat.pos_of_ne_zero h0
      have hjm : j ≠ m := Nat.ne_of_lt hj
      simp only [idxNat, if_neg h0, if_neg hjm, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        if_false]
      by_cases hlast : j + 1 = m
      · simp only [if_pos hlast]
        have hupp := hit_upper j (by omega) hjpos
        have hend : q 0 + (m : ℝ) * d ≤ q τ := by
          dsimp [d] at hrise ⊢
          linarith
        have hne : hit j ≠ τ := by
          intro heq
          rw [heq] at hupp
          have hjreal : (j : ℝ) + 1 = m := by exact_mod_cast hlast
          nlinarith
        exact lt_of_le_of_ne (hit_le j (by omega)) hne
      · simp only [if_neg hlast]
        exact hit_strict j hjpos (by omega)
  let idx : Fin (m + 1) → ℕ := fun j ↦ idxNat j
  refine ⟨idx, ?_, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro j
    exact idxNat_succ_lt j (by omega)
  · simp [idx, idxNat]
  · have hm0 : m ≠ 0 := by omega
    simp [idx, idxNat, hm0]
  · intro j
    have hj : j.val < m := j.isLt
    by_cases h0 : j.val = 0
    · have hnext : (j.val + 1 = m) ∨ (j.val + 1 < m) := by omega
      rcases hnext with hlast | hinterior
      · have hval : q 0 + (m : ℝ) * d ≤ q τ := by
          dsimp [d] at hrise ⊢
          linarith
        have hleft : idx j.castSucc = 0 := by
          change idxNat j.val = 0
          simp [idxNat, h0]
        have hright : idx j.succ = τ := by
          change idxNat (j.val + 1) = τ
          simp [idxNat, hlast, show m ≠ 0 by omega]
        rw [hleft, hright]
        have hmreal : (m : ℝ) = 1 := by exact_mod_cast (show m = 1 by omega)
        dsimp [d] at hval
        nlinarith
      · have hlo := hit_lower 1 (by omega)
        have hleft : idx j.castSucc = 0 := by
          change idxNat j.val = 0
          simp [idxNat, h0]
        have hright : idx j.succ = hit 1 := by
          change idxNat (j.val + 1) = hit 1
          simp [idxNat, h0, show 1 ≠ m by omega]
        rw [hleft, hright]
        norm_num [d] at hlo
        linarith
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero h0
      have hjne : j.val ≠ m := Nat.ne_of_lt hj
      by_cases hlast : j.val + 1 = m
      · have hupp := hit_upper j.val (by omega) hjpos
        have hend : q 0 + (m : ℝ) * d ≤ q τ := by
          dsimp [d] at hrise ⊢
          linarith
        have hleft : idx j.castSucc = hit j.val := by
          change idxNat j.val = hit j.val
          simp [idxNat, h0, hjne]
        have hright : idx j.succ = τ := by
          change idxNat (j.val + 1) = τ
          simp [idxNat, hlast, show m ≠ 0 by omega]
        rw [hleft, hright]
        have hjreal : (j.val : ℝ) + 1 = m := by exact_mod_cast hlast
        dsimp [d] at hupp hend
        nlinarith
      · have hupp := hit_upper j.val (by omega) hjpos
        have hlo := hit_lower (j.val + 1) (by omega)
        have hleft : idx j.castSucc = hit j.val := by
          change idxNat j.val = hit j.val
          simp [idxNat, h0, hjne]
        have hright : idx j.succ = hit (j.val + 1) := by
          change idxNat (j.val + 1) = hit (j.val + 1)
          simp [idxNat, hlast]
        rw [hleft, hright]
        have hcast : ((j.val + 1 : ℕ) : ℝ) = (j.val : ℝ) + 1 := by norm_num
        rw [hcast] at hlo
        dsimp [d] at hupp hlo
        nlinarith

/-- Integer-budget form of the separated switching lemma.  A total budget
`κ` for positive jumps larger than `ρ` costs at most that amount of net rise.
If `m * (ρ + σ) + κ ≤ λ`, the path contains `m + 1` time indices, including
both endpoints, whose consecutive values rise by at least `σ`.

The paper's real-valued cardinal estimate follows by taking the integer part
of `λ / (ρ + σ) - κ / ρ`. -/
theorem separatedSwitchingSubsequence
    {τ m : ℕ} (p : ℕ → ℝ) {lam κ ρ σ : ℝ}
    (hm : 1 ≤ m) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hrise : lam ≤ p τ - p 0)
    (hlarge : largeIncrementSum p ρ τ ≤ κ)
    (hbudget : (m : ℝ) * (ρ + σ) + κ ≤ lam) :
    ∃ idx : Fin (m + 1) → ℕ,
      StrictMono idx ∧ idx 0 = 0 ∧ idx (Fin.last m) = τ ∧
        ∀ j : Fin m, σ ≤ p (idx j.succ) - p (idx j.castSucc) := by
  let b : ℕ → ℝ := largeIncrementSum p ρ
  let q : ℕ → ℝ := fun i ↦ p i - b i
  have hbmono : Monotone b := largeIncrementSum_mono hρ.le
  have hqstep : ∀ i < τ, q (i + 1) - q i ≤ ρ := by
    intro i hi
    dsimp [q, b, largeIncrementSum]
    rw [Finset.sum_range_succ]
    rw [largeIncrement]
    split_ifs with h
    · ring_nf
      linarith
    · have hle : p (i + 1) - p i ≤ ρ := le_of_not_gt h
      ring_nf
      simpa [add_comm] using hle
  have hqrise : (m : ℝ) * (ρ + σ) ≤ q τ - q 0 := by
    have hb0 : b 0 = 0 := by simp [b, largeIncrementSum]
    have hbτ : b τ ≤ κ := hlarge
    dsimp [q]
    rw [hb0]
    linarith
  obtain ⟨idx, hidx, hzero, hlast, hsep⟩ :=
    boundedRise_separated_subsequence q hm hρ.le hσ hqstep hqrise
  refine ⟨idx, hidx, hzero, hlast, ?_⟩
  intro j
  have hindices : idx j.castSucc ≤ idx j.succ :=
    (hidx Fin.castSucc_lt_succ).le
  have hb := hbmono hindices
  have hq := hsep j
  dsimp [q] at hq
  linarith

/-- Real-valued cardinal form of the switching lemma.

The explicit assumption `σ ≤ lam` is necessary for a subsequence containing
both endpoints: without it, even a path with one small positive increment is
a counterexample to the unqualified printed statement.  The conclusion uses
`m` for the number of transitions, so the subsequence itself has `m + 1`
members. -/
theorem separatedSwitchingSubsequence_realBound
    {τ : ℕ} (p : ℕ → ℝ) {lam κ ρ σ : ℝ}
    (hρ : 0 < ρ) (hσ : 0 < σ) (hσlam : σ ≤ lam)
    (hrise : lam ≤ p τ - p 0)
    (hlarge : largeIncrementSum p ρ τ ≤ κ) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ idx : Fin (m + 1) → ℕ,
      StrictMono idx ∧ idx 0 = 0 ∧ idx (Fin.last m) = τ ∧
        (∀ j : Fin m, σ ≤ p (idx j.succ) - p (idx j.castSucc)) ∧
        lam / (ρ + σ) - κ / ρ ≤ (m + 1 : ℕ) := by
  have hlarge_nonneg : 0 ≤ largeIncrementSum p ρ τ := by
    exact Finset.sum_nonneg fun i _ ↦ largeIncrement_nonneg hρ.le i
  have hκ : 0 ≤ κ := hlarge_nonneg.trans hlarge
  have hd : 0 < ρ + σ := by linarith
  let R : ℝ := lam / (ρ + σ) - κ / ρ
  by_cases hR : R ≤ 1
  · have hτ : 0 < τ := by
      by_contra hτ'
      have : τ = 0 := Nat.eq_zero_of_not_pos hτ'
      rw [this, sub_self] at hrise
      linarith
    let idx : Fin 2 → ℕ := fun i ↦ if i = 0 then 0 else τ
    have hidx : StrictMono idx := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp [idx, hτ]
    refine ⟨1, by omega, idx, hidx, ?_, ?_, ?_, ?_⟩
    · simp [idx]
    · simp [idx]
    · intro j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      simpa [idx] using hσlam.trans hrise
    · dsimp [R] at hR
      norm_num
      linarith
  · have hRpos : 0 ≤ R := le_trans (by norm_num) (le_of_not_ge hR)
    let m : ℕ := ⌊R⌋₊
    have hm : 1 ≤ m := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hm0
      have hfloor : (m : ℝ) ≤ R := Nat.floor_le hRpos
      have hlt := Nat.lt_floor_add_one R
      change R < (m : ℝ) + 1 at hlt
      rw [hm0] at hlt
      norm_num at hlt
      exact hR hlt.le
    have hmR : (m : ℝ) ≤ R := Nat.floor_le hRpos
    have hκscale : κ ≤ (κ / ρ) * (ρ + σ) := by
      have hqnonneg : 0 ≤ κ / ρ := div_nonneg hκ hρ.le
      calc
        κ = (κ / ρ) * ρ := by field_simp
        _ ≤ (κ / ρ) * (ρ + σ) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hqnonneg
    have hbudget : (m : ℝ) * (ρ + σ) + κ ≤ lam := by
      have hmul := mul_le_mul_of_nonneg_right hmR hd.le
      dsimp [R] at hmul
      have halg :
          (lam / (ρ + σ) - κ / ρ) * (ρ + σ) =
            lam - (κ / ρ) * (ρ + σ) := by
        field_simp
      rw [halg] at hmul
      linarith
    obtain ⟨idx, hidx, hzero, hlast, hsep⟩ :=
      separatedSwitchingSubsequence p hm hρ hσ hrise hlarge hbudget
    refine ⟨m, hm, idx, hidx, hzero, hlast, hsep, ?_⟩
    have hlt := Nat.lt_floor_add_one R
    dsimp [m] at hlt ⊢
    dsimp [R] at hlt ⊢
    calc
      lam / (ρ + σ) - κ / ρ ≤
          (⌊lam / (ρ + σ) - κ / ρ⌋₊ : ℝ) + 1 := hlt.le
      _ = (⌊lam / (ρ + σ) - κ / ρ⌋₊ + 1 : ℕ) := by norm_num

end Switching

end Erdos636
