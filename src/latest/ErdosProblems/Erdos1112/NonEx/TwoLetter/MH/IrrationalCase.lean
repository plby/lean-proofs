/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 1112.
Informal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
Formal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
GPT-5.5 and Gemini 3.1 supplied advice and adversarial review.
Source: https://www.erdosproblems.com/1112#post-7375
https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
/-
Morse–Hedlund, stage 3: irrational slope ⇒ some tail of the counting function
is exactly mechanical.

Threshold separation, density-free route: with the discrepancy
`D n := q n − n·α ∈ [−1, 1]`, a *bad pair* (`ε m = 1`, `ε n = 0`,
`{mα} < {nα}`) is **exactly** a pair with `D m − D n > 1` (since
`D i = ε i − {iα}`).  Balance transfers to increments: for `t := m − n > 0`
and every base `i`,
  `D(i+t) − D(i) ≥ (D(n+t) − D(n)) − 1 = (D m − D n) − 1 > 0`,
and iterating along `0, t, 2t, …` drives `D(r·t) → ∞`, contradicting
`|D| ≤ 1` (mirror case for `m < n`).  So the separation needs NO density, NO
three-distance, NO arc amplification — `exists_nat_gt` is the only analytic
input.  The threshold `c := sSup ({0} ∪ {fract(nα) : ε n = 0})` then defines
the mechanical intercept, with at most ONE boundary index (fract-injectivity
from irrationality), removed by passing to a tail.
-/
import ErdosProblems.Erdos1112.NonEx.TwoLetter.MH.Slope

namespace Erdos1112
namespace Proof
namespace MH

/-- Discrepancy of the counting word against slope `α`. -/
noncomputable def disc (h : ℕ → Bool) (α : ℝ) (n : ℕ) : ℝ :=
  (qCount h n : ℝ) - n * α

/-- **Separation core.**  Balance + `|D| ≤ 1` force the discrepancy
oscillation ≤ 1.  Route (see header): if
`D m − D n > 1`, iterate the balance-transferred increment along the
arithmetic progression with difference `t = |m − n|`; contradiction with
boundedness after `r > 2/(D m − D n − 1)` steps (`exists_nat_gt`).
No irrationality needed here. -/
theorem disc_osc_le_one (h : ℕ → Bool) (hbal : BalancedHyp h)
    {α : ℝ} (hD : ∀ n : ℕ, |disc h α n| ≤ 1) :
    ∀ m n : ℕ, disc h α m - disc h α n ≤ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m, n, hgap⟩ := hcon
  have hmn : m ≠ n := by rintro rfl; linarith
  -- increments over a fixed shift t: the n·α terms cancel
  have key : ∀ t i j : ℕ,
      disc h α (i + t) - disc h α i - (disc h α (j + t) - disc h α j) =
        ((qCount h (i + t) : ℝ) - qCount h i) -
          ((qCount h (j + t) : ℝ) - qCount h j) := by
    intro t i j
    simp only [disc]
    push_cast
    ring
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · -- m < n : descending ladder with step t := n − m
    set t := n - m with ht_def
    have htm : m + t = n := by omega
    have hstep : ∀ i : ℕ,
        disc h α (i + t) ≤ disc h α i + (disc h α n - disc h α m + 1) := by
      intro i
      have hb := hbal i m t
      have hbR : ((qCount h (i + t) : ℝ) - qCount h i) -
          ((qCount h (m + t) : ℝ) - qCount h m) ≤ 1 := by exact_mod_cast hb
      have hk := key t i m
      rw [htm] at hk hbR
      linarith
    have hiter : ∀ r : ℕ,
        disc h α (r * t) ≤ disc h α 0 + r * (disc h α n - disc h α m + 1) := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
          have hs := hstep (r * t)
          have heq : (r + 1) * t = r * t + t := by ring
          rw [heq]
          push_cast
          linarith
    have hx : 0 < -(disc h α n - disc h α m + 1) := by linarith
    obtain ⟨r, hr⟩ := exists_nat_gt (2 / (-(disc h α n - disc h α m + 1)))
    have h1 := hiter r
    have h2 := hD (r * t)
    have h3 := hD 0
    rw [abs_le] at h2 h3
    have h4 : 2 < (r : ℝ) * (-(disc h α n - disc h α m + 1)) := by
      have := (div_lt_iff₀ hx).mp hr
      linarith
    nlinarith [h1, h2.1, h3.2]
  · -- m > n : ascending ladder with step t := m − n
    set t := m - n with ht_def
    have htn : n + t = m := by omega
    have hstep : ∀ i : ℕ,
        disc h α i + (disc h α m - disc h α n - 1) ≤ disc h α (i + t) := by
      intro i
      have hb := hbal n i t
      have hbR : ((qCount h (n + t) : ℝ) - qCount h n) -
          ((qCount h (i + t) : ℝ) - qCount h i) ≤ 1 := by exact_mod_cast hb
      have hk := key t n i
      rw [htn] at hk hbR
      linarith
    have hiter : ∀ r : ℕ,
        disc h α 0 + r * (disc h α m - disc h α n - 1) ≤ disc h α (r * t) := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
          have hs := hstep (r * t)
          have heq : (r + 1) * t = r * t + t := by ring
          rw [heq]
          push_cast
          linarith
    have hx : 0 < disc h α m - disc h α n - 1 := by linarith
    obtain ⟨r, hr⟩ := exists_nat_gt (2 / (disc h α m - disc h α n - 1))
    have h1 := hiter r
    have h2 := hD (r * t)
    have h3 := hD 0
    rw [abs_le] at h2 h3
    have h4 : 2 < (r : ℝ) * (disc h α m - disc h α n - 1) := by
      have := (div_lt_iff₀ hx).mp hr
      linarith
    nlinarith [h1, h2.2, h3.1]

/-- For irrational `α` and `n ≥ 1`, `q n ∈ {⌊nα⌋, ⌊nα⌋ + 1}`.
Route: `|D n| ≤ 1`; the endpoint `q n = nα − 1` is excluded by
`(hα.natCast_mul).ne_int`-style rationality, giving the strict inequality
that `Int.le_floor` / `Int.floor_le_iff` convert. -/
theorem eps_mem (h : ℕ → Bool) {α : ℝ} (hα : Irrational α)
    (hD : ∀ n : ℕ, |disc h α n| ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    (qCount h n : ℤ) = ⌊(n : ℝ) * α⌋ ∨ (qCount h n : ℤ) = ⌊(n : ℝ) * α⌋ + 1 := by
  have hDn := hD n
  rw [disc, abs_le] at hDn
  have hup : (qCount h n : ℤ) ≤ ⌊(n : ℝ) * α⌋ + 1 := by
    have h1 : (qCount h n : ℤ) ≤ ⌊(n : ℝ) * α + ((1 : ℤ) : ℝ)⌋ :=
      Int.le_floor.mpr (by push_cast; linarith [hDn.2])
    rwa [Int.floor_add_intCast] at h1
  have hstrict : (n : ℝ) * α - 1 < qCount h n := by
    rcases lt_or_eq_of_le hDn.1 with hlt | heq
    · linarith
    · exfalso
      have hirr : Irrational ((n : ℝ) * α) := by
        have hn0 : n ≠ 0 := by omega
        exact_mod_cast hα.natCast_mul hn0
      exact hirr.ne_int ((qCount h n : ℤ) + 1) (by push_cast; linarith)
  have hlow : ⌊(n : ℝ) * α⌋ ≤ (qCount h n : ℤ) := by
    rw [Int.floor_le_iff]
    push_cast
    linarith
  omega

/-- `n ↦ Int.fract (n·α)` is injective on `n ≥ 1` for irrational `α`.
Route: equal fracts ⇒ `(m − n)·α ∈ ℤ` ⇒ `m = n` via `hα.intCast_mul` +
`Irrational.ne_int`. -/
theorem fract_injective {α : ℝ} (hα : Irrational α) {m n : ℕ}
    (hf : Int.fract ((m : ℝ) * α) = Int.fract ((n : ℝ) * α)) : m = n := by
  by_contra hne
  have h1 : (m : ℝ) * α - ⌊(m : ℝ) * α⌋ = (n : ℝ) * α - ⌊(n : ℝ) * α⌋ := by
    rw [Int.self_sub_floor, Int.self_sub_floor]
    exact hf
  have hmn : (m : ℤ) - n ≠ 0 := by omega
  have hirr : Irrational ((((m : ℤ) - n : ℤ) : ℝ) * α) := hα.intCast_mul hmn
  exact hirr.ne_int (⌊(m : ℝ) * α⌋ - ⌊(n : ℝ) * α⌋) (by push_cast; linarith)

/-- **Mechanical tail** for irrational slope.  Route: `disc_osc_le_one` +
`eps_mem`; threshold `c := sSup ({0} ∪ {Int.fract (nα) : ε n = 0})`;
`ε n = 1 ⇒ c ≤ fract(nα)` (upper-bound check unpacks a would-be bad pair),
`ε n = 0 ⇒ fract(nα) ≤ c` (`le_csSup`); at most one index attains `c`
(`fract_injective`), tail `T₀` past it; floor identity
`⌊nα + (1 − c)⌋ = ⌊nα⌋ + ind(fract(nα) ≥ c)` (`Int.floor_intCast_add`);
finally the tail shift `β := Int.fract (T·α + (1 − c))` via
`Int.floor_add_intCast`. -/
theorem mechanical_tail (h : ℕ → Bool) (hbal : BalancedHyp h)
    {α : ℝ} (hα : Irrational α) (hD : ∀ n : ℕ, |disc h α n| ≤ 1) :
    ∃ (β : ℝ) (T : ℕ), ∀ n : ℕ,
      (qCount h (T + n) : ℤ) - qCount h T = ⌊(n : ℝ) * α + β⌋ := by
  classical
  have hosc : ∀ m n, disc h α m - disc h α n ≤ 1 := disc_osc_le_one h hbal hD
  set ev : ℕ → ℤ := fun n => (qCount h n : ℤ) - ⌊(n : ℝ) * α⌋ with hev_def
  have hev01 : ∀ n, 1 ≤ n → ev n = 0 ∨ ev n = 1 := by
    intro n hn
    simp only [hev_def]
    rcases eps_mem h hα hD n hn with h0 | h1
    · left; rw [h0]; ring
    · right; rw [h1]; ring
  have hDeq : ∀ n, disc h α n = (ev n : ℝ) - Int.fract ((n : ℝ) * α) := by
    intro n
    have hf : Int.fract ((n : ℝ) * α) = (n : ℝ) * α - ⌊(n : ℝ) * α⌋ :=
      (Int.self_sub_floor _).symm
    rw [disc, hf]; simp only [hev_def]; push_cast; ring
  have hsep : ∀ m n, 1 ≤ m → 1 ≤ n → ev m = 1 → ev n = 0 →
      Int.fract ((n : ℝ) * α) ≤ Int.fract ((m : ℝ) * α) := by
    intro m n _ _ hem hen
    have := hosc m n; rw [hDeq, hDeq, hem, hen] at this; push_cast at this; linarith
  set S : Set ℝ := insert 0 {r | ∃ n, 1 ≤ n ∧ ev n = 0 ∧ Int.fract ((n : ℝ) * α) = r}
    with hS_def
  have hSbdd : BddAbove S := by
    refine ⟨1, fun r hr => ?_⟩
    rcases hr with h0 | ⟨n, _, _, hrn⟩
    · exact h0 ▸ zero_le_one
    · exact hrn ▸ le_of_lt (Int.fract_lt_one _)
  have hSne : S.Nonempty := ⟨0, Set.mem_insert 0 _⟩
  set c := sSup S with hc_def
  have hc0 : 0 ≤ c := le_csSup hSbdd (Set.mem_insert 0 _)
  have hc1 : c ≤ 1 := csSup_le hSne (fun r hr => by
    rcases hr with h0 | ⟨n, _, _, hrn⟩
    · exact h0 ▸ zero_le_one
    · exact hrn ▸ le_of_lt (Int.fract_lt_one _))
  have hle_c : ∀ n, 1 ≤ n → ev n = 0 → Int.fract ((n : ℝ) * α) ≤ c :=
    fun n hn hen => le_csSup hSbdd (Or.inr ⟨n, hn, hen, rfl⟩)
  have hge_c : ∀ m, 1 ≤ m → ev m = 1 → c ≤ Int.fract ((m : ℝ) * α) :=
    fun m hm hem => csSup_le hSne (fun r hr => by
      rcases hr with h0 | ⟨n, hn, hen, hrn⟩
      · exact h0 ▸ Int.fract_nonneg _
      · exact hrn ▸ hsep m n hm hn hem hen)
  -- tail `T` past the at-most-one boundary index `fract = c`
  obtain ⟨T, hT1, hTbdry⟩ :
      ∃ T : ℕ, 1 ≤ T ∧ ∀ m : ℕ, T ≤ m → Int.fract ((m : ℝ) * α) ≠ c := by
    by_cases hb : ∃ n₀ : ℕ, 1 ≤ n₀ ∧ Int.fract ((n₀ : ℝ) * α) = c
    · obtain ⟨n₀, hn₀1, hn₀c⟩ := hb
      refine ⟨n₀ + 1, by omega, fun m hm hmc => ?_⟩
      have hm1 : 1 ≤ m := by omega
      have hmeq : m = n₀ := fract_injective hα (by rw [hmc, hn₀c])
      omega
    · push Not at hb; exact ⟨1, le_refl 1, fun m hm hmc => hb m hm hmc⟩
  have hqm : ∀ m, T ≤ m → (qCount h m : ℤ) = ⌊(m : ℝ) * α + (1 - c)⌋ := by
    intro m hm
    have hm1 : 1 ≤ m := le_trans hT1 hm
    have hne := hTbdry m hm
    have hqeps : (qCount h m : ℤ) = ⌊(m : ℝ) * α⌋ + ev m := by rw [hev_def]; ring
    rw [hqeps]; symm; rw [Int.floor_eq_iff]
    have hfe : (m : ℝ) * α = ⌊(m : ℝ) * α⌋ + Int.fract ((m : ℝ) * α) :=
      (Int.floor_add_fract _).symm
    rcases hev01 m hm1 with h0 | h1
    · have hfc : Int.fract ((m : ℝ) * α) < c := lt_of_le_of_ne (hle_c m hm1 h0) hne
      rw [h0]; push_cast; constructor <;> linarith [hfe, hfc, hc1, Int.fract_nonneg ((m:ℝ)*α)]
    · have hgc : c < Int.fract ((m : ℝ) * α) := lt_of_le_of_ne (hge_c m hm1 h1) (Ne.symm hne)
      rw [h1]; push_cast; constructor <;> linarith [hfe, hgc, hc0, Int.fract_lt_one ((m:ℝ)*α)]
  refine ⟨(T : ℝ) * α + (1 - c) - (qCount h T : ℝ), T, fun n => ?_⟩
  rw [hqm (T + n) (by omega)]
  rw [show (n : ℝ) * α + ((T : ℝ) * α + (1 - c) - (qCount h T : ℝ))
      = (((T + n : ℕ) : ℝ) * α + (1 - c)) - ((qCount h T : ℤ) : ℝ) from by push_cast; ring]
  rw [Int.floor_sub_intCast]

end MH
end Proof
end Erdos1112
