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
Case T of the bounded subset-sum covering lemma: the per-`a` decidable
T-line check `TlineGo`, its soundness, and the generic linear tail
(`a > 3000`).

Design note: an earlier draft's Case-T lemma used three staircase variants
(A: two-frame merge, `x = c+1`; B: the short merge, staircase part (c),
`x = c`; and the base form, part (d), `x = c+g`). Variant B rests on
`staircase_merge_c` (proved in Staircase.lean); `TlineBudget` checks only
variant A (`g = 1`) and the base form (`g ≥ 2`) — the paper's two
merge-robust variants — and the **14** triples where only variant B's budget
fits (all with `a ≤ 29`) are instead certified by explicit kernel-checked
frame certificates (`tSuppT` below, same `frameCertOK` checker as the
Appendix-B tables). The scan invariant `TlineGo e h a = true` for all lines
and `a ≤ 3000` was verified against this exact ℕ-truncated formula set:
budget failures = 158 (= `certTableA`) + 14 (= `tSuppT`) — together the
paper's 172-row Table A — none unexplained.

For `a > 3000` the base form alone fits on every line (`T_tail`): with
`μ' ≥ 3` (from `e ≠ h`), `z ≤ (a + 201)/3`, so the budget `2(y+z) + g + 1`
has slope `2/3 < 1` against `M = a + μ` — part (ii) of the paper's T-tail
proposition, with crude constants.
-/
import ErdosProblems.Erdos1112.Sharp.Staircase
import ErdosProblems.Erdos1112.Sharp.TablesData

namespace Erdos1112
namespace Proof

/-! ### Ceiling division -/

/-- Ceiling division `⌈n/m⌉` as `(n + m − 1)/m`. -/
def cdiv (n m : ℕ) : ℕ := (n + m - 1) / m

/-- `⌈n/m⌉·m ≥ n` (for `m > 0`). -/
lemma le_mul_cdiv {m : ℕ} (hm : 0 < m) (n : ℕ) : n ≤ m * cdiv n m := by
  unfold cdiv
  have h1 := Nat.div_add_mod (n + m - 1) m
  have h2 := Nat.mod_lt (n + m - 1) hm
  omega

/-- `⌈n/m⌉·m ≤ n + m − 1`. -/
lemma cdiv_mul_le {m : ℕ} (n : ℕ) : cdiv n m * m ≤ n + m - 1 := by
  unfold cdiv
  exact Nat.div_mul_le_self _ _

/-! ### The supplementary certificate table (variant-B replacements) -/

/-- The 14 T-line triples whose minimal draft budget was achieved only by
the short merge (part (c) of the paper's staircase lemma); certified here
directly by mod-`a` frame boxes so that Case T does not depend on
`staircase_merge_c`. Format `(a,b,M,x,Y,Z)`, same checker as Tables A/B. -/
def tSuppT : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (10, 13, 15, 9, 4, 1),
  (11, 14, 15, 7, 3, 4),
  (13, 16, 21, 10, 6, 1),
  (16, 19, 27, 13, 6, 2),
  (16, 21, 23, 10, 5, 2),
  (17, 22, 23, 10, 5, 6),
  (17, 22, 25, 10, 4, 3),
  (18, 23, 27, 14, 8, 1),
  (22, 29, 31, 11, 6, 3),
  (23, 30, 31, 13, 7, 8),
  (23, 30, 33, 13, 7, 2),
  (24, 31, 35, 12, 4, 4),
  (28, 37, 39, 14, 4, 5),
  (29, 38, 39, 15, 9, 10)]

set_option maxRecDepth 100000 in
theorem tSuppT_ok : tSuppT.all frameCertOK = true := by decide

/-- Every supplementary row yields its (SHARP) witness. -/
theorem tSuppT_sharp : ∀ r ∈ tSuppT, SharpTriple r.1 r.2.1 r.2.2.1 := by
  intro r hr
  obtain ⟨a, b, M, x, Y, Z⟩ := r
  exact frameCertOK_sharpTriple (List.all_eq_true.mp tSuppT_ok _ hr)

/-! ### The decidable per-`a` T-line check -/

/-- Side conditions of the T-scan at line `(e,h)`, position `a`: the
specialization of the Case-T routing hypotheses to `b = a+e`, `M = a+e+h`
(`h + 2 ≤ a` from the hard core's `δ ≥ 2`; `gcd(a,e) = 1` from
`gcd(a,b) = 1`; `a ∤ μ` ⟺ `a ∤ M`; `a ∤ 2e+h` ⟺ `a ∤ b+M`). -/
def TlineSide (e h a : ℕ) : Bool :=
  decide (h + 2 ≤ a) && decide (Nat.gcd a e = 1) &&
  decide ((e + h) % a ≠ 0) && decide ((2 * e + h) % a ≠ 0)

/-- Budget check for the two formalized Case-T variants, with the line
constants passed explicitly: variant A (`g = 1`, `x = c+1`, extended form)
and the base form (`g ≥ 2`, `x = c+g`). `μ` is the second argument. -/
def TlineBudgetCore (a μ g e' μ' C y : ℕ) : Bool :=
  if g = 1 then
    decide (2 * (y + max (e' - 1) (cdiv (max a μ - 1 + 2 * C - e' * y) μ')) + 1
      ≤ a + μ - 1)
  else
    decide (2 * (y + max (e' - 1) (cdiv (a + cdiv (μ - 1) g + 2 * C - e' * y) μ')) + g
      ≤ a + μ - 1)

/-- Budget check at line `(e,h)`, position `a`. -/
def TlineBudget (e h a : ℕ) : Bool :=
  TlineBudgetCore a (e + h) (Nat.gcd e (e + h)) (e / Nat.gcd e (e + h))
    ((e + h) / Nat.gcd e (e + h))
    ((e / Nat.gcd e (e + h) - 1) * ((e + h) / Nat.gcd e (e + h) - 1))
    ((e + h) / Nat.gcd e (e + h) - 1)

/-- Exception lookup: `(a, a+e, a+e+h)` is a row of Table A or of the
supplementary table. -/
def TlineTable (e h a : ℕ) : Bool :=
  (certTableA.any fun r => decide (r.1 = a ∧ r.2.1 = a + e ∧ r.2.2.1 = a + e + h)) ||
  (tSuppT.any fun r => decide (r.1 = a ∧ r.2.1 = a + e ∧ r.2.2.1 = a + e + h))

/-- The full per-`a` check: side conditions imply budget-or-table. -/
def TlineGo (e h a : ℕ) : Bool :=
  !TlineSide e h a || TlineBudget e h a || TlineTable e h a

/-! ### Soundness of the two variants -/

/-- Generic base-form soundness (any `g ≥ 1`): a staircase `(x, y, z)` with
one frame per phase class and run-length/budget inequalities yields the
(SHARP) witness. `hrun` is the additive form of
`g·(V′−C′) ≥ (g−1)·a + M − 1`. -/
lemma T_base {a b M g e' μ' C' y z x : ℕ} (S : StairSetup a b M g e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1))
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    (hag : Nat.Coprime a g)
    (hx : y + z + g - 1 ≤ x)
    (hrun : (g - 1) * a + M + 2 * (g * C') ≤ g * (e' * y + μ' * z) + 1)
    (hbud : x + y + z + 1 ≤ M) : SharpTriple a b M := by
  have hg1 : 1 ≤ g := S.g_pos
  have hCW : C' ≤ e' * y + μ' * z := by
    have h1 : (e' - 1) * (μ' - 1) ≤ e' * y := Nat.mul_le_mul (Nat.sub_le e' 1) hy
    omega
  set V' := e' * y + μ' * z - C' with hV'def
  have hV' : V' + C' = e' * y + μ' * z := by omega
  have run := staircase_phase_base S hC' hV' hag hy hz hx
  refine ⟨stair a b M x y z, ?_, ?_, (y + z + g - 1) * a + g * C', ?_⟩
  · intro w hw
    simp only [stair] at hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inl (Multiset.eq_of_mem_replicate hw)
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hw))
    · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hw))
  · simp only [stair, Multiset.card_add, Multiset.card_replicate]
    omega
  · intro i hi
    apply run
    · exact Nat.le_add_right _ _
    · have hsplit : (y + z + g - 1) * a = (y + z) * a + (g - 1) * a := by
        have hb : y + z + g - 1 = (y + z) + (g - 1) := by omega
        rw [hb, Nat.add_mul]
      have hgV : g * V' + g * C' = g * (e' * y + μ' * z) := by
        rw [← Nat.mul_add, hV']
      omega

/-- Variant-A soundness (`g = 1`, `x = c + 1`, extended form
the staircase extended/base form (d)): merge and run-length inequalities in additive `W`-form
(`W := e′·y + μ′·z = V′ + C′`), budget `2c + 2 ≤ M`. -/
lemma T_variantA {a b M e' μ' C' y z : ℕ} (S : StairSetup a b M 1 e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1))
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    (hmerge : a + 2 * C' ≤ e' * y + μ' * z + 1)
    (hlen : M + 2 * C' ≤ a + (e' * y + μ' * z) + 1)
    (hbud : 2 * (y + z) + 2 ≤ M) : SharpTriple a b M := by
  have hCW : C' ≤ e' * y + μ' * z := by
    have h1 : (e' - 1) * (μ' - 1) ≤ e' * y := Nat.mul_le_mul (Nat.sub_le e' 1) hy
    omega
  set V' := e' * y + μ' * z - C' with hV'def
  have hV' : V' + C' = e' * y + μ' * z := by omega
  have run := staircase_phase_extended S hC' hV' (Nat.coprime_one_right a) hy hz
    (le_refl (y + z + 1)) (by omega)
  refine ⟨stair a b M (y + z + 1) y z, ?_, ?_, (y + z) * a + C', ?_⟩
  · intro w hw
    simp only [stair] at hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inl (Multiset.eq_of_mem_replicate hw)
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hw))
    · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hw))
  · simp only [stair, Multiset.card_add, Multiset.card_replicate]
    omega
  · intro i hi
    apply run
    · rw [show y + z + 1 - 1 = y + z from by omega, Nat.one_mul]
      omega
    · rw [show y + z + 1 - 1 + 1 = y + z + 1 from by omega, Nat.one_mul]
      have hb2 : (y + z + 1) * a = (y + z) * a + a := by ring
      omega

/-! ### Soundness of the decided check -/

/-- Soundness of `TlineBudgetCore` at a T-line point, with the line
constants pinned by defining equations (all discharged by `rfl` at the
call site). -/
lemma TlineBudgetCore_sound {a e h g e' μ' C y : ℕ}
    (he : 1 ≤ e) (hh : 1 ≤ h) (ha : 0 < a) (hcop : Nat.Coprime a e)
    (hg : g = Nat.gcd e (e + h)) (he' : e' = e / g) (hμ' : μ' = (e + h) / g)
    (hC : C = (e' - 1) * (μ' - 1)) (hy : y = μ' - 1)
    (hbud : TlineBudgetCore a (e + h) g e' μ' C y = true) :
    SharpTriple a (a + e) (a + e + h) := by
  have S : StairSetup a (a + e) (a + e + h) g e' μ' := by
    refine ⟨by omega, by omega, ha, ?_, ?_, ?_⟩
    · rw [show a + e - a = e from by omega, show a + e + h - a = e + h from by omega]
      exact hg
    · rw [show a + e - a = e from by omega]
      exact he'
    · rw [show a + e + h - a = e + h from by omega]
      exact hμ'
  have he'0 : 0 < e' := S.e'_pos
  have hμ'0 : 0 < μ' := lt_trans he'0 S.e'_lt_μ'
  rw [TlineBudgetCore] at hbud
  by_cases hg1 : g = 1
  · -- variant A
    rw [if_pos hg1, decide_eq_true_eq] at hbud
    set z := max (e' - 1) (cdiv (max a (e + h) - 1 + 2 * C - e' * y) μ') with hzdef
    have hz1 : e' - 1 ≤ z := hzdef ▸ le_max_left _ _
    have hz2 : cdiv (max a (e + h) - 1 + 2 * C - e' * y) μ' ≤ z :=
      hzdef ▸ le_max_right _ _
    have hW : max a (e + h) - 1 + 2 * C ≤ e' * y + μ' * z := by
      have h1 : max a (e + h) - 1 + 2 * C - e' * y
          ≤ μ' * cdiv (max a (e + h) - 1 + 2 * C - e' * y) μ' := le_mul_cdiv hμ'0 _
      have h2 : μ' * cdiv (max a (e + h) - 1 + 2 * C - e' * y) μ' ≤ μ' * z :=
        Nat.mul_le_mul_left μ' hz2
      omega
    have S1 : StairSetup a (a + e) (a + e + h) 1 e' μ' := hg1 ▸ S
    exact T_variantA (y := y) (z := z) S1 hC (by omega) hz1 (by omega) (by omega)
      (by omega)
  · -- base form
    rw [if_neg hg1, decide_eq_true_eq] at hbud
    set z := max (e' - 1) (cdiv (a + cdiv (e + h - 1) g + 2 * C - e' * y) μ') with hzdef
    have hz1 : e' - 1 ≤ z := hzdef ▸ le_max_left _ _
    have hz2 : cdiv (a + cdiv (e + h - 1) g + 2 * C - e' * y) μ' ≤ z :=
      hzdef ▸ le_max_right _ _
    have hg0 : 0 < g := S.g_pos
    have hW : a + cdiv (e + h - 1) g + 2 * C ≤ e' * y + μ' * z := by
      have h1 : a + cdiv (e + h - 1) g + 2 * C - e' * y
          ≤ μ' * cdiv (a + cdiv (e + h - 1) g + 2 * C - e' * y) μ' := le_mul_cdiv hμ'0 _
      have h2 : μ' * cdiv (a + cdiv (e + h - 1) g + 2 * C - e' * y) μ' ≤ μ' * z :=
        Nat.mul_le_mul_left μ' hz2
      omega
    have hgdvde : g ∣ e := hg ▸ Nat.gcd_dvd_left _ _
    have hagg : Nat.Coprime a g := hcop.coprime_dvd_right hgdvde
    apply T_base (x := y + z + g) (y := y) (z := z) S hC (by omega) hz1 hagg
      (by omega)
    · -- hrun
      have h3 : e + h - 1 ≤ g * cdiv (e + h - 1) g := le_mul_cdiv hg0 _
      have h4 : g * (a + cdiv (e + h - 1) g + 2 * C) ≤ g * (e' * y + μ' * z) :=
        Nat.mul_le_mul_left g hW
      have h5 : g * (a + cdiv (e + h - 1) g + 2 * C)
          = g * a + g * cdiv (e + h - 1) g + 2 * (g * C) := by ring
      have h6 : (g - 1) * a + a = g * a := by
        have hb : g - 1 + 1 = g := by omega
        calc (g - 1) * a + a = (g - 1 + 1) * a := by ring
          _ = g * a := by rw [hb]
      omega
    · -- hbud
      omega

/-- Soundness of the full per-`a` check: at a genuine Case-T point
(specialized side hypotheses), `TlineGo e h a = true` yields the (SHARP)
witness — by variant A / base form when the budget fits, and by the
Table A / supplementary certificates otherwise. -/
lemma TlineGo_sound {e h a : ℕ} (he : 1 ≤ e) (hh : 1 ≤ h)
    (h2a : h + 2 ≤ a) (hcop : Nat.Coprime a e)
    (hnd1 : ¬ a ∣ (e + h)) (hnd2 : ¬ a ∣ (2 * e + h))
    (hgo : TlineGo e h a = true) : SharpTriple a (a + e) (a + e + h) := by
  have ha : 0 < a := by omega
  have hside : TlineSide e h a = true := by
    simp only [TlineSide, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨h2a, hcop⟩, fun hz => hnd1 (Nat.dvd_of_mod_eq_zero hz)⟩,
      fun hz => hnd2 (Nat.dvd_of_mod_eq_zero hz)⟩
  simp only [TlineGo, hside, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hgo
  rcases hgo with hbud | htab
  · -- budget branch
    simp only [TlineBudget] at hbud
    exact TlineBudgetCore_sound he hh ha hcop rfl rfl rfl rfl rfl hbud
  · -- table branch
    simp only [TlineTable, Bool.or_eq_true, List.any_eq_true,
      decide_eq_true_eq] at htab
    rcases htab with ⟨r, hrmem, hr1, hr2, hr3⟩ | ⟨r, hrmem, hr1, hr2, hr3⟩
    · have hs := certTableA_sharp r hrmem
      rw [hr1, hr2, hr3] at hs
      exact hs
    · have hs := tSuppT_sharp r hrmem
      rw [hr1, hr2, hr3] at hs
      exact hs

/-! ### The linear tail `a > 3000` (T-tail, part (ii)) -/

/-- Tail at line level: for `a ≥ 3001` the base form alone fits on every
line. Crude constants (`e', y, g ≤ 10`, `μ' ≤ 11`, `C ≤ 90`) give
`3·z ≤ a + 201`, whence the budget `2(y+z) + g + 1` is under
`M = a + e + h` with room `≥ (a − 495)/3`. Needs `μ' ≥ 3`, i.e. `e ≠ h`. -/
lemma T_tail_line {a e h : ℕ} (he : 1 ≤ e) (hh : 1 ≤ h) (hμ : e + h ≤ 11)
    (hne : e ≠ h) (hcop : Nat.Coprime a e) (ha : 3001 ≤ a) :
    SharpTriple a (a + e) (a + e + h) := by
  set g := Nat.gcd e (e + h) with hgdef
  set e' := e / g with he'def
  set μ' := (e + h) / g with hμ'def
  set C := (e' - 1) * (μ' - 1) with hCdef
  set y := μ' - 1 with hydef
  have S : StairSetup a (a + e) (a + e + h) g e' μ' := by
    refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [show a + e - a = e from by omega, show a + e + h - a = e + h from by omega]
    · rw [show a + e - a = e from by omega]
    · rw [show a + e + h - a = e + h from by omega]
  have hg0 : 0 < g := S.g_pos
  have hgdvde : g ∣ e := hgdef ▸ Nat.gcd_dvd_left _ _
  have hge : g ≤ e := Nat.le_of_dvd (by omega) hgdvde
  have he'e : e' ≤ e := he'def ▸ Nat.div_le_self e g
  have hμ'μ : μ' ≤ e + h := hμ'def ▸ Nat.div_le_self _ _
  have he'0 : 0 < e' := S.e'_pos
  have he'μ' : e' < μ' := S.e'_lt_μ'
  have hμ'0 : 0 < μ' := by omega
  -- `μ' ≥ 3`: `μ' ≤ 2` forces `(e', μ') = (1, 2)`, i.e. `h = g = e`.
  have hμ'3 : 3 ≤ μ' := by
    by_contra hlt
    push Not at hlt
    have hμ'2 : μ' = 2 := by omega
    have he'1 : e' = 1 := by omega
    have hbe := S.e_eq
    have hMe := S.μ_eq
    rw [he'1, Nat.mul_one] at hbe
    rw [hμ'2] at hMe
    exact hne (by omega)
  have hC90 : C ≤ 90 := by
    rw [hCdef]
    calc (e' - 1) * (μ' - 1) ≤ 9 * 10 := Nat.mul_le_mul (by omega) (by omega)
      _ = 90 := by norm_num
  have he'y : e' * y ≤ 100 := by
    calc e' * y ≤ 10 * 10 := Nat.mul_le_mul (by omega) (by omega)
      _ = 100 := by norm_num
  set N := a + (e + h) + 2 * C - e' * y with hNdef
  set z := max (e' - 1) (cdiv N μ') with hzdef
  have hz1 : e' - 1 ≤ z := hzdef ▸ le_max_left _ _
  have hz2 : cdiv N μ' ≤ z := hzdef ▸ le_max_right _ _
  have hWlo : a + (e + h) + 2 * C ≤ e' * y + μ' * z := by
    have h1 : N ≤ μ' * cdiv N μ' := le_mul_cdiv hμ'0 N
    have h2 : μ' * cdiv N μ' ≤ μ' * z := Nat.mul_le_mul_left μ' hz2
    omega
  have hz3 : 3 * z ≤ a + 201 := by
    have h1 : cdiv N μ' * μ' ≤ N + μ' - 1 := cdiv_mul_le N
    have h2 : cdiv N μ' * 3 ≤ cdiv N μ' * μ' := Nat.mul_le_mul_left _ hμ'3
    have h4 : 3 * cdiv N μ' = cdiv N μ' * 3 := Nat.mul_comm _ _
    omega
  have hagg : Nat.Coprime a g := hcop.coprime_dvd_right hgdvde
  apply T_base (x := y + z + g) (y := y) (z := z) S hCdef (by omega) hz1 hagg
    (by omega)
  · -- hrun: `g·W ≥ g·a + g·μ + 2·g·C ≥ (g−1)·a + M + 2·g·C − 1`
    have h4 : g * (a + (e + h) + 2 * C) ≤ g * (e' * y + μ' * z) :=
      Nat.mul_le_mul_left g hWlo
    have h5 : g * (a + (e + h) + 2 * C) = g * a + g * (e + h) + 2 * (g * C) := by
      ring
    have h6 : (g - 1) * a + a = g * a := by
      have hb : g - 1 + 1 = g := by omega
      calc (g - 1) * a + a = (g - 1 + 1) * a := by ring
        _ = g * a := by rw [hb]
    have h7 : e + h ≤ g * (e + h) := Nat.le_mul_of_pos_left _ hg0
    omega
  · -- budget: `2(y+z) + g + 1 ≤ a + e + h`, from `3z ≤ a + 201`, `a ≥ 3001`
    omega

/-- **T-tail (ii), packaged**: the Case-T tail `a ≥ 3001`. -/
lemma T_tail {a b M : ℕ} (hc : HardCore a b M) (hL : b - a ≠ M - b)
    (hμ : M - a ≤ 11) (ha : 3001 ≤ a) : SharpTriple a b M := by
  have hcop := hc.coprime_a_e
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  set e := b - a with hedef
  set h := M - b with hhdef
  have hbe : b = a + e := by omega
  have hMe : M = a + e + h := by omega
  rw [hbe, hMe]
  exact T_tail_line (by omega) (by omega) (by omega) hL hcop ha

end Proof
end Erdos1112
