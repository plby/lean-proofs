/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 694.
https://www.erdosproblems.com/forum/thread/694

Formalization status:
- Unconditional: standard Lean axioms only

Informal authors:
- GPT-5.5 Pro
- Liam Price

Formal authors:
- Claude Code 4.7
- GPT-5.5 Pro
- Pawan Sasanka Ammanamanchi

URLs:
- https://www.erdosproblems.com/forum/thread/694#post-6202
- https://www.overleaf.com/read/fgmhvywvdjkt#54ca5d
- https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P694/Proof.lean
- https://raw.githubusercontent.com/Shashi456/erdos-formalizations/refs/heads/main/Erdos/P694/Proof.lean
-/
/-
The lower bound uses products of distinct primes in dyadic intervals, supplied
by the proved uniform prime-counting theorem `Erdos387.shiftedSiegelWalfiszLower`.
No invocation of the shared Linnik axiom remains. The older height lemma is
retained in `LinnikConstruction` with its prime-existence hypothesis explicit.
-/

import ErdosProblems.Erdos694.Unconditional
import ErdosProblems.Erdos694.LinnikConstruction

namespace Erdos694

open Filter Asymptotics Topology
open scoped BigOperators Nat

/-- The unconditional lower-bound construction, with the original statement. -/
theorem totient_collision_construction :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      ∃ a b n : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧ n ≤ x ∧
        Nat.totient a = n ∧ Nat.totient b = n ∧
        (b : ℝ) / a ≥ (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log x) :=
  unconditional_totient_collision_construction

private lemma R_ge_of_totient_collision {x a b n : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hn : 1 ≤ n) (hnx : n ≤ x)
    (hφa : Nat.totient a = n) (hφb : Nat.totient b = n) :
    (b : ℝ) / a ≤ R x := by
  -- We show R x ≥ b/a by exhibiting n in the supremum index set.
  -- mmax := sSup {m | φ m = n} ≥ b (since b is in the set and the set is bounded)
  -- mmin := sInf {m | φ m = n} ≤ a (since a is in the set)
  -- so mmax/mmin ≥ b/a.
  set A : Set ℕ := {m | Nat.totient m = n} with hA_def
  have hb_in : b ∈ A := hφb
  have ha_in : a ∈ A := hφa
  have hA_ne : A.Nonempty := ⟨b, hb_in⟩
  -- A is bounded above by 2 n^2 (totient_preimage_bound).
  have hA_bdd : BddAbove A := by
    refine ⟨2 * n ^ 2, ?_⟩
    intro m hm
    have hm_pos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · have hm' : Nat.totient m = n := hm
        rw [h0, Nat.totient_zero] at hm'
        omega
      · exact hpos
    exact totient_preimage_bound hm_pos hm
  set mmax : ℕ := sSup A with hmmax_def
  set mmin : ℕ := sInf A with hmmin_def
  have hmmax_in : mmax ∈ A := Nat.sSup_mem hA_ne hA_bdd
  have hmmin_in : mmin ∈ A := Nat.sInf_mem hA_ne
  -- b ≤ mmax (since b ∈ A, mmax = sSup A).
  have hb_le_mmax : b ≤ mmax := le_csSup hA_bdd hb_in
  -- mmin ≤ a (since a ∈ A, mmin = sInf A).
  have hmmin_le_a : mmin ≤ a := Nat.sInf_le ha_in
  -- mmin ≥ 1.
  have hmmin_pos : 1 ≤ mmin := by
    rcases Nat.eq_zero_or_pos mmin with h0 | hpos
    · have : Nat.totient mmin = n := hmmin_in
      rw [h0, Nat.totient_zero] at this
      omega
    · exact hpos
  have hmmax_pos : 1 ≤ mmax := le_trans hb hb_le_mmax
  -- (mmax : ℝ)/mmin ≥ b/a.
  have ha_pos_R : (0 : ℝ) < a := by exact_mod_cast ha
  have hmmin_pos_R : (0 : ℝ) < mmin := by exact_mod_cast hmmin_pos
  have hb_le_mmax_R : (b : ℝ) ≤ mmax := by exact_mod_cast hb_le_mmax
  have hmmin_le_a_R : (mmin : ℝ) ≤ a := by exact_mod_cast hmmin_le_a
  have hratio_ge : (b : ℝ) / a ≤ (mmax : ℝ) / mmin := by
    -- b/a ≤ mmax/a ≤ mmax/mmin
    have h1 : (b : ℝ) / a ≤ (mmax : ℝ) / a :=
      div_le_div_of_nonneg_right hb_le_mmax_R (le_of_lt ha_pos_R)
    have hmmax_nn : (0 : ℝ) ≤ mmax := by exact_mod_cast Nat.zero_le _
    have h2 : (mmax : ℝ) / a ≤ (mmax : ℝ) / mmin :=
      div_le_div_of_nonneg_left hmmax_nn hmmin_pos_R hmmin_le_a_R
    linarith
  -- Now show R x ≥ mmax/mmin by inclusion in the supremum.
  -- n ∈ {n | n ∈ Icc 1 x ∧ ∃ m, φ m = n}
  have hn_in_idx : n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n} := by
    refine ⟨⟨hn, hnx⟩, b, hφb⟩
  -- Boundedness for the outer sup.
  -- The outer family ⨆ (n : ℕ), ⨆ (_ : n ∈ idx_set), (mmax_n : ℝ) / mmin_n is bounded
  -- by 2 * x^2 (since mmax ≤ 2 n² ≤ 2 x², and mmin ≥ 1).
  have hbdd_outer :
      BddAbove (Set.range (fun (n' : ℕ) =>
        ⨆ (_ : n' ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}),
          let mmax' := sSup {m | Nat.totient m = n'}
          let mmin' := sInf {m | Nat.totient m = n'}
          (mmax' : ℝ) / mmin')) := by
    refine ⟨((2 * x ^ 2 : ℕ) : ℝ), ?_⟩
    rintro _ ⟨n', rfl⟩
    simp only
    by_cases hn'mem : n' ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}
    · rw [ciSup_pos hn'mem]
      obtain ⟨⟨hn'_pos, hn'_le_x⟩, m_w, hφm_w⟩ := hn'mem
      have hm_w_pos : 1 ≤ m_w := by
        rcases Nat.eq_zero_or_pos m_w with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφm_w
          omega
        · exact hpos
      set A' : Set ℕ := {m | Nat.totient m = n'} with hA'_def
      have hA'_ne : A'.Nonempty := ⟨m_w, hφm_w⟩
      have hA'_bdd : BddAbove A' := by
        refine ⟨2 * n' ^ 2, ?_⟩
        intro m hm
        have hm_pos : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · have : Nat.totient m = n' := hm
            rw [h0, Nat.totient_zero] at this
            omega
          · exact hpos
        exact totient_preimage_bound hm_pos hm
      set mmax' : ℕ := sSup A' with hmmax'_def
      set mmin' : ℕ := sInf A' with hmmin'_def
      have hmmax'_in : mmax' ∈ A' := Nat.sSup_mem hA'_ne hA'_bdd
      have hmmin'_in : mmin' ∈ A' := Nat.sInf_mem hA'_ne
      have hφmmax' : Nat.totient mmax' = n' := hmmax'_in
      have hφmmin' : Nat.totient mmin' = n' := hmmin'_in
      have hmmax'_pos : 1 ≤ mmax' := by
        rcases Nat.eq_zero_or_pos mmax' with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmax'
          omega
        · exact hpos
      have hmmin'_pos : 1 ≤ mmin' := by
        rcases Nat.eq_zero_or_pos mmin' with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmin'
          omega
        · exact hpos
      have hmmax'_le : mmax' ≤ 2 * n' ^ 2 := totient_preimage_bound hmmax'_pos hφmmax'
      have hmmax'_le_2xsq : mmax' ≤ 2 * x ^ 2 := by
        have : 2 * n' ^ 2 ≤ 2 * x ^ 2 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn'_le_x 2)
        omega
      -- (mmax' : ℝ) / mmin' ≤ mmax' (since mmin' ≥ 1)
      have hmmin'_pos_R : (0 : ℝ) < mmin' := by exact_mod_cast hmmin'_pos
      have hmmax'_nn_R : (0 : ℝ) ≤ mmax' := by exact_mod_cast Nat.zero_le _
      have h1' : (mmax' : ℝ) / mmin' ≤ mmax' := by
        rw [div_le_iff₀ hmmin'_pos_R]
        have : (1 : ℝ) ≤ (mmin' : ℝ) := by exact_mod_cast hmmin'_pos
        nlinarith
      have h2' : (mmax' : ℝ) ≤ ((2 * x ^ 2 : ℕ) : ℝ) := by exact_mod_cast hmmax'_le_2xsq
      linarith
    · rw [ciSup_neg hn'mem]
      simp only [Real.sSup_empty]
      exact_mod_cast Nat.zero_le _
  -- R x ≥ inner term at n.
  have hR_ge : (mmax : ℝ) / mmin ≤ R x := by
    unfold R
    have h_inner_eq :
        (⨆ (_ : n ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}),
            let mmax' := sSup {m | Nat.totient m = n}
            let mmin' := sInf {m | Nat.totient m = n}
            (mmax' : ℝ) / mmin') = (mmax : ℝ) / mmin :=
      ciSup_pos hn_in_idx
    rw [← h_inner_eq]
    exact le_ciSup hbdd_outer n
  exact le_trans hratio_ge hR_ge

theorem R_lower_bound :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      R x ≥ (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log x) := by
  intro ε hε
  filter_upwards [totient_collision_construction ε hε, Filter.eventually_ge_atTop 1]
    with x hx hx1
  obtain ⟨a, b, n, ha, hb, hn, hnx, hφa, hφb, hba⟩ := hx
  have hR_ge : (b : ℝ) / a ≤ R x :=
    R_ge_of_totient_collision ha hb hn hnx hφa hφb
  linarith

/-- **Theorem 2.1.** Combined upper and lower bounds give the asymptotic.

Squeeze argument: given `R_upper_bound` and `R_lower_bound` (both `∀ ε > 0, ∀ᶠ x, …`),
choose `ε = δ · e^γ / 2` for target `δ > 0`. Eventually
`(R x - e^γ log log x) / log log x ∈ [-ε, ε]`, so `R x / (e^γ log log x) - 1 ∈
[-δ/2, δ/2]`, giving `dist < δ`. -/
theorem totient_fibre_extremes :
    Tendsto
      (fun x : ℕ => R x / (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  set ε : ℝ := δ * γc / 2 with hε_def
  have hε_pos : 0 < ε := by positivity
  have hev := (R_upper_bound ε hε_pos).and
    ((R_lower_bound ε hε_pos).and (Filter.eventually_ge_atTop 3))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun x hxN => ?_⟩
  obtain ⟨hxu, hxl, hx3⟩ := hN x hxN
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hlogx_gt_one : 1 < Real.log x := by
    have hle : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3R
    have hexp_lt_three : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have hlog3 : 1 < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos _) hexp_lt_three
      simpa [Real.log_exp] using h
    linarith
  have hllogx_pos : 0 < Real.log (Real.log x) := Real.log_pos hlogx_gt_one
  set L : ℝ := Real.log (Real.log x) with hL_def
  have hdenom_pos : 0 < γc * L := mul_pos hγc_pos hllogx_pos
  rw [Real.dist_eq]
  have key : R x / (γc * L) - 1 = (R x - γc * L) / (γc * L) := by
    field_simp
  rw [key, abs_div, abs_of_pos hdenom_pos]
  have hub : R x - γc * L ≤ ε * L := by
    have h1 : (γc + ε) * L = γc * L + ε * L := by ring
    linarith
  have hlb : -(ε * L) ≤ R x - γc * L := by
    have h1 : (γc - ε) * L = γc * L - ε * L := by ring
    linarith
  have habs : |R x - γc * L| ≤ ε * L := abs_le.mpr ⟨hlb, hub⟩
  have hratio : |R x - γc * L| / (γc * L) ≤ ε * L / (γc * L) :=
    div_le_div_of_nonneg_right habs (le_of_lt hdenom_pos)
  have hsimp : ε * L / (γc * L) = ε / γc := by
    field_simp
  rw [hsimp] at hratio
  have hε_over_γc : ε / γc = δ / 2 := by
    rw [hε_def]
    field_simp
  rw [hε_over_γc] at hratio
  have hδ2_lt : δ / 2 < δ := by linarith
  exact lt_of_le_of_lt hratio hδ2_lt

/- ## Section 3 — Permanence observation

This section is **fully proved** — no sorries, no extra trusted inputs beyond Mathlib.
-/

/-- **Proposition 3.1 (Permanence).** If `φ(a) = φ(b) = n` with `a > b ≥ 1`, then
for every prime `r` coprime to `a*b`, the totient value `N_r := (r - 1) · n` has
both `r·a` and `r·b` as preimages, with ratio `r·a / (r·b) = a/b`.

In particular, since there are infinitely many primes coprime to any given `a*b`,
infinitely many distinct totient values achieve at least the ratio `a/b`. -/
theorem permanence_step (a b r : ℕ)
    (hab : Nat.totient a = Nat.totient b) (hr : Nat.Prime r) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b) :
    Nat.totient (r * a) = Nat.totient (r * b) := by
  have hcop_a : Nat.Coprime r a := (Nat.Prime.coprime_iff_not_dvd hr).mpr hra
  have hcop_b : Nat.Coprime r b := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrb
  rw [Nat.totient_mul hcop_a, Nat.totient_mul hcop_b, hab]

/-- **Proposition 3.1 (corollary, faithful to the PDF).**
If `1 ≤ b < a` and `φ(a) = φ(b)`, then there are infinitely many distinct
totient values `N` admitting a pair of preimages `(x, y)` with `y < x` and
`b · x ≥ a · y` (equivalently, `x / y ≥ a / b` in `ℚ` — and hence
`f_max(N) / f_min(N) ≥ a / b` since `f_max(N) ≥ x` and `f_min(N) ≤ y`).

This is the strict form of PDF Proposition 3.1: any nontrivial totient
collision propagates to infinitely many collisions of at least the same ratio. -/
theorem infinitely_many_collisions (a b : ℕ) (hb : 1 ≤ b) (hgt : b < a)
    (hab : Nat.totient a = Nat.totient b) :
    {N : ℕ | ∃ x y, Nat.totient x = N ∧ Nat.totient y = N ∧ y < x ∧ b * x ≥ a * y}.Infinite := by
  have ha : 1 ≤ a := lt_of_le_of_lt hb hgt |>.le
  -- Strategy: f r := (r - 1) * φ(a) is injective on primes ≥ 2, and for primes r
  -- coprime to a*b, the witnesses x = r*a, y = r*b satisfy (since r ≥ 2 and a > b)
  -- y = r*b < r*a = x and b*x = a*y. {primes not dividing a*b} is infinite.
  set S : Set ℕ := {N | ∃ x y, Nat.totient x = N ∧ Nat.totient y = N ∧ y < x ∧ b * x ≥ a * y}
  -- The set of primes coprime to a*b is infinite (primes infinite, divisors finite).
  have h_inf_good : {r : ℕ | r.Prime ∧ ¬ r ∣ (a * b)}.Infinite := by
    apply Set.Infinite.mono (s := {r | r.Prime} \ {r | r ∣ (a * b)})
    · intro r hr
      exact ⟨hr.1, hr.2⟩
    · refine Set.Infinite.sdiff Nat.infinite_setOfPred_prime ?_
      exact Set.Finite.subset (Set.finite_Icc 0 (a * b)) (fun r hr =>
        Set.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_of_dvd (Nat.mul_pos ha hb) hr⟩)
  -- Each such prime maps into S.
  have hmap : ∀ r ∈ {r : ℕ | r.Prime ∧ ¬ r ∣ (a * b)}, (r - 1) * Nat.totient a ∈ S := by
    rintro r ⟨hpr, hndvd⟩
    have hra : ¬ r ∣ a := fun h => hndvd (h.mul_right b)
    have hrb : ¬ r ∣ b := fun h => hndvd (Dvd.dvd.mul_left h a)
    have hcop_a : Nat.Coprime r a := (Nat.Prime.coprime_iff_not_dvd hpr).mpr hra
    have hcop_b : Nat.Coprime r b := (Nat.Prime.coprime_iff_not_dvd hpr).mpr hrb
    have hr2 : 2 ≤ r := hpr.two_le
    have hr_pos : 0 < r := by omega
    refine ⟨r * a, r * b, ?_, ?_, ?_, ?_⟩
    · rw [Nat.totient_mul hcop_a, Nat.totient_prime hpr]
    · rw [Nat.totient_mul hcop_b, Nat.totient_prime hpr, hab]
    · -- y = r*b < r*a = x because b < a and r > 0
      exact (Nat.mul_lt_mul_left hr_pos).mpr hgt
    · -- b * (r * a) = a * (r * b) — exact equality, hence ≥.
      ring_nf
      exact le_refl _
  -- f is injective on primes (since primes ≥ 2 and φ(a) > 0).
  have hφ_pos : 0 < Nat.totient a := Nat.totient_pos.mpr ha
  have hinj : Set.InjOn (fun r : ℕ => (r - 1) * Nat.totient a)
      {r : ℕ | r.Prime ∧ ¬ r ∣ (a * b)} := by
    rintro r ⟨hpr, _⟩ s ⟨hps, _⟩ heq
    simp only at heq
    have h2r : 2 ≤ r := hpr.two_le
    have h2s : 2 ≤ s := hps.two_le
    have : r - 1 = s - 1 := Nat.eq_of_mul_eq_mul_right hφ_pos heq
    omega
  exact (h_inf_good.image hinj).mono (Set.image_subset_iff.mpr hmap)

/-- **Asymptotic companion theorem (Section 4).**

PDF Theorem 2.1 in the natural `Tendsto` shape an asymptotic result requires.

Trust boundary: standard Lean axioms only. There are no `sorry`s in this file. -/
theorem erdos_694 :
    Tendsto
      (fun x : ℕ => R x /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) :=
  totient_fibre_extremes

end Erdos694

/-! ## Trust boundary audit

Every declaration below depends only on `propext`, `Classical.choice`, and
`Quot.sound`. The optional historical height lemma has an explicit hypothesis;
the final lower bound uses the unconditional dyadic-prime construction.
-/
#print axioms Erdos694.totient_sq_ge_half
#print axioms Erdos694.permanence_step
#print axioms Erdos694.infinitely_many_collisions
#print axioms Erdos694.LowerConstruction.totient_a_eq_totient_b
#print axioms Erdos694.landau_max_ratio
#print axioms Erdos694.R_upper_bound
#print axioms Erdos694.collision_at_height
#print axioms Erdos694.totient_collision_construction
#print axioms Erdos694.R_lower_bound
#print axioms Erdos694.totient_fibre_extremes
#print axioms Erdos694.erdos_694

alias _root_.Erdos694.erdos_694_asymptotic := _root_.Erdos694.erdos_694
