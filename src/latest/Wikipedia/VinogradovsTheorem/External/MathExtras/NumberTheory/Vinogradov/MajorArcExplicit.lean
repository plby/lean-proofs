/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Wikipedia.VinogradovsTheorem.External.MathExtras.NumberTheory.Vinogradov.CircleMethod
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Explicit Major Arcs

This module is the planned home for the fixed major-arc approximation used to
replace the current weak existential major-arc interfaces.

Target contents:

* Ramanujan/Gauss sums attached to major-arc centers;
* totient-normalized main terms;
* truncated singular-series estimates;
* explicit major-arc lower and error bounds.
-/

namespace Vinogradov

open MeasureTheory Finset

/-! ## Rational centers and elementary arc geometry -/

/-- The real rational point attached to a numerator-denominator pair. -/
noncomputable def rationalCenter (a q : ℕ) : ℝ :=
  (a : ℝ) / (q : ℝ)

/-- The elementary radius used by the current major-arc definition. -/
noncomputable def majorArcRadius (N q : ℕ) : ℝ :=
  1 / ((q : ℝ) * N)

/-- Analytic-grade major-arc cutoff.  This is now narrowed to the checked
Siegel-Walfisz-scale placeholder used by the AP-PNT bridge. -/
def majorArcAnalyticCutoff (n : ℕ) : ℕ := Nat.log 2 n

/-- Siegel-Walfisz scale major-arc cutoff candidate. The current checked
placeholder is a single polylogarithmic scale; it is intended to be replaced by
`floor(exp(sqrt(log n / log log n)))` once the analytic chain is in place. -/
def swMajorArcCutoff (n : ℕ) : ℕ := Nat.log 2 n

/-- The current analytic major-arc cutoff is exactly the checked
Siegel-Walfisz-scale cutoff. -/
theorem majorArcAnalyticCutoff_eq_swMajorArcCutoff (n : ℕ) :
    majorArcAnalyticCutoff n = swMajorArcCutoff n := by
  rfl

/-- Membership in the current analytic major-arc center set is the same as
membership in the SW-cutoff center set. -/
theorem majorArcCenters_analyticCutoff_iff_swCutoff {N a q : ℕ} :
    (a, q) ∈ majorArcCenters (majorArcAnalyticCutoff N) ↔
      (a, q) ∈ majorArcCenters (swMajorArcCutoff N) := by
  rw [majorArcAnalyticCutoff_eq_swMajorArcCutoff]


private lemma three_mul_add_two_lt_two_pow_succ_aux (t : ℕ) :
    3 * (t + 3) + 2 < 2 ^ (t + 3 + 1) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hlin : 3 * (t + 1 + 3) + 2 < 2 * (3 * (t + 3) + 2) := by
        omega
      have hpow : 2 * (3 * (t + 3) + 2) ≤ 2 * 2 ^ (t + 3 + 1) := by
        exact Nat.mul_le_mul_left 2 ih.le
      have hpow_succ : 2 * 2 ^ (t + 3 + 1) = 2 ^ (t + 1 + 3 + 1) := by
        ring_nf
      exact lt_of_lt_of_le hlin (hpow.trans_eq hpow_succ)

private lemma three_mul_add_two_lt_two_pow_succ {k : ℕ} (hk : 3 ≤ k) :
    3 * k + 2 < 2 ^ (k + 1) := by
  have h := three_mul_add_two_lt_two_pow_succ_aux (k - 3)
  have hk_eq : k - 3 + 3 = k := Nat.sub_add_cancel hk
  simpa [hk_eq] using h

private lemma self_lt_two_pow_div_three_succ {n : ℕ} (hn : 9 ≤ n) :
    n < 2 ^ (n / 3 + 1) := by
  have hk : 3 ≤ n / 3 := by omega
  have hmod : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  have hdecomp : 3 * (n / 3) + n % 3 = n := Nat.div_add_mod n 3
  have hle : n ≤ 3 * (n / 3) + 2 := by omega
  exact lt_of_le_of_lt hle (three_mul_add_two_lt_two_pow_succ hk)

private lemma two_mul_add_one_lt_two_pow_succ_aux (t : ℕ) :
    2 * (t + 2) + 1 < 2 ^ (t + 2 + 1) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hlin : 2 * (t + 1 + 2) + 1 < 2 * (2 * (t + 2) + 1) := by
        omega
      have hpow : 2 * (2 * (t + 2) + 1) ≤ 2 * 2 ^ (t + 2 + 1) := by
        exact Nat.mul_le_mul_left 2 ih.le
      have hpow_succ : 2 * 2 ^ (t + 2 + 1) = 2 ^ (t + 1 + 2 + 1) := by
        ring_nf
      exact lt_of_lt_of_le hlin (hpow.trans_eq hpow_succ)

private lemma two_mul_add_one_lt_two_pow_succ {k : ℕ} (hk : 2 ≤ k) :
    2 * k + 1 < 2 ^ (k + 1) := by
  have h := two_mul_add_one_lt_two_pow_succ_aux (k - 2)
  have hk_eq : k - 2 + 2 = k := Nat.sub_add_cancel hk
  simpa [hk_eq] using h

private lemma self_lt_two_pow_div_two_succ {n : ℕ} (hn : 4 ≤ n) :
    n < 2 ^ (n / 2 + 1) := by
  have hk : 2 ≤ n / 2 := by omega
  have hmod : n % 2 < 2 := Nat.mod_lt n (by norm_num)
  have hdecomp : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  have hle : n ≤ 2 * (n / 2) + 1 := by omega
  exact lt_of_le_of_lt hle (two_mul_add_one_lt_two_pow_succ hk)

/-- For `n ≥ 9`, the SW cutoff candidate is bounded by the analytic cutoff. -/
theorem swMajorArcCutoff_le_majorArcAnalyticCutoff_of_nine {n : ℕ} (_hn : 9 ≤ n) :
    swMajorArcCutoff n ≤ majorArcAnalyticCutoff n := by
  unfold swMajorArcCutoff majorArcAnalyticCutoff
  omega


/-- The analytic cutoff lies in the disjoint local-arc range. -/
theorem two_mul_majorArcAnalyticCutoff_le (n : ℕ) :
    2 * majorArcAnalyticCutoff n ≤ n := by
  unfold majorArcAnalyticCutoff
  by_cases hn : n < 4
  · interval_cases n <;> norm_num
  · have hn4 : 4 ≤ n := by omega
    have hn0 : n ≠ 0 := by omega
    have hlog_lt : Nat.log 2 n < n / 2 + 1 :=
      Nat.log_lt_of_lt_pow hn0 (self_lt_two_pow_div_two_succ hn4)
    omega

/-- The analytic cutoff is bounded by the ambient scale. -/
theorem majorArcAnalyticCutoff_le_self (n : ℕ) :
    majorArcAnalyticCutoff n ≤ n := by
  unfold majorArcAnalyticCutoff
  exact Nat.log_le_self 2 n

/-- For `n ≥ 3`, the analytic cutoff is nontrivial. -/
theorem one_le_majorArcAnalyticCutoff {n : ℕ} (hn : 3 ≤ n) :
    1 ≤ majorArcAnalyticCutoff n := by
  unfold majorArcAnalyticCutoff
  exact Nat.succ_le_of_lt (Nat.log_pos Nat.one_lt_two (by omega))


theorem majorArcCenters_q_le {Q a q : ℕ} (h : (a, q) ∈ majorArcCenters Q) :
    q ≤ Q := h.1

theorem majorArcCenters_q_ne_zero {Q a q : ℕ} (h : (a, q) ∈ majorArcCenters Q) :
    q ≠ 0 := h.2.1

theorem majorArcCenters_q_pos {Q a q : ℕ} (h : (a, q) ∈ majorArcCenters Q) :
    0 < q :=
  Nat.pos_of_ne_zero (majorArcCenters_q_ne_zero h)


theorem majorArcCenters_a_lt_q {Q a q : ℕ} (h : (a, q) ∈ majorArcCenters Q) :
    a < q := h.2.2.1


theorem majorArcCenters_coprime {Q a q : ℕ} (h : (a, q) ∈ majorArcCenters Q) :
    Nat.Coprime a q := h.2.2.2

theorem majorArcCenters_mono {Q Q' a q : ℕ} (hQ : Q ≤ Q')
    (h : (a, q) ∈ majorArcCenters Q) :
    (a, q) ∈ majorArcCenters Q' :=
  ⟨le_trans h.1 hQ, h.2.1, h.2.2.1, h.2.2.2⟩


theorem zero_one_mem_majorArcCenters {Q : ℕ} (hQ : 1 ≤ Q) :
    (0, 1) ∈ majorArcCenters Q := by
  exact ⟨hQ, by decide, by decide, Nat.coprime_one_right 0⟩


@[simp] theorem rationalCenter_self_zero (q : ℕ) : rationalCenter 0 q = 0 := by
  simp [rationalCenter]


theorem exists_center_of_mem_majorArcs {N Q : ℕ} {α : ℝ}
    (hα : α ∈ majorArcs N Q) :
    ∃ a q : ℕ, (a, q) ∈ majorArcCenters Q ∧
      |α - rationalCenter a q| < majorArcRadius N q :=
  hα.2


theorem not_mem_majorArcs_of_mem_minorArcs {N Q : ℕ} {α : ℝ}
    (hα : α ∈ minorArcs N Q) : α ∉ majorArcs N Q :=
  hα.2


theorem majorArcs_not_minorArcs {N Q : ℕ} {α : ℝ}
    (hα : α ∈ majorArcs N Q) : α ∉ minorArcs N Q := by
  intro hminor
  exact hminor.2 hα


/-- Local major arc around the rational `a/q`. -/
noncomputable def localMajorArcExplicit (N a q : ℕ) : Set ℝ :=
  { α | α ∈ Set.Icc (0 : ℝ) 1 ∧ |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * N) }

theorem mem_localMajorArcExplicit_iff {N a q : ℕ} {α : ℝ} :
    α ∈ localMajorArcExplicit N a q ↔
      α ∈ Set.Icc (0 : ℝ) 1 ∧ |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * N) := by
  unfold localMajorArcExplicit; rfl

theorem localMajorArcExplicit_subset_Icc (N a q : ℕ) :
    localMajorArcExplicit N a q ⊆ Set.Icc (0 : ℝ) 1 := fun _ h => h.1

/-- `majorArcs N Q` is the union of `localMajorArcExplicit N a q` over centers. -/
theorem majorArcs_eq_iUnion_localMajorArcExplicit (N Q : ℕ) :
    majorArcs N Q =
      ⋃ aq ∈ majorArcCenters Q, localMajorArcExplicit N aq.1 aq.2 := by
  ext α
  constructor
  · rintro ⟨h1, a, q, h2, h3⟩
    simp only [Set.mem_iUnion]
    exact ⟨(a, q), h2, h1, h3⟩
  · intro hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨⟨a, q⟩, h2, h1, h3⟩ := hmem
    exact ⟨h1, a, q, h2, h3⟩


theorem localMajorArcExplicit_eq_inter_Icc_open (N a q : ℕ) :
    localMajorArcExplicit N a q =
      Set.Icc (0 : ℝ) 1 ∩
        { α | |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * N) } := by
  ext α
  rw [mem_localMajorArcExplicit_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩

/-- Local arcs are measurable. -/
theorem localMajorArcExplicit_measurableSet (N a q : ℕ) :
    MeasurableSet (localMajorArcExplicit N a q) := by
  rw [localMajorArcExplicit_eq_inter_Icc_open]
  refine measurableSet_Icc.inter ?_
  exact (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet

/-- Local arcs have finite Lebesgue measure (they are subsets of `[0, 1]`). -/
theorem localMajorArcExplicit_volume_le_one (N a q : ℕ) :
    (MeasureTheory.volume (localMajorArcExplicit N a q) : ENNReal) ≤ 1 := by
  have h : MeasureTheory.volume (localMajorArcExplicit N a q) ≤
           MeasureTheory.volume (Set.Icc (0 : ℝ) 1) :=
    MeasureTheory.measure_mono (localMajorArcExplicit_subset_Icc N a q)
  rw [Real.volume_Icc] at h
  simpa using h


@[simp]
theorem localMajorArcExplicit_zero_q (N a : ℕ) :
    localMajorArcExplicit N a 0 = ∅ := by
  ext α
  simp only [localMajorArcExplicit, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro ⟨_, hclose⟩
  push_cast at hclose
  simp at hclose
  exact absurd hclose (not_lt.mpr (abs_nonneg _))

/-! ## Ramanujan / Gauss sums attached to a denominator -/

/-- The Ramanujan-style Gauss sum
`c_q(n) = ∑_{a=1, gcd(a,q)=1}^{q} e(an/q)`.

We sum over `a ∈ Finset.Ico 1 (q+1)` filtered by `Nat.Coprime a q`. For `q = 0`
the sum is empty (the `Ico 1 1` index range is empty), giving `c_0(n) = 0`. -/
noncomputable def gaussSum (q n : ℕ) : ℂ :=
  ∑ a ∈ (Finset.Ico 1 (q + 1)).filter (fun a => Nat.Coprime a q),
    addChar ((n : ℝ) / (q : ℝ)) a

@[simp] theorem gaussSum_zero_q (n : ℕ) : gaussSum 0 n = 0 := by
  simp [gaussSum]

@[simp] theorem gaussSum_one (n : ℕ) : gaussSum 1 n = 1 := by
  unfold gaussSum
  have hset : (Finset.Ico 1 (1 + 1)).filter (fun a => Nat.Coprime a 1) = {1} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    refine ⟨fun ⟨ha, _⟩ => by omega, fun ha => ?_⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    subst ha; decide
  rw [hset, Finset.sum_singleton]
  have hα : ((n : ℝ) / (1 : ℕ)) = 0 + (n : ℕ) := by push_cast; ring
  rw [hα, addChar_add_nat]
  simp

/-- The Ramanujan sum, in the standard residues-mod-`q` convention:
`c_q(n) = ∑_{a ∈ ℤ/qℤ, gcd(a,q)=1} e(an/q)`.

We sum over `a ∈ Finset.range q` filtered by `Nat.Coprime a q`. For `q ≤ 1`
the filtered set agrees with the `Ico 1 (q+1)` convention used by `gaussSum`
(both empty for `q = 0`; both equal to one nonzero contribution for `q = 1`).
For `q ≥ 2`, `0` is excluded by the coprimality filter (since `gcd(0,q) = q ≥ 2`)
and `q` is excluded similarly, so both index sets give the same sum. -/
noncomputable def ramanujanSum (q n : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    addChar ((n : ℝ) / (q : ℝ)) a

@[simp] theorem ramanujanSum_zero_q (n : ℕ) : ramanujanSum 0 n = 0 := by
  simp [ramanujanSum]


private def ramanujanCrtMap (q₁ q₂ : ℕ) (p : ℕ × ℕ) : ℕ :=
  (p.1 * q₂ + p.2 * q₁) % (q₁ * q₂)

private theorem ramanujanCrtMap_mem {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hcop : q₁.Coprime q₂) {p : ℕ × ℕ}
    (hp : p ∈ ((Finset.range q₁).filter (fun a => Nat.Coprime a q₁) ×ˢ
        (Finset.range q₂).filter (fun b => Nat.Coprime b q₂) : Finset (ℕ × ℕ))) :
    ramanujanCrtMap q₁ q₂ p ∈ (Finset.range (q₁ * q₂)).filter
      (fun x => Nat.Coprime x (q₁ * q₂)) := by
  rcases p with ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hp ⊢
  constructor
  · exact Nat.mod_lt _ (Nat.mul_pos hq₁ hq₂)
  · have hExpr : (a * q₂ + b * q₁).Coprime (q₁ * q₂) := by
      rw [Nat.coprime_mul_iff_right]
      constructor
      · have hdrop : (a * q₂ + b * q₁).Coprime q₁ ↔ (a * q₂).Coprime q₁ := by
          exact Nat.add_coprime_iff_left (show q₁ ∣ b * q₁ by exact ⟨b, by rw [mul_comm]⟩)
        rw [hdrop, Nat.coprime_mul_iff_left]
        exact ⟨hp.1.2, hcop.symm⟩
      · have hdrop : (a * q₂ + b * q₁).Coprime q₂ ↔ (b * q₁).Coprime q₂ := by
          exact Nat.add_coprime_iff_right (show q₂ ∣ a * q₂ by exact ⟨a, by rw [mul_comm]⟩)
        rw [hdrop, Nat.coprime_mul_iff_left]
        exact ⟨hp.2.2, hcop⟩
    have hmod := Nat.mod_modEq (a * q₂ + b * q₁) (q₁ * q₂)
    exact Nat.coprime_iff_gcd_eq_one.mpr (by
      rw [ramanujanCrtMap, hmod.gcd_eq]
      exact Nat.coprime_iff_gcd_eq_one.mp hExpr)

private theorem ramanujanCrtMap_inj {q₁ q₂ : ℕ} (hcop : q₁.Coprime q₂) :
    Set.InjOn (ramanujanCrtMap q₁ q₂)
      (((Finset.range q₁).filter (fun a => Nat.Coprime a q₁) ×ˢ
        (Finset.range q₂).filter (fun b => Nat.Coprime b q₂) : Finset (ℕ × ℕ)) :
          Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  rcases x with ⟨a, b⟩
  rcases y with ⟨a', b'⟩
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx hy
  have hmodeqM : a * q₂ + b * q₁ ≡ a' * q₂ + b' * q₁ [MOD q₁ * q₂] := by
    have h1 := (Nat.mod_modEq (a * q₂ + b * q₁) (q₁ * q₂)).symm
    have h2 := Nat.mod_modEq (a' * q₂ + b' * q₁) (q₁ * q₂)
    have heq : (a * q₂ + b * q₁) % (q₁ * q₂) =
        (a' * q₂ + b' * q₁) % (q₁ * q₂) := by
      simpa [ramanujanCrtMap] using hxy
    have hmods : (a * q₂ + b * q₁) % (q₁ * q₂) ≡
        (a' * q₂ + b' * q₁) % (q₁ * q₂) [MOD q₁ * q₂] := by
      rw [heq]
    exact (h1.trans hmods).trans h2
  have hmodeq1 : a * q₂ + b * q₁ ≡ a' * q₂ + b' * q₁ [MOD q₁] :=
    hmodeqM.of_dvd (dvd_mul_right q₁ q₂)
  have htail1 : b * q₁ ≡ b' * q₁ [MOD q₁] := by
    have hb0 : b * q₁ ≡ 0 [MOD q₁] := Nat.modEq_zero_iff_dvd.mpr ⟨b, by rw [mul_comm]⟩
    have hb'0 : b' * q₁ ≡ 0 [MOD q₁] := Nat.modEq_zero_iff_dvd.mpr ⟨b', by rw [mul_comm]⟩
    exact hb0.trans hb'0.symm
  have ha_mul : a * q₂ ≡ a' * q₂ [MOD q₁] := htail1.add_right_cancel hmodeq1
  have ha_modeq : a ≡ a' [MOD q₁] :=
    Nat.ModEq.cancel_right_of_coprime (Nat.coprime_iff_gcd_eq_one.mp hcop) ha_mul
  have haeq : a = a' := Nat.ModEq.eq_of_lt_of_lt ha_modeq hx.1.1 hy.1.1
  have hmodeq2 : a * q₂ + b * q₁ ≡ a' * q₂ + b' * q₁ [MOD q₂] :=
    hmodeqM.of_dvd (by rw [mul_comm]; exact dvd_mul_right q₂ q₁)
  have htail2 : a * q₂ ≡ a' * q₂ [MOD q₂] := by
    have ha0 : a * q₂ ≡ 0 [MOD q₂] := Nat.modEq_zero_iff_dvd.mpr ⟨a, by rw [mul_comm]⟩
    have ha'0 : a' * q₂ ≡ 0 [MOD q₂] := Nat.modEq_zero_iff_dvd.mpr ⟨a', by rw [mul_comm]⟩
    exact ha0.trans ha'0.symm
  have hb_mul : b * q₁ ≡ b' * q₁ [MOD q₂] := htail2.add_left_cancel hmodeq2
  have hb_modeq : b ≡ b' [MOD q₂] :=
    Nat.ModEq.cancel_right_of_coprime (Nat.coprime_iff_gcd_eq_one.mp hcop.symm) hb_mul
  have hbeq : b = b' := Nat.ModEq.eq_of_lt_of_lt hb_modeq hx.2.1 hy.2.1
  subst haeq
  subst hbeq
  rfl

private theorem addChar_mul_div_mul {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (n a b : ℕ) :
    addChar ((n : ℝ) / (q₁ : ℝ)) a *
        addChar ((n : ℝ) / (q₂ : ℝ)) b =
      addChar ((n : ℝ) / ((q₁ * q₂ : ℕ) : ℝ)) (a * q₂ + b * q₁) := by
  unfold addChar
  rw [← Complex.exp_add]
  congr 1
  have hq₁c : (q₁ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq₁
  have hq₂c : (q₂ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq₂
  push_cast
  field_simp [hq₁c, hq₂c]

private theorem addChar_mod_eq {M : ℕ} (hM : 0 < M) (n x : ℕ) :
    addChar ((n : ℝ) / (M : ℝ)) (x % M) =
      addChar ((n : ℝ) / (M : ℝ)) x := by
  unfold addChar
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  have hxC : (x : ℂ) = (M : ℂ) * ((x / M : ℕ) : ℂ) + ((x % M : ℕ) : ℂ) := by
    exact_mod_cast (Nat.div_add_mod x M).symm
  have harg :
      2 * Real.pi * Complex.I * (x : ℂ) * (((n : ℝ) / (M : ℝ) : ℝ) : ℂ) =
        2 * Real.pi * Complex.I * ((x % M : ℕ) : ℂ) *
            (((n : ℝ) / (M : ℝ) : ℝ) : ℂ) +
          ((n * (x / M) : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hxC]
    push_cast
    field_simp [hMc]
    ring
  rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I]
  simp [mul_comm]

private theorem coprime_filter_card (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = Nat.totient q := by
  simpa [Nat.coprime_comm] using (Nat.totient_eq_card_coprime q).symm

private theorem ramanujanSum_mul_of_coprime_for_moebius {q₁ q₂ : ℕ}
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hcop : q₁.Coprime q₂) (n : ℕ) :
    ramanujanSum (q₁ * q₂) n =
      ramanujanSum q₁ n * ramanujanSum q₂ n := by
  classical
  let s₁ := (Finset.range q₁).filter (fun a => Nat.Coprime a q₁)
  let s₂ := (Finset.range q₂).filter (fun b => Nat.Coprime b q₂)
  let s := (s₁ ×ˢ s₂ : Finset (ℕ × ℕ))
  let t := (Finset.range (q₁ * q₂)).filter (fun x => Nat.Coprime x (q₁ * q₂))
  have hinj : Set.InjOn (ramanujanCrtMap q₁ q₂) (s : Set (ℕ × ℕ)) := by
    simpa [s, s₁, s₂] using ramanujanCrtMap_inj (q₁ := q₁) (q₂ := q₂) hcop
  have hmaps : ∀ p ∈ s, ramanujanCrtMap q₁ q₂ p ∈ t := by
    intro p hp
    simpa [s, s₁, s₂, t] using ramanujanCrtMap_mem (q₁ := q₁) (q₂ := q₂)
      hq₁ hq₂ hcop (p := p) (by simpa [s, s₁, s₂] using hp)
  have hcard : s.card = t.card := by
    simp [s, s₁, s₂, t, Finset.card_product, coprime_filter_card, Nat.totient_mul hcop]
  have hsurj : Set.SurjOn (ramanujanCrtMap q₁ q₂) (s : Set (ℕ × ℕ)) (t : Set ℕ) := by
    intro x hx
    have himg_eq : s.image (ramanujanCrtMap q₁ q₂) = t := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
        exact hmaps p hp
      · rw [Finset.card_image_of_injOn hinj]
        exact hcard.ge
    have hximg : x ∈ s.image (ramanujanCrtMap q₁ q₂) := by simpa [himg_eq] using hx
    rcases Finset.mem_image.mp hximg with ⟨p, hp, hpmap⟩
    exact ⟨p, hp, hpmap⟩
  unfold ramanujanSum
  rw [Finset.sum_mul_sum]
  have hprod :
      (∑ i ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          ∑ j ∈ (Finset.range q₂).filter (fun b => Nat.Coprime b q₂),
            addChar ((n : ℝ) / (q₁ : ℝ)) i *
              addChar ((n : ℝ) / (q₂ : ℝ)) j) =
        ∑ p ∈ s, addChar ((n : ℝ) / (q₁ : ℝ)) p.1 *
          addChar ((n : ℝ) / (q₂ : ℝ)) p.2 := by
    simpa [s, s₁, s₂] using
      (Finset.sum_product s₁ s₂
        (fun p : ℕ × ℕ => addChar ((n : ℝ) / (q₁ : ℝ)) p.1 *
          addChar ((n : ℝ) / (q₂ : ℝ)) p.2)).symm
  rw [hprod]
  change (∑ a ∈ t, addChar ((n : ℝ) / (((q₁ * q₂ : ℕ) : ℝ))) a) =
    ∑ p ∈ s, addChar ((n : ℝ) / (q₁ : ℝ)) p.1 *
      addChar ((n : ℝ) / (q₂ : ℝ)) p.2
  symm
  refine Finset.sum_nbij (ramanujanCrtMap q₁ q₂) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [s₁, s₂, t] using hmaps p (by simpa [s, s₁, s₂] using hp)
  · simpa [s₁, s₂] using hinj
  · simpa [s₁, s₂, t] using hsurj
  · intro p hp
    rcases p with ⟨a, b⟩
    have hmul := addChar_mul_div_mul (q₁ := q₁) (q₂ := q₂) hq₁ hq₂ n a b
    have hmod := addChar_mod_eq (M := q₁ * q₂) (Nat.mul_pos hq₁ hq₂) n
      (a * q₂ + b * q₁)
    rw [hmul]
    simpa [ramanujanCrtMap, Nat.cast_mul] using hmod.symm

private theorem ramanujan_filter_not_coprime_prime {p : ℕ} (hp : p.Prime) :
    (Finset.range p).filter (fun a => ¬ Nat.Coprime a p) = {0} := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨ha_lt, hnot⟩
    have hpdvd : p ∣ a := by
      exact (hp.dvd_iff_not_coprime).mpr (by simpa [Nat.coprime_comm] using hnot)
    rcases hpdvd with ⟨k, rfl⟩
    by_cases hk : k = 0
    · simp [hk]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have : p ≤ p * k := Nat.le_mul_of_pos_right p hkpos
      omega
  · intro ha
    subst ha
    exact ⟨hp.pos, by simp [Nat.coprime_comm, hp.ne_one]⟩

private theorem addChar_eq_pow (α : ℝ) (a : ℕ) :
    addChar α a = addChar α 1 ^ a := by
  unfold addChar
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem addChar_nat_div_eq_mod (p n a : ℕ) (hp0 : p ≠ 0) :
    addChar ((n : ℝ) / (p : ℝ)) a =
      addChar (((n % p : ℕ) : ℝ) / (p : ℝ)) a := by
  have hp0r : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
  have hcast :
      (n : ℝ) = (p : ℝ) * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod n p).symm
  have hα :
      (n : ℝ) / (p : ℝ) =
        ((n % p : ℕ) : ℝ) / (p : ℝ) + ((n / p : ℕ) : ℝ) := by
    rw [hcast]
    field_simp [hp0r]
    ring
  rw [hα]
  rw [addChar_add_nat]

private theorem ramanujan_full_sum_prime_dvd {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    (∑ a ∈ Finset.range p, addChar ((n : ℝ) / (p : ℝ)) a) = (p : ℂ) := by
  rcases hpn with ⟨k, rfl⟩
  have hp0r : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hα : (((p * k : ℕ) : ℝ) / (p : ℝ)) = (0 : ℝ) + k := by
    rw [Nat.cast_mul]
    field_simp [hp0r]
    ring
  calc
    (∑ a ∈ Finset.range p, addChar (((p * k : ℕ) : ℝ) / (p : ℝ)) a)
        = ∑ a ∈ Finset.range p, addChar ((0 : ℝ) + k) a := by rw [hα]
    _ = ∑ _a ∈ Finset.range p, (1 : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [addChar_add_nat]
          simp
    _ = (p : ℂ) := by simp

private theorem ramanujan_full_sum_prime_not_dvd {p n : ℕ}
    (hp : p.Prime) (hndvd : ¬ p ∣ n) :
    (∑ a ∈ Finset.range p, addChar ((n : ℝ) / (p : ℝ)) a) = 0 := by
  let i : ℕ := n % p
  have hi_ne_zero : i ≠ 0 := by
    intro hi
    exact hndvd ((Nat.dvd_iff_mod_eq_zero).mpr hi)
  have hi_lt : i < p := Nat.mod_lt n hp.pos
  have hnot_p_dvd_i : ¬ p ∣ i := by
    intro hpi
    rcases hpi with ⟨k, hk⟩
    by_cases hk0 : k = 0
    · subst hk0
      simp at hk
      exact hi_ne_zero hk
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hp_le : p ≤ p * k := Nat.le_mul_of_pos_right p hkpos
      omega
  have hcop : i.Coprime p := (hp.coprime_iff_not_dvd.mpr hnot_p_dvd_i).symm
  set ζ : ℂ := addChar (((i : ℕ) : ℝ) / (p : ℝ)) 1 with hζdef
  have hζprim : IsPrimitiveRoot ζ p := by
    rw [hζdef]
    unfold addChar
    convert Complex.isPrimitiveRoot_exp_of_coprime i p hp.ne_zero hcop using 1
    push_cast
    ring_nf
  calc
    (∑ a ∈ Finset.range p, addChar ((n : ℝ) / (p : ℝ)) a)
        = ∑ a ∈ Finset.range p, addChar (((i : ℕ) : ℝ) / (p : ℝ)) a := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact addChar_nat_div_eq_mod p n a hp.ne_zero
    _ = ∑ a ∈ Finset.range p, ζ ^ a := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          simpa [hζdef] using addChar_eq_pow (((i : ℕ) : ℝ) / (p : ℝ)) a
    _ = 0 := hζprim.geom_sum_eq_zero hp.one_lt

theorem ramanujanSum_prime_for_moebius {p n : ℕ} (hp : p.Prime) :
    ramanujanSum p n = if p ∣ n then ((p - 1 : ℕ) : ℂ) else (-1 : ℂ) := by
  unfold ramanujanSum
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range p)
      (fun a => Nat.Coprime a p) (fun a => addChar ((n : ℝ) / (p : ℝ)) a)
    have hnot : (∑ x ∈ Finset.range p with ¬ Nat.Coprime x p,
        addChar ((n : ℝ) / (p : ℝ)) x) = 1 := by
      rw [ramanujan_filter_not_coprime_prime hp]
      simp
    have hfull := ramanujan_full_sum_prime_dvd hp hpn
    rw [hnot, hfull] at hsplit
    have hp1 : 1 ≤ p := hp.one_lt.le
    calc
      (∑ x ∈ Finset.range p with Nat.Coprime x p,
          addChar ((n : ℝ) / (p : ℝ)) x) = (p : ℂ) - 1 := by
            rw [← hsplit]
            ring
      _ = ((p - 1 : ℕ) : ℂ) := by
            norm_num [Nat.cast_sub hp1]
  · rw [if_neg hpn]
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range p)
      (fun a => Nat.Coprime a p) (fun a => addChar ((n : ℝ) / (p : ℝ)) a)
    have hnot : (∑ x ∈ Finset.range p with ¬ Nat.Coprime x p,
        addChar ((n : ℝ) / (p : ℝ)) x) = 1 := by
      rw [ramanujan_filter_not_coprime_prime hp]
      simp
    have hfull := ramanujan_full_sum_prime_not_dvd hp hpn
    rw [hnot, hfull] at hsplit
    calc
      (∑ x ∈ Finset.range p with Nat.Coprime x p,
          addChar ((n : ℝ) / (p : ℝ)) x)
          = (∑ x ∈ Finset.range p with Nat.Coprime x p,
              addChar ((n : ℝ) / (p : ℝ)) x) + 1 - 1 := by ring
      _ = 0 - 1 := by rw [hsplit]
      _ = -1 := by ring

private theorem full_addChar_sum_prime_pow_eq_zero_of_coprime
    {p k a : ℕ} (hp : p.Prime) (hk : 0 < k) (hcop : Nat.Coprime a (p ^ k)) :
    (∑ x ∈ Finset.range (p ^ k),
        addChar ((a : ℝ) / ((p ^ k : ℕ) : ℝ)) x) = 0 := by
  set ζ : ℂ := addChar ((a : ℝ) / ((p ^ k : ℕ) : ℝ)) 1 with hζdef
  have hpk_ne : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hζprim : IsPrimitiveRoot ζ (p ^ k) := by
    rw [hζdef]
    unfold addChar
    convert Complex.isPrimitiveRoot_exp_of_coprime a (p ^ k) hpk_ne hcop using 1
    push_cast
    ring_nf
  have hpk_gt : 1 < p ^ k := by
    exact Nat.one_lt_pow hk.ne' hp.one_lt
  calc
    (∑ x ∈ Finset.range (p ^ k),
        addChar ((a : ℝ) / ((p ^ k : ℕ) : ℝ)) x)
        = ∑ x ∈ Finset.range (p ^ k), ζ ^ x := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          simpa [hζdef] using
            addChar_eq_pow
              ((a : ℝ) / ((p ^ k : ℕ) : ℝ)) x
    _ = 0 := hζprim.geom_sum_eq_zero hpk_gt

private theorem addChar_prime_pow_succ_mul_prime (p j a y : ℕ) (hp : p ≠ 0) :
    addChar ((a : ℝ) / ((p ^ (j + 1) : ℕ) : ℝ)) (p * y) =
      addChar ((a : ℝ) / ((p ^ j : ℕ) : ℝ)) y := by
  unfold addChar
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hpjC : ((p ^ j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero j hp)
  congr 1
  push_cast
  field_simp [hpC, hpjC, pow_succ]
  ring

private theorem ramanujanSum_prime_pow_succ_succ_eq_zero
    {p j a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime a (p ^ (j + 2))) :
    ramanujanSum (p ^ (j + 2)) a = 0 := by
  let m := p ^ (j + 2)
  let m' := p ^ (j + 1)
  let F : ℕ → ℂ := fun x => addChar ((a : ℝ) / (m : ℝ)) x
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range m)
    (fun x => Nat.Coprime x m) F
  have hfull : (∑ x ∈ Finset.range m, F x) = 0 := by
    simpa [m, F] using
      full_addChar_sum_prime_pow_eq_zero_of_coprime (p := p) (k := j + 2)
        (a := a) hp (by omega) hcop
  have hnon :
      (∑ x ∈ Finset.range m with ¬ Nat.Coprime x m, F x) = 0 := by
    have hsum :
        (∑ x ∈ Finset.range m with ¬ Nat.Coprime x m, F x) =
          ∑ y ∈ Finset.range m',
            addChar ((a : ℝ) / (m' : ℝ)) y := by
      symm
      refine Finset.sum_bij (fun y _hy => p * y) ?_ ?_ ?_ ?_
      · intro y hy
        have hylt : y < m' := Finset.mem_range.mp hy
        have hlt : p * y < m := by
          have := Nat.mul_lt_mul_of_pos_left hylt hp.pos
          simpa [m, m', pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
        have hnot : ¬ Nat.Coprime (p * y) m :=
          Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_mul_right p y) (by
            dsimp [m]
            exact ⟨p ^ (j + 1), by rw [pow_succ]; ring⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hnot⟩
      · intro y₁ _hy₁ y₂ _hy₂ hmul
        exact Nat.mul_left_cancel hp.pos hmul
      · intro x hx
        have hx_range : x < m := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
        have hx_not : ¬ Nat.Coprime x m := (Finset.mem_filter.mp hx).2
        have hpx : p ∣ x := by
          exact (hp.dvd_iff_not_coprime).mpr (by
            have hx_not_p : ¬ Nat.Coprime x p := by
              intro hxp
              exact hx_not ((Nat.coprime_pow_right_iff (by omega : 0 < j + 2) x p).mpr hxp)
            simpa [Nat.coprime_comm] using hx_not_p)
        rcases hpx with ⟨y, rfl⟩
        have hylt : y < m' := by
          have hlt : p * y < p * m' := by
            simpa [m, m', pow_succ, mul_comm, mul_left_comm, mul_assoc] using hx_range
          exact (Nat.mul_lt_mul_left hp.pos).mp hlt
        exact ⟨y, Finset.mem_range.mpr hylt, rfl⟩
      · intro y _hy
        simpa [F, m, m', Nat.cast_pow] using
          (addChar_prime_pow_succ_mul_prime p (j + 1) a y hp.ne_zero).symm
    rw [hsum]
    have hcop' : Nat.Coprime a m' := by
      exact Nat.Coprime.of_dvd_right (by
        dsimp [m, m']
        exact pow_dvd_pow p (by omega : j + 1 ≤ j + 2)) hcop
    simpa [m'] using
      full_addChar_sum_prime_pow_eq_zero_of_coprime (p := p) (k := j + 1)
        (a := a) hp (by omega) hcop'
  unfold ramanujanSum
  change (∑ x ∈ Finset.range m with Nat.Coprime x m, F x) = 0
  have hcalc :
      (∑ x ∈ Finset.range m with Nat.Coprime x m, F x) +
        (∑ x ∈ Finset.range m with ¬ Nat.Coprime x m, F x) = 0 := by
    simpa [hfull] using hsplit
  rw [hnon, add_zero] at hcalc
  exact hcalc

private theorem ramanujanSum_prime_pow_of_coprime_for_moebius
    {p k a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime a (p ^ k)) :
    ramanujanSum (p ^ k) a =
      ((ArithmeticFunction.moebius (p ^ k) : ℤ) : ℂ) := by
  rcases k with _ | k
  · simp [ramanujanSum]
  rcases k with _ | j
  · have hnot : ¬ p ∣ a := by
      have hpa : Nat.Coprime a p := by simpa using hcop
      exact (hp.coprime_iff_not_dvd.mp hpa.symm)
    rw [show p ^ (0 + 1) = p by simp, ramanujanSum_prime_for_moebius hp, if_neg hnot,
      ArithmeticFunction.moebius_apply_prime hp]
    norm_num
  · rw [ramanujanSum_prime_pow_succ_succ_eq_zero hp hcop,
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega : j + 2 ≠ 0)]
    simp

theorem ramanujanSum_fixed_isMultiplicative (a : ℕ) :
    ArithmeticFunction.IsMultiplicative
      ⟨fun q => ramanujanSum q a, ramanujanSum_zero_q a⟩ := by
  refine ⟨?_, ?_⟩
  · simp [ramanujanSum]
  · intro q₁ q₂ hcop
    rcases q₁.eq_zero_or_pos with rfl | hq₁
    · have hq₂ : q₂ = 1 := by
        simpa using Nat.coprime_iff_gcd_eq_one.mp hcop
      simp [hq₂, ramanujanSum]
    rcases q₂.eq_zero_or_pos with rfl | hq₂
    · have hq₁_one : q₁ = 1 := by
        simpa [Nat.gcd_comm] using Nat.coprime_iff_gcd_eq_one.mp hcop
      simp [hq₁_one, ramanujanSum]
    · exact ramanujanSum_mul_of_coprime_for_moebius hq₁ hq₂ hcop a

theorem ramanujanSum_eq_moebius_of_coprime
    {a q : ℕ} (hcop : Nat.Coprime a q) :
    ramanujanSum q a = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  by_cases hq : q = 0
  · subst hq
    simp
  let r : ArithmeticFunction ℂ :=
    ⟨fun q => ramanujanSum q a, ramanujanSum_zero_q a⟩
  let μ : ArithmeticFunction ℂ := (ArithmeticFunction.moebius : ArithmeticFunction ℂ)
  have hr_mult : r.IsMultiplicative := ramanujanSum_fixed_isMultiplicative a
  have hμ_mult : μ.IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.intCast ArithmeticFunction.isMultiplicative_moebius
  have hr_fact := ArithmeticFunction.IsMultiplicative.multiplicative_factorization r hr_mult hq
  have hμ_fact := ArithmeticFunction.IsMultiplicative.multiplicative_factorization μ hμ_mult hq
  calc
    ramanujanSum q a = r q := rfl
    _ = q.factorization.prod fun p k => r (p ^ k) := hr_fact
    _ = q.factorization.prod fun p k => μ (p ^ k) := by
          refine Finsupp.prod_congr ?_
          intro p hp_supp
          have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors
            (by simpa [Nat.support_factorization] using hp_supp)
          have hpk_dvd : p ^ q.factorization p ∣ q := by
            exact (hp_prime.pow_dvd_iff_le_factorization hq).mpr le_rfl
          have hcop_pk : Nat.Coprime a (p ^ q.factorization p) :=
            Nat.Coprime.of_dvd_right hpk_dvd hcop
          simpa [r, μ] using
            ramanujanSum_prime_pow_of_coprime_for_moebius
              (p := p) (k := q.factorization p) (a := a) hp_prime hcop_pk
    _ = μ q := hμ_fact.symm
    _ = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := rfl

/-! ## Singular integral -/

/-- The unweighted linear exponential sum `L(N, β) = ∑_{m ≤ N} e(mβ)`. -/
noncomputable def linearExpSum (N : ℕ) (β : ℝ) : ℂ :=
  ∑ m ∈ Finset.range (N + 1), addChar β m

theorem addChar_eq_addChar_one_pow (β : ℝ) (m : ℕ) :
    addChar β m = (addChar β 1) ^ m := by
  rw [addChar, addChar, ← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

theorem addChar_one_eq_one_iff (β : ℝ) :
    addChar β 1 = 1 ↔ ∃ k : ℤ, (k : ℝ) = β := by
  unfold addChar
  simp only [Nat.cast_one, mul_one]
  constructor
  · intro h
    rw [Complex.exp_eq_one_iff] at h
    rcases h with ⟨k, hk⟩
    have hfactor : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
    have hβk : (β : ℂ) = (k : ℂ) := by
      apply mul_right_cancel₀ hfactor
      simpa [mul_assoc, mul_comm, mul_left_comm] using hk
    refine ⟨k, ?_⟩
    exact (Complex.ofReal_inj.mp (by simpa using hβk.symm))
  · rintro ⟨k, hk⟩
    rw [Complex.exp_eq_one_iff]
    refine ⟨k, ?_⟩
    rw [← hk]
    push_cast
    ring

@[simp] theorem linearExpSum_zero_N (β : ℝ) : linearExpSum 0 β = 1 := by
  simp [linearExpSum]

theorem norm_linearExpSum_le (N : ℕ) (β : ℝ) :
    ‖linearExpSum N β‖ ≤ (N : ℝ) + 1 := by
  unfold linearExpSum
  refine (norm_sum_le _ _).trans ?_
  have h : ∑ m ∈ Finset.range (N + 1), ‖addChar β m‖ =
      ((Finset.range (N + 1)).card : ℝ) := by
    simp [norm_addChar]
  rw [h, Finset.card_range]
  push_cast
  exact le_refl _

theorem linearExpSum_eq_geom (N : ℕ) {β : ℝ}
    (hβ : addChar β 1 ≠ 1) :
    linearExpSum N β = ((addChar β 1) ^ (N + 1) - 1) / (addChar β 1 - 1) := by
  unfold linearExpSum
  have hsum :
      (∑ m ∈ Finset.range (N + 1), addChar β m) =
        ∑ m ∈ Finset.range (N + 1), (addChar β 1) ^ m := by
    refine Finset.sum_congr rfl ?_
    intro m _hm
    rw [addChar_eq_addChar_one_pow]
  rw [hsum]
  exact geom_sum_eq hβ (N + 1)

theorem norm_addChar_one_sub_one_eq_two_abs_sin (β : ℝ) :
    ‖addChar β 1 - 1‖ = 2 * |Real.sin (Real.pi * β)| := by
  unfold addChar
  simp only [Nat.cast_one, mul_one]
  have harg :
      2 * Real.pi * Complex.I * (β : ℂ) =
        Complex.I * ((2 * Real.pi * β : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : (2 * Real.pi * β) / 2 = Real.pi * β := by ring
  rw [hhalf]
  simp [Real.norm_eq_abs]

theorem norm_linearExpSum_le_oscillation_addChar (N : ℕ) {β : ℝ}
    (hβ : ¬ ∃ k : ℤ, (k : ℝ) = β) :
    ‖linearExpSum N β‖ ≤ 2 / ‖addChar β 1 - 1‖ := by
  have hchar : addChar β 1 ≠ 1 := by
    intro h
    exact hβ ((addChar_one_eq_one_iff β).mp h)
  have hgeom := linearExpSum_eq_geom N hchar
  calc
    ‖linearExpSum N β‖ =
        ‖((addChar β 1) ^ (N + 1) - 1) / (addChar β 1 - 1)‖ := by rw [hgeom]
    _ = ‖(addChar β 1) ^ (N + 1) - 1‖ / ‖addChar β 1 - 1‖ := by
      rw [norm_div]
    _ ≤ 2 / ‖addChar β 1 - 1‖ := by
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      calc
        ‖(addChar β 1) ^ (N + 1) - 1‖
            ≤ ‖(addChar β 1) ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by
          simp [norm_pow, norm_addChar]
          norm_num


theorem norm_linearExpSum_le_oscillation_sin (N : ℕ) {β : ℝ}
    (hβ : ¬ ∃ k : ℤ, (k : ℝ) = β) :
    ‖linearExpSum N β‖ ≤ 1 / |Real.sin (Real.pi * β)| := by
  have hchar : addChar β 1 ≠ 1 := by
    intro h
    exact hβ ((addChar_one_eq_one_iff β).mp h)
  have hsin_ne : |Real.sin (Real.pi * β)| ≠ 0 := by
    intro hsin
    have hnorm_ne : ‖addChar β 1 - 1‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hchar)
    exact hnorm_ne (by simp [norm_addChar_one_sub_one_eq_two_abs_sin, hsin])
  calc
    ‖linearExpSum N β‖ ≤ 2 / ‖addChar β 1 - 1‖ :=
      norm_linearExpSum_le_oscillation_addChar N hβ
    _ = 1 / |Real.sin (Real.pi * β)| := by
      rw [norm_addChar_one_sub_one_eq_two_abs_sin]
      field_simp [hsin_ne]

/-- The singular integral `J(N, n) := ∫_{[0,1]} L(N, β)³ · e(-nβ) dβ`,
the principal analytic main term in the Hardy–Littlewood circle method.
This is the integral one obtains by replacing each weighted sum
`S_Λ(α, N)` near a major-arc center by its leading-order linear surrogate. -/
noncomputable def singularIntegral (N n : ℕ) : ℂ :=
  ∫ β in Set.Icc (0 : ℝ) 1, (linearExpSum N β) ^ 3 * negAddChar β n

/-- The singular integral evaluates to the count of triples `(a, b, c) ∈ [0,N]³`
with `a + b + c = n`, by Fourier orthogonality. -/
theorem singularIntegral_eq_card (N n : ℕ) :
    singularIntegral N n =
      ∑ x ∈ Finset.range (N + 1) ×ˢ
          (Finset.range (N + 1) ×ˢ Finset.range (N + 1)),
        (if x.1 + x.2.1 + x.2.2 = n then (1 : ℂ) else 0) := by
  unfold singularIntegral
  let s := Finset.range (N + 1)
  have hpoint : ∀ β : ℝ,
      (linearExpSum N β) ^ 3 * negAddChar β n =
        ∑ x ∈ s ×ˢ (s ×ˢ s),
          addChar β (x.2.2 + x.2.1 + x.1) * negAddChar β n := by
    intro β
    unfold linearExpSum
    simp_rw [Finset.sum_product]
    simp [pow_succ, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    refine Finset.sum_congr rfl ?_
    intro a _ha
    refine Finset.sum_congr rfl ?_
    intro b _hb
    refine Finset.sum_congr rfl ?_
    intro c _hc
    rw [addChar_sum_three]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc (fun β _hβ => hpoint β)]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro x _hx
    rw [integral_addChar_negAddChar_kernel]
    have hsum : x.2.2 + x.2.1 + x.1 = x.1 + x.2.1 + x.2.2 := by omega
    rw [hsum]
  · intro x _hx
    apply Continuous.integrableOn_Icc
    unfold addChar negAddChar
    fun_prop

/-- The number of triples `(a, b, c) ∈ [0,n]³` with `a + b + c = n` equals
`C(n+2, 2) = (n+1)(n+2)/2`. -/
theorem singularIntegral_self_eq_choose (n : ℕ) :
    singularIntegral n n =
      ((Finset.range (n + 1) ×ˢ
          (Finset.range (n + 1) ×ˢ Finset.range (n + 1))).filter
        (fun x : ℕ × ℕ × ℕ => x.1 + x.2.1 + x.2.2 = n)).card := by
  rw [singularIntegral_eq_card]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  simp

/-- A weaker but useful corollary: `singularIntegral n n` is a real natural
number, equal to the cardinality of the filtered triple set. -/
theorem singularIntegral_self_re_eq (n : ℕ) :
    (singularIntegral n n).re =
      ((Finset.range (n + 1) ×ˢ
          (Finset.range (n + 1) ×ˢ Finset.range (n + 1))).filter
        (fun x : ℕ × ℕ × ℕ => x.1 + x.2.1 + x.2.2 = n)).card := by
  rw [singularIntegral_self_eq_choose]
  simp

/-- Lower bound on the singular integral. Inject the square `[0, n/2]²` into the
triple-count set via `(a, b) ↦ (a, b, n - a - b)`; cardinality `(n/2 + 1)²` is
at least `n²/4`. -/
theorem singularIntegral_lower_bound :
    ∃ N₀ K : ℝ, 0 < K ∧ ∀ n : ℕ, N₀ ≤ (n : ℝ) →
      K * (n : ℝ) ^ 2 ≤ (singularIntegral n n).re := by
  refine ⟨0, (1 : ℝ) / 4, by norm_num, ?_⟩
  intro n _hn
  rw [singularIntegral_self_re_eq]
  set m := n / 2 with hm
  set T := (Finset.range (n + 1) ×ˢ
      (Finset.range (n + 1) ×ˢ Finset.range (n + 1))).filter
    (fun x : ℕ × ℕ × ℕ => x.1 + x.2.1 + x.2.2 = n) with hT
  have h2m : 2 * m ≤ n := by simp [hm]; omega
  -- Inject [0, m] × [0, m] into T via (a, b) ↦ (a, b, n - a - b).
  have hsubset : (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).image
      (fun ab : ℕ × ℕ => (ab.1, ab.2, n - ab.1 - ab.2)) ⊆ T := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hx
    simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> omega
  have hinj : Set.InjOn
      (fun ab : ℕ × ℕ => (ab.1, ab.2, n - ab.1 - ab.2))
      ↑(Finset.range (m + 1) ×ˢ Finset.range (m + 1)) := by
    intros x _ y _ hxy
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext hxy.1 hxy.2.1
  have hcardimg : ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)).image
      (fun ab : ℕ × ℕ => (ab.1, ab.2, n - ab.1 - ab.2))).card = (m + 1) ^ 2 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product]
    simp [Finset.card_range, sq]
  have hcardT : (m + 1) ^ 2 ≤ T.card := by
    rw [← hcardimg]
    exact Finset.card_le_card hsubset
  -- Convert to real bound: n²/4 ≤ (m+1)² ≤ T.card.
  have hnle : (n : ℝ) ≤ 2 * (m + 1 : ℕ) := by
    have : n ≤ 2 * m + 2 := by omega
    exact_mod_cast this
  have hpos : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hpos' : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
  have hsq : (n : ℝ) ^ 2 ≤ (2 * ((m + 1 : ℕ) : ℝ)) ^ 2 := by
    have hmul : 0 ≤ 2 * ((m + 1 : ℕ) : ℝ) := by linarith
    nlinarith [sq_nonneg ((n : ℝ) - 2 * ((m + 1 : ℕ) : ℝ))]
  have hexpand : (2 * ((m + 1 : ℕ) : ℝ)) ^ 2 = 4 * ((m + 1 : ℕ) : ℝ) ^ 2 := by ring
  have hineq1 : (1 : ℝ) / 4 * (n : ℝ) ^ 2 ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
    rw [hexpand] at hsq
    linarith
  have hineq2 : (((m + 1) ^ 2 : ℕ) : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcardT
  have hcast : ((m + 1 : ℕ) : ℝ) ^ 2 = (((m + 1) ^ 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast] at hineq1
  linarith

/-! ## Truncated singular series -/

/-- The truncated singular series `S_Q(n) := ∏_{p prime, p ≤ Q} factor(p, n)`,
where `factor(p, n)` is the Hardy–Littlewood local factor:
* `1` if `p ≤ 2` (parity convention; absorbs `p = 2` into the global factor),
* `1 + 1/(p-1)³` if `p ∣ n` (and `p ≥ 3`),
* `1 - 1/(p-1)²` otherwise (and `p ≥ 3`).

This is the partial Euler product approximation to the full
`Math.Problems.TernaryGoldbach.singularSeries`. -/
noncomputable def truncatedSingularSeries (Q n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (Q + 1)).filter Nat.Prime,
    (if p ≤ 2 then (1 : ℝ)
     else if p ∣ n then 1 - 1 / ((p : ℝ) - 1) ^ 2
     else 1 + 1 / ((p : ℝ) - 1) ^ 3)

@[simp] theorem truncatedSingularSeries_zero_Q (n : ℕ) :
    truncatedSingularSeries 0 n = 1 := by
  unfold truncatedSingularSeries
  have h : (Finset.range (0 + 1)).filter Nat.Prime = ∅ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
      not_and]
    intro hp
    interval_cases p
    decide
  rw [h, Finset.prod_empty]

@[simp] theorem truncatedSingularSeries_one_Q (n : ℕ) :
    truncatedSingularSeries 1 n = 1 := by
  unfold truncatedSingularSeries
  have h : (Finset.range (1 + 1)).filter Nat.Prime = ∅ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
      not_and]
    intro hp
    interval_cases p <;> decide
  rw [h, Finset.prod_empty]


@[simp] theorem truncatedSingularSeries_two_Q (n : ℕ) :
    truncatedSingularSeries 2 n = 1 := by
  unfold truncatedSingularSeries
  have h : (Finset.range (2 + 1)).filter Nat.Prime = {2} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    refine ⟨fun ⟨hlt, hp⟩ => ?_, fun hp => ?_⟩
    · interval_cases p
      · exact (Nat.not_prime_zero hp).elim
      · exact (Nat.not_prime_one hp).elim
      · rfl
    · subst hp; exact ⟨by omega, Nat.prime_two⟩
  rw [h, Finset.prod_singleton]
  simp

/-- `|μ(q)/φ(q)| ≤ 1`. The quotient `μ(q)/φ(q)` is the principal coefficient
attached to a major-arc center; its absolute value is bounded by 1. -/
theorem mu_phi_quotient_bound (q : ℕ) :
    |((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ)| ≤ 1 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp
  · have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq
    rw [abs_div, abs_of_pos hphi_pos, div_le_one hphi_pos]
    have hμ : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := q)
      exact_mod_cast h
    have hphi : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq
    linarith


end Vinogradov
