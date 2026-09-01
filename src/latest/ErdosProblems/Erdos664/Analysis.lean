/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos664.Probability

namespace Erdos664

open scoped BigOperators ENNReal NNReal
open Finset MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ### The three error terms tend to zero -/

lemma tendsto_line_error :
    Filter.Tendsto
      (fun q : ℕ => (((q : ℝ) ^ 2 + q) * Real.exp (-(q : ℝ) / 50)))
      Filter.atTop (nhds 0) := by
  have htop : Filter.Tendsto (fun q : ℕ => (q : ℝ) / 50)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp htop
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp htop
  convert (h2.const_mul 2500).add (h1.const_mul 50) using 1
  · ext q
    simp only [Function.comp_apply, pow_one]
    ring_nf
  · norm_num

lemma tendsto_point_error :
    Filter.Tendsto
      (fun q : ℕ => ((q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 8)))
      Filter.atTop (nhds 0) := by
  have htop : Filter.Tendsto (fun q : ℕ => (q : ℝ) / 8)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp htop
  convert h2.const_mul 64 using 1
  · ext q
    simp only [Function.comp_apply]
    ring_nf
  · norm_num

lemma transversal_error_lt {u q : ℕ} (hq : 1 ≤ q)
    (hlog : Real.log (q : ℝ) / q <
      ((1 : ℝ) / 2) ^ (16 * u) / (32 * (u + 1)))
    (hexp : Real.exp (-(((1 : ℝ) / 2) ^ (16 * u)) * (q : ℝ) / 4) < 1 / 3) :
    ((q : ℝ) ^ 2) ^ (4 * q * u) *
        Real.exp (-(((1 : ℝ) / 2) ^ (16 * u)) *
          (((q : ℝ) ^ 2 + q) / 2)) < 1 / 3 := by
  let x : ℝ := q
  let a : ℝ := ((1 : ℝ) / 2) ^ (16 * u)
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast hq
  have ha : 0 < a := by positivity
  have hc : 0 < (32 : ℝ) * (u + 1) := by positivity
  have hlogxa : Real.log x / x < a / (32 * (u + 1)) := by
    simpa [x, a] using hlog
  have hlog' : Real.log x < (a * x) / (32 * (u + 1)) := by
    have htmp := (div_lt_iff₀ hx).mp hlogxa
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htmp
  have hlog2 : (32 : ℝ) * (u + 1) * Real.log x < a * x := by
    have hh := (lt_div_iff₀ hc).mp (by
      convert hlog' using 1)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hh
  have hlog3 := mul_lt_mul_of_pos_right hlog2 hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hexponent :
      8 * (u : ℝ) * x * Real.log x - a * (x ^ 2 + x) / 2 ≤ -a * x / 4 := by
    nlinarith
  have hpow :
      (x ^ 2) ^ (4 * q * u) = Real.exp (8 * (u : ℝ) * x * Real.log x) := by
    calc
      (x ^ 2) ^ (4 * q * u) =
          (Real.exp (Real.log (x ^ 2))) ^ (4 * q * u) := by
            rw [Real.exp_log (by positivity : 0 < x ^ 2)]
      _ = Real.exp ((4 * q * u : ℕ) * Real.log (x ^ 2)) := by
            rw [Real.exp_nat_mul]
      _ = Real.exp (8 * (u : ℝ) * x * Real.log x) := by
            rw [Real.log_pow]
            push_cast
            dsimp [x]
            ring
  change (x ^ 2) ^ (4 * q * u) *
      Real.exp (-a * ((x ^ 2 + x) / 2)) < 1 / 3
  calc
    (x ^ 2) ^ (4 * q * u) *
        Real.exp (-a * ((x ^ 2 + x) / 2)) =
        Real.exp (8 * (u : ℝ) * x * Real.log x - a * (x ^ 2 + x) / 2) := by
      rw [hpow, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-a * x / 4) := Real.exp_le_exp.mpr hexponent
    _ < 1 / 3 := by simpa [x, a] using hexp

lemma eventually_error_sum_lt_one (u : ℕ) :
    ∀ᶠ q : ℕ in Filter.atTop,
      (((q : ℝ) ^ 2 + q) * Real.exp (-(q : ℝ) / 50)) +
      ((q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 8)) +
      ((q : ℝ) ^ 2) ^ (4 * q * u) *
        Real.exp (-(((1 : ℝ) / 2) ^ (16 * u)) *
          (((q : ℝ) ^ 2 + q) / 2)) < 1 := by
  let a : ℝ := ((1 : ℝ) / 2) ^ (16 * u)
  have ha : 0 < a := by positivity
  have hline := tendsto_line_error.eventually
    (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 3))
  have hpoint := tendsto_point_error.eventually
    (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 3))
  have hloglim :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog := hloglim.eventually
    (Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < a / (32 * (u + 1))))
  have hexplim : Filter.Tendsto
      (fun q : ℕ => Real.exp (-a * (q : ℝ) / 4))
      Filter.atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
    have hneg : -a / 4 < 0 := by linarith
    convert hcast.atTop_mul_const_of_neg hneg using 1
    ext q
    ring
  have hexp := hexplim.eventually
    (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 3))
  have hqev : ∀ᶠ q : ℕ in Filter.atTop, 1 ≤ q :=
    Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩
  filter_upwards [hqev, hline, hpoint, hlog, hexp]
      with q hq hlineq hpointq hlogq hexpq
  have hline_nonneg : 0 ≤
      ((q : ℝ) ^ 2 + q) * Real.exp (-(q : ℝ) / 50) := by positivity
  have hpoint_nonneg : 0 ≤ (q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 8) := by positivity
  have hline_lt :
      ((q : ℝ) ^ 2 + q) * Real.exp (-(q : ℝ) / 50) < 1 / 3 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hline_nonneg] at hlineq
    exact hlineq
  have hpoint_lt : (q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 8) < 1 / 3 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hpoint_nonneg] at hpointq
    exact hpointq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogpos : 0 ≤ Real.log (q : ℝ) / q :=
    div_nonneg (Real.log_nonneg hqR) (by positivity)
  have hlog_lt : Real.log (q : ℝ) / q < a / (32 * (u + 1)) := by
    simp only [Function.comp_apply, pow_one, one_mul, add_zero] at hlogq
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hlogpos] at hlogq
    exact hlogq
  have hexp_nonneg : 0 ≤ Real.exp (-a * (q : ℝ) / 4) := Real.exp_nonneg _
  have hexp_lt : Real.exp (-a * (q : ℝ) / 4) < 1 / 3 := by
    simpa [Real.dist_eq, abs_of_nonneg hexp_nonneg] using hexpq
  have htrans := transversal_error_lt hq hlog_lt hexp_lt
  nlinarith

/-! ### Selected lines and point degrees -/

noncomputable def selectedSet {L P : Type*} [DecidableEq P] (A : L → Finset P)
    (ω : L → P → Bool) (l : L) : Finset P :=
  (A l).filter fun p => ω l p = true

noncomputable def selectedDegree {L P : Type*} [Fintype L] [DecidableEq P]
    (A : L → Finset P) (ω : L → P → Bool) (p : P) : ℕ :=
  #(Finset.univ.filter fun l => p ∈ selectedSet A ω l)

lemma selectedDegree_eq_filter {L P : Type*} [Fintype L] [DecidableEq P]
    (A : L → Finset P) (ω : L → P → Bool) (p : P) :
    selectedDegree A ω p = #((incidenceSet A p).filter fun l => ω l p = true) := by
  classical
  simp only [selectedDegree, incidenceSet, selectedSet, Finset.mem_filter]
  congr 1
  ext l
  simp

lemma fairMatrix_selectedSet_lower_tail {L P : Type*} [Fintype L] [Fintype P]
    [DecidableEq P] (A : L → Finset P) (l : L) :
    (fairMatrixMeasure L P).real
        {ω | (#(selectedSet A ω l) : ℝ) ≤ (2 / 5 : ℝ) * #(A l)} ≤
      Real.exp (-(#(A l) : ℝ) / 50) := by
  let E : Set (P → Bool) :=
    {row | (#((A l).filter fun p => row p = true) : ℝ) ≤ (2 / 5 : ℝ) * #(A l)}
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have hset : {ω | (#(selectedSet A ω l) : ℝ) ≤ (2 / 5 : ℝ) * #(A l)} =
      Function.eval l ⁻¹' E := by
    rfl
  rw [hset, Measure.real, fairMatrixMeasure_row l hE]
  exact fairVector_card_filter_lower_tail (A l)

lemma fairMatrix_selectedDegree_lower_tail {L P : Type*} [Fintype L] [Fintype P]
    [DecidableEq P] (A : L → Finset P) (p : P) :
    (fairMatrixMeasure L P).real
        {ω | (selectedDegree A ω p : ℝ) ≤ (1 / 4 : ℝ) * #(incidenceSet A p)} ≤
      Real.exp (-(#(incidenceSet A p) : ℝ) / 8) := by
  have hset :
      {ω | (selectedDegree A ω p : ℝ) ≤ (1 / 4 : ℝ) * #(incidenceSet A p)} =
        {ω | (#((incidenceSet A p).filter fun l => ω l p = true) : ℝ) ≤
          (1 / 4 : ℝ) * #(incidenceSet A p)} := by
    ext ω
    change ((selectedDegree A ω p : ℝ) ≤ (1 / 4 : ℝ) * #(incidenceSet A p)) ↔
      ((#((incidenceSet A p).filter fun l => ω l p = true) : ℝ) ≤
        (1 / 4 : ℝ) * #(incidenceSet A p))
    rw [selectedDegree_eq_filter]
  rw [hset]
  exact fairMatrix_card_filter_lower_tail p (incidenceSet A p)

lemma fairMatrix_exists_small_selectedSet {L P : Type*} [Fintype L] [Fintype P]
    [DecidableEq P] (A : L → Finset P) :
    (fairMatrixMeasure L P).real
        {ω | ∃ l, (#(selectedSet A ω l) : ℝ) ≤ (2 / 5 : ℝ) * #(A l)} ≤
      ∑ l, Real.exp (-(#(A l) : ℝ) / 50) := by
  have hset :
      {ω | ∃ l, (#(selectedSet A ω l) : ℝ) ≤ (2 / 5 : ℝ) * #(A l)} =
        ⋃ l, {ω | (#(selectedSet A ω l) : ℝ) ≤ (2 / 5 : ℝ) * #(A l)} := by
    ext ω
    simp
  rw [hset]
  exact (measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum fun l hl => fairMatrix_selectedSet_lower_tail A l)

lemma fairMatrix_exists_small_selectedDegree {L P : Type*} [Fintype L] [Fintype P]
    [DecidableEq P] (A : L → Finset P) :
    (fairMatrixMeasure L P).real
        {ω | ∃ p, (selectedDegree A ω p : ℝ) ≤
          (1 / 4 : ℝ) * #(incidenceSet A p)} ≤
      ∑ p, Real.exp (-(#(incidenceSet A p) : ℝ) / 8) := by
  have hset :
      {ω | ∃ p, (selectedDegree A ω p : ℝ) ≤
          (1 / 4 : ℝ) * #(incidenceSet A p)} =
        ⋃ p, {ω | (selectedDegree A ω p : ℝ) ≤
          (1 / 4 : ℝ) * #(incidenceSet A p)} := by
    ext ω
    simp
  rw [hset]
  exact (measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum fun p hp => fairMatrix_selectedDegree_lower_tail A p)

lemma sum_card_inter_selected_eq_sum_selectedDegree
    {L P : Type*} [Fintype L] [DecidableEq P]
    (A : L → Finset P) (ω : L → P → Bool) (T : Finset P) :
    ∑ l, #(T ∩ selectedSet A ω l) =
      ∑ p ∈ T, selectedDegree A ω p := by
  exact sum_card_inter_eq_sum_degrees (fun l => selectedSet A ω l) T

/-! ### Incidence double counting and extraction of a good configuration -/

lemma native_intersection_unbounded {F : Type*} [Field F] [Fintype F]
    [DecidableEq F]
    (K : ℕ) (ω : AffineLine F → F × F → Bool)
    (hdegree : ∀ p : F × F,
      (1 / 4 : ℝ) * (Fintype.card F + 1) <
        selectedDegree (fun l : AffineLine F => affineLinePoints l) ω p)
    (hsmall : ¬HasSmallTransversal
      (fun l : AffineLine F => affineLinePoints l)
      (4 * Fintype.card F * (K + 1)) ω)
    (C : Finset (F × F))
    (hC : ∀ l : AffineLine F,
      (C ∩ selectedSet (fun l : AffineLine F => affineLinePoints l) ω l).Nonempty) :
    ∃ l : AffineLine F,
      K < #(C ∩ selectedSet (fun l : AffineLine F => affineLinePoints l) ω l) := by
  let A : AffineLine F → Finset (F × F) := affineLinePoints
  by_contra hbounded
  simp only [not_exists, not_lt] at hbounded
  have hsumNat := sum_card_inter_selected_eq_sum_selectedDegree A ω C
  have hsumReal :
      ∑ p ∈ C, (selectedDegree A ω p : ℝ) =
        ∑ l : AffineLine F, (#(C ∩ selectedSet A ω l) : ℝ) := by
    exact_mod_cast hsumNat.symm
  have hlower :
      (1 / 4 : ℝ) * (Fintype.card F + 1) * C.card ≤
        ∑ p ∈ C, (selectedDegree A ω p : ℝ) := by
    calc
      (1 / 4 : ℝ) * (Fintype.card F + 1) * C.card =
          ∑ _p ∈ C, ((1 / 4 : ℝ) * (Fintype.card F + 1)) := by
        simp [mul_comm]
      _ ≤ ∑ p ∈ C, (selectedDegree A ω p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact (hdegree p).le
  have hupper :
      ∑ l : AffineLine F, (#(C ∩ selectedSet A ω l) : ℝ) ≤
        Fintype.card (AffineLine F) * K := by
    calc
      (∑ l : AffineLine F, (#(C ∩ selectedSet A ω l) : ℝ)) ≤
          ∑ _l : AffineLine F, (K : ℝ) := by
        apply Finset.sum_le_sum
        intro l hl
        exact_mod_cast hbounded l
      _ = _ := by simp
  have hlinecard :
      (Fintype.card (AffineLine F) : ℝ) =
        Fintype.card F * (Fintype.card F + 1) := by
    rw [card_affineLineType]
    push_cast
    ring
  have hqpos : (0 : ℝ) < Fintype.card F + 1 := by positivity
  have hcardReal : (C.card : ℝ) ≤ 4 * Fintype.card F * K := by
    rw [hsumReal] at hlower
    rw [hlinecard] at hupper
    nlinarith
  have hcardNat : C.card ≤ 4 * Fintype.card F * K := by exact_mod_cast hcardReal
  apply hsmall
  refine ⟨C, hcardNat.trans ?_, ?_⟩
  · nlinarith
  · intro l hl
    obtain ⟨p, hp⟩ := hC l
    have hpC : p ∈ C := (Finset.mem_inter.mp hp).1
    have hpSel : p ∈ selectedSet A ω l := (Finset.mem_inter.mp hp).2
    have hpA : p ∈ A l := (Finset.mem_filter.mp hpSel).1
    have hpω : ω l p = true := (Finset.mem_filter.mp hpSel).2
    refine ⟨p, ?_, hpω⟩
    simpa only [Finset.mem_inter, A] using And.intro hpC hpA

end Erdos664
