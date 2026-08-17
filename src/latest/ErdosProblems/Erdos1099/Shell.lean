/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1099.Construction
import ErdosProblems.Erdos1099.Net
import ErdosProblems.Erdos1099.Energy
import ErdosProblems.Erdos1099.Refinement
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.List.ChainOfFn

/-!
# Finite logarithmic shells for Erdős Problem 1099

This file turns the subset-sum net into actual, increasingly ordered divisor
chains.  At integral level `t`, and depth `r`, we retain every selected divisor
whose logarithmic correction is in `[0, log 2]`, and adjoin `2^(t+1)` as the
right endpoint.  Sorting this finite set gives a divisor chain across the
whole dyadic shell.  Its logarithmic mesh is at most `2 * 2⁻ʳ`.
-/

open Finset Set
open scoped BigOperators

namespace Erdos1099

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The finite family of index sets whose digit sums lie in one dyadic
logarithmic shell. -/
def shellIndexSets (r : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 r).powerset.filter
    (fun E ↦ (∑ i ∈ E, Net.delta i) ≤ Real.log 2)

/-- The actual selected divisors in the shell `[2^t,2^(t+1)]`, including the
right endpoint. -/
def shellDivisors (t r : ℕ) : Finset ℕ :=
  insert (2 ^ (t + 1))
    ((shellIndexSets r).image (fun E ↦ selectedDivisor t E))

lemma mem_shellIndexSets_iff {r : ℕ} {E : Finset ℕ} :
    E ∈ shellIndexSets r ↔
      E ⊆ Finset.Icc 1 r ∧ (∑ i ∈ E, Net.delta i) ≤ Real.log 2 := by
  simp [shellIndexSets]

lemma empty_mem_shellIndexSets (r : ℕ) : ∅ ∈ shellIndexSets r := by
  simp [shellIndexSets, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

lemma pow_mem_shellDivisors_left (t r : ℕ) :
    2 ^ t ∈ shellDivisors t r := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.2
  refine ⟨∅, empty_mem_shellIndexSets r, ?_⟩
  simp [selectedDivisor, indexSum, selectedProduct]

lemma pow_mem_shellDivisors_right (t r : ℕ) :
    2 ^ (t + 1) ∈ shellDivisors t r := by
  simp [shellDivisors]

lemma logDigit_eq_delta (i : ℕ) : logDigit i = Net.delta i := by
  rfl

lemma log_selectedDivisor_eq {t : ℕ} {E : Finset ℕ}
    (hEt : indexSum E ≤ t) :
    Real.log (selectedDivisor t E : ℝ) =
      (t : ℝ) * Real.log 2 + ∑ i ∈ E, Net.delta i := by
  simpa [logDigit_eq_delta] using log_selectedDivisor hEt

lemma indexSum_le_of_mem_shellIndexSets {t r : ℕ} {E : Finset ℕ}
    (hE : E ∈ shellIndexSets r) (hrt : triangular r ≤ t) :
    indexSum E ≤ t := by
  exact (indexSum_le_triangular (mem_shellIndexSets_iff.1 hE).1).trans hrt

lemma log_pow_two (t : ℕ) :
    Real.log ((2 ^ t : ℕ) : ℝ) = (t : ℝ) * Real.log 2 := by
  norm_num [Real.log_pow]

lemma shellDivisors_log_mem {t r d : ℕ} (hrt : triangular r ≤ t)
    (hd : d ∈ shellDivisors t r) :
    Real.log (d : ℝ) ∈
      Set.Icc ((t : ℝ) * Real.log 2) (((t + 1 : ℕ) : ℝ) * Real.log 2) := by
  simp only [shellDivisors, Finset.mem_insert, Finset.mem_image] at hd
  rcases hd with rfl | hd
  · rw [log_pow_two]
    exact ⟨mul_le_mul_of_nonneg_right (by norm_num) (Real.log_nonneg (by norm_num)), le_rfl⟩
  · obtain ⟨E, hE, rfl⟩ := hd
    have hsum0 : 0 ≤ ∑ i ∈ E, Net.delta i :=
      Finset.sum_nonneg fun i _ ↦ Net.delta_nonneg i
    have hsum2 : (∑ i ∈ E, Net.delta i) ≤ Real.log 2 :=
      (mem_shellIndexSets_iff.1 hE).2
    rw [log_selectedDivisor_eq (indexSum_le_of_mem_shellIndexSets hE hrt)]
    constructor
    · linarith
    · push_cast
      ring_nf
      linarith

lemma shellDivisors_pos {t r d : ℕ} (hd : d ∈ shellDivisors t r) : 0 < d := by
  simp only [shellDivisors, Finset.mem_insert, Finset.mem_image] at hd
  rcases hd with rfl | hd
  · positivity
  · obtain ⟨E, _, rfl⟩ := hd
    exact selectedDivisor_pos t E

lemma shellDivisors_dvd {k r t d : ℕ}
    (hrk : r ≤ k) (hrt : triangular r ≤ t)
    (htk : t + 1 ≤ triangular k) (hd : d ∈ shellDivisors t r) :
    d ∣ voseNumber k := by
  simp only [shellDivisors, Finset.mem_insert, Finset.mem_image] at hd
  rcases hd with rfl | hd
  · exact Nat.dvd_mul_right_of_dvd (pow_dvd_pow 2 htk) _
  · obtain ⟨E, hE, rfl⟩ := hd
    exact selectedDivisor_dvd (mem_shellIndexSets_iff.1 hE).1 hrk hrt
      (Nat.le_of_succ_le htk)

/-- Every point of the one-sided logarithmic net is represented by an actual
selected divisor in the shell. -/
lemma exists_shellDivisor_log_below {t r : ℕ} (hrt : triangular r ≤ t)
    {x : ℝ}
    (hx : x ∈ Set.Icc ((t : ℝ) * Real.log 2)
      (((t + 1 : ℕ) : ℝ) * Real.log 2)) :
    ∃ d ∈ shellDivisors t r,
      0 ≤ x - Real.log (d : ℝ) ∧
      x - Real.log (d : ℝ) ≤ Net.dyadic r := by
  let u := x - (t : ℝ) * Real.log 2
  have hu0 : 0 ≤ u := by exact sub_nonneg.mpr hx.1
  have hu2 : u ≤ Real.log 2 := by
    dsimp [u]
    norm_num [Nat.cast_add, Nat.cast_one] at hx
    ring_nf at hx ⊢
    linarith
  obtain ⟨E, hEsub, hE0, hEg⟩ := Net.exists_subsetSum_below hu0 hu2
  let d := selectedDivisor t E
  have hEmem : E ∈ shellIndexSets r := by
    rw [mem_shellIndexSets_iff]
    refine ⟨hEsub, ?_⟩
    linarith
  have hsumt : indexSum E ≤ t :=
    (indexSum_le_triangular hEsub).trans hrt
  refine ⟨d, ?_, ?_, ?_⟩
  · rw [shellDivisors]
    exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨E, hEmem, rfl⟩)
  · rw [log_selectedDivisor_eq hsumt]
    dsimp [u] at hE0
    linarith
  · rw [log_selectedDivisor_eq hsumt]
    dsimp [u] at hEg
    linarith

/-- Adjacent elements of the sorted finite divisor shell have logarithmic gap
at most `2 * 2⁻ʳ`. -/
lemma shellDivisors_log_mesh {t r a b : ℕ} (hrt : triangular r ≤ t)
    (ha : a ∈ shellDivisors t r) (hb : b ∈ shellDivisors t r)
    (hab : a < b)
    (hadj : ∀ d ∈ shellDivisors t r, ¬ (a < d ∧ d < b)) :
    Real.log (b : ℝ) - Real.log (a : ℝ) ≤ 2 * Net.dyadic r := by
  by_contra hgap
  let x := (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2
  have hxa := shellDivisors_log_mem hrt ha
  have hxb := shellDivisors_log_mem hrt hb
  have hx : x ∈ Set.Icc ((t : ℝ) * Real.log 2)
      (((t + 1 : ℕ) : ℝ) * Real.log 2) := by
    constructor <;> dsimp [x] <;> linarith [hxa.1, hxa.2, hxb.1, hxb.2]
  obtain ⟨d, hd, hd0, hdg⟩ := exists_shellDivisor_log_below hrt hx
  have hloga : Real.log (a : ℝ) < Real.log (d : ℝ) := by
    dsimp [x] at hd0 hdg
    linarith
  have hlogb : Real.log (d : ℝ) < Real.log (b : ℝ) := by
    dsimp [x] at hd0 hdg
    linarith
  have had : a < d := by
    exact_mod_cast (Real.log_lt_log_iff
      (by exact_mod_cast shellDivisors_pos ha)
      (by exact_mod_cast shellDivisors_pos hd)).mp hloga
  have hdb : d < b := by
    exact_mod_cast (Real.log_lt_log_iff
      (by exact_mod_cast shellDivisors_pos hd)
      (by exact_mod_cast shellDivisors_pos hb)).mp hlogb
  exact hadj d hd ⟨had, hdb⟩

/-! ## A list model for concatenating finite chains -/

/-- Logarithmic gap energy of a finite list of positive integers. -/
def listLogEnergy (alpha : ℝ) : List ℕ → ℝ
  | a :: b :: l =>
      (Real.log (b : ℝ) - Real.log (a : ℝ)) ^ alpha +
        listLogEnergy alpha (b :: l)
  | _ => 0

/-- The relative-gap energy used in Erdős Problem 1099, evaluated on a finite
divisor chain. -/
def listRelativeEnergy (alpha : ℝ) : List ℕ → ℝ
  | a :: b :: l =>
      (((b : ℝ) / (a : ℝ) - 1) ^ alpha) +
        listRelativeEnergy alpha (b :: l)
  | _ => 0

lemma listLogEnergy_nonneg (alpha : ℝ) (l : List ℕ)
    (hpos : ∀ d ∈ l, 0 < d) (hchain : l.IsChain (· ≤ ·)) :
    0 ≤ listLogEnergy alpha l := by
  induction l with
  | nil => simp [listLogEnergy]
  | cons a l ih =>
      cases l with
      | nil => simp [listLogEnergy]
      | cons b l =>
          simp only [List.isChain_cons_cons] at hchain
          have ha0 : 0 < a := hpos a (by simp)
          have hab : a ≤ b := hchain.1
          have hlog : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
            Real.log_le_log (by exact_mod_cast ha0) (by exact_mod_cast hab)
          simp only [listLogEnergy]
          exact add_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hlog) _)
            (ih (fun d hd ↦ hpos d (by simp [hd])) hchain.2)

lemma exp_sub_one_le_exp_mul {x C : ℝ} (hx0 : 0 ≤ x) (hxC : x ≤ C) :
    Real.exp x - 1 ≤ Real.exp C * x := by
  have htan := Real.add_one_le_exp (-x)
  have hmul := mul_le_mul_of_nonneg_left htan (Real.exp_pos x).le
  have hfirst : Real.exp x - 1 ≤ Real.exp x * x := by
    rw [mul_add, mul_one, ← Real.exp_add] at hmul
    simp only [add_neg_cancel, Real.exp_zero] at hmul
    linarith
  exact hfirst.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hxC) hx0)

lemma gap_le_of_rpow_le {alpha x C : ℝ} (halpha : 1 ≤ alpha)
    (hx0 : 0 ≤ x) (hC : 1 ≤ C) (hxpow : x ^ alpha ≤ C) : x ≤ C := by
  by_cases hx1 : x ≤ 1
  · exact hx1.trans hC
  · have hone : 1 ≤ x := le_of_not_ge hx1
    have hxle : x ≤ x ^ alpha := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hone halpha
    exact hxle.trans hxpow

/-- On a positive increasing chain whose logarithmic energy is at most
`C ≥ 1`, relative-gap energy is at most `exp(C)^alpha` times logarithmic
energy.  This deliberately coarse conversion is enough for uniformity and
does not need a separately stored mesh certificate. -/
lemma listRelativeEnergy_le_exp_mul_listLogEnergy {alpha C : ℝ}
    (halpha : 1 ≤ alpha) (hC : 1 ≤ C) (l : List ℕ)
    (hpos : ∀ d ∈ l, 0 < d) (hchain : l.IsChain (· ≤ ·))
    (henergy : listLogEnergy alpha l ≤ C) :
    listRelativeEnergy alpha l ≤
      (Real.exp C) ^ alpha * listLogEnergy alpha l := by
  induction l with
  | nil => simp [listRelativeEnergy, listLogEnergy]
  | cons a l ih =>
      cases l with
      | nil => simp [listRelativeEnergy, listLogEnergy]
      | cons b l =>
          simp only [List.isChain_cons_cons] at hchain
          have hab : a ≤ b := hchain.1
          have hchain' : (b :: l).IsChain (· ≤ ·) := hchain.2
          have ha0 : 0 < a := hpos a (by simp)
          have hb0 : 0 < b := hpos b (by simp)
          let x := Real.log (b : ℝ) - Real.log (a : ℝ)
          have hx0 : 0 ≤ x := sub_nonneg.mpr
            (Real.log_le_log (by exact_mod_cast ha0) (by exact_mod_cast hab))
          have htail0 : 0 ≤ listLogEnergy alpha (b :: l) :=
            listLogEnergy_nonneg alpha _ (fun d hd ↦ hpos d (by simp [hd])) hchain'
          have hxpow : x ^ alpha ≤ C := by
            have he : x ^ alpha + listLogEnergy alpha (b :: l) ≤ C := by
              simpa only [listLogEnergy] using henergy
            linarith
          have hxC : x ≤ C := gap_le_of_rpow_le halpha hx0 hC hxpow
          have htailC : listLogEnergy alpha (b :: l) ≤ C := by
            have he : x ^ alpha + listLogEnergy alpha (b :: l) ≤ C := by
              simpa only [listLogEnergy] using henergy
            linarith [Real.rpow_nonneg hx0 alpha]
          have ih' := ih (fun d hd ↦ hpos d (by simp [hd])) hchain' htailC
          have hratio : (b : ℝ) / (a : ℝ) = Real.exp x := by
            dsimp [x]
            rw [Real.exp_sub, Real.exp_log (by exact_mod_cast hb0),
              Real.exp_log (by exact_mod_cast ha0)]
          have hrel0 : 0 ≤ (b : ℝ) / (a : ℝ) - 1 := by
            rw [sub_nonneg, one_le_div (by exact_mod_cast ha0)]
            exact_mod_cast hab
          have hlin : (b : ℝ) / (a : ℝ) - 1 ≤ Real.exp C * x := by
            rw [hratio]
            exact exp_sub_one_le_exp_mul hx0 hxC
          have hterm : (((b : ℝ) / (a : ℝ) - 1) ^ alpha) ≤
              (Real.exp C) ^ alpha * x ^ alpha := by
            calc
              (((b : ℝ) / (a : ℝ) - 1) ^ alpha)
                  ≤ (Real.exp C * x) ^ alpha :=
                    Real.rpow_le_rpow hrel0 hlin (by linarith)
              _ = (Real.exp C) ^ alpha * x ^ alpha := by
                    rw [Real.mul_rpow (Real.exp_pos C).le hx0]
          simp only [listRelativeEnergy, listLogEnergy]
          calc
            ((b : ℝ) / (a : ℝ) - 1) ^ alpha + listRelativeEnergy alpha (b :: l)
                ≤ (Real.exp C) ^ alpha * x ^ alpha +
                    (Real.exp C) ^ alpha * listLogEnergy alpha (b :: l) :=
                  add_le_add hterm ih'
            _ = (Real.exp C) ^ alpha *
                  (x ^ alpha + listLogEnergy alpha (b :: l)) := by ring

lemma listLogEnergy_append (alpha : ℝ) {l₁ l₂ : List ℕ}
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    listLogEnergy alpha (l₁ ++ l₂) =
      listLogEnergy alpha l₁ +
        (Real.log (l₂.head h₂ : ℝ) - Real.log (l₁.getLast h₁ : ℝ)) ^ alpha +
          listLogEnergy alpha l₂ := by
  induction l₁ with
  | nil => contradiction
  | cons a l ih =>
      cases l with
      | nil =>
          cases l₂ with
          | nil => contradiction
          | cons b l₂ => simp [listLogEnergy]
      | cons b l =>
          rw [List.cons_append]
          simp only [listLogEnergy]
          change (Real.log (b : ℝ) - Real.log (a : ℝ)) ^ alpha +
              listLogEnergy alpha ((b :: l) ++ l₂) = _
          rw [ih (by simp)]
          have hlast : (a :: b :: l).getLast h₁ =
              (b :: l).getLast (by simp) := by simp
          rw [hlast]
          ring

lemma listLogEnergy_append_of_getLast_eq_head
    (alpha : ℝ) (halpha : alpha ≠ 0) {l₁ l₂ : List ℕ}
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (hconnect : l₁.getLast h₁ = l₂.head h₂) :
    listLogEnergy alpha (l₁ ++ l₂) =
      listLogEnergy alpha l₁ + listLogEnergy alpha l₂ := by
  rw [listLogEnergy_append alpha h₁ h₂, hconnect, sub_self]
  simp [halpha]

lemma log_nat_div_sub_log_nat_div {n a b : ℕ}
    (hn : 0 < n) (ha : a ∣ n) (hb : b ∣ n) (ha0 : 0 < a) (hb0 : 0 < b) :
    Real.log ((n / a : ℕ) : ℝ) - Real.log ((n / b : ℕ) : ℝ) =
      Real.log (b : ℝ) - Real.log (a : ℝ) := by
  rw [Nat.cast_div_charZero ha, Nat.cast_div_charZero hb]
  rw [Real.log_div (by exact_mod_cast hn.ne') (by exact_mod_cast ha0.ne'),
    Real.log_div (by exact_mod_cast hn.ne') (by exact_mod_cast hb0.ne')]
  ring

/-- Reversing a divisor list and replacing `d` by `n/d` preserves its
logarithmic gap energy. -/
lemma listLogEnergy_reverse_div {alpha : ℝ} {n : ℕ} (hn : 0 < n)
    (l : List ℕ) (hdvd : ∀ d ∈ l, d ∣ n) :
    listLogEnergy alpha (l.reverse.map (fun d ↦ n / d)) =
      listLogEnergy alpha l := by
  induction l with
  | nil => simp [listLogEnergy]
  | cons a l ih =>
      cases l with
      | nil => simp [listLogEnergy]
      | cons b l =>
          have ha : a ∣ n := hdvd a (by simp)
          have hb : b ∣ n := hdvd b (by simp)
          have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hn
          have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hb hn
          have ih' := ih (fun d hd ↦ hdvd d (by simp [hd]))
          rw [List.reverse_cons, List.map_append]
          have hrev : (List.reverse (b :: l)).map (fun d ↦ n / d) ≠ [] := by simp
          rw [listLogEnergy_append alpha hrev (by simp)]
          simp only [List.map_cons, List.map_nil, List.head_cons, listLogEnergy]
          have hlast :
              ((List.reverse (b :: l)).map (fun d ↦ n / d)).getLast hrev = n / b := by
            simp
          rw [hlast, ih', log_nat_div_sub_log_nat_div hn ha hb ha0 hb0]
          ring

lemma listLogEnergy_ofFn {alpha : ℝ} {m : ℕ} (d : Fin (m + 1) → ℕ) :
    listLogEnergy alpha (List.ofFn d) =
      gapEnergy alpha (fun i ↦ Real.log (d i : ℝ)) := by
  induction m with
  | zero => simp [listLogEnergy, gapEnergy]
  | succ m ih =>
    rw [List.ofFn_succ]
    rw [show List.ofFn (fun i : Fin (m + 1) ↦ d i.succ) =
        d (Fin.succ 0) :: List.ofFn (fun i : Fin m ↦ d i.succ.succ) by
          rw [List.ofFn_succ]]
    simp only [listLogEnergy, gapEnergy, Fin.sum_univ_succ]
    have htail := ih (fun i : Fin (m + 1) ↦ d i.succ)
    rw [List.ofFn_succ] at htail
    rw [htail]
    unfold gapEnergy
    congr 1

lemma listRelativeEnergy_ofFn {alpha : ℝ} {m : ℕ} (d : Fin (m + 1) → ℕ) :
    listRelativeEnergy alpha (List.ofFn d) = valueChainEnergy alpha d := by
  induction m with
  | zero => simp [listRelativeEnergy, valueChainEnergy]
  | succ m ih =>
    rw [List.ofFn_succ]
    rw [show List.ofFn (fun i : Fin (m + 1) ↦ d i.succ) =
        d (Fin.succ 0) :: List.ofFn (fun i : Fin m ↦ d i.succ.succ) by
          rw [List.ofFn_succ]]
    simp only [listRelativeEnergy, valueChainEnergy, Fin.sum_univ_succ]
    have htail := ih (fun i : Fin (m + 1) ↦ d i.succ)
    rw [List.ofFn_succ] at htail
    rw [htail]
    unfold valueChainEnergy
    congr 1

/-- A finite (weakly) increasing chain of divisors of `voseNumber k`, with
specified endpoints.  Weak increase is intentional: concatenation retains
the common endpoint of two pieces, producing a harmless zero-energy edge. -/
structure LogDivisorChain (k a b : ℕ) where
  values : List ℕ
  ne_nil : values ≠ []
  isChain : values.IsChain (· ≤ ·)
  head_eq : values.head ne_nil = a
  last_eq : values.getLast ne_nil = b
  dvd : ∀ d ∈ values, d ∣ voseNumber k

namespace LogDivisorChain

/-- Change only the endpoint indices of a chain along proved equalities. -/
def recast {k a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    (c : LogDivisorChain k a b) : LogDivisorChain k a' b' := by
  subst a'
  subst b'
  exact c

@[simp] lemma values_recast {k a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    (c : LogDivisorChain k a b) : (recast ha hb c).values = c.values := by
  subst a'
  subst b'
  rfl

lemma all_pos {k a b : ℕ} (c : LogDivisorChain k a b) {d : ℕ}
    (hd : d ∈ c.values) : 0 < d := by
  exact Nat.pos_of_dvd_of_pos (c.dvd d hd) (voseNumber_pos k)

lemma left_pos {k a b : ℕ} (c : LogDivisorChain k a b) : 0 < a := by
  rw [← c.head_eq]
  exact c.all_pos (List.head_mem c.ne_nil)

lemma right_pos {k a b : ℕ} (c : LogDivisorChain k a b) : 0 < b := by
  rw [← c.last_eq]
  exact c.all_pos (List.getLast_mem c.ne_nil)

def singleton {k a : ℕ} (ha : a ∣ voseNumber k) : LogDivisorChain k a a where
  values := [a]
  ne_nil := by simp
  isChain := by simp
  head_eq := by simp
  last_eq := by simp
  dvd d hd := by
    simp only [List.mem_singleton] at hd
    subst d
    exact ha

@[simp] lemma energy_singleton {alpha : ℝ} {k a : ℕ} (ha : a ∣ voseNumber k) :
    listLogEnergy alpha (singleton ha).values = 0 := by
  simp [singleton, listLogEnergy]

/-- Concatenation of chains.  The repeated common endpoint contributes
zero logarithmic energy. -/
def append {k a b c : ℕ} (p : LogDivisorChain k a b)
    (q : LogDivisorChain k b c) : LogDivisorChain k a c where
  values := p.values ++ q.values
  ne_nil := by simp [p.ne_nil]
  isChain := p.isChain.append q.isChain (by
    intro x hx y hy
    rw [List.getLast?_eq_getLast_of_ne_nil p.ne_nil] at hx
    rw [List.head?_eq_some_head q.ne_nil] at hy
    simp only [Option.mem_some_iff] at hx hy
    subst x
    subst y
    simpa [p.last_eq, q.head_eq])
  head_eq := by
    rw [List.head_append_of_ne_nil p.ne_nil]
    exact p.head_eq
  last_eq := by
    rw [List.getLast_append_of_right_ne_nil _ _ q.ne_nil]
    exact q.last_eq
  dvd d hd := by
    rw [List.mem_append] at hd
    exact hd.elim (p.dvd d) (q.dvd d)

lemma energy_append {alpha : ℝ} (halpha : alpha ≠ 0) {k a b c : ℕ}
    (p : LogDivisorChain k a b) (q : LogDivisorChain k b c) :
    listLogEnergy alpha (p.append q).values =
      listLogEnergy alpha p.values + listLogEnergy alpha q.values := by
  change listLogEnergy alpha (p.values ++ q.values) = _
  exact listLogEnergy_append_of_getLast_eq_head alpha halpha p.ne_nil q.ne_nil
    (p.last_eq.trans q.head_eq.symm)

/-- Totalized divisor complementation.  Its value at zero is chosen so the
function is antitone on all naturals; on every divisor chain it is simply
`d ↦ voseNumber k / d`. -/
def divisorComplement (n d : ℕ) : ℕ := if d = 0 then n else n / d

lemma nat_div_antitone_pos (n : ℕ) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    n / b ≤ n / a := by
  apply (Nat.le_div_iff_mul_le ha).2
  calc
    (n / b) * a ≤ (n / b) * b := Nat.mul_le_mul_left _ hab
    _ ≤ n := Nat.div_mul_le_self n b

lemma divisorComplement_antitone (n : ℕ) : Antitone (divisorComplement n) := by
  intro a b hab
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · simp [divisorComplement, hb]
    · simp [divisorComplement, hb, Nat.div_le_self]
  · have ha0 : 0 < a := Nat.pos_of_ne_zero ha
    have hb : b ≠ 0 := (ha0.trans_le hab).ne'
    simp only [divisorComplement, if_neg ha, if_neg hb]
    exact nat_div_antitone_pos n ha0 hab

/-- Reflection under `d ↦ voseNumber k / d`. -/
def reflect {k a b : ℕ} (c : LogDivisorChain k a b) :
    LogDivisorChain k (voseNumber k / b) (voseNumber k / a) where
  values := c.values.reverse.map (divisorComplement (voseNumber k))
  ne_nil := by simp [c.ne_nil]
  isChain := by
    apply List.isChain_map_of_isChain (divisorComplement (voseNumber k))
      (fun _ _ h ↦ divisorComplement_antitone _ h)
    exact List.isChain_reverse.2 c.isChain
  head_eq := by
    simp only [List.head_map]
    rw [List.head_reverse, c.last_eq]
    simp [divisorComplement, c.right_pos.ne']
  last_eq := by
    simp only [List.getLast_map]
    rw [List.getLast_reverse, c.head_eq]
    simp [divisorComplement, c.left_pos.ne']
  dvd d hd := by
    rw [List.mem_map] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    have hxdvd : x ∣ voseNumber k := c.dvd x (by simpa using hx)
    have hxpos : 0 < x := Nat.pos_of_dvd_of_pos hxdvd (voseNumber_pos k)
    simp only [divisorComplement, if_neg hxpos.ne']
    exact Nat.div_dvd_of_dvd hxdvd

lemma energy_reflect {alpha : ℝ} {k a b : ℕ} (c : LogDivisorChain k a b) :
    listLogEnergy alpha c.reflect.values = listLogEnergy alpha c.values := by
  have hmap : c.values.reverse.map (divisorComplement (voseNumber k)) =
      c.values.reverse.map (fun d ↦ voseNumber k / d) := by
    apply List.map_congr_left
    intro d hd
    have hd' : d ∈ c.values := by simpa using hd
    simp [divisorComplement, (c.all_pos hd').ne']
  change listLogEnergy alpha
    (c.values.reverse.map (divisorComplement (voseNumber k))) = _
  calc
    listLogEnergy alpha (c.values.reverse.map (divisorComplement (voseNumber k))) =
        listLogEnergy alpha (c.values.reverse.map (fun d ↦ voseNumber k / d)) :=
      congrArg (listLogEnergy alpha) hmap
    _ = listLogEnergy alpha c.values :=
      listLogEnergy_reverse_div (voseNumber_pos k) c.values c.dvd

end LogDivisorChain

/-- A `Fin`-indexed increasing chain crossing one dyadic shell. -/
def IsShellChain (k t : ℕ) {m : ℕ} (d : Fin (m + 1) → ℕ) : Prop :=
  StrictMono d ∧ d 0 = 2 ^ t ∧ d ⟨m, by omega⟩ = 2 ^ (t + 1) ∧
    ∀ i, d i ∣ voseNumber k

/-- The sorted shell gives a genuine divisor chain, together with its sharp
finite logarithmic energy estimate. -/
theorem exists_shell_chain {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k r t : ℕ} (hrk : r ≤ k) (hrt : triangular r ≤ t)
    (htk : t + 1 ≤ triangular k) :
    ∃ (m : ℕ) (d : Fin (m + 1) → ℕ),
      IsShellChain k t d ∧
      gapEnergy alpha (fun i ↦ Real.log (d i : ℝ)) ≤
        (2 * Net.dyadic r) ^ (alpha - 1) * Real.log 2 := by
  let s := shellDivisors t r
  have hsne : s.Nonempty := ⟨2 ^ t, pow_mem_shellDivisors_left t r⟩
  let m := s.card - 1
  have hcard : s.card = m + 1 := by
    dsimp [m]
    have : 0 < s.card := Finset.card_pos.mpr hsne
    omega
  let e : Fin (m + 1) ≃o s := s.orderIsoOfFin hcard
  let d : Fin (m + 1) → ℕ := fun i ↦ (e i : ℕ)
  have hdmem (i : Fin (m + 1)) : d i ∈ shellDivisors t r := by
    exact (e i).property
  have hstrict : StrictMono d := by
    intro i j hij
    exact e.lt_iff_lt.2 hij
  have hfirst : d 0 = 2 ^ t := by
    apply le_antisymm
    · have hepow := e.monotone
          (Fin.zero_le (e.symm ⟨2 ^ t, pow_mem_shellDivisors_left t r⟩))
      have hv : (e 0).val ≤
          (e (e.symm ⟨2 ^ t, pow_mem_shellDivisors_left t r⟩)).val := hepow
      change (e 0).val ≤ 2 ^ t
      simpa only [OrderIso.apply_symm_apply] using hv
    · have hm := shellDivisors_log_mem hrt (hdmem 0)
      have hposd : (0 : ℝ) < d 0 := by exact_mod_cast shellDivisors_pos (hdmem 0)
      have hlog : Real.log (((2 ^ t : ℕ) : ℝ)) ≤ Real.log (d 0 : ℝ) := by
        simpa only [log_pow_two] using hm.1
      exact_mod_cast (Real.log_le_log_iff (by positivity) hposd).mp hlog
  have hlast : d ⟨m, by omega⟩ = 2 ^ (t + 1) := by
    apply le_antisymm
    · have hm := shellDivisors_log_mem hrt (hdmem ⟨m, by omega⟩)
      have hposd : (0 : ℝ) < d ⟨m, by omega⟩ := by
        exact_mod_cast shellDivisors_pos (hdmem ⟨m, by omega⟩)
      have hlog : Real.log (d ⟨m, by omega⟩ : ℝ) ≤
          Real.log (((2 ^ (t + 1) : ℕ) : ℝ)) := by
        simpa only [log_pow_two] using hm.2
      exact_mod_cast (Real.log_le_log_iff hposd (by positivity)).mp hlog
    · have hidx : e.symm ⟨2 ^ (t + 1), pow_mem_shellDivisors_right t r⟩ ≤
          (Fin.last m : Fin (m + 1)) := Fin.le_last _
      have := e.monotone hidx
      have hv : (e (e.symm ⟨2 ^ (t + 1), pow_mem_shellDivisors_right t r⟩)).val ≤
          (e (Fin.last m)).val := this
      change 2 ^ (t + 1) ≤ (e (Fin.last m)).val
      simpa only [OrderIso.apply_symm_apply] using hv
  have hmonoLog : Monotone (fun i ↦ Real.log (d i : ℝ)) := by
    intro i j hij
    have hdij : d i ≤ d j := hstrict.monotone hij
    exact Real.log_le_log (by exact_mod_cast shellDivisors_pos (hdmem i))
      (by exact_mod_cast hdij)
  have hmesh : ∀ i : Fin m,
      Real.log (d ⟨i.1 + 1, by omega⟩ : ℝ) -
          Real.log (d ⟨i.1, by omega⟩ : ℝ) ≤ 2 * Net.dyadic r := by
    intro i
    apply shellDivisors_log_mesh hrt (hdmem _) (hdmem _) (hstrict (by simp))
    intro z hz hzbetween
    let iz : Fin (m + 1) := e.symm ⟨z, hz⟩
    have hi : (⟨i.1, by omega⟩ : Fin (m + 1)) < iz := by
      apply e.lt_iff_lt.1
      change (e ⟨i.1, by omega⟩).val < (e iz).val
      rw [show e iz = ⟨z, hz⟩ by simp [iz]]
      exact hzbetween.1
    have hiz : iz < (⟨i.1 + 1, by omega⟩ : Fin (m + 1)) := by
      apply e.lt_iff_lt.1
      change (e iz).val < (e ⟨i.1 + 1, by omega⟩).val
      rw [show e iz = ⟨z, hz⟩ by simp [iz]]
      exact hzbetween.2
    change i.1 < iz.1 at hi
    change iz.1 < i.1 + 1 at hiz
    omega
  refine ⟨m, d, ⟨hstrict, hfirst, hlast, fun i ↦
    shellDivisors_dvd hrk hrt htk (hdmem i)⟩, ?_⟩
  have henergy := gapEnergy_le_mesh_mul_length halpha
    (fun i ↦ Real.log (d i : ℝ)) hmonoLog
      (mul_nonneg (by norm_num) (Net.dyadic_nonneg r)) hmesh
  calc
    gapEnergy alpha (fun i ↦ Real.log (d i : ℝ)) ≤
        (2 * Net.dyadic r) ^ (alpha - 1) *
          (Real.log (d ⟨m, by omega⟩ : ℝ) - Real.log (d 0 : ℝ)) := henergy
    _ = (2 * Net.dyadic r) ^ (alpha - 1) * Real.log 2 := by
      rw [hlast, hfirst, log_pow_two, log_pow_two]
      push_cast
      ring

/-- List-valued form of `exists_shell_chain`, ready for concatenation. -/
theorem exists_shell_logDivisorChain {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k r t : ℕ} (hrk : r ≤ k) (hrt : triangular r ≤ t)
    (htk : t + 1 ≤ triangular k) :
    ∃ c : LogDivisorChain k (2 ^ t) (2 ^ (t + 1)),
      listLogEnergy alpha c.values ≤
        (2 * Net.dyadic r) ^ (alpha - 1) * Real.log 2 := by
  obtain ⟨m, d, hd, henergy⟩ := exists_shell_chain halpha hrk hrt htk
  let l := List.ofFn d
  have hlne : l ≠ [] := by simp [l]
  have hlchain : l.IsChain (· ≤ ·) := by
    rw [show l = List.ofFn d by rfl, List.isChain_ofFn]
    intro i hi
    exact hd.1.monotone (Fin.mk_le_mk.mpr (by omega))
  let c : LogDivisorChain k (2 ^ t) (2 ^ (t + 1)) :=
    { values := l
      ne_nil := hlne
      isChain := hlchain
      head_eq := by simpa [l] using hd.2.1
      last_eq := by
        have hlastfn := (List.getLast_ofFn_succ d).trans hd.2.2.1
        simpa only [l] using hlastfn
      dvd := by
        intro x hx
        simp only [l, List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hd.2.2.2 i }
  refine ⟨c, ?_⟩
  rw [show c.values = List.ofFn d by rfl, listLogEnergy_ofFn]
  exact henergy

/-- The geometric-polynomial majorant term for depth `r = n+3`. -/
def shellMajorantTerm (alpha : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 4) *
    (2 * Net.dyadic (n + 3)) ^ (alpha - 1) * Real.log 2

/-- Concatenate `n` consecutive unit shells, all using the same digit depth
`r`. -/
theorem exists_shell_block {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k r t n : ℕ} (hrk : r ≤ k) (hrt : triangular r ≤ t)
    (htk : t + n ≤ triangular k) :
    ∃ c : LogDivisorChain k (2 ^ t) (2 ^ (t + n)),
      listLogEnergy alpha c.values ≤
        (n : ℝ) * ((2 * Net.dyadic r) ^ (alpha - 1) * Real.log 2) := by
  induction n with
  | zero =>
      have hpow : 2 ^ t ∣ voseNumber k :=
        Nat.dvd_mul_right_of_dvd (pow_dvd_pow 2 (by simpa using htk)) _
      refine ⟨LogDivisorChain.singleton hpow, ?_⟩
      simp
  | succ n ih =>
      have htn : t + n ≤ triangular k := by omega
      obtain ⟨p, hp⟩ := ih htn
      have hrtn : triangular r ≤ t + n := hrt.trans (Nat.le_add_right t n)
      have hsucc : t + n + 1 ≤ triangular k := by omega
      obtain ⟨q, hq⟩ := exists_shell_logDivisorChain halpha hrk hrtn hsucc
      let c := p.append q
      refine ⟨c, ?_⟩
      rw [LogDivisorChain.energy_append (by linarith : alpha ≠ 0)]
      push_cast
      nlinarith

/-- A complete block at depth `r` contains exactly `r+1` dyadic shells. -/
theorem exists_depth_block {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k r : ℕ} (hrk : r + 1 ≤ k) :
    ∃ c : LogDivisorChain k (2 ^ triangular r) (2 ^ triangular (r + 1)),
      listLogEnergy alpha c.values ≤
        ((r : ℝ) + 1) *
          ((2 * Net.dyadic r) ^ (alpha - 1) * Real.log 2) := by
  have hrk' : r ≤ k := by omega
  have htri : triangular r + (r + 1) ≤ triangular k := by
    rw [← triangular_succ]
    exact triangular_mono hrk
  rw [triangular_succ]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (exists_shell_block halpha hrk' le_rfl htri)

/-- The initial six shells, from `1` to `2^triangular 3`, have a fixed
energy cost. -/
theorem exists_initial_block {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k 1 (2 ^ triangular 3),
      listLogEnergy alpha c.values ≤
        (triangular 3 : ℝ) *
          ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) := by
  have htri : triangular 0 + triangular 3 ≤ triangular k := by
    simpa using triangular_mono hk
  obtain ⟨c, hc⟩ := exists_shell_block halpha (k := k) (r := 0)
    (t := 0) (n := triangular 3) (Nat.zero_le _) (Nat.zero_le _) htri
  simpa only [triangular_zero, pow_zero, zero_add] using ⟨c, hc⟩

/-- For fixed ambient `k`, concatenate the complete depth blocks
`3,4,...,3+j-1`. -/
theorem exists_tail_blocks {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k j : ℕ} (hjk : 3 + j ≤ k) :
    ∃ c : LogDivisorChain k (2 ^ triangular 3) (2 ^ triangular (3 + j)),
      listLogEnergy alpha c.values ≤
        ∑ n ∈ Finset.range j, shellMajorantTerm alpha n := by
  induction j with
  | zero =>
      have hpow : 2 ^ triangular 3 ∣ voseNumber k :=
        Nat.dvd_mul_right_of_dvd
          (pow_dvd_pow 2 (triangular_mono (by omega : 3 ≤ k))) _
      refine ⟨LogDivisorChain.singleton hpow, ?_⟩
      simp
  | succ j ih =>
      have hjk' : 3 + j ≤ k := by omega
      obtain ⟨p, hp⟩ := ih hjk'
      obtain ⟨q, hq⟩ := exists_depth_block halpha
        (r := 3 + j) (by omega : 3 + j + 1 ≤ k)
      let c := p.append q
      have hidx : 3 + (j + 1) = 3 + j + 1 := by omega
      rw [hidx]
      refine ⟨c, ?_⟩
      rw [LogDivisorChain.energy_append (by linarith : alpha ≠ 0),
        Finset.sum_range_succ]
      ·
        have hq' : listLogEnergy alpha q.values ≤ shellMajorantTerm alpha j := by
          calc
            listLogEnergy alpha q.values ≤
                (((3 + j : ℕ) : ℝ) + 1) *
                  ((2 * Net.dyadic (3 + j)) ^ (alpha - 1) * Real.log 2) := hq
            _ = shellMajorantTerm alpha j := by
              unfold shellMajorantTerm
              rw [Nat.add_comm j 3]
              push_cast
              ring
        exact add_le_add hp hq'

/-- The full lower-half chain, from `1` to `2^triangular k`, has the stated
finite-prefix bound. -/
theorem exists_lower_chain {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k 1 (2 ^ triangular k),
      listLogEnergy alpha c.values ≤
        (triangular 3 : ℝ) *
            ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) +
          ∑ n ∈ Finset.range (k - 3), shellMajorantTerm alpha n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨p, hp⟩ := exists_initial_block halpha (by omega : 3 ≤ 3 + j)
  obtain ⟨q, hq⟩ := exists_tail_blocks halpha (le_rfl : 3 + j ≤ 3 + j)
  let c := p.append q
  refine ⟨c, ?_⟩
  rw [LogDivisorChain.energy_append (by linarith : alpha ≠ 0)]
  simpa only [Nat.add_sub_cancel_left] using add_le_add hp hq

/-! ## The cap and the convergent majorant -/

lemma log_generatorProduct (k : ℕ) :
    Real.log (generatorProduct k : ℝ) =
      (triangular k : ℝ) * Real.log 2 +
        ∑ i ∈ Finset.Icc 1 k, Net.delta i := by
  rw [generatorProduct, Nat.cast_prod, Real.log_prod]
  · simp_rw [log_generator, logDigit_eq_delta]
    rw [Finset.sum_add_distrib]
    change (∑ x ∈ Finset.Icc 1 k, (x : ℝ) * Real.log 2) +
        ∑ x ∈ Finset.Icc 1 k, Net.delta x = _
    rw [← Finset.sum_mul]
    congr 1
    rw [triangular, Nat.cast_sum]
  · intro i hi
    exact_mod_cast generator_ne_zero i

lemma pow_triangular_le_generatorProduct (k : ℕ) :
    2 ^ triangular k ≤ generatorProduct k := by
  calc
    2 ^ triangular k = ∏ i ∈ Finset.Icc 1 k, 2 ^ i := by
      rw [triangular, Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ i ∈ Finset.Icc 1 k, generator i := by
      exact Finset.prod_le_prod' fun i _ ↦ by simp [generator]
    _ = generatorProduct k := rfl

/-- The single central cap has logarithmic length less than one. -/
lemma cap_log_gap_lt_one (k : ℕ) :
    Real.log (generatorProduct k : ℝ) -
        Real.log ((2 ^ triangular k : ℕ) : ℝ) < 1 := by
  rw [log_generatorProduct, log_pow_two]
  have := Net.sum_delta_lt_one k
  push_cast
  linarith

/-- Consequently the cap's relative gap is less than `2`. -/
lemma cap_relative_gap_lt_two (k : ℕ) :
    (generatorProduct k : ℝ) / (2 ^ triangular k : ℕ) - 1 < 2 := by
  have hpowpos : (0 : ℝ) < (2 ^ triangular k : ℕ) := by positivity
  have hprodpos : (0 : ℝ) < generatorProduct k := by
    exact_mod_cast generatorProduct_pos k
  have hlog : Real.log ((generatorProduct k : ℝ) /
      (2 ^ triangular k : ℕ)) < 1 := by
    rw [Real.log_div hprodpos.ne' hpowpos.ne']
    exact cap_log_gap_lt_one k
  have hratio_pos : 0 < (generatorProduct k : ℝ) /
      (2 ^ triangular k : ℕ) := div_pos hprodpos hpowpos
  have hratio : (generatorProduct k : ℝ) /
      (2 ^ triangular k : ℕ) < Real.exp 1 := by
    exact (Real.log_lt_iff_lt_exp hratio_pos).mp (by simpa using hlog)
  have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
  linarith

/-- The cap from the last power of two to the generator product. -/
theorem exists_cap_chain {alpha : ℝ} (halpha : 1 ≤ alpha) (k : ℕ) :
    ∃ c : LogDivisorChain k (2 ^ triangular k) (generatorProduct k),
      listLogEnergy alpha c.values ≤ 1 := by
  have hpowdvd : 2 ^ triangular k ∣ voseNumber k := by
    rw [voseNumber]
    exact dvd_mul_right _ _
  have hprodvd : generatorProduct k ∣ voseNumber k := by
    rw [voseNumber]
    exact dvd_mul_left _ _
  let c : LogDivisorChain k (2 ^ triangular k) (generatorProduct k) :=
    { values := [2 ^ triangular k, generatorProduct k]
      ne_nil := by simp
      isChain := by simpa using pow_triangular_le_generatorProduct k
      head_eq := by simp
      last_eq := by simp
      dvd := by
        intro d hd
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
        rcases hd with rfl | rfl
        · exact hpowdvd
        · exact hprodvd }
  refine ⟨c, ?_⟩
  have hgap0 : 0 ≤ Real.log (generatorProduct k : ℝ) -
      Real.log ((2 ^ triangular k : ℕ) : ℝ) := by
    exact sub_nonneg.mpr (Real.log_le_log
      (by positivity : (0 : ℝ) < ((2 ^ triangular k : ℕ) : ℝ))
      (by exact_mod_cast pow_triangular_le_generatorProduct k))
  have hgap1 : Real.log (generatorProduct k : ℝ) -
      Real.log ((2 ^ triangular k : ℕ) : ℝ) ≤ 1 :=
    (cap_log_gap_lt_one k).le
  change listLogEnergy alpha [2 ^ triangular k, generatorProduct k] ≤ 1
  simp only [listLogEnergy, add_zero]
  change (Real.log (generatorProduct k : ℝ) -
      Real.log ((2 ^ triangular k : ℕ) : ℝ)) ^ alpha ≤ 1
  simpa using Real.rpow_le_one hgap0 hgap1 (by linarith : 0 ≤ alpha)

def shellMajorant (alpha : ℝ) : ℝ :=
  ∑' n : ℕ, shellMajorantTerm alpha n

lemma shellMajorantTerm_nonneg {alpha : ℝ} (halpha : 1 ≤ alpha) (n : ℕ) :
    0 ≤ shellMajorantTerm alpha n := by
  unfold shellMajorantTerm
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (Real.rpow_nonneg (mul_nonneg (by norm_num) (Net.dyadic_nonneg _)) _))
    (Real.log_nonneg (by norm_num))

lemma two_mul_dyadic_add_three (n : ℕ) :
    2 * Net.dyadic (n + 3) = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
  rw [Net.dyadic, pow_add]
  norm_num
  ring

lemma shellMajorantTerm_eq_geometric {alpha : ℝ} (n : ℕ) :
    shellMajorantTerm alpha n =
      ((1 / 4 : ℝ) ^ (alpha - 1) * Real.log 2) *
        (((n : ℝ) + 4) * ((1 / 2 : ℝ) ^ (alpha - 1)) ^ n) := by
  rw [shellMajorantTerm, two_mul_dyadic_add_three]
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1 / 4)
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n)]
  have hpow : (((1 / 2 : ℝ) ^ n) ^ (alpha - 1)) =
      (((1 / 2 : ℝ) ^ (alpha - 1)) ^ n) := by
    rw [← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 1 / 2),
      ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring
  rw [hpow]
  ring

/-- The shell majorant is a genuinely convergent series for every
`alpha > 1`. -/
lemma summable_shellMajorantTerm {alpha : ℝ} (halpha : 1 < alpha) :
    Summable (shellMajorantTerm alpha) := by
  let q : ℝ := (1 / 2 : ℝ) ^ (alpha - 1)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqlt : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr halpha)
  have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hqlt
  have hsumn : Summable (fun n : ℕ ↦ (n : ℝ) * q ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm)
  have hsumc : Summable (fun n : ℕ ↦ (4 : ℝ) * q ^ n) :=
    (summable_geometric_of_norm_lt_one hqnorm).mul_left 4
  have hsum : Summable (fun n : ℕ ↦ ((n : ℝ) + 4) * q ^ n) := by
    convert hsumn.add hsumc using 1
    ext n
    ring
  have hmul := hsum.mul_left ((1 / 4 : ℝ) ^ (alpha - 1) * Real.log 2)
  simpa only [q, ← shellMajorantTerm_eq_geometric] using hmul

lemma shellMajorant_nonneg {alpha : ℝ} (halpha : 1 ≤ alpha) :
    0 ≤ shellMajorant alpha := by
  unfold shellMajorant
  exact tsum_nonneg fun n ↦ shellMajorantTerm_nonneg halpha n

lemma sum_shellMajorantTerm_le {alpha : ℝ} (halpha : 1 < alpha) (j : ℕ) :
    (∑ n ∈ Finset.range j, shellMajorantTerm alpha n) ≤ shellMajorant alpha := by
  unfold shellMajorant
  exact (summable_shellMajorantTerm halpha).sum_le_tsum (Finset.range j)
    (fun n _ ↦ shellMajorantTerm_nonneg halpha.le n)

/-- A lower chain followed by the cap, uniformly bounded independently of
`k`. -/
theorem exists_lower_cap_chain {alpha : ℝ} (halpha : 1 < alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k 1 (generatorProduct k),
      listLogEnergy alpha c.values ≤
        (triangular 3 : ℝ) *
            ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) +
          shellMajorant alpha + 1 := by
  obtain ⟨p, hp⟩ := exists_lower_chain halpha.le hk
  obtain ⟨q, hq⟩ := exists_cap_chain halpha.le k
  let c := p.append q
  refine ⟨c, ?_⟩
  rw [LogDivisorChain.energy_append (by linarith : alpha ≠ 0)]
  have hprefix := sum_shellMajorantTerm_le halpha (k - 3)
  linarith

/-- Complementation turns the lower chain into the upper chain, beginning at
the generator product. -/
theorem reflect_lower_chain {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k (generatorProduct k) (voseNumber k),
      listLogEnergy alpha c.values ≤
        (triangular 3 : ℝ) *
            ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) +
          ∑ n ∈ Finset.range (k - 3), shellMajorantTerm alpha n := by
  obtain ⟨p, hp⟩ := exists_lower_chain halpha hk
  have hleft : voseNumber k / 2 ^ triangular k = generatorProduct k := by
    rw [voseNumber]
    simpa [Nat.mul_comm] using Nat.mul_div_left (generatorProduct k) (2 ^ triangular k)
  have hright : voseNumber k / 1 = voseNumber k := by simp
  let c : LogDivisorChain k (generatorProduct k) (voseNumber k) :=
    LogDivisorChain.recast hleft hright p.reflect
  refine ⟨c, ?_⟩
  simpa only [c, LogDivisorChain.values_recast, LogDivisorChain.energy_reflect] using hp

/-- The promised global finite divisor chain.  Its logarithmic `alpha`-energy
is bounded by a constant depending only on `alpha`, uniformly in `k`. -/
theorem exists_global_logDivisorChain {alpha : ℝ} (halpha : 1 < alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k 1 (voseNumber k),
      listLogEnergy alpha c.values ≤
        2 * ((triangular 3 : ℝ) *
              ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) +
            shellMajorant alpha) + 1 := by
  obtain ⟨p, hp⟩ := exists_lower_cap_chain halpha hk
  obtain ⟨q, hq⟩ := reflect_lower_chain halpha.le hk
  let c := p.append q
  refine ⟨c, ?_⟩
  rw [LogDivisorChain.energy_append (by linarith : alpha ≠ 0)]
  have hprefix := sum_shellMajorantTerm_le halpha (k - 3)
  linarith

/-- An explicit uniform constant for relative-gap energy of the constructed
chains. -/
def globalLogBound (alpha : ℝ) : ℝ :=
  2 * ((triangular 3 : ℝ) *
        ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) +
      shellMajorant alpha) + 1

def globalRelativeBound (alpha : ℝ) : ℝ :=
  (Real.exp (globalLogBound alpha)) ^ alpha * globalLogBound alpha

lemma one_le_globalLogBound {alpha : ℝ} (halpha : 1 < alpha) :
    1 ≤ globalLogBound alpha := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hshell : 0 ≤ shellMajorant alpha := shellMajorant_nonneg halpha.le
  have hdy : 0 ≤ 2 * Net.dyadic 0 :=
    mul_nonneg (by norm_num) (Net.dyadic_nonneg 0)
  have hpow : 0 ≤ (2 * Net.dyadic 0) ^ (alpha - 1) :=
    Real.rpow_nonneg hdy _
  have hearly : 0 ≤ (triangular 3 : ℝ) *
      ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) :=
    mul_nonneg (by positivity) (mul_nonneg hpow hlog)
  unfold globalLogBound
  linarith

lemma globalRelativeBound_nonneg {alpha : ℝ} (halpha : 1 < alpha) :
    0 ≤ globalRelativeBound alpha := by
  unfold globalRelativeBound
  exact mul_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _)
    (le_trans (by norm_num) (one_le_globalLogBound halpha))

/-- Final construction-side estimate: for every `k ≥ 3` there is a finite
increasing divisor chain from `1` to `voseNumber k` whose relative-gap
`alpha`-energy is bounded by a constant independent of `k`.

The chain is weakly increasing because concatenation retains common
endpoints.  Deleting repetitions makes it strictly increasing and leaves its
energy unchanged. -/
theorem exists_global_relativeDivisorChain {alpha : ℝ} (halpha : 1 < alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k 1 (voseNumber k),
      listRelativeEnergy alpha c.values ≤ globalRelativeBound alpha := by
  obtain ⟨c, hc⟩ := exists_global_logDivisorChain halpha hk
  refine ⟨c, ?_⟩
  have hconvert := listRelativeEnergy_le_exp_mul_listLogEnergy
    halpha.le (one_le_globalLogBound halpha) c.values
    (fun d hd ↦ c.all_pos hd) c.isChain (by simpa [globalLogBound] using hc)
  calc
    listRelativeEnergy alpha c.values
        ≤ (Real.exp (globalLogBound alpha)) ^ alpha *
            listLogEnergy alpha c.values := hconvert
    _ ≤ (Real.exp (globalLogBound alpha)) ^ alpha * globalLogBound alpha := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [globalLogBound] using hc)
        (Real.rpow_nonneg (Real.exp_pos _).le _)
    _ = globalRelativeBound alpha := rfl

/-- The complete ordered divisor sequence has no more relative-gap energy
than the uniformly bounded Vose chain. -/
theorem hAlpha_voseNumber_le_globalRelativeBound {alpha : ℝ}
    (halpha : 1 < alpha) {k : ℕ} (hk : 3 ≤ k) :
    hAlpha alpha (voseNumber k) ≤ globalRelativeBound alpha := by
  obtain ⟨c, hc⟩ := exists_global_relativeDivisorChain halpha hk
  let m := c.values.length - 1
  have hlenpos : 0 < c.values.length := List.length_pos_of_ne_nil c.ne_nil
  have hlen : c.values.length = m + 1 := by
    dsimp [m]
    omega
  let e : Fin (m + 1) → Fin c.values.length := fun i ↦ Fin.cast hlen.symm i
  let d : Fin (m + 1) → ℕ := fun i ↦ c.values.get (e i)
  have hdmem : ∀ i, d i ∈ (voseNumber k).divisors := by
    intro i
    apply Nat.mem_divisors.mpr
    exact ⟨c.dvd (d i) (List.get_mem c.values (e i)), (voseNumber_pos k).ne'⟩
  have hdmono : Monotone d := by
    intro i j hij
    exact c.isChain.sortedLE.monotone_get (by
      change i.1 ≤ j.1
      exact hij)
  have hd0 : d ⟨0, by omega⟩ = 1 := by
    have hh := (c.values.head_eq_getElem_zero c.ne_nil).symm.trans c.head_eq
    have he0 : e ⟨0, by omega⟩ = ⟨0, hlenpos⟩ := by
      apply Fin.ext
      rfl
    change c.values.get (e ⟨0, by omega⟩) = 1
    rw [he0]
    exact hh
  have hdlast : d ⟨m, by omega⟩ = voseNumber k := by
    have hh := (List.get_length_sub_one (by omega :
      c.values.length - 1 < c.values.length)).trans c.last_eq
    have helast : e ⟨m, by omega⟩ =
        ⟨c.values.length - 1, by omega⟩ := by
      apply Fin.ext
      simp only [e, Fin.coe_cast, m]
    change c.values.get (e ⟨m, by omega⟩) = voseNumber k
    rw [helast]
    exact hh
  have hof : List.ofFn d = c.values := by
    have hcongr := List.ofFn_congr hlen c.values.get
    exact (by simpa only [d, e] using hcongr.symm.trans (List.ofFn_get c.values))
  calc
    hAlpha alpha (voseNumber k) ≤ valueChainEnergy alpha d :=
      hAlpha_le_valueChainEnergy halpha.le (voseNumber_pos k).ne' d hdmem hdmono hd0 hdlast
    _ = listRelativeEnergy alpha c.values := by
      rw [← listRelativeEnergy_ofFn, hof]
    _ ≤ globalRelativeBound alpha := hc

end

end Erdos1099
