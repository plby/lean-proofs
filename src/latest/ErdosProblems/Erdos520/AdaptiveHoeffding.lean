import ErdosProblems.Erdos520.Bonami
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset
open scoped BigOperators

namespace Erdos.Problem520

def coinSign (b : Bool) : ℝ := if b then 1 else -1

inductive AdaptiveRademacherTree : ℕ → Type
  | nil : AdaptiveRademacherTree 0
  | node {n : ℕ} (c : ℝ) (next : Bool → AdaptiveRademacherTree n) :
      AdaptiveRademacherTree (n + 1)

def adaptiveSum : {n : ℕ} → AdaptiveRademacherTree n → (Fin n → Bool) → ℝ
  | 0, .nil, _ => 0
  | _ + 1, .node c next, omega =>
      c * coinSign (omega 0) + adaptiveSum (next (omega 0)) (Fin.tail omega)

def adaptiveSquareSum : {n : ℕ} → AdaptiveRademacherTree n → (Fin n → Bool) → ℝ
  | 0, .nil, _ => 0
  | _ + 1, .node c next, omega =>
      c ^ 2 + adaptiveSquareSum (next (omega 0)) (Fin.tail omega)

/-- Coefficients of a predictable Rademacher transform: the coefficient at
time `k` is a function only of the first `k` signs. -/
abbrev PredictableCoefficients (n : ℕ) :=
  (k : Fin n) → (Fin k → Bool) → ℝ

/-- Turn prefix-indexed predictable coefficients into their binary decision
tree. -/
def treeOfPredictable : (n : ℕ) →
    PredictableCoefficients n → AdaptiveRademacherTree n
  | 0, _ => .nil
  | n + 1, coeff => .node (coeff 0 Fin.elim0) (fun b =>
      treeOfPredictable n (fun k past => coeff k.succ (Fin.cons b past)))

def finPast {n : ℕ} (omega : Fin n → Bool) (k : Fin n) : Fin k → Bool :=
  fun i => omega ⟨i, i.isLt.trans k.isLt⟩

lemma finPast_zero {n : ℕ} (omega : Fin (n + 1) → Bool) :
    finPast omega 0 = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

lemma finPast_succ {n : ℕ} (omega : Fin (n + 1) → Bool) (k : Fin n) :
    Fin.cons (omega 0) (finPast (Fin.tail omega) k) =
      finPast omega k.succ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

noncomputable def predictableSum {n : ℕ} (coeff : PredictableCoefficients n)
    (omega : Fin n → Bool) : ℝ :=
  ∑ k, coeff k (finPast omega k) * coinSign (omega k)

noncomputable def predictableSquareSum {n : ℕ}
    (coeff : PredictableCoefficients n) (omega : Fin n → Bool) : ℝ :=
  ∑ k, (coeff k (finPast omega k)) ^ 2

theorem adaptiveSum_treeOfPredictable {n : ℕ}
    (coeff : PredictableCoefficients n) (omega : Fin n → Bool) :
    adaptiveSum (treeOfPredictable n coeff) omega =
      predictableSum coeff omega := by
  induction n with
  | zero => simp [treeOfPredictable, adaptiveSum, predictableSum]
  | succ n ih =>
      rw [predictableSum, Fin.sum_univ_succ]
      simp only [treeOfPredictable, adaptiveSum]
      rw [ih]
      congr 1
      · rw [finPast_zero]
      · unfold predictableSum
        apply Finset.sum_congr rfl
        intro k hk
        change coeff k.succ (Fin.cons (omega 0) (finPast (Fin.tail omega) k)) *
          coinSign (omega k.succ) = _
        rw [finPast_succ]

theorem adaptiveSquareSum_treeOfPredictable {n : ℕ}
    (coeff : PredictableCoefficients n) (omega : Fin n → Bool) :
    adaptiveSquareSum (treeOfPredictable n coeff) omega =
      predictableSquareSum coeff omega := by
  induction n with
  | zero => simp [treeOfPredictable, adaptiveSquareSum, predictableSquareSum]
  | succ n ih =>
      rw [predictableSquareSum, Fin.sum_univ_succ]
      simp only [treeOfPredictable, adaptiveSquareSum]
      rw [ih]
      congr 1
      · rw [finPast_zero]
      · unfold predictableSquareSum
        apply Finset.sum_congr rfl
        intro k hk
        change coeff k.succ (Fin.cons (omega 0) (finPast (Fin.tail omega) k)) ^ 2 = _
        rw [finPast_succ]

lemma fintypeAverage_const_mul {ι : Type*} [Fintype ι]
    (c : ℝ) (g : ι → ℝ) :
    fintypeAverage (fun i => c * g i) = c * fintypeAverage g := by
  unfold fintypeAverage
  change (∑ i, c * g i) / (Fintype.card ι : ℝ) =
    c * ((∑ i, g i) / (Fintype.card ι : ℝ))
  rw [← Finset.mul_sum]
  ring

lemma fintypeAverage_add {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) :
    fintypeAverage (fun i => f i + g i) =
      fintypeAverage f + fintypeAverage g := by
  unfold fintypeAverage
  rw [Finset.sum_add_distrib]
  ring

lemma fintypeAverage_const_mul_div {ι : Type*} [Fintype ι]
    (c d : ℝ) (g : ι → ℝ) :
    fintypeAverage (fun i => c * g i / d) = c / d * fintypeAverage g := by
  unfold fintypeAverage
  change (∑ i, c * g i / d) / (Fintype.card ι : ℝ) =
    c / d * ((∑ i, g i) / (Fintype.card ι : ℝ))
  rw [← Finset.sum_div, ← Finset.mul_sum]
  ring

theorem adaptive_mgf_le_one {n : ℕ} (A : AdaptiveRademacherTree n) (t : ℝ) :
    fintypeAverage (fun omega : Fin n → Bool =>
      Real.exp (t * adaptiveSum A omega -
        t ^ 2 / 2 * adaptiveSquareSum A omega)) ≤ 1 := by
  induction A with
  | nil => simp [fintypeAverage, adaptiveSum, adaptiveSquareSum]
  | @node n c next ih =>
      rw [fintypeAverage_fin_succ]
      have hfalse (omega : Fin n → Bool) :
          Real.exp (t * adaptiveSum (.node c next) (Fin.cons false omega) -
              t ^ 2 / 2 * adaptiveSquareSum (.node c next) (Fin.cons false omega)) =
            Real.exp (-t * c - t ^ 2 * c ^ 2 / 2) *
              Real.exp (t * adaptiveSum (next false) omega -
                t ^ 2 / 2 * adaptiveSquareSum (next false) omega) := by
        rw [← Real.exp_add]
        congr 1
        simp [adaptiveSum, adaptiveSquareSum, coinSign]
        ring
      have htrue (omega : Fin n → Bool) :
          Real.exp (t * adaptiveSum (.node c next) (Fin.cons true omega) -
              t ^ 2 / 2 * adaptiveSquareSum (.node c next) (Fin.cons true omega)) =
            Real.exp (t * c - t ^ 2 * c ^ 2 / 2) *
              Real.exp (t * adaptiveSum (next true) omega -
                t ^ 2 / 2 * adaptiveSquareSum (next true) omega) := by
        rw [← Real.exp_add]
        congr 1
        simp [adaptiveSum, adaptiveSquareSum, coinSign]
        ring
      simp_rw [hfalse, htrue, add_div]
      rw [fintypeAverage_add]
      rw [fintypeAverage_const_mul_div,
        fintypeAverage_const_mul_div]
      have ihfalse := ih false
      have ihtrue := ih true
      calc
        Real.exp (-t * c - t ^ 2 * c ^ 2 / 2) / 2 *
              fintypeAverage (fun omega : Fin n → Bool =>
                Real.exp (t * adaptiveSum (next false) omega -
                  t ^ 2 / 2 * adaptiveSquareSum (next false) omega)) +
            Real.exp (t * c - t ^ 2 * c ^ 2 / 2) / 2 *
              fintypeAverage (fun omega : Fin n → Bool =>
                Real.exp (t * adaptiveSum (next true) omega -
                  t ^ 2 / 2 * adaptiveSquareSum (next true) omega))
            ≤ Real.exp (-t * c - t ^ 2 * c ^ 2 / 2) / 2 +
                Real.exp (t * c - t ^ 2 * c ^ 2 / 2) / 2 := by
              apply add_le_add
              · have hc : 0 ≤ Real.exp (-t * c - t ^ 2 * c ^ 2 / 2) / 2 :=
                  div_nonneg (Real.exp_pos _).le (by norm_num)
                simpa using! mul_le_mul_of_nonneg_left ihfalse hc
              · have hc : 0 ≤ Real.exp (t * c - t ^ 2 * c ^ 2 / 2) / 2 :=
                  div_nonneg (Real.exp_pos _).le (by norm_num)
                simpa using! mul_le_mul_of_nonneg_left ihtrue hc
        _ = Real.exp (-(t ^ 2 * c ^ 2 / 2)) * Real.cosh (t * c) := by
              rw [Real.cosh_eq]
              rw [show -t * c - t ^ 2 * c ^ 2 / 2 =
                  -(t ^ 2 * c ^ 2 / 2) + -(t * c) by ring,
                show t * c - t ^ 2 * c ^ 2 / 2 =
                  -(t ^ 2 * c ^ 2 / 2) + t * c by ring,
                Real.exp_add, Real.exp_add]
              ring
        _ ≤ Real.exp (-(t ^ 2 * c ^ 2 / 2)) *
              Real.exp ((t * c) ^ 2 / 2) := by
              gcongr
              exact Real.cosh_le_exp_half_sq _
        _ = 1 := by
              rw [← Real.exp_add]
              convert! Real.exp_zero using 1
              ring_nf

theorem adaptive_oneSidedTail_average_le {n : ℕ}
    (A : AdaptiveRademacherTree n) {u T sigma : ℝ}
    (hu : 0 ≤ u) (hT : 0 < T) (hsigma : sigma ^ 2 = 1) :
    fintypeAverage (fun omega : Fin n → Bool =>
      if u ≤ sigma * adaptiveSum A omega ∧
          adaptiveSquareSum A omega ≤ T then (1 : ℝ) else 0) ≤
      Real.exp (-u ^ 2 / (2 * T)) := by
  let t : ℝ := (u / T) * sigma
  let c : ℝ := Real.exp (-u ^ 2 / (2 * T))
  let Z : (Fin n → Bool) → ℝ := fun omega =>
    Real.exp (t * adaptiveSum A omega -
      t ^ 2 / 2 * adaptiveSquareSum A omega)
  have htbase : 0 ≤ u / T := div_nonneg hu hT.le
  have ht_sq : t ^ 2 = (u / T) ^ 2 := by
    dsimp [t]
    rw [mul_pow, hsigma, mul_one]
  have hpoint (omega : Fin n → Bool) :
      (if u ≤ sigma * adaptiveSum A omega ∧
          adaptiveSquareSum A omega ≤ T then (1 : ℝ) else 0) ≤
        c * Z omega := by
    split_ifs with hgood
    · rcases hgood with ⟨hsum, hsq⟩
      have hsum' : (u / T) * u ≤ t * adaptiveSum A omega := by
        dsimp [t]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hsum htbase
      have hqcoef : 0 ≤ t ^ 2 / 2 := by positivity
      have hq : -(t ^ 2 / 2) * T ≤
          -(t ^ 2 / 2) * adaptiveSquareSum A omega := by
        exact mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hqcoef)
      have hexponent :
          0 ≤ -u ^ 2 / (2 * T) +
            (t * adaptiveSum A omega -
              t ^ 2 / 2 * adaptiveSquareSum A omega) := by
        calc
          0 = -u ^ 2 / (2 * T) + (u / T) * u -
              ((u / T) ^ 2 / 2) * T := by
                field_simp
                ring
          _ ≤ -u ^ 2 / (2 * T) + t * adaptiveSum A omega -
              (t ^ 2 / 2) * T := by
                rw [ht_sq]
                linarith
          _ ≤ -u ^ 2 / (2 * T) + t * adaptiveSum A omega -
              (t ^ 2 / 2) * adaptiveSquareSum A omega := by
                linarith
          _ = -u ^ 2 / (2 * T) +
              (t * adaptiveSum A omega -
                t ^ 2 / 2 * adaptiveSquareSum A omega) := by ring
      change 1 ≤ Real.exp (-u ^ 2 / (2 * T)) *
        Real.exp (t * adaptiveSum A omega -
          t ^ 2 / 2 * adaptiveSquareSum A omega)
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      simpa [sub_eq_add_neg, add_assoc] using! hexponent
    · exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc
    fintypeAverage (fun omega : Fin n → Bool =>
        if u ≤ sigma * adaptiveSum A omega ∧
            adaptiveSquareSum A omega ≤ T then (1 : ℝ) else 0)
        ≤ fintypeAverage (fun omega => c * Z omega) :=
          fintypeAverage_mono hpoint
    _ = c * fintypeAverage Z := fintypeAverage_const_mul c Z
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left
      (by simpa [Z] using! adaptive_mgf_le_one A t) (Real.exp_pos _).le
    _ = Real.exp (-u ^ 2 / (2 * T)) := by simp [c]

theorem adaptive_absTail_average_le {n : ℕ}
    (A : AdaptiveRademacherTree n) {u T : ℝ}
    (hu : 0 ≤ u) (hT : 0 < T) :
    fintypeAverage (fun omega : Fin n → Bool =>
      if u ≤ |adaptiveSum A omega| ∧
          adaptiveSquareSum A omega ≤ T then (1 : ℝ) else 0) ≤
      2 * Real.exp (-u ^ 2 / (2 * T)) := by
  let upper : (Fin n → Bool) → ℝ := fun omega =>
    if u ≤ adaptiveSum A omega ∧ adaptiveSquareSum A omega ≤ T then 1 else 0
  let lower : (Fin n → Bool) → ℝ := fun omega =>
    if u ≤ -adaptiveSum A omega ∧ adaptiveSquareSum A omega ≤ T then 1 else 0
  have hpoint (omega : Fin n → Bool) :
      (if u ≤ |adaptiveSum A omega| ∧ adaptiveSquareSum A omega ≤ T
          then (1 : ℝ) else 0) ≤ upper omega + lower omega := by
    dsimp [upper, lower]
    by_cases habs : u ≤ |adaptiveSum A omega|
    · by_cases hsq : adaptiveSquareSum A omega ≤ T
      · simp only [habs, hsq, and_self, if_true]
        rw [le_abs] at habs
        rcases habs with hpos | hneg
        · by_cases hlower : u ≤ -adaptiveSum A omega
          <;> simp [hpos, hlower]
        · by_cases hupper : u ≤ adaptiveSum A omega
          <;> simp [hupper, hneg]
      · simp [hsq]
    · simp only [habs, false_and, if_false]
      split_ifs <;> norm_num
  calc
    fintypeAverage (fun omega : Fin n → Bool =>
        if u ≤ |adaptiveSum A omega| ∧
            adaptiveSquareSum A omega ≤ T then (1 : ℝ) else 0)
        ≤ fintypeAverage (fun omega => upper omega + lower omega) :=
          fintypeAverage_mono hpoint
    _ = fintypeAverage upper + fintypeAverage lower :=
      fintypeAverage_add upper lower
    _ ≤ Real.exp (-u ^ 2 / (2 * T)) +
        Real.exp (-u ^ 2 / (2 * T)) := by
      apply add_le_add
      · simpa [upper] using!
          (adaptive_oneSidedTail_average_le A hu hT
            (sigma := (1 : ℝ)) (by norm_num))
      · simpa [lower] using!
          (adaptive_oneSidedTail_average_le A hu hT
            (sigma := (-1 : ℝ)) (by norm_num))
    _ = 2 * Real.exp (-u ^ 2 / (2 * T)) := by ring

/-- Stopped Hoeffding for an arbitrary finite predictable Rademacher
transform, stated directly in prefix-coefficient form. -/
theorem predictable_absTail_average_le {n : ℕ}
    (coeff : PredictableCoefficients n) {u T : ℝ}
    (hu : 0 ≤ u) (hT : 0 < T) :
    fintypeAverage (fun omega : Fin n → Bool =>
      if u ≤ |predictableSum coeff omega| ∧
          predictableSquareSum coeff omega ≤ T then (1 : ℝ) else 0) ≤
      2 * Real.exp (-u ^ 2 / (2 * T)) := by
  simpa only [adaptiveSum_treeOfPredictable,
    adaptiveSquareSum_treeOfPredictable] using!
      adaptive_absTail_average_le (treeOfPredictable n coeff) hu hT

end Erdos.Problem520
