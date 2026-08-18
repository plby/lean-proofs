/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos136.Freedman

/-!
# Bounded differences for sparse Bernoulli product spaces

This file gives the biased bounded-differences estimate used by the random
greedy construction.  In contrast with ordinary McDiarmid, the variance
budget remembers the Bernoulli bias: coordinate `i` contributes
`q * (1 - q) * c i ^ 2`.

The proof is the finite Doob-martingale proof.  We successively average one
coordinate of the function (`McDiarmid.sectionAverage`).  The centered
two-point increment has conditional mean zero, absolute value at most `c i`,
and conditional second moment at most `q * (1-q) * c i ^ 2`.  The elementary
exponential estimate is the one used in `Freedman.freedman`; iterating it and
optimizing the exponential parameter gives the same Bernstein denominator.
-/

open scoped BigOperators

namespace Erdos136.BernoulliFreedman

set_option autoImplicit false

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary finite product-space infrastructure -/

/-- The mass of a point in a finite product distribution. -/
def productMass {α : Type*} [Fintype α] {n : ℕ}
    (w : Fin n → α → ℝ) (x : Fin n → α) : ℝ :=
  ∏ i, w i (x i)

/-- Weighted expectation on a finite product space. -/
def weightedMean {α : Type*} [Fintype α] {n : ℕ}
    (w : Fin n → α → ℝ) (f : (Fin n → α) → ℝ) : ℝ :=
  ∑ x, productMass w x * f x

lemma sum_fin_succ_eq {α β : Type*} [Fintype α] [AddCommMonoid β] {n : ℕ}
    (F : (Fin (n + 1) → α) → β) :
    ∑ x, F x = ∑ a : α, ∑ y : Fin n → α, F (Fin.cons a y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ α)).sum_comp]
  exact Fintype.sum_prod_type _

@[simp] lemma productMass_cons {α : Type*} [Fintype α] {n : ℕ}
    (w : Fin (n + 1) → α → ℝ) (a : α) (y : Fin n → α) :
    productMass w (Fin.cons a y) =
      w 0 a * productMass (fun i z ↦ w i.succ z) y := by
  simp [productMass, Fin.prod_univ_succ]

/-- Average over the first coordinate, retaining the other coordinates. -/
def sectionAverage {α : Type*} [Fintype α] {n : ℕ}
    (w : Fin (n + 1) → α → ℝ) (f : (Fin (n + 1) → α) → ℝ)
    (y : Fin n → α) : ℝ :=
  ∑ a, w 0 a * f (Fin.cons a y)

lemma weightedMean_succ {α : Type*} [Fintype α] {n : ℕ}
    (w : Fin (n + 1) → α → ℝ) (f : (Fin (n + 1) → α) → ℝ) :
    weightedMean w f =
      weightedMean (fun i z ↦ w i.succ z) (sectionAverage w f) := by
  simp only [weightedMean, sum_fin_succ_eq, productMass_cons, sectionAverage]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma productMass_nonneg {α : Type*} [Fintype α] {n : ℕ}
    (w : Fin n → α → ℝ) (hw0 : ∀ i a, 0 ≤ w i a) (x : Fin n → α) :
    0 ≤ productMass w x := by
  exact Finset.prod_nonneg fun i _ ↦ hw0 i (x i)

lemma sum_productMass_eq_one {α : Type*} [Fintype α] {n : ℕ}
    (w : Fin n → α → ℝ) (hw1 : ∀ i, ∑ a, w i a = 1) :
    ∑ x, productMass w x = 1 := by
  induction n with
  | zero => simp [productMass]
  | succ n ih =>
      rw [sum_fin_succ_eq]
      simp_rw [productMass_cons, ← Finset.mul_sum]
      rw [← Finset.sum_mul, hw1 0]
      simp only [one_mul]
      simpa using ih (fun i a ↦ w i.succ a) (fun i ↦ hw1 i.succ)

lemma sectionAverage_boundedDiff {α : Type*} [Fintype α] {n : ℕ}
    (w : Fin (n + 1) → α → ℝ) (f : (Fin (n + 1) → α) → ℝ)
    (c : Fin (n + 1) → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hbd : ∀ i (x y : Fin (n + 1) → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) →
      |sectionAverage w f x - sectionAverage w f y| ≤ c i.succ := by
  intro i x y hxy
  rw [sectionAverage, sectionAverage, ← Finset.sum_sub_distrib]
  calc
    |∑ a, (w 0 a * f (Fin.cons a x) - w 0 a * f (Fin.cons a y))|
        ≤ ∑ a, |w 0 a * f (Fin.cons a x) - w 0 a * f (Fin.cons a y)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, w 0 a * |f (Fin.cons a x) - f (Fin.cons a y)| := by
          apply Finset.sum_congr rfl
          intro a _
          rw [← mul_sub, abs_mul, abs_of_nonneg (hw0 0 a)]
    _ ≤ ∑ a, w 0 a * c i.succ := by
          apply Finset.sum_le_sum
          intro a _
          apply mul_le_mul_of_nonneg_left _ (hw0 0 a)
          apply hbd i.succ
          intro j hj
          cases j using Fin.cases with
          | zero => rfl
          | succ j =>
              exact hxy j (fun h ↦ hj (congrArg (fun k : Fin n ↦ k.succ) h))
    _ = c i.succ := by rw [← Finset.sum_mul, hw1]; simp

/-- Weighted mass of an event in the finite product space. -/
def eventMass {α : Type*} [Fintype α] {n : ℕ}
    (w : Fin n → α → ℝ) (E : Set (Fin n → α)) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ E), productMass w x

/-- Bernoulli coordinate weights, with `true` having probability `p i`. -/
def bernoulliWeight {n : ℕ} (p : Fin n → ℝ) (i : Fin n) (b : Bool) : ℝ :=
  if b then p i else 1 - p i

lemma bernoulliWeight_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ i b, 0 ≤ bernoulliWeight p i b := by
  intro i b
  cases b <;> simp [bernoulliWeight, (hp i).1, (hp i).2]

lemma bernoulliWeight_sum_one {n : ℕ} (p : Fin n → ℝ) :
    ∀ i, ∑ b : Bool, bernoulliWeight p i b = 1 := by
  intro i
  rw [Fintype.sum_bool]
  simp [bernoulliWeight]

/-- The constant-bias Bernoulli coordinate weights. -/
def weight {n : ℕ} (q : ℝ) : Fin n → Bool → ℝ :=
  bernoulliWeight (fun _ ↦ q)

@[simp] lemma weight_false {n : ℕ} (q : ℝ) (i : Fin n) :
    weight q i false = 1 - q := by
  simp [weight, bernoulliWeight]

@[simp] lemma weight_true {n : ℕ} (q : ℝ) (i : Fin n) :
    weight q i true = q := by
  simp [weight, bernoulliWeight]

lemma weight_nonneg {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ i b, 0 ≤ weight (n := n) q i b := by
  exact bernoulliWeight_nonneg (fun _ : Fin n ↦ q) (fun _ ↦ ⟨hq0, hq1⟩)

lemma weight_sum_one {n : ℕ} (q : ℝ) :
    ∀ i, ∑ b : Bool, weight (n := n) q i b = 1 := by
  exact bernoulliWeight_sum_one (fun _ : Fin n ↦ q)

/-! ## Process-facing stopped-martingale interface -/

/-- Freedman's denominator-form inequality specialized only as far as the
underlying constant-bias Bernoulli product law.

Unlike `upperTail` below, this theorem deliberately makes no deterministic
coordinate-oscillation assumption.  A random-greedy application may stop its
increments when a guard fails, prove the conditional second-moment estimates
in `hmom` using outcome-dependent influences, and provide the resulting
predictable budget `hV` and guarded cap `hR` directly. -/
theorem upperTail_of_conditionalMoments {m steps : ℕ} {ι : Type*}
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {info : ℕ → (Fin m → Bool) → ι}
    (hfil : Erdos136.Freedman.IsFiltration info)
    {d : ℕ → (Fin m → Bool) → ℝ}
    (hadapted : ∀ k, Erdos136.Freedman.KnownAt info (k + 1) (d k))
    {v : ℕ → ℝ}
    (hmom : Erdos136.Freedman.ConditionalMomentBounds
      (productMass (weight q)) info d v)
    {R t V : ℝ} (hR0 : 0 ≤ R) (ht : 0 ≤ t) (hV0 : 0 ≤ V)
    (hden : 0 < V + R * t)
    (hR : ∀ k x, |d k x| ≤ R)
    (hV : ∑ k ∈ Finset.range steps, v k ≤ V) :
    Erdos136.Freedman.eventMass (productMass (weight q))
        (Finset.univ.filter
          (fun x ↦ t ≤ Erdos136.Freedman.partialSum d steps x)) ≤
      Real.exp (-(t ^ 2) / (4 * (V + R * t))) := by
  classical
  apply Erdos136.Freedman.freedman
    (p := productMass (weight q))
    (fun x ↦ productMass_nonneg (weight q) (weight_nonneg hq0 hq1) x)
    (sum_productMass_eq_one (weight q) (weight_sum_one q))
    hfil hadapted hmom hR0 ht hV0 hden hR hV

/-- If a finite Bernoulli-product bad event has mass strictly below one, at
least one concrete outcome avoids it.  This is the extraction step paired with
`upperTail_of_conditionalMoments`. -/
lemma exists_lt_of_eventMass_lt_one {m : ℕ} (q : ℝ)
    (X : (Fin m → Bool) → ℝ) (t : ℝ)
    (hbad : Erdos136.Freedman.eventMass (productMass (weight q))
      (Finset.univ.filter (fun x ↦ t ≤ X x)) < 1) :
    ∃ x, X x < t := by
  classical
  by_contra hnone
  have hall : ∀ x, t ≤ X x := by
    intro x
    exact le_of_not_gt (fun hx ↦ hnone ⟨x, hx⟩)
  have hfilter : Finset.univ.filter (fun x : Fin m → Bool ↦ t ≤ X x) =
      Finset.univ := by
    ext x
    simp [hall x]
  have hone : Erdos136.Freedman.eventMass (productMass (weight q))
      (Finset.univ.filter (fun x ↦ t ≤ X x)) = 1 := by
    rw [hfilter]
    simp [Erdos136.Freedman.eventMass,
      sum_productMass_eq_one (weight q) (weight_sum_one q)]
  linarith

/-- The exact conditional variance budget is no larger than the commonly used
sparse bound `q * ∑ i, c i ^ 2`. -/
lemma biasVarianceBudget_le {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q)
    (c : Fin n → ℝ) :
    q * (1 - q) * ∑ i, c i ^ 2 ≤ q * ∑ i, c i ^ 2 := by
  have hsum : 0 ≤ ∑ i, c i ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg (c i)
  nlinarith [mul_nonneg hq0 hsum]

private lemma centered_false (q a₀ a₁ : ℝ) :
    a₀ - ((1 - q) * a₀ + q * a₁) = -q * (a₁ - a₀) := by
  ring

private lemma centered_true (q a₀ a₁ : ℝ) :
    a₁ - ((1 - q) * a₀ + q * a₁) = (1 - q) * (a₁ - a₀) := by
  ring

/-- The conditional exponential estimate for one biased Boolean coordinate.
It is the two-point specialization of the exponential step in Freedman's
inequality. -/
lemma bernoulli_centered_exp_le (q a₀ a₁ c lam : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 ≤ c)
    (hosc : |a₁ - a₀| ≤ c) (hlam : 0 ≤ lam) (hlamc : lam * c ≤ 1) :
    (1 - q) * Real.exp (lam * (a₀ - ((1 - q) * a₀ + q * a₁))) +
        q * Real.exp (lam * (a₁ - ((1 - q) * a₀ + q * a₁))) ≤
      Real.exp (lam ^ 2 * (q * (1 - q) * c ^ 2)) := by
  let delta : ℝ := a₁ - a₀
  let m : ℝ := (1 - q) * a₀ + q * a₁
  have hqbar : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hdelta : |delta| ≤ c := by simpa [delta] using hosc
  have hfalse_abs : |lam * (a₀ - m)| ≤ 1 := by
    rw [show a₀ - m = -q * delta by simp [m, delta, centered_false]]
    calc
      |lam * (-q * delta)| = lam * q * |delta| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hlam, abs_of_nonneg hq0]
        ring
      _ ≤ lam * q * c := mul_le_mul_of_nonneg_left hdelta (mul_nonneg hlam hq0)
      _ ≤ lam * c := by
        calc
          lam * q * c = (lam * c) * q := by ring
          _ ≤ (lam * c) * 1 :=
            mul_le_mul_of_nonneg_left hq1 (mul_nonneg hlam hc)
          _ = lam * c := by ring
      _ ≤ 1 := hlamc
  have htrue_abs : |lam * (a₁ - m)| ≤ 1 := by
    rw [show a₁ - m = (1 - q) * delta by simp [m, delta, centered_true]]
    calc
      |lam * ((1 - q) * delta)| = lam * (1 - q) * |delta| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hlam, abs_of_nonneg hqbar]
        ring
      _ ≤ lam * (1 - q) * c :=
        mul_le_mul_of_nonneg_left hdelta (mul_nonneg hlam hqbar)
      _ ≤ lam * c := by
        calc
          lam * (1 - q) * c = (lam * c) * (1 - q) := by ring
          _ ≤ (lam * c) * 1 :=
            mul_le_mul_of_nonneg_left (by linarith : 1 - q ≤ 1) (mul_nonneg hlam hc)
          _ = lam * c := by ring
      _ ≤ 1 := hlamc
  have hfalse := Erdos136.Freedman.exp_mul_le lam (a₀ - m) hfalse_abs
  have htrue := Erdos136.Freedman.exp_mul_le lam (a₁ - m) htrue_abs
  have hweighted :
      (1 - q) * Real.exp (lam * (a₀ - m)) + q * Real.exp (lam * (a₁ - m)) ≤
        1 + lam ^ 2 * (q * (1 - q) * delta ^ 2) := by
    calc
      (1 - q) * Real.exp (lam * (a₀ - m)) + q * Real.exp (lam * (a₁ - m))
          ≤ (1 - q) * (1 + lam * (a₀ - m) + lam ^ 2 * (a₀ - m) ^ 2) +
              q * (1 + lam * (a₁ - m) + lam ^ 2 * (a₁ - m) ^ 2) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hfalse hqbar)
              (mul_le_mul_of_nonneg_left htrue hq0)
      _ = 1 + lam ^ 2 * (q * (1 - q) * delta ^ 2) := by
            simp only [m, delta]
            ring
  have hsquare : delta ^ 2 ≤ c ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hc] using hdelta
  calc
    (1 - q) * Real.exp (lam * (a₀ - ((1 - q) * a₀ + q * a₁))) +
          q * Real.exp (lam * (a₁ - ((1 - q) * a₀ + q * a₁)))
        ≤ 1 + lam ^ 2 * (q * (1 - q) * delta ^ 2) := by simpa [m] using hweighted
    _ ≤ 1 + lam ^ 2 * (q * (1 - q) * c ^ 2) := by
      gcongr
    _ ≤ Real.exp (lam ^ 2 * (q * (1 - q) * c ^ 2)) := by
      simpa [add_comm] using Real.add_one_le_exp (lam ^ 2 * (q * (1 - q) * c ^ 2))

/-- Exponential moment bound for the finite Doob martingale of a function on a
constant-bias Boolean product space. -/
theorem expMomentBound (n : ℕ) (q : ℝ) (f : (Fin n → Bool) → ℝ)
    (c : Fin n → ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hc : ∀ i, 0 ≤ c i)
    (hbd : ∀ i (x y : Fin n → Bool),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlamc : ∀ i, lam * c i ≤ 1) :
    ∑ x, productMass (weight q) x *
        Real.exp (lam * (f x - weightedMean (weight q) f)) ≤
      Real.exp (lam ^ 2 * (q * (1 - q) * ∑ i, c i ^ 2)) := by
  induction n with
  | zero => simp [productMass, weightedMean]
  | succ n ih =>
      let w : Fin (n + 1) → Bool → ℝ := weight q
      let wt : Fin n → Bool → ℝ := fun i b ↦ w i.succ b
      let g : (Fin n → Bool) → ℝ := sectionAverage w f
      let mu : ℝ := weightedMean w f
      have hwt : wt = weight q := by
        funext i b
        simp [wt, w, weight, bernoulliWeight]
      have hmean : weightedMean wt g = mu := by
        exact (weightedMean_succ w f).symm
      have hgdiff : ∀ i (x y : Fin n → Bool),
          (∀ j, j ≠ i → x j = y j) → |g x - g y| ≤ c i.succ := by
        exact sectionAverage_boundedDiff w f c
          (weight_nonneg hq0 hq1) (weight_sum_one q) hbd
      have hi := ih g (fun i ↦ c i.succ) (fun i ↦ hc i.succ)
        hgdiff (fun i ↦ hlamc i.succ)
      rw [← hwt, hmean] at hi
      have hsection (y : Fin n → Bool) :
          ∑ a : Bool, w 0 a * Real.exp (lam * (f (Fin.cons a y) - mu)) ≤
            Real.exp (lam ^ 2 * (q * (1 - q) * c 0 ^ 2)) *
              Real.exp (lam * (g y - mu)) := by
        let a₀ : ℝ := f (Fin.cons false y)
        let a₁ : ℝ := f (Fin.cons true y)
        have hosc : |a₁ - a₀| ≤ c 0 := by
          apply hbd 0
          intro j hj
          cases j using Fin.cases with
          | zero => exact (hj rfl).elim
          | succ j => rfl
        have hone := bernoulli_centered_exp_le q a₀ a₁ (c 0) lam
          hq0 hq1 (hc 0) hosc hlam (hlamc 0)
        have hg : g y = (1 - q) * a₀ + q * a₁ := by
          dsimp [g, sectionAverage]
          simp [w, weight, a₀, a₁, bernoulliWeight]
          ring
        have hfalsefactor :
            Real.exp (lam * (f (Fin.cons false y) - mu)) =
              Real.exp (lam * (g y - mu)) * Real.exp (lam * (a₀ - g y)) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [a₀]
          ring
        have htruefactor :
            Real.exp (lam * (f (Fin.cons true y) - mu)) =
              Real.exp (lam * (g y - mu)) * Real.exp (lam * (a₁ - g y)) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [a₁]
          ring
        have hfactor :
            ∑ a : Bool, w 0 a * Real.exp (lam * (f (Fin.cons a y) - mu)) =
              Real.exp (lam * (g y - mu)) *
                ((1 - q) * Real.exp (lam * (a₀ - g y)) +
                  q * Real.exp (lam * (a₁ - g y))) := by
          rw [Fintype.sum_bool]
          simp only [w, weight_false, weight_true]
          rw [hfalsefactor, htruefactor]
          ring
        rw [hfactor, hg]
        calc
          Real.exp (lam * (((1 - q) * a₀ + q * a₁) - mu)) *
                ((1 - q) * Real.exp
                    (lam * (a₀ - ((1 - q) * a₀ + q * a₁))) +
                  q * Real.exp
                    (lam * (a₁ - ((1 - q) * a₀ + q * a₁))))
              ≤ Real.exp (lam * (((1 - q) * a₀ + q * a₁) - mu)) *
                  Real.exp (lam ^ 2 * (q * (1 - q) * c 0 ^ 2)) := by
                    gcongr
          _ = Real.exp (lam ^ 2 * (q * (1 - q) * c 0 ^ 2)) *
                Real.exp (lam * (((1 - q) * a₀ + q * a₁) - mu)) := by ring
      simp only [sum_fin_succ_eq, productMass_cons]
      calc
        ∑ a : Bool, ∑ y : Fin n → Bool,
              w 0 a * productMass wt y * Real.exp (lam * (f (Fin.cons a y) - mu))
            = ∑ y : Fin n → Bool, productMass wt y *
                (∑ a : Bool, w 0 a * Real.exp (lam * (f (Fin.cons a y) - mu))) := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro y _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro a _
                  ring
        _ ≤ ∑ y : Fin n → Bool, productMass wt y *
              (Real.exp (lam ^ 2 * (q * (1 - q) * c 0 ^ 2)) *
                Real.exp (lam * (g y - mu))) := by
                apply Finset.sum_le_sum
                intro y _
                exact mul_le_mul_of_nonneg_left (hsection y)
                  (productMass_nonneg wt (fun i b ↦ weight_nonneg hq0 hq1 i.succ b) y)
        _ = Real.exp (lam ^ 2 * (q * (1 - q) * c 0 ^ 2)) *
              ∑ y : Fin n → Bool, productMass wt y * Real.exp (lam * (g y - mu)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                ring
        _ ≤ Real.exp (lam ^ 2 * (q * (1 - q) * c 0 ^ 2)) *
              Real.exp (lam ^ 2 * (q * (1 - q) * ∑ i : Fin n, c i.succ ^ 2)) :=
                mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)
        _ = Real.exp (lam ^ 2 * (q * (1 - q) * ∑ i : Fin (n + 1), c i ^ 2)) := by
              rw [← Real.exp_add, Fin.sum_univ_succ]
              congr 1
              ring

/-- Upper-tail biased bounded-differences inequality in Bernstein/Freedman
denominator form.  The predictable variance budget is exactly
`q * (1-q) * ∑ i, c i ^ 2`. -/
theorem upperTail (n : ℕ) (q : ℝ) (f : (Fin n → Bool) → ℝ)
    (c : Fin n → ℝ) (R t : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : ∀ i, 0 ≤ c i)
    (hbd : ∀ i (x y : Fin n → Bool),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (hR0 : 0 ≤ R) (hcR : ∀ i, c i ≤ R) (ht : 0 ≤ t)
    (hden : 0 < q * (1 - q) * ∑ i, c i ^ 2 + R * t) :
    eventMass (weight q) {x | weightedMean (weight q) f + t ≤ f x} ≤
      Real.exp (-(t ^ 2) /
        (4 * (q * (1 - q) * ∑ i, c i ^ 2 + R * t))) := by
  let V : ℝ := q * (1 - q) * ∑ i, c i ^ 2
  let lam : ℝ := t / (2 * (V + R * t))
  have hdenV : 0 < V + R * t := by simpa [V] using hden
  have hlam : 0 ≤ lam := div_nonneg ht (mul_nonneg (by norm_num) hdenV.le)
  have hlamR : lam * R ≤ 1 := by
    dsimp [lam]
    rw [div_mul_eq_mul_div, div_le_one (mul_pos (by norm_num) hdenV)]
    have hV0 : 0 ≤ V := by
      exact mul_nonneg (mul_nonneg hq0 (sub_nonneg.mpr hq1))
        (Finset.sum_nonneg fun i _ ↦ sq_nonneg (c i))
    nlinarith [mul_nonneg hR0 ht]
  have hlamc : ∀ i, lam * c i ≤ 1 := by
    intro i
    exact (mul_le_mul_of_nonneg_left (hcR i) hlam).trans hlamR
  have hmom := expMomentBound n q f c hq0 hq1 hc hbd lam hlam hlamc
  have hpoint : ∀ x ∈ Finset.univ.filter
      (fun x : Fin n → Bool ↦ x ∈ {x | weightedMean (weight q) f + t ≤ f x}),
      productMass (weight q) x * Real.exp (lam * t) ≤
        productMass (weight q) x *
          Real.exp (lam * (f x - weightedMean (weight q) f)) := by
    intro x hx
    apply mul_le_mul_of_nonneg_left _
      (productMass_nonneg (weight q) (weight_nonneg hq0 hq1) x)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hlam
    have hevent := (Finset.mem_filter.mp hx).2
    change weightedMean (weight q) f + t ≤ f x at hevent
    linarith
  have hmarkov :
      eventMass (weight q) {x | weightedMean (weight q) f + t ≤ f x} *
          Real.exp (lam * t) ≤
        ∑ x, productMass (weight q) x *
          Real.exp (lam * (f x - weightedMean (weight q) f)) := by
    calc
      eventMass (weight q) {x | weightedMean (weight q) f + t ≤ f x} *
            Real.exp (lam * t)
          = ∑ x ∈ Finset.univ.filter
              (fun x : Fin n → Bool ↦ x ∈ {x | weightedMean (weight q) f + t ≤ f x}),
                productMass (weight q) x * Real.exp (lam * t) := by
                  simp only [eventMass, Finset.sum_mul]
      _ ≤ ∑ x ∈ Finset.univ.filter
              (fun x : Fin n → Bool ↦ x ∈ {x | weightedMean (weight q) f + t ≤ f x}),
                productMass (weight q) x *
                  Real.exp (lam * (f x - weightedMean (weight q) f)) :=
            Finset.sum_le_sum hpoint
      _ ≤ ∑ x, productMass (weight q) x *
              Real.exp (lam * (f x - weightedMean (weight q) f)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro x _ _
            exact mul_nonneg (productMass_nonneg (weight q) (weight_nonneg hq0 hq1) x)
              (Real.exp_nonneg _)
  have hdiv : eventMass (weight q) {x | weightedMean (weight q) f + t ≤ f x} ≤
      Real.exp (lam ^ 2 * V) / Real.exp (lam * t) := by
    rw [le_div_iff₀ (Real.exp_pos _)]
    exact hmarkov.trans (by simpa [V] using hmom)
  calc
    eventMass (weight q) {x | weightedMean (weight q) f + t ≤ f x}
        ≤ Real.exp (lam ^ 2 * V) / Real.exp (lam * t) := hdiv
    _ = Real.exp (lam ^ 2 * V - lam * t) := by rw [Real.exp_sub]
    _ ≤ Real.exp (-(t ^ 2) / (4 * (V + R * t))) := by
      rw [Real.exp_le_exp]
      dsimp [lam]
      have hV0 : 0 ≤ V := by
        exact mul_nonneg (mul_nonneg hq0 (sub_nonneg.mpr hq1))
          (Finset.sum_nonneg fun i _ ↦ sq_nonneg (c i))
      have hne : V + R * t ≠ 0 := ne_of_gt hdenV
      have hne' : V + t * R ≠ 0 := by nlinarith
      field_simp [hne, hne']
      nlinarith [mul_nonneg hR0 ht]
    _ = Real.exp (-(t ^ 2) /
          (4 * (q * (1 - q) * ∑ i, c i ^ 2 + R * t))) := by rfl

end

#print axioms upperTail_of_conditionalMoments
#print axioms upperTail

end Erdos136.BernoulliFreedman
