/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteRealExpectation

/-!
# Exponential concentration for finite Markov kernels

This file proves the finite-kernel exponential-moment argument needed for
stopped trajectory variables.  It supports time-inhomogeneous kernels and
uses the elementary inequality `exp x ≤ 1 + x + x²` for `x ≤ 1`.
Consequently, conditional nonpositive drift, an upper jump bound, and a
conditional second-moment budget give a Bernstein/Freedman-style terminal
tail bound.  Catastrophic negative jumps therefore do not constrain the
exponential parameter.
-/

namespace Erdos207

open scoped BigOperators NNReal

noncomputable section

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- Apply the first `n` kernels of a time-inhomogeneous finite Markov chain. -/
def evolveKernels (K : ℕ → Ω → FiniteLaw Ω) :
    ℕ → FiniteLaw Ω → FiniteLaw Ω
  | 0, L => L
  | n + 1, L => bind (evolveKernels K n L) (K n)

@[simp]
theorem evolveKernels_zero (K : ℕ → Ω → FiniteLaw Ω)
    (L : FiniteLaw Ω) : evolveKernels K 0 L = L := rfl

@[simp]
theorem evolveKernels_succ (K : ℕ → Ω → FiniteLaw Ω)
    (n : ℕ) (L : FiniteLaw Ω) :
    evolveKernels K (n + 1) L =
      bind (evolveKernels K n L) (K n) := rfl

/-- A state invariant preserved by every time-indexed kernel is preserved by
the evolved law. -/
theorem SupportedOn.evolveKernels
    {P : Ω → Prop} {L : FiniteLaw Ω}
    (hL : L.SupportedOn P) (K : ℕ → Ω → FiniteLaw Ω)
    (hK : ∀ i x, P x → (K i x).SupportedOn P) (n : ℕ) :
    (evolveKernels K n L).SupportedOn P := by
  induction n with
  | zero => exact hL
  | succ n ih =>
      exact ih.bind (K n) fun x hx ↦ hK n x hx

/-- Iteration of conditional exponential-moment bounds. -/
theorem expectationReal_exp_evolveKernels_le
    {P : Ω → Prop} {L : FiniteLaw Ω}
    (K : ℕ → Ω → FiniteLaw Ω) (f : ℕ → Ω → ℝ)
    (theta : ℝ) (c : ℕ → ℝ) (n : ℕ)
    (hL : L.SupportedOn P)
    (hK : ∀ i x, P x → (K i x).SupportedOn P)
    (hmgf : ∀ i, i < n → ∀ x, P x →
      (K i x).expectationReal (fun y ↦
        Real.exp (theta * (f (i + 1) y - f i x))) ≤ Real.exp (c i)) :
    (evolveKernels K n L).expectationReal
        (fun x ↦ Real.exp (theta * f n x)) ≤
      L.expectationReal (fun x ↦ Real.exp (theta * f 0 x)) *
        ∏ i ∈ Finset.range n, Real.exp (c i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev : (evolveKernels K n L).SupportedOn P :=
        hL.evolveKernels K hK n
      rw [evolveKernels_succ, expectationReal_bind]
      calc
        (evolveKernels K n L).expectationReal (fun x ↦
            (K n x).expectationReal (fun y ↦
              Real.exp (theta * f (n + 1) y))) ≤
            (evolveKernels K n L).expectationReal (fun x ↦
              Real.exp (theta * f n x) * Real.exp (c n)) := by
          apply expectationReal_mono_of_supported _ hprev
          intro x hx
          calc
            (K n x).expectationReal (fun y ↦
                Real.exp (theta * f (n + 1) y)) =
                (K n x).expectationReal (fun y ↦
                  Real.exp (theta * f n x) *
                    Real.exp (theta * (f (n + 1) y - f n x))) := by
              congr 1
              funext y
              rw [← Real.exp_add]
              congr 1
              ring
            _ = Real.exp (theta * f n x) *
                (K n x).expectationReal (fun y ↦
                  Real.exp (theta * (f (n + 1) y - f n x))) :=
              expectationReal_const_mul _ _ _
            _ ≤ Real.exp (theta * f n x) * Real.exp (c n) := by
              exact mul_le_mul_of_nonneg_left
                (hmgf n (Nat.lt_succ_self n) x hx) (Real.exp_pos _).le
        _ = (evolveKernels K n L).expectationReal
              (fun x ↦ Real.exp (theta * f n x)) * Real.exp (c n) :=
          expectationReal_mul_const _ _ _
        _ ≤ (L.expectationReal (fun x ↦ Real.exp (theta * f 0 x)) *
              ∏ i ∈ Finset.range n, Real.exp (c i)) * Real.exp (c n) := by
          apply mul_le_mul_of_nonneg_right
          · exact ih (fun i hi ↦ hmgf i (hi.trans (Nat.lt_succ_self n)))
          · exact (Real.exp_pos _).le
        _ = L.expectationReal (fun x ↦ Real.exp (theta * f 0 x)) *
              ∏ i ∈ Finset.range (n + 1), Real.exp (c i) := by
          rw [Finset.prod_range_succ]
          ring

/-- A quadratic upper bound for the exponential needs only an upper bound on
the argument.  Large negative jumps are harmless for an upper-tail estimate. -/
theorem exp_le_one_add_self_add_sq_of_le_one {x : ℝ}
    (hx : x ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  by_cases hneg : x < -1
  · have hexp : Real.exp x ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have hone : 1 ≤ 1 + x + x ^ 2 := by nlinarith
    exact hexp.trans hone
  · have habs : |x| ≤ 1 := (abs_le).2 ⟨by linarith, hx⟩
    have hrem := Real.abs_exp_sub_one_sub_id_le habs
    have hupper : Real.exp x - 1 - x ≤ |Real.exp x - 1 - x| :=
      le_abs_self _
    linarith

/-- Conditional nonpositive drift plus a second-moment budget gives a
one-step exponential-moment bound. -/
theorem expectationReal_exp_increment_le
    (L : FiniteLaw Ω) {P : Ω → Prop} (hP : L.SupportedOn P)
    (Δ : Ω → ℝ) (theta R v : ℝ)
    (htheta : 0 ≤ theta) (hR : 0 ≤ R) (hthetaR : theta * R ≤ 1)
    (hjump : ∀ ω, P ω → Δ ω ≤ R)
    (hdrift : L.expectationReal Δ ≤ 0)
    (hsecond : L.expectationReal (fun ω ↦ (Δ ω) ^ 2) ≤ v) :
    L.expectationReal (fun ω ↦ Real.exp (theta * Δ ω)) ≤
      Real.exp (theta ^ 2 * v) := by
  have hpoint : ∀ ω, P ω →
      Real.exp (theta * Δ ω) ≤
        1 + theta * Δ ω + (theta * Δ ω) ^ 2 := by
    intro ω hω
    apply exp_le_one_add_self_add_sq_of_le_one
    exact (mul_le_mul_of_nonneg_left (hjump ω hω) htheta).trans hthetaR
  calc
    L.expectationReal (fun ω ↦ Real.exp (theta * Δ ω)) ≤
        L.expectationReal (fun ω ↦
          1 + theta * Δ ω + (theta * Δ ω) ^ 2) :=
      L.expectationReal_mono_of_supported hP hpoint
    _ = 1 + theta * L.expectationReal Δ +
        theta ^ 2 * L.expectationReal (fun ω ↦ (Δ ω) ^ 2) := by
      rw [expectationReal_add, expectationReal_add,
        expectationReal_const, expectationReal_const_mul]
      have hsquare : L.expectationReal (fun ω ↦ (theta * Δ ω) ^ 2) =
          theta ^ 2 * L.expectationReal (fun ω ↦ (Δ ω) ^ 2) := by
        rw [← expectationReal_const_mul]
        congr 1
        funext ω
        ring
      rw [hsquare]
    _ ≤ 1 + theta ^ 2 * v := by
      have hthetasq : 0 ≤ theta ^ 2 := sq_nonneg theta
      have hfirst : theta * L.expectationReal Δ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos htheta hdrift
      have hsecond' := mul_le_mul_of_nonneg_left hsecond hthetasq
      linarith
    _ ≤ Real.exp (theta ^ 2 * v) := by
      simpa [add_comm] using Real.add_one_le_exp (theta ^ 2 * v)

/-- Survival-weighted one-step exponential bound.  Outcomes outside `alive`
contribute zero, so only jumps of surviving outcomes need an upper bound. -/
theorem expectationReal_alive_exp_increment_le
    (L : FiniteLaw Ω) (alive : Ω → Prop) [DecidablePred alive]
    (Δ : Ω → ℝ) (theta R v : ℝ)
    (htheta : 0 ≤ theta) (hthetaR : theta * R ≤ 1)
    (hjump : ∀ ω, 0 < L.mass ω → alive ω → Δ ω ≤ R)
    (hdrift : L.expectationReal
      (fun ω ↦ if alive ω then Δ ω else 0) ≤ 0)
    (hsecond : L.expectationReal
      (fun ω ↦ if alive ω then (Δ ω) ^ 2 else 0) ≤ v) :
    L.expectationReal
        (fun ω ↦ if alive ω then Real.exp (theta * Δ ω) else 0) ≤
      Real.exp (theta ^ 2 * v) := by
  classical
  have hpoint : ∀ ω, 0 < L.mass ω →
      (if alive ω then Real.exp (theta * Δ ω) else 0) ≤
        (if alive ω then
          1 + theta * Δ ω + (theta * Δ ω) ^ 2 else 0) := by
    intro ω hmass
    by_cases hω : alive ω
    · simp only [hω, if_true]
      apply exp_le_one_add_self_add_sq_of_le_one
      exact (mul_le_mul_of_nonneg_left (hjump ω hmass hω) htheta).trans
        hthetaR
    · simp [hω]
  have hrewrite :
      (fun ω ↦ if alive ω then
          1 + theta * Δ ω + (theta * Δ ω) ^ 2 else 0) =
        (fun ω ↦
          (if alive ω then 1 else 0) +
          theta * (if alive ω then Δ ω else 0) +
          theta ^ 2 * (if alive ω then (Δ ω) ^ 2 else 0)) := by
    funext ω
    by_cases hω : alive ω <;> simp [hω] <;> ring
  have hprob : ((L.probability alive : ℝ)) ≤ 1 := by
    exact_mod_cast L.probability_le_one alive
  calc
    L.expectationReal
        (fun ω ↦ if alive ω then Real.exp (theta * Δ ω) else 0) ≤
        L.expectationReal (fun ω ↦ if alive ω then
          1 + theta * Δ ω + (theta * Δ ω) ^ 2 else 0) :=
      L.expectationReal_mono_of_supported
        (fun ω hω ↦ hω) hpoint
    _ = (L.probability alive : ℝ) +
          theta * L.expectationReal
            (fun ω ↦ if alive ω then Δ ω else 0) +
          theta ^ 2 * L.expectationReal
            (fun ω ↦ if alive ω then (Δ ω) ^ 2 else 0) := by
      rw [hrewrite, expectationReal_add, expectationReal_add,
        expectationReal_const_mul, expectationReal_const_mul,
        expectationReal_indicator]
    _ ≤ 1 + theta ^ 2 * v := by
      have hfirst : theta * L.expectationReal
          (fun ω ↦ if alive ω then Δ ω else 0) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos htheta hdrift
      have hsquare := mul_le_mul_of_nonneg_left hsecond (sq_nonneg theta)
      linarith
    _ ≤ Real.exp (theta ^ 2 * v) := by
      simpa [add_comm] using Real.add_one_le_exp (theta ^ 2 * v)

/-- Iteration of survival-weighted conditional exponential bounds.  A dead
state must remain dead, but no quantitative hypotheses are imposed there. -/
theorem expectationReal_alive_exp_evolveKernels_le
    (alive : Ω → Prop) [DecidablePred alive]
    {P : Ω → Prop} {L : FiniteLaw Ω}
    (K : ℕ → Ω → FiniteLaw Ω) (f : ℕ → Ω → ℝ)
    (theta : ℝ) (c : ℕ → ℝ) (n : ℕ)
    (hL : L.SupportedOn P)
    (hK : ∀ i x, P x → (K i x).SupportedOn P)
    (hdead : ∀ i x, P x → ¬ alive x →
      (K i x).SupportedOn (fun y ↦ ¬ alive y))
    (hmgf : ∀ i, i < n → ∀ x, P x → alive x →
      (K i x).expectationReal (fun y ↦
        if alive y then Real.exp (theta * (f (i + 1) y - f i x)) else 0) ≤
          Real.exp (c i)) :
    (evolveKernels K n L).expectationReal
        (fun x ↦ if alive x then Real.exp (theta * f n x) else 0) ≤
      L.expectationReal
          (fun x ↦ if alive x then Real.exp (theta * f 0 x) else 0) *
        ∏ i ∈ Finset.range n, Real.exp (c i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev : (evolveKernels K n L).SupportedOn P :=
        hL.evolveKernels K hK n
      rw [evolveKernels_succ, expectationReal_bind]
      calc
        (evolveKernels K n L).expectationReal (fun x ↦
            (K n x).expectationReal (fun y ↦
              if alive y then Real.exp (theta * f (n + 1) y) else 0)) ≤
          (evolveKernels K n L).expectationReal (fun x ↦
            (if alive x then Real.exp (theta * f n x) else 0) *
              Real.exp (c n)) := by
          apply expectationReal_mono_of_supported _ hprev
          intro x hx
          by_cases halive : alive x
          · calc
              (K n x).expectationReal (fun y ↦
                  if alive y then Real.exp (theta * f (n + 1) y) else 0) =
                Real.exp (theta * f n x) *
                  (K n x).expectationReal (fun y ↦ if alive y then
                    Real.exp (theta * (f (n + 1) y - f n x)) else 0) := by
                      rw [← expectationReal_const_mul]
                      congr 1
                      funext y
                      by_cases hy : alive y
                      · simp only [hy, if_true, ← Real.exp_add]
                        congr 1
                        ring
                      · simp [hy]
              _ ≤ Real.exp (theta * f n x) * Real.exp (c n) := by
                exact mul_le_mul_of_nonneg_left
                  (hmgf n (Nat.lt_succ_self n) x hx halive)
                  (Real.exp_pos _).le
              _ = (if alive x then Real.exp (theta * f n x) else 0) *
                    Real.exp (c n) := by simp [halive]
          · have hzero : (K n x).expectationReal (fun y ↦
                if alive y then Real.exp (theta * f (n + 1) y) else 0) = 0 := by
                rw [← expectationReal_zero (K n x)]
                apply expectationReal_congr_of_supported (K n x)
                  (hdead n x hx halive)
                intro y hy
                simp [hy]
            simp [halive, hzero]
        _ = (evolveKernels K n L).expectationReal
              (fun x ↦ if alive x then Real.exp (theta * f n x) else 0) *
                Real.exp (c n) := expectationReal_mul_const _ _ _
        _ ≤ (L.expectationReal
              (fun x ↦ if alive x then Real.exp (theta * f 0 x) else 0) *
              ∏ i ∈ Finset.range n, Real.exp (c i)) * Real.exp (c n) := by
          apply mul_le_mul_of_nonneg_right
          · exact ih (fun i hi ↦ hmgf i (hi.trans (Nat.lt_succ_self n)))
          · exact (Real.exp_pos _).le
        _ = L.expectationReal
              (fun x ↦ if alive x then Real.exp (theta * f 0 x) else 0) *
              ∏ i ∈ Finset.range (n + 1), Real.exp (c i) := by
          rw [Finset.prod_range_succ]
          ring

/-- Terminal upper-tail bound for a finite inhomogeneous process.  The
per-step assumptions are imposed only on the positive-mass invariant
support, so stopped kernels can be used directly. -/
theorem probability_evolveKernels_deviation_ge_le_exp
    {P : Ω → Prop} [DecidableEq Ω] [DecidablePred P]
    (K : ℕ → Ω → FiniteLaw Ω) (f : ℕ → Ω → ℝ)
    (x₀ : Ω) (theta R a : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hP₀ : P x₀) (htheta : 0 < theta) (hR : 0 ≤ R)
    (hthetaR : theta * R ≤ 1)
    (hK : ∀ i x, P x → (K i x).SupportedOn P)
    (hjump : ∀ i, i < n → ∀ x, P x → ∀ y,
      0 < (K i x).mass y → f (i + 1) y - f i x ≤ R)
    (hdrift : ∀ i, i < n → ∀ x, P x →
      (K i x).expectationReal
        (fun y ↦ f (i + 1) y - f i x) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ x, P x →
      (K i x).expectationReal
        (fun y ↦ (f (i + 1) y - f i x) ^ 2) ≤ v i) :
    ((evolveKernels K n (pure x₀)).probability
        (fun x ↦ a ≤ f n x - f 0 x₀) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * ∑ i ∈ Finset.range n, v i) := by
  let L := evolveKernels K n (pure x₀)
  let Y : Ω → ℝ := fun x ↦ Real.exp (theta * (f n x - f 0 x₀))
  have hmgfStep : ∀ i, i < n → ∀ x, P x →
      (K i x).expectationReal (fun y ↦
        Real.exp (theta * (f (i + 1) y - f i x))) ≤
        Real.exp (theta ^ 2 * v i) := by
    intro i hi x hx
    apply expectationReal_exp_increment_le (K i x)
      (P := fun y ↦ 0 < (K i x).mass y) (fun _ hy ↦ hy)
      (fun y ↦ f (i + 1) y - f i x) theta R (v i)
      htheta.le hR hthetaR
    · intro y hy
      exact hjump i hi x hx y hy
    · exact hdrift i hi x hx
    · exact hsecond i hi x hx
  have hmgf : L.expectationReal Y ≤
      Real.exp (theta ^ 2 * ∑ i ∈ Finset.range n, v i) := by
    have hiter := expectationReal_exp_evolveKernels_le
      K (fun i x ↦ f i x - f 0 x₀) theta
        (fun i ↦ theta ^ 2 * v i) n
      (supportedOn_pure P hP₀) hK (by
        intro i hi x hx
        have hfun :
            (fun y ↦ Real.exp (theta *
              ((f (i + 1) y - f 0 x₀) - (f i x - f 0 x₀)))) =
            (fun y ↦ Real.exp (theta * (f (i + 1) y - f i x))) := by
          funext y
          congr 1
          ring
        rw [hfun]
        exact hmgfStep i hi x hx)
    have hprod : ∏ i ∈ Finset.range n, Real.exp (theta ^ 2 * v i) =
        Real.exp (theta ^ 2 * ∑ i ∈ Finset.range n, v i) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
    simpa [L, Y, hprod] using hiter
  have hmarkov := probability_coe_le_expectationReal_div
    L Y (Real.exp (theta * a)) (Real.exp_pos _)
      (fun _ ↦ (Real.exp_pos _).le)
  have hevent : (fun x ↦ Real.exp (theta * a) ≤ Y x) =
      (fun x ↦ a ≤ f n x - f 0 x₀) := by
    funext x
    apply propext
    simp only [Y, Real.exp_le_exp]
    constructor <;> intro h <;> nlinarith [htheta]
  rw [hevent] at hmarkov
  refine hmarkov.trans (div_le_div_of_nonneg_right hmgf (Real.exp_pos _).le) |>.trans ?_
  rw [← Real.exp_sub]
  have hexponent :
      theta ^ 2 * ∑ i ∈ Finset.range n, v i - theta * a =
        -theta * a + theta ^ 2 * ∑ i ∈ Finset.range n, v i := by ring
  rw [hexponent]

/-- Terminal upper-tail bound restricted to states that remain in a monotone
alive region.  Dead paths carry zero exponential weight. -/
theorem probability_evolveKernels_alive_deviation_ge_le_exp
    [DecidableEq Ω] (alive : Ω → Prop) [DecidablePred alive]
    {P : Ω → Prop} [DecidablePred P]
    (K : ℕ → Ω → FiniteLaw Ω) (f : ℕ → Ω → ℝ)
    (x₀ : Ω) (theta R a : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hP₀ : P x₀) (halive₀ : alive x₀)
    (htheta : 0 < theta) (hthetaR : theta * R ≤ 1)
    (hK : ∀ i x, P x → (K i x).SupportedOn P)
    (hdead : ∀ i x, P x → ¬ alive x →
      (K i x).SupportedOn (fun y ↦ ¬ alive y))
    (hjump : ∀ i, i < n → ∀ x, P x → alive x → ∀ y,
      0 < (K i x).mass y → alive y → f (i + 1) y - f i x ≤ R)
    (hdrift : ∀ i, i < n → ∀ x, P x → alive x →
      (K i x).expectationReal (fun y ↦
        if alive y then f (i + 1) y - f i x else 0) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ x, P x → alive x →
      (K i x).expectationReal (fun y ↦
        if alive y then (f (i + 1) y - f i x) ^ 2 else 0) ≤ v i) :
    ((evolveKernels K n (pure x₀)).probability
      (fun x ↦ alive x ∧ a ≤ f n x - f 0 x₀) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * ∑ i ∈ Finset.range n, v i) := by
  classical
  let L := evolveKernels K n (pure x₀)
  let Y : Ω → ℝ := fun x ↦
    if alive x then Real.exp (theta * (f n x - f 0 x₀)) else 0
  have hmgfStep : ∀ i, i < n → ∀ x, P x → alive x →
      (K i x).expectationReal (fun y ↦ if alive y then
        Real.exp (theta * (f (i + 1) y - f i x)) else 0) ≤
          Real.exp (theta ^ 2 * v i) := by
    intro i hi x hx halive
    exact expectationReal_alive_exp_increment_le (K i x) alive
      (fun y ↦ f (i + 1) y - f i x) theta R (v i) htheta.le hthetaR
      (fun y hy ↦ hjump i hi x hx halive y hy)
      (hdrift i hi x hx halive) (hsecond i hi x hx halive)
  have hmgf : L.expectationReal Y ≤
      Real.exp (theta ^ 2 * ∑ i ∈ Finset.range n, v i) := by
    have hiter := expectationReal_alive_exp_evolveKernels_le alive
      (P := P) K (fun i x ↦ f i x - f 0 x₀) theta
      (fun i ↦ theta ^ 2 * v i) n
      (supportedOn_pure P hP₀) hK hdead (by
        intro i hi x hx halive
        have hfun :
            (fun y ↦ if alive y then Real.exp (theta *
              ((f (i + 1) y - f 0 x₀) - (f i x - f 0 x₀))) else 0) =
            (fun y ↦ if alive y then Real.exp
              (theta * (f (i + 1) y - f i x)) else 0) := by
          funext y
          by_cases hy : alive y <;> simp [hy] <;> congr 1 <;> ring
        rw [hfun]
        exact hmgfStep i hi x hx halive)
    have hprod : ∏ i ∈ Finset.range n, Real.exp (theta ^ 2 * v i) =
        Real.exp (theta ^ 2 * ∑ i ∈ Finset.range n, v i) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
    simpa [L, Y, halive₀, hprod] using hiter
  have hmarkov := probability_coe_le_expectationReal_div
    L Y (Real.exp (theta * a)) (Real.exp_pos _) (fun x ↦ by
      by_cases hx : alive x <;> simp [Y, hx, (Real.exp_pos _).le])
  have hevent : (fun x ↦ Real.exp (theta * a) ≤ Y x) =
      (fun x ↦ alive x ∧ a ≤ f n x - f 0 x₀) := by
    funext x
    apply propext
    by_cases hx : alive x
    · simp only [Y, hx, if_true, true_and, Real.exp_le_exp]
      constructor <;> intro h <;> nlinarith [htheta]
    · simp [Y, hx, Real.exp_pos]
  rw [hevent] at hmarkov
  refine hmarkov.trans
    (div_le_div_of_nonneg_right hmgf (Real.exp_pos _).le) |>.trans ?_
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  ring_nf
  exact le_rfl

/-- Terminal upper-tail bound on a monotone alive event using full one-step
moments at alive source states.  Dead successors are discarded only after
the ordinary exponential one-step estimate is applied.  This variant is
essential when crossing the alive boundary supplies part of the negative
drift. -/
theorem probability_evolveKernels_alive_deviation_ge_le_exp_fullIncrement
    [DecidableEq Ω] (alive : Ω → Prop) [DecidablePred alive]
    {P : Ω → Prop} [DecidablePred P]
    (K : ℕ → Ω → FiniteLaw Ω) (f : ℕ → Ω → ℝ)
    (x₀ : Ω) (theta R a : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hP₀ : P x₀) (halive₀ : alive x₀)
    (htheta : 0 < theta) (hR : 0 ≤ R) (hthetaR : theta * R ≤ 1)
    (hK : ∀ i x, P x → (K i x).SupportedOn P)
    (hdead : ∀ i x, P x → ¬ alive x →
      (K i x).SupportedOn (fun y ↦ ¬ alive y))
    (hjump : ∀ i, i < n → ∀ x, P x → alive x → ∀ y,
      0 < (K i x).mass y → f (i + 1) y - f i x ≤ R)
    (hdrift : ∀ i, i < n → ∀ x, P x → alive x →
      (K i x).expectationReal (fun y ↦ f (i + 1) y - f i x) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ x, P x → alive x →
      (K i x).expectationReal
        (fun y ↦ (f (i + 1) y - f i x) ^ 2) ≤ v i) :
    ((evolveKernels K n (pure x₀)).probability
      (fun x ↦ alive x ∧ a ≤ f n x - f 0 x₀) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * ∑ i ∈ Finset.range n, v i) := by
  classical
  let L := evolveKernels K n (pure x₀)
  let Y : Ω → ℝ := fun x ↦
    if alive x then Real.exp (theta * (f n x - f 0 x₀)) else 0
  have hmgfStep : ∀ i, i < n → ∀ x, P x → alive x →
      (K i x).expectationReal (fun y ↦ if alive y then
        Real.exp (theta * (f (i + 1) y - f i x)) else 0) ≤
          Real.exp (theta ^ 2 * v i) := by
    intro i hi x hx halive
    calc
      (K i x).expectationReal (fun y ↦ if alive y then
          Real.exp (theta * (f (i + 1) y - f i x)) else 0) ≤
        (K i x).expectationReal (fun y ↦
          Real.exp (theta * (f (i + 1) y - f i x))) := by
            apply (K i x).expectationReal_mono
            intro y
            by_cases hy : alive y
            · simp [hy]
            · simp [hy, (Real.exp_pos _).le]
      _ ≤ Real.exp (theta ^ 2 * v i) := by
        exact expectationReal_exp_increment_le (K i x)
          (P := fun y ↦ 0 < (K i x).mass y) (fun _ hy ↦ hy)
          (fun y ↦ f (i + 1) y - f i x) theta R (v i)
          htheta.le hR hthetaR
          (fun y hy ↦ hjump i hi x hx halive y hy)
          (hdrift i hi x hx halive) (hsecond i hi x hx halive)
  have hmgf : L.expectationReal Y ≤
      Real.exp (theta ^ 2 * ∑ i ∈ Finset.range n, v i) := by
    have hiter := expectationReal_alive_exp_evolveKernels_le alive
      (P := P) K (fun i x ↦ f i x - f 0 x₀) theta
      (fun i ↦ theta ^ 2 * v i) n
      (supportedOn_pure P hP₀) hK hdead (by
        intro i hi x hx halive
        have hfun :
            (fun y ↦ if alive y then Real.exp (theta *
              ((f (i + 1) y - f 0 x₀) - (f i x - f 0 x₀))) else 0) =
            (fun y ↦ if alive y then Real.exp
              (theta * (f (i + 1) y - f i x)) else 0) := by
          funext y
          by_cases hy : alive y <;> simp [hy] <;> congr 1 <;> ring
        rw [hfun]
        exact hmgfStep i hi x hx halive)
    have hprod : ∏ i ∈ Finset.range n, Real.exp (theta ^ 2 * v i) =
        Real.exp (theta ^ 2 * ∑ i ∈ Finset.range n, v i) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
    simpa [L, Y, halive₀, hprod] using hiter
  have hmarkov := probability_coe_le_expectationReal_div
    L Y (Real.exp (theta * a)) (Real.exp_pos _) (fun x ↦ by
      by_cases hx : alive x <;> simp [Y, hx, (Real.exp_pos _).le])
  have hevent : (fun x ↦ Real.exp (theta * a) ≤ Y x) =
      (fun x ↦ alive x ∧ a ≤ f n x - f 0 x₀) := by
    funext x
    apply propext
    by_cases hx : alive x
    · simp only [Y, hx, if_true, true_and, Real.exp_le_exp]
      constructor <;> intro h <;> nlinarith [htheta]
    · simp [Y, hx, Real.exp_pos]
  rw [hevent] at hmarkov
  refine hmarkov.trans
    (div_le_div_of_nonneg_right hmgf (Real.exp_pos _).le) |>.trans ?_
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  ring_nf
  exact le_rfl

end FiniteLaw

end

end Erdos207
