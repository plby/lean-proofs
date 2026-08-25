/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# Finite probability tools for Erdős Problem 207

Kwan--Sah--Sawhney--Simkin use only finite probability spaces.  This file
keeps the elementary part of their probability bookkeeping as finite sums of
nonnegative reals.  In particular, no measure-completion side conditions are
needed for union and Markov bounds.
-/

namespace Erdos207

open scoped BigOperators NNReal

noncomputable section

/-- A probability law on a finite sample type, represented by its mass
function. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ≥0
  sum_mass : ∑ ω, mass ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- The mass of one Bernoulli bit with success probability `p`. -/
def bernoulliBitMass (p : ℝ≥0) (b : Bool) : ℝ≥0 :=
  if b then p else 1 - p

lemma sum_bernoulliBitMass {p : ℝ≥0} (hp : p ≤ 1) :
    ∑ b : Bool, bernoulliBitMass p b = 1 := by
  simpa [Fintype.sum_bool, bernoulliBitMass, add_comm] using
    tsub_add_cancel_of_le hp

/-- Product law of independent, not necessarily identically distributed,
Bernoulli bits. -/
def independentBits {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) : FiniteLaw (I → Bool) where
  mass ω := ∏ i, bernoulliBitMass (p i) (ω i)
  sum_mass := by
    classical
    rw [← Fintype.prod_sum]
    simp_rw [sum_bernoulliBitMass (hp _)]
    simp

@[simp]
lemma independentBits_mass {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (ω : I → Bool) :
    (independentBits p hp).mass ω =
      ∏ i, bernoulliBitMass (p i) (ω i) := rfl

/-- The deterministic law concentrated at one outcome. -/
def pure [DecidableEq Ω] (x : Ω) : FiniteLaw Ω where
  mass y := if y = x then 1 else 0
  sum_mass := by simp

/-- The uniform law on a nonempty finite type. -/
def uniform [Nonempty Ω] : FiniteLaw Ω where
  mass _ := (Fintype.card Ω : ℝ≥0)⁻¹
  sum_mass := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ, mul_inv_cancel₀]
    positivity

/-- Push a finite law forward along a function. -/
def map {Ξ : Type*} [Fintype Ξ] [DecidableEq Ξ] (f : Ω → Ξ)
    (L : FiniteLaw Ω) : FiniteLaw Ξ where
  mass y := ∑ x, if f x = y then L.mass x else 0
  sum_mass := by
    classical
    rw [Finset.sum_comm]
    simpa using L.sum_mass

/-- Kleisli composition of finite laws. -/
def bind {Ξ : Type*} [Fintype Ξ] (L : FiniteLaw Ω)
    (K : Ω → FiniteLaw Ξ) : FiniteLaw Ξ where
  mass y := ∑ x, L.mass x * (K x).mass y
  sum_mass := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (K _).sum_mass, mul_one]
    exact L.sum_mass

/-- Every outcome carrying positive mass satisfies `P`. -/
def SupportedOn (P : Ω → Prop) (L : FiniteLaw Ω) : Prop :=
  ∀ x, 0 < L.mass x → P x

/-- Every finite probability law has at least one positive-mass outcome. -/
theorem exists_mass_pos (L : FiniteLaw Ω) : ∃ x, 0 < L.mass x := by
  have hsum : 0 < ∑ x, L.mass x := by
    rw [L.sum_mass]
    exact zero_lt_one
  obtain ⟨x, _hx, hmass⟩ := Finset.sum_pos_iff.mp hsum
  exact ⟨x, hmass⟩

/-- Iterate a finite Markov kernel for a fixed number of steps. -/
def iterateKernel (K : Ω → FiniteLaw Ω) : ℕ → FiniteLaw Ω → FiniteLaw Ω
  | 0, L => L
  | n + 1, L => iterateKernel K n (bind L K)

@[simp]
lemma pure_mass [DecidableEq Ω] (x y : Ω) :
    (pure x).mass y = if y = x then 1 else 0 := rfl

@[ext]
lemma ext {L K : FiniteLaw Ω} (h : ∀ x, L.mass x = K.mass x) : L = K := by
  cases L with
  | mk Lmass Lsum =>
      cases K with
      | mk Kmass Ksum =>
          simp only [mk.injEq]
          funext x
          exact h x

@[simp]
lemma bind_pure [DecidableEq Ω] (x : Ω)
    (K : Ω → FiniteLaw Ω) : bind (pure x) K = K x := by
  ext y
  simp [bind, pure]

lemma supportedOn_pure [DecidableEq Ω] (P : Ω → Prop) {x : Ω}
    (hx : P x) : SupportedOn P (pure x) := by
  intro y hy
  simp only [pure_mass] at hy
  by_cases h : y = x
  · simpa [h] using hx
  · simp [h] at hy

lemma SupportedOn.bind {Ξ : Type*} [Fintype Ξ]
    {P : Ω → Prop} {Q : Ξ → Prop} {L : FiniteLaw Ω}
    (hL : SupportedOn P L) (K : Ω → FiniteLaw Ξ)
    (hK : ∀ x, P x → SupportedOn Q (K x)) : SupportedOn Q (bind L K) := by
  intro y hy
  change 0 < ∑ x, L.mass x * (K x).mass y at hy
  obtain ⟨x, _, hx⟩ := Finset.sum_pos_iff.mp hy
  have hparts : 0 < L.mass x ∧ 0 < (K x).mass y := by
    rcases mul_pos_iff.mp hx with hpos | hneg
    · exact hpos
    · exact ((not_lt_of_ge (zero_le : 0 ≤ L.mass x)) hneg.1).elim
  exact hK x (hL x hparts.1) y hparts.2

lemma SupportedOn.map {Ξ : Type*} [Fintype Ξ] [DecidableEq Ξ]
    {P : Ω → Prop} {Q : Ξ → Prop} {L : FiniteLaw Ω}
    (hL : SupportedOn P L) (f : Ω → Ξ)
    (hf : ∀ x, P x → Q (f x)) : SupportedOn Q (map f L) := by
  intro y hy
  change 0 < ∑ x, if f x = y then L.mass x else 0 at hy
  obtain ⟨x, _, hx⟩ := Finset.sum_pos_iff.mp hy
  by_cases hxy : f x = y
  · subst y
    rw [if_pos rfl] at hx
    exact hf x (hL x hx)
  · simp [hxy] at hx

lemma uniform_supported [Nonempty Ω] (P : Ω → Prop) (hP : ∀ x, P x) :
    SupportedOn P (uniform : FiniteLaw Ω) := by
  intro x _
  exact hP x

lemma SupportedOn.iterateKernel {P : Ω → Prop} {L : FiniteLaw Ω}
    (hL : SupportedOn P L) (K : Ω → FiniteLaw Ω)
    (hK : ∀ x, P x → SupportedOn P (K x)) (n : ℕ) :
    SupportedOn P (iterateKernel K n L) := by
  induction n generalizing L with
  | zero => exact hL
  | succ n ih =>
      exact ih (hL.bind K hK)

/-- Probability of a decidable event. -/
def probability (P : Ω → Prop) (L : FiniteLaw Ω) : ℝ≥0 := by
  classical
  exact
  ∑ ω, if P ω then L.mass ω else 0

/-- Exact probability that the independent bits agree with a prescribed
assignment on a finite coordinate set. -/
theorem independentBits_probability_agrees
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (σ : I → Bool) (T : Finset I) :
    (independentBits p hp).probability
        (fun ω ↦ ∀ i ∈ T, ω i = σ i) =
      ∏ i ∈ T, bernoulliBitMass (p i) (σ i) := by
  classical
  unfold probability
  simp only [independentBits_mass]
  calc
    _ =
        ∑ ω : I → Bool, ∏ i,
          if i ∈ T then
            (if ω i = σ i then bernoulliBitMass (p i) (ω i) else 0)
          else bernoulliBitMass (p i) (ω i) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hall : ∀ i ∈ T, ω i = σ i
      · rw [if_pos hall]
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ T
        · simp [hi, hall i hi]
        · simp [hi]
      · rw [if_neg hall]
        push Not at hall
        obtain ⟨i, hiT, hiω⟩ := hall
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hiT, hiω]
    _ = ∏ i, ∑ b : Bool,
          if i ∈ T then
            (if b = σ i then bernoulliBitMass (p i) b else 0)
          else bernoulliBitMass (p i) b := by
      exact (Fintype.prod_sum fun i b ↦
        if i ∈ T then
          (if b = σ i then bernoulliBitMass (p i) b else 0)
        else bernoulliBitMass (p i) b).symm
    _ = ∏ i, if i ∈ T then bernoulliBitMass (p i) (σ i) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ T
      · cases σ i <;> simp [hi, bernoulliBitMass]
      · simpa [hi, Fintype.sum_bool, add_comm] using
          sum_bernoulliBitMass (hp i)
    _ = ∏ i ∈ T, bernoulliBitMass (p i) (σ i) := by simp

/-- Exact joint-success probability for the product Bernoulli law. -/
theorem independentBits_probability_forall_true
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (T : Finset I) :
    (independentBits p hp).probability
        (fun ω ↦ ∀ i ∈ T, ω i = true) =
      ∏ i ∈ T, p i := by
  simpa [bernoulliBitMass] using
    independentBits_probability_agrees p hp (fun _ ↦ true) T

/-- Exact probability that every coordinate in `T` is absent. -/
theorem independentBits_probability_forall_false
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (T : Finset I) :
    (independentBits p hp).probability
        (fun ω ↦ ∀ i ∈ T, ω i = false) =
      ∏ i ∈ T, (1 - p i) := by
  simpa [bernoulliBitMass] using
    independentBits_probability_agrees p hp (fun _ ↦ false) T

/-- Subset selected by a family of Bernoulli bits. -/
def selectedByBits {I : Type*} [Fintype I] [DecidableEq I]
    (ω : I → Bool) : Finset I :=
  Finset.univ.filter fun i ↦ ω i = true

@[simp]
lemma mem_selectedByBits_iff {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → Bool} {i : I} :
    i ∈ selectedByBits ω ↔ ω i = true := by
  simp [selectedByBits]

/-- Exact joint-inclusion probability in the independently selected subset. -/
theorem independentBits_probability_subset_selected
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (T : Finset I) :
    (independentBits p hp).probability
        (fun ω ↦ T ⊆ selectedByBits ω) =
      ∏ i ∈ T, p i := by
  rw [← independentBits_probability_forall_true p hp T]
  congr 1
  funext ω
  apply propext
  constructor
  · intro h i hiT
    exact mem_selectedByBits_iff.mp (h hiT)
  · intro h i hiT
    exact mem_selectedByBits_iff.mpr (h i hiT)

/-- Exact avoidance probability for the independently selected subset. -/
theorem independentBits_probability_disjoint_selected
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (T : Finset I) :
    (independentBits p hp).probability
        (fun ω ↦ Disjoint T (selectedByBits ω)) =
      ∏ i ∈ T, (1 - p i) := by
  rw [← independentBits_probability_forall_false p hp T]
  congr 1
  funext ω
  apply propext
  rw [Finset.disjoint_left]
  constructor
  · intro h i hiT
    cases hiω : ω i
    · rfl
    · exact (h hiT (mem_selectedByBits_iff.mpr hiω)).elim
  · intro h i hiT hiSelected
    have hiTrue := mem_selectedByBits_iff.mp hiSelected
    rw [h i hiT] at hiTrue
    simp at hiTrue

/-- A support event has probability one. -/
lemma probability_eq_one_of_supported (L : FiniteLaw Ω) (P : Ω → Prop)
    (hP : SupportedOn P L) : L.probability P = 1 := by
  classical
  rw [← L.sum_mass]
  unfold probability
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0 < L.mass x
  · simp [hP x hx]
  · have hx0 : L.mass x = 0 := le_antisymm (not_lt.mp hx) (zero_le : 0 ≤ L.mass x)
    simp [hx0]

@[simp]
lemma probability_pure [DecidableEq Ω] (x : Ω) (P : Ω → Prop)
    [DecidablePred P] :
    (pure x).probability P = if P x then 1 else 0 := by
  classical
  unfold probability
  by_cases hx : P x
  · rw [Finset.sum_eq_single x]
    · simp [hx, pure]
    · intro y _hy hyx
      simp [pure, hyx]
    · simp
  · simp only [if_neg hx]
    apply Finset.sum_eq_zero
    intro y _hy
    by_cases hyx : y = x
    · subst y
      simp [hx]
    · simp [pure, hyx]

/-- Probability under a finite bind is the average of the conditional
probabilities.  This is the finite-sum form of the law of total
probability. -/
lemma probability_bind {Ξ : Type*} [Fintype Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (P : Ξ → Prop) :
    (bind L K).probability P =
      ∑ x, L.mass x * (K x).probability P := by
  classical
  unfold probability
  change (∑ y, if P y then ∑ x, L.mass x * (K x).mass y else 0) = _
  calc
    (∑ y, if P y then ∑ x, L.mass x * (K x).mass y else 0) =
        ∑ y, ∑ x, L.mass x * (if P y then (K x).mass y else 0) := by
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hy : P y <;> simp [hy, Finset.mul_sum]
    _ = ∑ x, ∑ y, L.mass x *
        (if P y then (K x).mass y else 0) := Finset.sum_comm
    _ = ∑ x, L.mass x *
        (∑ y, if P y then (K x).mass y else 0) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
    _ = ∑ x, L.mass x * (K x).probability P := rfl

/-- Pushing a finite law forward takes probabilities to probabilities of
preimages. -/
lemma probability_map {Ξ : Type*} [Fintype Ξ] [DecidableEq Ξ]
    (f : Ω → Ξ) (L : FiniteLaw Ω) (P : Ξ → Prop) :
    (map f L).probability P = L.probability (fun x ↦ P (f x)) := by
  classical
  have hmap : map f L = bind L (fun x ↦ pure (f x)) := by
    apply FiniteLaw.ext
    intro y
    change (∑ x, if f x = y then L.mass x else 0) =
      ∑ x, L.mass x * (if y = f x then 1 else 0)
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hxy : f x = y
    · simp [hxy]
    · simp [hxy, Ne.symm hxy]
  rw [hmap, probability_bind]
  change (∑ x, L.mass x * (pure (f x)).probability P) =
    ∑ x, if P (f x) then L.mass x else 0
  apply Finset.sum_congr rfl
  intro x _hx
  rw [probability_pure]
  by_cases hx : P (f x) <;> simp [hx]

/-- An event containing exactly one outcome under the uniform law has mass
the inverse cardinality of the sample type. -/
lemma uniform_probability_unique [Nonempty Ω]
    (P : Ω → Prop) (x₀ : Ω) (hP : ∀ x, P x ↔ x = x₀) :
    (uniform : FiniteLaw Ω).probability P =
      (Fintype.card Ω : ℝ≥0)⁻¹ := by
  classical
  unfold probability
  simp only [hP, uniform]
  simp

/-- Exact probability of an arbitrary event under the uniform law, written
as its finite cardinality divided by the ambient cardinality. -/
lemma uniform_probability_eq_card_filter [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] :
    (uniform : FiniteLaw Ω).probability P =
      ((Finset.univ.filter P).card : ℝ≥0) *
        (Fintype.card Ω : ℝ≥0)⁻¹ := by
  classical
  unfold probability uniform
  simp only
  rw [← Finset.sum_filter]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Expectation of a nonnegative random variable. -/
def expectation (X : Ω → ℝ≥0) (L : FiniteLaw Ω) : ℝ≥0 :=
  ∑ ω, L.mass ω * X ω

@[simp]
lemma probability_false (L : FiniteLaw Ω) : L.probability (fun _ ↦ False) = 0 := by
  classical
  simp [probability]

@[simp]
lemma probability_true (L : FiniteLaw Ω) : L.probability (fun _ ↦ True) = 1 := by
  classical
  simpa [probability] using L.sum_mass

/-- Event probability is monotone under implication. -/
lemma probability_mono (L : FiniteLaw Ω) {P Q : Ω → Prop}
    (hPQ : ∀ ω, P ω → Q ω) :
    L.probability P ≤ L.probability Q := by
  classical
  unfold probability
  apply Finset.sum_le_sum
  intro ω _
  by_cases hP : P ω
  · simp [hP, hPQ ω hP]
  · simp [hP]

/-- Event monotonicity where the implication only has to hold on the
positive-mass support of the law. -/
lemma probability_mono_of_supported (L : FiniteLaw Ω)
    {P Q R : Ω → Prop} (hR : SupportedOn R L)
    (hPQ : ∀ ω, R ω → P ω → Q ω) :
    L.probability P ≤ L.probability Q := by
  classical
  unfold probability
  apply Finset.sum_le_sum
  intro ω _hω
  by_cases hmass : 0 < L.mass ω
  · by_cases hP : P ω
    · simp [hP, hPQ ω (hR ω hmass) hP]
    · simp [hP]
  · have hzero : L.mass ω = 0 :=
      le_antisymm (not_lt.mp hmass) (zero_le : 0 ≤ L.mass ω)
    simp [hzero]

lemma probability_le_one (L : FiniteLaw Ω) (P : Ω → Prop) :
    L.probability P ≤ 1 := by
  classical
  rw [← L.probability_true]
  exact L.probability_mono fun _ _ ↦ trivial

/-- The right-recursive form of the iterated kernel.  Although
`iterateKernel` is defined by first binding the initial law, repeated use of
one fixed kernel is equivalently obtained by applying one final bind. -/
lemma iterateKernel_succ_right (K : Ω → FiniteLaw Ω) (n : ℕ)
    (L : FiniteLaw Ω) :
    iterateKernel K (n + 1) L = bind (iterateKernel K n L) K := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
      change iterateKernel K (n + 1) (bind L K) =
        bind (iterateKernel K (n + 1) L) K
      rw [ih]
      rfl

/-- Positive probability supplies a deterministic successful outcome. -/
lemma exists_of_probability_pos (L : FiniteLaw Ω) {P : Ω → Prop}
    (hP : 0 < L.probability P) : ∃ ω, P ω := by
  classical
  by_contra hnone
  push Not at hnone
  have : L.probability P = 0 := by
    unfold probability
    simp [hnone]
  exact (this ▸ hP).false

/-- Positive event probability supplies a successful outcome in the
positive-mass support of the law. -/
lemma exists_supported_of_probability_pos (L : FiniteLaw Ω) {P : Ω → Prop}
    (hP : 0 < L.probability P) : ∃ ω, 0 < L.mass ω ∧ P ω := by
  classical
  unfold probability at hP
  rw [Finset.sum_pos_iff] at hP
  obtain ⟨ω, _hω, hterm⟩ := hP
  by_cases hgood : P ω
  · exact ⟨ω, by simpa only [if_pos hgood] using hterm, hgood⟩
  · simp only [if_neg hgood, lt_self_iff_false] at hterm

/-- Finite complement formula. -/
lemma probability_not (L : FiniteLaw Ω) (P : Ω → Prop) :
    L.probability (fun ω ↦ ¬ P ω) = 1 - L.probability P := by
  classical
  apply eq_tsub_of_add_eq
  unfold probability
  rw [← Finset.sum_add_distrib]
  rw [← L.sum_mass]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : P ω <;> simp [hω]

/-- Finite difference formula inside an event.  This is the elementary
partition identity used when a derived Bernoulli event is the conjunction of
several independent coordinates rather than one coordinate itself. -/
lemma probability_and_not (L : FiniteLaw Ω) (P Q : Ω → Prop) :
    L.probability (fun ω ↦ P ω ∧ ¬ Q ω) =
      L.probability P - L.probability (fun ω ↦ P ω ∧ Q ω) := by
  classical
  apply eq_tsub_of_add_eq
  unfold probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]

/-- The finite union bound for two events. -/
lemma probability_or_le (L : FiniteLaw Ω) (P Q : Ω → Prop)
    : L.probability (fun ω ↦ P ω ∨ Q ω) ≤
      L.probability P + L.probability Q := by
  classical
  unfold probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]

/-- Event monotonicity need only be proved on the positive-mass support of
the law.  This avoids totalizing auxiliary constructions on irrelevant
zero-mass outcomes. -/
lemma probability_mono_on_support (L : FiniteLaw Ω)
    (Support P Q : Ω -> Prop)
    (hSupport : L.SupportedOn Support)
    (himp : ∀ omega, Support omega -> P omega -> Q omega) :
    L.probability P <= L.probability Q := by
  classical
  unfold probability
  apply Finset.sum_le_sum
  intro omega _homega
  by_cases hmass : 0 < L.mass omega
  · have hs := hSupport omega hmass
    by_cases hP : P omega
    · simp [hP, himp omega hs hP]
    · simp [hP]
  · have hzero : L.mass omega = 0 :=
      le_antisymm (not_lt.mp hmass) zero_le
    simp [hzero]

/-- Union bound over an arbitrary finite family of events. -/
lemma probability_exists_le {I : Type*} [DecidableEq I] (L : FiniteLaw Ω)
    (S : Finset I) (P : I → Ω → Prop) :
    L.probability (fun ω ↦ ∃ i ∈ S, P i ω) ≤
      ∑ i ∈ S, L.probability (P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [probability]
  | @insert i S hi ih =>
      have hor := L.probability_or_le (P i) (fun ω ↦ ∃ j ∈ S, P j ω)
      have hadd : L.probability (P i) +
          L.probability (fun ω ↦ ∃ j ∈ S, P j ω) ≤
          L.probability (P i) + ∑ j ∈ S, L.probability (P j) :=
        add_le_add le_rfl ih
      simpa [hi, or_assoc] using hor.trans hadd

/-- A strict union-bound estimate supplies one outcome avoiding every bad
event in the finite family. -/
theorem exists_avoiding_of_sum_probability_lt_one
    {I : Type*} [DecidableEq I] (L : FiniteLaw Ω)
    (S : Finset I) (P : I → Ω → Prop)
    (hsmall : ∑ i ∈ S, L.probability (P i) < 1) :
    ∃ ω, ∀ i ∈ S, ¬ P i ω := by
  have hbad : L.probability (fun ω ↦ ∃ i ∈ S, P i ω) < 1 :=
    (L.probability_exists_le S P).trans_lt hsmall
  by_contra hnone
  push Not at hnone
  have htrue : (fun ω ↦ ∃ i ∈ S, P i ω) = (fun _ : Ω ↦ True) := by
    funext ω
    exact propext ⟨fun _ ↦ trivial, fun _ ↦ hnone ω⟩
  rw [htrue, L.probability_true] at hbad
  exact (lt_irrefl 1 hbad)

/-- Finite independent-sampling existence lemma: if the sum of the exact
avoidance probabilities is below one, one selected set meets every member of
the prescribed finite family. -/
theorem exists_selected_meets_all_of_sum_avoidance_lt_one
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (S : Finset J) (groups : J → Finset I)
    (hsmall : ∑ j ∈ S, ∏ i ∈ groups j, (1 - p i) < 1) :
    ∃ R : Finset I, ∀ j ∈ S, ¬ Disjoint (groups j) R := by
  let L := independentBits p hp
  obtain ⟨ω, hω⟩ := L.exists_avoiding_of_sum_probability_lt_one S
    (fun j ω ↦ Disjoint (groups j) (selectedByBits ω)) (by
      simpa [L, independentBits_probability_disjoint_selected] using hsmall)
  exact ⟨selectedByBits ω, hω⟩

/-- Pointwise comparison implies comparison of finite expectations. -/
lemma expectation_mono (L : FiniteLaw Ω) {X Y : Ω → ℝ≥0}
    (hXY : ∀ ω, X ω ≤ Y ω) : L.expectation X ≤ L.expectation Y := by
  unfold expectation
  exact Finset.sum_le_sum fun ω _ ↦ by
    simpa [mul_comm] using mul_le_mul_left (hXY ω) (L.mass ω)

@[simp]
lemma expectation_zero (L : FiniteLaw Ω) : L.expectation (fun _ ↦ 0) = 0 := by
  simp [expectation]

lemma expectation_add (L : FiniteLaw Ω) (X Y : Ω → ℝ≥0) :
    L.expectation (fun ω ↦ X ω + Y ω) = L.expectation X + L.expectation Y := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

/-- Multiplication form of Markov's inequality.  This formulation does not
need a positivity side condition on the threshold. -/
lemma probability_mul_le_expectation (L : FiniteLaw Ω) (X : Ω → ℝ≥0)
    (a : ℝ≥0) : L.probability (fun ω ↦ a ≤ X ω) * a ≤ L.expectation X := by
  classical
  unfold probability expectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : a ≤ X ω
  · simpa [hω, mul_comm, mul_assoc] using mul_le_mul_left hω (L.mass ω)
  · simp [hω]

/-- Markov's inequality in quotient form. -/
lemma probability_le_expectation_div (L : FiniteLaw Ω) (X : Ω → ℝ≥0)
    {a : ℝ≥0} (ha : 0 < a) :
    L.probability (fun ω ↦ a ≤ X ω) ≤ L.expectation X / a := by
  rw [le_div_iff₀ ha]
  exact L.probability_mul_le_expectation X a

end FiniteLaw

end

end Erdos207
