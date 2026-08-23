/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The rational-prime specialization of the Baker lower bound

This file is the assembly point for the van der Poorten--Loxton input used in
Erdős Problem 240.  The difficult auxiliary-function argument naturally
produces an integral coefficient cutoff `N`, normalized by `exp 2 ≤ N`.  The
project-facing theorem instead uses a real cutoff `B`, normalized by
`exp 1 ≤ B`.

The main theorem proved below performs that normalization without losing the
uniformity in the distinguished prime: replacing `B` by `ceil (e B)` costs
only a factor three in `log B`.  It reduces the unconditional result to the
source-shaped integral-cutoff bound
`HasNonemptyVDPLSmallFormContradiction`; that proposition is a named local
goal, not an assumption hidden in the final Erdős theorem.

The empty old-family case is also proved directly.  This isolates the source
theorem to the genuinely Baker-theoretic case of at least two logarithms.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.RationalPrimeBaker

universe u

/-- The finite indexed rational logarithmic form.  This definition is kept in
the main-independent Baker module so that `Erdos240.lean` can eventually
import the proved source theorem without an import cycle. -/
noncomputable def indexedRationalLogForm {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (p : ℕ) (c : ι → ℤ) (d : ℤ) : ℝ :=
  ∑ i, (c i : ℝ) * Real.log (a i : ℝ) +
    (d : ℝ) * Real.log (p : ℝ)

/-- The integral cutoff used by the source argument. -/
noncomputable def integerCoeffBound (B : ℝ) : ℕ :=
  ⌈Real.exp 1 * B⌉₊

lemma le_integerCoeffBound {B : ℝ} (hB : Real.exp 1 ≤ B) :
    B ≤ (integerCoeffBound B : ℝ) := by
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  calc
    B ≤ Real.exp 1 * B := by
      exact le_mul_of_one_le_left ((Real.exp_pos 1).trans_le hB).le he
    _ ≤ (integerCoeffBound B : ℝ) := Nat.le_ceil _

lemma exp_two_le_integerCoeffBound {B : ℝ} (hB : Real.exp 1 ≤ B) :
    Real.exp 2 ≤ (integerCoeffBound B : ℝ) := by
  calc
    Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    _ ≤ Real.exp 1 * B := mul_le_mul_of_nonneg_left hB (Real.exp_pos 1).le
    _ ≤ (integerCoeffBound B : ℝ) := Nat.le_ceil _

/-- Passing from `B` to `ceil (e B)` costs at most a factor three in its
logarithm. -/
lemma log_integerCoeffBound_le_three_mul_log {B : ℝ}
    (hB : Real.exp 1 ≤ B) :
    Real.log (integerCoeffBound B : ℝ) ≤ 3 * Real.log B := by
  have hBpos : 0 < B := (Real.exp_pos 1).trans_le hB
  have hxpos : 0 < Real.exp 1 * B := mul_pos (Real.exp_pos 1) hBpos
  have hxone : 1 ≤ Real.exp 1 * B := by
    calc
      1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      _ = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ Real.exp 1 * B := mul_le_mul_of_nonneg_left hB (Real.exp_pos 1).le
  have hceil : (integerCoeffBound B : ℝ) ≤ 2 * (Real.exp 1 * B) := by
    have hlt : (integerCoeffBound B : ℝ) < Real.exp 1 * B + 1 :=
      Nat.ceil_lt_add_one hxpos.le
    linarith
  have hboundPos : 0 < (integerCoeffBound B : ℝ) :=
    hBpos.trans_le (le_integerCoeffBound hB)
  have hlogB : 1 ≤ Real.log B :=
    (Real.le_log_iff_exp_le hBpos).2 hB
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  calc
    Real.log (integerCoeffBound B : ℝ) ≤
        Real.log (2 * (Real.exp 1 * B)) :=
      Real.log_le_log hboundPos hceil
    _ = Real.log 2 + Real.log (Real.exp 1) + Real.log B := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (mul_ne_zero (Real.exp_ne_zero 1) hBpos.ne'),
        Real.log_mul (Real.exp_ne_zero 1) hBpos.ne']
      ring
    _ = Real.log 2 + 1 + Real.log B := by rw [Real.log_exp]
    _ ≤ 3 * Real.log B := by linarith

lemma natAbs_le_integerCoeffBound {B : ℝ} {z : ℤ}
    (hB : Real.exp 1 ≤ B) (hz : |(z : ℝ)| ≤ B) :
    z.natAbs ≤ integerCoeffBound B := by
  have hz' : |(z : ℝ)| ≤ (integerCoeffBound B : ℝ) :=
    hz.trans (le_integerCoeffBound hB)
  have hcast : (z.natAbs : ℝ) = |(z : ℝ)| := by
    rw [Nat.cast_natAbs (α := ℝ), Int.cast_abs]
  have hz'' : (z.natAbs : ℝ) ≤ (integerCoeffBound B : ℝ) := by
    rw [hcast]
    exact hz'
  exact_mod_cast hz''

/-- The project-independent indexed-family formulation of the uniform
rational-prime lower bound.  The final coefficient is explicitly nonzero,
matching both the source theorem and the only downstream use. -/
def HasUniformRationalPrimeLogBounds : Prop :=
  ∀ (ι : Type*) [Fintype ι] (a : ι → ℕ),
    (∀ i, (a i).Prime) → Function.Injective a →
    ∃ K : ℝ, 0 < K ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (B : ℝ),
        p.Prime → (∀ i, a i ≠ p) → Real.exp 1 ≤ B →
        (∀ i, |(c i : ℝ)| ≤ B) → |(d : ℝ)| ≤ B → d ≠ 0 →
        indexedRationalLogForm a p c d ≠ 0 →
        Real.exp (-K * Real.log (p : ℝ) * Real.log B) ≤
          |indexedRationalLogForm a p c d|

/-- Finset form used by a finite stage in the Erdős 240 construction. -/
noncomputable def finsetRationalLogForm (s : Finset ℕ) (p : ℕ)
    (c : ℕ → ℤ) (d : ℤ) : ℝ :=
  ∑ q ∈ s, (c q : ℝ) * Real.log (q : ℝ) +
    (d : ℝ) * Real.log (p : ℝ)

/-- Enumerating a finite prime set by its subtype preserves the exact
logarithmic form and hence the uniform constant.  This is the
main-independent bridge eventually consumed by `FiniteStage`. -/
theorem finset_bounds_of_uniform
    (h : HasUniformRationalPrimeLogBounds.{0})
    (s : Finset ℕ) (hs : ∀ q ∈ s, q.Prime) :
    ∃ K : ℝ, 0 < K ∧
      ∀ ⦃p : ℕ⦄ (c : ℕ → ℤ) (d : ℤ) (B : ℝ),
        p.Prime → p ∉ s → Real.exp 1 ≤ B →
        (∀ q ∈ s, |(c q : ℝ)| ≤ B) → |(d : ℝ)| ≤ B → d ≠ 0 →
        finsetRationalLogForm s p c d ≠ 0 →
        Real.exp (-K * Real.log (p : ℝ) * Real.log B) ≤
          |finsetRationalLogForm s p c d| := by
  classical
  let ι := {q : ℕ // q ∈ s}
  let a : ι → ℕ := fun q ↦ q.1
  have haPrime : ∀ i, (a i).Prime := fun i ↦ hs i.1 i.2
  have haInj : Function.Injective a := fun i j hij ↦ Subtype.ext hij
  obtain ⟨K, hK, hbound⟩ := h ι a haPrime haInj
  refine ⟨K, hK, ?_⟩
  intro p c d B hp hpFresh hB hc hd hdne hform
  let ci : ι → ℤ := fun q ↦ c q.1
  have hpDistinct : ∀ i, a i ≠ p := by
    intro i hip
    apply hpFresh
    rw [← hip]
    exact i.2
  have hci : ∀ i, |(ci i : ℝ)| ≤ B := fun i ↦ hc i.1 i.2
  have hformEq : indexedRationalLogForm a p ci d =
      finsetRationalLogForm s p c d := by
    simp only [indexedRationalLogForm, finsetRationalLogForm, ci, a]
    congr 1
    symm
    exact Finset.sum_subtype s (fun q ↦ Iff.rfl)
      (fun q ↦ (c q : ℝ) * Real.log (q : ℝ))
  have hindexed : indexedRationalLogForm a p ci d ≠ 0 := by
    simpa only [hformEq] using hform
  simpa only [hformEq] using
    hbound ci d B hp hpDistinct hB hci hd hdne hindexed

/-- The exact integral-cutoff interface produced by the specialized
van der Poorten--Loxton auxiliary-function argument.  Its constant may depend
on the fixed indexed family `a`, but not on the varying prime `p`, the
coefficients, or the cutoff `N`.

This is an intermediate proposition describing the required output of the
source argument. -/
def HasIntegralCutoffRationalPrimeLogBounds : Prop :=
  ∀ (ι : Type*) [Fintype ι] (a : ι → ℕ),
    (∀ i, (a i).Prime) → Function.Injective a →
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (N : ℕ),
        p.Prime → (∀ i, a i ≠ p) → Real.exp 2 ≤ (N : ℝ) →
        (∀ i, (c i).natAbs ≤ N) → d.natAbs ≤ N → d ≠ 0 →
        indexedRationalLogForm a p c d ≠ 0 →
        Real.exp (-C * Real.log (p : ℝ) * Real.log (N : ℝ)) ≤
          |indexedRationalLogForm a p c d|

/-- Source-shaped bound with a genuinely distinguished last logarithm.  The
source auxiliary function divides by the last coefficient, so `d ≠ 0` is
an explicit hypothesis here. -/
def HasDistinguishedIntegralCutoffRationalPrimeLogBounds : Prop :=
  ∀ (ι : Type u) [Fintype ι] (a : ι → ℕ),
    (∀ i, (a i).Prime) → Function.Injective a →
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (N : ℕ),
        p.Prime → (∀ i, a i ≠ p) → Real.exp 2 ≤ (N : ℝ) →
        (∀ i, (c i).natAbs ≤ N) → d.natAbs ≤ N → d ≠ 0 →
        indexedRationalLogForm a p c d ≠ 0 →
        Real.exp (-C * Real.log (p : ℝ) * Real.log (N : ℝ)) ≤
          |indexedRationalLogForm a p c d|

/-- The integral-cutoff interface is deliberately source-shaped: the varying
prime is the distinguished last logarithm, and its coefficient is nonzero.
The two propositions are therefore definitionally the same.  This is exactly
the downstream case needed for Erdős 240, because unequal `p`-factorizations
give a nonzero coefficient of `log p`. -/
theorem integralCutoff_bounds_of_distinguished
    (hsource : HasDistinguishedIntegralCutoffRationalPrimeLogBounds.{u}) :
    HasIntegralCutoffRationalPrimeLogBounds.{u} :=
  hsource

/-- The integer-cutoff source estimate implies the real-cutoff indexed
estimate.  Crucially, the new constant is `3*C`; it remains independent of
the varying prime. -/
theorem uniform_rational_prime_log_lower_bound_of_integralCutoff
    (hsource : HasIntegralCutoffRationalPrimeLogBounds.{u}) :
    HasUniformRationalPrimeLogBounds.{u} := by
  intro ι _ a ha hinj
  obtain ⟨C, hC, hbound⟩ := hsource ι a ha hinj
  refine ⟨3 * C, by positivity, ?_⟩
  intro p c d B hp hpFresh hB hc hd hdne hform
  let N : ℕ := integerCoeffBound B
  have hNlarge : Real.exp 2 ≤ (N : ℝ) := by
    simpa only [N] using exp_two_le_integerCoeffBound hB
  have hcN : ∀ i, (c i).natAbs ≤ N := by
    intro i
    simpa only [N] using natAbs_le_integerCoeffBound hB (hc i)
  have hdN : d.natAbs ≤ N := by
    simpa only [N] using natAbs_le_integerCoeffBound hB hd
  have hlower := hbound c d N hp hpFresh hNlarge hcN hdN hdne hform
  have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (le_trans (by norm_num) hpTwo)
  have hlogN : Real.log (N : ℝ) ≤ 3 * Real.log B := by
    simpa only [N] using log_integerCoeffBound_le_three_mul_log hB
  have hexponent :
      -(3 * C) * Real.log (p : ℝ) * Real.log B ≤
        -C * Real.log (p : ℝ) * Real.log (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogN (mul_nonneg hC.le hlogp)
    nlinarith
  exact (Real.exp_le_exp.mpr hexponent).trans hlower

/-- An integral-cutoff source theorem yields the exact uniform family theorem
specified in `BakerPlan.md`. -/
theorem uniform_rational_prime_log_lower_bound_of_integralCutoff_apply
    (hsource : HasIntegralCutoffRationalPrimeLogBounds.{u})
    {ι : Type u} [Fintype ι]
    (old : ι → ℕ) (hold : ∀ i, (old i).Prime)
    (hinj : Function.Injective old) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (B : ℝ),
        p.Prime → (∀ i, old i ≠ p) → Real.exp 1 ≤ B →
        (∀ i, |(c i : ℝ)| ≤ B) → |(d : ℝ)| ≤ B → d ≠ 0 →
        indexedRationalLogForm old p c d ≠ 0 →
        Real.exp (-C * Real.log (p : ℝ) * Real.log B) ≤
          |indexedRationalLogForm old p c d| := by
  exact uniform_rational_prime_log_lower_bound_of_integralCutoff hsource
    ι old hold hinj

/-! ## The elementary empty-family case -/

/-- With no old primes, the form is just `d * log p`; its lower bound is
elementary.  The constant `1` already suffices under `exp 1 ≤ B`. -/
theorem uniform_rational_prime_log_lower_bound_isEmpty
    {ι : Type u} [Fintype ι] [IsEmpty ι]
    (old : ι → ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (B : ℝ),
        p.Prime → (∀ i, old i ≠ p) → Real.exp 1 ≤ B →
        (∀ i, |(c i : ℝ)| ≤ B) → |(d : ℝ)| ≤ B → d ≠ 0 →
        indexedRationalLogForm old p c d ≠ 0 →
        Real.exp (-C * Real.log (p : ℝ) * Real.log B) ≤
          |indexedRationalLogForm old p c d| := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro p c d B hp _hpfresh hB _hc _hd hdne _hform
  have hformEq : indexedRationalLogForm old p c d =
      (d : ℝ) * Real.log (p : ℝ) := by
    simp [indexedRationalLogForm]
  have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpPos : 0 < (p : ℝ) := lt_of_lt_of_le (by norm_num) hpTwo
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hpTwo)
  have hlogB : 1 ≤ Real.log B := by
    have hBpos : 0 < B := (Real.exp_pos 1).trans_le hB
    exact (Real.le_log_iff_exp_le hBpos).2 hB
  have hexponent :
      -(1 : ℝ) * Real.log (p : ℝ) * Real.log B ≤
        -Real.log (p : ℝ) := by
    nlinarith
  have hexpInv : Real.exp (-Real.log (p : ℝ)) = ((p : ℝ)⁻¹) := by
    rw [Real.exp_neg, Real.exp_log hpPos]
  have hinvHalf : ((p : ℝ)⁻¹) ≤ 1 / 2 := by
    simpa only [one_div] using
      (inv_anti₀ (by norm_num : (0 : ℝ) < 2) hpTwo)
  have hhalfLog : (1 / 2 : ℝ) ≤ Real.log (p : ℝ) := by
    have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
      Real.log_two_gt_d9.trans' (by norm_num)
    exact hlogTwo.le.trans (Real.log_le_log (by norm_num) hpTwo)
  have hdAbs : (1 : ℝ) ≤ |(d : ℝ)| := by
    exact_mod_cast Int.one_le_abs hdne
  rw [hformEq, abs_mul, abs_of_pos hlogp]
  calc
    Real.exp (-(1 : ℝ) * Real.log (p : ℝ) * Real.log B)
        ≤ Real.exp (-Real.log (p : ℝ)) := Real.exp_le_exp.mpr hexponent
    _ = ((p : ℝ)⁻¹) := hexpInv
    _ ≤ 1 / 2 := hinvHalf
    _ ≤ Real.log (p : ℝ) := hhalfLog
    _ ≤ |(d : ℝ)| * Real.log (p : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hdAbs hlogp.le

/-! ## Reduction of the source theorem to a nonempty old family -/

/-- The only genuinely Baker-theoretic source obligation.  A nonempty old
family means that after adjoining the distinguished prime there are at least
two logarithms, exactly the range of the van der Poorten--Loxton theorem. -/
def HasNonemptyIntegralCutoffRationalPrimeLogBounds : Prop :=
  ∀ (ι : Type u) [Fintype ι] [Nonempty ι] (a : ι → ℕ),
    (∀ i, (a i).Prime) → Function.Injective a →
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (N : ℕ),
        p.Prime → (∀ i, a i ≠ p) → Real.exp 2 ≤ (N : ℝ) →
        (∀ i, (c i).natAbs ≤ N) → d.natAbs ≤ N → d ≠ 0 →
        indexedRationalLogForm a p c d ≠ 0 →
        Real.exp (-C * Real.log (p : ℝ) * Real.log (N : ℝ)) ≤
          |indexedRationalLogForm a p c d|

/-- Contradiction-shaped formulation produced directly by the final
zero-count argument: a nonzero form cannot be *strictly smaller* than the
claimed source threshold. -/
def HasNonemptyVDPLSmallFormContradiction : Prop :=
  ∀ (ι : Type u) [Fintype ι] [Nonempty ι] (a : ι → ℕ),
    (∀ i, (a i).Prime) → Function.Injective a →
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (N : ℕ),
        p.Prime → (∀ i, a i ≠ p) → Real.exp 2 ≤ (N : ℝ) →
        (∀ i, (c i).natAbs ≤ N) → d.natAbs ≤ N → d ≠ 0 →
        indexedRationalLogForm a p c d ≠ 0 →
        ¬ |indexedRationalLogForm a p c d| <
          Real.exp (-C * Real.log (p : ℝ) * Real.log (N : ℝ))

/-- The source's strict-smallness contradiction is exactly the required
nonstrict lower bound. -/
theorem nonemptyIntegralCutoff_bounds_of_smallFormContradiction
    (hsource : HasNonemptyVDPLSmallFormContradiction.{u}) :
    HasNonemptyIntegralCutoffRationalPrimeLogBounds.{u} := by
  intro ι _ _ a ha hinj
  obtain ⟨C, hC, hsmall⟩ := hsource ι a ha hinj
  refine ⟨C, hC, ?_⟩
  intro p c d N hp hpFresh hN hc hd hdne hform
  exact not_lt.mp (hsmall c d N hp hpFresh hN hc hd hdne hform)

/-- Integral-cutoff version of the empty-family argument. -/
theorem integralCutoff_rational_prime_log_lower_bound_isEmpty
    {ι : Type u} [Fintype ι] [IsEmpty ι]
    (old : ι → ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (N : ℕ),
        p.Prime → (∀ i, old i ≠ p) → Real.exp 2 ≤ (N : ℝ) →
        (∀ i, (c i).natAbs ≤ N) → d.natAbs ≤ N → d ≠ 0 →
        indexedRationalLogForm old p c d ≠ 0 →
        Real.exp (-C * Real.log (p : ℝ) * Real.log (N : ℝ)) ≤
          |indexedRationalLogForm old p c d| := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    uniform_rational_prime_log_lower_bound_isEmpty old
  refine ⟨C, hC, ?_⟩
  intro p c d N hp hpFresh hN _hc hd hdne hform
  have hNexp : Real.exp 1 ≤ (N : ℝ) := by
    exact (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hN
  have hcReal : ∀ i, |(c i : ℝ)| ≤ (N : ℝ) := by
    intro i
    exact isEmptyElim i
  have hdReal : |(d : ℝ)| ≤ (N : ℝ) := by
    have hdcast : (d.natAbs : ℝ) ≤ (N : ℝ) := by exact_mod_cast hd
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hdcast
  exact hbound c d (N : ℝ) hp hpFresh hNexp hcReal hdReal hdne hform

/-- It suffices to prove the source theorem for nonempty old families.  The
empty case is discharged by the preceding elementary estimate. -/
theorem integralCutoff_bounds_of_nonempty
    (hsource : HasNonemptyIntegralCutoffRationalPrimeLogBounds.{u}) :
    HasIntegralCutoffRationalPrimeLogBounds.{u} := by
  intro ι _ a ha hinj
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      let _ : IsEmpty ι := hempty
      exact integralCutoff_rational_prime_log_lower_bound_isEmpty a
  | inr hnonempty =>
      let _ : Nonempty ι := hnonempty
      exact hsource ι a ha hinj

/-- Complete dependence-preserving assembly: once the source theorem is
proved for a nonempty old family, all coefficient normalization and the
empty-family boundary case are internal. -/
theorem uniform_bounds_of_nonemptyIntegralCutoff
    (hsource : HasNonemptyIntegralCutoffRationalPrimeLogBounds.{u}) :
    HasUniformRationalPrimeLogBounds.{u} :=
  uniform_rational_prime_log_lower_bound_of_integralCutoff
    (integralCutoff_bounds_of_nonempty hsource)

/-- Final assembly in the logical shape of the source proof. -/
theorem uniform_bounds_of_vdplSmallFormContradiction
    (hsource : HasNonemptyVDPLSmallFormContradiction.{u}) :
    HasUniformRationalPrimeLogBounds.{u} :=
  uniform_bounds_of_nonemptyIntegralCutoff
    (nonemptyIntegralCutoff_bounds_of_smallFormContradiction hsource)

/-!
The exact remaining local goal for the unconditional theorem is therefore
`HasNonemptyVDPLSmallFormContradiction`.  Its proof must be assembled from the
following layers, with no weakening of their quantitative dependence:

* the **sharp** Lemma 1 denominator
  `q^(2*h*lambda) * Nat.lcmUpto h ^ m` (never the nonsharp
  `Nat.lcmUpto h ^ (h*lambda)` bound);
* `BakerAuxiliary.exists_vdpl_auxiliary_coefficients_height_shape`;
* the analytic/Liouville alternatives in `BakerLemma3`;
* the quantitative integral and rational extrapolation certificates;
* exact thirteenth-root monomial linear independence from `RadicalBasis`;
* the level induction and `ShiftedZeroCount` contradiction.

The current source scaffolding is not yet a proof of this goal.  Before it can
be connected here, it must use strict height majorants such as
`max (exp (exp 1)) (prime + 1)` (the corrigendum requires
`|log alpha| < log A`), the
shift `z + lambda_-1`, the factor `alpha^(lambda*l)`, and the source parameter
`L_n`.  On the rational grid it must use the separate checked sharp bridge
`SharpDeltaIndependent.exists_int_cleared_poweredDeltaHasse_lcm`, whose factor
is exactly `q^(2*h*lambda) * lcmUpto(h)^m`; the integer-valued-polynomial
theorem alone does not supply the `q` factor.

At level `J`, only the Delta factor is evaluated at `z / q^J`; the
exponential monomial remains `exp (rate * z)`.  In particular, evaluation at
`z = l / q` exposes the thirteenth-root monomials used by radical descent.

The initial side lengths must also retain all source factors:
`L_0 + 1 = floor ((1/8) * k^(1-sigma) * Omega)` and
`L_j = floor ((8*n)⁻¹ * k^(1-sigma) * Omega * log OmegaOld / log A_j)`.
At level `J` the full derivative budget is
`floor (q⁻ᴶ * k * Omega * log OmegaOld)`; the final elimination argument uses
the source's `7/8` residual multiplicity.  Omitting any of these factors would
not instantiate the local goal above.

In particular, none of `C`, the enlarged source parameter, or any
interpolation constant may depend on `p`, `c`, `d`, or `N`; the varying new
height must remain a visible single factor until
`VDPLParameters.log_newHeight_le_heightConstant_mul_log_newPrime` is applied.
-/

end Erdos240.RationalPrimeBaker

#print axioms
  Erdos240.RationalPrimeBaker.uniform_rational_prime_log_lower_bound_of_integralCutoff_apply
#print axioms Erdos240.RationalPrimeBaker.uniform_rational_prime_log_lower_bound_isEmpty
#print axioms Erdos240.RationalPrimeBaker.integralCutoff_bounds_of_nonempty
#print axioms Erdos240.RationalPrimeBaker.uniform_bounds_of_nonemptyIntegralCutoff
#print axioms Erdos240.RationalPrimeBaker.uniform_bounds_of_vdplSmallFormContradiction
