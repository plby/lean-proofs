/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.ZMod

/-!
# Finite additive-character orthogonality

This file records the exact finite identities used when the high-moment
argument of BNPZ Lemma 9.2 is opened.  Keeping these identities separate
from the later dyadic and divisor bookkeeping makes clear that no analytic
estimate is hidden in the character-orthogonality step.
-/

namespace Erdos387

open scoped BigOperators ComplexConjugate

namespace AdditiveOrthogonality

/-- The complete standard additive-character sum over `ZMod q`. -/
theorem sum_stdAddChar_mul (q : ℕ) [NeZero q] (x : ZMod q) :
    ∑ u : ZMod q, ZMod.stdAddChar (u * x) =
      if x = 0 then (q : ℂ) else 0 := by
  simpa using
    (AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar q))

/-- Orthogonality in the form used after opening a squared exponential
sum: the complete frequency sum vanishes unless the two phases agree. -/
theorem sum_stdAddChar_mul_conj (q : ℕ) [NeZero q]
    (x y : ZMod q) :
    ∑ u : ZMod q,
        ZMod.stdAddChar (u * x) *
          conj (ZMod.stdAddChar (u * y)) =
      if x = y then (q : ℂ) else 0 := by
  calc
    ∑ u : ZMod q,
        ZMod.stdAddChar (u * x) *
          conj (ZMod.stdAddChar (u * y)) =
        ∑ u : ZMod q,
          ZMod.stdAddChar (u * (x - y)) := by
            apply Finset.sum_congr rfl
            intro u _hu
            rw [← AddChar.map_neg_eq_conj]
            rw [← AddChar.map_add_eq_mul]
            congr 1
            ring
    _ = if x - y = 0 then (q : ℂ) else 0 :=
      sum_stdAddChar_mul q (x - y)
    _ = if x = y then (q : ℂ) else 0 := by
      simp only [sub_eq_zero]

/-- A version without conjugation, useful when one phase has already been
negated algebraically. -/
theorem sum_stdAddChar_mul_sub (q : ℕ) [NeZero q]
    (x y : ZMod q) :
    ∑ u : ZMod q, ZMod.stdAddChar (u * (x - y)) =
      if x = y then (q : ℂ) else 0 := by
  simpa [sub_eq_zero] using sum_stdAddChar_mul q (x - y)

section Fibres

variable {q : ℕ}
variable {A : Type*}

/-- The fibre of a finite family of residues over a residue `u`. -/
noncomputable def residueFiber (s : Finset A) (phase : A → ZMod q)
    (u : ZMod q) : Finset A := by
  classical
  exact s.filter fun a => phase a = u

/-- Ordered pairs from `s` whose phases agree modulo `q`. -/
noncomputable def equalPhasePairs (s : Finset A) (phase : A → ZMod q) :
    Finset (A × A) := by
  classical
  exact (s ×ˢ s).filter fun ab => phase ab.1 = phase ab.2

/-- Equal-phase pairs are partitioned by their common residue.  This is the
finite counting identity behind the `∑ |ν(u)|²` term in BNPZ Lemma 9.2. -/
theorem sum_residueFiber_card_sq
    [NeZero q]
    (s : Finset A) (phase : A → ZMod q) :
    (∑ u : ZMod q, (residueFiber s phase u).card ^ 2) =
      (equalPhasePairs s phase).card := by
  classical
  let commonPhase : A × A → ZMod q := fun ab => phase ab.1
  have hmaps :
      (((equalPhasePairs s phase : Finset (A × A)) : Set (A × A))).MapsTo
        commonPhase ((Finset.univ : Finset (ZMod q)) : Set (ZMod q)) := by
    intro ab hab
    exact Finset.mem_univ _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro u _hu
  have heq :
      (equalPhasePairs s phase).filter (fun ab => commonPhase ab = u) =
        residueFiber s phase u ×ˢ residueFiber s phase u := by
    ext ab
    simp only [equalPhasePairs, residueFiber, commonPhase,
      Finset.mem_filter, Finset.mem_product]
    aesop
  rw [heq, Finset.card_product]
  simp [pow_two]

/-- A coefficient sum restricted to one residue fibre. -/
noncomputable def residueFiberSum
    (s : Finset A) (phase : A → ZMod q) (weight : A → ℂ)
    (u : ZMod q) : ℂ :=
  ∑ a ∈ residueFiber s phase u, weight a

/-- Regroup a weighted finite sum by the fibres of its phase. -/
theorem sum_residueFiberSum_mul
    [NeZero q]
    (s : Finset A) (phase : A → ZMod q) (weight : A → ℂ)
    (g : ZMod q → ℂ) :
    (∑ u : ZMod q, residueFiberSum s phase weight u * g u) =
      ∑ a ∈ s, weight a * g (phase a) := by
  classical
  calc
    (∑ u : ZMod q, residueFiberSum s phase weight u * g u) =
        ∑ u : ZMod q, ∑ a ∈ s with phase a = u, weight a * g u := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [residueFiberSum, residueFiber, Finset.sum_mul]
    _ = ∑ u : ZMod q, ∑ a ∈ s with phase a = u,
          weight a * g (phase a) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a ∈ s, weight a * g (phase a) :=
      Finset.sum_fiberwise s phase (fun a => weight a * g (phase a))

/-- Unnormalized finite Fourier transform using the standard additive
character of `ZMod q`. -/
noncomputable def stdAddCharFourierSum
    [NeZero q] (F : ZMod q → ℂ) (u : ZMod q) : ℂ :=
  ∑ v : ZMod q, F v * ZMod.stdAddChar (u * v)

/-- Fourier inversion for the unnormalized standard additive-character
transform.  The sign convention matches the interval Fourier coefficients
used in completion arguments. -/
theorem sum_stdAddChar_neg_mul_fourierSum
    [NeZero q] (F : ZMod q → ℂ) (x : ZMod q) :
    ∑ u : ZMod q,
        ZMod.stdAddChar (-(u * x)) * stdAddCharFourierSum F u =
      (q : ℂ) * F x := by
  classical
  simp_rw [stdAddCharFourierSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ v : ZMod q, ∑ u : ZMod q,
        ZMod.stdAddChar (-(u * x)) *
          (F v * ZMod.stdAddChar (u * v)) =
      ∑ v : ZMod q, F v *
        ∑ u : ZMod q, ZMod.stdAddChar (u * (v - x)) := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      calc
        ZMod.stdAddChar (-(u * x)) *
            (F v * ZMod.stdAddChar (u * v)) =
          F v * (ZMod.stdAddChar (-(u * x)) *
            ZMod.stdAddChar (u * v)) := by ring
        _ = F v * ZMod.stdAddChar (-(u * x) + u * v) := by
          rw [AddChar.map_add_eq_mul]
        _ = F v * ZMod.stdAddChar (u * (v - x)) := by
          congr 2
          ring
    _ = ∑ v : ZMod q, F v *
        (if v - x = 0 then (q : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [sum_stdAddChar_mul]
    _ = (q : ℂ) * F x := by
      simp only [sub_eq_zero]
      simp
      ring

/-- Complex-algebra form of Parseval for the unnormalized transform. -/
theorem sum_conj_stdAddCharFourierSum_mul_self
    [NeZero q] (F : ZMod q → ℂ) :
    (∑ u : ZMod q,
        conj (stdAddCharFourierSum F u) * stdAddCharFourierSum F u) =
      (q : ℂ) * ∑ v : ZMod q, conj (F v) * F v := by
  classical
  calc
    (∑ u : ZMod q,
        conj (stdAddCharFourierSum F u) * stdAddCharFourierSum F u) =
        ∑ u : ZMod q, ∑ v : ZMod q, ∑ w : ZMod q,
          (conj (F v) * conj (ZMod.stdAddChar (u * v))) *
            (F w * ZMod.stdAddChar (u * w)) := by
      unfold stdAddCharFourierSum
      simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ v : ZMod q, ∑ w : ZMod q, ∑ u : ZMod q,
          (conj (F v) * conj (ZMod.stdAddChar (u * v))) *
            (F w * ZMod.stdAddChar (u * w)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Finset.sum_comm]
    _ = ∑ v : ZMod q, ∑ w : ZMod q,
          (conj (F v) * F w) *
            ∑ u : ZMod q,
              ZMod.stdAddChar (u * w) *
                conj (ZMod.stdAddChar (u * v)) := by
      apply Finset.sum_congr rfl
      intro v _hv
      apply Finset.sum_congr rfl
      intro w _hw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      ring
    _ = ∑ v : ZMod q, ∑ w : ZMod q,
          (conj (F v) * F w) *
            (if w = v then (q : ℂ) else 0) := by
      simp_rw [sum_stdAddChar_mul_conj]
    _ = ∑ v : ZMod q, (q : ℂ) * (conj (F v) * F v) := by
      apply Finset.sum_congr rfl
      intro v _hv
      simp
      ring
    _ = (q : ℂ) * ∑ v : ZMod q, conj (F v) * F v := by
      rw [Finset.mul_sum]

/-- Real norm-squared Parseval identity. -/
theorem sum_norm_stdAddCharFourierSum_sq
    [NeZero q] (F : ZMod q → ℂ) :
    (∑ u : ZMod q, ‖stdAddCharFourierSum F u‖ ^ 2) =
      q * ∑ v : ZMod q, ‖F v‖ ^ 2 := by
  have hnorm (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = conj z * z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  have hnorm' (z : ℂ) : (‖z‖ : ℂ) ^ 2 = conj z * z := by
    rw [← Complex.ofReal_pow]
    exact hnorm z
  apply Complex.ofReal_injective
  push_cast
  simp_rw [hnorm']
  exact sum_conj_stdAddCharFourierSum_mul_self F

/-- The weighted exponential sum whose coefficient sequence is indexed by
the finite family `s` and whose frequency is `u`. -/
noncomputable def characterSum
    [NeZero q]
    (s : Finset A) (phase : A → ZMod q) (weight : A → ℂ)
    (u : ZMod q) : ℂ :=
  ∑ a ∈ s, weight a * ZMod.stdAddChar (u * phase a)

/-- Grouping a character sum by its phase fibres identifies it with the
unnormalized Fourier transform of the fibre sums. -/
theorem stdAddCharFourierSum_residueFiberSum_eq_characterSum
    [NeZero q]
    (s : Finset A) (phase : A → ZMod q) (weight : A → ℂ)
    (u : ZMod q) :
    stdAddCharFourierSum (residueFiberSum s phase weight) u =
      characterSum s phase weight u := by
  simpa [stdAddCharFourierSum, characterSum] using
    sum_residueFiberSum_mul s phase weight
      (fun v => ZMod.stdAddChar (u * v))

/-- Parseval expressed directly for a weighted finite character sum. -/
theorem sum_norm_characterSum_sq_eq
    [NeZero q]
    (s : Finset A) (phase : A → ZMod q) (weight : A → ℂ) :
    (∑ u : ZMod q, ‖characterSum s phase weight u‖ ^ 2) =
      q * ∑ v : ZMod q, ‖residueFiberSum s phase weight v‖ ^ 2 := by
  simpa only [stdAddCharFourierSum_residueFiberSum_eq_characterSum] using
    sum_norm_stdAddCharFourierSum_sq (residueFiberSum s phase weight)

/-- If every coefficient is one-bounded, its fibrewise second moment is
bounded by the number of equal-phase ordered pairs.  This is the precise
finite inequality used to replace `∑_u |ν(u)|²` by a reciprocal-energy
count. -/
theorem sum_norm_residueFiberSum_sq_le
    [NeZero q]
    (s : Finset A) (phase : A → ZMod q) (weight : A → ℂ)
    (hweight : ∀ a ∈ s, ‖weight a‖ ≤ 1) :
    (∑ u : ZMod q, ‖residueFiberSum s phase weight u‖ ^ 2) ≤
      ((equalPhasePairs s phase).card : ℝ) := by
  calc
    (∑ u : ZMod q, ‖residueFiberSum s phase weight u‖ ^ 2) ≤
        ∑ u : ZMod q, ((residueFiber s phase u).card : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro u _hu
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      calc
        ‖residueFiberSum s phase weight u‖ ≤
            ∑ a ∈ residueFiber s phase u, ‖weight a‖ := by
          exact norm_sum_le _ _
        _ ≤ ∑ _a ∈ residueFiber s phase u, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          apply hweight a
          exact (Finset.mem_filter.mp ha).1
        _ = ((residueFiber s phase u).card : ℝ) := by simp
    _ = ((∑ u : ZMod q, (residueFiber s phase u).card ^ 2 : ℕ) : ℝ) := by
      push_cast
      rfl
    _ = ((equalPhasePairs s phase).card : ℝ) := by
      rw [sum_residueFiber_card_sq]

/-- A one-bounded weighted character sum has complete second moment at
most the modulus times the number of equal-phase ordered pairs. -/
theorem sum_norm_characterSum_sq_le
    [NeZero q]
    (s : Finset A) (phase : A → ZMod q) (weight : A → ℂ)
    (hweight : ∀ a ∈ s, ‖weight a‖ ≤ 1) :
    (∑ u : ZMod q, ‖characterSum s phase weight u‖ ^ 2) ≤
      (q * (equalPhasePairs s phase).card : ℕ) := by
  rw [sum_norm_characterSum_sq_eq]
  have h := mul_le_mul_of_nonneg_left
    (sum_norm_residueFiberSum_sq_le s phase weight hweight)
    (Nat.cast_nonneg q)
  exact_mod_cast h

/-- The equal-phase pair count is at most the square of the size of the
underlying family. -/
theorem equalPhasePairs_card_le_sq
    (s : Finset A) (phase : A → ZMod q) :
    (equalPhasePairs s phase).card ≤ s.card ^ 2 := by
  classical
  calc
    (equalPhasePairs s phase).card ≤ (s ×ˢ s).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = s.card ^ 2 := by simp [pow_two]

end Fibres

end AdditiveOrthogonality

end Erdos387
