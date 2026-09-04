import ErdosProblems.Erdos67.Pretentious
import ErdosProblems.Erdos67.PrimeEstimates
import ErdosProblems.Erdos438.Fourier
import Mathlib.Combinatorics.Additive.Energy

/-!
# Fourth moments of prime exponential sums

This file isolates the elementary finite-Fourier input needed in the prime
averaging part of the logarithmically averaged Elliott argument.  The central
identity is exact: the fourth moment of an unnormalised exponential sum is the
modulus times the number of ordered additive quadruples.  A no-wrap hypothesis
then turns congruence modulo the Fourier modulus into equality in `ℕ`.

The resulting estimate

`sum_t |sum_{p ≤ X} e_T(tp)|^4 ≤ T * pi(X)^3`

is deliberately elementary.  It is not the deeper restriction estimate used
to obtain sharp logarithmic savings, but it provides the fully checked
diagonal/additive-energy layer on top of which that analytic estimate must be
built.
-/

open scoped BigOperators ComplexConjugate Combinatorics.Additive
open Filter

namespace Erdos67

noncomputable section

/-! ## Ordered additive quadruples -/

/-- Ordered quadruples `((a₁,a₂),(b₁,b₂))` from `s` satisfying
`a₁ + b₁ = a₂ + b₂`.  This ordering agrees with `Finset.addEnergy`. -/
def additiveQuadruples (s : Finset ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((s ×ˢ s) ×ˢ (s ×ˢ s)).filter fun x ↦
    x.1.1 + x.2.1 = x.1.2 + x.2.2

@[simp]
theorem mem_additiveQuadruples {s : Finset ℕ} {x : (ℕ × ℕ) × (ℕ × ℕ)} :
    x ∈ additiveQuadruples s ↔
      x.1.1 ∈ s ∧ x.1.2 ∈ s ∧ x.2.1 ∈ s ∧ x.2.2 ∈ s ∧
        x.1.1 + x.2.1 = x.1.2 + x.2.2 := by
  simp only [additiveQuadruples, Finset.mem_filter, Finset.mem_product]
  aesop

/-- The explicit quadruple set has cardinality equal to Mathlib's additive
energy. -/
theorem card_additiveQuadruples (s : Finset ℕ) :
    (additiveQuadruples s).card = Finset.addEnergy s s := by
  rfl

/-- Dropping the fourth coordinate is injective on additive quadruples: the
additive equation recovers that coordinate by cancellation. -/
theorem additiveQuadruples_card_le_cube (s : Finset ℕ) :
    (additiveQuadruples s).card ≤ s.card ^ 3 := by
  let target : Finset ((ℕ × ℕ) × ℕ) := (s ×ˢ s) ×ˢ s
  let dropFourth : ((ℕ × ℕ) × (ℕ × ℕ)) → ((ℕ × ℕ) × ℕ) :=
    fun x ↦ (x.1, x.2.1)
  have hmaps : Set.MapsTo dropFourth (additiveQuadruples s) target := by
    intro x hx
    have hx' : x ∈ additiveQuadruples s := hx
    rw [mem_additiveQuadruples] at hx'
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hx'.1, hx'.2.1⟩, hx'.2.2.1⟩
  have hinj : Set.InjOn dropFourth (additiveQuadruples s) := by
    intro x hx y hy hxy
    have hx' : x ∈ additiveQuadruples s := hx
    have hy' : y ∈ additiveQuadruples s := hy
    rw [mem_additiveQuadruples] at hx' hy'
    change (x.1, x.2.1) = (y.1, y.2.1) at hxy
    have hfirst : x.1 = y.1 :=
      congrArg (fun z : (ℕ × ℕ) × ℕ ↦ z.1) hxy
    have hthird : x.2.1 = y.2.1 :=
      congrArg (fun z : (ℕ × ℕ) × ℕ ↦ z.2) hxy
    have hfourth : x.2.2 = y.2.2 := by
      have hxsum := hx'.2.2.2.2
      have hysum := hy'.2.2.2.2
      rw [hfirst, hthird] at hxsum
      exact Nat.add_left_cancel (hxsum.symm.trans hysum)
    exact Prod.ext hfirst (Prod.ext hthird hfourth)
  calc
    (additiveQuadruples s).card ≤ target.card :=
      Finset.card_le_card_of_injOn dropFourth hmaps hinj
    _ = s.card ^ 3 := by simp [target, pow_succ]

/-- The diagonal quadruples give the standard lower bound on additive energy. -/
theorem card_sq_le_additiveQuadruples_card (s : Finset ℕ) :
    s.card ^ 2 ≤ (additiveQuadruples s).card := by
  rw [card_additiveQuadruples]
  exact Finset.le_addEnergy_self

/-! ## Modular quadruples and no wrap-around -/

/-- Ordered quadruples whose two sums agree modulo `T`. -/
def modularAdditiveQuadruples (T : ℕ) (s : Finset ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((s ×ˢ s) ×ˢ (s ×ˢ s)).filter fun x ↦
    ((x.1.1 + x.2.1 : ℕ) : ZMod T) =
      ((x.1.2 + x.2.2 : ℕ) : ZMod T)

@[simp]
theorem mem_modularAdditiveQuadruples {T : ℕ} {s : Finset ℕ}
    {x : (ℕ × ℕ) × (ℕ × ℕ)} :
    x ∈ modularAdditiveQuadruples T s ↔
      x.1.1 ∈ s ∧ x.1.2 ∈ s ∧ x.2.1 ∈ s ∧ x.2.2 ∈ s ∧
        ((x.1.1 + x.2.1 : ℕ) : ZMod T) =
          ((x.1.2 + x.2.2 : ℕ) : ZMod T) := by
  simp only [modularAdditiveQuadruples, Finset.mem_filter, Finset.mem_product]
  aesop

/-- If every element of `s` is at most `X` and `2*X < T`, equality modulo
`T` between two pair sums is literal equality. -/
theorem modularAdditiveQuadruples_eq_of_noWrap {T X : ℕ} {s : Finset ℕ}
    (hs : ∀ x ∈ s, x ≤ X) (hT : 2 * X < T) :
    modularAdditiveQuadruples T s = additiveQuadruples s := by
  ext x
  rw [mem_modularAdditiveQuadruples, mem_additiveQuadruples]
  constructor
  · rintro ⟨hx₁, hx₂, hx₃, hx₄, hmod⟩
    refine ⟨hx₁, hx₂, hx₃, hx₄, ?_⟩
    rw [ZMod.natCast_eq_natCast_iff] at hmod
    have hx₁X := hs x.1.1 hx₁
    have hx₂X := hs x.1.2 hx₂
    have hx₃X := hs x.2.1 hx₃
    have hx₄X := hs x.2.2 hx₄
    have hleft : x.1.1 + x.2.1 < T := by
      omega
    have hright : x.1.2 + x.2.2 < T := by
      omega
    exact hmod.eq_of_lt_of_lt hleft hright
  · rintro ⟨hx₁, hx₂, hx₃, hx₄, hsum⟩
    exact ⟨hx₁, hx₂, hx₃, hx₄, congrArg (fun n : ℕ ↦ (n : ZMod T)) hsum⟩

/-! ## Exact fourth-moment expansion -/

/-- The unnormalised exponential sum over a finite set, with frequencies
represented by the concrete interval `[0,T)`. -/
def exponentialSum (T : ℕ) (s : Finset ℕ) (t : ℤ) : ℂ :=
  Erdos438.Fourier.coefficient T s t

@[simp]
theorem exponentialSum_zero (T : ℕ) (s : Finset ℕ) :
    exponentialSum T s 0 = (s.card : ℂ) := by
  exact Erdos438.Fourier.coefficient_zero T s

/-- Pointwise expansion of a fourth power as a sum over ordered quadruples. -/
theorem norm_four_exponentialSum_eq_quadruple_sum (T : ℕ) (s : Finset ℕ) (t : ℤ) :
    (‖exponentialSum T s t‖ : ℂ) ^ 4 =
      ∑ x ∈ ((s ×ˢ s) ×ˢ (s ×ˢ s)),
        Erdos438.Fourier.phase T t
          (((x.1.2 : ℤ) + x.2.2) - x.1.1 - x.2.1) := by
  classical
  have hnorm (z : ℂ) : (‖z‖ : ℂ) ^ 4 = z * conj z * z * conj z := by
    have hsq : ((‖z‖ : ℂ) ^ 2) = conj z * z := by
      rw [← Complex.ofReal_pow, Complex.sq_norm,
        Complex.normSq_eq_conj_mul_self]
    rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul]
    rw [hsq]
    ring
  rw [hnorm]
  simp only [exponentialSum, Erdos438.Fourier.coefficient,
    map_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_product]
  simp_rw [Erdos438.Fourier.conj_phase]
  apply Finset.sum_congr rfl
  intro a₁ ha₁
  apply Finset.sum_congr rfl
  intro a₂ ha₂
  apply Finset.sum_congr rfl
  intro b₁ hb₁
  apply Finset.sum_congr rfl
  intro b₂ hb₂
  rw [← Erdos438.Fourier.phase_add_right,
    ← Erdos438.Fourier.phase_add_right,
    ← Erdos438.Fourier.phase_add_right]
  congr 1
  ring

/-- Exact fourth moment: character orthogonality counts congruent pair sums. -/
theorem fourth_moment_exponentialSum_mod (T : ℕ) [NeZero T] (s : Finset ℕ) :
    ∑ t ∈ Finset.range T, ‖exponentialSum T s (t : ℤ)‖ ^ 4 =
      T * (modularAdditiveQuadruples T s).card := by
  classical
  apply Complex.ofReal_injective
  push_cast
  simp_rw [norm_four_exponentialSum_eq_quadruple_sum]
  rw [Finset.sum_comm]
  calc
    (∑ x ∈ (s ×ˢ s) ×ˢ (s ×ˢ s),
        ∑ t ∈ Finset.range T,
          Erdos438.Fourier.phase T (t : ℤ)
            (((x.1.2 : ℤ) + x.2.2) - x.1.1 - x.2.1)) =
        ∑ x ∈ (s ×ˢ s) ×ˢ (s ×ˢ s),
          if ((x.1.1 + x.2.1 : ℕ) : ZMod T) =
              ((x.1.2 + x.2.2 : ℕ) : ZMod T) then
            (T : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Erdos438.Fourier.phase_orthogonality]
      have hcond :
          (((((x.1.2 : ℤ) + x.2.2) - x.1.1 - x.2.1 : ℤ) : ZMod T) = 0) ↔
            ((x.1.1 + x.2.1 : ℕ) : ZMod T) =
              ((x.1.2 + x.2.2 : ℕ) : ZMod T) := by
        push_cast
        constructor
        · intro h
          linear_combination -h
        · intro h
          linear_combination -h
      rw [if_congr hcond rfl rfl]
    _ = (T : ℂ) * ((modularAdditiveQuadruples T s).card : ℂ) := by
      rw [modularAdditiveQuadruples, Finset.natCast_card_filter,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp

/-- No-wrap form of the exact fourth moment. -/
theorem fourth_moment_exponentialSum (T X : ℕ) [NeZero T] (s : Finset ℕ)
    (hs : ∀ x ∈ s, x ≤ X) (hT : 2 * X < T) :
    ∑ t ∈ Finset.range T, ‖exponentialSum T s (t : ℤ)‖ ^ 4 =
      T * (additiveQuadruples s).card := by
  rw [fourth_moment_exponentialSum_mod,
    modularAdditiveQuadruples_eq_of_noWrap hs hT]

/-- Elementary fourth-moment restriction bound for an arbitrary finite set
contained in `[0,X]`. -/
theorem fourth_moment_exponentialSum_le (T X : ℕ) [NeZero T] (s : Finset ℕ)
    (hs : ∀ x ∈ s, x ≤ X) (hT : 2 * X < T) :
    ∑ t ∈ Finset.range T, ‖exponentialSum T s (t : ℤ)‖ ^ 4 ≤
      T * s.card ^ 3 := by
  rw [fourth_moment_exponentialSum T X s hs hT]
  exact_mod_cast Nat.mul_le_mul_left T (additiveQuadruples_card_le_cube s)

/-! ## Weighted fourth moments -/

/-- The unnormalised transform of coefficients supported on `s`. -/
def weightedExponentialSum (T : ℕ) (s : Finset ℕ) (w : ℕ → ℂ) (t : ℤ) : ℂ :=
  ∑ x ∈ s, w x * Erdos438.Fourier.phase T t x

/-- The coefficient product attached to an ordered additive quadruple. -/
def quadrupleWeight (w : ℕ → ℂ) (x : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  w x.2.2 * conj (w x.2.1) * w x.1.2 * conj (w x.1.1)

/-- Pointwise fourth-power expansion for a weighted exponential sum. -/
theorem norm_four_weightedExponentialSum_eq_quadruple_sum
    (T : ℕ) (s : Finset ℕ) (w : ℕ → ℂ) (t : ℤ) :
    (‖weightedExponentialSum T s w t‖ : ℂ) ^ 4 =
      ∑ x ∈ ((s ×ˢ s) ×ˢ (s ×ˢ s)),
        quadrupleWeight w x *
          Erdos438.Fourier.phase T t
            (((x.1.2 : ℤ) + x.2.2) - x.1.1 - x.2.1) := by
  classical
  have hnorm (z : ℂ) : (‖z‖ : ℂ) ^ 4 = z * conj z * z * conj z := by
    have hsq : ((‖z‖ : ℂ) ^ 2) = conj z * z := by
      rw [← Complex.ofReal_pow, Complex.sq_norm,
        Complex.normSq_eq_conj_mul_self]
    rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul, hsq]
    ring
  rw [hnorm]
  simp only [weightedExponentialSum, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_product, Erdos438.Fourier.conj_phase]
  apply Finset.sum_congr rfl
  intro a₁ ha₁
  apply Finset.sum_congr rfl
  intro a₂ ha₂
  apply Finset.sum_congr rfl
  intro b₁ hb₁
  apply Finset.sum_congr rfl
  intro b₂ hb₂
  calc
    w b₂ * Erdos438.Fourier.phase T t b₂ *
          (conj (w b₁) * Erdos438.Fourier.phase T t (-b₁)) *
          (w a₂ * Erdos438.Fourier.phase T t a₂) *
          (conj (w a₁) * Erdos438.Fourier.phase T t (-a₁)) =
        quadrupleWeight w ((a₁, a₂), (b₁, b₂)) *
          (Erdos438.Fourier.phase T t b₂ *
            Erdos438.Fourier.phase T t (-b₁) *
            Erdos438.Fourier.phase T t a₂ *
            Erdos438.Fourier.phase T t (-a₁)) := by
      unfold quadrupleWeight
      ring
    _ = quadrupleWeight w ((a₁, a₂), (b₁, b₂)) *
        Erdos438.Fourier.phase T t
          (((a₂ : ℤ) + b₂) - a₁ - b₁) := by
      rw [← Erdos438.Fourier.phase_add_right,
        ← Erdos438.Fourier.phase_add_right,
        ← Erdos438.Fourier.phase_add_right]
      congr 2
      ring

/-- Exact weighted fourth moment.  Only modular additive quadruples survive
the frequency average. -/
theorem fourth_moment_weightedExponentialSum_mod
    (T : ℕ) [NeZero T] (s : Finset ℕ) (w : ℕ → ℂ) :
    ((∑ t ∈ Finset.range T,
      ‖weightedExponentialSum T s w (t : ℤ)‖ ^ 4 : ℝ) : ℂ) =
      (T : ℂ) *
        ∑ x ∈ modularAdditiveQuadruples T s, quadrupleWeight w x := by
  classical
  push_cast
  simp_rw [norm_four_weightedExponentialSum_eq_quadruple_sum]
  rw [Finset.sum_comm]
  calc
    (∑ x ∈ (s ×ˢ s) ×ˢ (s ×ˢ s),
        ∑ t ∈ Finset.range T,
          quadrupleWeight w x *
            Erdos438.Fourier.phase T (t : ℤ)
              (((x.1.2 : ℤ) + x.2.2) - x.1.1 - x.2.1)) =
        ∑ x ∈ (s ×ˢ s) ×ˢ (s ×ˢ s),
          if ((x.1.1 + x.2.1 : ℕ) : ZMod T) =
              ((x.1.2 + x.2.2 : ℕ) : ZMod T) then
            (T : ℂ) * quadrupleWeight w x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.mul_sum, Erdos438.Fourier.phase_orthogonality]
      have hcond :
          (((((x.1.2 : ℤ) + x.2.2) - x.1.1 - x.2.1 : ℤ) : ZMod T) = 0) ↔
            ((x.1.1 + x.2.1 : ℕ) : ZMod T) =
              ((x.1.2 + x.2.2 : ℕ) : ZMod T) := by
        push_cast
        constructor
        · intro h
          linear_combination -h
        · intro h
          linear_combination -h
      rw [if_congr hcond rfl rfl]
      split_ifs <;> ring
    _ = (T : ℂ) *
        ∑ x ∈ modularAdditiveQuadruples T s, quadrupleWeight w x := by
      rw [modularAdditiveQuadruples, ← Finset.sum_filter, Finset.mul_sum]

/-- Exact no-wrap weighted fourth moment, expressed by literal additive
quadruples in the integers. -/
theorem fourth_moment_weightedExponentialSum
    (T X : ℕ) [NeZero T] (s : Finset ℕ) (w : ℕ → ℂ)
    (hs : ∀ x ∈ s, x ≤ X) (hT : 2 * X < T) :
    ((∑ t ∈ Finset.range T,
      ‖weightedExponentialSum T s w (t : ℤ)‖ ^ 4 : ℝ) : ℂ) =
      (T : ℂ) * ∑ x ∈ additiveQuadruples s, quadrupleWeight w x := by
  rw [fourth_moment_weightedExponentialSum_mod,
    modularAdditiveQuadruples_eq_of_noWrap hs hT]

/-- A weighted restriction bound controlled by the additive energy of the
support. -/
theorem fourth_moment_weightedExponentialSum_le_energy
    (T X : ℕ) [NeZero T] (s : Finset ℕ) (w : ℕ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hw : ∀ x ∈ s, ‖w x‖ ≤ B)
    (hs : ∀ x ∈ s, x ≤ X) (hT : 2 * X < T) :
    ∑ t ∈ Finset.range T, ‖weightedExponentialSum T s w (t : ℤ)‖ ^ 4 ≤
      T * (additiveQuadruples s).card * B ^ 4 := by
  let M : ℝ := ∑ t ∈ Finset.range T,
    ‖weightedExponentialSum T s w (t : ℤ)‖ ^ 4
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ by positivity
  have hexact := fourth_moment_weightedExponentialSum T X s w hs hT
  have hweight (x : (ℕ × ℕ) × (ℕ × ℕ))
      (hx : x ∈ additiveQuadruples s) : ‖quadrupleWeight w x‖ ≤ B ^ 4 := by
    rw [mem_additiveQuadruples] at hx
    simp only [quadrupleWeight, norm_mul, Complex.norm_conj]
    have h₁ := hw x.1.1 hx.1
    have h₂ := hw x.1.2 hx.2.1
    have h₃ := hw x.2.1 hx.2.2.1
    have h₄ := hw x.2.2 hx.2.2.2.1
    calc
      ‖w x.2.2‖ * ‖w x.2.1‖ * ‖w x.1.2‖ * ‖w x.1.1‖ ≤
          B * B * B * B := by gcongr
      _ = B ^ 4 := by ring
  change M ≤ _
  calc
    M = ‖(M : ℂ)‖ := by simp [Real.norm_eq_abs, abs_of_nonneg hM]
    _ = ‖(T : ℂ) *
        ∑ x ∈ additiveQuadruples s, quadrupleWeight w x‖ := by rw [hexact]
    _ ≤ (T : ℝ) *
        ∑ x ∈ additiveQuadruples s, ‖quadrupleWeight w x‖ := by
      rw [norm_mul, Complex.norm_natCast]
      gcongr
      exact norm_sum_le _ _
    _ ≤ (T : ℝ) * ∑ _x ∈ additiveQuadruples s, B ^ 4 := by
      gcongr with x hx
      exact hweight x hx
    _ = T * (additiveQuadruples s).card * B ^ 4 := by
      simp
      ring

/-- Energy-free corollary obtained from `E(s) ≤ |s|³`. -/
theorem fourth_moment_weightedExponentialSum_le
    (T X : ℕ) [NeZero T] (s : Finset ℕ) (w : ℕ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hw : ∀ x ∈ s, ‖w x‖ ≤ B)
    (hs : ∀ x ∈ s, x ≤ X) (hT : 2 * X < T) :
    ∑ t ∈ Finset.range T, ‖weightedExponentialSum T s w (t : ℤ)‖ ^ 4 ≤
      T * s.card ^ 3 * B ^ 4 := by
  calc
    _ ≤ T * (additiveQuadruples s).card * B ^ 4 :=
      fourth_moment_weightedExponentialSum_le_energy T X s w B hB hw hs hT
    _ ≤ T * s.card ^ 3 * B ^ 4 := by
      gcongr
      exact_mod_cast additiveQuadruples_card_le_cube s

/-! ## Prime specialization -/

/-- The prime exponential sum `sum_{p ≤ X} e_T(tp)`. -/
def primeExponentialSum (T X : ℕ) (t : ℤ) : ℂ :=
  exponentialSum T (primesUpTo X) t

@[simp]
theorem primeExponentialSum_zero (T X : ℕ) :
    primeExponentialSum T X 0 = ((primesUpTo X).card : ℂ) := by
  exact exponentialSum_zero T (primesUpTo X)

/-- Exact `L⁴` expansion of the prime exponential sum as the ordered count of
prime solutions to `p₁ + p₃ = p₂ + p₄`. -/
theorem fourth_moment_primeExponentialSum (T X : ℕ) [NeZero T]
    (hT : 2 * X < T) :
    ∑ t ∈ Finset.range T, ‖primeExponentialSum T X (t : ℤ)‖ ^ 4 =
      T * (additiveQuadruples (primesUpTo X)).card := by
  apply fourth_moment_exponentialSum T X
  · intro p hp
    exact (mem_primesUpTo.mp hp).2
  · exact hT

/-- The elementary unweighted prime restriction estimate obtained by dropping
one coordinate from an additive prime quadruple. -/
theorem fourth_moment_primeExponentialSum_le (T X : ℕ) [NeZero T]
    (hT : 2 * X < T) :
    ∑ t ∈ Finset.range T, ‖primeExponentialSum T X (t : ℤ)‖ ^ 4 ≤
      T * (primesUpTo X).card ^ 3 := by
  apply fourth_moment_exponentialSum_le T X
  · intro p hp
    exact (mem_primesUpTo.mp hp).2
  · exact hT

/-- The prime prefix used here has the standard prime-counting cardinality. -/
theorem card_primesUpTo_eq_primeCounting (X : ℕ) :
    (primesUpTo X).card = Nat.primeCounting X := by
  classical
  simp [primesUpTo, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

/-- Weighted prime exponential sum. -/
def weightedPrimeExponentialSum
    (T X : ℕ) (w : ℕ → ℂ) (t : ℤ) : ℂ :=
  weightedExponentialSum T (primesUpTo X) w t

/-- Exact weighted prime fourth moment. -/
theorem fourth_moment_weightedPrimeExponentialSum
    (T X : ℕ) [NeZero T] (w : ℕ → ℂ) (hT : 2 * X < T) :
    ((∑ t ∈ Finset.range T,
      ‖weightedPrimeExponentialSum T X w (t : ℤ)‖ ^ 4 : ℝ) : ℂ) =
      (T : ℂ) *
        ∑ x ∈ additiveQuadruples (primesUpTo X), quadrupleWeight w x := by
  apply fourth_moment_weightedExponentialSum T X
  · intro p hp
    exact (mem_primesUpTo.mp hp).2
  · exact hT

/-- Weighted prime restriction estimate in terms of the exact additive prime
quadruple count. -/
theorem fourth_moment_weightedPrimeExponentialSum_le_energy
    (T X : ℕ) [NeZero T] (w : ℕ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hw : ∀ p ∈ primesUpTo X, ‖w p‖ ≤ B)
    (hT : 2 * X < T) :
    ∑ t ∈ Finset.range T,
        ‖weightedPrimeExponentialSum T X w (t : ℤ)‖ ^ 4 ≤
      T * (additiveQuadruples (primesUpTo X)).card * B ^ 4 := by
  apply fourth_moment_weightedExponentialSum_le_energy T X
  · exact hB
  · exact hw
  · intro p hp
    exact (mem_primesUpTo.mp hp).2
  · exact hT

/-- Weighted prime restriction estimate using only the number of primes. -/
theorem fourth_moment_weightedPrimeExponentialSum_le
    (T X : ℕ) [NeZero T] (w : ℕ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hw : ∀ p ∈ primesUpTo X, ‖w p‖ ≤ B)
    (hT : 2 * X < T) :
    ∑ t ∈ Finset.range T,
        ‖weightedPrimeExponentialSum T X w (t : ℤ)‖ ^ 4 ≤
      T * (primesUpTo X).card ^ 3 * B ^ 4 := by
  apply fourth_moment_weightedExponentialSum_le T X
  · exact hB
  · exact hw
  · intro p hp
    exact (mem_primesUpTo.mp hp).2
  · exact hT

/-! ## Prime-block restriction bounds

The prime averages in the entropy-decrement and Ramaré steps are supported
on intervals of primes rather than on prime prefixes.  The following
specializations package the general weighted estimate in exactly that form.
-/

/-- A weighted exponential sum over the half-open prime interval `(L,U]`. -/
def weightedPrimeBlockExponentialSum
    (T L U : ℕ) (w : ℕ → ℂ) (t : ℤ) : ℂ :=
  weightedExponentialSum T (primesBetween L U) w t

/-- Exact no-wrap fourth moment for a weighted prime block. -/
theorem fourth_moment_weightedPrimeBlockExponentialSum
    (T L U : ℕ) [NeZero T] (w : ℕ → ℂ) (hT : 2 * U < T) :
    ((∑ t ∈ Finset.range T,
      ‖weightedPrimeBlockExponentialSum T L U w (t : ℤ)‖ ^ 4 : ℝ) : ℂ) =
      (T : ℂ) *
        ∑ x ∈ additiveQuadruples (primesBetween L U), quadrupleWeight w x := by
  apply fourth_moment_weightedExponentialSum T U
  · intro p hp
    exact (mem_primesBetween.mp hp).2.2
  · exact hT

/-- Prime-block restriction estimate in terms of its exact additive energy. -/
theorem fourth_moment_weightedPrimeBlockExponentialSum_le_energy
    (T L U : ℕ) [NeZero T] (w : ℕ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hw : ∀ p ∈ primesBetween L U, ‖w p‖ ≤ B)
    (hT : 2 * U < T) :
    ∑ t ∈ Finset.range T,
        ‖weightedPrimeBlockExponentialSum T L U w (t : ℤ)‖ ^ 4 ≤
      T * (additiveQuadruples (primesBetween L U)).card * B ^ 4 := by
  apply fourth_moment_weightedExponentialSum_le_energy T U
  · exact hB
  · exact hw
  · intro p hp
    exact (mem_primesBetween.mp hp).2.2
  · exact hT

/-- Energy-free weighted restriction estimate for a prime block. -/
theorem fourth_moment_weightedPrimeBlockExponentialSum_le
    (T L U : ℕ) [NeZero T] (w : ℕ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hw : ∀ p ∈ primesBetween L U, ‖w p‖ ≤ B)
    (hT : 2 * U < T) :
    ∑ t ∈ Finset.range T,
        ‖weightedPrimeBlockExponentialSum T L U w (t : ℤ)‖ ^ 4 ≤
      T * (primesBetween L U).card ^ 3 * B ^ 4 := by
  apply fourth_moment_weightedExponentialSum_le T U
  · exact hB
  · exact hw
  · intro p hp
    exact (mem_primesBetween.mp hp).2.2
  · exact hT

/-- The prime-block exponential sum with the logarithmic-average weight
`p ↦ 1/p`. -/
def reciprocalPrimeBlockExponentialSum (T L U : ℕ) (t : ℤ) : ℂ :=
  weightedPrimeBlockExponentialSum T L U (fun p ↦ (p : ℂ)⁻¹) t

/-- Every reciprocal weight on `(L,U]` is bounded by `1/(L+1)`. -/
theorem norm_reciprocalPrime_le_succ_inv {L U p : ℕ}
    (hp : p ∈ primesBetween L U) :
    ‖((p : ℂ)⁻¹)‖ ≤ (((L + 1 : ℕ) : ℝ))⁻¹ := by
  have hpNat : L + 1 ≤ p := Nat.succ_le_iff.mpr (mem_primesBetween.mp hp).2.1
  have hpReal : ((L + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hpNat
  rw [norm_inv, Complex.norm_natCast]
  simpa [one_div] using
    (one_div_le_one_div_of_le (show (0 : ℝ) < (L + 1 : ℕ) by positivity) hpReal)

/-- An unconditional weighted restriction endpoint for the reciprocal prime
weights used in logarithmic prime averages. -/
theorem fourth_moment_reciprocalPrimeBlockExponentialSum_le
    (T L U : ℕ) [NeZero T] (hT : 2 * U < T) :
    ∑ t ∈ Finset.range T,
        ‖reciprocalPrimeBlockExponentialSum T L U (t : ℤ)‖ ^ 4 ≤
      T * (primesBetween L U).card ^ 3 *
        (((L + 1 : ℕ) : ℝ))⁻¹ ^ 4 := by
  apply fourth_moment_weightedPrimeBlockExponentialSum_le T L U
      (fun p ↦ (p : ℂ)⁻¹) (((L + 1 : ℕ) : ℝ))⁻¹
  · positivity
  · intro p hp
    exact norm_reciprocalPrime_le_succ_inv hp
  · exact hT

/-! ## PNT-sized prime restriction endpoints -/

/-- PNT-sized weighted restriction estimate, uniform in the lower endpoint of
the prime block. -/
theorem eventually_fourth_moment_weightedPrimeBlockExponentialSum_le_pnt
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ U : ℕ in atTop, ∀ L T : ℕ, 0 < T → 2 * U < T →
      ∀ w : ℕ → ℂ, (∀ p ∈ primesBetween L U, ‖w p‖ ≤ B) →
        ∑ t ∈ Finset.range T,
            ‖weightedPrimeBlockExponentialSum T L U w (t : ℤ)‖ ^ 4 ≤
          (T : ℝ) *
            ((11 / 10 : ℝ) * ((U : ℝ) / Real.log (U : ℝ))) ^ 3 * B ^ 4 := by
  filter_upwards [PrimeEstimates.eventually_primeCounting_tenth_bounds] with U hpi
  intro L T hTpos hnoWrap w hw
  let : NeZero T := ⟨hTpos.ne'⟩
  have hsubset : primesBetween L U ⊆ primesUpTo U := by
    intro p hp
    have hp' := mem_primesBetween.mp hp
    exact mem_primesUpTo.mpr ⟨hp'.1, hp'.2.2⟩
  have hcard : ((primesBetween L U).card : ℝ) ≤
      (11 / 10 : ℝ) * ((U : ℝ) / Real.log (U : ℝ)) := by
    calc
      ((primesBetween L U).card : ℝ) ≤ ((primesUpTo U).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ = (Nat.primeCounting U : ℝ) := by rw [card_primesUpTo_eq_primeCounting]
      _ ≤ (11 / 10 : ℝ) * ((U : ℝ) / Real.log (U : ℝ)) := hpi.2
  calc
    ∑ t ∈ Finset.range T,
        ‖weightedPrimeBlockExponentialSum T L U w (t : ℤ)‖ ^ 4 ≤
        (T : ℝ) * ((primesBetween L U).card : ℝ) ^ 3 * B ^ 4 :=
      fourth_moment_weightedPrimeBlockExponentialSum_le T L U w B hB hw hnoWrap
    _ ≤ (T : ℝ) *
        ((11 / 10 : ℝ) * ((U : ℝ) / Real.log (U : ℝ))) ^ 3 * B ^ 4 := by
      gcongr

/-- Explicit PNT-sized endpoint for reciprocal prime-block weights. -/
theorem eventually_fourth_moment_reciprocalPrimeBlockExponentialSum_le_pnt :
    ∀ᶠ U : ℕ in atTop, ∀ L T : ℕ, 0 < T → 2 * U < T →
      ∑ t ∈ Finset.range T,
          ‖reciprocalPrimeBlockExponentialSum T L U (t : ℤ)‖ ^ 4 ≤
        (T : ℝ) *
          ((11 / 10 : ℝ) * ((U : ℝ) / Real.log (U : ℝ))) ^ 3 *
            (((L + 1 : ℕ) : ℝ))⁻¹ ^ 4 := by
  filter_upwards [PrimeEstimates.eventually_primeCounting_tenth_bounds] with U hpi
  intro L T hTpos hnoWrap
  let : NeZero T := ⟨hTpos.ne'⟩
  have hsubset : primesBetween L U ⊆ primesUpTo U := by
    intro p hp
    have hp' := mem_primesBetween.mp hp
    exact mem_primesUpTo.mpr ⟨hp'.1, hp'.2.2⟩
  have hcard : ((primesBetween L U).card : ℝ) ≤
      (11 / 10 : ℝ) * ((U : ℝ) / Real.log (U : ℝ)) := by
    calc
      ((primesBetween L U).card : ℝ) ≤ ((primesUpTo U).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ = (Nat.primeCounting U : ℝ) := by rw [card_primesUpTo_eq_primeCounting]
      _ ≤ (11 / 10 : ℝ) * ((U : ℝ) / Real.log (U : ℝ)) := hpi.2
  calc
    ∑ t ∈ Finset.range T,
        ‖reciprocalPrimeBlockExponentialSum T L U (t : ℤ)‖ ^ 4 ≤
        (T : ℝ) * ((primesBetween L U).card : ℝ) ^ 3 *
          (((L + 1 : ℕ) : ℝ))⁻¹ ^ 4 :=
      fourth_moment_reciprocalPrimeBlockExponentialSum_le T L U hnoWrap
    _ ≤ (T : ℝ) *
        ((11 / 10 : ℝ) * ((U : ℝ) / Real.log (U : ℝ))) ^ 3 *
          (((L + 1 : ℕ) : ℝ))⁻¹ ^ 4 := by
      gcongr

/-- PNT-sized form of the elementary prime fourth-moment estimate.  This uses
the already formalized fixed-relative-error prime number theorem. -/
theorem eventually_fourth_moment_primeExponentialSum_le_pnt :
    ∀ᶠ X : ℕ in atTop, ∀ T : ℕ, 0 < T → 2 * X < T →
      ∑ t ∈ Finset.range T, ‖primeExponentialSum T X (t : ℤ)‖ ^ 4 ≤
        (T : ℝ) *
          ((11 / 10 : ℝ) * ((X : ℝ) / Real.log (X : ℝ))) ^ 3 := by
  filter_upwards
      [PrimeEstimates.eventually_primeCounting_tenth_bounds,
        eventually_ge_atTop 3] with X hpi hX
  intro T hTpos hnoWrap
  let : NeZero T := ⟨hTpos.ne'⟩
  have hcount : ((primesUpTo X).card : ℝ) ≤
      (11 / 10 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by
    rw [card_primesUpTo_eq_primeCounting]
    exact hpi.2
  calc
    ∑ t ∈ Finset.range T, ‖primeExponentialSum T X (t : ℤ)‖ ^ 4 ≤
        (T : ℝ) * ((primesUpTo X).card : ℝ) ^ 3 :=
      fourth_moment_primeExponentialSum_le T X hnoWrap
    _ ≤ (T : ℝ) *
        ((11 / 10 : ℝ) * ((X : ℝ) / Real.log (X : ℝ))) ^ 3 := by
      gcongr

/-- Weighted PNT-sized corollary. -/
theorem eventually_fourth_moment_weightedPrimeExponentialSum_le_pnt
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ X : ℕ in atTop, ∀ T : ℕ, 0 < T → 2 * X < T →
      ∀ w : ℕ → ℂ, (∀ p ∈ primesUpTo X, ‖w p‖ ≤ B) →
        ∑ t ∈ Finset.range T,
            ‖weightedPrimeExponentialSum T X w (t : ℤ)‖ ^ 4 ≤
          (T : ℝ) *
            ((11 / 10 : ℝ) * ((X : ℝ) / Real.log (X : ℝ))) ^ 3 * B ^ 4 := by
  filter_upwards
      [PrimeEstimates.eventually_primeCounting_tenth_bounds,
        eventually_ge_atTop 3] with X hpi hX
  intro T hTpos hnoWrap w hw
  let : NeZero T := ⟨hTpos.ne'⟩
  have hcount : ((primesUpTo X).card : ℝ) ≤
      (11 / 10 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by
    rw [card_primesUpTo_eq_primeCounting]
    exact hpi.2
  calc
    ∑ t ∈ Finset.range T,
        ‖weightedPrimeExponentialSum T X w (t : ℤ)‖ ^ 4 ≤
        (T : ℝ) * ((primesUpTo X).card : ℝ) ^ 3 * B ^ 4 :=
      fourth_moment_weightedPrimeExponentialSum_le T X w B hB hw hnoWrap
    _ ≤ (T : ℝ) *
        ((11 / 10 : ℝ) * ((X : ℝ) / Real.log (X : ℝ))) ^ 3 * B ^ 4 := by
      gcongr

end

end Erdos67
