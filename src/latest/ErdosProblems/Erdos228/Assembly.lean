import Mathlib

/-!
# Pairing identities and final estimates for Erdős Problem 228

The flat-polynomial construction is first made as a Laurent polynomial with
paired coefficients.  Equal coefficients at `k` and `-k` give a cosine term;
opposite coefficients give a purely imaginary sine term.  This file records
that conversion and the elementary norm estimates used at the end of the
proof.  The lemmas are independent of the particular way in which the signs
are constructed.
-/

namespace Erdos228

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ## Points on the circle and paired Laurent monomials -/

/-- The standard parametrization of the complex unit circle. -/
def unitPoint (theta : ℝ) : ℂ :=
  Complex.exp ((theta : ℂ) * Complex.I)

@[simp]
theorem norm_unitPoint (theta : ℝ) : ‖unitPoint theta‖ = 1 := by
  simp [unitPoint, Complex.norm_exp]

@[simp]
theorem unitPoint_ne_zero (theta : ℝ) : unitPoint theta ≠ 0 := by
  simp [unitPoint]

@[simp]
theorem unitPoint_neg (theta : ℝ) : unitPoint (-theta) = (unitPoint theta)⁻¹ := by
  simp [unitPoint, Complex.exp_neg]

/-- Euler's identity for a natural power of a point on the circle. -/
theorem unitPoint_pow (theta : ℝ) (k : ℕ) :
    unitPoint theta ^ k =
      (Real.cos (k * theta) : ℂ) + (Real.sin (k * theta) : ℂ) * Complex.I := by
  rw [unitPoint, ← Complex.exp_nat_mul]
  have harg : (k : ℂ) * ((theta : ℂ) * Complex.I) =
      (((k : ℝ) * theta : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, ← Complex.cos_add_sin_I]
  simp

/-- The inverse power has the opposite sine component. -/
theorem unitPoint_inv_pow (theta : ℝ) (k : ℕ) :
    (unitPoint theta)⁻¹ ^ k =
      (Real.cos (k * theta) : ℂ) - (Real.sin (k * theta) : ℂ) * Complex.I := by
  rw [← unitPoint_neg, unitPoint_pow]
  simp [Real.cos_neg, Real.sin_neg]
  ring_nf

/-- A symmetric pair of Laurent monomials is twice a cosine. -/
theorem unitPoint_pow_add_inv_pow (theta : ℝ) (k : ℕ) :
    unitPoint theta ^ k + (unitPoint theta)⁻¹ ^ k =
      (2 * Real.cos (k * theta) : ℝ) := by
  rw [unitPoint_pow, unitPoint_inv_pow]
  push_cast
  ring

/-- An antisymmetric pair of Laurent monomials is twice `I` times a sine. -/
theorem unitPoint_pow_sub_inv_pow (theta : ℝ) (k : ℕ) :
    unitPoint theta ^ k - (unitPoint theta)⁻¹ ^ k =
      (2 * Real.sin (k * theta) : ℝ) * Complex.I := by
  rw [unitPoint_pow, unitPoint_inv_pow]
  push_cast
  ring

/-! ## Finite paired sums -/

/-- The real cosine sum belonging to a finite set of symmetric pairs. -/
def cosineSum (s : Finset ℕ) (eps : ℕ → ℝ) (theta : ℝ) : ℝ :=
  ∑ k ∈ s, eps k * Real.cos (k * theta)

/-- The real sine sum belonging to a finite set of antisymmetric pairs. -/
def sineSum (s : Finset ℕ) (eps : ℕ → ℝ) (theta : ℝ) : ℝ :=
  ∑ k ∈ s, eps k * Real.sin (k * theta)

/-- A centered Laurent value, split into one symmetric and two antisymmetric
parts.  The two sine parts correspond to the even and odd pieces in the
Balister--Bollobás--Morris--Sahasrabudhe--Tiba construction. -/
def pairedLaurentValue (C Se So : Finset ℕ)
    (epsC epsE epsO : ℕ → ℝ) (theta : ℝ) : ℂ :=
  1 +
    ∑ k ∈ C, (epsC k : ℂ) *
      (unitPoint theta ^ k + (unitPoint theta)⁻¹ ^ k) +
    ∑ k ∈ Se, (epsE k : ℂ) *
      (unitPoint theta ^ k - (unitPoint theta)⁻¹ ^ k) +
    ∑ k ∈ So, (epsO k : ℂ) *
      (unitPoint theta ^ k - (unitPoint theta)⁻¹ ^ k)

/-- The real/imaginary normal form used in the final estimates. -/
def assembledValue (c se so : ℝ) : ℂ :=
  ((1 + 2 * c : ℝ) : ℂ) + ((2 * (se + so) : ℝ) : ℂ) * Complex.I

@[simp]
theorem assembledValue_re (c se so : ℝ) :
    (assembledValue c se so).re = 1 + 2 * c := by
  simp [assembledValue]

@[simp]
theorem assembledValue_im (c se so : ℝ) :
    (assembledValue c se so).im = 2 * (se + so) := by
  simp [assembledValue]

/-- Pairing the Laurent coefficients gives exactly one real cosine component
and the sum of the two real sine components in the imaginary coordinate. -/
theorem pairedLaurentValue_eq_assembledValue (C Se So : Finset ℕ)
    (epsC epsE epsO : ℕ → ℝ) (theta : ℝ) :
    pairedLaurentValue C Se So epsC epsE epsO theta =
      assembledValue (cosineSum C epsC theta)
        (sineSum Se epsE theta) (sineSum So epsO theta) := by
  classical
  have hC :
      (∑ k ∈ C, (epsC k : ℂ) *
        (unitPoint theta ^ k + (unitPoint theta)⁻¹ ^ k)) =
        ((2 * cosineSum C epsC theta : ℝ) : ℂ) := by
    rw [cosineSum]
    push_cast
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [unitPoint_pow_add_inv_pow]
    push_cast
    ring
  have hE :
      (∑ k ∈ Se, (epsE k : ℂ) *
        (unitPoint theta ^ k - (unitPoint theta)⁻¹ ^ k)) =
        ((2 * sineSum Se epsE theta : ℝ) : ℂ) * Complex.I := by
    rw [sineSum]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [unitPoint_pow_sub_inv_pow]
    push_cast
    ring
  have hO :
      (∑ k ∈ So, (epsO k : ℂ) *
        (unitPoint theta ^ k - (unitPoint theta)⁻¹ ^ k)) =
        ((2 * sineSum So epsO theta : ℝ) : ℂ) * Complex.I := by
    rw [sineSum]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [unitPoint_pow_sub_inv_pow]
    push_cast
    ring
  rw [pairedLaurentValue, hC, hE, hO]
  simp only [assembledValue]
  push_cast
  ring

/-! ## Final lower and upper estimates -/

/-- Exact Pythagorean identity for the assembled complex value. -/
theorem norm_assembledValue_sq (c se so : ℝ) :
    ‖assembledValue c se so‖ ^ 2 =
      (1 + 2 * c) ^ 2 + (2 * (se + so)) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, pow_two]

/-- The cosine coordinate alone gives the lower bound `2 |c| - 1`. -/
theorem two_mul_abs_sub_one_le_norm_assembledValue (c se so : ℝ) :
    2 * |c| - 1 ≤ ‖assembledValue c se so‖ := by
  have htriangle : |2 * c| ≤ |1 + 2 * c| + 1 := by
    calc
      |2 * c| = |(1 + 2 * c) - 1| := by ring_nf
      _ ≤ |1 + 2 * c| + |(1 : ℝ)| := abs_sub _ _
      _ = |1 + 2 * c| + 1 := by norm_num
  have hre : |1 + 2 * c| ≤ ‖assembledValue c se so‖ := by
    simpa using Complex.abs_re_le_norm (assembledValue c se so)
  rw [abs_mul] at htriangle
  norm_num at htriangle
  linarith

/-- If the cosine component is at least `a`, with `a ≥ 1`, then the whole
assembled value has norm at least `a`. -/
theorem le_norm_assembledValue_of_le_abs_cosine {a c se so : ℝ}
    (ha : 1 ≤ a) (hc : a ≤ |c|) :
    a ≤ ‖assembledValue c se so‖ := by
  calc
    a ≤ 2 * |c| - 1 := by linarith
    _ ≤ ‖assembledValue c se so‖ :=
      two_mul_abs_sub_one_le_norm_assembledValue c se so

/-- The imaginary coordinate gives a lower bound after subtracting the size
of the already chosen even-sine part from the odd-sine part. -/
theorem two_mul_abs_sub_abs_le_norm_assembledValue (c se so : ℝ) :
    2 * (|so| - |se|) ≤ ‖assembledValue c se so‖ := by
  have htriangle : |so| ≤ |se + so| + |se| := by
    calc
      |so| = |(se + so) - se| := by ring_nf
      _ ≤ |se + so| + |se| := abs_sub _ _
  have him : |2 * (se + so)| ≤ ‖assembledValue c se so‖ := by
    simpa using Complex.abs_im_le_norm (assembledValue c se so)
  rw [abs_mul] at him
  norm_num at him
  linarith

/-- A convenient hypothesis form of the sine-coordinate lower bound. -/
theorem le_norm_assembledValue_of_sine_gap {a c se so : ℝ}
    (hgap : a / 2 + |se| ≤ |so|) :
    a ≤ ‖assembledValue c se so‖ := by
  have h := two_mul_abs_sub_abs_le_norm_assembledValue c se so
  linarith

/-- A linear upper bound obtained from the two coordinates.  This is looser
than the exact Pythagorean estimate but has especially convenient hypotheses. -/
theorem norm_assembledValue_le (c se so A B D : ℝ)
    (hA : |c| ≤ A) (hB : |se| ≤ B) (hD : |so| ≤ D) :
    ‖assembledValue c se so‖ ≤ 1 + 2 * (A + B + D) := by
  calc
    ‖assembledValue c se so‖ ≤ |1 + 2 * c| + |2 * (se + so)| := by
      simpa [assembledValue] using
        Complex.norm_le_abs_re_add_abs_im (assembledValue c se so)
    _ ≤ (1 + 2 * |c|) + 2 * (|se| + |so|) := by
      calc
        |1 + 2 * c| + |2 * (se + so)| ≤
            (|1| + |2 * c|) + |2| * (|se| + |so|) := by
              gcongr
              · exact abs_add_le _ _
              · rw [abs_mul]
                gcongr
                exact abs_add_le _ _
        _ = (1 + 2 * |c|) + 2 * (|se| + |so|) := by norm_num
    _ ≤ 1 + 2 * (A + B + D) := by linarith

/-- The numerical upper-bound calculation used in the published construction:
`|c| ≤ sqrt n`, `|se| ≤ 6 sqrt n`, and `|so| ≤ 2^10 sqrt n` are more
than enough for the advertised `2^12 sqrt n` bound. -/
theorem norm_assembledValue_le_two_pow_twelve_sqrt {n : ℕ} {c se so : ℝ}
    (hn : 1 ≤ n)
    (hc : |c| ≤ Real.sqrt n)
    (hse : |se| ≤ 6 * Real.sqrt n)
    (hso : |so| ≤ 2 ^ 10 * Real.sqrt n) :
    ‖assembledValue c se so‖ ≤ 2 ^ 12 * Real.sqrt n := by
  have hsqrt : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have h := norm_assembledValue_le c se so
    (Real.sqrt n) (6 * Real.sqrt n) (2 ^ 10 * Real.sqrt n) hc hse hso
  norm_num at h ⊢
  nlinarith

/-- On a dangerous interval, an odd-sine value larger than `10 sqrt n`
dominates an even-sine error bounded by `6 sqrt n`. -/
theorem eight_sqrt_le_norm_assembledValue_of_odd_sine {n : ℕ} {c se so : ℝ}
    (hse : |se| ≤ 6 * Real.sqrt n)
    (hso : 10 * Real.sqrt n ≤ |so|) :
    8 * Real.sqrt n ≤ ‖assembledValue c se so‖ := by
  apply le_norm_assembledValue_of_sine_gap
  linarith

end

end Erdos228
