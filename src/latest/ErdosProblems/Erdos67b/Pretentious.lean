import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic

/-!
# Finite pretentious distances

This file defines the finite squared pretentious distance

`sum_{p ≤ x} (1 - Re (f(p) * conj (g(p)))) / p`

and the Dirichlet--Archimedean twist occurring in Tao's logarithmically averaged Elliott
theorem.  The definitions are deliberately finite: no convergence theorem is needed to state
the non-asymptotic Elliott estimate.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos67b

noncomputable section

/-- The finite set of natural primes at most `x`. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

/-- The finite set of natural primes in the half-open interval `(x, y]`. -/
def primesBetween (x y : ℕ) : Finset ℕ :=
  (Finset.Ioc x y).filter Nat.Prime

@[simp]
theorem mem_primesUpTo {p x : ℕ} : p ∈ primesUpTo x ↔ p.Prime ∧ p ≤ x := by
  simp [primesUpTo, and_comm]

@[simp]
theorem mem_primesBetween {p x y : ℕ} : p ∈ primesBetween x y ↔ p.Prime ∧ x < p ∧ p ≤ y := by
  simp only [primesBetween, Finset.mem_filter, Finset.mem_Ioc]
  aesop

/-- A single summand of the finite squared pretentious distance. -/
def pretentiousTerm (f g : ℕ → ℂ) (p : ℕ) : ℝ :=
  (1 - (f p * conj (g p)).re) / (p : ℝ)

/-- The squared pretentious distance between `f` and `g`, restricted to the primes at most `x`.

The traditional notation for its square root is `ᵓ(f,g;x)`. -/
def pretentiousDistSq (f g : ℕ → ℂ) (x : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo x, pretentiousTerm f g p

/-- The Archimedean character `n ↦ n^(it)`.  Its value at zero is harmless because all
pretentious sums in this file are over primes. -/
def archimedeanTwist (t : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ (Complex.I * (t : ℂ))

/-- The product of a Dirichlet character and the Archimedean character `n^(it)`. -/
def dirichletArchimedeanTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  χ n * archimedeanTwist t n

/-- The exact finite distance used in the non-asymptotic Elliott theorem. -/
def pretentiousDistSqToTwist (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (x : ℕ) : ℝ :=
  pretentiousDistSq f (dirichletArchimedeanTwist χ t) x

theorem norm_archimedeanTwist {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖archimedeanTwist t n‖ = 1 := by
  rw [archimedeanTwist, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn)]
  simp

theorem conj_archimedeanTwist (t : ℝ) (n : ℕ) :
    conj (archimedeanTwist t n) = (n : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
  unfold archimedeanTwist
  calc
    conj ((n : ℂ) ^ (Complex.I * (t : ℂ))) =
        conj (conj (n : ℂ) ^ (Complex.I * (t : ℂ))) := by rw [Complex.conj_natCast]
    _ = (n : ℂ) ^ conj (Complex.I * (t : ℂ)) := by
      rw [Complex.cpow_conj]
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    _ = (n : ℂ) ^ (-(Complex.I * (t : ℂ))) := by simp

theorem norm_dirichletArchimedeanTwist_le_one {q n : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (hn : 0 < n) :
    ‖dirichletArchimedeanTwist χ t n‖ ≤ 1 := by
  rw [dirichletArchimedeanTwist, norm_mul, norm_archimedeanTwist hn, mul_one]
  exact χ.norm_le_one n

/-- Expanded form of the exact twist in Tao's hypothesis:
`f(p) * conj (χ(p)) * p^(-it)`. -/
theorem pretentiousDistSqToTwist_eq (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (x : ℕ) :
    pretentiousDistSqToTwist f χ t x =
      ∑ p ∈ primesUpTo x,
        (1 - (f p * conj (χ p) * (p : ℂ) ^ (-(Complex.I * (t : ℂ)))).re) / (p : ℝ) := by
  simp only [pretentiousDistSqToTwist, pretentiousDistSq]
  apply Finset.sum_congr rfl
  intro p _
  simp only [pretentiousTerm, dirichletArchimedeanTwist, map_mul, conj_archimedeanTwist]
  rw [mul_assoc]

theorem primesUpTo_mono {x y : ℕ} (hxy : x ≤ y) : primesUpTo x ⊆ primesUpTo y := by
  intro p hp
  rw [mem_primesUpTo] at hp ⊢
  exact ⟨hp.1, hp.2.trans hxy⟩

theorem primesUpTo_union_primesBetween {x y : ℕ} (hxy : x ≤ y) :
    primesUpTo x ∪ primesBetween x y = primesUpTo y := by
  ext p
  simp only [Finset.mem_union, mem_primesUpTo, mem_primesBetween]
  constructor
  · rintro (⟨hp, hpx⟩ | ⟨hp, _, hpy⟩)
    · exact ⟨hp, hpx.trans hxy⟩
    · exact ⟨hp, hpy⟩
  · rintro ⟨hp, hpy⟩
    by_cases hpx : p ≤ x
    · exact Or.inl ⟨hp, hpx⟩
    · exact Or.inr ⟨hp, Nat.lt_of_not_ge hpx, hpy⟩

theorem disjoint_primesUpTo_primesBetween (x y : ℕ) :
    Disjoint (primesUpTo x) (primesBetween x y) := by
  refine Finset.disjoint_left.mpr ?_
  intro p hp hpb
  rw [mem_primesUpTo] at hp
  rw [mem_primesBetween] at hpb
  exact (Nat.not_lt_of_ge hp.2) hpb.2.1

theorem pretentiousTerm_nonneg {f g : ℕ → ℂ} {p : ℕ}
    (hf : ‖f p‖ ≤ 1) (hg : ‖g p‖ ≤ 1) :
    0 ≤ pretentiousTerm f g p := by
  have hnorm : ‖f p * conj (g p)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (f p), norm_nonneg (g p)]
  have hre : (f p * conj (g p)).re ≤ 1 :=
    (Complex.re_le_norm _).trans hnorm
  exact div_nonneg (sub_nonneg.mpr hre) (Nat.cast_nonneg p)

theorem pretentiousTerm_le_two_div {f g : ℕ → ℂ} {p : ℕ}
    (hf : ‖f p‖ ≤ 1) (hg : ‖g p‖ ≤ 1) :
    pretentiousTerm f g p ≤ 2 / (p : ℝ) := by
  have hnorm : ‖f p * conj (g p)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (f p), norm_nonneg (g p)]
  have hre : -1 ≤ (f p * conj (g p)).re := by
    have := neg_le_of_abs_le (Complex.abs_re_le_norm (f p * conj (g p)))
    linarith
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg p)

theorem pretentiousDistSq_nonneg {f g : ℕ → ℂ} {x : ℕ}
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    0 ≤ pretentiousDistSq f g x := by
  apply Finset.sum_nonneg
  intro p hp
  have hp' := (mem_primesUpTo.mp hp).1
  exact pretentiousTerm_nonneg (hf p hp') (hg p hp')

theorem pretentiousDistSq_mono {f g : ℕ → ℂ} {x y : ℕ} (hxy : x ≤ y)
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    pretentiousDistSq f g x ≤ pretentiousDistSq f g y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (primesUpTo_mono hxy)
  intro p hp _
  have hp' := (mem_primesUpTo.mp hp).1
  exact pretentiousTerm_nonneg (hf p hp') (hg p hp')

theorem pretentiousDistSq_eq_add_between {f g : ℕ → ℂ} {x y : ℕ} (hxy : x ≤ y) :
    pretentiousDistSq f g y =
      pretentiousDistSq f g x + ∑ p ∈ primesBetween x y, pretentiousTerm f g p := by
  change (∑ p ∈ primesUpTo y, pretentiousTerm f g p) =
    (∑ p ∈ primesUpTo x, pretentiousTerm f g p) +
      ∑ p ∈ primesBetween x y, pretentiousTerm f g p
  rw [← primesUpTo_union_primesBetween hxy,
    Finset.sum_union (disjoint_primesUpTo_primesBetween x y)]

theorem pretentiousDistSq_sub_eq_between {f g : ℕ → ℂ} {x y : ℕ} (hxy : x ≤ y) :
    pretentiousDistSq f g y - pretentiousDistSq f g x =
      ∑ p ∈ primesBetween x y, pretentiousTerm f g p := by
  rw [pretentiousDistSq_eq_add_between hxy]
  ring

theorem pretentiousDistSq_le_primeHarmonic {f g : ℕ → ℂ} {x : ℕ}
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    pretentiousDistSq f g x ≤ ∑ p ∈ primesUpTo x, 2 / (p : ℝ) := by
  apply Finset.sum_le_sum
  intro p hp
  have hp' := (mem_primesUpTo.mp hp).1
  exact pretentiousTerm_le_two_div (hf p hp') (hg p hp')

theorem pretentiousDistSq_tail_le_primeHarmonic {f g : ℕ → ℂ} {x y : ℕ} (hxy : x ≤ y)
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    pretentiousDistSq f g y - pretentiousDistSq f g x ≤
      ∑ p ∈ primesBetween x y, 2 / (p : ℝ) := by
  rw [pretentiousDistSq_sub_eq_between hxy]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := (mem_primesBetween.mp hp).1
  exact pretentiousTerm_le_two_div (hf p hp') (hg p hp')

theorem pretentiousDistSqToTwist_nonneg {f : ℕ → ℂ} {q x : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ)
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) :
    0 ≤ pretentiousDistSqToTwist f χ t x := by
  apply pretentiousDistSq_nonneg hf
  intro p hp
  exact norm_dirichletArchimedeanTwist_le_one χ t hp.pos

theorem pretentiousDistSqToTwist_mono {f : ℕ → ℂ} {q x y : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (hxy : x ≤ y)
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) :
    pretentiousDistSqToTwist f χ t x ≤ pretentiousDistSqToTwist f χ t y := by
  apply pretentiousDistSq_mono hxy hf
  intro p hp
  exact norm_dirichletArchimedeanTwist_le_one χ t hp.pos

theorem pretentiousDistSqToTwist_le_primeHarmonic {f : ℕ → ℂ} {q x : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ)
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) :
    pretentiousDistSqToTwist f χ t x ≤ ∑ p ∈ primesUpTo x, 2 / (p : ℝ) := by
  apply pretentiousDistSq_le_primeHarmonic hf
  intro p hp
  exact norm_dirichletArchimedeanTwist_le_one χ t hp.pos

theorem pretentiousTerm_symm (f g : ℕ → ℂ) (p : ℕ) :
    pretentiousTerm f g p = pretentiousTerm g f p := by
  simp [pretentiousTerm, Complex.mul_re]
  ring

theorem pretentiousDistSq_symm (f g : ℕ → ℂ) (x : ℕ) :
    pretentiousDistSq f g x = pretentiousDistSq g f x := by
  apply Finset.sum_congr rfl
  intro p _
  exact pretentiousTerm_symm f g p

theorem pretentiousTerm_conj (f g : ℕ → ℂ) (p : ℕ) :
    pretentiousTerm (fun n ↦ conj (f n)) (fun n ↦ conj (g n)) p =
      pretentiousTerm f g p := by
  simp [pretentiousTerm, Complex.mul_re]

theorem pretentiousDistSq_conj (f g : ℕ → ℂ) (x : ℕ) :
    pretentiousDistSq (fun n ↦ conj (f n)) (fun n ↦ conj (g n)) x =
      pretentiousDistSq f g x := by
  apply Finset.sum_congr rfl
  intro p _
  exact pretentiousTerm_conj f g p

theorem pretentiousTerm_eq_norm_sub_sq {f g : ℕ → ℂ} {p : ℕ}
    (hf : ‖f p‖ = 1) (hg : ‖g p‖ = 1) :
    pretentiousTerm f g p = ‖f p - g p‖ ^ 2 / (2 * (p : ℝ)) := by
  have hsq : ‖f p - g p‖ ^ 2 = 2 * (1 - (f p * conj (g p)).re) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hf, hg]
    ring
  rw [pretentiousTerm, hsq]
  ring

theorem pretentiousTerm_self {f : ℕ → ℂ} {p : ℕ} (hf : ‖f p‖ = 1) :
    pretentiousTerm f f p = 0 := by
  rw [pretentiousTerm_eq_norm_sub_sq hf hf, sub_self, norm_zero, zero_pow (by decide), zero_div]

theorem pretentiousDistSq_self {f : ℕ → ℂ} {x : ℕ}
    (hf : ∀ p, p.Prime → ‖f p‖ = 1) :
    pretentiousDistSq f f x = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  exact pretentiousTerm_self (hf p (mem_primesUpTo.mp hp).1)

/-- A triangle inequality for squared pretentious distance.  The factor `2` is the standard
loss incurred by squaring the pointwise triangle inequality. -/
theorem pretentiousTerm_triangle_sq {f g h : ℕ → ℂ} {p : ℕ} (hp : p.Prime)
    (hf : ‖f p‖ = 1) (hg : ‖g p‖ = 1) (hh : ‖h p‖ = 1) :
    pretentiousTerm f h p ≤ 2 * (pretentiousTerm f g p + pretentiousTerm g h p) := by
  rw [pretentiousTerm_eq_norm_sub_sq hf hh, pretentiousTerm_eq_norm_sub_sq hf hg,
    pretentiousTerm_eq_norm_sub_sq hg hh]
  have htri : ‖f p - h p‖ ≤ ‖f p - g p‖ + ‖g p - h p‖ := by
    calc
      ‖f p - h p‖ = ‖(f p - g p) + (g p - h p)‖ := by ring_nf
      _ ≤ ‖f p - g p‖ + ‖g p - h p‖ := norm_add_le _ _
  have hsq : ‖f p - h p‖ ^ 2 ≤
      2 * (‖f p - g p‖ ^ 2 + ‖g p - h p‖ ^ 2) := by
    nlinarith [norm_nonneg (f p - h p), norm_nonneg (f p - g p),
      norm_nonneg (g p - h p), sq_nonneg (‖f p - g p‖ - ‖g p - h p‖)]
  have hpden : 0 ≤ 2 * (p : ℝ) := by positivity
  calc
    ‖f p - h p‖ ^ 2 / (2 * (p : ℝ)) ≤
        (2 * (‖f p - g p‖ ^ 2 + ‖g p - h p‖ ^ 2)) / (2 * (p : ℝ)) :=
      div_le_div_of_nonneg_right hsq hpden
    _ = 2 * (‖f p - g p‖ ^ 2 / (2 * (p : ℝ)) +
        ‖g p - h p‖ ^ 2 / (2 * (p : ℝ))) := by
      field_simp [hp.ne_zero]

theorem pretentiousDistSq_triangle_sq {f g h : ℕ → ℂ} {x : ℕ}
    (hf : ∀ p, p.Prime → ‖f p‖ = 1) (hg : ∀ p, p.Prime → ‖g p‖ = 1)
    (hh : ∀ p, p.Prime → ‖h p‖ = 1) :
    pretentiousDistSq f h x ≤
      2 * (pretentiousDistSq f g x + pretentiousDistSq g h x) := by
  calc
    pretentiousDistSq f h x ≤
        ∑ p ∈ primesUpTo x, 2 * (pretentiousTerm f g p + pretentiousTerm g h p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := (mem_primesUpTo.mp hp).1
      exact pretentiousTerm_triangle_sq hp' (hf p hp') (hg p hp') (hh p hp')
    _ = 2 * (pretentiousDistSq f g x + pretentiousDistSq g h x) := by
      simp only [pretentiousDistSq]
      calc
        (∑ p ∈ primesUpTo x, 2 * (pretentiousTerm f g p + pretentiousTerm g h p)) =
            (∑ p ∈ primesUpTo x, 2 * pretentiousTerm f g p) +
              ∑ p ∈ primesUpTo x, 2 * pretentiousTerm g h p := by
          simp_rw [mul_add]
          exact Finset.sum_add_distrib
        _ = 2 * (∑ p ∈ primesUpTo x, pretentiousTerm f g p) +
              2 * (∑ p ∈ primesUpTo x, pretentiousTerm g h p) := by
          rw [Finset.mul_sum, Finset.mul_sum]
        _ = 2 * ((∑ p ∈ primesUpTo x, pretentiousTerm f g p) +
              ∑ p ∈ primesUpTo x, pretentiousTerm g h p) := by ring

end

end Erdos67b
