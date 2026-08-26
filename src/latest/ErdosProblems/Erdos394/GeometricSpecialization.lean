import ErdosProblems.Erdos394.GlobalMediumSieve
import ErdosProblems.Erdos394.GeometricBrun

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Specializing the finite global sieve to power-of-16 prime intervals
-/

open Nat Finset

namespace Erdos394

/-- Prime-interval membership gives the expected strict/lax endpoint bounds. -/
theorem mem_primeInterval_bounds {a b p : ℕ} (hp : p ∈ primeInterval a b) :
    a < p ∧ p ≤ b := by
  have hp' := Finset.mem_sdiff.mp hp
  have hpb := Nat.mem_primesLE.mp hp'.1
  refine ⟨?_, hpb.1⟩
  by_contra hnot
  have hpa : p ≤ a := Nat.le_of_not_gt hnot
  exact hp'.2 (Nat.mem_primesLE.mpr ⟨hpa, hpb.2⟩)

/-- Every member of a prime interval is prime. -/
theorem prime_of_mem_primeInterval {a b p : ℕ} (hp : p ∈ primeInterval a b) :
    p.Prime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2

/-- A prime interval ending at positive `y` has cardinality at most `y`. -/
theorem card_primeInterval_le {a y : ℕ} (hy : 0 < y) :
    (primeInterval a y).card ≤ y := by
  have hsub : primeInterval a y ⊆ Finset.Icc 1 y := by
    intro p hp
    have hb := mem_primeInterval_bounds hp
    exact Finset.mem_Icc.mpr ⟨(prime_of_mem_primeInterval hp).one_le, hb.2⟩
  exact (Finset.card_le_card hsub).trans (by simp)

/-- On every sufficiently late moving power-of-16 interval, the finite global
bound collapses to a squared-prime term, twice the combined Euler decay, and
the explicit Brun remainder. -/
theorem exists_geometric_finite_medium_bound :
    ∃ Jmin : ℕ, 2 ≤ Jmin ∧ ∀ Jz Jy X : ℕ, Jmin ≤ Jz → Jz ≤ Jy →
      (∑ n ∈ Finset.Icc 1 X, (t 2 n : ℝ)) ≤
        (X : ℝ) ^ 2 / (16 ^ Jz : ℕ) +
        2 * (X : ℝ) ^ 2 *
          Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) +
        2 * (X : ℝ) *
          (((geometricBrunOrder Jy + 1) *
            (16 ^ Jy) ^ geometricBrunOrder Jy : ℕ) : ℝ) *
          ((((16 ^ Jy) ^ geometricBrunOrder Jy : ℕ) : ℝ) *
            ((((16 ^ Jy) ^ geometricBrunOrder Jy + 1 : ℕ) : ℝ))) := by
  obtain ⟨Jb, hJb, hbrun⟩ := exists_geometric_primeInterval_brun_tail
  obtain ⟨Je, hJe, heuler⟩ := exists_geometric_interval_euler_bounds
  let Jmin := max Jb Je
  refine ⟨Jmin, hJb.trans (le_max_left Jb Je), ?_⟩
  intro Jz Jy X hmin hzY
  have hbmin : Jb ≤ Jz := (le_max_left Jb Je).trans (by simpa [Jmin] using hmin)
  have hemin : Je ≤ Jz := (le_max_right Jb Je).trans (by simpa [Jmin] using hmin)
  let z : ℕ := 16 ^ Jz
  let y : ℕ := 16 ^ Jy
  let R : ℕ := geometricBrunOrder Jy
  let P : Finset ℕ := primeInterval z y
  have hJy2 : 2 ≤ Jy := hJb.trans hbmin |>.trans hzY
  have hzpos : 0 < z := by simp [z]
  have hypos : 0 < y := by simp [y]
  have hzy : z ≤ y := by
    dsimp [z, y]
    exact Nat.pow_le_pow_right (by norm_num) hzY
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeInterval hp
  have hPinterval : ∀ p ∈ P, z < p ∧ p ≤ y := by
    intro p hp
    exact mem_primeInterval_bounds hp
  have hne2 : ∀ p ∈ P, p ≠ 2 := by
    intro p hp hp2
    have hpz := (hPinterval p hp).1
    subst p
    have : 2 < z := by
      dsimp [z]
      have : 1 ≤ Jz := by omega
      exact (by norm_num : 2 < 16 ^ 1) |>.trans_le
        (Nat.pow_le_pow_right (by norm_num) this)
    omega
  have hPcard : P.card ≤ y := card_primeInterval_le hypos
  have htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ)) := by
    dsimp [P, R, z, y]
    exact hbrun Jz Jy hbmin hzY
  have hfinite := finite_medium_sieve_bound P hprime
    (X := X) (R := R) (y := y) (z := z) hzpos.ne' hzy hPinterval
    hne2 hypos hPcard (geometricBrunOrder_even Jy) htail
  have hEuler := (heuler Jz Jy hemin hzY).1
  have hV0 : 0 ≤ localEulerProduct P (fun p ↦ 1 / (p : ℝ)) := by
    apply localEulerProduct_nonneg P (fun p ↦ 1 / (p : ℝ))
    · intro p hp
      positivity
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
      exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
  have hhalfOne : (1 : ℝ) ≤ ∏ p ∈ P, (1 + 1 / (2 * (p : ℝ))) := by
    apply Finset.one_le_prod
    intro p hp
    have : 0 ≤ 1 / (2 * (p : ℝ)) := by positivity
    linarith
  have hhalfEq : (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) =
      ∏ p ∈ P, (1 + (1 / (p : ℝ)) / 2) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
    field_simp
  have hEulerP : localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
      (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) ≤
      Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) := by
    rw [hhalfEq]
    simpa [P, z, y] using hEuler
  have hVleCombined : localEulerProduct P (fun p ↦ 1 / (p : ℝ)) ≤
      localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) := by
    nlinarith
  have hdecay : localEulerProduct P (fun p ↦ 1 / (p : ℝ)) ≤
      Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) := by
    exact hVleCombined.trans hEulerP
  have htailTerm : (X : ℝ) ^ 2 *
      ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
        ((R + 1).factorial : ℝ)) ≤
      (X : ℝ) ^ 2 *
        Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) := by
    apply mul_le_mul_of_nonneg_left (htail.trans hdecay)
    positivity
  have hmainTerm : (X : ℝ) ^ 2 *
      localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) ≤
      (X : ℝ) ^ 2 *
        Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) := by
    calc
      (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) =
        (X : ℝ) ^ 2 * (localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ))))) := by ring
      _ ≤ (X : ℝ) ^ 2 *
          Real.exp (-((Real.log Jy - (1 + Real.log Jz)) / 128)) :=
        mul_le_mul_of_nonneg_left hEulerP (by positivity)
  dsimp [P, R, z, y] at hfinite htailTerm hmainTerm ⊢
  linarith

end Erdos394
