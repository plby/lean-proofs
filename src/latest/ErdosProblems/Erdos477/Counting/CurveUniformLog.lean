/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A coefficient-uniform plane curve bound, with an explicit logarithmic loss.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.UniformLogHeight
import ErdosProblems.Erdos477.Counting.CurveHeightBound

namespace Erdos477.Counting

open Erdos477.Geometry

variable {K : Type*} [Field K]

lemma degreeOf_le_of_dvd_plane (P Q : MvPolynomial (Fin 2) K)
    (hQ : Q ≠ 0) (hdiv : P ∣ Q) (i : Fin 2) : P.degreeOf i ≤ Q.degreeOf i := by
  obtain ⟨G, hG⟩ := hdiv
  have hP0 : P ≠ 0 := by intro h; rw [h, zero_mul] at hG; exact hQ hG
  have hG0 : G ≠ 0 := by intro h; rw [h, mul_zero] at hG; exact hQ hG
  rw [hG, MvPolynomial.degreeOf_mul_eq hP0 hG0]
  omega

lemma degreeOf_eq_of_associated_plane (P Q : MvPolynomial (Fin 2) K)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (h : Associated P Q) (i : Fin 2) :
    P.degreeOf i = Q.degreeOf i :=
  (degreeOf_le_of_dvd_plane P Q hQ h.dvd i).antisymm
    (degreeOf_le_of_dvd_plane Q P hP h.symm.dvd i)

variable [CharZero K]

theorem exists_uniform_curve_log_bound (D d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 ≤ ε) (hεn : 1 ≤ ε * ((n : ℝ) - 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      2 * Real.log (d * n : ℕ) < Real.log B →
      ∀ P : MvPolynomial (Fin 2) K, Irreducible P → P.totalDegree = D →
      P.degreeOf 0 = d → ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, MvPolynomial.eval (fun k => (z k : K)) P = 0) →
      (∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * (Real.log B + 1) ^ 4 * B ^ (1 / (d : ℝ) + ε) := by
  obtain ⟨C₀, hC₀, hcurve⟩ := exists_curve_height_bound (K := K)
  obtain ⟨L, hL, hlog⟩ := exists_uniform_log_derivative_bound D
  let J := C₀ * L + 2
  have hJ : 0 < J := by dsimp only [J]; positivity
  let C : ℝ := (D : ℝ) ^ 2 + J ^ 4 * (D * (d + n - 2) : ℕ) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro B hB hlarge P hP hD hPd S hS hheight
  have hBlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hfactor : 1 ≤ (Real.log B + 1) ^ 4 * B ^ (1 / (d : ℝ) + ε) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith))
      (Real.one_le_rpow hB (by positivity))
  have hDcard : (D : ℝ) ^ 2 ≤ C := by
    have h : 0 ≤ J ^ 4 * (D * (d + n - 2) : ℕ) := by positivity
    dsimp only [C]
    linarith
  by_cases hsmall : S.card ≤ D ^ 2
  · have hsmallR : (S.card : ℝ) ≤ (D : ℝ) ^ 2 := by exact_mod_cast hsmall
    calc
      _ ≤ C := hsmallR.trans hDcard
      _ ≤ C * ((Real.log B + 1) ^ 4 * B ^ (1 / (d : ℝ) + ε)) :=
        le_mul_of_one_le_right hC.le hfactor
      _ = _ := by ring
  have hlargecard : P.totalDegree ^ 2 < S.card := by rw [hD]; omega
  obtain ⟨Q, hQ, hQD, hassoc, hvan, hcoeff⟩ := exists_bounded_associated_equation
    P hP B hB S hlargecard hS hheight
  rw [hD] at hQD hcoeff
  have hQmap : Irreducible (MvPolynomial.map (Int.castRingHom K) Q) :=
    hassoc.irreducible hP
  have hQd : Q.degreeOf 0 = d := by
    have h := degreeOf_eq_of_associated_plane P _ hP.ne_zero hQmap.ne_zero hassoc 0
    rw [degreeOf_map_of_injective _ Int.cast_injective, hPd] at h
    exact h.symm
  let W := Real.log (coefficientSum (MvPolynomial.pderiv 0 Q) + 1 : ℕ) +
    Q.totalDegree * Real.log B + 1
  let T := ⌈C₀ * W⌉₊
  have hW : 0 ≤ W := by
    have hlogQ : 0 ≤ Real.log (coefficientSum (MvPolynomial.pderiv 0 Q) + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 _)
    dsimp only [W]
    positivity
  have hT : ((T + 1 : ℕ) : ℝ) ≤ J * (Real.log B + 1) :=
    ceil_height_le_log C₀ L hC₀.le B W hB hW (hlog B hB Q hQD hcoeff 0)
  have hbound := hcurve d n hd hn ε hε hεn B hB hlarge Q hQd hQmap S hvan hheight
  change (S.card : ℝ) ≤ (Q.totalDegree * (Q.totalDegree - 1) : ℕ) +
    ((T + 1 : ℕ) : ℝ) ^ 4 * (Q.totalDegree * (d + n - 2) : ℕ) *
      B ^ (1 / (d : ℝ) + ε) at hbound
  have hQD' : (Q.totalDegree * (Q.totalDegree - 1) : ℕ) ≤ D ^ 2 := by
    calc
      _ ≤ D * D := Nat.mul_le_mul hQD ((Nat.sub_le _ _).trans hQD)
      _ = _ := (pow_two D).symm
  have hpoly : (Q.totalDegree * (d + n - 2) : ℕ) ≤ D * (d + n - 2) :=
    Nat.mul_le_mul_right _ hQD
  have hbound' : (S.card : ℝ) ≤ (D : ℝ) ^ 2 +
      (J * (Real.log B + 1)) ^ 4 * (D * (d + n - 2) : ℕ) *
        B ^ (1 / (d : ℝ) + ε) := by
    apply hbound.trans
    gcongr
    · exact_mod_cast hQD'
  apply hbound'.trans
  have hfirst := mul_le_mul_of_nonneg_left hfactor (sq_nonneg (D : ℝ))
  have hnonneg := mul_nonneg hC.le (sub_nonneg.mpr hfactor)
  dsimp only [C]
  nlinarith

#print axioms exists_uniform_curve_log_bound
-- 'Erdos477.Counting.exists_uniform_curve_log_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
