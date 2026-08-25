/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.Geometry

namespace Erdos232

open scoped ComplexConjugate

private theorem normalized_two_centres (z w : ℂ)
    (h0 : Complex.normSq z = Complex.normSq w)
    (h1 : Complex.normSq (z - 1) = Complex.normSq (w - 1)) :
    z.re = w.re ∧ z.im ^ 2 = w.im ^ 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im] at h0 h1
  constructor <;> nlinarith

private theorem same_im_of_three_centres (z w z₀ w₀ : ℂ)
    (hre : z.re = w.re) (hre₀ : z₀.re = w₀.re)
    (him2 : z.im ^ 2 = w.im ^ 2) (him₀ : z₀.im = w₀.im) (hz₀ : z₀.im ≠ 0)
    (hd : Complex.normSq (z - z₀) = Complex.normSq (w - w₀)) :
    z.im = w.im := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hd
  rw [hre, hre₀, him₀] at hd
  have hw₀ : w₀.im ≠ 0 := by simpa only [him₀] using hz₀
  have hprod : (z.im - w.im) * w₀.im = 0 := by
    nlinarith [him2]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hw₀)

private theorem opposite_im_of_three_centres (z w z₀ w₀ : ℂ)
    (hre : z.re = w.re) (hre₀ : z₀.re = w₀.re)
    (him2 : z.im ^ 2 = w.im ^ 2) (him₀ : z₀.im = -w₀.im) (hz₀ : z₀.im ≠ 0)
    (hd : Complex.normSq (z - z₀) = Complex.normSq (w - w₀)) :
    z.im = -w.im := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hd
  rw [hre, hre₀, him₀] at hd
  have hw₀ : w₀.im ≠ 0 := by
    intro hw
    apply hz₀
    rw [him₀, hw, neg_zero]
  have hprod : (z.im + w.im) * w₀.im = 0 := by
    nlinarith [him2]
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hprod).resolve_right hw₀)

private theorem affine_of_normalized_eq (p q pa qa pb qb : ℂ)
    (hp : pb - pa ≠ 0) (hq : qb - qa ≠ 0)
    (h : (q - qa) / (qb - qa) = (p - pa) / (pb - pa)) :
    q = (qb - qa) / (pb - pa) * p +
      (qa - (qb - qa) / (pb - pa) * pa) := by
  have hdelta : q - qa = (qb - qa) / (pb - pa) * (p - pa) := by
    calc
      q - qa = (qb - qa) * ((q - qa) / (qb - qa)) := by field_simp
      _ = (qb - qa) * ((p - pa) / (pb - pa)) := by rw [h]
      _ = (qb - qa) / (pb - pa) * (p - pa) := by ring
  calc
    q = (q - qa) + qa := by ring
    _ = (qb - qa) / (pb - pa) * (p - pa) + qa := by rw [hdelta]
    _ = _ := by ring

/-- Any two nonempty finite configurations in the complex plane with the same complete
distance matrix differ by a translation followed by either a rotation or a reflected rotation.

The statement uses squared complex norms, which is the form in which the exact radical
coordinates of the 23-point certificate are checked. -/
theorem exists_complex_rigid_of_normSq_eq
    {m : ℕ} (hm : 0 < m) (p q : Fin m → ℂ)
    (h : ∀ i j, Complex.normSq (p i - p j) = Complex.normSq (q i - q j)) :
    ∃ reflected : Bool, ∃ u c : ℂ, Complex.normSq u = 1 ∧
      ∀ i, q i = u * (if reflected then conj (p i) else p i) + c := by
  classical
  let a : Fin m := ⟨0, hm⟩
  by_cases hp : ∀ i, p i = p a
  · have hq : ∀ i, q i = q a := by
      intro i
      have hi := h i a
      rw [hp i, sub_self, Complex.normSq_zero] at hi
      exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hi.symm)
    refine ⟨false, 1, q a - p a, Complex.normSq_one, ?_⟩
    intro i
    simp only [Bool.false_eq_true, if_false, one_mul]
    rw [hp i, hq i]
    ring
  · push_neg at hp
    obtain ⟨b, hb⟩ := hp
    have hpba : p b - p a ≠ 0 := sub_ne_zero.mpr hb
    have hqba : q b - q a ≠ 0 := by
      intro hz
      have hz' : Complex.normSq (q b - q a) = 0 := by rw [hz, Complex.normSq_zero]
      have hpzero : Complex.normSq (p b - p a) = 0 := (h b a).trans hz'
      exact hpba (Complex.normSq_eq_zero.mp hpzero)
    let P : Fin m → ℂ := fun i ↦ (p i - p a) / (p b - p a)
    let Q : Fin m → ℂ := fun i ↦ (q i - q a) / (q b - q a)
    have hden : Complex.normSq (p b - p a) = Complex.normSq (q b - q a) := h b a
    have hPsub (i j : Fin m) :
        P i - P j = (p i - p j) / (p b - p a) := by
      dsimp only [P]
      field_simp
      ring
    have hQsub (i j : Fin m) :
        Q i - Q j = (q i - q j) / (q b - q a) := by
      dsimp only [Q]
      field_simp
      ring
    have hPQ (i j : Fin m) :
        Complex.normSq (P i - P j) = Complex.normSq (Q i - Q j) := by
      rw [hPsub, hQsub, Complex.normSq_div, Complex.normSq_div, h i j, hden]
    have hPa : P a = 0 := by simp [P, hpba]
    have hQa : Q a = 0 := by simp [Q, hqba]
    have hPb : P b = 1 := by simp [P, hpba]
    have hQb : Q b = 1 := by simp [Q, hqba]
    have hcoordinates (i : Fin m) :
        (P i).re = (Q i).re ∧ (P i).im ^ 2 = (Q i).im ^ 2 := by
      apply normalized_two_centres (P i) (Q i)
      · simpa [hPa, hQa] using hPQ i a
      · simpa [hPb, hQb] using hPQ i b
    by_cases hline : ∀ i, (P i).im = 0
    · have hPQeq : ∀ i, Q i = P i := by
        intro i
        apply Complex.ext
        · exact (hcoordinates i).1.symm
        · have hqi : (Q i).im = 0 := by
            have := (hcoordinates i).2
            rw [hline i] at this
            nlinarith
          rw [hqi, hline i]
      refine ⟨false, (q b - q a) / (p b - p a),
        q a - ((q b - q a) / (p b - p a)) * p a, ?_, ?_⟩
      · rw [Complex.normSq_div, hden]
        apply div_self
        simpa only [ne_eq, Complex.normSq_eq_zero] using hqba
      · intro i
        simp only [Bool.false_eq_true, if_false]
        have hi := hPQeq i
        dsimp only [P, Q] at hi
        exact affine_of_normalized_eq (p i) (q i) (p a) (q a) (p b) (q b)
          hpba hqba hi
    · push_neg at hline
      obtain ⟨k, hk⟩ := hline
      have hkcases : (P k).im = (Q k).im ∨ (P k).im = -(Q k).im := by
        exact (sq_eq_sq_iff_eq_or_eq_neg).mp (hcoordinates k).2
      rcases hkcases with hksame | hkopposite
      · have hPQeq : ∀ i, Q i = P i := by
          intro i
          apply Complex.ext
          · exact (hcoordinates i).1.symm
          · exact (same_im_of_three_centres (P i) (Q i) (P k) (Q k)
              (hcoordinates i).1 (hcoordinates k).1 (hcoordinates i).2 hksame hk
              (hPQ i k)).symm
        refine ⟨false, (q b - q a) / (p b - p a),
          q a - ((q b - q a) / (p b - p a)) * p a, ?_, ?_⟩
        · rw [Complex.normSq_div, hden]
          apply div_self
          simpa only [ne_eq, Complex.normSq_eq_zero] using hqba
        · intro i
          simp only [Bool.false_eq_true, if_false]
          have hi := hPQeq i
          dsimp only [P, Q] at hi
          exact affine_of_normalized_eq (p i) (q i) (p a) (q a) (p b) (q b)
            hpba hqba hi
      · have hPQconj : ∀ i, Q i = conj (P i) := by
          intro i
          apply Complex.ext
          · simpa using (hcoordinates i).1.symm
          · have him := opposite_im_of_three_centres (P i) (Q i) (P k) (Q k)
                (hcoordinates i).1 (hcoordinates k).1 (hcoordinates i).2 hkopposite hk
                (hPQ i k)
            rw [Complex.conj_im]
            linarith
        refine ⟨true, (q b - q a) / conj (p b - p a),
          q a - ((q b - q a) / conj (p b - p a)) * conj (p a), ?_, ?_⟩
        · rw [Complex.normSq_div, Complex.normSq_conj, hden]
          apply div_self
          simpa only [ne_eq, Complex.normSq_eq_zero] using hqba
        · intro i
          simp only [if_true]
          have hi := hPQconj i
          dsimp only [P, Q] at hi
          have hi' : (q i - q a) / (q b - q a) =
              (conj (p i) - conj (p a)) / (conj (p b) - conj (p a)) := by
            calc
              _ = conj ((p i - p a) / (p b - p a)) := hi
              _ = _ := by rw [RCLike.conj_div, map_sub, map_sub]
          have hpba' : conj (p b) - conj (p a) ≠ 0 := by
            intro hz
            apply hpba
            apply Complex.normSq_eq_zero.mp
            rw [← Complex.normSq_conj, show conj (p b - p a) = 0 by
              simpa only [map_sub] using hz, Complex.normSq_zero]
          have hrigid : q i = (q b - q a) / (conj (p b) - conj (p a)) * conj (p i) +
              (q a - (q b - q a) / (conj (p b) - conj (p a)) * conj (p a)) :=
            affine_of_normalized_eq (conj (p i)) (q i) (conj (p a)) (q a)
              (conj (p b)) (q b) hpba' hqba hi'
          simpa only [map_sub] using hrigid

/-- Fintype-indexed form of `exists_complex_rigid_of_normSq_eq`. -/
theorem exists_complex_rigid_of_fintype_normSq_eq
    {ι : Type*} [Fintype ι] [Nonempty ι] (p q : ι → ℂ)
    (h : ∀ i j, Complex.normSq (p i - p j) = Complex.normSq (q i - q j)) :
    ∃ reflected : Bool, ∃ u c : ℂ, Complex.normSq u = 1 ∧
      ∀ i, q i = u * (if reflected then conj (p i) else p i) + c := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  obtain ⟨reflected, u, c, hu, hrigid⟩ :=
    exists_complex_rigid_of_normSq_eq hcard (p ∘ e) (q ∘ e) fun i j ↦ h (e i) (e j)
  refine ⟨reflected, u, c, hu, fun i ↦ ?_⟩
  simpa [e] using hrigid ((Fintype.equivFin ι) i)

end Erdos232
