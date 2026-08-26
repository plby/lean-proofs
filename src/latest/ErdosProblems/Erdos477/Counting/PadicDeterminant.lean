/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Integer determinant divisibility on a sextic surface in residue classes.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.DiagonalResidues

namespace Erdos477.Counting

open scoped BigOperators

/-- The local determinant estimate over the integers, combining finitely
many residue classes of `u^6 + y^6 - x^6 = c` at a prime not dividing `6c`.
This is an unconditional divisibility lemma, not a surface point-count bound. -/
theorem prime_pow_dvd_sextic_eval_det_residues {κ : Type*} [Fintype κ]
    {s : ℕ} (p : ℕ) [Fact p.Prime]
    (r : ℕ) (hr : 0 < r)
    (h6 : p.Coprime 6) (c : ℤ) (hc : ¬ (p : ℤ) ∣ c)
    (center : κ → Fin 3 → ℤ)
    (hcenter : ∀ t, center t 0 ^ 6 + center t 1 ^ 6 - center t 2 ^ 6 = c)
    (g : Fin s → κ) (z : Fin s → Fin 3 → ℤ)
    (hres : ∀ j k, (p : ℤ) ^ r ∣ z j k - center (g j) k)
    (hz : ∀ j, z j 0 ^ 6 + z j 1 ^ 6 - z j 2 ^ 6 = c)
    (F : Fin s → MvPolynomial (Fin 3) ℤ) (m : ℕ) :
    (p : ℤ) ^ (r * residueExponent (Fintype.card κ) s m) ∣
      Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) := by
  let φ : ℤ →+* ℤ_[p] := Int.castRingHom ℤ_[p]
  have hp : ¬ IsUnit (p : ℤ_[p]) := by
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_natCast_lt_one_iff]
  have hpr : ¬ IsUnit ((p : ℤ_[p]) ^ r) :=
    fun h => hp ((isUnit_pow_iff hr.ne').mp h)
  have h6unit : IsUnit (6 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.mpr h6
  obtain ⟨six, hsix⟩ := h6unit
  have ha : (6 : ℤ_[p]) * (six⁻¹ : ℤ_[p]ˣ) = 1 := by
    rw [← hsix]
    exact Units.mul_inv six
  have hcunit : IsUnit (φ c) := by
    apply not_not.mp
    rw [PadicInt.not_isUnit_iff]
    exact (PadicInt.norm_intCast_lt_one_iff (z := c)).not.mpr hc
  let b : Fin 3 → ℤ_[p]ˣ := ![1, 1, -1]
  have hcenter' (t) : ∑ k, (b k : ℤ_[p]) * φ (center t k) ^ 6 = φ c := by
    simp only [Fin.sum_univ_three, b, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Units.val_one, Units.val_neg, one_mul,
      neg_one_mul, ← sub_eq_add_neg]
    simpa only [map_sub, map_add, map_pow] using congrArg φ (hcenter t)
  have hres' (j k) : (p : ℤ_[p]) ^ r ∣ φ (z j k) - φ (center (g j) k) := by
    have h := map_dvd φ (hres j k)
    simpa [φ] using h
  have hz' (j) : ∑ k, (b k : ℤ_[p]) * φ (z j k) ^ 6 = φ c := by
    simp only [Fin.sum_univ_three, b, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Units.val_one, Units.val_neg, one_mul,
      neg_one_mul, ← sub_eq_add_neg]
    simpa only [map_sub, map_add, map_pow] using congrArg φ (hz j)
  let F' : Fin s → MvPolynomial (Fin 3) ℤ_[p] := fun i => MvPolynomial.map φ (F i)
  have h := pow_dvd_diagonal_eval_det_residues ((six⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ha
    ((p : ℤ_[p]) ^ r) hpr b (φ c) hcunit (fun t => φ ∘ center t) hcenter' g
    (fun j => φ ∘ z j) hres' hz' F' m
  have heval (i j) : MvPolynomial.eval (φ ∘ z j) (F' i) =
      φ (MvPolynomial.eval (z j) (F i)) := by
    dsimp only [F']
    rw [MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp]
  have hdet : Matrix.det (Matrix.of fun i j => φ (MvPolynomial.eval (z j) (F i))) =
      φ (Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i))) :=
    (φ.map_det _).symm
  simp only [heval, hdet, ← pow_mul] at h
  exact (PadicInt.pow_p_dvd_int_iff _ _).mp h

/-- The first prime-power level, with any finite set of residue classes. -/
theorem pow_dvd_sextic_eval_det_residues {κ : Type*} [Fintype κ]
    {s : ℕ} (p : ℕ) [Fact p.Prime]
    (h6 : p.Coprime 6) (c : ℤ) (hc : ¬ (p : ℤ) ∣ c)
    (center : κ → Fin 3 → ℤ)
    (hcenter : ∀ t, center t 0 ^ 6 + center t 1 ^ 6 - center t 2 ^ 6 = c)
    (g : Fin s → κ) (z : Fin s → Fin 3 → ℤ)
    (hres : ∀ j k, (p : ℤ) ∣ z j k - center (g j) k)
    (hz : ∀ j, z j 0 ^ 6 + z j 1 ^ 6 - z j 2 ^ 6 = c)
    (F : Fin s → MvPolynomial (Fin 3) ℤ) (m : ℕ) :
    (p : ℤ) ^ residueExponent (Fintype.card κ) s m ∣
      Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) := by
  simpa only [pow_one, one_mul] using prime_pow_dvd_sextic_eval_det_residues
    p 1 (by decide) h6 c hc center hcenter g z (by simpa only [pow_one] using hres) hz F m

/-- Deeper prime-power congruences multiply the local exponent by their depth. -/
theorem prime_pow_dvd_sextic_eval_det {s : ℕ} (p : ℕ) [Fact p.Prime]
    (r : ℕ) (h6 : p.Coprime 6) (c : ℤ) (hc : ¬ (p : ℤ) ∣ c)
    (center : Fin 3 → ℤ) (hcenter : center 0 ^ 6 + center 1 ^ 6 - center 2 ^ 6 = c)
    (z : Fin s → Fin 3 → ℤ) (hres : ∀ j k, (p : ℤ) ^ r ∣ z j k - center k)
    (hz : ∀ j, z j 0 ^ 6 + z j 1 ^ 6 - z j 2 ^ 6 = c)
    (F : Fin s → MvPolynomial (Fin 3) ℤ) (m : ℕ) :
    (p : ℤ) ^ (r * localExponent s m) ∣
      Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) := by
  by_cases hr : 0 < r
  · have h := prime_pow_dvd_sextic_eval_det_residues p r hr h6 c hc
      (fun _ : PUnit.{1} => center) (fun _ => hcenter) (fun _ => PUnit.unit) z hres hz F m
    simpa only [Fintype.card_punit, residueExponent, localExponent, one_mul] using h
  · have hr0 : r = 0 := by omega
    simp only [hr0, zero_mul, pow_zero, one_dvd]

/-- The specialization to one residue class. -/
theorem pow_dvd_sextic_eval_det {s : ℕ} (p : ℕ) [Fact p.Prime]
    (h6 : p.Coprime 6) (c : ℤ) (hc : ¬ (p : ℤ) ∣ c)
    (center : Fin 3 → ℤ) (hcenter : center 0 ^ 6 + center 1 ^ 6 - center 2 ^ 6 = c)
    (z : Fin s → Fin 3 → ℤ) (hres : ∀ j k, (p : ℤ) ∣ z j k - center k)
    (hz : ∀ j, z j 0 ^ 6 + z j 1 ^ 6 - z j 2 ^ 6 = c)
    (F : Fin s → MvPolynomial (Fin 3) ℤ) (m : ℕ) :
    (p : ℤ) ^ localExponent s m ∣
      Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) := by
  have h := pow_dvd_sextic_eval_det_residues p h6 c hc (fun _ : PUnit.{1} => center)
    (fun _ => hcenter) (fun _ => PUnit.unit) z hres hz F m
  simpa only [Fintype.card_punit, residueExponent, localExponent, one_mul] using h

#print axioms pow_dvd_sextic_eval_det_residues
-- 'Erdos477.Counting.pow_dvd_sextic_eval_det_residues' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms pow_dvd_sextic_eval_det
-- 'Erdos477.Counting.pow_dvd_sextic_eval_det' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
