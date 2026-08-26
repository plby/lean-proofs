/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The determinant divisor from finitely many diagonal surface residue classes.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.DiagonalExpansion
import ErdosProblems.Erdos477.Counting.ResidueDeterminant

namespace Erdos477.Counting

open scoped BigOperators

variable {R κ : Type*} [CommRing R] [Fintype κ]

/-- Combine all occupied residue classes of an affine diagonal sextic. The
bound uses their number, with no distribution hypothesis on the points. -/
theorem pow_dvd_diagonal_eval_det_residues [IsLocalRing R] [BinomialRing R]
    {s : ℕ} (a : R) (ha : 6 * a = 1) (p : R) (hp : ¬ IsUnit p)
    (b : Fin 3 → Rˣ) (c : R) (hc : IsUnit c) (center : κ → Fin 3 → R)
    (hcenter : ∀ t, ∑ k, (b k : R) * center t k ^ 6 = c)
    (g : Fin s → κ) (z : Fin s → Fin 3 → R)
    (hres : ∀ j k, p ∣ z j k - center (g j) k)
    (hz : ∀ j, ∑ k, (b k : R) * z j k ^ 6 = c)
    (F : Fin s → MvPolynomial (Fin 3) R) (m : ℕ) :
    p ^ residueExponent (Fintype.card κ) s m ∣
      Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) := by
  classical
  let N := residueExponent (Fintype.card κ) s m
  choose e H hH using fun t =>
    exists_diagonal_expansion a ha p hp b c hc (center t) (hcenter t) N
  choose x hx using fun j => hres j (e (g j) 0)
  choose y hy using fun j => hres j (e (g j) 1)
  apply pow_dvd_det_of_piecewise_expansion p _ (fun i t => H t (F i)) g x y m N le_rfl
  intro i j
  have h := hH (g j) (z j) (hres j) (hz j) (F i)
  rwa [hx j, hy j] at h

#print axioms pow_dvd_diagonal_eval_det_residues
-- 'Erdos477.Counting.pow_dvd_diagonal_eval_det_residues' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
