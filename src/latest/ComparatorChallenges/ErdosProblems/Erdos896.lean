/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos896

def box (N : ℕ) : Finset ℕ := Finset.Icc 1 N

def representationCount (A B : Finset ℕ) (m : ℕ) : ℕ :=
  ((A.product B).filter fun p ↦ p.1 * p.2 = m).card

def uniqueProducts (A B : Finset ℕ) : Finset ℕ :=
  ((A.product B).image fun p ↦ p.1 * p.2).filter fun m ↦
    representationCount A B m = 1

def F (A B : Finset ℕ) : ℕ := (uniqueProducts A B).card

def maxF (N : ℕ) : ℕ :=
  ((box N).powerset.product (box N).powerset).sup fun p ↦ F p.1 p.2

noncomputable def delta896 : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

noncomputable def logDenom896R (x : ℝ) : ℝ :=
  (Real.log x) ^ delta896 *
    (Real.log (Real.log x)) ^ (3 / 2 : ℝ)

noncomputable def logDenom896 (N : ℕ) : ℝ :=
  logDenom896R N

noncomputable def scale896 (N : ℕ) : ℝ :=
  (N : ℝ) ^ (2 : ℕ) / logDenom896 N

theorem erdos_896 :
    (fun N : ℕ ↦ (maxF N : ℝ)) =Θ[atTop] scale896 := by
  sorry

end Erdos896
