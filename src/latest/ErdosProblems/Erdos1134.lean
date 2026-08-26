/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
MIT License

Copyright (c) 2026 Axiom Math.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Modified for this repository and Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 1134.
Informal proof: D. J. Crampin and A. J. W. Hilton.
Formal proof: AxiomProver, published by Axiom Math.
Source: https://www.erdosproblems.com/1134#post-7068
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos1134/solution.lean
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
import ErdosProblems.Erdos1134.Dirichlet

namespace Erdos1134

lemma sublinear_bound_implies_density_zero (S : Set ℕ) (C : ℝ) (α : ℝ)
    (hC : 0 < C) (hα : α < 1)
    (hbound : ∀ N : ℕ, 0 < N → (Set.ncard (S ∩ Set.Iic N) : ℝ) ≤ C * (N : ℝ) ^ α) :
    lowerDensity S = 0 := by
  unfold lowerDensity
  have htend : Filter.Tendsto
      (fun N : ℕ => (Set.ncard (S ∩ Set.Iic N) : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) := by
    apply squeeze_zero (f := fun N => (Set.ncard (S ∩ Set.Iic N) : ℝ) / (N : ℝ))
      (g := fun N : ℕ => C * (N : ℝ) ^ (α - 1))
    · intro N
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · intro N
      by_cases hN : N = 0
      · subst hN
        simp only [Nat.cast_zero, div_zero]
        apply mul_nonneg (le_of_lt hC)
        exact Real.rpow_nonneg (le_refl 0) _
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
        have hNcast : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
        have hbound' := hbound N hNpos
        calc (Set.ncard (S ∩ Set.Iic N) : ℝ) / (N : ℝ)
            ≤ (C * (N : ℝ) ^ α) / (N : ℝ) := by
              apply div_le_div_of_nonneg_right hbound' (le_of_lt hNcast)
          _ = C * ((N : ℝ) ^ α / (N : ℝ)) := by ring
          _ = C * (N : ℝ) ^ (α - 1) := by
              rw [Real.rpow_sub_one (ne_of_gt hNcast)]
    · have h1α : 0 < 1 - α := by linarith
      have hαeq : α - 1 = -(1 - α) := by ring
      simp_rw [hαeq]
      rw [show (0 : ℝ) = C * 0 from by ring]
      apply Filter.Tendsto.const_mul
      exact (tendsto_rpow_neg_atTop h1α).comp tendsto_natCast_atTop_atTop
  exact htend.liminf_eq

theorem lower_density_zero : lowerDensity (Set.ofPred ErdosSetA) = 0 := by
  obtain ⟨C, hC, hbound⟩ := erdos_set_sublinear_bound
  exact sublinear_bound_implies_density_zero (Set.ofPred ErdosSetA) C (19/20 : ℝ)
    hC (by norm_num) (fun N _ => hbound N)

theorem not_erdos_1134 : ¬ 0 < lowerDensity (Set.ofPred ErdosSetA) := by
  rw [lower_density_zero]
  exact lt_irrefl 0

#print axioms not_erdos_1134
-- 'Erdos1134.not_erdos_1134' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms lower_density_zero
-- 'Erdos1134.lower_density_zero' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms erdos_set_sublinear_bound
-- 'Erdos1134.erdos_set_sublinear_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos1134
