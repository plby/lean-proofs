/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Auxiliary polynomials of decreasing degree in prime-power residue classes.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.AuxiliaryPolynomial
import ErdosProblems.Erdos477.Counting.CongruenceDegree
import ErdosProblems.Erdos477.Counting.OptimizedCongruence

namespace Erdos477.Counting

open scoped BigOperators

theorem exists_sextic_congruence_auxiliary (c : ℤ) (hc : c ≠ 0)
    (p : ℕ) [Fact p.Prime] (h6 : p.Coprime 6) (hpc : ¬ (p : ℤ) ∣ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : ℝ) (r : ℕ), 1 ≤ B →
      (p : ℝ) ^ r ≤ B ^ ((41 : ℝ) / 100) →
      ∀ (center : Fin 3 → ℤ), center 0 ^ 6 + center 1 ^ 6 - center 2 ^ 6 = c →
      ∃ P : MvPolynomial (Fin 3) ℤ, P ≠ 0 ∧ P.degreeOf 2 ≤ 5 ∧
        (P.totalDegree : ℝ) ≤ K * B ^ ((41 : ℝ) / 100) / (p : ℝ) ^ r ∧
        ¬ sexticSurface c ∣ P ∧
        ∀ z : Fin 3 → ℤ, z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c →
          (∀ k, |(z k : ℝ)| ≤ B) → (∀ k, (p : ℤ) ^ r ∣ z k - center k) →
          MvPolynomial.eval z P = 0 := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_global_det_lower_sqrt_congruence c hc p h6 hpc
  obtain ⟨K, hK, hdegree⟩ := exists_sextic_congruence_degree_bound C hC
  refine ⟨K, hK, ?_⟩
  intro B r hB hqB center hcenter
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hq1 : (1 : ℝ) ≤ (p : ℝ) ^ r := one_le_pow₀ hp1
  obtain ⟨n, hn, hsmall⟩ := hdegree B ((p : ℝ) ^ r) hB hq1 hqB
  let s := Fintype.card (SexticMonomial n)
  let S := (sexticBox c B).filter (fun z => ∀ k, (p : ℤ) ^ r ∣ z k - center k)
  have hdet (z : Fin s → Fin 3 → ℤ) (hz : ∀ j, z j ∈ S) :
      (sexticEvaluationMatrix n z).det = 0 := by
    by_contra hD
    have hpoints (j) := (mem_sexticBox c B (z j)).mp (Finset.mem_filter.mp (hz j)).1
    have hres (j k) := (Finset.mem_filter.mp (hz j)).2 k
    have hs : 0 < s := by dsimp only [s]; rw [card_sexticMonomial]; omega
    let M := sexticEvaluationMatrix n z
    let φ : ℤ →+* ℝ := Int.castRingHom ℝ
    let Mr : Matrix (Fin s) (Fin s) ℝ := M.map φ
    have hmap : (M.det : ℝ) = Mr.det := φ.map_det M
    have hMr : Mr.det ≠ 0 := by rw [← hmap]; exact_mod_cast hD
    have hentry (i j : Fin s) : |Mr i j| ≤ B ^ sexticDegree (sexticIndex n i) :=
      abs_eval_sexticPolynomial_le (sexticIndex n i) (z j) B
        (by linarith) (hpoints j).2
    have hw : (∑ i : Fin s, sexticDegree (sexticIndex n i)) = sexticWeight n :=
      (sexticIndex n).sum_comp sexticDegree
    have hupp := log_abs_det_le hs Mr hMr B (by linarith)
      (fun i => sexticDegree (sexticIndex n i)) hentry
    rw [← hmap, hw] at hupp
    have hlow := hbound s r hs center hcenter z hres (fun j => (hpoints j).1)
      (fun i => sexticPolynomial (sexticIndex n i)) hD
    rw [Real.log_pow] at hsmall
    have hsmall' : (s : ℝ) * Real.log s + sexticWeight n * Real.log B <
        Real.sqrt 2 / 3 * s * Real.sqrt s * (Real.log s + 2 * r * Real.log p) -
          C * s * Real.sqrt s - 3 * s * r * Real.log p := by
      convert hsmall using 1
      ring
    exact (not_lt_of_ge hupp) (hsmall'.trans_le hlow)
  obtain ⟨v, hv, heval⟩ := exists_sextic_combination_of_det_eq_zero n S hdet
  refine ⟨sexticCombination v, sexticCombination_ne_zero v hv,
    degreeOf_sexticCombination v, ?_, sexticSurface_not_dvd_combination c v hv, ?_⟩
  · have hd : ((sexticCombination v).totalDegree : ℝ) ≤ (n : ℝ) + 5 := by
      exact_mod_cast totalDegree_sexticCombination v
    exact hd.trans hn
  · intro z hz hheight hres
    exact heval z (Finset.mem_filter.mpr ⟨(mem_sexticBox c B z).mpr ⟨hz, hheight⟩, hres⟩)

#print axioms exists_sextic_congruence_auxiliary
-- 'Erdos477.Counting.exists_sextic_congruence_auxiliary' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
