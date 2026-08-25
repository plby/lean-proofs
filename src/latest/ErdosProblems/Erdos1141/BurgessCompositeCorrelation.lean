import ErdosProblems.Erdos1141.QuadraticCRT
import ErdosProblems.Erdos1141.BurgessGcdAverage

/-!
# Complete composite correlations with gcd losses

A distinguished shift gives a simple root at every prime which does not
divide one of its differences from the other shifts. The remaining local
factors are bounded trivially and charged to these gcds.
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem simpleRootConstant_one_le (n : ℕ) : 1 ≤ Stepanov.simpleRootConstant n := by
  unfold Stepanov.simpleRootConstant
  omega

theorem local_correlation_le_gcd {p : ℕ} (hp : p.Prime) [NeZero p]
    {n : ℕ} (v : Fin n → ℕ) (i : Fin n) :
    |∑ x : ZMod p, localChar p hp (∏ j : Fin n, (x + v j))| ≤
      (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p *
        ∏ j ∈ Finset.univ.erase i, (p.gcd (Nat.dist (v i) (v j)) : ℝ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let g : Fin n → ℕ := fun j => p.gcd (Nat.dist (v i) (v j))
  have hg : ∀ j : Fin n, 1 ≤ g j := fun j => Nat.gcd_pos_of_pos_left _ hp.pos
  have hprod : (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (g j : ℝ) := by
    exact_mod_cast Finset.one_le_prod' (s := Finset.univ.erase i) (fun j _ => hg j)
  have hbase : (1 : ℝ) ≤ (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p := by
    have hC : (1 : ℝ) ≤ Stepanov.simpleRootConstant n := by
      exact_mod_cast simpleRootConstant_one_le n
    have hS : (1 : ℝ) ≤ Real.sqrt p :=
      Real.one_le_sqrt.mpr (by exact_mod_cast hp.one_lt.le)
    nlinarith
  by_cases hsingle : ∀ j : Fin n, j ≠ i → (v j : ZMod p) ≠ v i
  · have hcorr := correlation_le_of_singleton (fun j => (v j : ZMod p)) ⟨i, hsingle⟩
    exact hcorr.trans (le_mul_of_one_le_right (le_trans zero_le_one hbase) hprod)
  · push Not at hsingle
    obtain ⟨j, hji, hval⟩ := hsingle
    have hdiv : p ∣ Nat.dist (v i) (v j) :=
      (modEq_iff_dvd_dist p (v i) (v j)).mp
        ((ZMod.natCast_eq_natCast_iff _ _ _).mp hval.symm)
    have hgj : g j = p := Nat.gcd_eq_left_iff_dvd.mpr hdiv
    have hpProd : (p : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (g j : ℝ) := by
      have h := Finset.single_le_prod' (s := Finset.univ.erase i)
        (fun j _ => hg j) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      rw [hgj] at h
      exact_mod_cast h
    have htrivial : |∑ x : ZMod p, localChar p hp (∏ j : Fin n, (x + v j))| ≤ p := by
      calc
        _ ≤ ∑ x : ZMod p, |localChar p hp (∏ j : Fin n, (x + v j))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _x : ZMod p, (1 : ℝ) :=
          Finset.sum_le_sum fun x _ => abs_localChar_le_one p hp _
        _ = _ := by simp
    exact htrivial.trans (hpProd.trans
      (le_mul_of_one_le_left (le_trans zero_le_one hprod) hbase))

theorem product_correlation_le_gcd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] {n : ℕ} (v : Fin n → ℕ) (i : Fin n) :
    |∑ x : ZMod (primeModulus s), productChar s hs (∏ j : Fin n, (x + v j))| ≤
      (Stepanov.simpleRootConstant n : ℝ) ^ s.card * Real.sqrt (primeModulus s) *
        ∏ j ∈ Finset.univ.erase i, ((primeModulus s).gcd (Nat.dist (v i) (v j)) : ℝ) := by
  classical
  have : (p : s) → NeZero (p : ℕ) := fun p => ⟨(hs p p.property).ne_zero⟩
  rw [productChar_complete_correlation s hs v, Finset.abs_prod]
  refine (Finset.prod_le_prod (s := (Finset.univ : Finset s)) (fun _ _ => abs_nonneg _)
    (fun (p : s) _ => local_correlation_le_gcd (hs p p.property) v i)).trans_eq ?_
  simp only [Finset.prod_mul_distrib]
  have hC : (∏ _p : s, (Stepanov.simpleRootConstant n : ℝ)) =
      (Stepanov.simpleRootConstant n : ℝ) ^ s.card := by simp
  have hsqrt : (∏ p : s, Real.sqrt (p : ℕ)) = Real.sqrt (primeModulus s) := by
    rw [← Real.sqrt_prod _ (fun p _ => Nat.cast_nonneg _), ← Nat.cast_prod]
    congr 2
    exact Finset.prod_attach s (fun p : ℕ => p)
  have hgcd : (∏ p : s, ∏ j ∈ Finset.univ.erase i,
        ((p : ℕ).gcd (Nat.dist (v i) (v j)) : ℝ)) =
      ∏ j ∈ Finset.univ.erase i, ((primeModulus s).gcd (Nat.dist (v i) (v j)) : ℝ) := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    rw [← Nat.cast_prod]
    congr 1
    exact (Finset.prod_coe_sort s (fun p : ℕ => p.gcd (Nat.dist (v i) (v j)))).trans
      (prod_prime_gcd s hs _)
  rw [hC, hsqrt, hgcd]

end Pollack17.Burgess
