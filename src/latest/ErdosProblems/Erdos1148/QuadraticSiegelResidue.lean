import ErdosProblems.Erdos1148.QuadraticResidueComparison
import ErdosProblems.Erdos1148.PrincipalMeanLowerBound

/-! # An unconditional subpower lower bound for real quadratic zeta residues -/

namespace Erdos1148.DukeArithmetic

theorem exists_quadratic_zetaResidue_lower_bound_nat {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℕ) [NeZero a] [Fact (¬IsSquare (a : ℤ))]
      (t : ℤ × ℤ × ℤ), discr t = (a : ℤ) →
      c * (a : ℝ) ^ (-ε) ≤ NumberField.dedekindZeta_residue (QuadraticDiscrAlgebra (a : ℤ)) := by
  obtain ⟨C, hC, hL⟩ := exists_quadraticDirichlet_siegel_lower_bound (half_pos hε)
  obtain ⟨D, hD, hMean⟩ := exists_principalMean_lower_bound (half_pos hε)
  refine ⟨D * (4 : ℝ) ^ (-(ε / 2)) * C,
    mul_pos (mul_pos hD (Real.rpow_pos_of_pos (by norm_num) _)) hC, ?_⟩
  intro a ha hns t ht
  have haR : (0 : ℝ) < a := by exact_mod_cast NeZero.pos a
  have hnsNat : ¬IsSquare a := by
    rintro ⟨b, hb⟩
    exact hns.out ⟨(b : ℤ), by exact_mod_cast hb⟩
  have h1 := hL a hnsNat
  have h2 := hMean (4 * a) (Nat.mul_ne_zero (by norm_num) (NeZero.ne a))
  have hprod := mul_le_mul h2 h1 (by positivity : 0 ≤ C * (a : ℝ) ^ (-(ε / 2)))
    (principalCharacterMean_nonneg (4 * a))
  apply le_trans _ (quadratic_residue_ge_principalMean_mul_LValue a ht)
  convert hprod using 1
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) haR.le]
  calc
    D * (4 : ℝ) ^ (-(ε / 2)) * C * (a : ℝ) ^ (-ε) =
        (D * (4 : ℝ) ^ (-(ε / 2)) * C) *
          ((a : ℝ) ^ (-(ε / 2)) * (a : ℝ) ^ (-(ε / 2))) := by
      rw [← Real.rpow_add haR, show -(ε / 2) + -(ε / 2) = -ε by ring]
    _ = _ := by ring

theorem exists_quadratic_zetaResidue_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℤ) [Fact (¬IsSquare d)], 0 < d →
      ∀ (t : ℤ × ℤ × ℤ), discr t = d →
      c * (d : ℝ) ^ (-ε) ≤ NumberField.dedekindZeta_residue (QuadraticDiscrAlgebra d) := by
  obtain ⟨c, hc, hbound⟩ := exists_quadratic_zetaResidue_lower_bound_nat hε
  refine ⟨c, hc, ?_⟩
  intro d hns hd t ht
  cases d with
  | ofNat a =>
    change 0 < (a : ℤ) at hd
    have ha : 0 < a := by exact_mod_cast hd
    let : NeZero a := ⟨ha.ne'⟩
    change c * ((a : ℤ) : ℝ) ^ (-ε) ≤
      NumberField.dedekindZeta_residue (QuadraticDiscrAlgebra (a : ℤ))
    simpa only [Int.cast_natCast] using hbound a t ht
  | negSucc a => omega

end Erdos1148.DukeArithmetic
