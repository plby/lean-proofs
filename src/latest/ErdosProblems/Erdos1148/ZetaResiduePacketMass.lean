import ErdosProblems.Erdos1148.OrderIndexPacketMass
import ErdosProblems.Erdos1148.QuadraticZetaResidue

/-! # Isolating the Dedekind-zeta residue in the packet-volume bound -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped ENNReal

lemma sqrt_discr_eq_orderIndex_mul_sqrt_field {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Real.sqrt (d : ℝ) = (quadraticOrderIndex ht : ℝ) *
      Real.sqrt (NumberField.discr (QuadraticDiscrAlgebra d) : ℝ) := by
  have h : (quadraticOrderIndex ht : ℝ) ^ 2 *
      (NumberField.discr (QuadraticDiscrAlgebra d) : ℝ) = d := by
    exact_mod_cast quadraticOrderIndex_sq_mul_field_discr ht
  rw [← h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

lemma quadraticOrderIndex_le_discr {d : ℤ} [Fact (¬IsSquare d)]
    (hd : 0 < d) {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (quadraticOrderIndex ht : ℝ) ≤ d := by
  have hf : (1 : ℤ) ≤ quadraticOrderIndex ht := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (quadraticOrderIndex_ne_zero ht)
  have hD : (1 : ℤ) ≤ NumberField.discr (QuadraticDiscrAlgebra d) :=
    quadraticDiscrAlgebra_field_discr_pos hd ht
  have h := quadraticOrderIndex_sq_mul_field_discr ht
  have hs : (quadraticOrderIndex ht : ℤ) ^ 2 ≤ d := by
    nlinarith [sq_nonneg (quadraticOrderIndex ht : ℤ)]
  have hfd : (quadraticOrderIndex ht : ℤ) ≤ d := by nlinarith
  exact_mod_cast hfd

theorem exists_zetaResidue_packetMass_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℤ) [hns : Fact (¬IsSquare d)] (hd : 0 < d)
      (_base : PrimitiveIntegralFormOrbits d),
      ENNReal.ofReal (c * NumberField.dedekindZeta_residue (QuadraticDiscrAlgebra d) *
        (d : ℝ) ^ (1 / 2 - ε)) ≤ discriminantPacket hd hns.out Set.univ := by
  obtain ⟨c, hc, hbound⟩ := exists_orderIndex_packetMass_lower_bound hε
  refine ⟨c, hc, ?_⟩
  intro d hns hd base
  have hf : (0 : ℝ) < quadraticOrderIndex base.1.out.2 := by
    exact_mod_cast Nat.pos_of_ne_zero (quadraticOrderIndex_ne_zero base.1.out.2)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hres := NumberField.dedekindZeta_residue_pos (QuadraticDiscrAlgebra d)
  have hmass := hbound d hd base
  have hscale : (Nat.card (ClassGroup (𝓞 (QuadraticDiscrAlgebra d))) : ℝ) *
      (c * (quadraticOrderIndex base.1.out.2 : ℝ) ^ (1 - ε)) *
        (2 * NumberField.Units.regulator (QuadraticDiscrAlgebra d)) =
      c * NumberField.dedekindZeta_residue (QuadraticDiscrAlgebra d) * Real.sqrt (d : ℝ) *
        (quadraticOrderIndex base.1.out.2 : ℝ) ^ (-ε) := by
    rw [Real.rpow_sub hf, Real.rpow_one, Real.rpow_neg hf.le,
      sqrt_discr_eq_orderIndex_mul_sqrt_field base.1.out.2, div_eq_mul_inv]
    have hr := quadraticField_zeta_residue_mul_sqrt hd base.1.out.2
    linear_combination -(c * (quadraticOrderIndex base.1.out.2 : ℝ) *
      ((quadraticOrderIndex base.1.out.2 : ℝ) ^ ε)⁻¹) * hr
  have hmass' : ENNReal.ofReal (c * NumberField.dedekindZeta_residue (QuadraticDiscrAlgebra d) *
      Real.sqrt (d : ℝ) * (quadraticOrderIndex base.1.out.2 : ℝ) ^ (-ε)) ≤
        discriminantPacket hd hns.out Set.univ := by
    rw [← hscale, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    exact hmass
  have hpow : (d : ℝ) ^ (-ε) ≤ (quadraticOrderIndex base.1.out.2 : ℝ) ^ (-ε) :=
    Real.rpow_le_rpow_of_nonpos hf (quadraticOrderIndex_le_discr hd base.1.out.2) (by linarith)
  have hnum : c * NumberField.dedekindZeta_residue (QuadraticDiscrAlgebra d) *
      (d : ℝ) ^ (1 / 2 - ε) ≤
      c * NumberField.dedekindZeta_residue (QuadraticDiscrAlgebra d) * Real.sqrt (d : ℝ) *
        (quadraticOrderIndex base.1.out.2 : ℝ) ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hdR, ← Real.sqrt_eq_rpow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  exact (ENNReal.ofReal_le_ofReal hnum).trans hmass'

end Erdos1148.DukeArithmetic
