import ErdosProblems.Erdos1148.OrderUnitSubgroup
import ErdosProblems.Erdos1148.QuadraticOrderIndex
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-! # The Dedekind-zeta residue in the positive quadratic field -/

namespace Erdos1148.DukeArithmetic

open NumberField

theorem quadraticField_torsionOrder {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d) :
    NumberField.Units.torsionOrder (QuadraticDiscrAlgebra d) = 2 := by
  have hsub : (NumberField.Units.torsion (QuadraticDiscrAlgebra d) :
      Set (𝓞 (QuadraticDiscrAlgebra d))ˣ) ⊆ {1, -1} := by
    intro u hu
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      quadraticField_torsion_eq_one_or_neg_one hd hu
  have hcard : NumberField.Units.torsionOrder (QuadraticDiscrAlgebra d) ≤ 2 := by
    calc
      _ = (NumberField.Units.torsion (QuadraticDiscrAlgebra d) :
          Set (𝓞 (QuadraticDiscrAlgebra d))ˣ).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, -1} : Set (𝓞 (QuadraticDiscrAlgebra d))ˣ).ncard :=
        Set.ncard_le_ncard hsub (by simp)
      _ ≤ 2 := by simpa using Set.ncard_insert_le (1 : (𝓞 (QuadraticDiscrAlgebra d))ˣ) {-1}
  have hpos := NumberField.Units.torsionOrder_pos (QuadraticDiscrAlgebra d)
  obtain ⟨k, hk⟩ := NumberField.Units.even_torsionOrder (QuadraticDiscrAlgebra d)
  omega

theorem quadraticField_zeta_residue_mul_sqrt {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    NumberField.dedekindZeta_residue (QuadraticDiscrAlgebra d) *
        Real.sqrt (NumberField.discr (QuadraticDiscrAlgebra d) : ℝ) =
      2 * (Nat.card (ClassGroup (𝓞 (QuadraticDiscrAlgebra d))) : ℝ) *
        NumberField.Units.regulator (QuadraticDiscrAlgebra d) := by
  have hD : (0 : ℝ) < NumberField.discr (QuadraticDiscrAlgebra d) := by
    exact_mod_cast quadraticDiscrAlgebra_field_discr_pos hd ht
  rw [NumberField.dedekindZeta_residue_def, quadraticDiscrAlgebra_nrRealPlaces hd,
    quadraticDiscrAlgebra_nrComplexPlaces hd, quadraticField_torsionOrder hd,
    abs_of_pos hD]
  have hs := (Real.sqrt_pos_of_pos hD).ne'
  simp only [pow_zero, pow_two, Nat.cast_ofNat, mul_one, NumberField.classNumber,
    Nat.card_eq_fintype_card]
  field_simp

end Erdos1148.DukeArithmetic
