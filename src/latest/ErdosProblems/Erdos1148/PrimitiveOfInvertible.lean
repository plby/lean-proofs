import ErdosProblems.Erdos1148.PrimitiveOfOptimal
import ErdosProblems.Erdos1148.InvertibleFormIdeal

/-! # Invertibility and primitivity of the form ideal -/

namespace Erdos1148.DukeArithmetic

open scoped nonZeroDivisors

lemma fractionalIdealUnit_multiplier_mem_one {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I : (FractionalIdeal R⁰ K)ˣ) (w : K)
    (hw : ∀ z ∈ (I : FractionalIdeal R⁰ K), w * z ∈ (I : FractionalIdeal R⁰ K)) :
    w ∈ (1 : FractionalIdeal R⁰ K) := by
  have hle : FractionalIdeal.spanSingleton R⁰ w * (I : FractionalIdeal R⁰ K) ≤
      (I : FractionalIdeal R⁰ K) := FractionalIdeal.spanSingleton_mul_le_iff.mpr hw
  have hinv : (I : FractionalIdeal R⁰ K) * (↑I⁻¹ : FractionalIdeal R⁰ K) = 1 := by
    exact_mod_cast I.mul_inv
  have hmul := mul_le_mul' hle (le_refl (↑I⁻¹ : FractionalIdeal R⁰ K))
  apply FractionalIdeal.spanSingleton_le_iff_mem.mp
  simpa only [mul_assoc, hinv, mul_one] using hmul

theorem primitiveIntegralForm_of_formFractionalIdeal_isUnit {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (ha : t.1 ≠ 0)
    (hI : IsUnit (formFractionalIdeal ht ha)) : PrimitiveIntegralForm t := by
  apply primitiveIntegralForm_of_optimal ht ha
  apply le_antisymm
  · intro w hw
    have hm : w ∈ latticeMultiplierRing (formIdealLattice (d := d) t ha) := by
      rw [formIdealLattice_multiplier_ring ht ha]
      exact hw
    have hm' : ∀ z ∈ (hI.unit : FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d)),
        w * z ∈ (hI.unit : FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d)) := by
      rw [hI.unit_spec]
      exact hm
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff (quadraticOrder d)⁰).mp
      (fractionalIdealUnit_multiplier_mem_one hI.unit w hm')
    change (r : QuadraticDiscrAlgebra d) = w at hr
    rw [← hr]
    exact r.2
  · exact quadraticOrder_le_integral_preimage ht

theorem formFractionalIdeal_isUnit_iff {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (ha : t.1 ≠ 0) :
    IsUnit (formFractionalIdeal ht ha) ↔ PrimitiveIntegralForm t :=
  ⟨primitiveIntegralForm_of_formFractionalIdeal_isUnit ht ha,
    fun hp => formFractionalIdeal_isUnit ht hp ha⟩

end Erdos1148.DukeArithmetic
