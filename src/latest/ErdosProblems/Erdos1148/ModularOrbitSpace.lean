import ErdosProblems.Erdos1148.PeriodGroup

/-! # The modular orbit space and its diagonal-flow curves -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

instance integralRealMatrixAction : MulAction SL(2, ℤ) SL(2, ℝ) :=
  MulAction.compHom SL(2, ℝ) (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))

lemma integralRealMatrix_smul (γ : SL(2, ℤ)) (g : SL(2, ℝ)) :
    γ • g = (γ : SL(2, ℝ)) * g := rfl

instance integralRealMatrixProperSMul : ProperSMul SL(2, ℤ) SL(2, ℝ) :=
  properSMul_of_isClosedEmbedding (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
    Int.isClosedEmbedding_coe_real.specialLinearGroup_map (fun _ _ => rfl)

instance realSpecialLinearSecondCountable : SecondCountableTopology SL(2, ℝ) := by
  let : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology

abbrev ModularOrbitSpace := Quotient (MulAction.orbitRel SL(2, ℤ) SL(2, ℝ))

instance modularOrbitSpaceSecondCountable : SecondCountableTopology ModularOrbitSpace :=
  ContinuousConstSMul.secondCountableTopology

instance modularOrbitSpaceMeasurableSpace : MeasurableSpace ModularOrbitSpace :=
  borel ModularOrbitSpace

instance modularOrbitSpaceBorelSpace : BorelSpace ModularOrbitSpace := ⟨rfl⟩

def modularMk (g : SL(2, ℝ)) : ModularOrbitSpace := Quotient.mk _ g

lemma modularMk_eq_iff (g h : SL(2, ℝ)) :
    modularMk g = modularMk h ↔ ∃ γ : SL(2, ℤ), (γ : SL(2, ℝ)) * g = h := by
  constructor
  · intro heq
    exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact heq.symm))
  · rintro ⟨γ, hγ⟩
    apply Eq.symm
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact MulAction.mem_orbit_iff.mpr ⟨γ, hγ⟩

lemma modularMk_integral_mul (γ : SL(2, ℤ)) (g : SL(2, ℝ)) :
    modularMk ((γ : SL(2, ℝ)) * g) = modularMk g :=
  ((modularMk_eq_iff g _).mpr ⟨γ, rfl⟩).symm

lemma modularMk_neg (g : SL(2, ℝ)) : modularMk (-g) = modularMk g := by
  have h := modularMk_integral_mul (-1) g
  simpa using h

lemma continuous_diagonalFlow : Continuous diagonalFlow := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [diagonalFlow] <;> fun_prop

lemma continuous_modularMk : Continuous modularMk := continuous_quotient_mk'

noncomputable def modularFlowCurve (g : SL(2, ℝ)) (t : ℝ) : ModularOrbitSpace :=
  modularMk (g * diagonalFlow t)

lemma continuous_modularFlowCurve (g : SL(2, ℝ)) : Continuous (modularFlowCurve g) :=
  continuous_modularMk.comp (continuous_const.mul continuous_diagonalFlow)

lemma modularFlowCurve_periodic {g : SL(2, ℝ)} {T : ℝ} (hT : T ∈ flowPeriodGroup g) :
    Function.Periodic (modularFlowCurve g) T := by
  obtain ⟨γ, hγ⟩ := hT
  intro s
  change modularMk (g * diagonalFlow (s + T)) = modularMk (g * diagonalFlow s)
  calc
    modularMk (g * diagonalFlow (s + T)) =
        modularMk ((γ : SL(2, ℝ)) * (g * diagonalFlow s)) := by
      congr 1
      rw [add_comm s T, diagonalFlow_add, ← mul_assoc, ← hγ, mul_assoc]
    _ = _ := modularMk_integral_mul γ _

lemma modularFlowCurve_eq_iff (g : SL(2, ℝ)) (s t : ℝ) :
    modularFlowCurve g s = modularFlowCurve g t ↔ t - s ∈ flowPeriodGroup g := by
  rw [modularFlowCurve, modularFlowCurve, modularMk_eq_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    calc
      (γ : SL(2, ℝ)) * g = (γ : SL(2, ℝ)) * (g * diagonalFlow s) * (diagonalFlow s)⁻¹ := by
        simp [mul_assoc]
      _ = (g * diagonalFlow t) * (diagonalFlow s)⁻¹ := by rw [hγ]
      _ = g * diagonalFlow (t - s) := by
        rw [sub_eq_add_neg, diagonalFlow_add, diagonalFlow_neg, mul_assoc]
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    rw [← mul_assoc, hγ, mul_assoc, ← diagonalFlow_add, sub_add_cancel]

end Erdos1148.DukeArithmetic
