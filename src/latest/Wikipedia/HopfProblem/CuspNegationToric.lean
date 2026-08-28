import Wikipedia.HopfProblem.CuspNegationFan
import Wikipedia.HopfProblem.CuspNegationPeriods

/-!
# Actual toric fibre negation and corrected lattice equivariance

Central symmetry of the fan and reversal of chart coordinates define a
holomorphic involution of the actual glued toric space. It preserves the
time parameter and conjugates every corrected lattice translation by
`v` to the translation by `-v`, for an arbitrary correction matrix `C`.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspNegation

open ToricCharts ToricFan Triangle ToricSpace

theorem negation_compatible (s t : Triangle) (z : CoordinateSpace 3)
    (hz : z ∈ (chartChange s t).source) :
    inclusion (triangleNeg t) (permute (chartChange s t z)) =
      inclusion (triangleNeg s) (permute z) := by
  apply ((inclusion_eq_iff (triangleNeg s) (triangleNeg t) (permute z) _).mpr ?_).symm
  exact ⟨(chartChange_triangleNeg_source_iff s t z).mpr hz,
    chartChange_triangleNeg_apply s t z⟩

def toricNegation : Space → Space :=
  descend (fun s z => inclusion (triangleNeg s) (permute z))

@[simp] theorem toricNegation_inclusion (s : Triangle) (z : CoordinateSpace 3) :
    toricNegation (inclusion s z) = inclusion (triangleNeg s) (permute z) :=
  descend_inclusion _ negation_compatible s z

theorem toricNegation_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω toricNegation :=
  descend_holomorphic _ _ negation_compatible
    (fun s => (inclusion_holomorphic (triangleNeg s)).comp permute_holomorphic.contMDiff)

theorem toricNegation_involutive : Function.Involutive toricNegation := by
  intro x
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [toricNegation_inclusion, toricNegation_inclusion,
    triangleNeg_involutive s, permute_involutive z]

def toricHomeomorph : Space ≃ₜ Space where
  toFun := toricNegation
  invFun := toricNegation
  left_inv := toricNegation_involutive
  right_inv := toricNegation_involutive
  continuous_toFun := toricNegation_holomorphic.continuous
  continuous_invFun := toricNegation_holomorphic.continuous

@[simp] theorem time_toricNegation (x : Space) : time (toricNegation x) = time x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [toricNegation_inclusion, time_inclusion, time_inclusion, time_permute]

theorem toricNegation_translate (v : Fin 2 → ℤ) (x : Space) :
    toricNegation (translate v x) = translate (-v) (toricNegation x) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [translate_inclusion, toricNegation_inclusion, toricNegation_inclusion,
    translate_inclusion, triangleNeg_shift]

theorem factors_triangleNeg_inverse (s : Triangle) (u : Fin 2 → ℂˣ) :
    factors (triangleNeg s) (fibreMultiplier u⁻¹) = permute (factors s (fibreMultiplier u)) := by
  ext i
  cases hs : s.upper <;> fin_cases i <;>
    simp [factors, monomial, Triangle.dual, triangleNeg, permute, hs, fibreMultiplier,
      Fin.prod_univ_succ, Fin.rev, mul_comm]

theorem permute_scale (s : Triangle) (u : Fin 2 → ℂˣ) (z : CoordinateSpace 3) :
    permute (scale s (fibreMultiplier u) z) =
      scale (triangleNeg s) (fibreMultiplier u⁻¹) (permute z) := by
  ext i
  change factors s (fibreMultiplier u) i.rev * z i.rev =
    factors (triangleNeg s) (fibreMultiplier u⁻¹) i * z i.rev
  rw [factors_triangleNeg_inverse]
  rfl

theorem toricNegation_fibreMultiplier (u : Fin 2 → ℂˣ) (x : Space) :
    toricNegation (torusAction (fibreMultiplier u) x) =
      torusAction (fibreMultiplier u⁻¹) (toricNegation x) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [torusAction_inclusion, toricNegation_inclusion, toricNegation_inclusion,
    torusAction_inclusion, permute_scale]

theorem toricNegation_variableMultiplier (u : ℂ → Fin 2 → ℂˣ) (x : Space) :
    toricNegation (variableMultiplier u x) =
      variableMultiplier (fun t => (u t)⁻¹) (toricNegation x) := by
  simp only [variableMultiplier, toricNegation_fibreMultiplier, time_toricNegation]

theorem toricNegation_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : Space) :
    toricNegation (twistedTranslate C v x) = twistedTranslate C (-v) (toricNegation x) := by
  have he : (fun t => (exponentialMultiplier C v t)⁻¹) =
      exponentialMultiplier C (-v) := funext fun t => (exponentialMultiplier_neg C v t).symm
  rw [twistedTranslate, toricNegation_variableMultiplier, toricNegation_translate,
    he, twistedTranslate, cuspVector_neg]

end Wikipedia.HopfProblem.CuspNegation
