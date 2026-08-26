import ErdosProblems.Erdos1148.QuadraticOrderIntegers
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-! # The discriminant of the order basis inside the ring of integers -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped nonZeroDivisors

lemma quadraticOrderBasis_zero {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (quadraticOrderBasis ht 0 : QuadraticDiscrAlgebra d) = 1 := by
  simp [quadraticOrderBasis, quadraticOrderParam, Pi.basisFun_apply]

lemma quadraticOrderBasis_one {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (quadraticOrderBasis ht 1 : QuadraticDiscrAlgebra d) = quadraticOrderGenerator d := by
  simp [quadraticOrderBasis, quadraticOrderParam, Pi.basisFun_apply]

lemma quadraticDiscrAlgebra_trace (d : ℤ) (x : QuadraticDiscrAlgebra d) :
    Algebra.trace ℚ (QuadraticDiscrAlgebra d) x = 2 * x.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (d : ℚ) 0)]
  simp [Matrix.trace, Fin.sum_univ_two, Algebra.leftMulMatrix_eq_repr_mul,
    QuadraticAlgebra.basis]
  ring

theorem quadraticOrderBasis_rat_discr {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Algebra.discr ℚ (fun i => (quadraticOrderBasis ht i : QuadraticDiscrAlgebra d)) = d := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, quadraticOrderBasis_zero,
    quadraticOrderBasis_one, quadraticDiscrAlgebra_trace]
  simp [quadraticOrderGenerator, QuadraticAlgebra.re_one]
  ring

lemma discr_integerFamily_eq_rat {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → 𝓞 K) :
    (Algebra.discr ℤ b : ℚ) = Algebra.discr ℚ (fun i => (b i : K)) := by
  change algebraMap ℤ ℚ (Algebra.discr ℤ b) = _
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have h := Algebra.trace_localization ℤ ℤ⁰ (Rₘ := ℚ) (Sₘ := K) (b i * b j)
  simpa only [map_mul] using h.symm

theorem quadraticOrderBasis_integer_discr {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Algebra.discr ℤ (fun i => quadraticOrderToIntegers ht (quadraticOrderBasis ht i)) = d := by
  apply Int.cast_injective (α := ℚ)
  rw [discr_integerFamily_eq_rat]
  exact quadraticOrderBasis_rat_discr ht

end Erdos1148.DukeArithmetic
