import Wikipedia.SmoothSixDPoincare.IntegerPresentationMatrix
import Mathlib.Algebra.BigOperators.Fin

/-!
# Independent retained columns remain independent after adjoining an infinite-order relation

Apply the original presentation map to a linear combination of the new
columns. Every old column vanishes and the new coefficient multiplies the
original quotient relation. Infinite order makes that coefficient zero;
injectivity for the old matrix then makes every remaining coefficient zero.
-/

noncomputable section

open Set Function

namespace Wikipedia.SmoothSixDPoincare.IntegerPresentation

variable {B C : Type*} [AddCommGroup B] [AddCommGroup C] [Module ℤ B] [Module ℤ C]
  {r c : ℕ} (P : IntegerPresentation B r c)

theorem transport_matrix (e : B ≃ₗ[ℤ] C) : (P.transport e).matrix = P.matrix := rfl

theorem ofEquiv_matrix_injective (e : (Fin r → ℤ) ≃ₗ[ℤ] B) :
    Injective (ofEquiv e).matrix.mulVec := fun _ _ _ => Subsingleton.elim _ _

variable (q : B →ₗ[ℤ] C) (hq : Surjective q) (b : B)
  (hker : LinearMap.ker q = Submodule.span ℤ {b})

theorem adjoin_mulVec (z : Fin (c + 1) → ℤ) :
    (P.adjoin q hq b hker).matrix.mulVec z =
      z 0 • P.liftRelation b + P.matrix.mulVec (Fin.tail z) := by
  rw [← (P.adjoin q hq b hker).columns_sum_eq_mulVec, Fin.sum_univ_succ]
  change z 0 • P.liftRelation b + (∑ i, z i.succ • P.columns i) = _
  rw [P.columns_sum_eq_mulVec]
  rfl

theorem adjoin_coefficient (z : Fin (c + 1) → ℤ) :
    P.map ((P.adjoin q hq b hker).matrix.mulVec z) = z 0 • b := by
  rw [P.adjoin_mulVec q hq b hker, map_add, map_zsmul,
    P.map_liftRelation, P.matrix_relation, add_zero]

theorem adjoin_matrix_injective (hP : Injective P.matrix.mulVec)
    (hb : ∀ z : ℤ, z • b = 0 → z = 0) :
    Injective (P.adjoin q hq b hker).matrix.mulVec := by
  have hzero (z : Fin (c + 1) → ℤ)
      (hz : (P.adjoin q hq b hker).matrix.mulVec z = 0) : z = 0 := by
    have hcoeff : z 0 • b = 0 := (P.adjoin_coefficient q hq b hker z).symm.trans
      ((congrArg P.map hz).trans (map_zero P.map))
    have hz0 := hb (z 0) hcoeff
    have htail : P.matrix.mulVec (Fin.tail z) = 0 := by
      rw [P.adjoin_mulVec q hq b hker, hz0, zero_smul, zero_add] at hz
      exact hz
    have hzero' : P.matrix.mulVec (0 : Fin c → ℤ) = 0 := by simp
    have ht : Fin.tail z = 0 := hP (htail.trans hzero'.symm)
    funext i
    exact Fin.cases hz0 (fun j => congrFun ht j) i
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  rw [Matrix.mulVec_sub, hxy, sub_self]

end Wikipedia.SmoothSixDPoincare.IntegerPresentation
