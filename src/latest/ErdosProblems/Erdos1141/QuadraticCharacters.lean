import ErdosProblems.Erdos1141.CompositeCharacterSums
import BoundedGaps.BombieriVinogradov.Analytic.ImprimitivePolyaVinogradovPrefix

/-!
# Dirichlet characters attached to the complete-sum estimates
-/

open scoped BigOperators

namespace Erdos1141.CharacterSums

variable {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise fun i j ↦ (p i).Coprime (p j))

lemma primeProductCharacter_eq_zero_of_not_isUnit (x : ZMod (∏ i, p i))
    (hx : ¬ IsUnit x) : primeProductCharacter p hc x = 0 := by
  classical
  by_contra hnonzero
  have heach : ∀ i, ZMod.prodEquivPi p hc x i ≠ 0 := by
    intro i hi
    apply hnonzero
    unfold primeProductCharacter
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, MulChar.map_zero])
  apply hx
  apply isUnit_iff_exists_inv.mpr
  refine ⟨(ZMod.prodEquivPi p hc).symm (fun i ↦ (ZMod.prodEquivPi p hc x i)⁻¹), ?_⟩
  apply (ZMod.prodEquivPi p hc).injective
  ext i
  simp only [map_mul, RingEquiv.apply_symm_apply, map_one, Pi.mul_apply, Pi.one_apply]
  exact mul_inv_cancel₀ (heach i)

/-- The CRT product, packaged as a multiplicative character. -/
noncomputable def primeProductMulChar : DirichletCharacter ℤ (∏ i, p i) where
  toFun := primeProductCharacter p hc
  map_one' := by
    unfold primeProductCharacter
    simp only [map_one, Pi.one_apply, Finset.prod_const_one]
  map_mul' := primeProductCharacter_mul p hc
  map_nonunit' := primeProductCharacter_eq_zero_of_not_isUnit p hc

/-- The same character with complex values, for the analytic library. -/
noncomputable def primeProductDirichletCharacter : DirichletCharacter ℂ (∏ i, p i) :=
  (primeProductMulChar p hc).ringHomComp (Int.castRingHom ℂ)

@[simp]
lemma primeProductDirichletCharacter_apply (x : ZMod (∏ i, p i)) :
    primeProductDirichletCharacter p hc x = (primeProductCharacter p hc x : ℂ) := rfl

lemma primeProductMulChar_isQuadratic : (primeProductMulChar p hc).IsQuadratic := by
  intro x
  have hb := abs_primeProductCharacter_le_one p hc x
  have hi : |primeProductCharacter p hc x| ≤ 1 := by exact_mod_cast hb
  have hbounds := abs_le.mp hi
  change primeProductCharacter p hc x = 0 ∨ primeProductCharacter p hc x = 1 ∨
    primeProductCharacter p hc x = -1
  omega

lemma primeProductDirichletCharacter_isQuadratic :
    (primeProductDirichletCharacter p hc).IsQuadratic :=
  (primeProductMulChar_isQuadratic p hc).comp _

lemma primeProductDirichletCharacter_prefix_bound
    (hq : 1 < ∏ i, p i) (hχ : primeProductDirichletCharacter p hc ≠ 1) (N : ℕ) :
    |∑ n ∈ Finset.Icc 1 N, (primeProductCharacter p hc (n : ZMod (∏ i, p i)) : ℝ)| ≤
      2 * Real.sqrt (∏ i, p i : ℕ) * Real.log (∏ i, p i : ℕ) := by
  have h := BoundedGaps.Maynard.norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    hq (primeProductDirichletCharacter p hc) hχ N
  simp only [BoundedGaps.Maynard.dirichletCharacterIntervalSum,
    primeProductDirichletCharacter_apply] at h
  rw [← Int.cast_sum, Complex.norm_intCast] at h
  rw [← Int.cast_sum]
  exact h

end Erdos1141.CharacterSums
