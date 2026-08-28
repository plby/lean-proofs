import Wikipedia.NoExoticSixSphere.RelativeModTwoCochains

/-!
# Degreewise extension from actual subspace cochains

The subspace inclusion is injective on actual singular simplices. Extend
simplex values by zero and use the original singular-chain coproduct to
obtain an ambient cochain. This is a degreewise extension, not a claim
that extension by zero commutes with the coboundary.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- The original subspace map on singular simplices. -/
def simplexInclusion (p : ℕ) (σ : SingularSimplex U p) : SingularSimplex X p :=
  (subtypeInclusion U).comp σ

theorem simplexInclusion_injective (p : ℕ) : Function.Injective (simplexInclusion U p) := by
  intro σ τ he
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact congrArg (fun f : SingularSimplex X p => f t) he

/-- Extend the actual simplex values, with zero on simplices outside the subspace image. -/
def extendByZero (p : ℕ) (α : ModTwoCapProduct.Cochain U p) : ModTwoCapProduct.Cochain X p :=
  ConstantSheafSingularComparison.cochainFromValues X (AddCommGrpCat.of (ZMod 2)) p
    (Function.extend (simplexInclusion U p) (fun σ => α (simplexChain U p σ)) (fun _ => 0))

/-- The original restriction of this degreewise extension is the original subspace cochain. -/
theorem pullback_extendByZero (p : ℕ) (α : ModTwoCapProduct.Cochain U p) :
    ModTwoCapProduct.pullback (subtypeInclusion U) p (extendByZero U p α) = α := by
  apply ConstantSheafSingularComparison.cochain_ext U (AddCommGrpCat.of (ZMod 2)) p
  intro σ
  rw [ModTwoCapProduct.pullback_simplex, extendByZero,
    ConstantSheafSingularComparison.cochainFromValues_simplex]
  exact (simplexInclusion_injective U p).extend_apply _ _ σ

/-- Restriction to an arbitrary actual subspace is degreewise surjective. -/
theorem pullback_subtype_surjective (p : ℕ) :
    Function.Surjective (ModTwoCapProduct.pullback (subtypeInclusion U) p) :=
  fun α => ⟨extendByZero U p α, pullback_extendByZero U p α⟩

/-- An absolute cochain restricting to zero kills the original relative quotient kernel. -/
theorem quotient_ker_le_cochain_ker (p : ℕ) (α : ModTwoCapProduct.Cochain X p)
    (hα : ModTwoCapProduct.pullback (subtypeInclusion U) p α = 0) :
    (RelativeCoefficients.quotientMap (ModuleCat.of ℤ ℤ) U p).toAddMonoidHom.ker ≤ α.ker := by
  intro c hc
  obtain ⟨d, rfl⟩ :=
    (RelativeCoefficients.quotientMap_eq_zero_iff (ModuleCat.of ℤ ℤ) U p c).mp hc
  exact congrArg (fun β : ModTwoCapProduct.Cochain U p => β d) hα

/-- Descend an actual cochain vanishing on subspace chains through the original quotient. -/
def descend (p : ℕ) (α : ModTwoCapProduct.Cochain X p)
    (hα : ModTwoCapProduct.pullback (subtypeInclusion U) p α = 0) : Cochain U p :=
  (RelativeCoefficients.quotientMap (ModuleCat.of ℤ ℤ) U p).toAddMonoidHom.liftOfSurjective
    (RelativeCoefficients.quotientMap_surjective (ModuleCat.of ℤ ℤ) U p)
    ⟨α, quotient_ker_le_cochain_ker U p α hα⟩

/-- Quotient descent recovers precisely the given ambient cochain. -/
theorem toAbsolute_descend (p : ℕ) (α : ModTwoCapProduct.Cochain X p)
    (hα : ModTwoCapProduct.pullback (subtypeInclusion U) p α = 0) :
    toAbsolute U p (descend U p α hα) = α := by
  apply AddMonoidHom.ext
  intro c
  exact AddMonoidHom.liftOfRightInverse_comp_apply
    (RelativeCoefficients.quotientMap (ModuleCat.of ℤ ℤ) U p).toAddMonoidHom
    (Function.surjInv (RelativeCoefficients.quotientMap_surjective (ModuleCat.of ℤ ℤ) U p))
    (Function.rightInverse_surjInv
      (RelativeCoefficients.quotientMap_surjective (ModuleCat.of ℤ ℤ) U p))
    ⟨α, quotient_ker_le_cochain_ker U p α hα⟩ c

end NoExoticSixSphere.RelativeModTwoCochains
