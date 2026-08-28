import Wikipedia.NoExoticSixSphere.CoefficientChainBoundary
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainSingular
import Wikipedia.HopfProblem.SingularCohomologyCupFacesDifferential

/-!
# The cap operation on the original mod-two singular chains

Cochains are additive homomorphisms from the native integral singular
chains to `ZMod 2`, with the original coboundary. The cap operation uses
the actual front and back faces and the native mod-two coefficient
coproducts. Its boundary identity and descent will be proved separately.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SphereHomologyCoefficients SingularCohomologyCup

namespace NoExoticSixSphere.ModTwoCapProduct

abbrev Coefficient := ModTwoChains.Coefficient

/-- The original arbitrary-coefficient singular cochains, specialized to mod two. -/
abbrev Cochain (X : Type) [TopologicalSpace X] (n : ℕ) :=
  ConstantSheafSingularComparison.Cochains X (AddCommGrpCat.of (ZMod 2)) n

variable {X : Type} [TopologicalSpace X]

/-- Literal precomposition with the original integral singular differential. -/
def coboundary {n : ℕ} (α : Cochain X n) : Cochain X (n + 1) :=
  (ConstantSheafSingularComparison.singularCochainComplex X
    (AddCommGrpCat.of (ZMod 2))).d n (n + 1) α

/-- The original coboundary has the unsigned face formula with mod-two coefficients. -/
theorem coboundary_simplex {n : ℕ} (α : Cochain X n) (σ : SingularSimplex X (n + 1)) :
    coboundary α (simplexChain X (n + 1) σ) =
      ∑ i : Fin (n + 2), α (simplexChain X n (σ.comp (simplexFace n i))) := by
  rw [coboundary, ConstantSheafSingularComparison.singularCochainComplex_d_simplex]
  apply Finset.sum_congr rfl
  intro i _
  exact ModTwoChains.sign_smul_coefficient i.val _

/-- Multiplication in the actual coefficient object, as an integral linear map. -/
def multiplyCoefficient (a : ZMod 2) : Coefficient →ₗ[ℤ] Coefficient :=
  LinearMap.mulLeft ℤ a

/-- Cap with a cochain in an explicitly specified total chain degree. -/
def capInDegree {p q n : ℕ} (h : p + q = n) (α : Cochain X p) :
    ModTwoChains.Chains X n →ₗ[ℤ] ModTwoChains.Chains X q :=
  CoefficientChains.lift Coefficient X n (fun σ =>
    (CoefficientChains.simplex Coefficient X q
      (σ.comp (windowFace p q n (by omega)))).comp
        (multiplyCoefficient (α (simplexChain X p (σ.comp (windowFace 0 p n (by omega)))))))

/-- The cap operation retains the actual front-cochain and back-chain formula. -/
theorem capInDegree_simplex {p q n : ℕ} (h : p + q = n) (α : Cochain X p)
    (σ : SingularSimplex X n) (a : ZMod 2) :
    capInDegree h α (CoefficientChains.simplex Coefficient X n σ a) =
      CoefficientChains.simplex Coefficient X q (σ.comp (windowFace p q n (by omega)))
        (α (simplexChain X p (σ.comp (windowFace 0 p n (by omega)))) * a) :=
  CoefficientChains.lift_simplex Coefficient X n _ σ a

/-- The original front/back cap operation. -/
def cap {p q : ℕ} (α : Cochain X p) :
    ModTwoChains.Chains X (p + q) →ₗ[ℤ] ModTwoChains.Chains X q :=
  capInDegree rfl α

theorem cap_simplex {p q : ℕ} (α : Cochain X p)
    (σ : SingularSimplex X (p + q)) (a : ZMod 2) :
    cap α (CoefficientChains.simplex Coefficient X (p + q) σ a) =
      CoefficientChains.simplex Coefficient X q (σ.comp (backFace p q))
        (α (simplexChain X p (σ.comp (frontFace p q))) * a) :=
  capInDegree_simplex rfl α σ a

theorem capInDegree_zero {p q n : ℕ} (h : p + q = n) :
    capInDegree (X := X) h (0 : Cochain X p) = 0 := by
  apply CoefficientChains.map_ext Coefficient X n
  intro σ a
  have he := capInDegree_simplex h (0 : Cochain X p) σ a
  simpa only [AddMonoidHom.zero_apply, zero_mul, map_zero, LinearMap.zero_apply] using! he

theorem capInDegree_add {p q n : ℕ} (h : p + q = n) (α β : Cochain X p) :
    capInDegree h (α + β) = capInDegree h α + capInDegree h β := by
  apply CoefficientChains.map_ext Coefficient X n
  intro σ a
  rw [LinearMap.add_apply]
  exact (capInDegree_simplex h (α + β) σ a).trans (by
    rw [AddMonoidHom.add_apply, add_mul, map_add]
    exact congrArg₂ (fun x y => x + y)
      (capInDegree_simplex h α σ a).symm (capInDegree_simplex h β σ a).symm)

end NoExoticSixSphere.ModTwoCapProduct
