import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBilinear
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductPoints

/-!
# Actual singular cross products with a degree-zero factor

These products are literal point insertions on simplex generators. They are
bilinear on Mathlib's actual singular chains, natural under continuous maps,
and commute with the differential in the positive-degree factor.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Cross product with a degree-zero chain in the left factor. -/
def crossProductZeroLeft (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    Chains X 0 →ₗ[ℤ] Chains Y n →ₗ[ℤ] Chains (X × Y) n :=
  chainBilinearLift X Y 0 n fun σ τ =>
    simplexChain (X × Y) n ((crossInsertLeft (zeroSimplexValue σ)).comp τ)

/-- Cross product with a degree-zero chain in the right factor. -/
def crossProductZeroRight (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    Chains X n →ₗ[ℤ] Chains Y 0 →ₗ[ℤ] Chains (X × Y) n :=
  chainBilinearLift X Y n 0 fun σ τ =>
    simplexChain (X × Y) n ((crossInsertRight (zeroSimplexValue τ)).comp σ)

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

@[simp] theorem crossProductZeroLeft_simplex_left (n : ℕ) (σ : SingularSimplex X 0) :
    crossProductZeroLeft X Y n (simplexChain X 0 σ) =
      inducedChain (crossInsertLeft (Y := Y) (zeroSimplexValue σ)) n := by
  apply chainMap_ext Y n
  intro τ
  rw [crossProductZeroLeft, chainBilinearLift_simplex, inducedChain_simplex]

@[simp] theorem crossProductZeroLeft_simplex (n : ℕ)
    (σ : SingularSimplex X 0) (τ : SingularSimplex Y n) :
    crossProductZeroLeft X Y n (simplexChain X 0 σ) (simplexChain Y n τ) =
      simplexChain (X × Y) n ((crossInsertLeft (zeroSimplexValue σ)).comp τ) := by
  rw [crossProductZeroLeft_simplex_left, inducedChain_simplex]

@[simp] theorem crossProductZeroRight_simplex_right (n : ℕ)
    (c : Chains X n) (τ : SingularSimplex Y 0) :
    crossProductZeroRight X Y n c (simplexChain Y 0 τ) =
      inducedChain (crossInsertRight (zeroSimplexValue τ)) n c := by
  have h : integerBilinearRightApply (crossProductZeroRight X Y n) (simplexChain Y 0 τ) =
      inducedChain (crossInsertRight (zeroSimplexValue τ)) n := by
    apply chainMap_ext X n
    intro σ
    simp only [integerBilinearRightApply_apply, crossProductZeroRight,
      chainBilinearLift_simplex, inducedChain_simplex]
  exact LinearMap.congr_fun h c

@[simp] theorem crossProductZeroRight_simplex (n : ℕ)
    (σ : SingularSimplex X n) (τ : SingularSimplex Y 0) :
    crossProductZeroRight X Y n (simplexChain X n σ) (simplexChain Y 0 τ) =
      simplexChain (X × Y) n ((crossInsertRight (zeroSimplexValue τ)).comp σ) := by
  rw [crossProductZeroRight_simplex_right, inducedChain_simplex]

/-- The left point factor commutes with every actual singular differential. -/
theorem crossProductZeroLeft_d (i j : ℕ) (a : Chains X 0) (b : Chains Y i) :
    ((singularComplex (X × Y)).d i j).hom (crossProductZeroLeft X Y i a b) =
      crossProductZeroLeft X Y j a (((singularComplex Y).d i j).hom b) := by
  have h : (((singularComplex (X × Y)).d i j).hom).comp
        (integerBilinearRightApply (crossProductZeroLeft X Y i) b) =
      integerBilinearRightApply (crossProductZeroLeft X Y j)
        (((singularComplex Y).d i j).hom b) := by
    apply chainMap_ext X 0
    intro σ
    simp only [LinearMap.comp_apply, integerBilinearRightApply_apply,
      crossProductZeroLeft_simplex_left]
    exact (inducedChain_boundary (crossInsertLeft (zeroSimplexValue σ)) i j b).symm
  exact LinearMap.congr_fun h a

/-- The right point factor commutes with every actual singular differential. -/
theorem crossProductZeroRight_d (i j : ℕ) (a : Chains X i) (b : Chains Y 0) :
    ((singularComplex (X × Y)).d i j).hom (crossProductZeroRight X Y i a b) =
      crossProductZeroRight X Y j (((singularComplex X).d i j).hom a) b := by
  have h : (((singularComplex (X × Y)).d i j).hom).comp (crossProductZeroRight X Y i a) =
      crossProductZeroRight X Y j (((singularComplex X).d i j).hom a) := by
    apply chainMap_ext Y 0
    intro τ
    simp only [LinearMap.comp_apply, crossProductZeroRight_simplex_right]
    exact (inducedChain_boundary (crossInsertRight (zeroSimplexValue τ)) i j a).symm
  exact LinearMap.congr_fun h b

/-- Naturality of the left degree-zero product under arbitrary continuous maps. -/
theorem crossProductZeroLeft_natural (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (a : Chains X 0) (b : Chains Y n) :
    inducedChain (f.prodMap g) n (crossProductZeroLeft X Y n a b) =
      crossProductZeroLeft X' Y' n (inducedChain f 0 a) (inducedChain g n b) := by
  have h : (inducedChain (f.prodMap g) n).comp
        (integerBilinearRightApply (crossProductZeroLeft X Y n) b) =
      (integerBilinearRightApply (crossProductZeroLeft X' Y' n) (inducedChain g n b)).comp
        (inducedChain f 0) := by
    apply chainMap_ext X 0
    intro σ
    simp only [LinearMap.comp_apply, integerBilinearRightApply_apply, inducedChain_simplex,
      crossProductZeroLeft_simplex_left, zeroSimplexValue_comp]
    exact inducedChain_crossInsertLeft f g (zeroSimplexValue σ) n b
  exact LinearMap.congr_fun h a

/-- Naturality of the right degree-zero product under arbitrary continuous maps. -/
theorem crossProductZeroRight_natural (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (a : Chains X n) (b : Chains Y 0) :
    inducedChain (f.prodMap g) n (crossProductZeroRight X Y n a b) =
      crossProductZeroRight X' Y' n (inducedChain f n a) (inducedChain g 0 b) := by
  have h : (inducedChain (f.prodMap g) n).comp (crossProductZeroRight X Y n a) =
      (crossProductZeroRight X' Y' n (inducedChain f n a)).comp (inducedChain g 0) := by
    apply chainMap_ext Y 0
    intro τ
    simp only [LinearMap.comp_apply, inducedChain_simplex,
      crossProductZeroRight_simplex_right, zeroSimplexValue_comp]
    exact inducedChain_crossInsertRight f g (zeroSimplexValue τ) n a
  exact LinearMap.congr_fun h b

/-- Both descriptions agree for the cross product of two actual zero-chains. -/
theorem crossProductZeroLeft_eq_right :
    crossProductZeroLeft X Y 0 = crossProductZeroRight X Y 0 := by
  apply chainBilinearMap_ext X Y 0 0
  intro σ τ
  rw [crossProductZeroLeft_simplex, crossProductZeroRight_simplex]
  congr 1
  apply ContinuousMap.ext
  intro t
  change (zeroSimplexValue σ, τ t) = (σ t, zeroSimplexValue τ)
  rw [zeroSimplex_apply σ t, zeroSimplex_apply τ t]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
