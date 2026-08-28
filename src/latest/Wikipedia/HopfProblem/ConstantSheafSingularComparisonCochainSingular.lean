import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainComplex

/-!
# The coefficient-general native singular cochain functor

Every differential is dual to the original singular boundary, and every
pullback is dual to Mathlib's original singular chain map.  Coefficients
may be any small abelian group, including the additive group of `ℂ`.
-/

noncomputable section

open CategoryTheory Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

/-- Additive duality on native integral chain complexes. -/
def dualFunctor (A : AddCommGrpCat.{0}) :
    (ChainComplex (ModuleCat.{0} ℤ) ℕ)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ where
  obj K := dualComplex K.unop A
  map f := dualMap A f.unop
  map_id K := dualMap_id A K.unop
  map_comp f g := dualMap_comp A g.unop f.unop

/-- The actual singular cochain complex with coefficient group `A`. -/
abbrev singularCochainComplex (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{0}) :
    CochainComplex AddCommGrpCat.{0} ℕ :=
  dualComplex (FirstHurewicz.singularComplex X) A

@[simp]
theorem singularCochainComplex_X (X : Type) [TopologicalSpace X]
    (A : AddCommGrpCat.{0}) (n : ℕ) :
    (singularCochainComplex X A).X n = AddCommGrpCat.of (Cochains X A n) := rfl

/-- Cochains are differentiated by literal precomposition with the native boundary. -/
@[simp]
theorem singularCochainComplex_d_apply (X : Type) [TopologicalSpace X]
    (A : AddCommGrpCat.{0}) (i j : ℕ) (φ : Cochains X A i) (c : Chains X j) :
    (singularCochainComplex X A).d i j φ c =
      φ (((FirstHurewicz.singularComplex X).d j i).hom c) := rfl

/-- The alternating face formula holds for arbitrary abelian coefficients. -/
theorem singularCochainComplex_d_simplex (X : Type) [TopologicalSpace X]
    (A : AddCommGrpCat.{0}) (n : ℕ) (φ : Cochains X A n)
    (σ : SingularSimplex X (n + 1)) :
    (singularCochainComplex X A).d n (n + 1) φ (simplexChain X (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        φ (simplexChain X n (σ.comp (simplexFace n i))) := by
  rw [singularCochainComplex_d_apply, boundary_simplex]
  simp only [map_sum, map_zsmul]

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Pullback on cochains by the original continuous-map singular chain action. -/
def singularPullback (A : AddCommGrpCat.{0}) (f : C(X, Y)) :
    singularCochainComplex Y A ⟶ singularCochainComplex X A :=
  dualMap A (singularChainMap f)

@[simp]
theorem singularPullback_apply (A : AddCommGrpCat.{0}) (f : C(X, Y)) (n : ℕ)
    (φ : Cochains Y A n) (c : Chains X n) :
    (singularPullback A f).f n φ c = φ (inducedChain f n c) := rfl

@[simp]
theorem singularPullback_simplex (A : AddCommGrpCat.{0}) (f : C(X, Y)) (n : ℕ)
    (φ : Cochains Y A n) (σ : SingularSimplex X n) :
    (singularPullback A f).f n φ (simplexChain X n σ) =
      φ (simplexChain Y n (f.comp σ)) := by
  rw [singularPullback_apply, inducedChain_simplex]

/-- The original singular-chain functor followed by actual additive duality. -/
def singularCochainFunctor (A : AddCommGrpCat.{0}) :
    TopCat.{0}ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).op) ⋙ dualFunctor A

@[simp]
theorem singularCochainFunctor_obj (A : AddCommGrpCat.{0}) (X : Type) [TopologicalSpace X] :
    (singularCochainFunctor A).obj (op (TopCat.of X)) = singularCochainComplex X A := rfl

@[simp]
theorem singularCochainFunctor_map (A : AddCommGrpCat.{0}) (f : C(X, Y)) :
    (singularCochainFunctor A).map (TopCat.ofHom f).op = singularPullback A f := rfl

@[simp]
theorem singularPullback_id (A : AddCommGrpCat.{0}) (X : Type) [TopologicalSpace X] :
    singularPullback A (ContinuousMap.id X) = 𝟙 (singularCochainComplex X A) :=
  (singularCochainFunctor A).map_id (op (TopCat.of X))

@[simp]
theorem singularPullback_comp (A : AddCommGrpCat.{0}) (f : C(X, Y)) (g : C(Y, Z)) :
    singularPullback A (g.comp f) = singularPullback A g ≫ singularPullback A f :=
  (singularCochainFunctor A).map_comp (TopCat.ofHom g).op (TopCat.ofHom f).op

/-- Literal covariant change of the coefficient group. -/
def coefficientMap (X : Type) [TopologicalSpace X] {A B : AddCommGrpCat.{0}}
    (α : A ⟶ B) : singularCochainComplex X A ⟶ singularCochainComplex X B :=
  dualCoefficientMap A (FirstHurewicz.singularComplex X) α

@[simp]
theorem coefficientMap_apply (X : Type) [TopologicalSpace X] {A B : AddCommGrpCat.{0}}
    (α : A ⟶ B) (n : ℕ) (φ : Cochains X A n) (c : Chains X n) :
    (coefficientMap X α).f n φ c = α (φ c) := rfl

@[simp]
theorem coefficientMap_id (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{0}) :
    coefficientMap X (𝟙 A) = 𝟙 (singularCochainComplex X A) :=
  dualCoefficientMap_id A (FirstHurewicz.singularComplex X)

@[simp]
theorem coefficientMap_comp (X : Type) [TopologicalSpace X]
    {A B C : AddCommGrpCat.{0}} (α : A ⟶ B) (β : B ⟶ C) :
    coefficientMap X (α ≫ β) = coefficientMap X α ≫ coefficientMap X β :=
  dualCoefficientMap_comp A (FirstHurewicz.singularComplex X) α β

/-- Continuous-map pullback commutes with the genuine coefficient map. -/
theorem coefficientMap_naturality {A B : AddCommGrpCat.{0}} (α : A ⟶ B) (f : C(X, Y)) :
    singularPullback A f ≫ coefficientMap X α =
      coefficientMap Y α ≫ singularPullback B f :=
  dualCoefficientMap_naturality A α (singularChainMap f)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
