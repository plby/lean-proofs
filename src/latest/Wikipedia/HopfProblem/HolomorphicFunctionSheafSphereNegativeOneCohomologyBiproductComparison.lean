import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereNegativeOneCohomologyBiproductBasic

/-!
# Complex-linear native binary-biproduct cohomology

The genuine cohomology comparison respects the scalar action induced by the
diagonal sheaf endomorphism.  Its inverse is the sum of the cohomology maps
of the original two summand inclusions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
namespace NegativeOneCohomology.GenericBiproduct

open CuspNormalization.SheafCohomology

variable {X : TopCat.{0}} (F G : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ)

/-- The first actual sheaf inclusion induces the first summand inclusion
under the native cohomology comparison. -/
@[simp] theorem cohomologyAddEquiv_inl (a : CategoryTheory.Sheaf.H.{0} F n) :
    cohomologyAddEquiv F G n
      (CategoryTheory.Sheaf.H.map (biprod.inl : F ⟶ F ⊞ G) n a) = (a, 0) := by
  apply Prod.ext
  · rw [cohomologyAddEquiv_fst]
    have hm : (cohomologyFunctor X n).map (biprod.inl : F ⟶ F ⊞ G) ≫
        (cohomologyFunctor X n).map (biprod.fst : F ⊞ G ⟶ F) =
        𝟙 ((cohomologyFunctor X n).obj F) := by
      rw [← Functor.map_comp, biprod.inl_fst]
      exact (cohomologyFunctor X n).map_id F
    have h := ConcreteCategory.congr_hom hm a
    exact h
  · rw [cohomologyAddEquiv_snd]
    have hm : (cohomologyFunctor X n).map (biprod.inl : F ⟶ F ⊞ G) ≫
        (cohomologyFunctor X n).map (biprod.snd : F ⊞ G ⟶ G) = 0 := by
      rw [← Functor.map_comp, biprod.inl_snd, Functor.map_zero]
    have h := ConcreteCategory.congr_hom hm a
    exact h

/-- The second actual sheaf inclusion induces the second summand inclusion
under the native cohomology comparison. -/
@[simp] theorem cohomologyAddEquiv_inr (b : CategoryTheory.Sheaf.H.{0} G n) :
    cohomologyAddEquiv F G n
      (CategoryTheory.Sheaf.H.map (biprod.inr : G ⟶ F ⊞ G) n b) = (0, b) := by
  apply Prod.ext
  · rw [cohomologyAddEquiv_fst]
    have hm : (cohomologyFunctor X n).map (biprod.inr : G ⟶ F ⊞ G) ≫
        (cohomologyFunctor X n).map (biprod.fst : F ⊞ G ⟶ F) = 0 := by
      rw [← Functor.map_comp, biprod.inr_fst, Functor.map_zero]
    have h := ConcreteCategory.congr_hom hm b
    exact h
  · rw [cohomologyAddEquiv_snd]
    have hm : (cohomologyFunctor X n).map (biprod.inr : G ⟶ F ⊞ G) ≫
        (cohomologyFunctor X n).map (biprod.snd : F ⊞ G ⟶ G) =
        𝟙 ((cohomologyFunctor X n).obj G) := by
      rw [← Functor.map_comp, biprod.inr_snd]
      exact (cohomologyFunctor X n).map_id G
    have h := ConcreteCategory.congr_hom hm b
    exact h

/-- The inverse comparison is the sum of the two native inclusion maps. -/
theorem cohomologyAddEquiv_symm_apply
    (a : CategoryTheory.Sheaf.H.{0} F n) (b : CategoryTheory.Sheaf.H.{0} G n) :
    (cohomologyAddEquiv F G n).symm (a, b) =
      CategoryTheory.Sheaf.H.map (biprod.inl : F ⟶ F ⊞ G) n a +
        CategoryTheory.Sheaf.H.map (biprod.inr : G ⟶ F ⊞ G) n b := by
  apply (cohomologyAddEquiv F G n).injective
  simp

@[simp] theorem cohomologyAddEquiv_symm_inl (a : CategoryTheory.Sheaf.H.{0} F n) :
    (cohomologyAddEquiv F G n).symm (a, 0) =
      CategoryTheory.Sheaf.H.map (biprod.inl : F ⟶ F ⊞ G) n a := by
  rw [cohomologyAddEquiv_symm_apply, map_zero, add_zero]

@[simp] theorem cohomologyAddEquiv_symm_inr (b : CategoryTheory.Sheaf.H.{0} G n) :
    (cohomologyAddEquiv F G n).symm (0, b) =
      CategoryTheory.Sheaf.H.map (biprod.inr : G ⟶ F ⊞ G) n b := by
  rw [cohomologyAddEquiv_symm_apply, map_zero, zero_add]

variable (ρ : ℂ →+* End F) (σ : ℂ →+* End G)

/-- The comparison intertwines the actual scalar endomorphisms in all
degrees, before any module structure is introduced. -/
theorem cohomologyAddEquiv_diagonalScalarEnd (c : ℂ)
    (a : CategoryTheory.Sheaf.H.{0} (F ⊞ G : TopCat.Sheaf AddCommGrpCat.{0} X) n) :
    cohomologyAddEquiv F G n
        (CategoryTheory.Sheaf.H.map (diagonalScalarEnd ρ σ c) n a) =
      (CategoryTheory.Sheaf.H.map (ρ c) n (cohomologyAddEquiv F G n a).1,
        CategoryTheory.Sheaf.H.map (σ c) n (cohomologyAddEquiv F G n a).2) := by
  apply Prod.ext
  · rw [cohomologyAddEquiv_fst, cohomologyAddEquiv_fst]
    have hm : (cohomologyFunctor X n).map (diagonalScalarEnd ρ σ c) ≫
        (cohomologyFunctor X n).map (biprod.fst : F ⊞ G ⟶ F) =
        (cohomologyFunctor X n).map (biprod.fst : F ⊞ G ⟶ F) ≫
          (cohomologyFunctor X n).map (ρ c) := by
      rw [← Functor.map_comp, diagonalScalarEnd_fst, Functor.map_comp]
    have h := ConcreteCategory.congr_hom hm a
    exact h
  · rw [cohomologyAddEquiv_snd, cohomologyAddEquiv_snd]
    have hm : (cohomologyFunctor X n).map (diagonalScalarEnd ρ σ c) ≫
        (cohomologyFunctor X n).map (biprod.snd : F ⊞ G ⟶ G) =
        (cohomologyFunctor X n).map (biprod.snd : F ⊞ G ⟶ G) ≫
          (cohomologyFunctor X n).map (σ c) := by
      rw [← Functor.map_comp, diagonalScalarEnd_snd, Functor.map_comp]
    have h := ConcreteCategory.congr_hom hm a
    exact h

/-- The actual native cohomology comparison as a complex-linear equivalence;
all three module structures are induced by the original sheaf scalar maps. -/
def cohomologyLinearEquiv :
    letI := cohomologyModule F ρ n
    letI := cohomologyModule G σ n
    letI := cohomologyModule (F ⊞ G) (diagonalScalarEnd ρ σ) n
    CategoryTheory.Sheaf.H.{0} (F ⊞ G : TopCat.Sheaf AddCommGrpCat.{0} X) n ≃ₗ[ℂ]
      (CategoryTheory.Sheaf.H.{0} F n × CategoryTheory.Sheaf.H.{0} G n) := by
  letI := cohomologyModule F ρ n
  letI := cohomologyModule G σ n
  letI := cohomologyModule (F ⊞ G) (diagonalScalarEnd ρ σ) n
  refine { __ := cohomologyAddEquiv F G n, map_smul' := ?_ }
  intro c a
  exact cohomologyAddEquiv_diagonalScalarEnd F G n ρ σ c a

/-- The linear comparison retains exactly the native additive comparison. -/
@[simp] theorem cohomologyLinearEquiv_toAddEquiv :
    letI := cohomologyModule F ρ n
    letI := cohomologyModule G σ n
    letI := cohomologyModule (F ⊞ G) (diagonalScalarEnd ρ σ) n
    (cohomologyLinearEquiv F G n ρ σ).toAddEquiv = cohomologyAddEquiv F G n := rfl

@[simp] theorem cohomologyLinearEquiv_fst
    (a : CategoryTheory.Sheaf.H.{0} (F ⊞ G : TopCat.Sheaf AddCommGrpCat.{0} X) n) :
    letI := cohomologyModule F ρ n
    letI := cohomologyModule G σ n
    letI := cohomologyModule (F ⊞ G) (diagonalScalarEnd ρ σ) n
    (cohomologyLinearEquiv F G n ρ σ a).1 =
      CategoryTheory.Sheaf.H.map (biprod.fst : F ⊞ G ⟶ F) n a :=
  cohomologyAddEquiv_fst F G n a

@[simp] theorem cohomologyLinearEquiv_snd
    (a : CategoryTheory.Sheaf.H.{0} (F ⊞ G : TopCat.Sheaf AddCommGrpCat.{0} X) n) :
    letI := cohomologyModule F ρ n
    letI := cohomologyModule G σ n
    letI := cohomologyModule (F ⊞ G) (diagonalScalarEnd ρ σ) n
    (cohomologyLinearEquiv F G n ρ σ a).2 =
      CategoryTheory.Sheaf.H.map (biprod.snd : F ⊞ G ⟶ G) n a :=
  cohomologyAddEquiv_snd F G n a

theorem cohomologyLinearEquiv_symm_apply
    (a : CategoryTheory.Sheaf.H.{0} F n) (b : CategoryTheory.Sheaf.H.{0} G n) :
    letI := cohomologyModule F ρ n
    letI := cohomologyModule G σ n
    letI := cohomologyModule (F ⊞ G) (diagonalScalarEnd ρ σ) n
    (cohomologyLinearEquiv F G n ρ σ).symm (a, b) =
      CategoryTheory.Sheaf.H.map (biprod.inl : F ⟶ F ⊞ G) n a +
        CategoryTheory.Sheaf.H.map (biprod.inr : G ⟶ F ⊞ G) n b :=
  cohomologyAddEquiv_symm_apply F G n a b

@[simp] theorem cohomologyLinearEquiv_symm_inl (a : CategoryTheory.Sheaf.H.{0} F n) :
    letI := cohomologyModule F ρ n
    letI := cohomologyModule G σ n
    letI := cohomologyModule (F ⊞ G) (diagonalScalarEnd ρ σ) n
    (cohomologyLinearEquiv F G n ρ σ).symm (a, 0) =
      CategoryTheory.Sheaf.H.map (biprod.inl : F ⟶ F ⊞ G) n a :=
  cohomologyAddEquiv_symm_inl F G n a

@[simp] theorem cohomologyLinearEquiv_symm_inr (b : CategoryTheory.Sheaf.H.{0} G n) :
    letI := cohomologyModule F ρ n
    letI := cohomologyModule G σ n
    letI := cohomologyModule (F ⊞ G) (diagonalScalarEnd ρ σ) n
    (cohomologyLinearEquiv F G n ρ σ).symm (0, b) =
      CategoryTheory.Sheaf.H.map (biprod.inr : G ⟶ F ⊞ G) n b :=
  cohomologyAddEquiv_symm_inr F G n b

end NegativeOneCohomology.GenericBiproduct
end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
