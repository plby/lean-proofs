import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# Tensor transport of integral chain-homotopy equivalences

All tensor products below are Mathlib's total tensor complexes. The forward
and inverse chain maps are the literal tensor products of the supplied maps;
the homology isomorphisms are induced by those same chain maps.
-/

noncomputable section

open CategoryTheory HomologicalComplex
open scoped TensorProduct MonoidalCategory

namespace Wikipedia.HopfProblem.ChainTensorHomotopy

variable {K₁ K₂ L₁ L₂ M₁ M₂ : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- Tensoring two homotopies gives a homotopy of the actual total tensor maps. -/
def tensorHomotopy {f₁ g₁ : K₁ ⟶ L₁} {f₂ g₂ : K₂ ⟶ L₂}
    (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) :
    Homotopy (tensorHom f₁ f₂) (tensorHom g₁ g₂) :=
  (mapBifunctorMapHomotopy₁ h₁ f₂ (MonoidalCategory.curriedTensor (ModuleCat ℤ))
    (.down ℕ)).trans
    (mapBifunctorMapHomotopy₂ g₁ h₂ (MonoidalCategory.curriedTensor (ModuleCat ℤ))
      (.down ℕ))

/-- Composition of the actual total tensor maps. -/
theorem tensorHom_comp (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    (g₁ : L₁ ⟶ M₁) (g₂ : L₂ ⟶ M₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) :=
  MonoidalCategory.tensorHom_comp_tensorHom f₁ f₂ g₁ g₂

/-- The total tensor product of two identity maps is the identity. -/
@[simp] theorem tensorHom_id_id (K₁ K₂ : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    tensorHom (𝟙 K₁) (𝟙 K₂) = 𝟙 (tensorObj K₁ K₂) :=
  MonoidalCategory.id_tensorHom_id K₁ K₂

/-- Chain-homotopy equivalences transport through the actual total tensor product. -/
def tensorHomotopyEquiv (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (tensorObj K₁ K₂) (tensorObj L₁ L₂) where
  hom := tensorHom e₁.hom e₂.hom
  inv := tensorHom e₁.inv e₂.inv
  homotopyHomInvId := by
    rw [tensorHom_comp, ← tensorHom_id_id]
    exact tensorHomotopy e₁.homotopyHomInvId e₂.homotopyHomInvId
  homotopyInvHomId := by
    rw [tensorHom_comp, ← tensorHom_id_id]
    exact tensorHomotopy e₁.homotopyInvHomId e₂.homotopyInvHomId

@[simp] theorem tensorHomotopyEquiv_hom
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    (tensorHomotopyEquiv e₁ e₂).hom = tensorHom e₁.hom e₂.hom := rfl

@[simp] theorem tensorHomotopyEquiv_inv
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    (tensorHomotopyEquiv e₁ e₂).inv = tensorHom e₁.inv e₂.inv := rfl

/-- The homology isomorphism induced by the actual tensor of the forward maps. -/
def tensorHomologyIso (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) (n : ℕ) :
    (tensorObj K₁ K₂).homology n ≅ (tensorObj L₁ L₂).homology n :=
  (tensorHomotopyEquiv e₁ e₂).toHomologyIso n

@[simp] theorem tensorHomologyIso_hom
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) (n : ℕ) :
    (tensorHomologyIso e₁ e₂ n).hom = homologyMap (tensorHom e₁.hom e₂.hom) n := rfl

@[simp] theorem tensorHomologyIso_inv
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) (n : ℕ) :
    (tensorHomologyIso e₁ e₂ n).inv = homologyMap (tensorHom e₁.inv e₂.inv) n := rfl

/-- The same induced homology isomorphism as an integral linear equivalence. -/
def tensorHomologyEquiv (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) (n : ℕ) :
    (tensorObj K₁ K₂).homology n ≃ₗ[ℤ] (tensorObj L₁ L₂).homology n :=
  (tensorHomologyIso e₁ e₂ n).toLinearEquiv

@[simp] theorem tensorHomologyEquiv_toLinearMap
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) (n : ℕ) :
    (tensorHomologyEquiv e₁ e₂ n).toLinearMap =
      (homologyMap (tensorHom e₁.hom e₂.hom) n).hom := rfl

@[simp] theorem tensorHomologyEquiv_apply
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) (n : ℕ)
    (x : (tensorObj K₁ K₂).homology n) :
    tensorHomologyEquiv e₁ e₂ n x =
      (homologyMap (tensorHom e₁.hom e₂.hom) n).hom x := rfl

@[simp] theorem tensorHomologyEquiv_symm_apply
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) (n : ℕ)
    (x : (tensorObj L₁ L₂).homology n) :
    (tensorHomologyEquiv e₁ e₂ n).symm x =
      (homologyMap (tensorHom e₁.inv e₂.inv) n).hom x := rfl

/-- No flatness or replacement-complex hypothesis is needed for a tensor of
chain-homotopy equivalences to be a quasi-isomorphism. -/
theorem tensorHom_quasiIso
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    QuasiIso (tensorHom e₁.hom e₂.hom) :=
  (tensorHomotopyEquiv e₁ e₂).quasiIso_hom

/-- The actual total tensor map restricts to the tensor of the component maps
on every summand. -/
theorem ιTensorObj_tensorHom (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    (p q n : ℕ) (h : p + q = n) :
    ιTensorObj K₁ K₂ p q n h ≫ (tensorHom f₁ f₂).f n =
      (f₁.f p ⊗ₘ f₂.f q) ≫ ιTensorObj L₁ L₂ p q n h := by
  unfold ιTensorObj tensorHom
  rw [ι_mapBifunctorMap, MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

/-- On a pure tensor in a specified summand, the total tensor map applies
the two chain maps separately. -/
@[simp] theorem tensorHom_ιTensorObj_tmul (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    (p q n : ℕ) (h : p + q = n) (x : K₁.X p) (y : K₂.X q) :
    ((tensorHom f₁ f₂).f n).hom ((ιTensorObj K₁ K₂ p q n h).hom (x ⊗ₜ[ℤ] y)) =
      (ιTensorObj L₁ L₂ p q n h).hom ((f₁.f p).hom x ⊗ₜ[ℤ] (f₂.f q).hom y) := by
  exact congrArg (fun f => (f : K₁.X p ⊗ K₂.X q ⟶ (tensorObj L₁ L₂).X n).hom
    (x ⊗ₜ[ℤ] y)) (ιTensorObj_tensorHom f₁ f₂ p q n h)

end Wikipedia.HopfProblem.ChainTensorHomotopy
