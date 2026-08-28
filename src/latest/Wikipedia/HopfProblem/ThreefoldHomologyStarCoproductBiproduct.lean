import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Homology of finite biproducts of integral chain complexes

The coordinates are the homology maps of the actual categorical projections.
The inverse is the finite sum of the homology maps of the actual inclusions.
The descent formula therefore preserves the original chain maps, rather than
choosing an unrelated isomorphism of the homology groups.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct

local instance homologyFiniteBiproducts :
    HasFiniteBiproducts (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {ι : Type}

section Finite

variable [Finite ι]
variable (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

private theorem homology_π_ι_self (i : ι) (a : (K i).homology n) :
    (homologyMap (biproduct.π K i) n).hom
      ((homologyMap (biproduct.ι K i) n).hom a) = a := by
  have h := homologyMap_comp (biproduct.ι K i) (biproduct.π K i) n
  rw [biproduct.ι_π_self, homologyMap_id] at h
  exact (congrArg (fun f => f.hom a) h).symm

private theorem homology_π_ι_ne {i j : ι} (hij : i ≠ j)
    (a : (K i).homology n) :
    (homologyMap (biproduct.π K j) n).hom
      ((homologyMap (biproduct.ι K i) n).hom a) = 0 := by
  have h := homologyMap_comp (biproduct.ι K i) (biproduct.π K j) n
  rw [biproduct.ι_π_ne K hij, homologyMap_zero] at h
  exact (congrArg (fun f => f.hom a) h).symm

end Finite

variable [Fintype ι]
variable (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

private theorem homology_biproduct_total (a : (⨁ K).homology n) :
    ∑ i, (homologyMap (biproduct.ι K i) n).hom
      ((homologyMap (biproduct.π K i) n).hom a) = a := by
  have h : homologyMap (∑ i, biproduct.π K i ≫ biproduct.ι K i) n =
      𝟙 ((⨁ K).homology n) := by
    rw [biproduct.total, homologyMap_id]
  change (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
    (∑ i, biproduct.π K i ≫ biproduct.ι K i) = _ at h
  rw [Functor.map_sum] at h
  change (∑ i, homologyMap (biproduct.π K i ≫ biproduct.ι K i) n) = _ at h
  simpa only [homologyMap_comp, ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    using congrArg (fun f => f.hom a) h

/-- Actual homology commutes with a finite categorical biproduct, with the
canonical projection coordinates and the sum-of-inclusions inverse. -/
def homologyBiproductEquiv :
    (⨁ K).homology n ≃ₗ[ℤ] (∀ i, (K i).homology n) := by
  classical
  exact
    ({ toFun a i := (homologyMap (biproduct.π K i) n).hom a
       invFun a := ∑ i, (homologyMap (biproduct.ι K i) n).hom (a i)
       left_inv := homology_biproduct_total K n
       right_inv a := by
         funext i
         change (homologyMap (biproduct.π K i) n).hom
           (∑ j, (homologyMap (biproduct.ι K j) n).hom (a j)) = a i
         rw [map_sum, Finset.sum_eq_single i]
         · exact homology_π_ι_self K n i (a i)
         · intro j _ hji
           exact homology_π_ι_ne K n hji (a j)
         · simp
       map_add' a b := by
         funext i
         exact map_add (homologyMap (biproduct.π K i) n).hom a b
      } : (⨁ K).homology n ≃+ (∀ i, (K i).homology n)).toIntLinearEquiv

/-- The forward map consists of the original homology projections. -/
theorem homologyBiproductEquiv_apply (a : (⨁ K).homology n) :
    homologyBiproductEquiv K n a =
      fun i => (homologyMap (biproduct.π K i) n).hom a := rfl

@[simp] theorem homologyBiproductEquiv_apply_apply (a : (⨁ K).homology n) (i : ι) :
    homologyBiproductEquiv K n a i =
      (homologyMap (biproduct.π K i) n).hom a := rfl

/-- The inverse is literally the finite sum of the induced inclusions. -/
theorem homologyBiproductEquiv_symm_apply (a : ∀ i, (K i).homology n) :
    (homologyBiproductEquiv K n).symm a =
      ∑ i, (homologyMap (biproduct.ι K i) n).hom (a i) := rfl

@[simp] theorem homologyBiproductEquiv_ι [DecidableEq ι]
    (i : ι) (a : (K i).homology n) :
    homologyBiproductEquiv K n ((homologyMap (biproduct.ι K i) n).hom a) =
      Pi.single i a := by
  funext j
  rw [homologyBiproductEquiv_apply_apply]
  by_cases hji : j = i
  · subst j
    rw [Pi.single_eq_same]
    exact homology_π_ι_self K n i a
  · rw [Pi.single_eq_of_ne hji]
    exact homology_π_ι_ne K n (Ne.symm hji) a

@[simp] theorem homologyBiproductEquiv_symm_single [DecidableEq ι]
    (i : ι) (a : (K i).homology n) :
    (homologyBiproductEquiv K n).symm (Pi.single i a) =
      (homologyMap (biproduct.ι K i) n).hom a := by
  apply (homologyBiproductEquiv K n).injective
  rw [LinearEquiv.apply_symm_apply, homologyBiproductEquiv_ι]

@[simp] theorem homologyBiproductEquiv_π_symm
    (a : ∀ i, (K i).homology n) (i : ι) :
    (homologyMap (biproduct.π K i) n).hom ((homologyBiproductEquiv K n).symm a) =
      a i := by
  change homologyBiproductEquiv K n ((homologyBiproductEquiv K n).symm a) i = a i
  rw [LinearEquiv.apply_symm_apply]

variable {K}

/-- A lift of actual chain maps has their genuine homology maps as coordinates. -/
theorem homologyBiproductEquiv_lift {L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : ∀ i, L ⟶ K i) (a : L.homology n) :
    homologyBiproductEquiv K n ((homologyMap (biproduct.lift f) n).hom a) =
      fun i => (homologyMap (f i) n).hom a := by
  funext i
  rw [homologyBiproductEquiv_apply_apply]
  have h := homologyMap_comp (biproduct.lift f) (biproduct.π K i) n
  rw [biproduct.lift_π] at h
  exact (congrArg (fun k => k.hom a) h).symm

/-- A map descended from the finite biproduct becomes the sum of the actual
induced homology maps under the inverse equivalence. -/
theorem homologyBiproductEquiv_desc {L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : ∀ i, K i ⟶ L) (a : ∀ i, (K i).homology n) :
    (homologyMap (biproduct.desc f) n).hom ((homologyBiproductEquiv K n).symm a) =
      ∑ i, (homologyMap (f i) n).hom (a i) := by
  rw [homologyBiproductEquiv_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := homologyMap_comp (biproduct.ι K i) (biproduct.desc f) n
  rw [biproduct.ι_desc] at h
  exact (congrArg (fun k => k.hom (a i)) h).symm

/-- The same descent formula on an arbitrary class of the biproduct homology. -/
theorem homologyBiproductEquiv_desc_apply {L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : ∀ i, K i ⟶ L) (a : (⨁ K).homology n) :
    (homologyMap (biproduct.desc f) n).hom a =
      ∑ i, (homologyMap (f i) n).hom (homologyBiproductEquiv K n a i) := by
  have h := homologyBiproductEquiv_desc n f (homologyBiproductEquiv K n a)
  rwa [LinearEquiv.symm_apply_apply] at h

end Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct
