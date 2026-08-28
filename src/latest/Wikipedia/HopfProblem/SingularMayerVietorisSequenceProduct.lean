import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Homology of the middle biproduct in Mayer--Vietoris

The actual homology of the categorical biproduct of integral chain complexes
is identified with the product of their actual homology modules. The forward
map consists of the induced projections and the inverse is the sum of the
induced injections. Their inverse identities follow from functoriality,
additivity of homology, and the categorical biproduct identities.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace Wikipedia.HopfProblem.SingularMayerVietoris

variable (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

private theorem homology_fst_inl (a : K.homology n) :
    (homologyMap (biprod.fst : K ⊞ L ⟶ K) n).hom
      ((homologyMap (biprod.inl : K ⟶ K ⊞ L) n).hom a) = a := by
  have h := homologyMap_comp (biprod.inl : K ⟶ K ⊞ L) biprod.fst n
  rw [biprod.inl_fst, homologyMap_id] at h
  exact (congrArg (fun f => f.hom a) h).symm

private theorem homology_snd_inl (a : K.homology n) :
    (homologyMap (biprod.snd : K ⊞ L ⟶ L) n).hom
      ((homologyMap (biprod.inl : K ⟶ K ⊞ L) n).hom a) = 0 := by
  have h := homologyMap_comp (biprod.inl : K ⟶ K ⊞ L) biprod.snd n
  rw [biprod.inl_snd, homologyMap_zero] at h
  exact (congrArg (fun f => f.hom a) h).symm

private theorem homology_fst_inr (b : L.homology n) :
    (homologyMap (biprod.fst : K ⊞ L ⟶ K) n).hom
      ((homologyMap (biprod.inr : L ⟶ K ⊞ L) n).hom b) = 0 := by
  have h := homologyMap_comp (biprod.inr : L ⟶ K ⊞ L) biprod.fst n
  rw [biprod.inr_fst, homologyMap_zero] at h
  exact (congrArg (fun f => f.hom b) h).symm

private theorem homology_snd_inr (b : L.homology n) :
    (homologyMap (biprod.snd : K ⊞ L ⟶ L) n).hom
      ((homologyMap (biprod.inr : L ⟶ K ⊞ L) n).hom b) = b := by
  have h := homologyMap_comp (biprod.inr : L ⟶ K ⊞ L) biprod.snd n
  rw [biprod.inr_snd, homologyMap_id] at h
  exact (congrArg (fun f => f.hom b) h).symm

private theorem homology_biprod_total (a : (K ⊞ L).homology n) :
    (homologyMap (biprod.inl : K ⟶ K ⊞ L) n).hom
        ((homologyMap (biprod.fst : K ⊞ L ⟶ K) n).hom a) +
      (homologyMap (biprod.inr : L ⟶ K ⊞ L) n).hom
        ((homologyMap (biprod.snd : K ⊞ L ⟶ L) n).hom a) = a := by
  have h : homologyMap
      (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr : K ⊞ L ⟶ K ⊞ L) n =
        𝟙 ((K ⊞ L).homology n) := by
    rw [biprod.total, homologyMap_id]
  rw [homologyMap_add, homologyMap_comp, homologyMap_comp] at h
  exact congrArg (fun f => f.hom a) h

/-- The actual homology of a categorical biproduct is the product of the
actual homology modules, with the canonical induced projections. -/
def homologyBiprodEquiv :
    (K ⊞ L).homology n ≃ₗ[ℤ] (K.homology n × L.homology n) :=
  ({ toFun a := ((homologyMap (biprod.fst : K ⊞ L ⟶ K) n).hom a,
        (homologyMap (biprod.snd : K ⊞ L ⟶ L) n).hom a)
     invFun a := (homologyMap (biprod.inl : K ⟶ K ⊞ L) n).hom a.1 +
       (homologyMap (biprod.inr : L ⟶ K ⊞ L) n).hom a.2
     left_inv := homology_biprod_total K L n
     right_inv a := by
       apply Prod.ext
       · change (homologyMap (biprod.fst : K ⊞ L ⟶ K) n).hom
           ((homologyMap (biprod.inl : K ⟶ K ⊞ L) n).hom a.1 +
             (homologyMap (biprod.inr : L ⟶ K ⊞ L) n).hom a.2) = a.1
         rw [map_add, homology_fst_inl, homology_fst_inr, add_zero]
       · change (homologyMap (biprod.snd : K ⊞ L ⟶ L) n).hom
           ((homologyMap (biprod.inl : K ⟶ K ⊞ L) n).hom a.1 +
             (homologyMap (biprod.inr : L ⟶ K ⊞ L) n).hom a.2) = a.2
         rw [map_add, homology_snd_inl, homology_snd_inr, zero_add]
     map_add' a b := by
       change (_, _) = (_, _)
       rw [map_add, map_add]
    } : (K ⊞ L).homology n ≃+ (K.homology n × L.homology n)).toIntLinearEquiv

/-- Both coordinates are literally the maps induced by the chain projections. -/
theorem homologyBiprodEquiv_apply (a : (K ⊞ L).homology n) :
    homologyBiprodEquiv K L n a =
      ((homologyMap (biprod.fst : K ⊞ L ⟶ K) n).hom a,
        (homologyMap (biprod.snd : K ⊞ L ⟶ L) n).hom a) := rfl

@[simp] theorem homologyBiprodEquiv_fst (a : (K ⊞ L).homology n) :
    (homologyBiprodEquiv K L n a).1 =
      (homologyMap (biprod.fst : K ⊞ L ⟶ K) n).hom a := rfl

@[simp] theorem homologyBiprodEquiv_snd (a : (K ⊞ L).homology n) :
    (homologyBiprodEquiv K L n a).2 =
      (homologyMap (biprod.snd : K ⊞ L ⟶ L) n).hom a := rfl

/-- The inverse is the sum of the maps induced by the chain injections. -/
theorem homologyBiprodEquiv_symm_apply (a : K.homology n × L.homology n) :
    (homologyBiprodEquiv K L n).symm a =
      (homologyMap (biprod.inl : K ⟶ K ⊞ L) n).hom a.1 +
        (homologyMap (biprod.inr : L ⟶ K ⊞ L) n).hom a.2 := rfl

@[simp] theorem homologyBiprodEquiv_inl (a : K.homology n) :
    homologyBiprodEquiv K L n
      ((homologyMap (biprod.inl : K ⟶ K ⊞ L) n).hom a) = (a, 0) := by
  rw [homologyBiprodEquiv_apply, homology_fst_inl, homology_snd_inl]

@[simp] theorem homologyBiprodEquiv_inr (b : L.homology n) :
    homologyBiprodEquiv K L n
      ((homologyMap (biprod.inr : L ⟶ K ⊞ L) n).hom b) = (0, b) := by
  rw [homologyBiprodEquiv_apply, homology_fst_inr, homology_snd_inr]

@[simp] theorem homologyBiprodEquiv_symm_inl (a : K.homology n) :
    (homologyBiprodEquiv K L n).symm (a, 0) =
      (homologyMap (biprod.inl : K ⟶ K ⊞ L) n).hom a := by
  rw [homologyBiprodEquiv_symm_apply, map_zero, add_zero]

@[simp] theorem homologyBiprodEquiv_symm_inr (b : L.homology n) :
    (homologyBiprodEquiv K L n).symm (0, b) =
      (homologyMap (biprod.inr : L ⟶ K ⊞ L) n).hom b := by
  rw [homologyBiprodEquiv_symm_apply, map_zero, zero_add]

@[simp] theorem homologyBiprodEquiv_fst_symm (a : K.homology n × L.homology n) :
    (homologyMap (biprod.fst : K ⊞ L ⟶ K) n).hom
      ((homologyBiprodEquiv K L n).symm a) = a.1 := by
  change (homologyBiprodEquiv K L n ((homologyBiprodEquiv K L n).symm a)).1 = a.1
  rw [LinearEquiv.apply_symm_apply]

@[simp] theorem homologyBiprodEquiv_snd_symm (a : K.homology n × L.homology n) :
    (homologyMap (biprod.snd : K ⊞ L ⟶ L) n).hom
      ((homologyBiprodEquiv K L n).symm a) = a.2 := by
  change (homologyBiprodEquiv K L n ((homologyBiprodEquiv K L n).symm a)).2 = a.2
  rw [LinearEquiv.apply_symm_apply]

variable {K L}

/-- The actual map induced by a chain-level lift has the two expected
homology coordinates. -/
theorem homologyBiprodEquiv_lift {A : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : A ⟶ K) (g : A ⟶ L) (a : A.homology n) :
    homologyBiprodEquiv K L n ((homologyMap (biprod.lift f g) n).hom a) =
      ((homologyMap f n).hom a, (homologyMap g n).hom a) := by
  apply Prod.ext
  · rw [homologyBiprodEquiv_fst]
    have h := homologyMap_comp (biprod.lift f g) biprod.fst n
    rw [biprod.lift_fst] at h
    exact (congrArg (fun k => k.hom a) h).symm
  · rw [homologyBiprodEquiv_snd]
    have h := homologyMap_comp (biprod.lift f g) biprod.snd n
    rw [biprod.lift_snd] at h
    exact (congrArg (fun k => k.hom a) h).symm

/-- In particular, the Mayer--Vietoris sign convention on the left map
is carried to the genuine pair of induced homology maps. -/
theorem homologyBiprodEquiv_lift_neg {A : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : A ⟶ K) (g : A ⟶ L) (a : A.homology n) :
    homologyBiprodEquiv K L n ((homologyMap (biprod.lift f (-g)) n).hom a) =
      ((homologyMap f n).hom a, -(homologyMap g n).hom a) := by
  rw [homologyBiprodEquiv_lift, homologyMap_neg]
  rfl

/-- A chain-level map out of the biproduct becomes the sum of its two
actual induced homology maps under the inverse equivalence. -/
theorem homologyBiprodEquiv_desc {A : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : K ⟶ A) (g : L ⟶ A) (a : K.homology n × L.homology n) :
    (homologyMap (biprod.desc f g) n).hom ((homologyBiprodEquiv K L n).symm a) =
      (homologyMap f n).hom a.1 + (homologyMap g n).hom a.2 := by
  rw [homologyBiprodEquiv_symm_apply, map_add]
  congr 1
  · have h := homologyMap_comp (biprod.inl : K ⟶ K ⊞ L) (biprod.desc f g) n
    rw [biprod.inl_desc] at h
    exact (congrArg (fun k => k.hom a.1) h).symm
  · have h := homologyMap_comp (biprod.inr : L ⟶ K ⊞ L) (biprod.desc f g) n
    rw [biprod.inr_desc] at h
    exact (congrArg (fun k => k.hom a.2) h).symm

/-- The same sum formula for an arbitrary class of the biproduct homology. -/
theorem homologyBiprodEquiv_desc_apply {A : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : K ⟶ A) (g : L ⟶ A) (a : (K ⊞ L).homology n) :
    (homologyMap (biprod.desc f g) n).hom a =
      (homologyMap f n).hom (homologyBiprodEquiv K L n a).1 +
        (homologyMap g n).hom (homologyBiprodEquiv K L n a).2 := by
  have h := homologyBiprodEquiv_desc n f g (homologyBiprodEquiv K L n a)
  rwa [LinearEquiv.symm_apply_apply] at h

end Wikipedia.HopfProblem.SingularMayerVietoris
