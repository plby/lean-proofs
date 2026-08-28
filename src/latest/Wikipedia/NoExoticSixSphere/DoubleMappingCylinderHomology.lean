import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderOverlapEquivalence
import Wikipedia.HopfProblem.SingularMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Homology of the attaching span when its actual double cylinder contracts

Exactness of the genuine open-cover Mayer--Vietoris sequence makes its
signed intersection map an isomorphism in positive degrees. The actual
cover and midpoint equivalences identify the coordinates with the two
original attaching maps. Removing the second sign gives their joint
homology isomorphism. Contractibility of the actual double cylinder is
an explicit hypothesis here, proved separately for the James stages.
-/

noncomputable section

open CategoryTheory Set
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y : TopCat} (e : A ⟶ X) (f : A ⟶ Y)
    [ContractibleSpace (space e f)]

theorem cover_left_bijective (k : ℕ) (hk : k ≠ 0) :
    Function.Bijective (leftHomologyMap (lower e f) (upper e f) k) := by
  let := contractible_homology_subsingleton (space e f) k hk
  let := contractible_homology_subsingleton (space e f) (k + 1) (Nat.succ_ne_zero k)
  have hd : connectingHomomorphism (lower e f) (upper e f)
      (lower_isOpen e f) (upper_isOpen e f) (cover e f) k = 0 := by
    apply LinearMap.ext
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    rw [ha, map_zero]
    rfl
  have hr : rightHomologyMap (lower e f) (upper e f) k = 0 := by
    apply LinearMap.ext
    intro a
    exact Subsingleton.elim _ _
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [← exact_at_intersection (lower e f) (upper e f)
      (lower_isOpen e f) (upper_isOpen e f) (cover e f) k, hd, LinearMap.range_zero]
  · apply LinearMap.range_eq_top.mp
    rw [exact_at_pair (lower e f) (upper e f)
      (lower_isOpen e f) (upper_isOpen e f) (cover e f) k, hr, LinearMap.ker_zero]

def coverHomologyEquiv (k : ℕ) (hk : k ≠ 0) : SingularHomology (overlap e f) k ≃ₗ[ℤ]
    (SingularHomology (lower e f) k × SingularHomology (upper e f) k) :=
  LinearEquiv.ofBijective (leftHomologyMap (lower e f) (upper e f) k)
    (cover_left_bijective e f k hk)

def signedAttachingEquiv (k : ℕ) (hk : k ≠ 0) :
    SingularHomology A k ≃ₗ[ℤ] (SingularHomology Y k × SingularHomology X k) :=
  ((homotopyEquivHomologyEquiv (overlapEquiv e f) k).trans
    (coverHomologyEquiv e f k hk)).trans
      (((homotopyEquivHomologyEquiv (lowerEquiv e f).symm k).toAddEquiv.prodCongr
        (homotopyEquivHomologyEquiv (upperEquiv e f).symm k).toAddEquiv).toIntLinearEquiv)

theorem signedAttachingEquiv_fst (k : ℕ) (hk : k ≠ 0) (a : SingularHomology A k) :
    (signedAttachingEquiv e f k hk a).1 = singularHomologyMap f.hom k a := by
  let ψ : C(A, (lower e f ∩ upper e f : Set (space e f))) := (overlapEquiv e f).toFun
  change singularHomologyMap (lowerRetraction e f) k
    (leftHomologyMap (lower e f) (upper e f) k
      (singularHomologyMap ψ k a)).1 = _
  rw [leftHomologyMap_apply]
  have h := congrArg (fun q ↦ singularHomologyMap q k) (lowerRetraction_midpoint e f)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

theorem signedAttachingEquiv_snd (k : ℕ) (hk : k ≠ 0) (a : SingularHomology A k) :
    (signedAttachingEquiv e f k hk a).2 = -singularHomologyMap e.hom k a := by
  let ψ : C(A, (lower e f ∩ upper e f : Set (space e f))) := (overlapEquiv e f).toFun
  change singularHomologyMap (upperRetraction e f) k
    (leftHomologyMap (lower e f) (upper e f) k
      (singularHomologyMap ψ k a)).2 = _
  rw [leftHomologyMap_apply, map_neg]
  have h := congrArg (fun q ↦ singularHomologyMap q k) (upperRetraction_midpoint e f)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact congrArg Neg.neg (LinearMap.congr_fun h a)

def removeSecondSign (G H : Type*) [AddCommGroup G] [AddCommGroup H] :
    (G × H) ≃ₗ[ℤ] (G × H) where
  toFun p := (p.1, -p.2)
  invFun p := (p.1, -p.2)
  left_inv p := Prod.ext rfl (neg_neg p.2)
  right_inv p := Prod.ext rfl (neg_neg p.2)
  map_add' p q := Prod.ext rfl (neg_add p.2 q.2)
  map_smul' r p := Prod.ext rfl (smul_neg r p.2).symm

def attachingHomologyEquiv (k : ℕ) (hk : k ≠ 0) :
    SingularHomology A k ≃ₗ[ℤ] (SingularHomology Y k × SingularHomology X k) :=
  (signedAttachingEquiv e f k hk).trans
    (removeSecondSign (SingularHomology Y k) (SingularHomology X k))

theorem attachingHomologyEquiv_apply (k : ℕ) (hk : k ≠ 0) (a : SingularHomology A k) :
    attachingHomologyEquiv e f k hk a =
      (singularHomologyMap f.hom k a, singularHomologyMap e.hom k a) := by
  apply Prod.ext
  · exact signedAttachingEquiv_fst e f k hk a
  · change -(signedAttachingEquiv e f k hk a).2 = _
    rw [signedAttachingEquiv_snd, neg_neg]

theorem attaching_homology_bijective (k : ℕ) (hk : k ≠ 0) :
    Function.Bijective (fun a : SingularHomology A k ↦
      (singularHomologyMap f.hom k a, singularHomologyMap e.hom k a)) := by
  have h : (fun a : SingularHomology A k ↦
      (singularHomologyMap f.hom k a, singularHomologyMap e.hom k a)) =
      attachingHomologyEquiv e f k hk := by
    funext a
    exact (attachingHomologyEquiv_apply e f k hk a).symm
  rw [h]
  exact (attachingHomologyEquiv e f k hk).bijective

end NoExoticSixSphere.DoubleMappingCylinder
