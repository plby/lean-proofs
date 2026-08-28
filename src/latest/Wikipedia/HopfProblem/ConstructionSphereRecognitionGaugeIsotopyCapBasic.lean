import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCore
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticFullProduct

/-!
# Literal equivariant translations on the original elliptic cap

A smooth real vector on the original disc, with the actual rotation
covariance, gives an additive family of translations of the original
finite-orbit quotient. The construction uses only the original quotient
topology. Its negative parameter is the literal inverse, and the original
base projection and root radius are unchanged.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods
open Elliptic.HigherHomology.MappingTorusQuotient

/-- The actual translation of the underlying varying-period family. -/
def capFamilyTranslation (c : Disc → RealCoordinates) (s : ℝ)
    (p : Disc × RealTorus₄) : Disc × RealTorus₄ :=
  (p.1, p.2 + standardLattice.mkQ (s • c p.1))

@[simp] theorem capFamilyTranslation_apply (c : Disc → RealCoordinates) (s : ℝ)
    (z : Disc) (x : RealTorus₄) :
    capFamilyTranslation c s (z, x) = (z, x + standardLattice.mkQ (s • c z)) := rfl

theorem capFamilyTranslation_continuous (c : Disc → RealCoordinates) (hc : Continuous c)
    (s : ℝ) : Continuous (capFamilyTranslation c s) := by
  have hs : Continuous (fun _ : Disc × RealTorus₄ => s) := continuous_const
  exact continuous_fst.prodMk (continuous_snd.add
    (standardLattice.continuous_mkQ.comp (hs.smul (hc.comp continuous_fst))))

theorem capFamilyTranslation_add (c : Disc → RealCoordinates) (s r : ℝ)
    (p : Disc × RealTorus₄) :
    capFamilyTranslation c (s + r) p =
      capFamilyTranslation c s (capFamilyTranslation c r p) := by
  rcases p with ⟨z, x⟩
  simp only [capFamilyTranslation_apply, add_smul, map_add]
  congr 1
  abel

@[simp] theorem capFamilyTranslation_zero (c : Disc → RealCoordinates)
    (p : Disc × RealTorus₄) : capFamilyTranslation c 0 p = p := by
  rcases p with ⟨z, x⟩
  simp only [capFamilyTranslation_apply, zero_smul, map_zero, add_zero]

/-- The real family translation has exactly its negative as inverse. -/
def capFamilyHomeomorph (c : Disc → RealCoordinates) (hc : Continuous c) (s : ℝ) :
    (Disc × RealTorus₄) ≃ₜ (Disc × RealTorus₄) where
  toFun := capFamilyTranslation c s
  invFun := capFamilyTranslation c (-s)
  left_inv p := by
    rw [← capFamilyTranslation_add, neg_add_cancel, capFamilyTranslation_zero]
  right_inv p := by
    rw [← capFamilyTranslation_add, add_neg_cancel, capFamilyTranslation_zero]
  continuous_toFun := capFamilyTranslation_continuous c hc s
  continuous_invFun := capFamilyTranslation_continuous c hc (-s)

@[simp] theorem capFamilyHomeomorph_apply (c : Disc → RealCoordinates) (hc : Continuous c)
    (s : ℝ) (p : Disc × RealTorus₄) :
    capFamilyHomeomorph c hc s p = capFamilyTranslation c s p := rfl

@[simp] theorem capFamilyHomeomorph_symm_apply (c : Disc → RealCoordinates)
    (hc : Continuous c) (s : ℝ) (p : Disc × RealTorus₄) :
    (capFamilyHomeomorph c hc s).symm p = capFamilyTranslation c (-s) p := rfl

variable {j : Kind} (D : Equivariant.Data j) (c : Disc → RealCoordinates)
  (hc : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, RealCoordinates) ∞ c)
  (hcov : ∀ z, c (familyRotation j z) = flatLinear j (c z))

include hcov in
/-- The genuine vector covariance gives exact commutation with the native
affine generator, before passing to either quotient. -/
theorem capFamilyHomeomorph_permutation (v : Lattice) (s : ℝ) (p : D.TotalSpace) :
    capFamilyHomeomorph c hc.continuous s (D.permutation v p) =
      D.permutation v (capFamilyHomeomorph c hc.continuous s p) := by
  rcases p with ⟨z, x⟩
  change (familyRotation j z,
      flatTorusAffine j v x + standardLattice.mkQ (s • c (familyRotation j z))) =
    (familyRotation j z, flatTorusAffine j v (x + standardLattice.mkQ (s • c z)))
  apply Prod.ext
  · rfl
  · rw [flatTorusAffine_add_mkQ, (flatLinear j).map_smul, hcov]

/-- Translation on the original cap, with the original orbit-quotient topology. -/
def capTranslation (s : ℝ) :
    D.Space j.twist (mainTwist_admissible j) ≃ₜ D.Space j.twist (mainTwist_admissible j) :=
  cyclicQuotientCongr (D.permutation j.twist)
    (D.permutation_pow_order j.twist (mainTwist_admissible j).1)
    (D.permutation j.twist) (D.permutation_pow_order j.twist (mainTwist_admissible j).1)
    (capFamilyHomeomorph c hc.continuous s)
    (capFamilyHomeomorph_permutation D c hc hcov j.twist s)

/-- The descended map retains exactly the given real-period translation. -/
@[simp] theorem capTranslation_quotient (s : ℝ) (z : Disc) (x : RealTorus₄) :
    capTranslation D c hc hcov s (D.quotient j.twist (mainTwist_admissible j) (z, x)) =
      D.quotient j.twist (mainTwist_admissible j)
        (z, x + standardLattice.mkQ (s • c z)) := rfl

/-- Its inverse has the literal opposite real translation on the same cover. -/
@[simp] theorem capTranslation_symm_quotient (s : ℝ) (z : Disc) (x : RealTorus₄) :
    (capTranslation D c hc hcov s).symm
        (D.quotient j.twist (mainTwist_admissible j) (z, x)) =
      D.quotient j.twist (mainTwist_admissible j)
        (z, x + standardLattice.mkQ ((-s) • c z)) := rfl

@[simp] theorem capTranslation_symm_apply (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    (capTranslation D c hc hcov s).symm y = capTranslation D c hc hcov (-s) y := by
  obtain ⟨⟨z, x⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) y
  rfl

@[simp] theorem capTranslation_zero (y : D.Space j.twist (mainTwist_admissible j)) :
    capTranslation D c hc hcov 0 y = y := by
  obtain ⟨⟨z, x⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) y
  simp only [capTranslation_quotient, zero_smul, map_zero, add_zero]

/-- The real parameter acts additively on the actual cap. -/
theorem capTranslation_add (s r : ℝ) (y : D.Space j.twist (mainTwist_admissible j)) :
    capTranslation D c hc hcov (s + r) y =
      capTranslation D c hc hcov s (capTranslation D c hc hcov r y) := by
  obtain ⟨⟨z, x⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) y
  exact congrArg (D.quotient j.twist (mainTwist_admissible j))
    (capFamilyTranslation_add c s r (z, x))

/-- The original power-map projection is fixed pointwise. -/
theorem capTranslation_projection (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    D.projection j.twist (mainTwist_admissible j) (capTranslation D c hc hcov s y) =
      D.projection j.twist (mainTwist_admissible j) y := by
  obtain ⟨⟨z, x⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) y
  rw [capTranslation_quotient, D.projection_quotient, D.projection_quotient]

/-- The norm of the root in the exact frozen cap product is unchanged. -/
theorem capTranslation_root_norm (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    ‖((EllipticFullProduct.fillingProductHomeomorph D
      (capTranslation D c hc hcov s y)).1 : ℂ)‖ =
      ‖((EllipticFullProduct.fillingProductHomeomorph D y).1 : ℂ)‖ := by
  obtain ⟨⟨z, x⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) y
  rw [capTranslation_quotient,
    EllipticFullProduct.fillingProductHomeomorph_quotient_norm,
    EllipticFullProduct.fillingProductHomeomorph_quotient_norm]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
