import Wikipedia.HopfProblem.ThreefoldHomologyStarTopology
import Wikipedia.HopfProblem.ThreefoldHomologyStarMaps
import Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct

/-!
# Genuine homology coordinates for the threefold star cover

The actual disjoint-union homeomorphisms, followed by the proved singular
chain decomposition, identify the filling and overlap homology with finite
products of the original pieces' homology.  The inverse maps send each
coordinate to the actual inclusion of that component.
-/

noncomputable section

open scoped BigOperators ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris PeriodTorusHigherHomology ThreefoldHomologyStarCoproduct

/-- The regular cover member has its original quotient-family homology. -/
def starRegularHomologyEquiv (n : ℕ) :
    SingularHomology (liftedPatch none) n ≃ₗ[ℤ]
      SingularHomology SpecialRegularFamily n :=
  homeomorphHomologyEquiv originalRegularPatchHomeomorph.symm n

/-- The genuine homology coordinates of the disjoint original fillings. -/
def starFillingsHomologyEquiv (n : ℕ) :
    SingularHomology starFillings n ≃ₗ[ℤ] StarFillingHomology n :=
  ((homeomorphHomologyEquiv starFillingsHomeomorph.symm n).toAddEquiv.trans
    (sigmaHomologyEquiv (fun i : Puncture => localPiece (some i)) n).toAddEquiv).toIntLinearEquiv

/-- The genuine homology coordinates of the disjoint full overlaps. -/
def starOverlapHomologyEquiv (n : ℕ) :
    SingularHomology starOverlap n ≃ₗ[ℤ] StarOverlapHomology n :=
  ((homeomorphHomologyEquiv starOverlapHomeomorph.symm n).toAddEquiv.trans
    (sigmaHomologyEquiv (fun i : Puncture => RegularOverlap i) n).toAddEquiv).toIntLinearEquiv

/-- The original regular family and the three original filling factors. -/
def starPairHomologyEquiv (n : ℕ) :
    (SingularHomology (liftedPatch none) n × SingularHomology starFillings n) ≃ₗ[ℤ]
      StarPairHomology n :=
  ((starRegularHomologyEquiv n).toAddEquiv.prodCongr
    (starFillingsHomologyEquiv n).toAddEquiv).toIntLinearEquiv

@[simp] theorem starRegularHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (liftedPatch none) n) :
    starRegularHomologyEquiv n a = singularHomologyMap
      (originalRegularPatchHomeomorph.symm : C(liftedPatch none, SpecialRegularFamily)) n a := rfl

@[simp] theorem starPairHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (liftedPatch none) n × SingularHomology starFillings n) :
    starPairHomologyEquiv n a =
      (starRegularHomologyEquiv n a.1, starFillingsHomologyEquiv n a.2) := rfl

@[simp] theorem starFillingsHomologyEquiv_symm_apply (n : ℕ) (a : StarFillingHomology n) :
    (starFillingsHomologyEquiv n).symm a =
      singularHomologyMap
        (starFillingsHomeomorph : C((Σ i : Puncture, localPiece (some i)), starFillings)) n
        ((sigmaHomologyEquiv (fun i : Puncture => localPiece (some i)) n).symm a) := rfl

@[simp] theorem starOverlapHomologyEquiv_symm_apply (n : ℕ) (a : StarOverlapHomology n) :
    (starOverlapHomologyEquiv n).symm a =
      singularHomologyMap
        (starOverlapHomeomorph : C((Σ i : Puncture, RegularOverlap i), starOverlap)) n
        ((sigmaHomologyEquiv (fun i : Puncture => RegularOverlap i) n).symm a) := rfl

/-- A single filling coordinate is its actual component inclusion. -/
@[simp] theorem starFillingsHomologyEquiv_symm_single (n : ℕ) (i : Puncture)
    (a : SingularHomology (localPiece (some i)) n) :
    (starFillingsHomologyEquiv n).symm (Pi.single i a) =
      singularHomologyMap (fillingToStar i) n a := by
  rw [starFillingsHomologyEquiv_symm_apply, sigmaHomologyEquiv_symm_single]
  change singularHomologyMap
      (starFillingsHomeomorph : C((Σ i : Puncture, localPiece (some i)), starFillings)) n
      (singularHomologyMap (ContinuousMap.sigmaMk i) n a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, starFillingsHomeomorph_sigmaMk]

/-- A single overlap coordinate is its actual component inclusion. -/
@[simp] theorem starOverlapHomologyEquiv_symm_single (n : ℕ) (i : Puncture)
    (a : SingularHomology (RegularOverlap i) n) :
    (starOverlapHomologyEquiv n).symm (Pi.single i a) =
      singularHomologyMap (overlapToStar i) n a := by
  rw [starOverlapHomologyEquiv_symm_apply, sigmaHomologyEquiv_symm_single]
  change singularHomologyMap
      (starOverlapHomeomorph : C((Σ i : Puncture, RegularOverlap i), starOverlap)) n
      (singularHomologyMap (ContinuousMap.sigmaMk i) n a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, starOverlapHomeomorph_sigmaMk]

@[simp] theorem starFillingsHomologyEquiv_inclusion (n : ℕ) (i : Puncture)
    (a : SingularHomology (localPiece (some i)) n) :
    starFillingsHomologyEquiv n (singularHomologyMap (fillingToStar i) n a) =
      Pi.single i a := by
  apply (starFillingsHomologyEquiv n).symm.injective
  rw [LinearEquiv.symm_apply_apply, starFillingsHomologyEquiv_symm_single]

@[simp] theorem starOverlapHomologyEquiv_inclusion (n : ℕ) (i : Puncture)
    (a : SingularHomology (RegularOverlap i) n) :
    starOverlapHomologyEquiv n (singularHomologyMap (overlapToStar i) n a) =
      Pi.single i a := by
  apply (starOverlapHomologyEquiv n).symm.injective
  rw [LinearEquiv.symm_apply_apply, starOverlapHomologyEquiv_symm_single]

/-- The actual filling inverse is the finite sum of the component maps. -/
theorem starFillingsHomologyEquiv_symm_sum (n : ℕ) (a : StarFillingHomology n) :
    (starFillingsHomologyEquiv n).symm a =
      ∑ i : Puncture, singularHomologyMap (fillingToStar i) n (a i) := by
  conv_lhs => rw [← Finset.univ_sum_single a]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact starFillingsHomologyEquiv_symm_single n i (a i)

/-- The actual overlap inverse is the finite sum of the component maps. -/
theorem starOverlapHomologyEquiv_symm_sum (n : ℕ) (a : StarOverlapHomology n) :
    (starOverlapHomologyEquiv n).symm a =
      ∑ i : Puncture, singularHomologyMap (overlapToStar i) n (a i) := by
  conv_lhs => rw [← Finset.univ_sum_single a]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact starOverlapHomologyEquiv_symm_single n i (a i)

theorem starFillingsHomologyEquiv_decomposition (n : ℕ)
    (a : SingularHomology starFillings n) :
    a = ∑ i : Puncture, singularHomologyMap (fillingToStar i) n
      (starFillingsHomologyEquiv n a i) := by
  have h := starFillingsHomologyEquiv_symm_sum n (starFillingsHomologyEquiv n a)
  rwa [LinearEquiv.symm_apply_apply] at h

theorem starOverlapHomologyEquiv_decomposition (n : ℕ)
    (a : SingularHomology starOverlap n) :
    a = ∑ i : Puncture, singularHomologyMap (overlapToStar i) n
      (starOverlapHomologyEquiv n a i) := by
  have h := starOverlapHomologyEquiv_symm_sum n (starOverlapHomologyEquiv n a)
  rwa [LinearEquiv.symm_apply_apply] at h

/-- The actual component inclusions detect homomorphisms out of the filling union. -/
theorem starFillingsHomology_hom_ext (n : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    (f g : SingularHomology starFillings n →ₗ[ℤ] M)
    (h : ∀ (i : Puncture) (a : SingularHomology (localPiece (some i)) n),
      f (singularHomologyMap (fillingToStar i) n a) =
        g (singularHomologyMap (fillingToStar i) n a)) : f = g := by
  apply LinearMap.ext
  intro a
  rw [starFillingsHomologyEquiv_decomposition n a, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun i _ => h i _)

/-- The actual component inclusions detect homomorphisms out of the full overlap. -/
theorem starOverlapHomology_hom_ext (n : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    (f g : SingularHomology starOverlap n →ₗ[ℤ] M)
    (h : ∀ (i : Puncture) (a : SingularHomology (RegularOverlap i) n),
      f (singularHomologyMap (overlapToStar i) n a) =
        g (singularHomologyMap (overlapToStar i) n a)) : f = g := by
  apply LinearMap.ext
  intro a
  rw [starOverlapHomologyEquiv_decomposition n a, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun i _ => h i _)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
