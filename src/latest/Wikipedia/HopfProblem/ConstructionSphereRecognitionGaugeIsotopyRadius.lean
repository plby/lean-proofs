import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopySmallCollar

/-!
# The smooth invariant root radius in the original cap atlas

The squared root radius is well defined on the native finite quotient.
Its smoothness is checked on the original complex-vector covering, where
it is literally the squared norm of the original disc coordinate.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods SpecialPeriods.EllipticFilling SpecialPeriods.Threefold
open ThreefoldOverlapMappingTorus ThreefoldOverlapMappingTorus.Elliptic

local notation "IR" => modelWithCornersSelf ℝ FamilyModel

attribute [local instance] capVectorChartedSpace

variable {j : Kind} (D : Equivariant.Data j)

local instance radiusFillingChartedSpace :
    ChartedSpace FamilyModel (D.Space j.twist (mainTwist_admissible j)) :=
  D.chartedSpace j.twist (mainTwist_admissible j)

/-- The actual squared radius in the unchanged full-cap product. -/
def capRootSquared (y : D.Space j.twist (mainTwist_admissible j)) : ℝ :=
  ‖((EllipticFullProduct.fillingProductHomeomorph D y).1 : ℂ)‖ ^ 2

@[simp] theorem capRootSquared_quotient (z : Disc) (x : RealTorus₄) :
    capRootSquared D (D.quotient j.twist (mainTwist_admissible j) (z, x)) = ‖(z : ℂ)‖ ^ 2 := by
  rw [capRootSquared, EllipticFullProduct.fillingProductHomeomorph_quotient_norm]

@[simp] theorem capRootSquared_fillingCover (p : Disc × ComplexPlane₂) :
    capRootSquared D (EllipticSmooth.fillingCover D p) = ‖(p.1 : ℂ)‖ ^ 2 :=
  capRootSquared_quotient D p.1 (D.periods.quotientMap p).2

private theorem complexNormSquared_contDiff : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2) := by
  have he : (fun z : ℂ => ‖z‖ ^ 2) = (fun z : ℂ => z.re ^ 2 + z.im ^ 2) := by
    funext z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [he]
  exact (Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)

/-- The radius is smooth because its lift to the original cover is the native squared norm. -/
theorem capRootSquared_contMDiff : ContMDiff IR 𝓘(ℝ, ℝ) ∞ (capRootSquared D) := by
  apply EllipticSmooth.contMDiff_of_comp_real_localDiffeomorph
    (EllipticSmooth.fillingCover_real_isLocalDiffeomorph D)
    (EllipticSmooth.fillingCover_surjective D)
  have hb : ContMDiff IR 𝓘(ℝ, ℂ) ∞ (fun p : Disc × ComplexPlane₂ => (p.1 : ℂ)) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_subtype_val.comp contMDiff_fst
  exact (complexNormSquared_contDiff.contMDiff.comp hb).congr (capRootSquared_fillingCover D)

theorem capRootSquared_collarTranslation (τ θ a : ℝ) (ha : 0 < a) (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    capRootSquared D (collarTranslation D τ θ a ha s y) = capRootSquared D y := by
  rw [capRootSquared, capRootSquared, collarTranslation_root_norm]

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace

/-- Restriction of the same radius to the literal original small piece. -/
def smallRootSquared (j : Kind) (y : SpecialEllipticPiece j) : ℝ :=
  capRootSquared (specialLocalData j) y.val

theorem smallRootSquared_contMDiff (j : Kind) :
    ContMDiff IR 𝓘(ℝ, ℝ) ∞ (smallRootSquared j) :=
  (capRootSquared_contMDiff (specialLocalData j)).comp
    (EllipticSmooth.smallPiece_inclusion_contMDiff j)

theorem smallRootSquared_collar (j : Kind) (τ θ : ℝ) (a : CollarRadius j)
    (s : ℝ) (y : SpecialEllipticPiece j) :
    smallRootSquared j (smallCollarHomeomorph j τ θ a s y) = smallRootSquared j y :=
  capRootSquared_collarTranslation (specialLocalData j) τ θ a a.property.1 s y.val

/-- The actual boundary radius has exactly its declared value, for every fibre point. -/
theorem smallRootSquared_boundaryToPieceAt (j : Kind) (a : CollarRadius j) (θ : ℝ)
    (x : SpecialBoundary j) :
    smallRootSquared j (specialBoundaryToPieceAt j a θ x) = (a : ℝ) ^ 2 := by
  obtain ⟨⟨t, u⟩, rfl⟩ := MappingTorus.mk_surjective (flatTorusAffine j j.twist) x
  change capRootSquared (specialLocalData j)
    ((specialBoundaryInclusionAt j a θ
      (MappingTorus.mk (flatTorusAffine j j.twist) (t, u))).val :
        SpecialEllipticPiece j).val = (a : ℝ) ^ 2
  rw [specialBoundaryInclusionAt_mk, capRootSquared_quotient, root_norm]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
