import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCapBasic
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCapLift
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothCovers

/-!
# Joint smoothness of the original cap translations

The literal vector-cover translation is jointly real smooth. The product
of the identity on the real parameter with the original filling covering
is a local diffeomorphism, so this regularity descends in the unchanged
quotient atlas. No smooth group structure on the bare real torus is used.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods

local notation "IR" => modelWithCornersSelf ℝ FamilyModel
local notation "IT" => modelWithCornersSelf ℝ (ℝ × FamilyModel)

variable {j : Kind} (D : Equivariant.Data j)

attribute [local instance] capVectorChartedSpace capTimeVectorChartedSpace

/-- The filling chart is exactly the original chart selected from the given period family. -/
local instance capFillingChartedSpace :
    ChartedSpace FamilyModel (D.Space j.twist (mainTwist_admissible j)) :=
  D.chartedSpace j.twist (mainTwist_admissible j)

/-- The time-dependent cap uses only the native product of the real line
and the original filling atlas. -/
@[instance_reducible] def capTimeFillingChartedSpace :
    ChartedSpace (ℝ × FamilyModel) (ℝ × D.Space j.twist (mainTwist_admissible j)) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ FamilyModel)
    (ℝ × D.Space j.twist (mainTwist_admissible j)))

attribute [local instance] capTimeFillingChartedSpace

/-- The parameter-preserving product of the original filling vector cover. -/
def capTimeCover (p : ℝ × (Disc × ComplexPlane₂)) :
    ℝ × D.Space j.twist (mainTwist_admissible j) :=
  (p.1, EllipticSmooth.fillingCover D p.2)

@[simp] theorem capTimeCover_apply (s : ℝ) (p : Disc × ComplexPlane₂) :
    capTimeCover D (s, p) = (s, EllipticSmooth.fillingCover D p) := rfl

theorem capTimeCover_surjective : Function.Surjective (capTimeCover D) := by
  rintro ⟨s, y⟩
  obtain ⟨p, rfl⟩ := EllipticSmooth.fillingCover_surjective D y
  exact ⟨(s, p), rfl⟩

/-- The product cover has the original real-analytic local inverse charts. -/
theorem capTimeCover_isLocalDiffeomorph :
    IsLocalDiffeomorph IT IT ω (capTimeCover D) := by
  have h := EllipticSmooth.isLocalDiffeomorph_prodLeft 𝓘(ℝ, ℝ) (B := ℝ)
    (EllipticSmooth.fillingCover_real_isLocalDiffeomorph D)
  rw [modelWithCornersSelf_prod]
  exact h

variable (c : Disc → RealCoordinates)
  (hc : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, RealCoordinates) ∞ c)
  (hcov : ∀ z, c (familyRotation j z) = flatLinear j (c z))

/-- The vector lift commutes with the original lattice and finite quotient
maps, with the exact real translation retained. -/
theorem capTranslation_fillingCover (s : ℝ) (p : Disc × ComplexPlane₂) :
    capTranslation D c hc hcov s (EllipticSmooth.fillingCover D p) =
      EllipticSmooth.fillingCover D (capVectorTranslation D c s p) := by
  calc
    _ = D.quotient j.twist (mainTwist_admissible j)
        (p.1, (D.periods.quotientMap p).2 + standardLattice.mkQ (s • c p.1)) :=
      capTranslation_quotient D c hc hcov s p.1 (D.periods.quotientMap p).2
    _ = _ := congrArg (D.quotient j.twist (mainTwist_admissible j))
      (capVectorTranslation_quotientMap D c s p).symm

/-- Joint real smoothness in time and the original filling point. -/
theorem capTranslation_joint_contMDiff :
    ContMDiff IT IR ∞ (fun p : ℝ × D.Space j.twist (mainTwist_admissible j) =>
      capTranslation D c hc hcov p.1 p.2) := by
  apply EllipticSmooth.contMDiff_of_comp_real_localDiffeomorph
    (capTimeCover_isLocalDiffeomorph D) (capTimeCover_surjective D)
  have hq : ContMDiff IR IR ∞ (EllipticSmooth.fillingCover D) :=
    (EllipticSmooth.fillingCover_real_isLocalDiffeomorph D).contMDiff.of_le le_top
  exact (hq.comp (capVectorTranslation_joint_contMDiff D hc)).congr
    (fun p => capTranslation_fillingCover D c hc hcov p.1 p.2)

theorem capTranslation_joint_continuous :
    Continuous (fun p : ℝ × D.Space j.twist (mainTwist_admissible j) =>
      capTranslation D c hc hcov p.1 p.2) :=
  (capTranslation_joint_contMDiff D c hc hcov).continuous

private theorem capTimeReverse_contMDiff :
    ContMDiff IT IT ∞
      (fun p : ℝ × D.Space j.twist (mainTwist_admissible j) => (-p.1, p.2)) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst.neg.prodMk contMDiff_snd

/-- The inverse family is jointly smooth as well, by the exact negative-time formula. -/
theorem capTranslation_symm_joint_contMDiff :
    ContMDiff IT IR ∞ (fun p : ℝ × D.Space j.twist (mainTwist_admissible j) =>
      (capTranslation D c hc hcov p.1).symm p.2) :=
  ((capTranslation_joint_contMDiff D c hc hcov).comp (capTimeReverse_contMDiff D)).congr
    (fun p => capTranslation_symm_apply D c hc hcov p.1 p.2)

private theorem capTimeInsert_contMDiff (s : ℝ) :
    ContMDiff IR IT ∞
      (fun y : D.Space j.twist (mainTwist_admissible j) => (s, y)) := by
  have hs : ContMDiff IR 𝓘(ℝ, ℝ) ∞
      (fun _ : D.Space j.twist (mainTwist_admissible j) => s) := contMDiff_const
  have hi : ContMDiff IR IR ∞
      (id : D.Space j.twist (mainTwist_admissible j) →
        D.Space j.twist (mainTwist_admissible j)) := contMDiff_id
  have hp := hs.prodMk hi
  rw [← modelWithCornersSelf_prod] at hp
  exact hp

/-- Every time slice is smooth in the unchanged quotient atlas. -/
theorem capTranslation_contMDiff (s : ℝ) :
    ContMDiff IR IR ∞ (capTranslation D c hc hcov s) := by
  change ContMDiff IR IR ∞
    ((fun p : ℝ × D.Space j.twist (mainTwist_admissible j) =>
      capTranslation D c hc hcov p.1 p.2) ∘
      (fun y : D.Space j.twist (mainTwist_admissible j) => (s, y)))
  exact (capTranslation_joint_contMDiff D c hc hcov).comp (capTimeInsert_contMDiff D s)

/-- The literal negative translation proves smoothness of the actual inverse. -/
theorem capTranslation_symm_contMDiff (s : ℝ) :
    ContMDiff IR IR ∞ (capTranslation D c hc hcov s).symm :=
  (capTranslation_contMDiff D c hc hcov (-s)).congr
    (fun y => capTranslation_symm_apply D c hc hcov s y)

/-- The original quotient atlas is a real smooth manifold. -/
theorem cap_isRealManifold : IsManifold IR ∞ (D.Space j.twist (mainTwist_admissible j)) := by
  let := D.isManifold j.twist (mainTwist_admissible j)
  exact complexManifold_isRealManifold _ ∞

/-- A real smooth cap translation with the exact original underlying homeomorphism. -/
def capTranslationDiffeomorph (s : ℝ) :
    Diffeomorph IR IR (D.Space j.twist (mainTwist_admissible j))
      (D.Space j.twist (mainTwist_admissible j)) ∞ where
  toEquiv := (capTranslation D c hc hcov s).toEquiv
  contMDiff_toFun := capTranslation_contMDiff D c hc hcov s
  contMDiff_invFun := capTranslation_symm_contMDiff D c hc hcov s

@[simp] theorem capTranslationDiffeomorph_apply (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    capTranslationDiffeomorph D c hc hcov s y = capTranslation D c hc hcov s y := rfl

@[simp] theorem capTranslationDiffeomorph_symm_apply (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    (capTranslationDiffeomorph D c hc hcov s).symm y =
      capTranslation D c hc hcov (-s) y :=
  capTranslation_symm_apply D c hc hcov s y

@[simp] theorem capTranslationDiffeomorph_toHomeomorph (s : ℝ) :
    (capTranslationDiffeomorph D c hc hcov s).toHomeomorph =
      capTranslation D c hc hcov s := by
  apply Homeomorph.ext
  intro y
  rfl

@[simp] theorem capTranslationDiffeomorph_quotient (s : ℝ) (z : Disc) (x : RealTorus₄) :
    capTranslationDiffeomorph D c hc hcov s
        (D.quotient j.twist (mainTwist_admissible j) (z, x)) =
      D.quotient j.twist (mainTwist_admissible j)
        (z, x + standardLattice.mkQ (s • c z)) := rfl

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
