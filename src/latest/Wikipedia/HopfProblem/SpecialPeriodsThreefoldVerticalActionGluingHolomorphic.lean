import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionGluingBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalProductLocal

/-!
# Joint analytic gluing on the original threefold atlas

The actual piece inclusions have local analytic inverses.  Their products
with the parameter line detect joint holomorphicity, without imposing a
new topology or first assuming continuity of the global map.
-/

noncomputable section

open Set Topology Filter
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Gluing

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] chartedSpace localPieceChartedSpace

theorem inclusion_isLocalDiffeomorph (i : Index) :
    IsLocalDiffeomorph IF IF ω (inclusion i) := by
  intro x
  exact ((patchBiholomorph i).isLocalDiffeomorph x).comp (K := IF) (P := Space)
    (isLocalDiffeomorph_subtypeVal IF (liftedPatch i) (patchBiholomorph i x))

/-- Joint holomorphicity is local on the actual four piece inclusions,
with the complex parameter unchanged. -/
theorem holomorphic_of_comp_patchLine (f : Space × ℂ → Space)
    (hf : ∀ i, ContMDiff ((IF).prod I₁) IF ω
      (fun p : localPiece i × ℂ => f (inclusion i p.1, p.2))) :
    ContMDiff ((IF).prod I₁) IF ω f := by
  rintro ⟨y, s⟩
  obtain ⟨i, x, rfl⟩ := gluingData.inclusion_jointly_surjective y
  let q : localPiece i × ℂ → Space × ℂ := fun p => (inclusion i p.1, p.2)
  have hq : IsLocalDiffeomorphAt ((IF).prod I₁) ((IF).prod I₁) ω q (x, s) :=
    CanonicalProduct.isLocalDiffeomorphAt_prodLine (inclusion_isLocalDiffeomorph i x)
  have hc : ContMDiff ((IF).prod I₁) IF ω (f ∘ q) := hf i
  have hh := hc.contMDiffAt.comp (q (x, s)) hq.localInverse_contMDiffAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [hq.localInverse_eventuallyEq_right] with z hz
  change f z = f (q (hq.localInverse z))
  exact (congrArg f hz).symm

variable (F : ∀ i : Index, ℂ → localPiece i → localPiece i)
  (hbase : ∀ i s x, localProjectionToBase i (F i s x) = localProjectionToBase i x)
  (hoverlap : ∀ i s x, x ∈ (localOverlap i).source →
    localOverlap i (F (some i) s x) = F none s (localOverlap i x))
  (hF : ∀ i, ContMDiff ((IF).prod I₁) IF ω
    (fun p : localPiece i × ℂ => F i p.2 p.1))

include hF

/-- Actual compatible jointly holomorphic local maps yield a jointly
holomorphic map for the unchanged global threefold atlas. -/
theorem glue_joint_holomorphic :
    ContMDiff ((IF).prod I₁) IF ω
      (fun p : Space × ℂ => glue F hbase hoverlap p.2 p.1) := by
  apply holomorphic_of_comp_patchLine
  intro i
  simp_rw [glue_inclusion]
  exact (inclusion_holomorphic i).comp (hF i)

theorem glue_holomorphic (s : ℂ) : ContMDiff IF IF ω (glue F hbase hoverlap s) := by
  have hi : ContMDiff IF ((IF).prod I₁) ω (fun x : Space => (x, s)) :=
    contMDiff_id.prodMk contMDiff_const
  have hh := (glue_joint_holomorphic F hbase hoverlap hF).comp hi
  simpa only [Function.comp_def] using hh

/-- Opposite local parameters give the actual holomorphic inverse of
the constructed global map. -/
def glueBiholomorph (hzero : ∀ i x, F i 0 x = x)
    (hadd : ∀ i s t x, F i (s + t) x = F i s (F i t x)) (s : ℂ) :
    Diffeomorph IF IF Space Space ω where
  toFun := glue F hbase hoverlap s
  invFun := glue F hbase hoverlap (-s)
  left_inv x := by
    rw [← glue_add F hbase hoverlap hadd, neg_add_cancel, glue_zero F hbase hoverlap hzero]
  right_inv x := by
    rw [← glue_add F hbase hoverlap hadd, add_neg_cancel, glue_zero F hbase hoverlap hzero]
  contMDiff_toFun := glue_holomorphic F hbase hoverlap hF s
  contMDiff_invFun := glue_holomorphic F hbase hoverlap hF (-s)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Gluing
