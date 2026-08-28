import Wikipedia.SmoothSixDPoincare.FramedSurgeryBoundaryPair
import Wikipedia.SmoothSixDPoincare.FramedSurgerySmoothBoundary
import Wikipedia.SmoothSixDPoincare.OpenSurgeryExterior

/-!
# The constructed smooth boundary retains the exact smooth open exterior

Outside the entire old and new closed faces, the common-exterior
homeomorphism is a native diffeomorphism. Its two maps are the original
old-patch map and its smooth inverse. This does not assert smoothness of
an arbitrary whole-body or whole-boundary realization.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

theorem oldWholeExterior_mem_oldPatch (x : (boundaryPair A n).oldOpenExterior) :
    x.val ∈ oldPatch A := by
  rintro ⟨u, hu⟩
  exact x.property ⟨(u, ballZero), hu⟩

def oldWholeExteriorToPatch : C((boundaryPair A n).oldOpenExterior, oldPatch A) := by
  refine ⟨fun x => ⟨x.val, oldWholeExterior_mem_oldPatch A n x⟩, ?_⟩
  exact continuous_subtype_val.subtype_mk _

theorem contMDiff_oldWholeExteriorToPatch :
    ContMDiff J J ∞ (oldWholeExteriorToPatch A n) :=
  (ContMDiff.subtypeVal_comp_iff (oldPatch A) _).mp contMDiff_subtype_val

theorem openExteriorHomeomorph_eq_oldMap (x : (boundaryPair A n).oldOpenExterior) :
    ((boundaryPair A n).openExteriorHomeomorph x).val =
      oldMap A n (oldWholeExteriorToPatch A n x) := by
  change oldMap A n (exteriorToOldPatch A ((boundaryPair A n).oldOpenCoordinates x)) = _
  exact congrArg (oldMap A n)
    (Subtype.ext ((boundaryPair A n).oldExterior_oldOpenCoordinates x))

namespace SmoothBoundaryData

variable {A n} (P : SmoothBoundaryData A n)

theorem openExteriorHomeomorph_eq_oldPartial (x : (boundaryPair A n).oldOpenExterior) :
    letI := P.charted
    ((boundaryPair A n).openExteriorHomeomorph x).val =
      P.oldPartial (oldWholeExteriorToPatch A n x) := by
  let _ := P.charted
  exact (openExteriorHomeomorph_eq_oldMap A n x).trans (P.old_point _).symm

theorem openExteriorHomeomorph_symm_eq_oldPartial
    (y : (boundaryPair A n).newOpenExterior) :
    letI := P.charted
    P.oldPartial.symm y.val =
      oldWholeExteriorToPatch A n ((boundaryPair A n).openExteriorHomeomorph.symm y) := by
  let _ := P.charted
  have he := P.openExteriorHomeomorph_eq_oldPartial
    ((boundaryPair A n).openExteriorHomeomorph.symm y)
  rw [Homeomorph.apply_symm_apply] at he
  rw [he]
  exact P.oldPartial.left_inv (P.old_source ▸ mem_univ _)

theorem newOpenExterior_mem_oldPartial_target (y : (boundaryPair A n).newOpenExterior) :
    letI := P.charted; y.val ∈ P.oldPartial.target := by
  let _ := P.charted
  have he := P.openExteriorHomeomorph_eq_oldPartial
    ((boundaryPair A n).openExteriorHomeomorph.symm y)
  rw [Homeomorph.apply_symm_apply] at he
  rw [he]
  exact P.oldPartial.map_source (P.old_source ▸ mem_univ _)

theorem contMDiff_openExteriorHomeomorph :
    letI := P.charted
    ContMDiff J J ∞ (boundaryPair A n).openExteriorHomeomorph := by
  let _ := P.charted
  apply (ContMDiff.subtypeVal_comp_iff (boundaryPair A n).newOpenExterior _).mp
  exact (P.oldPartial.contMDiffOn.comp_contMDiff (contMDiff_oldWholeExteriorToPatch A n)
    (fun _ => P.old_source ▸ mem_univ _)).congr P.openExteriorHomeomorph_eq_oldPartial

theorem contMDiff_openExteriorHomeomorph_symm :
    letI := P.charted
    ContMDiff J J ∞ (boundaryPair A n).openExteriorHomeomorph.symm := by
  let _ := P.charted
  apply (ContMDiff.subtypeVal_comp_iff (boundaryPair A n).oldOpenExterior _).mp
  have hc : ContMDiff J J ∞ (fun y : (boundaryPair A n).newOpenExterior =>
      P.oldPartial.symm y.val) :=
    P.oldPartial.symm.contMDiffOn.comp_contMDiff contMDiff_subtype_val
      P.newOpenExterior_mem_oldPartial_target
  have hv : ContMDiff J J ∞ (fun y : (boundaryPair A n).newOpenExterior =>
      (P.oldPartial.symm y.val).val) := contMDiff_subtype_val.comp hc
  exact hv.congr (fun y => (congrArg (fun x : oldPatch A => x.val)
    (P.openExteriorHomeomorph_symm_eq_oldPartial y)).symm)

def openExteriorDiffeomorph :
    letI := P.charted
    Diffeomorph J J (boundaryPair A n).oldOpenExterior (boundaryPair A n).newOpenExterior ∞ := by
  let _ := P.charted
  exact {
    toEquiv := (boundaryPair A n).openExteriorHomeomorph.toEquiv
    contMDiff_toFun := P.contMDiff_openExteriorHomeomorph
    contMDiff_invFun := P.contMDiff_openExteriorHomeomorph_symm }

theorem openExteriorDiffeomorph_toHomeomorph :
    letI := P.charted
    P.openExteriorDiffeomorph.toHomeomorph = (boundaryPair A n).openExteriorHomeomorph := rfl

end SmoothBoundaryData

end Wikipedia.SmoothSixDPoincare.FramedSurgery
