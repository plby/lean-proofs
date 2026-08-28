import Wikipedia.SmoothSixDPoincare.SmoothFaceDescent
import Wikipedia.SmoothSixDPoincare.ShrunkFaceAttachmentRealization
import Wikipedia.SmoothSixDPoincare.RegularLevelIsotopyExtension

/-!
# Whole-attachment realization of a downward face move

Extend the retained upper-level isotopy to a height-preserving ambient
diffeomorphism and undo it after the shrunk realization. The resulting
whole-handle quotient sends the lower face exactly to the original upper
face, not just its isotoped image. All original handle coordinates remain.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M} {d : MorseSurgeryData E f p}
  {hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f}
  {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {I : ModelWithCorners ℝ G H} {X N : Type*} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  {g : d.UpperSmoothFace hf I X N} (T : d.FaceDescent hf I X N g)

structure Realization where
  ambient : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞
  height : ∀ x, f (ambient x) = f x
  level : letI := RegularLevel.chartedSpace hf d.upper_regular;
    ∀ x : d.UpperLevel, ambient x.val = (T.upperMap x).val

variable [T2Space M] [CompactSpace M]

theorem nonempty_realization : Nonempty T.Realization := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  obtain ⟨_, _, D, _, _, hlevel, hheight, _⟩ :=
    RegularLevel.exists_height_preserving_ambient_extension hf d.upper_regular T.upperMap T.isotopic
  exact ⟨⟨D, hheight, hlevel⟩⟩

namespace Realization

variable {T} (A : T.Realization)

def upperCorrection : {x : M // f x ≤ f p + d.radius ^ 2} ≃ₜ
    {x : M // f x ≤ f p + d.radius ^ 2} :=
  (A.ambient.toHomeomorph.subtype (fun x => by
    change f x ≤ f p + d.radius ^ 2 ↔ f (A.ambient x) ≤ f p + d.radius ^ 2
    rw [A.height])).symm

omit [T2Space M] [CompactSpace M] in
theorem upperCorrection_coe (x : {x : M // f x ≤ f p + d.radius ^ 2}) :
    (A.upperCorrection x).val = A.ambient.symm x.val := rfl

open Classical in
def faceQuotientRealization : FaceAttachment.Space d.handleFaceToSublevel ≃ₜ
    {x : M // f x ≤ f p + d.radius ^ 2} :=
  (T.shrunk.faceQuotientRealization hf.continuous).trans A.upperCorrection

open Classical in
theorem faceQuotientRealization_old (x : {y : M // f y ≤ f p - d.radius ^ 2}) :
    (A.faceQuotientRealization (FaceAttachment.oldMap d.handleFaceToSublevel x)).val =
      A.ambient.symm (T.shrunk.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩).val := by
  change (A.upperCorrection (T.shrunk.faceQuotientRealization hf.continuous
    (FaceAttachment.oldMap d.handleFaceToSublevel x))).val = _
  rw [T.shrunk.faceQuotientRealization_old, A.upperCorrection_coe]

open Classical in
theorem faceQuotientRealization_handle (z : d.HandleDomain) :
    (A.faceQuotientRealization (FaceAttachment.handleMap d.handleFaceToSublevel z)).val =
      A.ambient.symm
        (T.shrunk.attachmentHomeomorph ⟨d.handleMap z, Or.inr ⟨z, rfl⟩⟩).val := by
  change (A.upperCorrection (T.shrunk.faceQuotientRealization hf.continuous
    (FaceAttachment.handleMap d.handleFaceToSublevel z))).val = _
  rw [T.shrunk.faceQuotientRealization_handle, A.upperCorrection_coe]

open Classical in
theorem faceQuotientRealization_face :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ z, A.faceQuotientRealization (FaceAttachment.oldMap d.handleFaceToSublevel
        ⟨(T.lower.map z).val, (T.lower.map z).property.le⟩) =
      ⟨(g.map z).val, (g.map z).property.le⟩ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro z
  apply Subtype.ext
  rw [A.faceQuotientRealization_old]
  apply A.ambient.injective
  change A.ambient (A.ambient.symm _) = A.ambient _
  rw [A.ambient.apply_symm_apply]
  exact (T.face_eq z).trans (A.level (g.map z)).symm

end Realization

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent
