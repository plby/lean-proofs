import Wikipedia.SmoothSixDPoincare.OrderedBandBoundary
import Wikipedia.SmoothSixDPoincare.NativeHandleFaceCoordinates
import Wikipedia.SmoothSixDPoincare.MorseFaceAttachmentTransport
import Wikipedia.SmoothSixDPoincare.NormalizedCoreTube
import Wikipedia.SmoothSixDPoincare.RegularLevelIsotopyExtension

/-!
# The retained band and a level isotopy on the entire original sublevels

The original band restriction agrees exactly with its recorded level map.
The given level isotopy extends to a height-preserving ambient diffeomorphism.
Their composite transports the entire next face by precisely the original
moved-face formula and preserves the native level boundary in both directions.
-/

noncomputable section

open Set Function ContinuousMap Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows.BandData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
  {S : SurgeryWindows E f} {i j : Fin S.count} (B : S.BandData i j)

theorem sublevelHomeomorph_on_level (x : (S.data (S.point i)).UpperLevel) :
    (B.sublevelHomeomorph ⟨x.val, x.property.le⟩).val = (B.level x).val :=
  (B.level_coe x).symm

theorem sublevelHomeomorph_symm_on_level (x : (S.data (S.point j)).LowerLevel) :
    (B.sublevelHomeomorph.symm ⟨x.val, x.property.le⟩).val = (B.level.symm x).val := by
  apply B.ambient.injective
  exact (congrArg Subtype.val (B.sublevelHomeomorph.apply_symm_apply
    ⟨x.val, x.property.le⟩)).trans
      ((congrArg Subtype.val (B.level.apply_symm_apply x)).symm.trans
        (B.level_coe (B.level.symm x)))

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

open Classical in
theorem exists_isotoped_sublevel_bridge
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    letI := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
    let d := S.data (S.point i)
    let d' := S.data (S.point j)
    ∀ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        d.UpperLevel d.UpperLevel ∞,
      SupportedDiffeomorph.IsotopicToIdentity e →
      ∃ A : {x : M // f x ≤ S.lower (S.point j)} ≃ₜ
          {x : M // f x ≤ S.upper (S.point i)},
        (∀ z : d'.handleFace, (d'.transportedFaceMap A z).val =
          (d.movedAttachingFace d' B.level e.toHomeomorph (Homeomorph.refl _)
            (d'.handleFaceCoordinates z)).val) ∧
        ∀ x, f (A x).val = S.upper (S.point i) ↔ f x.val = S.lower (S.point j) := by
  let d := S.data (S.point i)
  let d' := S.data (S.point j)
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro e he
  obtain ⟨_, _, D, _, _, hDlevel, hDheight, _⟩ :=
    RegularLevel.exists_height_preserving_ambient_extension hf d.upper_regular e he
  let U : {x : M // f x ≤ S.upper (S.point i)} ≃ₜ
      {x : M // f x ≤ S.upper (S.point i)} :=
    D.toHomeomorph.subtype (fun x => by
      change f x ≤ S.upper (S.point i) ↔ f (D x) ≤ S.upper (S.point i)
      rw [hDheight])
  let A := B.sublevelHomeomorph.symm.trans U
  refine ⟨A, ?_, ?_⟩
  · intro z
    let x := d'.attachingFace (d'.handleFaceCoordinates z)
    have hB : (B.sublevelHomeomorph.symm (d'.handleFaceToSublevel z)).val =
        (B.level.symm x).val := by
      rw [d'.handleFaceToSublevel_coordinates]
      exact B.sublevelHomeomorph_symm_on_level x
    change D (B.sublevelHomeomorph.symm (d'.handleFaceToSublevel z)).val = _
    rw [hB]
    exact hDlevel (B.level.symm x)
  · intro x
    change f (D (B.sublevelHomeomorph.symm x).val) = S.upper (S.point i) ↔ _
    rw [hDheight]
    exact B.sublevelHomeomorph_symm_level_iff x

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows.BandData
