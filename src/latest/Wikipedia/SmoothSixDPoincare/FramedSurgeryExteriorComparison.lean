import Wikipedia.SmoothSixDPoincare.FramedSurgeryPresentationComparison
import Wikipedia.SmoothSixDPoincare.FramedSurgerySmoothExterior
import Wikipedia.SmoothSixDPoincare.OpenDiffeomorphCongr

/-!
# The exact boundary comparison is smooth on the whole-piece exteriors

The old exterior coordinates are the identity in the original old
boundary. Composing the two native exterior diffeomorphisms then gives
exactly the already constructed boundary homeomorphism and its inverse
on the complements of the full closed new pieces.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X R Z : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  [TopologicalSpace R] [TopologicalSpace Z] (d : SurgeryBoundaryPair E F R X Z)
  (hface : ∀ p, d.oldPiece p = A.map (oldFaceCoordinates E F p))
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

include hface in
theorem presentationOldOpenExterior_eq :
    ((boundaryPair A n).oldOpenExterior : Set X) = d.oldOpenExterior := by
  change (range ((boundaryPair A n).oldPiece))ᶜ = (range d.oldPiece)ᶜ
  exact congrArg (fun f => (range f)ᶜ) (funext hface).symm

def presentationOldExteriorDiffeomorph :
    Diffeomorph J J (boundaryPair A n).oldOpenExterior d.oldOpenExterior ∞ :=
  OpenDiffeomorph.setCongr (boundaryPair A n).oldOpenExterior d.oldOpenExterior
    (presentationOldOpenExterior_eq A d hface n)

theorem presentationOldExteriorDiffeomorph_coe (x : (boundaryPair A n).oldOpenExterior) :
    (presentationOldExteriorDiffeomorph A d hface n x).val = x.val := rfl

theorem presentationOldOpenCoordinates (x : (boundaryPair A n).oldOpenExterior) :
    presentationExteriorCoordinates A d hface ((boundaryPair A n).oldOpenCoordinates x) =
      d.oldOpenCoordinates (presentationOldExteriorDiffeomorph A d hface n x) := by
  apply d.oldExterior_closed.injective
  rw [presentationExteriorCoordinates_point, d.oldExterior_oldOpenCoordinates]
  exact (boundaryPair A n).oldExterior_oldOpenCoordinates x

namespace SmoothBoundaryData

variable {A n} (P : SmoothBoundaryData A n)
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace W]
  {K : ModelWithCorners ℝ V W} [ChartedSpace W Z]
  (D : Diffeomorph J K d.oldOpenExterior d.newOpenExterior ∞)

def presentationExteriorDiffeomorph :
    letI := P.charted
    Diffeomorph J K (boundaryPair A n).newOpenExterior d.newOpenExterior ∞ := by
  let _ := P.charted
  exact P.openExteriorDiffeomorph.symm.trans
    ((presentationOldExteriorDiffeomorph A d hface n).trans D)

theorem presentationExteriorDiffeomorph_point
    (hD : D.toHomeomorph = d.openExteriorHomeomorph)
    (y : (boundaryPair A n).newOpenExterior) :
    letI := P.charted
    (P.presentationExteriorDiffeomorph d hface D y).val =
      presentationBoundaryHomeomorph A d hface n y.val := by
  let _ := P.charted
  let x := (boundaryPair A n).openExteriorHomeomorph.symm y
  let r := (boundaryPair A n).oldOpenCoordinates x
  have hy : exteriorNewMap A n r = y.val :=
    congrArg Subtype.val ((boundaryPair A n).openExteriorHomeomorph.apply_symm_apply y)
  change (D (presentationOldExteriorDiffeomorph A d hface n x)).val = _
  calc
    _ = d.newExterior (d.oldOpenCoordinates
        (presentationOldExteriorDiffeomorph A d hface n x)) :=
      congrArg (fun h : d.oldOpenExterior ≃ₜ d.newOpenExterior =>
        (h (presentationOldExteriorDiffeomorph A d hface n x)).val) hD
    _ = d.newExterior (presentationExteriorCoordinates A d hface r) :=
      congrArg d.newExterior (presentationOldOpenCoordinates A d hface n x).symm
    _ = presentationBoundaryHomeomorph A d hface n (exteriorNewMap A n r) :=
      (presentationBoundaryHomeomorph_exterior A d hface n r).symm
    _ = presentationBoundaryHomeomorph A d hface n y.val :=
      congrArg (presentationBoundaryHomeomorph A d hface n) hy

theorem presentationExteriorDiffeomorph_symm_point
    (hD : D.toHomeomorph = d.openExteriorHomeomorph) (z : d.newOpenExterior) :
    letI := P.charted
    ((P.presentationExteriorDiffeomorph d hface D).symm z).val =
      (presentationBoundaryHomeomorph A d hface n).symm z.val := by
  let _ := P.charted
  have he := P.presentationExteriorDiffeomorph_point d hface D hD
    ((P.presentationExteriorDiffeomorph d hface D).symm z)
  rw [Diffeomorph.apply_symm_apply] at he
  have hi := congrArg (presentationBoundaryHomeomorph A d hface n).symm he
  rw [Homeomorph.symm_apply_apply] at hi
  exact hi.symm

end SmoothBoundaryData

end Wikipedia.SmoothSixDPoincare.FramedSurgery
