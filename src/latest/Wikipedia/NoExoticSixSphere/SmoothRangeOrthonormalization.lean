import Wikipedia.NoExoticSixSphere.RectangularSmoothNormalization
import Wikipedia.NoExoticSixSphere.SmoothFrameCoordinates

/-!
# Orthonormalizing the given smooth range frame

The original ambient frame is normalized by Gram--Schmidt, preserving its
actual range. Smoothness is proved in the original manifold charts by
composition with the smooth normalization map on injective operators.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization Stiefel

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] {N k : ℕ}

theorem Stiefel.Orthonormalization.contMDiff_operator {A : M → Vector k →L[ℝ] Vector N}
    (hA : ContMDiff I 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ A)
    (hi : ∀ x, Function.Injective (A x)) :
    ContMDiff I 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (operator A) := by
  intro x
  have h := contDiffAt_operator (id : (Vector k →L[ℝ] Vector N) →
    Vector k →L[ℝ] Vector N) (A x) contDiffAt_id (hi x)
  exact h.contMDiffAt.comp x hA.contMDiffAt

namespace SmoothRangeFrame

variable {P : M → Vector N →L[ℝ] Vector N} (a : SmoothRangeFrame I P (Vector k))

theorem ambient_range (x : M) : (a.ambient x).range = (P x).range := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact (a.equiv x v).property
  · intro hy
    obtain ⟨v, hv⟩ := (a.equiv x).surjective ⟨y, hy⟩
    exact ⟨v, congrArg Subtype.val hv⟩

def orthonormal (x : M) : Space N k :=
  ⟨Orthonormalization.operator a.ambient x,
    Orthonormalization.operator_norm a.ambient x (a.ambient_injective x)⟩

theorem orthonormal_range (x : M) : (a.orthonormal x).val.range = (P x).range :=
  (Orthonormalization.operator_range a.ambient x (a.ambient_injective x)).trans
    (a.ambient_range x)

theorem contMDiff_orthonormal :
    ContMDiff I 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun x ↦ (a.orthonormal x).val) :=
  Orthonormalization.contMDiff_operator a.smooth a.ambient_injective

end SmoothRangeFrame

end NoExoticSixSphere
