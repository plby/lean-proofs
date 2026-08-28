import Wikipedia.SmoothSixDPoincare.AttachedHandleCollarImage
import Wikipedia.SmoothSixDPoincare.NativeInwardBoundaryCollar
import Wikipedia.SmoothSixDPoincare.SmoothHandleChain

/-!
# Construct collars after arbitrary framed attachments and along smooth chains

The original collar produces the new one by the proved whole-handle
construction, including the corner and the open-image identity. Commuting
realizations then transport it to the next body, so finite iteration does
not assume collars on the modified stages.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H}

namespace SmoothBoundaryBody

variable (U : SmoothBoundaryBody J)
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (PuncturedHandle.UnitSphere E) F U.boundary)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]
  (P : FramedSurgery.SmoothBoundaryData A n)

theorem attach_hasInwardCollar (hU : U.HasInwardCollar) : (U.attach A n P).HasInwardCollar := by
  obtain ⟨C⟩ := hU
  exact ⟨FramedSurgery.inwardCollar A U.inclusion C U.closedEmbedding n⟩

end SmoothBoundaryBody

namespace SmoothHandleChain

theorem hasInwardCollar {U V : SmoothBoundaryBody J} {k : ℕ}
    (c : SmoothHandleChain J U V k) (hU : U.HasInwardCollar) : V.HasInwardCollar := by
  revert hU
  induction c with
  | nil r => exact SmoothBoundaryBody.hasInwardCollar_transport r
  | @cons U V W k E F _ _ _ _ _ _ m n _ _ A P r c ih =>
      intro hU
      exact ih (SmoothBoundaryBody.hasInwardCollar_transport r
        (U.attach_hasInwardCollar A n P hU))

end SmoothHandleChain
end Wikipedia.SmoothSixDPoincare
