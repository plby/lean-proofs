import Wikipedia.SmoothSixDPoincare.NativeFullSmoothSequence
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyClosed

/-!
# A constructed full smooth handle decomposition of the original manifold

The endpoints are the canonical empty body and the original manifold with
empty boundary. All critical indices are allowed, and the chain is obtained
from the constructed native Morse function, windows, and band maps.
This decomposition does not yet eliminate any of its handles.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

namespace SurgeryWindows

variable (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
theorem exists_fullSmoothDecomposition (hs : S.HasSmoothExteriors hf) (hcount : 0 < S.count) :
    ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        (SmoothBoundaryBody.empty 𝓘(ℝ, RegularLevel.Model E))
        (SmoothBoundaryBody.closed 𝓘(ℝ, RegularLevel.Model E) M) S.count,
      c.indices = List.ofFn (fun i : Fin S.count =>
        Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) := by
  let _ := S.first_lowerSmoothBody_isEmpty hf hcount
  let _ := S.last_upperSmoothBoundary_isEmpty hf hcount
  obtain ⟨c, hc⟩ := S.exists_fullSmoothSequence hf hs hcount
  let e := SmoothBoundaryBody.toEmptyEquiv ((S.data (S.first hcount)).lowerSmoothBody hf)
  let e' := SmoothBoundaryBody.toClosedEquiv ((S.data (S.last hcount)).upperSmoothBody hf)
    (S.last_upperSmoothBodyHomeomorph hf hcount)
  exact ⟨(c.rebase e).retarget e', ((c.rebase e).retarget_indices e').trans
    ((c.rebase_indices e).trans hc)⟩

end SurgeryWindows

variable (E M) [Nonempty M]

theorem exists_fullSmoothHandleDecomposition (hdim : 0 < Module.finrank ℝ E) :
    ∃ k : ℕ, 2 ≤ k ∧ Nonempty
      (FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        (SmoothBoundaryBody.empty 𝓘(ℝ, RegularLevel.Model E))
        (SmoothBoundaryBody.closed 𝓘(ℝ, RegularLevel.Model E) M) k) := by
  obtain ⟨f, hf, _, S, hs⟩ := exists_morse_function_with_smoothSurgeryWindows E M
  obtain ⟨c, -⟩ := S.exists_fullSmoothDecomposition hf hs (S.count_pos hf)
  exact ⟨S.count, S.two_le_count hf hdim, ⟨c⟩⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
