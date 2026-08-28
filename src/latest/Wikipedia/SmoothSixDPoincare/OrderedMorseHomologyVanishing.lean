import Wikipedia.SmoothSixDPoincare.MorseHomologyPropagation
import Wikipedia.SmoothSixDPoincare.MorseBandHomology
import Wikipedia.SmoothSixDPoincare.TerminalSublevelHomology

/-!
# Propagate the original homotopy-sphere homology backward through the finite chain

The terminal lower sublevel has the homology vanishing already derived
from the original homotopy equivalence. Descending through the actual band
homeomorphisms and nonmatching handle indices gives vanishing above a
chosen earlier handle, without assuming homology of intermediate sublevels.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : SurgeryWindows E f)

theorem upper_homology_subsingleton_of_later_indices
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hM : M ≃ₕ SixSphere) (j : Fin S.count) (hj : j.val + 1 < S.count)
    (k : ℕ) (hk : 0 < k) (hk5 : k < 5)
    (hindex : ∀ i : Fin S.count, j.val < i.val → i.val + 1 < S.count →
      2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ∧
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ≠ k + 1) :
    Subsingleton (SingularHomology {x : M // f x ≤ S.upper (S.point j)} k) := by
  have hcount : 0 < S.count := by omega
  let P : ℕ → Prop := fun i => ∀ hi : i < S.count,
    Subsingleton (SingularHomology {x : M // f x ≤ S.lower (S.point ⟨i, hi⟩)} k)
  have hlow : P (j.val + 1) := by
    apply Nat.decreasingInduction' (P := P) (m := j.val + 1) (n := S.count - 1)
    · intro i hi hji ih hi'
      have hs : i + 1 < S.count := by omega
      let : Subsingleton (SingularHomology
          {x : M // f x ≤ f (S.point ⟨i + 1, hs⟩) -
            (S.data (S.point ⟨i + 1, hs⟩)).radius ^ 2} k) := ih hs
      obtain ⟨T, _, hT, _⟩ :=
        S.exists_consecutiveBandBridge hf ⟨i, hi'⟩ ⟨i + 1, hs⟩ rfl
      let H := (S.data (S.point ⟨i, hi'⟩)).bandSublevelHomeomorph
        (S.data (S.point ⟨i + 1, hs⟩)) T.toHomeomorph hT
      let : Subsingleton (SingularHomology
          {x : M // f x ≤ f (S.point ⟨i, hi'⟩) +
            (S.data (S.point ⟨i, hi'⟩)).radius ^ 2} k) :=
        (homeomorphHomologyEquiv H k).injective.subsingleton
      obtain ⟨hlo, hne⟩ := hindex ⟨i, hi'⟩ (by change j.val < i; omega) hs
      exact (S.data (S.point ⟨i, hi'⟩)).lowerHomology_subsingleton_of_upper_and_index
        hf.continuous k hk.ne' hlo hne
    · omega
    · intro hi
      exact S.lastLower_homology_subsingleton hf hdim hM hcount k hk hk5
  let : Subsingleton (SingularHomology
      {x : M // f x ≤ f (S.point ⟨j.val + 1, hj⟩) -
        (S.data (S.point ⟨j.val + 1, hj⟩)).radius ^ 2} k) := hlow hj
  obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf j ⟨j.val + 1, hj⟩ rfl
  let H := (S.data (S.point j)).bandSublevelHomeomorph
    (S.data (S.point ⟨j.val + 1, hj⟩)) T.toHomeomorph hT
  exact (homeomorphHomologyEquiv H k).injective.subsingleton

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
