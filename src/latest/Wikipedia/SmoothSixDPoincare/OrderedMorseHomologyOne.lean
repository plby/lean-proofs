import Wikipedia.SmoothSixDPoincare.MorseHomologyOne
import Wikipedia.SmoothSixDPoincare.SublevelDiskHomology
import Wikipedia.SmoothSixDPoincare.MorseBandHomology
import Wikipedia.SmoothSixDPoincare.MorseSurgeryEndpoints

/-!
# First homology vanishes along the actual index-at-least-two surgery chain

The initial sublevel is the constructed minimum disk. The actual ambient
band maps and Morse exact sequences propagate its first-homology vanishing
to every subsequent lower sublevel before an index-one or additional
index-zero handle. The index restriction remains an explicit global task.
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

theorem lower_homologyOne_subsingleton_of_indices
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin S.count) (hj : 0 < j.val)
    (hindex : ∀ i : Fin S.count, 0 < i.val → i.val < j.val →
      2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) :
    Subsingleton (SingularHomology {x : M // f x ≤ S.lower (S.point j)} 1) := by
  have hupper : ∀ n : ℕ, ∀ hn : n < S.count, n < j.val →
      Subsingleton (SingularHomology {x : M // f x ≤ S.upper (S.point ⟨n, hn⟩)} 1) := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
      exact D.homology_subsingleton 1 one_ne_zero
    | succ n ih =>
      intro hn hnj
      have hn' : n < S.count := by omega
      let : Subsingleton (SingularHomology
          {x : M // f x ≤ f (S.point ⟨n, hn'⟩) +
            (S.data (S.point ⟨n, hn'⟩)).radius ^ 2} 1) := ih hn' (by omega)
      obtain ⟨T, _, hT, _⟩ :=
        S.exists_consecutiveBandBridge hf ⟨n, hn'⟩ ⟨n + 1, hn⟩ rfl
      let H := (S.data (S.point ⟨n, hn'⟩)).bandSublevelHomeomorph
        (S.data (S.point ⟨n + 1, hn⟩)) T.toHomeomorph hT
      let : Subsingleton (SingularHomology
          {x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) -
            (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2} 1) :=
        (homeomorphHomologyEquiv H.symm 1).injective.subsingleton
      exact (S.data (S.point ⟨n + 1, hn⟩)).upperHomologyOne_subsingleton hf.continuous
        (hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj)
  have hp : j.val - 1 < S.count := by omega
  let : Subsingleton (SingularHomology
      {x : M // f x ≤ f (S.point ⟨j.val - 1, hp⟩) +
        (S.data (S.point ⟨j.val - 1, hp⟩)).radius ^ 2} 1) :=
    hupper (j.val - 1) hp (by omega)
  obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf ⟨j.val - 1, hp⟩ j
    (by change j.val - 1 + 1 = j.val; omega)
  let H := (S.data (S.point ⟨j.val - 1, hp⟩)).bandSublevelHomeomorph
    (S.data (S.point j)) T.toHomeomorph hT
  exact (homeomorphHomologyEquiv H.symm 1).injective.subsingleton

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
