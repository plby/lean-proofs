import Wikipedia.NoExoticSixSphere.MorseHomologyFinite
import Wikipedia.SmoothSixDPoincare.MorseSurgeryEndpoints
import Wikipedia.SmoothSixDPoincare.MorseBandHomology
import Wikipedia.SmoothSixDPoincare.SublevelDiskHomology

/-!
# Actual higher integral homology of compact smooth manifolds is finitely generated

The finite surgery system is constructed from a smooth Morse function. Start
with its actual first sublevel disk, propagate finite generation through each
genuine Morse attachment and each regular-band homeomorphism, and identify the
last upper sublevel with the original manifold. Degrees at least two suffice
for the middle-dimensional quadratic form and coefficient sequence.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

include S hf

theorem upper_homology_finite (k : ℕ) (hk : k ≠ 0) (j : Fin S.count) :
    Module.Finite ℤ (SingularHomology {x : M // f x ≤ S.upper (S.point j)} (k + 1)) := by
  have H : ∀ i : ℕ, ∀ hi : i < S.count,
      Module.Finite ℤ
        (SingularHomology {x : M // f x ≤ S.upper (S.point ⟨i, hi⟩)} (k + 1)) := by
    intro i
    induction i with
    | zero =>
      intro hi
      obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hi
      let : Subsingleton (SingularHomology
          {x : M // f x ≤ S.upper (S.point ⟨0, hi⟩)} (k + 1)) :=
        D.homology_subsingleton (k + 1) (Nat.succ_ne_zero _)
      infer_instance
    | succ i ih =>
      intro hi
      have hi' : i < S.count := by omega
      let : Module.Finite ℤ
          (SingularHomology {x : M // f x ≤ f (S.point ⟨i, hi'⟩) +
            (S.data (S.point ⟨i, hi'⟩)).radius ^ 2} (k + 1)) := ih hi'
      obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf ⟨i, hi'⟩ ⟨i + 1, hi⟩ rfl
      let H := (S.data (S.point ⟨i, hi'⟩)).bandSublevelHomeomorph
        (S.data (S.point ⟨i + 1, hi⟩)) T.toHomeomorph hT
      let : Module.Finite ℤ (SingularHomology
          {x : M // f x ≤ f (S.point ⟨i + 1, hi⟩) -
            (S.data (S.point ⟨i + 1, hi⟩)).radius ^ 2} (k + 1)) :=
        Module.Finite.of_surjective (homeomorphHomologyEquiv H (k + 1)).toLinearMap
          (homeomorphHomologyEquiv H (k + 1)).surjective
      exact (S.data (S.point ⟨i + 1, hi⟩)).upperHomology_finite hf.continuous k hk
  exact H j.val j.isLt

theorem manifold_homology_finite [Nonempty M] (k : ℕ) (hk : k ≠ 0) :
    Module.Finite ℤ (SingularHomology M (k + 1)) := by
  have hc := S.count_pos hf
  let j : Fin S.count := ⟨S.count - 1, Nat.sub_lt hc zero_lt_one⟩
  let : Module.Finite ℤ
      (SingularHomology {x : M // f x ≤ S.upper (S.last hc)} (k + 1)) :=
    S.upper_homology_finite hf k hk j
  let H : {x : M // f x ≤ S.upper (S.last hc)} ≃ₜ M :=
    (Homeomorph.setCongr (S.last_upper_univ hf hc)).trans (Homeomorph.Set.univ M)
  exact Module.Finite.of_surjective (homeomorphHomologyEquiv H (k + 1)).toLinearMap
    (homeomorphHomologyEquiv H (k + 1)).surjective

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

namespace NoExoticSixSphere

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

include E

theorem compactManifold_higherHomology_finite (k : ℕ) (hk : k ≠ 0) :
    Module.Finite ℤ (SingularHomology M (k + 1)) := by
  cases isEmpty_or_nonempty M with
  | inl h =>
    let := h
    let := totallyDisconnected_homology_subsingleton M (k + 1) (Nat.succ_ne_zero _)
    infer_instance
  | inr h =>
    let := h
    obtain ⟨f, hf, _, ⟨S⟩⟩ := exists_morse_function_with_surgeryWindows E M
    exact S.manifold_homology_finite hf k hk

theorem compactManifold_middleHomology_finite : Module.Finite ℤ (SingularHomology M 3) :=
  compactManifold_higherHomology_finite E M 2 (by decide)

end NoExoticSixSphere
