import Wikipedia.NoExoticSixSphere.MorseHomologyFinite
import Wikipedia.SmoothSixDPoincare.MorseSurgeryEndpoints
import Wikipedia.SmoothSixDPoincare.MorseBandHomology
import Wikipedia.SmoothSixDPoincare.SublevelDiskHomology

/-!
# Finite generation from native compact Morse sublevels

Start with the actual first sublevel disk, propagate through the genuine
Morse handles and regular bands, then use the literal inclusion of the
last sublevel into the original manifold. Its continuous right inverse
proves surjectivity on homology. No homology-finiteness assumption or
replacement smooth structure is used.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseFiniteness

open SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.SmoothSixDPoincare.ManifoldMorse

section Windows

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
    upper_homology_finite S hf k hk j
  let i : C({x : M // f x ≤ S.upper (S.last hc)}, M) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hall : ∀ x : M, f x ≤ S.upper (S.last hc) := by
    intro x
    have hx : x ∈ ({x : M | f x ≤ S.upper (S.last hc)} : Set M) := by
      rw [S.last_upper_univ hf hc]
      exact Set.mem_univ x
    exact hx
  let r : C(M, {x : M // f x ≤ S.upper (S.last hc)}) :=
    ⟨fun x => ⟨x, hall x⟩, continuous_id.subtype_mk _⟩
  have hir : i.comp r = ContinuousMap.id M := rfl
  have hsur : Surjective (singularHomologyMap i (k + 1)) := by
    intro x
    refine ⟨singularHomologyMap r (k + 1) x, ?_⟩
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, hir,
      singularHomologyMap_id, LinearMap.id_apply]
  exact Module.Finite.of_surjective (singularHomologyMap i (k + 1)) hsur

end Windows

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
    exact manifold_homology_finite S hf k hk

theorem compactManifold_middleHomology_finite : Module.Finite ℤ (SingularHomology M 3) :=
  compactManifold_higherHomology_finite E M 2 (by decide)

end Wikipedia.HopfProblem.DegreeCollapse.MorseFiniteness
