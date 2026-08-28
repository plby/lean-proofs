import Wikipedia.HopfProblem.DegreeCollapseOrderedInclusionBands

/-!
# The actual canonical middle section classes span the common sublevel homology

Intrinsic counts identify the complete index-three block. Homotopy-sphere
homology and the later native indices make its terminal second homology
zero. The finite literal-inclusion kernel formula then proves spanning
by these actual geometric classes, not by separately chosen relation lifts.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

theorem native_middle_terminal_homology_subsingleton
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (r n : ℕ) (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n) :
    ∃ hrc : r + n < S.toSurgeryWindows.count,
      Subsingleton (SingularHomology
        {y : M // f y ≤ S.toSurgeryWindows.upper (S.toSurgeryWindows.point ⟨r + n, hrc⟩)} 2) := by
  obtain ⟨r', n', htwo, hrc, hthree, hj, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr', hn'⟩ := native_middle_block_counts S.toSurgeryWindows hf r' n' htwo hrc hthree hafter
  have hrr : r' = r := hr'.symm.trans hr
  have hnn : n' = n := hn'.symm.trans hn
  rw [hrr, hnn] at hrc hj hafter
  refine ⟨hrc, ?_⟩
  exact S.toSurgeryWindows.upper_homology_subsingleton_of_later_indices hf hdim e
    ⟨r + n, hrc⟩ hj 2 (by norm_num) (by norm_num)
      (fun i hi _ => by have hh := hafter i hi; exact ⟨by omega, by omega⟩)

theorem nativeMiddleCutSequence_terminal_homology_subsingleton
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (r n : ℕ) (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count) :
    Subsingleton (SingularHomology
      {y : M // f y ≤ nativeMiddleCutSequence S T r n hrc (Fin.last n)} 2) := by
  cases n with
  | zero =>
    obtain ⟨h, hH⟩ := native_middle_terminal_homology_subsingleton
      S hf hdim e horder hzero hone r 0 hr hn
    exact hH
  | succ n =>
    obtain ⟨h, hH⟩ := native_middle_terminal_homology_subsingleton
      T hf hdim e horder hzero hone r (n + 1) hr hn
    exact hH

theorem middle_section_classes_span
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (r n : ℕ) (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hrc j) = 3)
    (hbefore : ∀ j, nativeMiddleBaseCut S r n hrc <
      T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hrc j))
    (γ : Fin n → C(S₂, {y : M // f y = nativeMiddleBaseCut S r n hrc}))
    (horbit : ∀ j x, ∃ t : ℝ, T.flow t
      (nativeIndexThreeAttachingSphere T (nativeMiddleBlockPoint S r n hrc j) (hp j) x).val =
        (γ j x).val) :
    Submodule.span ℤ (range (fun j => middleSectionClass (γ j))) = ⊤ := by
  obtain ⟨h, -, hker⟩ := ordered_middle_inclusion_relations S T hf r n hrc hp hbefore γ horbit
  let _ := nativeMiddleCutSequence_terminal_homology_subsingleton
    S T hf hdim e horder hzero hone r n hr hn hrc
  apply top_unique
  intro v hv
  rw [← hker]
  exact Subsingleton.elim _ _

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
