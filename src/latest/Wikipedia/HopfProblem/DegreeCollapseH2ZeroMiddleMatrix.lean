import Wikipedia.HopfProblem.DegreeCollapseMiddleHomologyVanishing
import Wikipedia.HopfProblem.DegreeCollapseCanonicalMiddleMatrix

/-!
# Actual middle matrices from H2 vanishing alone

The actual original second homology vanishes. Propagation through the later
native handles makes the terminal middle sublevel's second homology zero.
The actual finite attaching sequence therefore gives a surjective matrix,
and its canonical transported sphere classes span the common sublevel.
No homotopy-sphere equivalence or vanishing middle homology is required.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.HomologyVanishing

open SingularMayerVietoris

local notation "S₂" => Hemisphere.Sphere 2


section
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  [Subsingleton (SingularHomology M 2)]

variable (S : SurgeryWindows E f)

theorem middleMatrix_surjective
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count)
    (hthree : S.HasIndexThreeBlock r c) (hj : r + c + 1 < S.count)
    (hafter : ∀ i : Fin S.count, r + c < i.val → i.val + 1 < S.count →
      2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ∧
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ≠ 3) :
    Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  let : Subsingleton (SingularHomology
      {x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩)} 2) :=
    upper_homology_subsingleton_of_later_indices S hf hdim ⟨r + c, hc⟩ hj 2
      (by norm_num) (by norm_num) hafter
  exact (S.middlePresentation hf r htwo c hc hthree).matrix_surjective_of_subsingleton

end

section

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] [Subsingleton (SingularHomology M 2)] {f : M → ℝ}

theorem exists_surjective_middle_matrix_of_ordered_indices
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) :
    ∃ r c : ℕ, ∃ htwo : S.HasIndexTwoPrefix r,
      ∃ hc : r + c < S.count, ∃ hthree : S.HasIndexThreeBlock r c,
        r + c + 1 < S.count ∧
        (∀ i : Fin S.count, r + c < i.val →
          4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) ∧
        Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec ∧ r ≤ c := by
  obtain ⟨r, c, htwo, hc, hthree, hj, hafter⟩ :=
    exists_middle_index_blocks S hf hdim horder hzero hone
  have hsurj : Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec :=
    middleMatrix_surjective S hf hdim r c htwo hc hthree hj
      (fun i hi _ => by have hh := hafter i hi; exact ⟨by omega, by omega⟩)
  refine ⟨r, c, htwo, hc, hthree, hj, hafter, hsurj, ?_⟩
  have hrank := LinearMap.finrank_le_finrank_of_surjective
    (f := (S.middleMatrix hf r c htwo hc hthree).mulVecLin) hsurj
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] using hrank

end

section

open SingularMayerVietoris


variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] [Subsingleton (SingularHomology M 2)] {f : M → ℝ}

theorem native_middle_terminal_homology_subsingleton
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
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
  exact upper_homology_subsingleton_of_later_indices S.toSurgeryWindows hf hdim
    ⟨r + n, hrc⟩ hj 2 (by norm_num) (by norm_num)
      (fun i hi _ => by have hh := hafter i hi; exact ⟨by omega, by omega⟩)

theorem nativeMiddleCutSequence_terminal_homology_subsingleton
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
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
      S hf hdim horder hzero hone r 0 hr hn
    exact hH
  | succ n =>
    obtain ⟨h, hH⟩ := native_middle_terminal_homology_subsingleton
      T hf hdim horder hzero hone r (n + 1) hr hn
    exact hH

theorem middle_section_classes_span
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
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
    S T hf hdim horder hzero hone r n hr hn hrc
  apply top_unique
  intro v hv
  rw [← hker]
  exact Subsingleton.elim _ _

end

section
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  [Subsingleton (SingularHomology M 2)]

variable [Nonempty M]

theorem canonical_middle_matrix_surjective
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (r n : ℕ) (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hrc j) = 3)
    (hbefore : ∀ j, nativeMiddleBaseCut S r n hrc <
      T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hrc j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology
      {y : M // f y ≤ nativeMiddleBaseCut S r n hrc} 2)
    (γ : Fin n → C(S₂, {y : M // f y = nativeMiddleBaseCut S r n hrc}))
    (horbit : ∀ j x, ∃ t : ℝ, T.flow t
      (nativeIndexThreeAttachingSphere T (nativeMiddleBlockPoint S r n hrc j) (hp j) x).val =
        (γ j x).val) : Surjective (canonicalMiddleMatrix B γ).mulVec :=
  classCoordinateMatrix_surjective B _
    (middle_section_classes_span S T hf hdim horder hzero hone r n hr hn hrc hp hbefore γ horbit)

end

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.HomologyVanishing
