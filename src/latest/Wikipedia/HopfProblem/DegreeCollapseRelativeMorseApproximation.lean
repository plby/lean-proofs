import Wikipedia.HopfProblem.DegreeCollapseRelativeMorsePatch
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Relative uniform Morse approximation on the actual compact manifold

Keep the function exactly fixed outside a prescribed open set. A compact
region already Morse covers the complement of that open set in its
interior. Finite chart induction across the remaining compact set makes
the function globally Morse, with any prescribed positive uniform error.
No boundary or zero-fiber atlas is changed by this construction.
-/

noncomputable section

open Set Function Filter Metric MeasureTheory MeasureTheory.Measure Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

section Haar

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

include μ in
theorem exists_relative_morse_close_of_haar {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (K O : Set M)
    (hK : IsCompact K) (hfK : IsMorseOn E f K) (hO : IsOpen O)
    (hcover : (interior K)ᶜ ⊆ O) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (∀ x : M, |g x - f x| < ε) ∧ EqOn g f Oᶜ := by
  classical
  let D := ↥((interior K)ᶜ)
  have hpatch (p : D) := exists_compact_plateau_supported (E := E) O hO p.val (hcover p.property)
  choose φ U L hφO hU hUs hφ hL hn hLU using hpatch
  have hbadCover : (interior K)ᶜ ⊆ ⋃ p : D, interior (L p) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := isOpen_interior.isClosed_compl.isCompact.elim_finite_subcover
    (fun p : D ↦ interior (L p)) (fun _ ↦ isOpen_interior) hbadCover
  have hfinite : ∀ (s : Finset D) (η : ℝ), 0 < η →
      ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        IsMorseOn E g (K ∪ ⋃ p ∈ s, L p) ∧
        (∀ x : M, |g x - f x| < η) ∧ EqOn g f Oᶜ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro η hη
      refine ⟨f, hf, ?_, ?_, fun _ _ ↦ rfl⟩
      · simpa using hfK
      · intro x
        simpa using hη
    | @insert p s hp ih =>
      intro η hη
      obtain ⟨g, hg, hm, hclose, hfixed⟩ := ih (η / 2) (half_pos hη)
      have hKs : IsCompact (K ∪ ⋃ q ∈ s, L q) :=
        hK.union (s.isCompact_biUnion (fun q _ ↦ hL q))
      obtain ⟨g', hg', hm', hclose', hfixed'⟩ := exists_morse_extension_close μ (φ p)
        (hU p) (hUs p) (hφ p) (hL p) (hLU p) hg hKs hm (η / 2) (half_pos hη)
      refine ⟨g', hg', ?_, ?_, ?_⟩
      · simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left, union_left_comm] using hm'
      · intro x
        calc
          |g' x - f x| = |(g' x - g x) + (g x - f x)| := by congr 1; ring
          _ ≤ |g' x - g x| + |g x - f x| := by
            simpa only [Real.norm_eq_abs] using norm_add_le (g' x - g x) (g x - f x)
          _ < η / 2 + η / 2 := add_lt_add (hclose' x) (hclose x)
          _ = η := by ring
      · intro x hx
        have hφx : φ p x = 0 := by
          by_contra hn
          exact hx (hφO p (subset_closure hn))
        exact (hfixed' x hφx).trans (hfixed hx)
  obtain ⟨g, hg, hm, hclose, hfixed⟩ := hfinite s ε hε
  refine ⟨g, hg, ?_, hclose, hfixed⟩
  intro x
  by_cases hx : x ∈ K
  · exact hm x (Or.inl hx)
  · have hbad : x ∈ (interior K)ᶜ := fun h ↦ hx (interior_subset h)
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hbad)
    exact hm x (Or.inr (mem_iUnion₂.mpr ⟨p, hp, interior_subset hxp⟩))

end Haar

theorem exists_relative_morse_close {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (K O : Set M)
    (hK : IsCompact K) (hfK : IsMorseOn E f K) (hO : IsOpen O)
    (hcover : (interior K)ᶜ ⊆ O) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (∀ x : M, |g x - f x| < ε) ∧ EqOn g f Oᶜ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  exact exists_relative_morse_close_of_haar Measure.addHaar hf K O hK hfK hO hcover ε hε

end Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse
