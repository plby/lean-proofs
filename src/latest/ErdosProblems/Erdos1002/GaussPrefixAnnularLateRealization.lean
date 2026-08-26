import ErdosProblems.Erdos1002.GaussPrefixAnnularMidpointGap
import ErdosProblems.Erdos1002.GaussPrefixLateAggregateCancellation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical labeled realizations of upper retained annular tuples

The late argument is carried out with the labeled mixed-prefix character,
whereas the canonical marked measure is indexed by chronological natural
tuples.  This file chooses one of the already-proved unique canonical
realizations and records all equations needed to move between the two
coordinate systems.  It also instantiates the midpoint-gap package for the
chosen realization and proves the exact prefix/future indicator split.
-/

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularLateRealizationPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- A chronological tag together with one upper retained tuple for that
tag. -/
def AnnularUpperRetainedTaggedTuple
    (rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :=
  Σ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    ↥(annularCanonicalLaterUpperMidpointTupleFamily
      rho N k hr e (mode e) (hmode e))

instance annularUpperRetainedTaggedTupleFintype
    (rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Fintype (AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) := by
  unfold AnnularUpperRetainedTaggedTuple
  infer_instance

instance annularUpperRetainedTaggedTupleDecidableEq
    (rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    DecidableEq
      (AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :=
  Classical.decEq _

/-- The chronological tuple underlying a tagged retained element. -/
def annularUpperRetainedTimes
    {rho : ℝ} {N : ℕ} {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    Fin (MixedOccurrenceCount k) → ℕ :=
  p.2.1

/-- Every upper retained tuple is still a member of its full canonical
annular family. -/
theorem annularUpperRetainedTimes_mem_canonical
    {rho : ℝ} {N : ℕ} {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    annularUpperRetainedTimes p ∈
      canonicalAnnularGridTupleFamily N k p.1 := by
  have hupper :=
    (mem_laterUpperMidpointNatTupleFamily_iff.mp p.2.2).1
  have hlate := (mem_lateFirstNatTupleFamily_iff.mp hupper).1
  exact (mem_separatedNatTupleFamily_iff.mp hlate).1

/-- Existence of a labeled globally injective tuple realizing the tagged
chronological tuple. -/
theorem exists_annularUpperRetainedRealization
    {rho : ℝ} {N : ℕ} {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    ∃ F : GloballyInjectiveMixedDepthTuple N k,
      canonicalMixedOccurrenceOrder N k F = p.1 ∧
        fixedOrderMixedTimes N k p.1 F =
          annularUpperRetainedTimes p := by
  rcases mem_canonicalMixedOrderParityBoxTimes_iff.mp
      (annularUpperRetainedTimes_mem_canonical p) with
    ⟨F, horder, _hboxes, htimes⟩
  exact ⟨F, horder, htimes⟩

/-- Canonical chosen labeled realization. -/
def annularUpperRetainedRealization
    {rho : ℝ} {N : ℕ} {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    GloballyInjectiveMixedDepthTuple N k :=
  Classical.choose (exists_annularUpperRetainedRealization p)

theorem annularUpperRetainedRealization_order
    {rho : ℝ} {N : ℕ} {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    canonicalMixedOccurrenceOrder N k
        (annularUpperRetainedRealization p) = p.1 :=
  (Classical.choose_spec
    (exists_annularUpperRetainedRealization p)).1

theorem annularUpperRetainedRealization_times
    {rho : ℝ} {N : ℕ} {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    fixedOrderMixedTimes N k p.1
        (annularUpperRetainedRealization p) =
      annularUpperRetainedTimes p :=
  (Classical.choose_spec
    (exists_annularUpperRetainedRealization p)).2

/-- Midpoint split belonging to one tagged upper retained tuple. -/
def annularUpperRetainedSplitDepth
    {rho : ℝ} {N : ℕ} {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) : ℕ :=
  midpointPrefixSplitDepth
    (annularLastNonzeroIndex (mode p.1) (hmode p.1))
    (annularDepthAmbientSize N)
    (annularUpperRetainedTimes p)

/-- Common half-band gap for the tagged upper family. -/
def annularUpperRetainedGap (rho : ℝ) (N : ℕ) : ℕ :=
  midpointPrefixFutureGap (annularMidpointBandWidth rho N)

/-- Instantiated midpoint-gap package, with the ambient depth bound proved
from canonical annular membership rather than assumed by the caller. -/
theorem annularUpperRetainedRealization_gap_package
    {rho : ℝ} {N : ℕ} {grid : ℕ}
    (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    let m := annularUpperRetainedSplitDepth p
    let gap := annularUpperRetainedGap rho N
    (∀ j, annularUpperRetainedTimes p j ≤ m →
      annularUpperRetainedTimes p j + gap ≤ m) ∧
    (∀ j, m < annularUpperRetainedTimes p j →
      m + gap ≤ annularUpperRetainedTimes p j) ∧
    ∀ j, m < annularUpperRetainedTimes p j →
      mode p.1 j = 0 := by
  have hbound :
      ∀ j, annularUpperRetainedTimes p j <
        annularDepthAmbientSize N := by
    intro j
    exact canonicalAnnularGridTupleFamily_lt_ambient
      hgrid k htime hN p.1 (annularUpperRetainedTimes p)
      (annularUpperRetainedTimes_mem_canonical p) j
  have hp :=
    annularUpperRetained_midpointGap_package
      k hr p.1 (mode p.1) (hmode p.1) p.2.2 hW hbound
  simpa only [annularUpperRetainedSplitDepth,
    annularUpperRetainedGap, annularUpperRetainedTimes] using!
    ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

/-- Every upper retained tuple has at least one genuine future
coordinate after its midpoint split. -/
theorem annularUpperRetained_exists_after_split
    {rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hW : 0 < annularMidpointBandWidth rho N) :
    ∃ j : Fin (MixedOccurrenceCount k),
      annularUpperRetainedSplitDepth p <
        annularUpperRetainedTimes p j := by
  have hmem :=
    mem_laterUpperMidpointNatTupleFamily_iff.mp p.2.2
  obtain ⟨j, _hsj, hjUpper⟩ := hmem.2.2
  refine ⟨j, ?_⟩
  exact midpointPrefixSplitDepth_lt_of_upper_witness hW hjUpper

/-- Fourier modes of the chosen labeled realization vanish after the
midpoint split. -/
theorem annularUpperRetained_labeledMode_zero_after_split
    {rho : ℝ} {N : ℕ} {grid : ℕ}
    (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (z : GaussPrefixMixedOccurrence k)
    (hz :
      annularUpperRetainedSplitDepth p <
        (annularUpperRetainedRealization p).1 z.1 z.2) :
    unflattenedAnnularFourierMode p.1 (mode p.1) z.1 z.2 = 0 := by
  let j : Fin (MixedOccurrenceCount k) := p.1.symm z
  have htimeEq :
      annularUpperRetainedTimes p j =
        ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) := by
    have htimes :=
      congrFun (annularUpperRetainedRealization_times p) j
    change
      ((annularUpperRetainedRealization p).1
          (p.1 j).1 (p.1 j).2 : ℕ) =
        annularUpperRetainedTimes p j at htimes
    have hej : p.1 j = z := by
      exact p.1.apply_symm_apply z
    rw [hej] at htimes
    exact htimes.symm
  have hp :=
    (annularUpperRetainedRealization_gap_package
      hgrid htime p hN hW).2.2 j
  have hj : mode p.1 j = 0 := hp (by simpa only [htimeEq] using! hz)
  simpa only [unflattenedAnnularFourierMode, j,
    p.1.symm_apply_apply] using! hj

/-- Exact prefix/future indicator factorization for the chosen realization
at its deterministic midpoint split. -/
theorem annularUpperRetained_character_eq_prefix_mul_futureIndicator
    {rho : ℝ} {N : ℕ} {grid : ℕ}
    (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ))
    (x : ℝ) :
    gaussPrefixMarkedMixedTupleCharacter N B k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularUpperRetainedRealization p).1 x =
      gaussPrefixMarkedMixedPrefixCharacter N B k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularUpperRetainedRealization p).1
          (annularUpperRetainedSplitDepth p) x *
        (gaussPrefixMarkedMixedFutureEvent N B k
          (annularUpperRetainedRealization p).1
          (annularUpperRetainedSplitDepth p)).indicator
            (fun _ ↦ (1 : ℂ)) x := by
  apply gaussPrefixMarkedMixedTupleCharacter_eq_prefix_mul_futureIndicator
  intro z hz
  exact annularUpperRetained_labeledMode_zero_after_split
    hgrid htime p hN hW z hz

end

end Erdos1002
