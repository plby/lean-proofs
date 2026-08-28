import Wikipedia.NoExoticSixSphere.GenericFamilyUnorderedCurve
import Wikipedia.NoExoticSixSphere.FamilyDoublePointOpenLocus
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# The diagonal orbit set is exactly the local boundary and is discrete

Every diagonal orbit has a genuine half-line chart, and throughout its source
coordinate zero is equivalent to membership in the diagonal orbit set. Chart
injectivity therefore isolates each such orbit inside that set. No compactness
or evenness of its cardinality is inferred from this local statement.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace NoExoticSixSphere.FamilyEmbedding

open GLOrthonormalization InvolutionQuotient OperatorRank

theorem exists_unordered_boundary_chart (f : ℝ → Vector 3 → Vector 6)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hreg : RegularThreeSix (fun p : ℝ × Vector 3 ↦ fderiv ℝ (f p.1) p.2))
    (q : UnorderedClosedDoublePoints f) (hq : q ∈ diagonalOrbits f) :
    ∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints f) HalfLine,
      q ∈ d.source ∧ d q = ⟨0, le_rfl⟩ ∧
      ∀ y ∈ d.source, (d y).val = 0 ↔ y ∈ diagonalOrbits f := by
  obtain ⟨r, hrdiag, rfl⟩ := hq
  rcases r with ⟨⟨t, x, y⟩, hcl⟩
  change x = y at hrdiag
  subst y
  have hsing : ¬ Injective (fderiv ℝ (f t) x) := by
    intro hi
    exact diagonal_not_mem_closure_doublePoints f hf t x hi hcl
  obtain ⟨hc, c, d, hcp, hcz, hdp, hdz, hsrc, htgt, happ, hiff, hsmooth⟩ :=
    exists_unordered_closed_curve_chart f hf hreg (t, x) hsing
  refine ⟨d, hdp, hdz, ?_⟩
  intro y hy
  rw [hsrc] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  exact (hiff s hs).trans (mem_diagonalOrbits_iff f s).symm

theorem isDiscrete_diagonalOrbits (f : ℝ → Vector 3 → Vector 6)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hreg : RegularThreeSix (fun p : ℝ × Vector 3 ↦ fderiv ℝ (f p.1) p.2)) :
    IsDiscrete (diagonalOrbits f) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro q hq
  obtain ⟨d, hqd, hdq, hiff⟩ := exists_unordered_boundary_chart f hf hreg q hq
  refine ⟨d.source, d.open_source, ?_⟩
  ext y
  constructor
  · rintro ⟨hyd, hy⟩
    have he : d y = d q := (Subtype.ext ((hiff y hyd).mpr hy)).trans hdq.symm
    exact mem_singleton_iff.mpr (d.injOn hyd hqd he)
  · rintro rfl
    exact ⟨hqd, hq⟩

end NoExoticSixSphere.FamilyEmbedding
