import Wikipedia.NoExoticSixSphere.GenericFamilyUnorderedLocalModels
import Wikipedia.NoExoticSixSphere.HalfLineInteriorChart

/-!
# A global topological half-line atlas on the actual unordered double curve

All interior charts are expressed in positive half-line coordinates. The
resulting chart family covers the original quotient topology, and every chart
identifies coordinate zero exactly with the actual diagonal orbit set. This is
a topological atlas; no smooth structure on the quotient is asserted here.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace NoExoticSixSphere.FamilyEmbedding

open GLOrthonormalization InvolutionQuotient OperatorRank

variable (f : ℝ → Vector 3 → Vector 6) (hf : ContDiff ℝ ∞ (uncurry f))
  (hreg : RegularThreeSix (fun p : ℝ × Vector 3 ↦ fderiv ℝ (f p.1) p.2))
  (hoff : ∀ q : ℝ × (Vector 3 × Vector 3), q.2.1 ≠ q.2.2 →
    DoublePointPerturbation.baseDifference f q = 0 →
    Surjective (fderiv ℝ (DoublePointPerturbation.baseDifference f) q))

include hf hreg hoff

theorem exists_unordered_halfLine_chart (q : UnorderedClosedDoublePoints f) :
    ∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints f) HalfLine,
      q ∈ d.source ∧ ∀ y ∈ d.source, (d y).val = 0 ↔ y ∈ diagonalOrbits f := by
  rcases unordered_local_models f hf hreg hoff q with ⟨c, hqc, hdis⟩ | ⟨d, hqd, hdq, hiff⟩
  · refine ⟨c.trans positiveHalfLine, ⟨hqc, mem_univ _⟩, ?_⟩
    intro y hy
    change Real.exp (c y) = 0 ↔ y ∈ diagonalOrbits f
    exact iff_of_false (Real.exp_ne_zero _) ((disjoint_left.mp hdis) hy.1)
  · exact ⟨d, hqd, hiff⟩

def unorderedChart (q : UnorderedClosedDoublePoints f) :
    OpenPartialHomeomorph (UnorderedClosedDoublePoints f) HalfLine :=
  (exists_unordered_halfLine_chart f hf hreg hoff q).choose

theorem unorderedChart_mem_source (q : UnorderedClosedDoublePoints f) :
    q ∈ (unorderedChart f hf hreg hoff q).source :=
  (exists_unordered_halfLine_chart f hf hreg hoff q).choose_spec.1

theorem unorderedChart_zero_iff (q y : UnorderedClosedDoublePoints f)
    (hy : y ∈ (unorderedChart f hf hreg hoff q).source) :
    (unorderedChart f hf hreg hoff q y).val = 0 ↔ y ∈ diagonalOrbits f :=
  (exists_unordered_halfLine_chart f hf hreg hoff q).choose_spec.2 y hy

@[instance_reducible]
def unorderedChartedSpace : ChartedSpace HalfLine (UnorderedClosedDoublePoints f) where
  atlas := range (unorderedChart f hf hreg hoff)
  chartAt := unorderedChart f hf hreg hoff
  mem_chart_source := unorderedChart_mem_source f hf hreg hoff
  chart_mem_atlas q := ⟨q, rfl⟩

theorem unordered_atlas_boundary
    (c : OpenPartialHomeomorph (UnorderedClosedDoublePoints f) HalfLine)
    (hc : c ∈ (unorderedChartedSpace f hf hreg hoff).atlas)
    (y : UnorderedClosedDoublePoints f) (hy : y ∈ c.source) :
    (c y).val = 0 ↔ y ∈ diagonalOrbits f := by
  obtain ⟨q, rfl⟩ := hc
  exact unorderedChart_zero_iff f hf hreg hoff q y hy

end NoExoticSixSphere.FamilyEmbedding
