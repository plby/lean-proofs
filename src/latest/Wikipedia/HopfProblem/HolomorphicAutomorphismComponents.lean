import Wikipedia.HopfProblem.HolomorphicAutomorphismTopology
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Sequences

/-!
# Sequences and connected components in the genuine automorphism group

On a compact second-countable Hausdorff manifold the original compact-open
automorphism group is first countable. Thus failure of local surjectivity
can be tested by an actual sequence of automorphisms approaching one.
The final lemma records the purely topological component argument after
local surjectivity has been proved.
-/

noncomputable section

open Filter Set Topology TopologicalSpace
open scoped Uniformity

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M]

theorem firstCountable_of_compact [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] : FirstCountableTopology (HolomorphicAutomorphism I M) := by
  let : UniformSpace M := pseudoMetrizableSpaceUniformity M
  let : (𝓤 M).IsCountablyGenerated := pseudoMetrizableSpaceUniformity_countably_generated M
  exact (isEmbedding_toPair I M).firstCountableTopology

/-- Failure to contain a neighborhood produces actual full native
automorphisms outside the set converging to the identity. -/
theorem exists_sequence_outside [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] {s : Set (HolomorphicAutomorphism I M)}
    (hs : s ∉ 𝓝 (1 : HolomorphicAutomorphism I M)) :
    ∃ f : ℕ → HolomorphicAutomorphism I M,
      (∀ n, f n ∉ s) ∧ Tendsto f atTop (𝓝 1) := by
  let := firstCountable_of_compact I M
  apply (mem_closure_iff_seq_limit (s := sᶜ) (a := (1 : HolomorphicAutomorphism I M))).mp
  simpa only [closure_compl, mem_compl_iff, mem_interior_iff_mem_nhds] using hs

end Wikipedia.HopfProblem.HolomorphicAutomorphism

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismComponents

/-- A continuous homomorphism from a connected group whose image
contains a neighborhood of one has exactly the genuine identity
component as its image. Local surjectivity is used, not inferred from
an equality of infinitesimal dimensions. -/
theorem range_eq_connectedComponent_of_mem_nhds
    {G H : Type*} [Group G] [TopologicalSpace G] [ConnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →* H) (hf : Continuous f) (hlocal : (f.range : Set H) ∈ 𝓝 (1 : H)) :
    (f.range : Set H) = connectedComponent (1 : H) := by
  apply Subset.antisymm
  · exact (isPreconnected_range hf).subset_connectedComponent ⟨1, map_one f⟩
  · have hopen : IsOpen (f.range : Set H) := f.range.isOpen_of_mem_nhds hlocal
    have hclopen : IsClopen (f.range : Set H) :=
      ⟨f.range.isClosed_of_isOpen hopen, hopen⟩
    exact hclopen.connectedComponent_subset f.range.one_mem

end Wikipedia.HopfProblem.HolomorphicAutomorphismComponents
