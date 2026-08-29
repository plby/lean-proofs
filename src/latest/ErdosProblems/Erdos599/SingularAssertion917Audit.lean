/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProgressiveExchangeAmbient

/-!
# A source-faithful audit of Assertion 9.17's successor step

This packages the finite crossing example with the exact local data present
when Assertion 9.17 invokes the half-way clause: the ambient web is normalized
and unhindered, the current row is a qualified full-source half-way linkage,
the fixed family is a linkage on the complementary source, and the next
competitor set genuinely contains `b`.  Nevertheless no target-row stage can
both forward-extend the current row and link that next source.

The obstruction is the nontrivial component `d-x-t1`, whose initial vertex
`d` belongs to the recorded stop-over.  Consequently the source half-way
certificate does not imply the terminal-clean hypothesis needed by the
checked quotient-continuation theorem.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularAssertion917Audit

open SingularExtension
open SingularSafeBatchCounterexample
open SingularSafeBatchCounterexample.Vertex
open SingularProgressiveExchangeCounterexample

/-- The fixed linkage has exactly the complementary source required by the
extension-clause decomposition with designated set `{d}`. -/
theorem source_sdiff_designated :
    web.source \ ({d} : Set Vertex) = ({b} : Set Vertex) := by
  ext v
  cases v <;> simp [web]

theorem fixed_isComplementLinkage :
    IsLinkageBetween web (web.source \ ({d} : Set Vertex)) web.target fixed := by
  rw [source_sdiff_designated]
  exact fixed_isLinkageBetween

/-- The displayed row satisfies the actual qualified half-way predicate,
including full ambient-source coverage, target linkage of the designated
source, and an altitude bound. -/
theorem paths_qualified :
    IsHalfwayLinkageOfAltitude web ({d} : Set Vertex)
      (Cardinal.mk (↑(web.sourceᶜ))) paths := by
  refine ⟨⟨boundary, exactHalfwayStopover.toHalfwayStopover⟩,
    paths_linksToTarget_d, ?_⟩
  exact (altitude_le_height_of_stopover
    exactHalfwayStopover.toHalfwayStopover).trans
      (height_le_source_compl web boundary)

/-- The row is not terminal-clean at its recorded stop-over.  Its completed
`d-x-t1` component starts at the stop-over vertex `d` but does not terminate
there. -/
theorem not_terminalCleanAt_boundary :
    ¬ SingularContinuation.TerminalCleanAt web paths boundary := by
  intro hclean
  have hterm := hclean (.inl dxt1) (by simp [paths]) d
    (by
      change d ∈ dxt1.support
      rw [support_dxt1]
      simp)
    (by simp [boundary])
  change some t1 = some d at hterm
  exact Vertex.noConfusion (Option.some.inj hterm)

/-- Boundary-starting components need not be trivial under the source
half-way predicate. -/
theorem exists_nontrivial_boundaryStarting_component :
    ∃ f : DirectedPath.FinitePath web.graph,
      (.inl f : web.DPath) ∈ paths ∧ f.start ∈ boundary ∧
        f.finish ≠ f.start := by
  refine ⟨dxt1, by simp [paths], by simp [boundary], ?_⟩
  exact Vertex.noConfusion

/-- The general source-arrow operation does not repair the obstruction.
It always preserves every old prefix, so warpness of the arrow output is
incompatible with target-linking `b` in this example. -/
theorem arrow_cannot_link_b (U : Set web.DPath) (hU : web.IsWarp U) :
    ¬ LinksToTarget web (web.arrow paths U) ({b} : Set Vertex) := by
  intro hlinks
  exact no_forward_warp_links_b ⟨web.arrow paths U,
    web.isWarp_arrow paths_isWarp hU,
    web.forwardExtension_arrow paths U, hlinks⟩

/-- Exact local refutation of the unconditional successor inference made in
the one-line proof of Assertion 9.17. -/
theorem sourceFaithfulAssertion917_obstruction :
    web.IsNormalized ∧
      web.IsUnhindered ∧
      IsHalfwayLinkageOfAltitude web ({d} : Set Vertex)
        (Cardinal.mk (↑(web.sourceᶜ))) paths ∧
      IsLinkageBetween web (web.source \ ({d} : Set Vertex))
        web.target fixed ∧
      b ∈ nextTargetSources web fixed rowUnit () ∧
      ¬ ∃ T : TargetRowStage web Unit,
        T.sources = nextTargetSources web fixed rowUnit ∧
          ∀ i, web.ForwardExtension (rowUnit.paths i) (T.paths i) := by
  refine ⟨web_normalized,
    SingularProgressiveExchangeAmbient.web_unhindered,
    paths_qualified, fixed_isComplementLinkage,
    b_mem_nextTargetSources_unit, no_rowUnit_successor⟩

#print axioms sourceFaithfulAssertion917_obstruction

end SingularAssertion917Audit
end CardinalInduction
end Erdos599
