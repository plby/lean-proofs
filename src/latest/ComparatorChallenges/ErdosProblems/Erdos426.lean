/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos426

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.deprecated false
set_option linter.flexible false
set_option linter.style.cases false
set_option linter.style.cdot false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

noncomputable section

open Finset Function SimpleGraph


namespace UniqueSubgraphs

open scoped Classical in
instance graphIsoSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r G₁ G₂ := Nonempty (G₁.Iso G₂)
  iseqv := {
    refl := fun _ => ⟨Iso.refl⟩
    symm := fun ⟨i⟩ => ⟨i.symm⟩
    trans := fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩
  }

open scoped Classical in
def paperDenom (n : ℕ) : ℝ :=
  (2 ^ n.choose 2 : ℝ) / (Nat.factorial n : ℝ)

open scoped Classical in
def IsUniqueSubgraph {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃! S : H.Subgraph, S.IsSpanning ∧ Nonempty (S.spanningCoe.Iso G)

open scoped Classical in
def uniqueSubgraphClasses {n : ℕ} (H : SimpleGraph (Fin n)) :
    Finset (Quotient (graphIsoSetoid n)) :=
  (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsUniqueSubgraph G H)).image
    (Quotient.mk (graphIsoSetoid n))

open scoped Classical in
def fH {n : ℕ} (H : SimpleGraph (Fin n)) : ℝ :=
  ((uniqueSubgraphClasses H).card : ℝ) / paperDenom n

open scoped Classical in
def fSeq (n : ℕ) : ℝ :=
  (Finset.univ : Finset (SimpleGraph (Fin n))).sup' ⟨⊥, mem_univ _⟩ fH
end UniqueSubgraphs

open Finset Function SimpleGraph

namespace UniqueSubgraphs

end UniqueSubgraphs
open Finset Function SimpleGraph

set_option maxHeartbeats 1600000

namespace UniqueSubgraphs

end UniqueSubgraphs
open Finset Function SimpleGraph

namespace UniqueSubgraphs

end UniqueSubgraphs

open Finset Function SimpleGraph

namespace UniqueSubgraphs

end UniqueSubgraphs
section EdgeOrderingSection

open Finset Function

namespace EdgeOrderingCount

variable {N : ℕ}

end EdgeOrderingCount
end EdgeOrderingSection

section PolyaWrightSection

open Finset Function SimpleGraph Filter

namespace PolyaWright

open UniqueSubgraphs

end PolyaWright
end PolyaWrightSection

section ChernoffBoundSection

open Finset Real Function
open scoped BigOperators

namespace ChernoffBound

end ChernoffBound
end ChernoffBoundSection

section AzumaHoeffdingSection

open Finset Real

namespace AzumaHoeffding

end AzumaHoeffding
end AzumaHoeffdingSection

open Finset Function SimpleGraph

namespace UniqueSubgraphs

end UniqueSubgraphs

end

end Erdos426


open Finset Function SimpleGraph
open Finset Function
open Finset Function SimpleGraph Filter
open Finset Real Function
open scoped BigOperators
open Finset Real

namespace Erdos426.UniqueSubgraphs

open scoped Classical in
theorem f_tendsto_zero : Filter.Tendsto fSeq Filter.atTop (nhds 0) := by
  sorry

end Erdos426.UniqueSubgraphs
