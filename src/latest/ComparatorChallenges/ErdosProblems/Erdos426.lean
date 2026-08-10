import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

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

attribute [local instance] Classical.propDecidable

namespace UniqueSubgraphs

instance graphIsoSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r G₁ G₂ := Nonempty (G₁.Iso G₂)
  iseqv := {
    refl := fun _ => ⟨Iso.refl⟩
    symm := fun ⟨i⟩ => ⟨i.symm⟩
    trans := fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩
  }

def paperDenom (n : ℕ) : ℝ :=
  (2 ^ n.choose 2 : ℝ) / (Nat.factorial n : ℝ)

def IsUniqueSubgraph {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃! S : H.Subgraph, S.IsSpanning ∧ Nonempty (S.spanningCoe.Iso G)

def uniqueSubgraphClasses {n : ℕ} (H : SimpleGraph (Fin n)) :
    Finset (Quotient (graphIsoSetoid n)) :=
  (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsUniqueSubgraph G H)).image
    (Quotient.mk (graphIsoSetoid n))

def fH {n : ℕ} (H : SimpleGraph (Fin n)) : ℝ :=
  ((uniqueSubgraphClasses H).card : ℝ) / paperDenom n

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

attribute [local instance] Classical.propDecidable

theorem Erdos426.UniqueSubgraphs.f_tendsto_zero :
    @Filter.Tendsto.{0, 0} Nat Real Erdos426.UniqueSubgraphs.fSeq
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  := by
  sorry
