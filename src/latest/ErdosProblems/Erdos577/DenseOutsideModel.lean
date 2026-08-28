import ErdosProblems.Erdos577.UnattachedModel
import ErdosProblems.Erdos577.StrictExchange

/-! Positive outcomes for the dense triangle join in Wang's Lemma 3.2. -/

namespace Erdos577.DenseOutside

open Finset Unattached

def terminalCount (m : ℕ) : ℕ :=
  ((List.range 4).map fun i ↦ (m.testBit i).toNat).sum

def triangleCount (m : ℕ) : ℕ :=
  ((List.range 12).map fun i ↦ (m.testBit (i + 4)).toNat).sum

/-- This improvement is strict in edge count, with no attachment condition. -/
def Positive (diagonal : Fin 4) (m : ℕ) : Prop :=
  LocalFactor (graph diagonal m) univ ∨
    StrictImprovement (graph diagonal m) univ (oldEdges diagonal)

lemma Positive.mono {diagonal : Fin 4} {small large : ℕ}
    (hs : Positive diagonal small) (h : large &&& small = small) : Positive diagonal large := by
  let f := SimpleGraph.Copy.ofLE (graph diagonal small) (graph diagonal large)
    (graph_mono diagonal h)
  rcases hs with hs | hs
  · left
    simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f
  · right
    simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f

end Erdos577.DenseOutside
