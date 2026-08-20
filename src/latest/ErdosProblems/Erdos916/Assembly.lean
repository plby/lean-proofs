/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreClassification
import ErdosProblems.Erdos916.BlockPathDecomposition

/-!
# Assembly of the circuit proof for Erdős Problem 916

This file isolates the short final assembly from the one deep structural input:
the Aboulker--Havet--Trotignon false-twin theorem.  The premise below will be
discharged by its source-level formalization; everything after it is the
already formalized extremal circuit and three-terminal block argument.
-/

namespace Erdos916

open SimpleGraph

universe u

/-- The minimum-degree specialization of the AHT false-twin theorem used by
the circuit proof. -/
def DegreeThreeFalseTwinPrinciple : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
    4 ≤ Fintype.card W →
      (∀ w : W, 3 ≤ H.degree w) →
        ¬HasWheelWitness H →
          ∃ u v : W, AreFalseTwins H u v ∧ H.degree u = 3

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Once the AHT false-twin theorem is available, every genuine `(2,3)`
circuit has the desired wheel. -/
theorem Is23Circuit.hasWheelWitness_of_falseTwinPrinciple
    (hcore : DegreeThreeFalseTwinPrinciple.{u})
    (hcircuit : Is23Circuit G) (hcard : 4 ≤ Fintype.card V) :
    HasWheelWitness G := by
  by_contra hnoWheel
  obtain ⟨u, v, htwin, hdeg⟩ :=
    hcore V G hcard (hcircuit.degree_three_le hcard) hnoWheel
  exact hnoWheel (hcircuit.hasWheelWitness_of_falseTwins htwin hdeg)

/-- A wheel in any spanning subgraph of an induced graph lifts to the ambient
graph. -/
theorem HasWheelWitness.lift_le_induce
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (H : SimpleGraph S) [DecidableRel H.Adj]
    (hHG : H ≤ G.induce (S : Set V)) (hH : HasWheelWitness H) :
    HasWheelWitness G := by
  let f : H →g G :=
    { toFun := fun x ↦ x.1
      map_rel' := by
        intro x y hxy
        exact hHG hxy }
  exact HasWheelWitness.mapHomOfInjective f Subtype.val_injective hH

/-- Lift the circuit conclusion through its inclusion in an induced ambient
subgraph. -/
theorem hasWheelWitness_of_circuit_subgraph
    (hcore : DegreeThreeFalseTwinPrinciple.{u})
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (H : SimpleGraph S) [DecidableRel H.Adj]
    (hS4 : 4 ≤ Fintype.card S)
    (hHG : H ≤ G.induce (S : Set V))
    (hcircuit : Is23Circuit H) : HasWheelWitness G := by
  have hH : HasWheelWitness H :=
    hcircuit.hasWheelWitness_of_falseTwinPrinciple hcore hS4
  exact HasWheelWitness.lift_le_induce G S H hHG hH

/-- The exact dense-graph statement, reduced to the source-level AHT theorem.
This is the final mathematical assembly: extract a minimum dense vertex set,
retain a spanning `(2,3)` circuit, find a wheel there, then lift it first to
the induced graph and then to the ambient graph. -/
theorem erdos_916_of_falseTwinPrinciple
    (hcore : DegreeThreeFalseTwinPrinciple.{u})
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V)
    (hedges : G.edgeFinset.card = 2 * Fintype.card V - 2) :
    HasWheelWitness G := by
  classical
  have hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2 := by
    rw [hedges]
    omega
  obtain ⟨S, H, hS4, hHG, hcircuit⟩ :=
    exists_is23Circuit_subgraph_with_card G hcard hdense
  letI : DecidableRel H.Adj := Classical.decRel _
  exact hasWheelWitness_of_circuit_subgraph
    hcore G S H hS4 hHG hcircuit

end Erdos916
