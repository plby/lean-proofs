/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CircuitTwins
import ErdosProblems.Erdos916.ThreePathCut

/-!
# Closing the false-twin route

A cubic false-twin pair in a `(2,3)` circuit forces a wheel.  After deleting
the twins, the remaining graph is connected, `(2,3)`-sparse, and has
`e + 4 = 2v`.  A path through the three common neighbours closes to a wheel;
if no such path exists, the three-terminal density theorem gives the
contradictory bound `e + 5 ≤ 2v`.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A degree-three false-twin pair in a `(2,3)` circuit forces the desired
wheel witness. -/
theorem Is23Circuit.hasWheelWitness_of_falseTwins_via_density
    (hcircuit : Is23Circuit G) {u v : V}
    (htwin : AreFalseTwins G u v) (hdeg : G.degree u = 3) :
    HasWheelWitness G := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hNu, -⟩ :=
    exists_common_neighbors_three_of_falseTwins htwin hdeg
  have ha : G.Adj u a := by
    rw [← SimpleGraph.mem_neighborFinset, hNu]
    simp
  have hb : G.Adj u b := by
    rw [← SimpleGraph.mem_neighborFinset, hNu]
    simp
  have hc : G.Adj u c := by
    rw [← SimpleGraph.mem_neighborFinset, hNu]
    simp
  let aD : {w : V // w ∈ (({u, v} : Set V)ᶜ)} :=
    ⟨a, common_neighbor_mem_deletePair htwin ha⟩
  let bD : {w : V // w ∈ (({u, v} : Set V)ᶜ)} :=
    ⟨b, common_neighbor_mem_deletePair htwin hb⟩
  let cD : {w : V // w ∈ (({u, v} : Set V)ᶜ)} :=
    ⟨c, common_neighbor_mem_deletePair htwin hc⟩
  have habD : aD ≠ bD := fun h => hab (congrArg Subtype.val h)
  have hacD : aD ≠ cD := fun h => hac (congrArg Subtype.val h)
  have hbcD : bD ≠ cD := fun h => hbc (congrArg Subtype.val h)
  by_cases hpath : HasThreeTerminalPath (deletePair G u v) aD bD cD
  · exact hasWheelWitness_of_falseTwins_of_deletePair_terminalPath
      htwin hab hac hbc ha hb hc aD.2 bD.2 cD.2 hpath
  · have hbound := edge_card_add_five_le_of_no_threeTerminalPath
      (deletePair G u v)
      (hcircuit.deletePair_connected htwin hdeg)
      (hcircuit.is23Sparse_deletePair u v)
      habD hacD hbcD hpath
    have hcount := hcircuit.deletePair_has24Count htwin hdeg
    omega

end Erdos916
