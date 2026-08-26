import ErdosProblems.Erdos556.CubeWeights
import ErdosProblems.Erdos556.FiberCardSums
import ErdosProblems.Erdos556.MappedDensity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The graph of all profile pairs that can support a retained bipartite edge. -/

namespace Erdos556

open SimpleGraph Finset

def profilePotentialGraph {V : Type*} (label : V → CubeProfile) : SimpleGraph V where
  Adj u v := Disjoint (profileVertices (label u)) (profileVertices (label v))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro v h
    have he : profileVertices (label v) = ∅ := by
      simpa only [disjoint_self, Finset.bot_eq_empty] using h
    have hp : 0 < (profileVertices (label v)).card := by rw [profileVertices_card]; positivity
    rw [he, card_empty] at hp
    omega⟩

def cubeDisjointMass (w : CubeProfile → ℝ) : ℝ :=
  ∑ p, ∑ q, if Disjoint (profileVertices p) (profileVertices q) then w p * w q else 0

theorem twice_edge_count_eq_ordered_pair_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * (Nat.card G.edgeSet : ℝ) = ∑ u, ∑ v, if G.Adj u v then (1 : ℝ) else 0 := by
  classical
  have hdegree (u : V) : G.degree u = ∑ v, if G.Adj u v then (1 : ℕ) else 0 := by
    rw [sum_boole, ← card_neighborFinset_eq_degree]
    congr 1
    ext v
    simp
  have h := G.sum_degrees_eq_twice_card_edges
  simp only [hdegree, edgeFinset_card_eq_natCard_edgeSet] at h
  exact_mod_cast h.symm

theorem profilePotentialGraph_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (label : V → CubeProfile) :
    2 * (Nat.card (profilePotentialGraph label).edgeSet : ℝ) =
      cubeDisjointMass (fun p => ((univ.filter (fun v => label v = p)).card : ℝ)) := by
  classical
  rw [twice_edge_count_eq_ordered_pair_sum]
  have hadj : (∑ u, ∑ v, if (profilePotentialGraph label).Adj u v then (1 : ℝ) else 0) =
      ∑ u, ∑ v, if Disjoint (profileVertices (label u)) (profileVertices (label v)) then (1 : ℝ) else 0 := by
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    by_cases h : Disjoint (profileVertices (label u)) (profileVertices (label v)) <;>
      simp [profilePotentialGraph, h]
  rw [hadj]
  rw [sum_double_by_fiber_card label (fun p q =>
    if Disjoint (profileVertices p) (profileVertices q) then (1 : ℝ) else 0)]
  unfold cubeDisjointMass
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp

theorem cubeEnergy_disjoint_identity (w : CubeProfile → ℝ) :
    cubeEnergy w = (∑ p, w p) ^ 2 - cubeDisjointMass w -
      ∑ p, (profileDimension p : ℝ) * w p := by
  have h : (∑ p, ∑ q, cubeOverlap p q * w p * w q) + cubeDisjointMass w = (∑ p, w p) ^ 2 := by
    calc
      _ = ∑ p, ∑ q, (cubeOverlap p q * w p * w q +
          if Disjoint (profileVertices p) (profileVertices q) then w p * w q else 0) := by
        simp only [cubeDisjointMass, sum_add_distrib]
      _ = ∑ p, ∑ q, w p * w q := by
        apply sum_congr rfl
        intro p _
        apply sum_congr rfl
        intro q _
        unfold cubeOverlap
        split_ifs <;> simp
      _ = _ := by
        simp only [pow_two, sum_mul, mul_sum]
        exact sum_comm
  unfold cubeEnergy
  linarith

#print axioms profilePotentialGraph_edge_count
#print axioms cubeEnergy_disjoint_identity

end Erdos556
