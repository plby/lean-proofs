import Wikipedia.SchoenfliesTheorem.Graph.Redrawing
import Wikipedia.SchoenfliesTheorem.FaceCyclesLand
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Metric Set Schoenflies unitInterval
open scoped Graph

namespace Graph


variable {β : Type*} {G : Graph Plane β}

/-- A concrete two-colouring of a multigraph. -/
def IsBicoloring (G : Graph Plane β) (c : Plane → Bool) : Prop :=
  ∀ ⦃e u v⦄, G.IsLink e u v → c u ≠ c v

theorem exists_isBicoloring_of_toSimpleGraph_isBipartite [G.Loopless]
    (hbi : G.toSimpleGraph.IsBipartite) : ∃ c : Plane → Bool, G.IsBicoloring c := by
  classical
  obtain ⟨s, t, hst⟩ := hbi.exists_isBipartiteWith
  let c : Plane → Bool := fun x =>
    if hx : x ∈ V(G) then decide (⟨x, hx⟩ ∈ s) else false
  refine ⟨c, fun {e u v} huv => ?_⟩
  have hadj : G.toSimpleGraph.Adj ⟨u, huv.left_mem⟩ ⟨v, huv.right_mem⟩ :=
    (G.toSimpleGraph_adj_iff _ _).2 ⟨e, huv⟩
  rcases hst.mem_of_adj hadj with hst' | hts'
  · obtain ⟨hu, hv⟩ := hst'
    have hv' : (⟨v, huv.right_mem⟩ : V(G)) ∉ s :=
      fun hvS => Set.disjoint_left.1 hst.disjoint hvS hv
    simp [c, huv.left_mem, huv.right_mem, hu, hv']
  · obtain ⟨hu, hv⟩ := hts'
    have hu' : (⟨u, huv.left_mem⟩ : V(G)) ∉ s :=
      fun huS => Set.disjoint_left.1 hst.disjoint huS hu
    simp [c, huv.left_mem, huv.right_mem, hu', hv]

theorem IsWalk.color_eq_iff_even {c : Plane → Bool}
    (hc : G.IsBicoloring c) {u v : Plane} {W : List β}
    (hW : G.IsWalk u W v) : c u = c v ↔ Even W.length := by
  induction hW with
  | nil => simp
  | @cons u w v e W he hW ih =>
      have hne : c u ≠ c w := hc he
      cases hu : c u <;> cases hw : c w <;> cases hv : c v <;>
        simp_all [Nat.even_add_one]

theorem IsCycleThrough.even_length {c : Plane → Bool}
    (hc : G.IsBicoloring c) {e : β} {u v : Plane} {D : List β}
    (hcyc : G.IsCycleThrough e u v D) : Even (e :: D).length := by
  have huv : c u ≠ c v := hc hcyc.isLink
  have hodd : ¬ Even D.length := by
    intro hEven
    exact huv ((hcyc.isPath.isWalk.color_eq_iff_even hc).2 hEven)
  simpa [Nat.even_add_one] using hodd

theorem IsCycleThrough.three_le_length [G.Simple]
    {e : β} {u v : Plane} {D : List β}
    (hcyc : G.IsCycleThrough e u v D) : 3 ≤ (e :: D).length := by
  have huv : u ≠ v := hcyc.isLink.ne
  have hDne : D ≠ [] := hcyc.isPath.ne_nil huv
  cases D with
  | nil => exact (hDne rfl).elim
  | cons f D =>
      cases D with
      | nil =>
          have hlinkf : G.IsLink f u v := by
            have hw := hcyc.isPath.isWalk
            cases hw with
            | cons hl hrest =>
                cases hrest with
                | nil => exact hl
          exact (hcyc.notMem (by simpa using hcyc.isLink.eq hlinkf)).elim
      | cons g D => simp

theorem IsCycleThrough.four_le_length [G.Simple] {c : Plane → Bool}
    (hc : G.IsBicoloring c) {e : β} {u v : Plane} {D : List β}
    (hcyc : G.IsCycleThrough e u v D) : 4 ≤ (e :: D).length := by
  have h3 := hcyc.three_le_length
  have hev := hcyc.even_length hc
  rcases hev with ⟨k, hk⟩
  simp only [List.length_cons] at h3 hk ⊢
  omega

end Graph
