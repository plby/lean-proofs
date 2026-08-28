import ErdosProblems.Erdos577.CoreTransferRoutes
import ErdosProblems.Erdos577.DenseOutside
import ErdosProblems.Erdos577.TriangleAssembly

/-! Actual low-terminal routes transfer factor obstructions and row bounds
to every outside block. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {q : Quadrilateral G} {bs : Finset (Finset V)}

theorem Route.terminal_universal (r : Route c q bs) (i : Fin 4) (hi : i = 1 ∨ i = 3)
    {a : Finset V} (ha : a ∈ c.blocks) (hna : a ∉ bs)
    (hrow : 3 ≤ degreeIn G (q i) a) (u : V) (hu : u ∈ a) :
    QuadOn G (insert (q i) (a.erase u)) := by
  obtain ⟨d, hdf, hdt, _, hkeep⟩ := r.terminals i hi
  have hh := hdf.terminal_universal_replace (hkeep a ha hna) (by rw [hdt]; exact hrow) hu
  rwa [hdt] at hh

theorem Route.triangle_column_le_one (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) {a : Finset V} (ha : a ∈ c.blocks) (hna : a ∉ bs)
    (hrow : 3 ≤ degreeIn G (q i) a) (u : V) (hu : u ∈ a) :
    degreeIn G u c.triangle ≤ 1 := by
  obtain ⟨d, hdf, hdt, htri, hkeep⟩ := r.terminals i hi
  have ha' := hkeep a ha hna
  have hrep := hdf.terminal_universal_replace ha' (by rw [hdt]; exact hrow) hu
  have hh := (d.replaceBlock a ha' (d.swapTerminal ha' hu hrep)).terminal_degree_le_one hcard hn
  change degreeIn G u d.triangle ≤ 1 at hh
  rwa [htri] at hh

theorem Route.triangle_contacts_le_four (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) {a : Finset V} (ha : a ∈ c.blocks) (hna : a ∉ bs)
    (hrow : 3 ≤ degreeIn G (q i) a) : contacts G c.triangle a ≤ 4 := by
  rw [contacts_comm]
  calc
    _ ≤ ∑ _ ∈ a, 1 := sum_le_sum fun u hu ↦ r.triangle_column_le_one hcard hn i hi ha hna hrow u hu
    _ = 4 := by simp only [sum_const, smul_eq_mul, mul_one, (c.property.blocks_quad a ha).card]

theorem Route.low_degree_le_one (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) {a : Finset V} (ha : a ∈ c.blocks) (hna : a ∉ bs)
    (htri : 9 ≤ contacts G c.triangle a) : degreeIn G (q i) a ≤ 1 := by
  obtain ⟨d, hdf, hdt, ht, hkeep⟩ := r.terminals i hi
  have hh := hdf.terminal_degree_le_one_of_dense hcard hn (hkeep a ha hna)
    (by rw [ht]; exact htri)
  rwa [hdt] at hh

theorem Route.no_local_factor (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) {a : Finset V} (ha : a ∈ c.blocks) (hna : a ∉ bs) :
    ¬LocalFactor G (insert (q i) (c.triangle ∪ a)) := by
  intro hf
  obtain ⟨d, _, hdt, ht, hkeep⟩ := r.terminals i hi
  apply d.no_local_factor hcard hn (hkeep a ha hna)
  change LocalFactor G (insert d.terminal d.triangle ∪ a)
  simpa only [hdt, ht, insert_union] using hf

theorem Route.no_selected_factor (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) (as : Finset (Finset V))
    (has : as ⊆ c.blocks) (hdis : Disjoint as bs) :
    ¬Nonempty (BlockPartition G (insert (q i) (c.triangle ∪ as.biUnion id))) := by
  rintro ⟨hf⟩
  obtain ⟨d, _, hdt, ht, hkeep⟩ := r.terminals i hi
  have has' : as ⊆ d.blocks := by
    intro a ha
    exact hkeep a (has ha) (fun hb ↦ disjoint_left.mp hdis ha hb)
  have he : insert (q i) (c.triangle ∪ as.biUnion id) = d.remainder ∪ as.biUnion id := by
    change _ = insert d.terminal d.triangle ∪ _
    rw [hdt, ht, insert_union]
  exact hn (d.complementPartition.hasPacking_of_selected_factor hcard as has' (he ▸ hf))

end Erdos577.CoreTransfer
