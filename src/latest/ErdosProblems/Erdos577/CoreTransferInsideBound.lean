import ErdosProblems.Erdos577.CoreTransferHeavyExact
import ErdosProblems.Erdos577.CoreTransferFinalFactor

/-! The two outside-block averages and their factor prove the seven-vertex core's inside bound. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem inside_bound {c : TriangleChain G} (hc : c.Strong) {q : Quadrilateral G}
    {bs : Finset (Finset V)} (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hnb : b ∉ bs)
    (hcore : LocalFactor G (insert (q 2) (c.triangle ∪ b)))
    {z : V} (hz : z ∈ c.triangle ∪ b) (hzl : G.Adj z (q 1))
    (hzrep : z ∈ b → ∃ x ∈ c.triangle, ∃ y ∈ c.triangle,
      x ≠ y ∧ G.Adj z x ∧ QuadOn G (insert y (b.erase z))) :
    12 * ((insert b bs).card + 1) ≤
      contacts G (rows c q) (c.remainder ∪ (insert b bs).biUnion id) + 1 := by
  by_contra! hsmall
  have hinside : contacts G (rows c q) (c.remainder ∪ (insert b bs).biUnion id) + 2 ≤
      12 * ((insert b bs).card + 1) := by omega
  have hsel : insert b bs ⊆ c.blocks := insert_subset_iff.mpr ⟨hb, r.blocks_subset⟩
  have hbq : b ≠ q.support := fun he ↦ hnb (he ▸ r.contains_cycle)
  have hdata (a : Finset V) (ha : a ∈ c.blocks) (hna : a ∉ insert b bs)
      (hh : 13 ≤ contacts G (rows c q) a) :
      contacts G (rows c q) a = 13 ∧ degreeIn G (q 3) a = 1 ∧
        11 ≤ contacts G c.triangle a ∧
        ∀ x ∈ c.triangle, ∀ u ∈ a, QuadOn G (insert x (a.erase u)) := by
    have has : a ∉ bs := fun he ↦ hna (mem_insert_of_mem he)
    have hab : a ≠ b := fun he ↦ hna (mem_insert.mpr (Or.inl he))
    obtain ⟨htotal, hlow⟩ := heavy_exact hc r hcard hdeg hn hb hnb hcore hz hzl hzrep ha has hab hh
    obtain ⟨_, htri, _, _, _, hrep⟩ := heavy_shape hc r hcard hdeg hn hb hbq hcore ha has hab hh
    exact ⟨htotal, hlow, htri, hrep⟩
  obtain ⟨a, ha, hna, hheavy, d, hd, hnd, hda, hdheavy⟩ :=
    exists_two_heavy c hcard hdeg (insert b bs) hsel (rows c q)
      (rows_card c q (r.blocks_subset r.contains_cycle)) hinside
      (fun a ha hna hh ↦ le_of_eq (hdata a ha hna hh).1)
  obtain ⟨_, hla, hta, hra⟩ := hdata a ha hna hheavy
  obtain ⟨_, hld, htd, hrd⟩ := hdata d hd hnd hdheavy
  exact r.no_two_dense_low_blocks hcard hn 3 (Or.inr rfl) ha hd
    (fun he ↦ hna (mem_insert_of_mem he)) (fun he ↦ hnd (mem_insert_of_mem he)) hda.symm
    hta htd (by omega) (by omega) hra hrd

end Erdos577.CoreTransfer
