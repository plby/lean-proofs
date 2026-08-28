import ErdosProblems.Erdos577.WeightedFourteenSixPreparation
import ErdosProblems.Erdos577.TriangleHighContact

/-! The strict-score argument selects the three-contact center in the case-(6) heavy block. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem six_rows {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (v : Quadrilateral G) (hv : v.support = a) (swap : Bool)
    (h6 : PawBlock.Pattern6 (FirstPaw.normalizedPaw p swap) v)
    (hx2 : degreeIn G p.leaf a = 2) (hy2 : degreeIn G (q 1) a = 2)
    (hE : 9 ≤ contacts G p.support a) :
    ¬G.Adj (q 1) (v 1) ∧ G.Adj (q 1) (v 0) ∧ contacts G p.support a = 9 ∧
      PawBlock.ExactRows (FirstPaw.normalizedPaw p swap) v ![3, 13, 7, 1] := by
  obtain ⟨hnon, htotal, hrows⟩ := six_columns_exact hc hcard hn p hp hb q hq hd h ha hab
    v hv swap h6 hx2 hy2 hE
  let z := FirstPaw.normalizedPaw p swap
  have hfull0 (i : Fin 4) : G.Adj (z.vertices i) (v 0) := by
    rcases hrows with hr | hr
    · have hbits : ∀ i : Fin 4, ((![3, 13, 7, 1] : Fin 4 → ℕ) i).testBit 0 = true := by
        decide +kernel
      exact (hr i 0).mpr (hbits i)
    · have hbits : ∀ i : Fin 4, ((![3, 15, 5, 1] : Fin 4 → ℕ) i).testBit 0 = true := by
        decide +kernel
      exact (hr i 0).mpr (hbits i)
  have hfull : ∀ u ∈ p.triangle, G.Adj (v 0) u := by
    intro u hu
    rw [← FirstPaw.normalizedPaw_triangle p swap] at hu
    change u ∈ {z.vertices 1, z.vertices 2, z.vertices 3} at hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact (hfull0 1).symm
    · exact (hfull0 2).symm
    · exact (hfull0 3).symm
  obtain ⟨d, hdF, hdx, hdt, hkeep⟩ := exists_terminal_chain hc p hp hb q hq hd h 1
  change d.terminal = q 1 at hdx
  have hscore : edgeCount G a ≤ 5 := by
    rw [← hv, v.edgeCount_eq, if_pos h6.1.1, if_neg h6.1.2]
  have hy0 := hdF.terminal_high_contact hcard hn (hkeep a ha hab) v hv
    (by rw [hdt]; exact hfull) hscore (by rw [hdx, hv]; exact hy2)
  rw [hdx] at hy0
  refine ⟨hnon, hy0, htotal, ?_⟩
  rcases hrows with hr | hr
  · exact hr
  have hrf (j : Fin 4) : G.Adj p.center (v j) := by
    have hbits : ∀ j : Fin 4, (15 : ℕ).testBit j.val = true := by decide +kernel
    have hh := (hr 1 j).mpr (hbits j)
    change G.Adj z.center (v j) at hh
    rwa [FirstPaw.normalizedPaw_center] at hh
  have hrout : p.center ∉ v.support := by
    intro hh
    have hmem : p.center ∈ c.remainder := by
      rw [← hp, p.support_eq]
      exact mem_insert_of_mem p.center_mem_triangle
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha (hv ▸ hh))).2 hmem
  have hrep := v.quad_replaceAt 0 p.center hrout (fun j _ ↦ hrf j)
  rw [hv] at hrep
  have hx0 := hfull0 0
  change G.Adj z.leaf (v 0) at hx0
  rw [FirstPaw.normalizedPaw_leaf] at hx0
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab 8
  change ¬CommonReplacement G p.leaf (q 1) p.center a at hno
  exact False.elim (hno ⟨v 0, hv ▸ (v.mem_support _).mpr ⟨0, rfl⟩, hx0, hy0, hrep⟩)

end Erdos577.WeightedFourteen
