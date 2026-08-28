import ErdosProblems.Erdos577.JointFirstSwap
import ErdosProblems.Erdos577.CoreDirectObstruction

/-! The direct core obstruction applies to either of the two actual strong terminals. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem terminal_high_pair_forbidden {c : TriangleChain G} (hc : c.Strong) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hT : c.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks) (j : Quadrilateral G) (hj : j.support ∈ c.blocks)
    (haj : a ≠ j.support) (hdiag : ¬G.Adj (j 1) (j 3))
    (hcore : ∀ v, v ∉ p.triangle ∪ a → 2 ≤ degreeIn G v (p.triangle ∪ a) →
      LocalFactor G (insert v (p.triangle ∪ a)))
    {z w : V} (hz : z ∈ a) (hw : w ∈ a) (hne : z ≠ w)
    (hrz : G.Adj p.center z) (hrep : QuadOn G (insert (p.vertices 3) (a.erase z)))
    (hz1 : G.Adj z (j 1)) (hz2 : G.Adj z (j 2)) (hw2 : G.Adj w (j 2)) :
    ¬(G.Adj c.terminal (j 0) ∧ G.Adj c.terminal (j 2)) := by
  rintro ⟨h0, h2⟩
  have hcore' : ∀ v, v ∉ c.triangle ∪ a → 2 ≤ degreeIn G v (c.triangle ∪ a) →
      LocalFactor G (insert v (c.triangle ∪ a)) := by rwa [hT]
  have hrep' : z ∈ a → ∃ x ∈ c.triangle, ∃ y ∈ c.triangle,
      x ≠ y ∧ G.Adj z x ∧ QuadOn G (insert y (a.erase z)) := by
    intro _
    rw [hT]
    exact ⟨p.center, p.center_mem_triangle, p.vertices 3, by simp [Paw.triangle],
      p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 3), hrz.symm, hrep⟩
  have hbound := CoreTransfer.direct_core_degree_le_one hc j hj hcard hdeg hn hdiag
    h0 h2 ha haj hcore' (mem_union_right _ hz) hz1 hrep'
  have hpair : ({z, w} : Finset V) ⊆ (c.triangle ∪ a).filter (G.Adj (j 2)) :=
    insert_subset (mem_filter.mpr ⟨mem_union_right _ hz, hz2.symm⟩)
      (singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_union_right _ hw, hw2.symm⟩))
  have htwo := card_le_card hpair
  rw [card_pair_eq_two_iff.mpr hne] at htwo
  change 2 ≤ degreeIn G (j 2) (c.triangle ∪ a) at htwo
  omega

theorem both_leaves_high_pair_forbidden {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q)
    (j : Quadrilateral G) (hj : j.support ∈ c.blocks) (hjs : j.support ≠ s)
    (haj : a ≠ j.support) (hdiag : ¬G.Adj (j 1) (j 3))
    (hcore : ∀ v, v ∉ p.triangle ∪ a → 2 ≤ degreeIn G v (p.triangle ∪ a) →
      LocalFactor G (insert v (p.triangle ∪ a)))
    {z w : V} (hz : z ∈ a) (hw : w ∈ a) (hne : z ≠ w)
    (hrz : G.Adj p.center z) (hrep : QuadOn G (insert (p.vertices 3) (a.erase z)))
    (hz1 : G.Adj z (j 1)) (hz2 : G.Adj z (j 2)) (hw2 : G.Adj w (j 2)) :
    ¬(G.Adj p.leaf (j 0) ∧ G.Adj p.leaf (j 2)) ∧
    ¬(G.Adj (q 1) (j 0) ∧ G.Adj (q 1) (j 2)) := by
  have hx := terminal_high_pair_forbidden (hc.presentPaw_strong hcard hn p hp)
    hcard hdeg hn p rfl ha j hj haj hdiag hcore hz hw hne hrz hrep hz1 hz2 hw2
  obtain ⟨d, hd, ht, hT, _, _, _, hkeep⟩ := exists_center_terminal hc hcard hn p hp hs q hq hcase
  have hv := terminal_high_pair_forbidden hd hcard hdeg hn p hT (hkeep a ha has)
    j (hkeep j.support hj hjs) haj hdiag hcore hz hw hne hrz hrep hz1 hz2 hw2
  rw [ht] at hv
  exact ⟨hx, hv⟩

end Erdos577.JointFirst
