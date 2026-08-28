import ErdosProblems.Erdos577.JointFirstGainGeometry
import ErdosProblems.Erdos577.AlmostComplete

/-! Two new blocks with at least eleven edges strictly improve the two old blocks. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem strict_crossing_gain {c : TriangleChain G} (hc : c.Feasible)
    {a : Finset V} (ha : a ∈ c.blocks)
    (j : Quadrilateral G) (hj : j.support ∈ c.blocks) (haj : a ≠ j.support)
    (hje : edgeCount G j.support = 4)
    (primary : Finset V) (hp : QuadOn G primary) (hpsub : primary ⊆ c.triangle ∪ a)
    (hpe : 5 ≤ edgeCount G primary)
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a) (h1p : z1 ∉ primary) (h2p : z2 ∉ primary)
    (hz : G.Adj z1 z2) (h11 : G.Adj z1 (j 1)) (h12 : G.Adj z1 (j 2))
    (h21 : G.Adj z2 (j 1)) (h22 : G.Adj z2 (j 2))
    (hx0 : G.Adj c.terminal (j 0)) (hx3 : G.Adj c.terminal (j 3)) : False := by
  have hcl := crossing_clique j hz h11 h12 h21 h22
  have hquad := QuadOn.of_clique hcl.card_eq hcl.isClique
  obtain ⟨hd, hu, hcard, htri⟩ := crossing_gain_geometry c ha j hj haj primary hp hpsub
    h1 h2 h1p h2p hcl hx0 hx3
  let parts := (BlockPartition.single hp).union (BlockPartition.single hquad) hd
  have hsel : ({a, j.support} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset ha (singleton_subset_iff.mpr hj)
  have hcore : c.remainder ∪ ({a, j.support} : Finset (Finset V)).biUnion id =
      c.remainder ∪ (a ∪ j.support) := by
    simp only [biUnion_insert, singleton_biUnion, id_eq]
  have hbound := hc.selected_edges_le {a, j.support} hsel parts
    (by rwa [hcore]) (by rwa [hcore]) (by rwa [hcore])
  have hold : (c.complementPartition.select {a, j.support} hsel).weightSum (edgeCount G) =
      edgeCount G a + edgeCount G j.support := by
    change ∑ t ∈ ({a, j.support} : Finset (Finset V)), edgeCount G t = _
    exact sum_pair haj
  have hbe : edgeCount G {z1, z2, j 1, j 2} = 6 := by
    rw [edgeCount_clique hcl.isClique, hcl.card_eq]
    rfl
  have hae : edgeCount G a ≤ 6 := by
    have hh := edgeCount_le_choose_two G a
    rw [(c.property.blocks_quad a ha).card] at hh
    exact hh
  rw [BlockPartition.weightSum_union, BlockPartition.weightSum_single,
    BlockPartition.weightSum_single, hold, hje, hbe] at hbound
  omega

end Erdos577.JointFirst
