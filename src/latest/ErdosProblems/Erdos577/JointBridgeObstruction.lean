import ErdosProblems.Erdos577.JointBridgeRowObstruction

/-! TeX9.54: no other block has a positive eight-row alternative in a CaseII core configuration. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem other_block_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (q : Quadrilateral G) {a : Finset V} (hconfig : JointClaims.CaseTwoCore c p q a)
    {b : Finset V} (hb : b ∈ c.blocks) (hbs : b ≠ q.support)
    (hpositive : Positive p q b) : False := by
  obtain ⟨hp, hs, ha, has, hcase, houter, hweighted⟩ := hconfig
  obtain ⟨_, ht0, v, hv, hne, hr1, hr2, hz, hrep, hprimary, hpe, hsec1, hsec2, _,
      hcore, _, _, h17, _, _, _⟩ := JointClaims.dense_seven_vertex_core hc hcard hdeg hn
    p hp hs ha has q rfl (Or.inr hcase) houter hweighted
  have h1 : v 2 ∈ a := hv ▸ (v.mem_support _).mpr ⟨2, rfl⟩
  have h2 : v 3 ∈ a := hv ▸ (v.mem_support _).mpr ⟨3, rfl⟩
  obtain ⟨ht3, _, _⟩ := positive_degrees p q (c.property.blocks_quad b hb).card hpositive
  have hab : a ≠ b := by intro he; rw [← he, ht0] at ht3; omega
  obtain ⟨u, hu, hru, d, hd, ht, hT, _, _, hkeep⟩ :=
    exists_center_route hc hcard hn p hp hs hb hbs q rfl hcase hpositive
  have had := hkeep a ha has hab
  have hcol := block_core_degree_le_one hc hcard hn p hp hs ha hb has hbs hab.symm
    q rfl hcase ht3 hcore u hu
  have h4 := three_rows_on_bridge hc hcard hn p hp hs ha hb has hab hbs q rfl hcase
    ht3 hcore h1 h2 hne hr1 hr2 hsec1 hsec2
  have h30 := arms_inside_of_bounds p hp hs ha hb has hab hbs q rfl u (v 2) (v 3) hu hcol h17 h4
  obtain ⟨jset, hj, hjs, hja, hjb, hnine⟩ := exists_heavy_arms hcard hdeg p hp hs ha hb
    has hab hbs q rfl u (v 2) (v 3) hu h1 h2 hne h30
  obtain ⟨j, rfl⟩ := c.property.blocks_quad jset hj
  have hjd := hkeep j.support hj hjs hjb
  have hF (t : Finset V) (ht : t ∈ c.blocks) : Disjoint p.support t := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ht)
  have hAB := c.property.blocks_disjoint ha hb hab
  have hAJ := c.property.blocks_disjoint ha hj hja.symm
  have hBJ := c.property.blocks_disjoint hb hj hjb.symm
  have hfour := arms_card p u (v 2) (v 3) (hF a ha) (hF b hb) hAB hu h1 h2 hne
  have hdis : Disjoint (arms p u (v 2) (v 3)) j.support := by
    apply disjoint_left.mpr
    intro w hw hwj
    simp only [arms, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact disjoint_left.mp (hF j.support hj) (p.support_eq ▸ mem_insert_self _ _) hwj
    · exact disjoint_left.mp hBJ hu hwj
    · exact disjoint_left.mp hAJ h1 hwj
    · exact disjoint_left.mp hAJ h2 hwj
  have hrj : p.center ∉ j.support := fun hh ↦ disjoint_left.mp (hF j.support hj)
    ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩) hh
  have hno := arms_erase_no_factor hc hcard hn p hp hs ha hb hj has hab hbs hjs hja.symm hjb
    q rfl hcase ht3 hu hru d ht hT had hjd h1 h2 hne hprimary hsec1 hsec2
  obtain ⟨hcommon, hrows, hx2, hu2⟩ := arms_row_restrictions hc hd.toFeasible p hp
    u (v 2) (v 3) ht hj hjd hfour hdis hrj (arms_center p u (v 2) (v 3) hru hr1 hr2) hno hnine
  exact four_arm_obstruction hc hd hcard hdeg hn p hp u ht hT ha had j hj hjd hja.symm
    h1 h2 hr1 hr2 hz hrep hprimary hpe hcore hfour hdis hnine hcommon hrows hx2 hu2

end Erdos577.JointBridge
