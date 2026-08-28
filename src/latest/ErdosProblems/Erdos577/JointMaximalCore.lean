import ErdosProblems.Erdos577.JointBridgeObstruction

/-! The additional two finite maxima are choices of a block in a fixed chain, TeX9.55. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def MaximalCore (c : TriangleChain G) (p : Paw G) (q : Quadrilateral G)
    (a : Finset V) : Prop :=
  CaseTwoCore c p q a ∧
    (∀ b, CaseTwoCore c p q b → contacts G p.triangle b ≤ contacts G p.triangle a) ∧
    (∀ b, CaseTwoCore c p q b → contacts G p.triangle b = contacts G p.triangle a →
      degreeIn G p.center b + degreeIn G (p.vertices 3) b ≤
        degreeIn G p.center a + degreeIn G (p.vertices 3) a)

theorem exists_maximal_core {c : TriangleChain G} (p : Paw G) (q : Quadrilateral G)
    {a : Finset V} (hconfig : CaseTwoCore c p q a) :
    ∃ b : Finset V, MaximalCore c p q b := by
  classical
  let candidates := c.blocks.filter (CaseTwoCore c p q)
  have ha : a ∈ candidates := mem_filter.mpr ⟨hconfig.2.2.1, hconfig⟩
  obtain ⟨b, hb, hmax⟩ := candidates.exists_max_image (contacts G p.triangle) ⟨a, ha⟩
  let firstMaxima := candidates.filter fun d ↦ contacts G p.triangle d = contacts G p.triangle b
  have hm : firstMaxima.Nonempty := ⟨b, mem_filter.mpr ⟨hb, rfl⟩⟩
  obtain ⟨d, hd, htie⟩ := firstMaxima.exists_max_image
    (fun e ↦ degreeIn G p.center e + degreeIn G (p.vertices 3) e) hm
  obtain ⟨hdc, he⟩ := mem_filter.mp hd
  refine ⟨d, (mem_filter.mp hdc).2, ?_, ?_⟩
  · intro e hec
    rw [he]
    exact hmax e (mem_filter.mpr ⟨hec.2.2.1, hec⟩)
  · intro e hec het
    exact htie e (mem_filter.mpr ⟨mem_filter.mpr ⟨hec.2.2.1, hec⟩, het.trans he⟩)

theorem exists_good_core_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (q : Quadrilateral G) {a : Finset V} (hconfig : CaseTwoCore c p q a) :
    ∃ b : Finset V, CaseTwoCore c p q b ∧ degreeIn G p.leaf b = 0 ∧
      degreeIn G (q 3) b = 0 ∧ ∃ η : Fin 2,
        degreeIn G p.center b + degreeIn G (p.vertices 3) b = 7 + η.val ∧
        10 - η.val ≤ contacts G p.triangle b := by
  have hdata := hconfig
  obtain ⟨hp, hs, _, _, hcase, _, _⟩ := hdata
  obtain ⟨b, hb, hbs, halt⟩ := exists_eight_alternative hc hcard hdeg hn p hp hs q rfl hcase
  rcases halt with hzero | hpositive
  · obtain ⟨hx, ht, η, hsum, hT⟩ := hzero
    have hη := η.isLt
    have hr4 := degreeIn_le_card G p.center b
    rw [(c.property.blocks_quad b hb).card] at hr4
    exact ⟨b, ⟨hp, hs, hb, hbs, hcase, by omega, by omega⟩, hx, ht, η, hsum, hT⟩
  · exact False.elim (JointBridge.other_block_false hc hcard hdeg hn p q hconfig hb hbs hpositive)

theorem maximal_core_seven_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (q : Quadrilateral G) {a : Finset V} (hmax : MaximalCore c p q a)
    (hseven : degreeIn G p.center a + degreeIn G (p.vertices 3) a = 7) :
    10 ≤ contacts G p.triangle a := by
  obtain ⟨b, hb, _, _, η, hsum, hT⟩ := exists_good_core_block hc hcard hdeg hn p q hmax.1
  have hle := hmax.2.1 b hb
  have hη := η.isLt
  by_contra hnot
  have he : contacts G p.triangle b = contacts G p.triangle a := by omega
  have htie := hmax.2.2 b hb he
  omega

theorem maximal_case_two_of_failure {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfail : 7 ≤ degreeIn G p.leaf s + degreeIn G (p.vertices 2) s ∨
      7 ≤ degreeIn G p.leaf s + degreeIn G (p.vertices 3) s) :
    ∃ (d : TriangleChain G) (p' : Paw G) (q : Quadrilateral G) (a : Finset V),
      d.Strong ∧ MaximalCore d p' q a ∧ p'.triangle = p.triangle ∧
      degreeIn G p'.center q.support = 0 ∧
      (degreeIn G p'.center a + degreeIn G (p'.vertices 3) a = 7 →
        10 ≤ contacts G p'.triangle a) := by
  obtain ⟨d, p', q, a, hd, hconfig, hT⟩ := case_two_reduction hc hcard hdeg hn p hp hs hfail
  obtain ⟨b, hb⟩ := exists_maximal_core p' q hconfig
  refine ⟨d, p', q, b, hd, hb, hT, ?_, ?_⟩
  · exact case_two_center_zero hd.toFeasible hcard hdeg hn p' hb.1.1 hb.1.2.1 q rfl
      hb.1.2.2.2.2.1
  · exact maximal_core_seven_bound hd.toFeasible hcard hdeg hn p' q hb

end Erdos577.JointClaims
