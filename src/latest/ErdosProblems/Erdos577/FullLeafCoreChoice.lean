import ErdosProblems.Erdos577.FullLeafCoreGeometry

/-! The additional contact maximum is attained by an actual strong configuration. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Maximal (c : TriangleChain G) (p : Paw G) (s a : Finset V) (y : V) : Prop :=
  Configuration c p s a y ∧
    ∀ (e : TriangleChain G) (p' : Paw G) (s' a' : Finset V) (y' : V),
      Configuration e p' s' a' y' →
        contacts G (insert (p'.vertices 3) a') s' ≤ contacts G (insert (p.vertices 3) a) s

theorem Configuration.objective_le_twenty {c : TriangleChain G} {p : Paw G}
    {s a : Finset V} {y : V} (h : Configuration c p s a y) :
    contacts G (insert (p.vertices 3) a) s ≤ 20 := by
  have hh := contacts_le_card_mul G (insert (p.vertices 3) a) s
  simpa only [h.second_five_card, h.first_clique.card_eq] using hh

theorem Configuration.exists_maximal {c : TriangleChain G} {p : Paw G}
    {s a : Finset V} {y : V} (h : Configuration c p s a y) :
    ∃ (e : TriangleChain G) (p' : Paw G) (s' a' : Finset V) (y' : V), Maximal e p' s' a' y' := by
  classical
  let attained (n : ℕ) : Prop := ∃ (e : TriangleChain G) (p' : Paw G) (s' a' : Finset V) (y' : V),
    Configuration e p' s' a' y' ∧ contacts G (insert (p'.vertices 3) a') s' = n
  let scores := (range 21).filter attained
  have hmem (e : TriangleChain G) (p' : Paw G) (s' a' : Finset V) (y' : V)
      (hh : Configuration e p' s' a' y') : contacts G (insert (p'.vertices 3) a') s' ∈ scores := by
    have hb := hh.objective_le_twenty
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), e, p', s', a', y', hh, rfl⟩
  obtain ⟨m, hm, hmax⟩ := scores.exists_max_image id
    ⟨contacts G (insert (p.vertices 3) a) s, hmem c p s a y h⟩
  obtain ⟨e, p', s', a', y', hh, he⟩ := (mem_filter.mp hm).2
  refine ⟨e, p', s', a', y', hh, ?_⟩
  intro d q t b z hz
  rw [he]
  exact hmax _ (hmem d q t b z hz)

theorem Configuration.exists_strong_maximal {c : TriangleChain G} {p : Paw G}
    {s a : Finset V} {y : V} (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    ∃ (e : TriangleChain G) (p' : Paw G) (s' a' : Finset V) (y' : V),
      e.Strong ∧ Maximal e p' s' a' y' ∧ e.terminal = p'.leaf ∧ e.triangle = p'.triangle := by
  obtain ⟨d, q, t, b, z, hh, hmax⟩ := h.exists_maximal
  let e := d.presentPaw q hh.paw
  have he : Configuration e q t b z :=
    ⟨hh.feasible.presentPaw_feasible q hh.paw, q.support_eq, hh.first, hh.core, hh.different,
      hh.full, hh.exposed, hh.attached, hh.dense⟩
  exact ⟨e, q, t, b, z, hh.feasible.presentPaw_strong hcard hn q hh.paw,
    ⟨he, hmax⟩, rfl, rfl⟩

theorem Maximal.transfer {c e : TriangleChain G} {p q : Paw G}
    {s a t b : Finset V} {y z : V} (h : Maximal c p s a y) (he : Configuration e q t b z)
    (hscore : contacts G (insert (q.vertices 3) b) t = contacts G (insert (p.vertices 3) a) s) :
    Maximal e q t b z := by
  refine ⟨he, ?_⟩
  intro d r j f w hw
  rw [hscore]
  exact h.2 d r j f w hw

theorem exists_configuration {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4)
    (hpositive : 1 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s) :
    ∃ (p' : Paw G) (a : Finset V) (y : V), Configuration c p' s a y ∧
      p'.leaf = p.leaf ∧ p'.triangle = p.triangle := by
  obtain ⟨_, _, _, a, ha, has, hT⟩ := hc.full_leaf_preparation hcard hdeg hn p hp hs
    hfull hpositive
  by_cases hb : 0 < degreeIn G (p.vertices 2) s
  · obtain ⟨y, hy⟩ := card_pos.mp hb
    obtain ⟨hy, hby⟩ := mem_filter.mp hy
    exact ⟨p, a, y, ⟨hc, hp, hs, ha, has, hfull, hy, hby, hT⟩, rfl, rfl⟩
  · have hpos : 0 < degreeIn G (p.vertices 3) s := by omega
    obtain ⟨y, hy⟩ := card_pos.mp hpos
    obtain ⟨hy, hcy⟩ := mem_filter.mp hy
    refine ⟨p.swapNoncentral, a, y, ?_, p.swapNoncentral_leaf, p.swapNoncentral_triangle⟩
    refine ⟨hc, ?_, hs, ha, has, ?_, hy, ?_, ?_⟩
    · rw [Paw.swapNoncentral_support, hp]
    · simpa only [Paw.swapNoncentral_leaf] using hfull
    · simpa only [Paw.swapNoncentral_apply, Equiv.swap_apply_left] using hcy
    · simpa only [Paw.swapNoncentral_triangle] using hT

end Erdos577.FullLeafCore
