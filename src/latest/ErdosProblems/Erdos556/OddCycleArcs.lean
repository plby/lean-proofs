import ErdosProblems.Erdos556.PathOperations
import ErdosProblems.Erdos556.OddCycles

/-!
# Opposite-parity paths through an odd cycle

The two arcs between distinct vertices of an odd cycle have opposite
parities. Attaching disjoint paths to those vertices preserves that parity
difference and yields two simple paths with the desired endpoints.
-/

namespace Erdos556

open SimpleGraph

theorem exists_opposite_parity_arcs {V : Type*} {G : SimpleGraph V}
    {w : V} (c : G.Walk w w) (hc : c.IsCycle) (hodd : Odd c.length)
    (u v : V) (hu : u ∈ c.support) (hv : v ∈ c.support) (huv : u ≠ v) :
    ∃ p q : G.Walk u v, p.IsPath ∧ q.IsPath ∧
      p.length + q.length = c.length ∧ p.length % 2 ≠ q.length % 2 ∧
      p.support ⊆ c.support ∧ q.support ⊆ c.support := by
  classical
  let r := c.rotate u hu
  have hr : r.IsCycle := hc.rotate hu
  have hvr : v ∈ r.support := (c.mem_support_rotate_iff u hu).mpr hv
  let p := r.takeUntil v hvr
  let s := r.dropUntil v hvr
  have hp : p.IsPath := hr.isPath_takeUntil hvr
  have hs : s.IsPath := by
    have hcycle : (p.append s).IsCycle := by
      simpa only [p, s, Walk.take_spec] using hr
    exact hcycle.isPath_of_append_right (Walk.not_nil_of_ne huv)
  have hlen : p.length + s.reverse.length = c.length := by
    have h := congrArg Walk.length (r.take_spec hvr)
    simpa only [Walk.length_append, r, Walk.length_rotate, Walk.length_reverse] using h
  refine ⟨p, s.reverse, hp, hs.reverse, hlen, ?_, ?_, ?_⟩
  · have ho := Nat.odd_iff.mp hodd
    omega
  · intro x hx
    exact (c.mem_support_rotate_iff u hu).mp (r.support_takeUntil_subset_support hvr hx)
  · intro x hx
    rw [Walk.support_reverse, List.mem_reverse] at hx
    exact (c.mem_support_rotate_iff u hu).mp (r.support_dropUntil_subset_support hvr hx)

/-- Attach vertex-disjoint paths to two distinct vertices of an odd cycle.
The resulting paths have opposite parity and remain inside the union of
the three supplied supports. -/
theorem exists_opposite_parity_paths_through_cycle {V : Type*} {G : SimpleGraph V}
    {w u v x y : V} (c : G.Walk w w) (hc : c.IsCycle) (hodd : Odd c.length)
    (p : G.Walk u x) (q : G.Walk v y) (hp : p.IsPath) (hq : q.IsPath)
    (hx : x ∈ c.support) (hy : y ∈ c.support) (hxy : x ≠ y)
    (hpC : ∀ z ∈ p.support, z ∈ c.support → z = x)
    (hqC : ∀ z ∈ q.support, z ∈ c.support → z = y)
    (hpq : ∀ z ∈ p.support, z ∉ q.support) :
    ∃ p₀ p₁ : G.Walk u v, p₀.IsPath ∧ p₁.IsPath ∧
      p₀.length % 2 ≠ p₁.length % 2 ∧
      p₀.length ≤ p.length + q.length + c.length ∧
      p₁.length ≤ p.length + q.length + c.length ∧
      (∀ z ∈ p₀.support, z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support) ∧
      (∀ z ∈ p₁.support, z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support) := by
  obtain ⟨a, b, ha, hb, hlen, hpar, haC, hbC⟩ :=
    exists_opposite_parity_arcs c hc hodd x y hx hy hxy
  have hpath (r : G.Walk x y) (hr : r.IsPath) (hrC : r.support ⊆ c.support) :
      ((p.append r).append q.reverse).IsPath := by
    have hpr := isPath_append_of_support_inter p r hp hr
      (fun z hz hzr => hpC z hz (hrC hzr))
    apply isPath_append_of_support_inter (p.append r) q.reverse hpr hq.reverse
    intro z hz hzq
    rw [Walk.support_reverse, List.mem_reverse] at hzq
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzp | hzr
    · exact (hpq z hzp hzq).elim
    · exact hqC z hzq (hrC hzr)
  have hsupport (r : G.Walk x y) (hrC : r.support ⊆ c.support) (z : V)
      (hz : z ∈ ((p.append r).append q.reverse).support) :
      z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support := by
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzpr | hzq
    · rcases (Walk.mem_support_append_iff _ _).mp hzpr with hzp | hzr
      · exact Or.inl hzp
      · exact Or.inr (Or.inr (hrC hzr))
    · exact Or.inr (Or.inl (by simpa only [Walk.support_reverse, List.mem_reverse] using hzq))
  refine ⟨(p.append a).append q.reverse, (p.append b).append q.reverse,
    hpath a ha haC, hpath b hb hbC, ?_, ?_, ?_, hsupport a haC, hsupport b hbC⟩
  · simp only [Walk.length_append, Walk.length_reverse]
    omega
  · simp only [Walk.length_append, Walk.length_reverse]
    omega
  · simp only [Walk.length_append, Walk.length_reverse]
    omega

#print axioms exists_opposite_parity_paths_through_cycle

end Erdos556
