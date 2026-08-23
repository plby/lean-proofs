import ErdosProblems.Erdos1105.CycleBoundary
import ErdosProblems.Erdos1105.CycleExtension

namespace Erdos1105

open SimpleGraph

/-- A rainbow private `(k-1)`-cycle has no external neighbor whose vertex
has at least two private colors. This is the first component claim in the
structural proof of the cycle upper bound. -/
theorem private_cycle_no_external_neighbor {V C : Type*} [Fintype C] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (f : (cycleGraph (n + 3)).Copy R) (u : V) (hu : u ∉ Set.range f)
    (hnew : 2 ≤ (privateColors c u).card) : ¬R.Adj u (f 0) := by
  classical
  intro hadj
  have hboundary := private_representative_cycle_boundary c hH R hR howned f u hu hadj
  let a := c ⟨s(u, f 0), hadj.ne⟩
  have hchoice : ∃ i ∈ privateColors c u, i ≠ a := by
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (privateColors c u).card)
    by_cases hia : i = a
    · exact ⟨j, hj, fun hja ↦ hij (hia.trans hja.symm)⟩
    · exact ⟨i, hi, hia⟩
  obtain ⟨i, hi, hia⟩ := hchoice
  have hip : PrivateAt c u i := (mem_privateColors c u i).mp hi
  obtain ⟨⟨e, he⟩, hci⟩ := hc i
  have humem := hip ⟨e, he⟩ hci
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp humem
  have huw : u ≠ w := he
  have hw : w ∉ Set.range f := by
    rintro ⟨j, rfl⟩
    apply hia
    have hraw : c ⟨s(u, f j), he⟩ = a := by
      apply Option.some.inj
      rw [← extendColor_edge c ⟨s(u, f j), he⟩,
        ← extendColor_edge c ⟨s(u, f 0), hadj.ne⟩]
      exact hboundary.1 j
    exact hci.symm.trans hraw
  let q := (cycleGraph.cycle n).map f.toHom
  have hq : q.IsCycle := cycleGraph.isCycle_cycle.map f.injective
  have hqH : ∀ g : (cycleGraph (q.length + 1)).Copy (⊤ : SimpleGraph V), ¬IsRainbow g c := by
    have hlen : q.length + 1 = n + 4 := by simp [q]
    rwa [hlen]
  have hs (x : V) (hx : x ∈ q.support) : x ∈ Set.range f := by
    rw [Walk.support_map] at hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨j, rfl⟩
  have hconst : ∀ x ∈ q.support, extendColor c s(u, x) = some a := by
    intro x hx
    obtain ⟨j, rfl⟩ := hs x hx
    exact (hboundary.1 j).trans (extendColor_edge c ⟨s(u, f 0), hadj.ne⟩)
  apply private_cycle_two_colors_impossible c R hR howned q hq hqH u w
    (fun hx ↦ hu (hs u hx)) (fun hx ↦ hw (hs w hx)) huw a hboundary.2 hconst
  · rwa [hci]
  · exact fun h ↦ hia (hci.symm.trans h.symm)

/-- Rotating a cycle copy changes its distinguished first vertex. -/
def rotateCycleCopy {V : Type*} {R : SimpleGraph V} {n : ℕ}
    (f : (cycleGraph (n + 3)).Copy R) (i : Fin (n + 3)) :
    (cycleGraph (n + 3)).Copy R where
  toHom :=
    { toFun := fun j ↦ f (j + i)
      map_rel' := by
        intro j k h
        apply f.toHom.map_rel'
        rw [cycleGraph_adj] at h ⊢
        simpa only [add_sub_add_right_eq_sub] using h }
  injective' := fun _ _ h ↦ add_right_cancel (f.injective h)

/-- Consequently, the entire connected component of such a cycle is
contained in its vertex set. -/
theorem private_cycle_component_contained {V C : Type*} [Fintype C] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    (f : (cycleGraph (n + 3)).Copy R) (x : V) (hx : R.Reachable (f 0) x) :
    x ∈ Set.range f := by
  classical
  by_contra hnot
  obtain ⟨p⟩ := hx
  obtain ⟨d, _, hdin, hdout⟩ := p.exists_boundary_dart (Set.range f) ⟨0, rfl⟩ hnot
  obtain ⟨i, hi⟩ := hdin
  let g := rotateCycleCopy f i
  have hout : d.snd ∉ Set.range g := by
    rintro ⟨j, hj⟩
    exact hdout ⟨j + i, hj⟩
  apply private_cycle_no_external_neighbor c hc hH R hR howned g d.snd hout (hnew d.snd)
  have hg0 : g 0 = d.fst := by
    change f (0 + i) = d.fst
    simpa using hi
  rw [hg0]
  exact d.adj.symm

/-- A component containing a path on at least `k` vertices cannot contain
a private `(k-1)`-cycle. -/
theorem private_cycle_absent_in_large_path_component {V C : Type*} [Finite V] [Fintype C] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    {x y : V} (p : R.Walk x y) (hp : p.IsPath) (hlen : n + 3 ≤ p.length)
    (f : (cycleGraph (n + 3)).Copy R) (hreach : R.Reachable x (f 0)) : False := by
  classical
  have hsub : (p.support.toFinset : Set V) ⊆ Set.range f := by
    intro z hz
    have hzp : z ∈ p.support := List.mem_toFinset.mp hz
    exact private_cycle_component_contained c hc hH R hR howned hnew f z
      (hreach.symm.trans ⟨p.takeUntil z hzp⟩)
  have hcard := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.support_nodup,
    Walk.length_support, Set.ncard_range_of_injective (f := fun i ↦ f i) f.injective,
    Nat.card_fin] at hcard
  omega

/-- No induced vertex set inside a large-path component contains a
`(k-1)`-cycle, even when its other edges are not part of the path. -/
theorem private_cycle_free_on_reachable_set {V C : Type*} [Finite V] [Fintype C] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    {x y : V} (p : R.Walk x y) (hp : p.IsPath) (hlen : n + 3 ≤ p.length)
    (S : Set V) (hS : ∀ z ∈ S, R.Reachable x z) :
    ¬cycleGraph (n + 3) ⊑ R.induce S := by
  rintro ⟨f⟩
  exact private_cycle_absent_in_large_path_component c hc hH R hR howned hnew p hp hlen
    ((Copy.induce R S).comp f) (hS (f 0).val (f 0).property)

end Erdos1105
