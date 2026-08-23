import ErdosProblems.Erdos1105.TwoPathCycle
import ErdosProblems.Erdos1105.PrivateColors

namespace Erdos1105

open SimpleGraph

lemma nonprivate_color_ne_representative {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (d : (⊤ : SimpleGraph V).edgeSet) (hd : ∀ w, ¬PrivateAt c w (c d)) (e : R.edgeSet) :
    extendColor c d.val ≠ extendColor c e.val := by
  intro hcol
  have hraw : c d = c ⟨e.val, edgeSet_mono le_top e.property⟩ := by
    apply Option.some.inj
    rw [← extendColor_edge c d, ← extendColor_edge c ⟨e.val, edgeSet_mono le_top e.property⟩]
    exact hcol
  obtain ⟨w, hw⟩ := howned e
  apply hd w
  rwa [hraw]

lemma distinct_component_vertices_ne {V : Type*} {R : SimpleGraph V}
    {B D : R.ConnectedComponent} (hBD : B ≠ D) (x : B) (y : D) : x.val ≠ y.val := by
  intro hxy
  apply hBD
  exact ((B.mem_supp_iff _).mp x.property).symm.trans
    (hxy ▸ (D.mem_supp_iff _).mp y.property)

def componentHom {V : Type*} (R : SimpleGraph V) (B : R.ConnectedComponent) :
    B.toSimpleGraph →g R := { toFun := Subtype.val, map_rel' := fun h ↦ h }

lemma componentHom_injective {V : Type*} (R : SimpleGraph V) (B : R.ConnectedComponent) :
    Function.Injective (componentHom R B) := Subtype.val_injective

lemma component_walks_disjoint {V : Type*} (R : SimpleGraph V)
    (B D : R.ConnectedComponent) (hBD : B ≠ D) {a b : B} {u v : D}
    (p : B.toSimpleGraph.Walk a b) (q : D.toSimpleGraph.Walk u v) :
    (p.map (componentHom R B)).support.Disjoint (q.map (componentHom R D)).support := by
  intro z hzB hzD
  rw [Walk.support_map] at hzB hzD
  obtain ⟨x, _, hx⟩ := List.mem_map.mp hzB
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hzD
  exact distinct_component_vertices_ne hBD x y (hx.trans hy.symm)

/-- Two-path color equality, expressed entirely in the component vertex types. -/
theorem component_paths_cross_colors_eq {V C : Type*} {k : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet)
    (hH : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (B D : R.ConnectedComponent) (hBD : B ≠ D)
    (hnew : ∀ (x : B) (y : D) (e : R.edgeSet),
      extendColor c s(x.val, y.val) ≠ extendColor c e.val)
    {a b : B} {u v : D} (p : B.toSimpleGraph.Walk a b) (q : D.toSimpleGraph.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath) (hlen : p.length + q.length + 2 = k) (hk : 3 ≤ k) :
    extendColor c s(b.val, u.val) = extendColor c s(v.val, a.val) := by
  let fB : B.toSimpleGraph →g R := { toFun := Subtype.val, map_rel' := fun h ↦ h }
  let fD : D.toSimpleGraph →g R := { toFun := Subtype.val, map_rel' := fun h ↦ h }
  let p' := p.map fB
  let q' := q.map fD
  have hdisj : p'.support.Disjoint q'.support := by
    intro z hzB hzD
    change z ∈ (p.map fB).support at hzB
    change z ∈ (q.map fD).support at hzD
    rw [Walk.support_map] at hzB hzD
    obtain ⟨x, _, hx⟩ := List.mem_map.mp hzB
    obtain ⟨y, _, hy⟩ := List.mem_map.mp hzD
    exact distinct_component_vertices_ne hBD x y (hx.trans hy.symm)
  apply two_paths_cross_colors_eq c R hR hH p' q' (hp.map Subtype.val_injective)
    (hq.map Subtype.val_injective)
    hdisj (by simpa only [p', q', Walk.length_map] using hlen) hk
  · intro e he
    exact hnew b u ⟨e, he⟩
  · intro e he
    change extendColor c s(v.val, a.val) ≠ extendColor c e
    simpa only [Sym2.eq_swap] using hnew a v ⟨e, he⟩

end Erdos1105
