import ErdosProblems.Erdos1105.PathCycleSplice
import ErdosProblems.Erdos1105.PathSegments
import ErdosProblems.Erdos1105.AdjoinRepresentative

namespace Erdos1105

open SimpleGraph

theorem exists_three_path_lengths (a b c k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hk : 3 ≤ k) (hcap : k ≤ a + b + c) :
    ∃ i j l : ℕ, i < a ∧ j < b ∧ l < c ∧ i + j + l + 3 = k := by
  refine ⟨min (a - 1) (k - 3), min (b - 1) (k - 3 - min (a - 1) (k - 3)),
    k - 3 - min (a - 1) (k - 3) - min (b - 1) (k - 3 - min (a - 1) (k - 3)),
    ?_, ?_, ?_, ?_⟩ <;> omega

theorem cycle_of_three_disjoint_paths {V : Type*} {G : SimpleGraph V}
    {a b c d e f : V} (p : G.Walk a b) (q : G.Walk c d) (r : G.Walk e f)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hpq : p.support.Disjoint q.support) (hpr : p.support.Disjoint r.support)
    (hqr : q.support.Disjoint r.support)
    (hbc : G.Adj b c) (hde : G.Adj d e) (hfa : G.Adj f a) :
    ∃ s : G.Walk f f, s.IsCycle ∧ s.length = p.length + q.length + r.length + 3 := by
  let t := q.append (Walk.cons hde r)
  have ht : t.IsPath := by
    apply Walk.IsPath.mk'
    simp only [t, Walk.support_append, Walk.support_cons, List.tail_cons]
    exact List.nodup_append'.mpr ⟨hq.support_nodup, hr.support_nodup, hqr⟩
  have hpt : p.support.Disjoint t.support := by
    simp only [t, Walk.support_append, Walk.support_cons, List.tail_cons,
      List.disjoint_append_right]
    exact ⟨hpq, hpr⟩
  obtain ⟨s, hs, hlen⟩ := cycle_of_two_disjoint_paths p t hp ht hpt hbc hfa
    (by simp only [t, Walk.length_append, Walk.length_cons]; omega)
  exact ⟨s, hs, by simp only [t, Walk.length_append, Walk.length_cons] at hlen; omega⟩

/-- Three disjoint representative paths whose vertex counts total `k`
force a repeated cross-edge color, when the cross colors are all absent
from the representative. -/
theorem three_paths_cross_colors {V C : Type*} {k : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet)
    (hH : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    {a b u v w z : V} (p : R.Walk a b) (q : R.Walk u v) (r : R.Walk w z)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hpq : p.support.Disjoint q.support) (hpr : p.support.Disjoint r.support)
    (hqr : q.support.Disjoint r.support) (hlen : p.length + q.length + r.length + 3 = k)
    (hnew₁ : ∀ e ∈ R.edgeSet, extendColor c s(b, u) ≠ extendColor c e)
    (hnew₂ : ∀ e ∈ R.edgeSet, extendColor c s(v, w) ≠ extendColor c e)
    (hnew₃ : ∀ e ∈ R.edgeSet, extendColor c s(z, a) ≠ extendColor c e) :
    extendColor c s(b, u) = extendColor c s(v, w) ∨
      extendColor c s(v, w) = extendColor c s(z, a) ∨
      extendColor c s(z, a) = extendColor c s(b, u) := by
  by_contra h
  have h₁₂ : extendColor c s(b, u) ≠ extendColor c s(v, w) := by tauto
  have h₂₃ : extendColor c s(v, w) ≠ extendColor c s(z, a) := by tauto
  have h₃₁ : extendColor c s(z, a) ≠ extendColor c s(b, u) := by tauto
  have hbu : b ≠ u := fun h ↦ hpq p.end_mem_support (h.symm ▸ q.start_mem_support)
  have hvw : v ≠ w := fun h ↦ hqr q.end_mem_support (h.symm ▸ r.start_mem_support)
  have hza : z ≠ a := fun h ↦ hpr p.start_mem_support (h ▸ r.end_mem_support)
  let d₁ : (⊤ : SimpleGraph V).edgeSet := ⟨s(b, u), hbu⟩
  let d₂ : (⊤ : SimpleGraph V).edgeSet := ⟨s(v, w), hvw⟩
  let d₃ : (⊤ : SimpleGraph V).edgeSet := ⟨s(z, a), hza⟩
  let H₁ := adjoinRepresentative R d₁
  let H₂ := adjoinRepresentative H₁ d₂
  let H := adjoinRepresentative H₂ d₃
  have hr₁ : Set.InjOn (extendColor c) H₁.edgeSet := adjoinRepresentative_rainbow c R hR d₁ hnew₁
  have hr₂ : Set.InjOn (extendColor c) H₂.edgeSet := by
    apply adjoinRepresentative_rainbow c H₁ hr₁ d₂
    intro e he
    rcases (mem_adjoinRepresentative R d₁ e).mp he with he | rfl
    · exact hnew₂ e he
    · exact Ne.symm h₁₂
  have hrH : Set.InjOn (extendColor c) H.edgeSet := by
    apply adjoinRepresentative_rainbow c H₂ hr₂ d₃
    intro e he
    rcases (mem_adjoinRepresentative H₁ d₂ e).mp he with he | rfl
    · rcases (mem_adjoinRepresentative R d₁ e).mp he with he | rfl
      · exact hnew₃ e he
      · exact h₃₁
    · exact Ne.symm h₂₃
  have h₁₂H : H₁ ≤ H₂ := le_adjoinRepresentative H₁ d₂
  have h₂H : H₂ ≤ H := le_adjoinRepresentative H₂ d₃
  have hRH : R ≤ H := ((le_adjoinRepresentative R d₁).trans h₁₂H).trans h₂H
  have hsubp : ∀ e ∈ p.edges, e ∈ H.edgeSet := fun _ he ↦ edgeSet_mono hRH (p.edges_subset_edgeSet he)
  have hsubq : ∀ e ∈ q.edges, e ∈ H.edgeSet := fun _ he ↦ edgeSet_mono hRH (q.edges_subset_edgeSet he)
  have hsubr : ∀ e ∈ r.edges, e ∈ H.edgeSet := fun _ he ↦ edgeSet_mono hRH (r.edges_subset_edgeSet he)
  obtain ⟨s, hs, hslen⟩ := cycle_of_three_disjoint_paths
    (p.transfer H hsubp) (q.transfer H hsubq) (r.transfer H hsubr)
    (Walk.IsPath.mk' (by simpa only [Walk.support_transfer] using hp.support_nodup))
    (Walk.IsPath.mk' (by simpa only [Walk.support_transfer] using hq.support_nodup))
    (Walk.IsPath.mk' (by simpa only [Walk.support_transfer] using hr.support_nodup))
    (by simpa using hpq) (by simpa using hpr) (by simpa using hqr)
    (edgeSet_mono (h₁₂H.trans h₂H) (added_mem_adjoinRepresentative R d₁))
    (edgeSet_mono h₂H (added_mem_adjoinRepresentative H₁ d₂))
    (added_mem_adjoinRepresentative H₂ d₃)
  simp only [Walk.length_transfer] at hslen
  obtain ⟨f⟩ := (cycleGraph_isContained_iff (by omega : 2 < k)).mpr
    ⟨z, s, hs, hslen.trans hlen⟩
  exact hH ((Copy.ofLE H ⊤ le_top).comp f) (isRainbow_comp_of_color_injOn le_top c hrH f)

/-- Three chords join three consecutive pieces of a path into a cycle
through every vertex of the path. -/
theorem cycle_of_three_segment_chords {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) {a t : ℕ}
    (ha : 1 ≤ a) (hat : a ≤ t) (ht : t < p.length)
    (h₁ : G.Adj (p.getVert (a - 1)) (p.getVert t))
    (h₂ : G.Adj (p.getVert a) y) (h₃ : G.Adj (p.getVert (t + 1)) x) :
    ∃ v, ∃ s : G.Walk v v, s.IsCycle ∧ s.length = p.length + 1 := by
  let r₁ := pathSegment p 0 (a - 1) (Nat.zero_le _)
  let r₂ := pathSegment p a t hat
  let r₃ := pathSegment p (t + 1) p.length (by omega)
  have hd₁₂ : r₁.support.Disjoint r₂.reverse.support := by
    simpa only [Walk.support_reverse, List.disjoint_reverse_right] using
      disjoint_pathSegments p hp 0 (a - 1) a t (by omega) (by omega) hat ht.le
  have hd₁₃ : r₁.support.Disjoint r₃.reverse.support := by
    simpa only [Walk.support_reverse, List.disjoint_reverse_right] using
      disjoint_pathSegments p hp 0 (a - 1) (t + 1) p.length
        (by omega) (by omega) (by omega) le_rfl
  have hd₂₃ : r₂.reverse.support.Disjoint r₃.reverse.support := by
    simpa only [Walk.support_reverse, List.disjoint_reverse_left, List.disjoint_reverse_right] using
      disjoint_pathSegments p hp a t (t + 1) p.length hat (by omega) (by omega) le_rfl
  obtain ⟨s, hs, hlen⟩ := cycle_of_three_disjoint_paths r₁ r₂.reverse r₃.reverse
    (pathSegment_isPath p hp _ _ _) (pathSegment_isPath p hp _ _ _).reverse
    (pathSegment_isPath p hp _ _ _).reverse hd₁₂ hd₁₃ hd₂₃ h₁
    (by simpa only [Walk.getVert_length] using h₂)
    (by simpa only [Walk.getVert_zero] using h₃)
  refine ⟨p.getVert (t + 1), s, hs, ?_⟩
  have hlen₁ : r₁.length = a - 1 := by
    simpa using pathSegment_length p 0 (a - 1) (by omega) (by omega)
  have hlen₂ : r₂.length = t - a := pathSegment_length p a t hat ht.le
  have hlen₃ : r₃.length = p.length - (t + 1) :=
    pathSegment_length p (t + 1) p.length (by omega) le_rfl
  rw [Walk.length_reverse, Walk.length_reverse, hlen₁, hlen₂, hlen₃] at hlen
  omega

end Erdos1105

#print axioms Erdos1105.cycle_of_three_segment_chords
