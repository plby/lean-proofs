import ErdosProblems.Erdos73.TileEdgeGapSeparation

/-! Three-piece route regions have exactly the intersection pattern of their edges. -/

namespace Erdos73.BrickTileArray
noncomputable section
open scoped Classical
open SimpleGraph Finset

variable {c r C R : ℕ} (A : BrickTileArray c r C R)

theorem center_mem_arm (w : ElementaryWallVertex c r) (a : Fin 3) :
    A.center w ∈ (A.arm w a).vertexSet := by
  rw [← A.arm_source w a]
  exact (A.arm w a).source_mem_vertexSet

theorem center_on_arm {w u : ElementaryWallVertex c r} {a : Fin 3}
    (hw : A.center w ∈ (A.arm u a).vertexSet) : w = u := by
  by_contra hne
  exact Finset.disjoint_left.mp (A.arms_disjoint_of_ne hne 0 a) (A.center_mem_arm w 0) hw

theorem center_not_mem_edgeGap {u v : ElementaryWallVertex c r}
    (huv : (elementaryWall c r).Adj u v) (w : ElementaryWallVertex c r) :
    A.center w ∉ A.edgeGap u v := by
  intro hw
  have he := (A.edgeGap_arm_endpoint huv w 0 hw (A.center_mem_arm w 0)).2
  exact A.arm_target_ne_center w 0 he.symm

theorem gap_disjoint_other_arm {e : OrientedEdge (elementaryWall c r)}
    {u v : ElementaryWallVertex c r} (huv : (elementaryWall c r).Adj u v)
    (hne : s(u, v) ≠ s(e.lo, e.hi)) :
    Disjoint (A.edgeGap e.lo e.hi) (A.arm u (brickWallPort u.val v.val)).vertexSet := by
  apply Finset.disjoint_left.mpr
  intro x hx hxa
  obtain ⟨hh, _⟩ := A.edgeGap_arm_endpoint e.adj u (brickWallPort u.val v.val) hx hxa
  apply hne
  rcases hh with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
  · have hv : v = e.hi := Subtype.ext (brickWallPort_injective_on_neighbors e.lo.val huv e.adj hp)
    rw [hv]
  · have hv : v = e.lo := Subtype.ext (brickWallPort_injective_on_neighbors e.hi.val huv e.adj.symm hp)
    rw [hv, Sym2.eq_swap]

theorem arms_of_distinct_edges_intersection {u v s t : ElementaryWallVertex c r}
    (huv : (elementaryWall c r).Adj u v) (hst : (elementaryWall c r).Adj s t)
    (hne : s(u, v) ≠ s(s, t)) {x : ElementaryWallVertex C R}
    (hx : x ∈ (A.arm u (brickWallPort u.val v.val)).vertexSet)
    (hx' : x ∈ (A.arm s (brickWallPort s.val t.val)).vertexSet) :
    u = s ∧ x = A.center u := by
  have hus : u = s := by
    by_contra hn
    exact Finset.disjoint_left.mp (A.arms_disjoint_of_ne hn _ _) hx hx'
  subst s
  have hp : brickWallPort u.val v.val ≠ brickWallPort u.val t.val := by
    intro he
    have hv : v = t := Subtype.ext (brickWallPort_injective_on_neighbors u.val huv hst he)
    exact hne (by rw [hv])
  exact ⟨rfl, A.arms_intersection u hp hx hx'⟩

def edgeRegion (e : OrientedEdge (elementaryWall c r)) : Finset (ElementaryWallVertex C R) :=
  (A.arm e.lo (brickWallPort e.lo.val e.hi.val)).vertexSet ∪ A.edgeGap e.lo e.hi ∪
    (A.arm e.hi (brickWallPort e.hi.val e.lo.val)).vertexSet

theorem mem_edgeRegion_cases {e : OrientedEdge (elementaryWall c r)}
    {x : ElementaryWallVertex C R} (hx : x ∈ A.edgeRegion e) :
    x ∈ A.edgeGap e.lo e.hi ∨
      ∃ u v, (elementaryWall c r).Adj u v ∧ s(u, v) = s(e.lo, e.hi) ∧
        x ∈ (A.arm u (brickWallPort u.val v.val)).vertexSet := by
  simp only [edgeRegion, mem_union] at hx
  rcases hx with (hx | hx) | hx
  · exact Or.inr ⟨e.lo, e.hi, e.adj, rfl, hx⟩
  · exact Or.inl hx
  · exact Or.inr ⟨e.hi, e.lo, e.adj.symm, Sym2.eq_swap, hx⟩

theorem edgeRegion_branch {e : OrientedEdge (elementaryWall c r)}
    {w : ElementaryWallVertex c r} (hw : A.center w ∈ A.edgeRegion e) :
    w = e.lo ∨ w = e.hi := by
  rcases A.mem_edgeRegion_cases hw with hw | ⟨u, v, _, he, hw⟩
  · exact (A.center_not_mem_edgeGap e.adj w hw).elim
  · have hwu := A.center_on_arm hw
    rcases Sym2.eq_iff.mp he with he | he
    · exact Or.inl (hwu.trans he.1)
    · exact Or.inr (hwu.trans he.1)

theorem edgeRegion_intersection {e f : OrientedEdge (elementaryWall c r)} (hef : e ≠ f)
    {x : ElementaryWallVertex C R} (hx : x ∈ A.edgeRegion e) (hx' : x ∈ A.edgeRegion f) :
    ∃ w, x = A.center w ∧ (w = e.lo ∨ w = e.hi) ∧ (w = f.lo ∨ w = f.hi) := by
  have hsym : s(e.lo, e.hi) ≠ s(f.lo, f.hi) := fun he => hef (OrientedEdge.eq_of_sym2_eq he)
  rcases A.mem_edgeRegion_cases hx with hx | ⟨u, v, huv, he, hx⟩
  · rcases A.mem_edgeRegion_cases hx' with hx' | ⟨s, t, hst, hf, hx'⟩
    · exact (Finset.disjoint_left.mp (A.edgeGap_disjoint hef) hx hx').elim
    · have hn : s(s, t) ≠ s(e.lo, e.hi) := fun hh => hsym (hh.symm.trans hf)
      exact (Finset.disjoint_left.mp (A.gap_disjoint_other_arm hst hn) hx hx').elim
  · rcases A.mem_edgeRegion_cases hx' with hx' | ⟨s, t, hst, hf, hx'⟩
    · have hn : s(u, v) ≠ s(f.lo, f.hi) := fun hh => hsym (he.symm.trans hh)
      exact (Finset.disjoint_left.mp (A.gap_disjoint_other_arm huv hn) hx' hx).elim
    · have hn : s(u, v) ≠ s(s, t) := fun hh => hsym (he.symm.trans (hh.trans hf))
      obtain ⟨hus, hxu⟩ := A.arms_of_distinct_edges_intersection huv hst hn hx hx'
      refine ⟨u, hxu, ?_, ?_⟩
      · rcases Sym2.eq_iff.mp he with he | he
        · exact Or.inl he.1
        · exact Or.inr he.1
      · rcases Sym2.eq_iff.mp hf with hf | hf
        · exact Or.inl (hus.trans hf.1)
        · exact Or.inr (hus.trans hf.1)

end
end Erdos73.BrickTileArray
