import ErdosProblems.Erdos73.SubcubicSubdivision

/-! Canonical edge orientations and their injective transport along graph copies. -/

namespace Erdos73.OrientedEdge
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph

variable {U W : Type*} [Fintype U] [LinearOrder U] [Fintype W] [LinearOrder W]
variable {F : SimpleGraph U} {H : SimpleGraph W}

def ofAdj {u v : U} (h : F.Adj u v) : OrientedEdge F := by
  refine ⟨(min u v, max u v), ?_, ?_⟩
  · rcases lt_or_gt_of_ne h.ne with huv | hvu
    · simpa only [min_eq_left huv.le, max_eq_right huv.le] using huv
    · simpa only [min_eq_right hvu.le, max_eq_left hvu.le] using hvu
  · rcases le_total u v with huv | hvu
    · simpa only [min_eq_left huv, max_eq_right huv] using h
    · simpa only [min_eq_right hvu, max_eq_left hvu] using h.symm

theorem ofAdj_endpoints {u v : U} (h : F.Adj u v) :
    ((ofAdj h).lo = u ∧ (ofAdj h).hi = v) ∨
      ((ofAdj h).lo = v ∧ (ofAdj h).hi = u) := by
  rcases le_total u v with hh | hh
  · exact Or.inl ⟨min_eq_left hh, max_eq_right hh⟩
  · exact Or.inr ⟨min_eq_right hh, max_eq_left hh⟩

theorem ofAdj_sym2 {u v : U} (h : F.Adj u v) :
    s((ofAdj h).lo, (ofAdj h).hi) = s(u, v) := by
  rcases ofAdj_endpoints h with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, Sym2.eq_swap]

theorem eq_of_sym2_eq {e f : OrientedEdge F} (he : s(e.lo, e.hi) = s(f.lo, f.hi)) : e = f := by
  rcases Sym2.eq_iff.mp he with he | he
  · exact Subtype.ext (Prod.ext he.1 he.2)
  · have h1 := e.lo_lt_hi
    have h2 := f.lo_lt_hi
    rw [he.1, he.2] at h1
    exact (lt_asymm h1 h2).elim

def mapCopy (f : F.Copy H) (e : OrientedEdge F) : OrientedEdge H := ofAdj (f.toHom.map_adj e.adj)

theorem mapCopy_endpoints (f : F.Copy H) (e : OrientedEdge F) :
    ((mapCopy f e).lo = f e.lo ∧ (mapCopy f e).hi = f e.hi) ∨
      ((mapCopy f e).lo = f e.hi ∧ (mapCopy f e).hi = f e.lo) :=
  ofAdj_endpoints _

theorem mapCopy_sym2 (f : F.Copy H) (e : OrientedEdge F) :
    s((mapCopy f e).lo, (mapCopy f e).hi) = s(f e.lo, f e.hi) := ofAdj_sym2 _

theorem mapCopy_endpoint_iff (f : F.Copy H) (e : OrientedEdge F) (w : W) :
    (w = (mapCopy f e).lo ∨ w = (mapCopy f e).hi) ↔ (w = f e.lo ∨ w = f e.hi) := by
  rcases mapCopy_endpoints f e with hh | hh
  · rw [hh.1, hh.2]
  · rw [hh.1, hh.2, or_comm]

theorem mapCopy_injective (f : F.Copy H) : Function.Injective (mapCopy f) := by
  intro e d he
  have hh := congrArg (fun a : OrientedEdge H => s(a.lo, a.hi)) he
  rw [mapCopy_sym2, mapCopy_sym2] at hh
  apply eq_of_sym2_eq
  apply Sym2.eq_iff.mpr
  rcases Sym2.eq_iff.mp hh with hh | hh
  · exact Or.inl ⟨f.injective hh.1, f.injective hh.2⟩
  · exact Or.inr ⟨f.injective hh.1, f.injective hh.2⟩

end
end Erdos73.OrientedEdge
