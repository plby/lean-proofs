import ErdosProblems.Erdos1105.PrivateColors

namespace Erdos1105

open SimpleGraph

/-- Replace one representative edge by another edge of the same color. -/
def swapRepresentative {V : Type*} (R : SimpleGraph V) (e d : Sym2 V) : SimpleGraph V :=
  fromEdgeSet ((R.edgeSet \ {e}) ∪ {d})

lemma mem_swapRepresentative {V : Type*} (R : SimpleGraph V) (e : Sym2 V)
    (d : (⊤ : SimpleGraph V).edgeSet) (a : Sym2 V) :
    a ∈ (swapRepresentative R e d.val).edgeSet ↔ (a ∈ R.edgeSet ∧ a ≠ e) ∨ a = d.val := by
  rw [swapRepresentative, edgeSet_fromEdgeSet]
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · exact fun h ↦ h.1
  · rintro (⟨ha, he⟩ | rfl)
    · exact ⟨Or.inl ⟨ha, he⟩, R.not_isDiag_of_mem_edgeSet ha⟩
    · exact ⟨Or.inr rfl, (⊤ : SimpleGraph V).not_isDiag_of_mem_edgeSet d.property⟩

theorem swapRepresentative_rainbow {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet) (e : R.edgeSet)
    (d : (⊤ : SimpleGraph V).edgeSet) (hcol : extendColor c d.val = extendColor c e.val) :
    Set.InjOn (extendColor c) (swapRepresentative R e.val d.val).edgeSet := by
  intro a ha b hb hab
  rw [mem_swapRepresentative R e.val d a] at ha
  rw [mem_swapRepresentative R e.val d b] at hb
  rcases ha with ⟨ha, hane⟩ | rfl <;> rcases hb with ⟨hb, hbne⟩ | rfl
  · exact hR ha hb hab
  · exact (hane (hR ha e.property (hab.trans hcol))).elim
  · exact (hbne (hR hb e.property (hab.symm.trans hcol))).elim
  · rfl

lemma deleteEdges_le_swapRepresentative {V : Type*} (R : SimpleGraph V) (e : Sym2 V)
    (d : (⊤ : SimpleGraph V).edgeSet) : R.deleteEdges {e} ≤ swapRepresentative R e d.val := by
  intro x y hxy
  apply (mem_swapRepresentative R e d s(x, y)).mpr
  exact Or.inl (deleteEdges_adj.mp hxy)

theorem swapRepresentative_owned {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (e : R.edgeSet) (d : (⊤ : SimpleGraph V).edgeSet)
    (hcol : extendColor c d.val = extendColor c e.val) :
    ∀ a : (swapRepresentative R e.val d.val).edgeSet, ∃ w, PrivateAt c w
      (c ⟨a.val, edgeSet_mono (show swapRepresentative R e.val d.val ≤ ⊤ from le_top)
        a.property⟩) := by
  intro ⟨a, ha⟩
  rw [mem_swapRepresentative R e.val d a] at ha
  rcases ha with ⟨ha, _⟩ | rfl
  · exact howned ⟨a, ha⟩
  · have hraw : c d = c ⟨e.val, edgeSet_mono le_top e.property⟩ := by
      apply Option.some.inj
      rw [← extendColor_edge c d,
        ← extendColor_edge c ⟨e.val, edgeSet_mono le_top e.property⟩]
      exact hcol
    simpa only [hraw] using howned e

theorem swapRepresentative_palette {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (e : R.edgeSet) (d : (⊤ : SimpleGraph V).edgeSet)
    (hcol : extendColor c d.val = extendColor c e.val) :
    ∀ i, (∃ v, PrivateAt c v i) →
      ∃ a : (swapRepresentative R e.val d.val).edgeSet, extendColor c a.val = some i := by
  intro i hi
  obtain ⟨⟨a, ha⟩, hca⟩ := hpalette i hi
  by_cases he : a = e.val
  · exact ⟨⟨d.val, (mem_swapRepresentative R e.val d d.val).mpr (Or.inr rfl)⟩,
      hcol.trans (he ▸ hca)⟩
  · exact ⟨⟨a, (mem_swapRepresentative R e.val d a).mpr (Or.inl ⟨ha, he⟩)⟩, hca⟩

end Erdos1105
