import ErdosProblems.Erdos1105.Representatives

namespace Erdos1105

open SimpleGraph

def adjoinRepresentative {V : Type*} (R : SimpleGraph V)
    (d : (⊤ : SimpleGraph V).edgeSet) : SimpleGraph V := fromEdgeSet (R.edgeSet ∪ {d.val})

lemma mem_adjoinRepresentative {V : Type*} (R : SimpleGraph V)
    (d : (⊤ : SimpleGraph V).edgeSet) (e : Sym2 V) :
    e ∈ (adjoinRepresentative R d).edgeSet ↔ e ∈ R.edgeSet ∨ e = d.val := by
  rw [adjoinRepresentative, edgeSet_fromEdgeSet]
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · exact fun h ↦ h.1
  · rintro (he | rfl)
    · exact ⟨Or.inl he, R.not_isDiag_of_mem_edgeSet he⟩
    · exact ⟨Or.inr rfl, (⊤ : SimpleGraph V).not_isDiag_of_mem_edgeSet d.property⟩

lemma le_adjoinRepresentative {V : Type*} (R : SimpleGraph V)
    (d : (⊤ : SimpleGraph V).edgeSet) : R ≤ adjoinRepresentative R d :=
  fun x y h ↦ (mem_adjoinRepresentative R d s(x, y)).mpr (Or.inl h)

lemma added_mem_adjoinRepresentative {V : Type*} (R : SimpleGraph V)
    (d : (⊤ : SimpleGraph V).edgeSet) : d.val ∈ (adjoinRepresentative R d).edgeSet :=
  (mem_adjoinRepresentative R d _).mpr (Or.inr rfl)

theorem adjoinRepresentative_rainbow {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet) (d : (⊤ : SimpleGraph V).edgeSet)
    (hnew : ∀ e ∈ R.edgeSet, extendColor c d.val ≠ extendColor c e) :
    Set.InjOn (extendColor c) (adjoinRepresentative R d).edgeSet := by
  intro e he f hf hcol
  rw [mem_adjoinRepresentative] at he hf
  rcases he with he | rfl <;> rcases hf with hf | rfl
  · exact hR he hf hcol
  · exact (hnew e he hcol.symm).elim
  · exact (hnew f hf hcol).elim
  · rfl

end Erdos1105
