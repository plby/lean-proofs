import ErdosProblems.Erdos19.CoreCoverColoring

/-! # Transporting individual color classes out of an edge restriction -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem exists_partial_coloring_with_class_control (H : SetHypergraph V)
    (S : Finset H) (n : ℕ) (hn : 0 < n)
    (color : (H.restrictEdges (S : Set H)).EdgeColoring (Fin n)) :
    ∃ c : H → Fin n, H.IsProperOn S c ∧
      (∀ a, ({e : H | e ∈ S ∧ c e = a} : Set H).ncard ≤
        ({f : H.restrictEdges (S : Set H) | color f = a} :
          Set (H.restrictEdges (S : Set H))).ncard) ∧
      (∀ a, H.coveredVertices {e : H | e ∈ S ∧ c e = a} ⊆
        (H.restrictEdges (S : Set H)).coveredVertices {f | color f = a}) := by
  classical
  let J := H.restrictEdges (S : Set H)
  let E := H.restrictEdgesEquiv (S : Set H)
  let c : H → Fin n := fun e ↦ if he : e ∈ S then color (E ⟨e, he⟩) else ⟨0, hn⟩
  have hc (e : H) (he : e ∈ S) : c e = color (E ⟨e, he⟩) := by simp [c, he]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro e he f hf hef hinter
    rw [hc e he, hc f hf]
    apply color.valid
    · intro h
      exact hef (congrArg Subtype.val (E.injective h))
    · simpa only [E, restrictEdgesEquiv_val] using hinter
  · intro a
    let code : {e : H // e ∈ S ∧ c e = a} → {f : J // color f = a} :=
      fun e ↦ ⟨E ⟨e.1, e.2.1⟩, (hc e.1 e.2.1).symm.trans e.2.2⟩
    have hinj : Function.Injective code := by
      intro e f hef
      apply Subtype.ext
      have hh : (⟨e.1, e.2.1⟩ : (S : Set H)) = ⟨f.1, f.2.1⟩ :=
        E.injective (congrArg Subtype.val hef)
      exact congrArg (fun x : (S : Set H) ↦ x.1) hh
    have hcard := Fintype.card_le_of_injective code hinj
    simp only [← Nat.card_eq_fintype_card] at hcard
    change Nat.card ({e : H | e ∈ S ∧ c e = a} : Set H) ≤
      Nat.card ({f : J | color f = a} : Set J) at hcard
    simpa only [Nat.card_coe_set_eq] using hcard
  · intro a v hv
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
    obtain ⟨heS, hve⟩ := Set.mem_iUnion.mp he
    apply Set.mem_iUnion.mpr ⟨E ⟨e, heS.1⟩, ?_⟩
    apply Set.mem_iUnion.mpr ⟨(hc e heS.1).symm.trans heS.2, ?_⟩
    simpa only [E, restrictEdgesEquiv_val] using hve

#print axioms exists_partial_coloring_with_class_control

end Erdos19.SetHypergraph
