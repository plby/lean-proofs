import ErdosProblems.Erdos73.ForestEdgeCounts

/-! In a once-subdivided tree, the original vertices form the unique maximum independent set. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset

variable {W : Type*} [Fintype W] [LinearOrder W]

def treeIncidenceGraph (T : SimpleGraph W) : SimpleGraph (W ⊕ OrientedEdge T) where
  Adj x y := match x, y with
    | Sum.inl v, Sum.inr e => v = e.lo ∨ v = e.hi
    | Sum.inr e, Sum.inl v => v = e.lo ∨ v = e.hi
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x; cases x <;> exact not_false⟩

def incidenceOriginalPart {T : SimpleGraph W} (I : Finset (W ⊕ OrientedEdge T)) : Finset W :=
  univ.filter (fun v => Sum.inl v ∈ I)

def incidenceEdgePart {T : SimpleGraph W} (I : Finset (W ⊕ OrientedEdge T)) :
    Finset (OrientedEdge T) := univ.filter (fun e => Sum.inr e ∈ I)

theorem incidence_card_eq {T : SimpleGraph W} (I : Finset (W ⊕ OrientedEdge T)) :
    I.card = (incidenceOriginalPart I).card + (incidenceEdgePart I).card := by
  have hh : I.card = ∑ z : W ⊕ OrientedEdge T, if z ∈ I then (1 : ℕ) else 0 := by simp
  rw [hh, Fintype.sum_sum_type]
  simp only [incidenceOriginalPart, incidenceEdgePart, card_filter]

theorem incidenceEdge_endpoints_omitted {T : SimpleGraph W} {I : Finset (W ⊕ OrientedEdge T)}
    (hI : (treeIncidenceGraph T).IsIndepSet (I : Set _)) {e : OrientedEdge T}
    (he : e ∈ incidenceEdgePart I) : e.lo ∉ incidenceOriginalPart I ∧ e.hi ∉ incidenceOriginalPart I := by
  have heI : Sum.inr e ∈ I := (mem_filter.mp he).2
  constructor
  · intro hv
    exact hI (mem_filter.mp hv).2 heI (by simp) (Or.inl rfl)
  · intro hv
    exact hI (mem_filter.mp hv).2 heI (by simp) (Or.inr rfl)

def incidenceSelectedEdgeMap {T : SimpleGraph W} {I : Finset (W ⊕ OrientedEdge T)}
    (hI : (treeIncidenceGraph T).IsIndepSet (I : Set _)) :
    (incidenceEdgePart I) → OrientedEdge (T.induce (↑(incidenceOriginalPart I)ᶜ : Set W)) :=
  fun e => ⟨(⟨e.val.lo, mem_compl.mpr (incidenceEdge_endpoints_omitted hI e.property).1⟩,
    ⟨e.val.hi, mem_compl.mpr (incidenceEdge_endpoints_omitted hI e.property).2⟩),
    e.val.lo_lt_hi, e.val.adj⟩

theorem incidenceSelectedEdgeMap_injective {T : SimpleGraph W} {I : Finset (W ⊕ OrientedEdge T)}
    (hI : (treeIncidenceGraph T).IsIndepSet (I : Set _)) :
    Function.Injective (incidenceSelectedEdgeMap hI) := by
  intro e f he
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun z => z.lo.val) he) (congrArg (fun z => z.hi.val) he)

theorem incidenceEdge_card_lt_complement {T : SimpleGraph W} (hT : T.IsAcyclic)
    {I : Finset (W ⊕ OrientedEdge T)} (hI : (treeIncidenceGraph T).IsIndepSet (I : Set _))
    (hJ : (incidenceEdgePart I).Nonempty) :
    (incidenceEdgePart I).card < ((incidenceOriginalPart I)ᶜ).card := by
  obtain ⟨e, he⟩ := hJ
  letI : Nonempty (↑((incidenceOriginalPart I)ᶜ : Finset W) : Set W) :=
    ⟨⟨e.lo, mem_compl.mpr (incidenceEdge_endpoints_omitted hI he).1⟩⟩
  have hle := Fintype.card_le_of_injective _ (incidenceSelectedEdgeMap_injective hI)
  have hlt := acyclic_card_orientedEdge_lt
    (T.induce (↑((incidenceOriginalPart I)ᶜ) : Set W)) (hT.induce _)
  have hh := hle.trans_lt hlt
  simpa only [Finset.coe_compl, Fintype.card_compl_set, Finset.coe_sort_coe, Fintype.card_coe,
    Finset.card_compl] using hh

theorem treeIncidence_isIndepSet_card_le {T : SimpleGraph W} (hT : T.IsTree)
    {I : Finset (W ⊕ OrientedEdge T)} (hI : (treeIncidenceGraph T).IsIndepSet (I : Set _)) :
    I.card ≤ Fintype.card (OrientedEdge T) + if ∀ v, Sum.inl v ∈ I then 1 else 0 := by
  have he := tree_card_orientedEdge_add_one T hT
  have hi := incidence_card_eq I
  have hA := card_le_card (subset_univ (incidenceOriginalPart I))
  rw [card_univ] at hA
  by_cases hJ : (incidenceEdgePart I).Nonempty
  · have hj := incidenceEdge_card_lt_complement hT.isAcyclic hI hJ
    rw [card_compl] at hj
    split_ifs <;> omega
  · have hj : (incidenceEdgePart I).card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hJ)
    by_cases hall : ∀ v, Sum.inl v ∈ I
    · rw [if_pos hall]
      omega
    · rw [if_neg hall]
      have hlt : (incidenceOriginalPart I).card < Fintype.card W := by
        by_contra hn
        have hEq : incidenceOriginalPart I = univ :=
          eq_of_subset_of_card_le (subset_univ _) (by simpa only [card_univ] using (not_lt.mp hn))
        apply hall
        intro v
        have hv : v ∈ incidenceOriginalPart I := hEq ▸ mem_univ v
        exact (mem_filter.mp hv).2
      omega

end
end Erdos73
