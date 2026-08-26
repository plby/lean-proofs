import ErdosProblems.Erdos19.Core

/-! # Combining compatible colorings in one palette -/

namespace Erdos19.SetHypergraph

variable {V P : Type*}

noncomputable def unionColoring (L M : SetHypergraph V)
    (cL : L.EdgeColoring P) (cM : M.EdgeColoring P)
    (hcross : ∀ e : L, ∀ f : M, (e.1 ∩ f.1).Nonempty → cL.color e ≠ cM.color f) :
    (L ∪ M).EdgeColoring P := by
  classical
  let c : ↥(L ∪ M) → P := fun e ↦
    if he : e.1 ∈ L then cL ⟨e.1, he⟩ else cM ⟨e.1, e.2.resolve_left he⟩
  refine ⟨c, ?_⟩
  intro e f hef hinter hsame
  by_cases he : e.1 ∈ L
  · by_cases hf : f.1 ∈ L
    · have hne : (⟨e.1, he⟩ : L) ≠ ⟨f.1, hf⟩ :=
        fun h ↦ hef (Subtype.ext (congrArg (fun z : L ↦ z.1) h))
      exact cL.valid hne hinter (by simpa [c, he, hf] using hsame)
    · exact hcross ⟨e.1, he⟩ ⟨f.1, f.2.resolve_left hf⟩ hinter
        (by simpa [c, he, hf] using hsame)
  · by_cases hf : f.1 ∈ L
    · have hinter' : (f.1 ∩ e.1).Nonempty := by simpa only [Set.inter_comm] using hinter
      exact hcross ⟨f.1, hf⟩ ⟨e.1, e.2.resolve_left he⟩ hinter'
        (by simpa [c, he, hf] using hsame.symm)
    · have hne : (⟨e.1, e.2.resolve_left he⟩ : M) ≠ ⟨f.1, f.2.resolve_left hf⟩ :=
        fun h ↦ hef (Subtype.ext (congrArg (fun z : M ↦ z.1) h))
      exact cM.valid hne hinter (by simpa [c, he, hf] using hsame)

@[simp] theorem unionColoring_left (L M : SetHypergraph V)
    (cL : L.EdgeColoring P) (cM : M.EdgeColoring P)
    (hcross : ∀ e : L, ∀ f : M, (e.1 ∩ f.1).Nonempty → cL.color e ≠ cM.color f)
    (e : L) : (L.unionColoring M cL cM hcross).color ⟨e.1, Or.inl e.2⟩ = cL.color e := by
  simp only [unionColoring, dif_pos e.2]

theorem unionColoring_right (L M : SetHypergraph V)
    (cL : L.EdgeColoring P) (cM : M.EdgeColoring P)
    (hcross : ∀ e : L, ∀ f : M, (e.1 ∩ f.1).Nonempty → cL.color e ≠ cM.color f)
    (e : M) (he : e.1 ∉ L) :
    (L.unionColoring M cL cM hcross).color ⟨e.1, Or.inr e.2⟩ = cM.color e := by
  simp only [unionColoring, dif_neg he]

theorem unionColoring_covered_subset (L M : SetHypergraph V)
    (cL : L.EdgeColoring P) (cM : M.EdgeColoring P)
    (hcross : ∀ e : L, ∀ f : M, (e.1 ∩ f.1).Nonempty → cL.color e ≠ cM.color f)
    (a : P) :
    (L ∪ M).coveredVertices {e | (L.unionColoring M cL cM hcross).color e = a} ⊆
      L.coveredVertices {e | cL.color e = a} ∪ M.coveredVertices {e | cM.color e = a} := by
  intro v hv
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
  obtain ⟨hcolor, hve⟩ := Set.mem_iUnion.mp he
  by_cases heL : e.1 ∈ L
  · left
    apply Set.mem_iUnion.mpr ⟨⟨e.1, heL⟩, ?_⟩
    apply Set.mem_iUnion.mpr ⟨?_, hve⟩
    simpa only [Set.mem_ofPred_eq, unionColoring, dif_pos heL] using hcolor
  · right
    apply Set.mem_iUnion.mpr ⟨⟨e.1, e.2.resolve_left heL⟩, ?_⟩
    apply Set.mem_iUnion.mpr ⟨?_, hve⟩
    simpa only [Set.mem_ofPred_eq, unionColoring, dif_neg heL] using hcolor

theorem unionColoring_covered_card_le [Fintype V] (L M : SetHypergraph V)
    (cL : L.EdgeColoring P) (cM : M.EdgeColoring P)
    (hcross : ∀ e : L, ∀ f : M, (e.1 ∩ f.1).Nonempty → cL.color e ≠ cM.color f)
    (a : P) :
    ((L ∪ M).coveredVertices {e | (L.unionColoring M cL cM hcross).color e = a}).ncard ≤
      (L.coveredVertices {e | cL.color e = a}).ncard +
        (M.coveredVertices {e | cM.color e = a}).ncard :=
  (Set.ncard_le_ncard (L.unionColoring_covered_subset M cL cM hcross a)).trans
    (Set.ncard_union_le _ _)

theorem unionColoring_fiber_card_le_left [Fintype V] (L M : SetHypergraph V)
    (cL : L.EdgeColoring P) (cM : M.EdgeColoring P)
    (hcross : ∀ e : L, ∀ f : M, (e.1 ∩ f.1).Nonempty → cL.color e ≠ cM.color f)
    (a : P) (hnotM : ∀ f : M, cM.color f ≠ a) :
    ({e : ↥(L ∪ M) | (L.unionColoring M cL cM hcross).color e = a} : Set ↥(L ∪ M)).ncard ≤
      ({e : L | cL.color e = a} : Set L).ncard := by
  classical
  let F : Set ↥(L ∪ M) := {e | (L.unionColoring M cL cM hcross).color e = a}
  have hleft (e : F) : e.1.1 ∈ L := by
    by_contra he
    apply hnotM ⟨e.1.1, e.1.2.resolve_left he⟩
    simpa only [F, Set.mem_ofPred_eq, unionColoring, dif_neg he] using e.2
  let code : F → {e : L // cL.color e = a} := fun e ↦
    ⟨⟨e.1.1, hleft e⟩, by simpa only [F, Set.mem_ofPred_eq, unionColoring, dif_pos (hleft e)] using e.2⟩
  have hinj : Function.Injective code := by
    intro e f hef
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : {e : L // cL.color e = a} ↦ x.1.1) hef
  have hcard := Fintype.card_le_of_injective code hinj
  simp only [← Nat.card_eq_fintype_card] at hcard
  change Nat.card F ≤ Nat.card ({e : L | cL.color e = a} : Set L) at hcard
  simpa only [Nat.card_coe_set_eq, F] using hcard

theorem unionColoring_coverBounded_left [Fintype V] (L M : SetHypergraph V)
    (cL : L.EdgeColoring P) (cM : M.EdgeColoring P)
    (hcross : ∀ e : L, ∀ f : M, (e.1 ∩ f.1).Nonempty → cL.color e ≠ cM.color f)
    (a : P) (A : ℕ) (hnotM : ∀ f : M, cM.color f ≠ a)
    (hL : ({e : L | cL.color e = a} : Set L).ncard ≤ 1 ∨
      (L.coveredVertices {e | cL.color e = a}).ncard ≤ A) :
    ({e : ↥(L ∪ M) | (L.unionColoring M cL cM hcross).color e = a} : Set ↥(L ∪ M)).ncard ≤ 1 ∨
      ((L ∪ M).coveredVertices {e | (L.unionColoring M cL cM hcross).color e = a}).ncard ≤ A := by
  rcases hL with hsmall | hcover
  · exact Or.inl ((L.unionColoring_fiber_card_le_left M cL cM hcross a hnotM).trans hsmall)
  · right
    have hMempty : M.coveredVertices {e | cM.color e = a} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
      obtain ⟨heq, _⟩ := Set.mem_iUnion.mp he
      exact hnotM e heq
    have h := L.unionColoring_covered_card_le M cL cM hcross a
    rw [hMempty, Set.ncard_empty, Nat.add_zero] at h
    exact h.trans hcover

#print axioms unionColoring_coverBounded_left

end Erdos19.SetHypergraph
