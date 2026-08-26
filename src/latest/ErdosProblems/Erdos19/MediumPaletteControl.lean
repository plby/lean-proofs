import ErdosProblems.Erdos19.Core

/-! # The edge-size partition and its required medium-palette controls -/

namespace Erdos19.SetHypergraph

variable {V P : Type*}

def rankAtLeast (H : SetHypergraph V) (R : ℕ) : SetHypergraph V :=
  {e | e ∈ H ∧ R ≤ e.ncard}

def rankBelow (H : SetHypergraph V) (R : ℕ) : SetHypergraph V :=
  {e | e ∈ H ∧ e.ncard < R}

theorem rankAtLeast_union_rankBelow (H : SetHypergraph V) (R : ℕ) :
    H.rankAtLeast R ∪ H.rankBelow R = H := by
  ext e
  change (e ∈ H ∧ R ≤ e.ncard) ∨ (e ∈ H ∧ e.ncard < R) ↔ e ∈ H
  constructor
  · rintro (h | h) <;> exact h.1
  · intro he
    by_cases hR : R ≤ e.ncard
    · exact Or.inl ⟨he, hR⟩
    · exact Or.inr ⟨he, Nat.lt_of_not_ge hR⟩

theorem rankAtLeast_linear (H : SetHypergraph V) (hlinear : H.IsLinear) (R : ℕ) :
    (H.rankAtLeast R).IsLinear :=
  fun {_e} he {_f} hf hne ↦ hlinear he.1 hf.1 hne

theorem rankBelow_linear (H : SetHypergraph V) (hlinear : H.IsLinear) (R : ℕ) :
    (H.rankBelow R).IsLinear :=
  fun {_e} he {_f} hf hne ↦ hlinear he.1 hf.1 hne

def rankAtLeastEmbedding (H : SetHypergraph V) (R : ℕ) : H.rankAtLeast R ↪ H where
  toFun e := ⟨e.1, e.2.1⟩
  inj' := fun _ _ h ↦ Subtype.ext (congrArg (fun x : H ↦ x.1) h)

/-- The palette contains all edges below `R`. Its classes cover at most `B`
vertices; every other class is a singleton or covers at most `A` vertices. -/
def HasControlledMediumPalette (H : SetHypergraph V) (color : H.EdgeColoring P)
    (palette : Finset P) (R A B : ℕ) : Prop :=
  (∀ e : H, e.1.ncard < R → color.color e ∈ palette) ∧
  (∀ a ∈ palette, (H.coveredVertices {e | color.color e = a}).ncard ≤ B) ∧
  (∀ a, a ∉ palette → ({e : H | color.color e = a} : Set H).ncard ≤ 1 ∨
    (H.coveredVertices {e | color.color e = a}).ncard ≤ A)

def EdgeColoring.transport {H J : SetHypergraph V} (color : H.EdgeColoring P)
    (h : H = J) : J.EdgeColoring P := h ▸ color

theorem EdgeColoring.transport_apply {H J : SetHypergraph V} (color : H.EdgeColoring P)
    (h : H = J) (e : J) :
    (color.transport h).color e = color.color ⟨e.1, h.symm ▸ e.2⟩ := by
  cases h
  rfl

theorem EdgeColoring.transport_fiber_ncard {H J : SetHypergraph V} (color : H.EdgeColoring P)
    (h : H = J) (a : P) :
    ({e : J | (color.transport h).color e = a} : Set J).ncard =
      ({e : H | color.color e = a} : Set H).ncard := by
  cases h
  rfl

theorem EdgeColoring.transport_covered {H J : SetHypergraph V} (color : H.EdgeColoring P)
    (h : H = J) (a : P) :
    J.coveredVertices {e | (color.transport h).color e = a} =
      H.coveredVertices {e | color.color e = a} := by
  cases h
  rfl

theorem controlled_medium_palette_of_partition (H : SetHypergraph V) (R A B : ℕ)
    (palette : Finset P)
    (h : ∃ c : (H.rankAtLeast R ∪ H.rankBelow R).EdgeColoring P,
      (∀ e : H.rankBelow R, e.1 ∉ H.rankAtLeast R →
        c.color ⟨e.1, Or.inr e.2⟩ ∈ palette) ∧
      (∀ a ∈ palette,
        ((H.rankAtLeast R ∪ H.rankBelow R).coveredVertices {e | c.color e = a}).ncard ≤ B) ∧
      (∀ a, a ∉ palette →
        ({e : ↥(H.rankAtLeast R ∪ H.rankBelow R) | c.color e = a} :
          Set ↥(H.rankAtLeast R ∪ H.rankBelow R)).ncard ≤ 1 ∨
        ((H.rankAtLeast R ∪ H.rankBelow R).coveredVertices {e | c.color e = a}).ncard ≤ A)) :
    ∃ c : H.EdgeColoring P, H.HasControlledMediumPalette c palette R A B := by
  obtain ⟨c, hmedium, hcover, hrest⟩ := h
  let hEq := H.rankAtLeast_union_rankBelow R
  refine ⟨c.transport hEq, ?_, ?_, ?_⟩
  · intro e he
    have heM : e.1 ∈ H.rankBelow R := ⟨e.2, he⟩
    have heL : e.1 ∉ H.rankAtLeast R := fun h ↦ (Nat.not_le_of_gt he) h.2
    rw [c.transport_apply hEq e]
    exact hmedium ⟨e.1, heM⟩ heL
  · intro a ha
    simpa only [EdgeColoring.transport_covered] using hcover a ha
  · intro a ha
    simpa only [EdgeColoring.transport_fiber_ncard, EdgeColoring.transport_covered] using hrest a ha

#print axioms controlled_medium_palette_of_partition

end Erdos19.SetHypergraph
