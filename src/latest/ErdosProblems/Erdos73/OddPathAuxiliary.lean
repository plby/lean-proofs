import ErdosProblems.Erdos556.MatchingInterface

/-!
# The doubled graph for odd terminal paths

Each nonterminal has two copies, joined by a matching edge. Ordinary
edges preserve the copy layer. Terminals have only their original copy.
-/

namespace Erdos73

open SimpleGraph Finset Erdos556

variable {V : Type*} [DecidableEq V]

abbrev OddPathVertex (A : Finset V) := V ⊕ {v : V // v ∉ A}

namespace OddPathVertex

variable {A : Finset V}

def projection : OddPathVertex A → V
  | Sum.inl v => v
  | Sum.inr v => v.val

def layer : OddPathVertex A → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

def mate : OddPathVertex A → OddPathVertex A
  | Sum.inl v => if h : v ∈ A then Sum.inl v else Sum.inr ⟨v, h⟩
  | Sum.inr v => Sum.inl v.val

@[simp] theorem projection_mate (x : OddPathVertex A) :
    projection (mate x) = projection x := by
  cases x with
  | inl v => simp only [mate]; split <;> rfl
  | inr v => rfl

@[simp] theorem mate_mate (x : OddPathVertex A) : mate (mate x) = x := by
  cases x with
  | inl v =>
    by_cases hv : v ∈ A <;> simp [mate, hv]
  | inr v => simp [mate, v.property]

theorem mate_injective : Function.Injective (@mate V _ A) :=
  Function.LeftInverse.injective mate_mate

@[simp] theorem mate_eq_self_iff (x : OddPathVertex A) :
    mate x = x ↔ projection x ∈ A := by
  cases x with
  | inl v => by_cases hv : v ∈ A <;> simp [mate, projection, hv]
  | inr v => simp [mate, projection, v.property]

omit [DecidableEq V] in
theorem ext {x y : OddPathVertex A}
    (hp : projection x = projection y) (hl : layer x = layer y) : x = y := by
  cases x with
  | inl v =>
    cases y with
    | inl w => exact congrArg Sum.inl hp
    | inr w => exact (Bool.false_ne_true hl).elim
  | inr v =>
    cases y with
    | inl w => exact (Bool.false_ne_true hl.symm).elim
    | inr w => exact congrArg Sum.inr (Subtype.ext hp)

theorem layer_mate (x : OddPathVertex A) (hx : projection x ∉ A) :
    layer (mate x) = !(layer x) := by
  cases x with
  | inl v => simp_all [mate, projection, layer]
  | inr v => rfl

theorem projection_eq_iff {x y : OddPathVertex A} :
    projection x = projection y ↔ x = y ∨ x = mate y := by
  constructor
  · intro hp
    by_cases hl : layer x = layer y
    · exact Or.inl (ext hp hl)
    · cases x with
      | inl v =>
        cases y with
        | inl w => exact (hl rfl).elim
        | inr w => exact Or.inr (congrArg Sum.inl hp)
      | inr v =>
        cases y with
        | inl w =>
          change v.val = w at hp
          subst w
          exact Or.inr (by simp [mate, v.property])
        | inr w => exact (hl rfl).elim
  · rintro (rfl | rfl)
    · rfl
    · exact projection_mate _

omit [DecidableEq V] in
theorem eq_original_of_terminal {x : OddPathVertex A} (hx : projection x ∈ A) :
    x = Sum.inl (projection x) := by
  cases x with
  | inl v => rfl
  | inr v => exact (v.property hx).elim

omit [DecidableEq V] in
theorem exists_projection_layer (v : V) (b : Bool) (hb : b = true → v ∉ A) :
    ∃ x : OddPathVertex A, projection x = v ∧ layer x = b := by
  cases b with
  | false => exact ⟨Sum.inl v, rfl, rfl⟩
  | true => exact ⟨Sum.inr ⟨v, hb rfl⟩, rfl, rfl⟩

end OddPathVertex

open OddPathVertex

def oddPathAuxiliary (G : SimpleGraph V) (A : Finset V) :
    SimpleGraph (OddPathVertex A) where
  Adj x y := (layer x = layer y ∧ G.Adj (projection x) (projection y)) ∨
    (projection x = projection y ∧ layer x ≠ layer y)
  symm := ⟨by
    intro x y h
    rcases h with ⟨hl, he⟩ | ⟨hp, hl⟩
    · exact Or.inl ⟨hl.symm, he.symm⟩
    · exact Or.inr ⟨hp.symm, hl.symm⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h
    · exact h.2.ne rfl
    · exact h.2 rfl⟩

theorem oddPathAuxiliary_adj_mate (G : SimpleGraph V) (A : Finset V)
    (x : OddPathVertex A) (hx : projection x ∉ A) :
    (oddPathAuxiliary G A).Adj x (mate x) := by
  refine Or.inr ⟨(projection_mate x).symm, ?_⟩
  rw [layer_mate x hx]
  cases layer x <;> decide

theorem oddPathAuxiliary_adj_nonmate {G : SimpleGraph V} {A : Finset V}
    {x y : OddPathVertex A} (h : (oddPathAuxiliary G A).Adj x y)
    (hm : x ≠ mate y) :
    layer x = layer y ∧ G.Adj (projection x) (projection y) := by
  rcases h with h | ⟨hp, hl⟩
  · exact h
  · rcases projection_eq_iff.mp hp with he | he
    · exact (hl (congrArg layer he)).elim
    · exact (hm he).elim

theorem oddPathAuxiliary_reflect {G : SimpleGraph V} {A : Finset V}
    {x y : OddPathVertex A} (h : (oddPathAuxiliary G A).Adj x y)
    (hx : projection x ∉ A) (hy : projection y ∉ A) :
    (oddPathAuxiliary G A).Adj (mate x) (mate y) := by
  rcases h with ⟨hl, he⟩ | ⟨hp, hl⟩
  · exact Or.inl ⟨by rw [layer_mate x hx, layer_mate y hy, hl],
      by simpa only [projection_mate] using he⟩
  · refine Or.inr ⟨by simpa only [projection_mate] using hp, ?_⟩
    rw [layer_mate x hx, layer_mate y hy]
    simpa using hl

def oddPathMateEdge {A : Finset V} (v : {v : V // v ∉ A}) :
    Sym2 (OddPathVertex A) := s(Sum.inl v.val, Sum.inr v)

omit [DecidableEq V] in
theorem oddPathMateEdge_injective {A : Finset V} :
    Function.Injective (@oddPathMateEdge V A) := by
  intro u v h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Sum.inr.inj h.2
  · have hbad := h.1
    cases hbad

variable [Fintype V]

def oddPathBaseMatching (A : Finset V) : Finset (Sym2 (OddPathVertex A)) :=
  Finset.univ.image oddPathMateEdge

theorem oddPathBaseMatching_card (A : Finset V) :
    (oddPathBaseMatching A).card = Fintype.card {v : V // v ∉ A} := by
  rw [oddPathBaseMatching, Finset.card_image_of_injective _ oddPathMateEdge_injective,
    Finset.card_univ]

theorem mem_oddPathBaseMatching_iff {A : Finset V} (x y : OddPathVertex A) :
    s(x, y) ∈ oddPathBaseMatching A ↔ y = mate x ∧ projection x ∉ A := by
  constructor
  · intro he
    obtain ⟨v, _, he⟩ := Finset.mem_image.mp he
    rcases Sym2.eq_iff.mp he with h | h
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp [mate, v.property], v.property⟩
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, v.property⟩
  · rintro ⟨rfl, hx⟩
    cases x with
    | inl v =>
      change v ∉ A at hx
      exact Finset.mem_image.mpr ⟨⟨v, hx⟩, Finset.mem_univ _, by
        simp [oddPathMateEdge, mate, hx]⟩
    | inr v =>
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, Sym2.eq_swap⟩

theorem oddPathBaseMatching_isMatching (G : SimpleGraph V) (A : Finset V) :
    EdgeMatching (oddPathAuxiliary G A) (oddPathBaseMatching A) := by
  constructor
  · intro e he
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he
    exact Or.inr ⟨rfl, Bool.false_ne_true⟩
  · intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro x hxe hxf
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hxe)
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hxf)
    have hy := (mem_oddPathBaseMatching_iff x y).mp he
    have hz := (mem_oddPathBaseMatching_iff x z).mp hf
    exact hne (congrArg (fun w => s(x, w)) (hy.1.trans hz.1.symm))

theorem mem_oddPathBaseMatching_support (A : Finset V) (x : OddPathVertex A) :
    x ∈ matchingSupport (oddPathBaseMatching A) ↔ projection x ∉ A := by
  constructor
  · intro hx
    obtain ⟨e, he, hxe⟩ := matchingSupport_mem.mp hx
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
    exact ((mem_oddPathBaseMatching_iff x y).mp he).2
  · intro hx
    exact matchingSupport_mem.mpr ⟨s(x, mate x),
      (mem_oddPathBaseMatching_iff x (mate x)).mpr ⟨rfl, hx⟩,
      Sym2.mem_mk_left _ _⟩

theorem oddPathAuxiliary_matching_iff_same_projection {G : SimpleGraph V} {A : Finset V}
    {x y : OddPathVertex A} (hxy : (oddPathAuxiliary G A).Adj x y) :
    s(x, y) ∈ oddPathBaseMatching A ↔ projection x = projection y := by
  constructor
  · intro hm
    have he := (mem_oddPathBaseMatching_iff x y).mp hm
    rw [he.1, projection_mate]
  · intro hp
    rcases projection_eq_iff.mp hp with he | he
    · exact (hxy.ne he).elim
    · have hm : y = mate x := by rw [he, mate_mate]
      have hxt : projection x ∉ A := by
        intro ht
        exact hxy.ne (hm.trans ((mate_eq_self_iff x).mpr ht)).symm
      exact (mem_oddPathBaseMatching_iff x y).mpr ⟨hm, hxt⟩

theorem oddPathAuxiliary_card (A : Finset V) :
    Fintype.card (OddPathVertex A) + A.card = 2 * Fintype.card V := by
  have hcard : Fintype.card {v : V // v ∉ A} + A.card = Fintype.card V := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    exact Nat.sub_add_cancel (Finset.card_le_univ A)
  rw [Fintype.card_sum]
  omega

theorem oddPathBaseMatching_card_add (A : Finset V) :
    (oddPathBaseMatching A).card + A.card = Fintype.card V := by
  rw [oddPathBaseMatching_card]
  rw [Fintype.card_subtype_compl, Fintype.card_coe]
  exact Nat.sub_add_cancel (Finset.card_le_univ A)

end Erdos73
