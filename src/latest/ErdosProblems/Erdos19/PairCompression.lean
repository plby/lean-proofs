import ErdosProblems.Erdos19.Core

/-!
# Pair-compression certificates

These certificates retain the disjoint pairs used in a coloring proof, rather
than only the existence of a coloring. They will supply bounds on color classes.
-/

namespace Erdos19.SetHypergraph

variable {X : Type*} [Fintype X]

/-- A family can be assigned at most `k` labels by identifying disjoint pairs
with distinct endpoints and leaving all other edges alone. -/
def PairCompressible (H : SetHypergraph X) (k : ℕ) : Prop :=
  ∃ t : ℕ, ∃ left right : Fin t → H,
    Function.Injective (Sum.elim left right) ∧
    (∀ i, Disjoint (left i).1 (right i).1) ∧
    Fintype.card H ≤ k + t

theorem pairCompressible_of_card_le (H : SetHypergraph X) {k : ℕ}
    (hcard : Fintype.card H ≤ k) : H.PairCompressible k := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, by simpa using hcard⟩
  · intro a
    exact isEmptyElim a
  · intro i
    exact Fin.elim0 i

theorem pairCompressible_of_disjoint_pairs (H : SetHypergraph X) {t k : ℕ}
    (left right : Fin t → H)
    (hinj : Function.Injective (Sum.elim left right))
    (hpairs : ∀ i, Disjoint (left i).1 (right i).1)
    (hcard : Fintype.card H ≤ k + t) : H.PairCompressible k :=
  ⟨t, left, right, hinj, hpairs, hcard⟩

theorem pairCompressible_of_disjointnessMatching (H : SetHypergraph X)
    (M : H.disjointnessGraph.Subgraph) (hM : M.IsMatching) {k : ℕ}
    (hcard : Fintype.card H ≤ k + M.edgeSet.ncard) :
    H.PairCompressible k := by
  obtain ⟨left, right, hinj, hpairs⟩ :=
    exists_injective_endpoints_of_matching M hM (Nat.le_refl M.edgeSet.ncard)
  exact ⟨M.edgeSet.ncard, left, right, hinj, fun i ↦ (hpairs i).2, hcard⟩

theorem PairCompressible.edgeColorable {H : SetHypergraph X} {k : ℕ}
    (h : H.PairCompressible k) : H.EdgeColorable k := by
  obtain ⟨t, left, right, hinj, hpairs, hcard⟩ := h
  exact H.edgeColorable_of_disjoint_pairs left right hinj hpairs hcard

/-- Embedding a finite palette preserves a bound on the number of edges in
each color class. -/
theorem exists_bounded_fiber_coloring_of_compression (H : SetHypergraph X)
    {C : Type*} [Fintype C] {k b : ℕ} (label : H → C)
    (hlabel : ∀ ⦃e f : H⦄, e ≠ f → label e = label f → Disjoint e.1 f.1)
    (hcard : Fintype.card C ≤ k)
    (hfiber : ∀ c, ({e : H | label e = c} : Set H).ncard ≤ b) :
    ∃ color : H.EdgeColoring (Fin k),
      ∀ c, ({e : H | color.color e = c} : Set H).ncard ≤ b := by
  classical
  have hcard' : Fintype.card C ≤ Fintype.card (Fin k) := by simpa using hcard
  obtain ⟨embedding : C ↪ Fin k⟩ :=
    Function.Embedding.nonempty_of_card_le hcard'
  let color : H.EdgeColoring (Fin k) :=
    { color := fun e ↦ embedding (label e)
      valid := by
        intro e f hef hinter hsame
        have hd := hlabel hef (embedding.injective hsame)
        obtain ⟨x, hxe, hxf⟩ := hinter
        exact Set.disjoint_left.mp hd hxe hxf }
  refine ⟨color, fun c ↦ ?_⟩
  by_cases hc : ({e : H | color.color e = c} : Set H).Nonempty
  · obtain ⟨e, he⟩ := hc
    apply (Set.ncard_le_ncard (t := {f : H | label f = label e}) ?_).trans
      (hfiber (label e))
    intro f hf
    exact embedding.injective (hf.trans he.symm)
  · rw [Set.not_nonempty_iff_eq_empty.mp hc, Set.ncard_empty]
    exact Nat.zero_le _


theorem exists_pair_bounded_coloring_of_disjoint_pairs (H : SetHypergraph X)
    {t k : ℕ} (left right : Fin t → H)
    (hendpoints : Function.Injective (Sum.elim left right))
    (hpairs : ∀ i, Disjoint (left i).1 (right i).1)
    (hcard : Fintype.card H ≤ k + t) :
    ∃ color : H.EdgeColoring (Fin k),
      ∀ c, ({e : H | color.color e = c} : Set H).ncard ≤ 2 := by
  classical
  let endpoint : Fin t ⊕ Fin t → H := Sum.elim left right
  have endpoint_injective : Function.Injective endpoint := hendpoints
  let rangeEquiv : (Fin t ⊕ Fin t) ≃ Set.range endpoint :=
    Equiv.ofInjective endpoint endpoint_injective
  let pairIndex : Fin t ⊕ Fin t → Fin t := Sum.elim id id
  let Label := Fin t ⊕ {e : H // e ∉ Set.range endpoint}
  let label : H → Label := fun e ↦
    if he : e ∈ Set.range endpoint then
      Sum.inl (pairIndex (rangeEquiv.symm ⟨e, he⟩))
    else Sum.inr ⟨e, he⟩
  have hlabel : ∀ ⦃e f : H⦄, e ≠ f → label e = label f → Disjoint e.1 f.1 := by
    intro e f hef hsame
    by_cases he : e ∈ Set.range endpoint
    · by_cases hf : f ∈ Set.range endpoint
      · simp only [label, dif_pos he, dif_pos hf] at hsame
        have hindex :
            pairIndex (rangeEquiv.symm ⟨e, he⟩) =
              pairIndex (rangeEquiv.symm ⟨f, hf⟩) :=
          Sum.inl_injective hsame
        have heq : endpoint (rangeEquiv.symm ⟨e, he⟩) = e := by
          exact congrArg Subtype.val (rangeEquiv.apply_symm_apply ⟨e, he⟩)
        have hfeq : endpoint (rangeEquiv.symm ⟨f, hf⟩) = f := by
          exact congrArg Subtype.val (rangeEquiv.apply_symm_apply ⟨f, hf⟩)
        generalize hse : rangeEquiv.symm ⟨e, he⟩ = se at hindex heq
        generalize hsf : rangeEquiv.symm ⟨f, hf⟩ = sf at hindex hfeq
        rcases se with i | i <;> rcases sf with j | j
        · have hij : i = j := by simpa [pairIndex] using hindex
          exfalso
          apply hef
          rw [← heq, ← hfeq, hij]
        · have hij : i = j := by simpa [pairIndex] using hindex
          subst j
          rw [← heq, ← hfeq]
          exact hpairs i
        · have hij : i = j := by simpa [pairIndex] using hindex
          subst j
          rw [← heq, ← hfeq]
          exact (hpairs i).symm
        · have hij : i = j := by simpa [pairIndex] using hindex
          exfalso
          apply hef
          rw [← heq, ← hfeq, hij]
      · have hcontra :
            (Sum.inl (pairIndex (rangeEquiv.symm ⟨e, he⟩)) : Label) =
              Sum.inr ⟨f, hf⟩ := by
          dsimp only [label] at hsame
          rw [dif_pos he, dif_neg hf] at hsame
          exact hsame
        exact (Sum.inl_ne_inr hcontra).elim
    · by_cases hf : f ∈ Set.range endpoint
      · have hcontra :
            (Sum.inr ⟨e, he⟩ : Label) =
              Sum.inl (pairIndex (rangeEquiv.symm ⟨f, hf⟩)) := by
          dsimp only [label] at hsame
          rw [dif_neg he, dif_pos hf] at hsame
          exact hsame
        exact (Sum.inr_ne_inl hcontra).elim
      · have hunmatched :
            (⟨e, he⟩ : {e : H // e ∉ Set.range endpoint}) = ⟨f, hf⟩ := by
          simp only [label, dif_neg he, dif_neg hf] at hsame
          exact Sum.inr_injective hsame
        exact (hef (congrArg Subtype.val hunmatched)).elim
  have hrange : (Set.range endpoint).ncard = 2 * t := by
    calc
      (Set.range endpoint).ncard = Nat.card (Fin t ⊕ Fin t) :=
        Set.ncard_range_of_injective endpoint_injective
      _ = Fintype.card (Fin t ⊕ Fin t) := Nat.card_eq_fintype_card
      _ = Fintype.card (Fin t) + Fintype.card (Fin t) := Fintype.card_sum
      _ = 2 * t := by simp [two_mul]
  have hrange_le : 2 * t ≤ Fintype.card H := by
    rw [← hrange]
    calc
      (Set.range endpoint).ncard ≤ (Set.univ : Set H).ncard :=
        Set.ncard_le_ncard (Set.range endpoint).subset_univ
      _ = Fintype.card H := by simp
  have hLabel : Fintype.card Label = t + (Fintype.card H - 2 * t) := by
    calc
      Fintype.card Label = Fintype.card (Fin t) +
          Fintype.card {e : H // e ∉ Set.range endpoint} := Fintype.card_sum
      _ = t + ((Set.range endpoint)ᶜ : Set H).ncard := by
        rw [Fintype.card_fin]
        congr 1
        change Fintype.card ((Set.range endpoint)ᶜ : Set H) = _
        exact Set.fintypeCard_eq_ncard _
      _ = t + (Fintype.card H - (Set.range endpoint).ncard) := by
        rw [Set.ncard_compl, Nat.card_eq_fintype_card]
      _ = t + (Fintype.card H - 2 * t) := by rw [hrange]
  have hfiber : ∀ c, ({e : H | label e = c} : Set H).ncard ≤ 2 := by
    intro c
    rcases c with i | u
    · have hsub : ({e : H | label e = Sum.inl i} : Set H) ⊆ {left i, right i} := by
        intro e he
        by_cases her : e ∈ Set.range endpoint
        · have hindex : pairIndex (rangeEquiv.symm ⟨e, her⟩) = i := by
            apply Sum.inl_injective
            simpa only [Set.mem_setOf_eq, label, dif_pos her] using he
          have heq : endpoint (rangeEquiv.symm ⟨e, her⟩) = e :=
            congrArg Subtype.val (rangeEquiv.apply_symm_apply ⟨e, her⟩)
          generalize hs : rangeEquiv.symm ⟨e, her⟩ = a at hindex heq
          rcases a with j | j
          · have hji : j = i := hindex
            subst j
            exact Or.inl heq.symm
          · have hji : j = i := hindex
            subst j
            exact Or.inr heq.symm
        · have hh : (Sum.inr ⟨e, her⟩ : Label) = Sum.inl i := by
            simpa only [Set.mem_setOf_eq, label, dif_neg her] using he
          exact (Sum.inr_ne_inl hh).elim
      have hne : left i ≠ right i := fun h ↦ Sum.inl_ne_inr (hendpoints h)
      simpa only [Set.ncard_pair hne] using Set.ncard_le_ncard hsub
    · have hsub : ({e : H | label e = Sum.inr u} : Set H) ⊆ {u.1} := by
        intro e he
        by_cases her : e ∈ Set.range endpoint
        · have hh : (Sum.inl (pairIndex (rangeEquiv.symm ⟨e, her⟩)) : Label) =
              Sum.inr u := by
            simpa only [Set.mem_setOf_eq, label, dif_pos her] using he
          exact (Sum.inl_ne_inr hh).elim
        · have hh : (⟨e, her⟩ : {e : H // e ∉ Set.range endpoint}) = u := by
            apply Sum.inr_injective
            simpa only [Set.mem_setOf_eq, label, dif_neg her] using he
          exact congrArg Subtype.val hh
      have hc := Set.ncard_le_ncard hsub
      simp only [Set.ncard_singleton] at hc
      omega
  apply H.exists_bounded_fiber_coloring_of_compression label hlabel
  · rw [hLabel]
    omega
  · exact hfiber

/-- A pair-compression certificate gives a proper coloring with at most two
edges in every color class. -/
theorem PairCompressible.exists_pair_bounded_coloring {H : SetHypergraph X} {k : ℕ}
    (h : H.PairCompressible k) :
    ∃ color : H.EdgeColoring (Fin k),
      ∀ c, ({e : H | color.color e = c} : Set H).ncard ≤ 2 := by
  obtain ⟨t, left, right, hinj, hpairs, hcard⟩ := h
  exact H.exists_pair_bounded_coloring_of_disjoint_pairs left right hinj hpairs hcard

/-- A proper class with at most `b` edges of size at most `R` covers at most
`b * R` vertices. -/
theorem coveredVertices_le_of_class_bound (H : SetHypergraph X)
    {C : Type*} (color : H.EdgeColoring C) (c : C) (b R : ℕ)
    (hfiber : ({e : H | color.color e = c} : Set H).ncard ≤ b)
    (hmax : ∀ e : H, e.1.ncard ≤ R) :
    (H.coveredVertices {e : H | color.color e = c}).ncard ≤ b * R := by
  classical
  let M : Set H := {e | color.color e = c}
  have hM : H.IsMatching M :=
    (H.edgeColoring_iff_colorClasses_matching color.color).mp color.valid c
  have hcover := hM.coveredVertices_ncard_eq_sum
  rw [finsum_mem_eq_finite_toFinset_sum (fun e : H ↦ e.1.ncard) M.toFinite] at hcover
  calc
    (H.coveredVertices {e : H | color.color e = c}).ncard =
        ∑ e ∈ M.toFinite.toFinset, e.1.ncard := hcover
    _ ≤ ∑ _e ∈ M.toFinite.toFinset, R := Finset.sum_le_sum (fun e _ ↦ hmax e)
    _ = M.ncard * R := by
      rw [Finset.sum_const, smul_eq_mul]
      congr 1
      exact (Set.ncard_eq_toFinset_card M M.toFinite).symm
    _ ≤ b * R := Nat.mul_le_mul_right R hfiber

theorem PairCompressible.exists_cover_bounded_coloring {H : SetHypergraph X} {k : ℕ}
    (h : H.PairCompressible k) (R : ℕ) (hmax : ∀ e : H, e.1.ncard ≤ R) :
    ∃ color : H.EdgeColoring (Fin k), H.IsCoverBoundedColoring color (2 * R) := by
  obtain ⟨color, hfiber⟩ := h.exists_pair_bounded_coloring
  exact ⟨color, fun c ↦ Or.inr (H.coveredVertices_le_of_class_bound color c 2 R
    (hfiber c) hmax)⟩

theorem exists_singleton_coloring_of_card_le (H : SetHypergraph X) {k : ℕ}
    (hcard : Fintype.card H ≤ k) :
    ∃ color : H.EdgeColoring (Fin k),
      ∀ c, ({e : H | color.color e = c} : Set H).ncard ≤ 1 := by
  apply H.exists_bounded_fiber_coloring_of_compression id
    (fun {_ _} hne heq ↦ (hne heq).elim) hcard
  intro c
  have hset : ({e : H | id e = c} : Set H) = {c} := by ext e; rfl
  simp only [hset, Set.ncard_singleton, le_refl]

end Erdos19.SetHypergraph

#print axioms Erdos19.SetHypergraph.pairCompressible_of_disjointnessMatching
#print axioms Erdos19.SetHypergraph.PairCompressible.edgeColorable

#print axioms Erdos19.SetHypergraph.PairCompressible.exists_pair_bounded_coloring
