-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Defs

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Isolated-vertex reduction (§2)

The reduction `F ↦ F°` deletes isolated vertices, and embeddability into an
infinite host is unaffected (`lem:isolated-reduction`).
-/

open Cardinal Function

namespace Erdos1177

universe u

open Classical in
/-- The isolated-vertex reduction `F°`: delete all isolated vertices. -/
noncomputable def FTS.reduce (F : FTS) : FTS where
  V := {x : F.V // ¬ F.Isolated x}
  finV := Fintype.ofFinite _
  decV := Subtype.instDecidableEq
  edges := F.edges.attach.image (fun e => Finset.subtype (fun x => ¬ F.Isolated x) e.1)
  card3 := by
    classical
    intro e he
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at he
    obtain ⟨d, rfl⟩ := he
    have hd : d.1 ∈ F.edges := d.2
    rw [Finset.card_subtype]
    have : d.1.filter (fun x => ¬ F.Isolated x) = d.1 := by
      apply Finset.filter_true_of_mem
      intro x hx
      simp only [FTS.Isolated, not_forall]
      exact ⟨d.1, hd, by simpa using! hx⟩
    rw [this]
    exact F.card3 d.1 hd

/-- A triple-system host that is uncountably chromatic has an infinite vertex
type. -/
theorem Hypergraph.UncountablyChromatic.infinite {W : Type u} {H : Hypergraph W}
    (htri : H.IsTripleSystem) (h : H.UncountablyChromatic) : Infinite W := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  apply h
  have hinf : Infinite ((ℵ₀ : Cardinal.{u}).out) := by
    rw [Cardinal.infinite_iff, Cardinal.mk_out]
  have hle : (#W) ≤ (#((ℵ₀ : Cardinal.{u}).out)) :=
    le_trans (le_of_lt (Cardinal.lt_aleph0_of_finite W)) (Cardinal.infinite_iff.mp hinf)
  obtain ⟨c, hc⟩ := (Cardinal.le_def _ _).mp hle
  exact ⟨c, fun e he => by
    obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Set.ncard_eq_three.mp (htri e he)
    exact ⟨a, by simp, b, by simp, fun hcab => hab (hc hcab)⟩⟩

/-- Forward direction of the reduction: an embedding of `F` restricts to one of
`F°`. -/
theorem FTS.reduce_embeds_of_embeds (F : FTS) {W : Type u} {H : Hypergraph W}
    (h : F.Embeds H) : F.reduce.Embeds H := by
  obtain ⟨f, hf₁, hf₂⟩ := h
  refine ⟨fun x => f x.val, hf₁.comp Subtype.coe_injective, ?_⟩
  simp only [FTS.reduce, Finset.mem_image, Finset.mem_attach, true_and, forall_exists_index]
  rintro e d rfl
  convert! hf₂ d.1 d.2 using 1
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.val, by simpa [Finset.mem_subtype] using! ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    have hna : ¬ F.Isolated a := fun hiso => hiso d.1 d.2 ha
    exact ⟨⟨a, hna⟩, by simpa [Finset.mem_subtype] using! ha, rfl⟩

/-- An injection from a finite type into an infinite type avoiding the range of
a given map (used to place isolated vertices on fresh host vertices). -/
theorem exists_injective_avoiding {A : Type} [Finite A] {W : Type u} (g : A → W)
    [Infinite W] (S : Type) [Finite S] :
    ∃ emb : S → W, Function.Injective emb ∧ ∀ x, emb x ∉ Set.range g := by
  classical
  have hcompl : Set.Infinite ((Set.range g)ᶜ) := (Set.finite_range g).infinite_compl
  obtain ⟨t, ht_sub, ht_card⟩ := hcompl.exists_subset_card_eq (Nat.card S)
  have e : S ≃ Fin (Nat.card S) := by
    have := Fintype.ofFinite S; simpa [Nat.card_eq_fintype_card] using! Fintype.equivFin S
  have e2 := (Finset.equivFinOfCardEq ht_card).symm
  exact ⟨fun x => (e2 (e x)).1, fun a b hab => e.injective (e2.injective (Subtype.ext hab)),
    fun x hx => (ht_sub (e2 (e x)).2) hx⟩

/-- Backward direction of the reduction, for an infinite host. -/
theorem FTS.embeds_of_reduce_embeds (F : FTS) {W : Type u} [Infinite W]
    {H : Hypergraph W} (h : F.reduce.Embeds H) : F.Embeds H := by
  classical
  obtain ⟨g, hg, hge⟩ := h
  obtain ⟨emb, hemb_inj, hemb_range⟩ := exists_injective_avoiding g {x : F.V // F.Isolated x}
  set f : F.V → W := fun x => if hx : ¬ F.Isolated x then g ⟨x, hx⟩ else emb ⟨x, not_not.mp hx⟩
    with hf
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    simp only [hf] at hab
    by_cases ha : ¬ F.Isolated a <;> by_cases hb : ¬ F.Isolated b
    · rw [dif_pos ha, dif_pos hb] at hab; exact congrArg Subtype.val (hg hab)
    · rw [dif_pos ha, dif_neg hb] at hab
      exact absurd ⟨_, hab⟩ (hemb_range ⟨b, not_not.mp hb⟩)
    · rw [dif_neg ha, dif_pos hb] at hab
      exact absurd ⟨_, hab.symm⟩ (hemb_range ⟨a, not_not.mp ha⟩)
    · rw [dif_neg ha, dif_neg hb] at hab; exact congrArg Subtype.val (hemb_inj hab)
  · intro e he
    have hre : Finset.subtype (fun x => ¬ F.Isolated x) e ∈ F.reduce.edges := by
      simp only [FTS.reduce, Finset.mem_image, Finset.mem_attach, true_and]; exact ⟨⟨e, he⟩, rfl⟩
    have hE := hge _ hre
    convert! hE using 1
    ext w
    simp only [Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have haa : a ∈ e := by simpa using! ha
      have hna : ¬ F.Isolated a := fun hiso => hiso e he haa
      refine ⟨⟨a, hna⟩, Finset.mem_coe.mpr (Finset.mem_subtype.mpr haa), ?_⟩
      simp only [hf]; rw [dif_pos hna]
    · rintro ⟨a, ha, rfl⟩
      have haa : a.val ∈ e := Finset.mem_subtype.mp (Finset.mem_coe.mp ha)
      refine ⟨a.val, Finset.mem_coe.mpr haa, ?_⟩
      simp only [hf]; rw [dif_pos a.2]; exact congrArg g (Subtype.eta a a.2)

/-- **Isolated-vertex reduction** (`lem:isolated-reduction`, embedding form).
For an infinite host `H`, `F` embeds iff its reduction `F°` embeds. -/
theorem FTS.embeds_reduce_iff (F : FTS) {W : Type u} [Infinite W] (H : Hypergraph W) :
    F.Embeds H ↔ F.reduce.Embeds H :=
  ⟨F.reduce_embeds_of_embeds, F.embeds_of_reduce_embeds⟩

/-- Obligatoriness is unaffected by isolated vertices. -/
theorem FTS.obligatory_reduce_iff (F : FTS) :
    FTS.Obligatory.{u} F ↔ FTS.Obligatory.{u} F.reduce := by
  constructor
  · intro hF W H htri huc
    exact F.reduce_embeds_of_embeds (hF H htri huc)
  · intro hF W H htri huc
    have : Infinite W := huc.infinite htri
    exact F.embeds_of_reduce_embeds (hF H htri huc)

/-- The spectrum is unaffected by isolated vertices. -/
theorem FTS.inSpec_reduce_iff (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ F.reduce.InSpec lam := by
  unfold FTS.InSpec
  constructor
  · rintro ⟨hlam, W, H, htri, hchr, hne⟩
    have hInf : Infinite W := Hypergraph.UncountablyChromatic.infinite htri (by
      intro hc; exact absurd (hchr.2 ℵ₀ hlam hc) (by simp))
    exact ⟨hlam, W, H, htri, hchr, fun hcon => hne (F.embeds_of_reduce_embeds hcon)⟩
  · rintro ⟨hlam, W, H, htri, hchr, hne⟩
    exact ⟨hlam, W, H, htri, hchr, fun hcon => hne (F.reduce_embeds_of_embeds hcon)⟩

end Erdos1177
