import ErdosProblems.Erdos1105.Representatives

namespace Erdos1105

open SimpleGraph

attribute [local instance] Classical.propDecidable

/-- A color is private to a vertex if every edge of that color contains it. -/
def PrivateAt {V C : Type*} (c : (⊤ : SimpleGraph V).edgeSet → C) (v : V) (i : C) : Prop :=
  ∀ e, c e = i → v ∈ e.val

lemma privateAt_of_external_color_collision {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (e : (⊤ : SimpleGraph V).edgeSet)
    (he : ∃ w, PrivateAt c w (c e)) (u v : V) (hu : u ∉ e.val) (huv : u ≠ v)
    (hcol : extendColor c s(u, v) = extendColor c e.val) : PrivateAt c v (c e) := by
  have hraw : c ⟨s(u, v), huv⟩ = c e := by
    apply Option.some.inj
    rw [← extendColor_edge c ⟨s(u, v), huv⟩, ← extendColor_edge c e]
    exact hcol
  obtain ⟨w, hw⟩ := he
  have hm : w = u ∨ w = v := Sym2.mem_iff.mp (hw ⟨s(u, v), huv⟩ hraw)
  rcases hm with rfl | rfl
  · exact (hu (hw e rfl)).elim
  · exact hw

noncomputable def privateColors {V C : Type*} [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (v : V) : Finset C :=
  Finset.univ.filter (PrivateAt c v)

@[simp] lemma mem_privateColors {V C : Type*} [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (v : V) (i : C) :
    i ∈ privateColors c v ↔ PrivateAt c v i := by simp [privateColors]

/-- Inclusion after deleting one vertex. -/
def deleteVertexCopy {V : Type*} (v : V) :
    (⊤ : SimpleGraph {w // w ≠ v}).Copy (⊤ : SimpleGraph V) where
  toHom := { toFun := Subtype.val, map_rel' := fun h ↦ Subtype.val_injective.ne h }
  injective' := Subtype.val_injective

lemma not_private_deleted_edge {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (v : V)
    (e : (⊤ : SimpleGraph {w // w ≠ v}).edgeSet) :
    ¬PrivateAt c v (c ((deleteVertexCopy v).mapEdgeSet e)) := by
  intro h
  have hv := h ((deleteVertexCopy v).mapEdgeSet e) rfl
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | _ a b =>
    change v ∈ s(a.val, b.val) at hv
    simp only [Sym2.mem_iff] at hv
    exact hv.elim (fun h ↦ a.property h.symm) (fun h ↦ b.property h.symm)

/-- Deleting a vertex removes exactly its private colors. -/
def deleteVertexColoring {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (v : V) :
    (⊤ : SimpleGraph {w // w ≠ v}).edgeSet → {i // ¬PrivateAt c v i} :=
  fun e ↦ ⟨c ((deleteVertexCopy v).mapEdgeSet e), not_private_deleted_edge c v e⟩

lemma deleteVertexColoring_surjective {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (v : V) :
    Function.Surjective (deleteVertexColoring c v) := by
  intro i
  have hnot := i.property
  simp only [PrivateAt, not_forall] at hnot
  obtain ⟨⟨e, he⟩, hcol, haway⟩ := hnot
  induction e using Sym2.inductionOn with
  | _ a b =>
    have ha : a ≠ v := by intro h; exact haway (by simp [h])
    have hb : b ≠ v := by intro h; exact haway (by simp [h])
    refine ⟨⟨s(⟨a, ha⟩, ⟨b, hb⟩), fun h ↦ he (congrArg Subtype.val h)⟩, ?_⟩
    exact Subtype.ext hcol

lemma rainbow_comp_iff {α V W C : Type*} {H : SimpleGraph α}
    {G : SimpleGraph V} {K : SimpleGraph W} (f : H.Copy G) (g : G.Copy K)
    (c : K.edgeSet → C) : IsRainbow (g.comp f) c ↔ IsRainbow f (c ∘ g.mapEdgeSet) := by
  have hmap (e : H.edgeSet) : (g.comp f).mapEdgeSet e = g.mapEdgeSet (f.mapEdgeSet e) := by
    apply Subtype.ext
    simp [Copy.mapEdgeSet, Hom.mapEdgeSet, Copy.comp, Sym2.map_map]
  simp only [IsRainbow, Function.comp_def, hmap]

lemma deleteVertexColoring_no_rainbow {α V C : Type*} {H : SimpleGraph α}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (v : V)
    (hH : ∀ f : H.Copy (⊤ : SimpleGraph V), ¬IsRainbow f c) :
    ∀ f : H.Copy (⊤ : SimpleGraph {w // w ≠ v}), ¬IsRainbow f (deleteVertexColoring c v) := by
  intro f hf
  apply hH ((deleteVertexCopy v).comp f)
  rw [rainbow_comp_iff]
  intro a b hab
  apply hf
  exact Subtype.ext hab

/-- The exact loss-of-colors inequality used in induction on the host size. -/
theorem color_count_le_delete_add_private {α V C : Type*}
    [Fintype α] [Fintype V] [Fintype C] {H : SimpleGraph α}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (v : V)
    (hH : ∀ f : H.Copy (⊤ : SimpleGraph V), ¬IsRainbow f c) :
    Fintype.card C ≤ antiRamseyNum H (Fintype.card V - 1) + (privateColors c v).card := by
  have h := card_le_antiRamseyNum (deleteVertexColoring c v)
    (deleteVertexColoring_surjective c v) (deleteVertexColoring_no_rainbow c v hH)
  have hverts : Fintype.card {w // w ≠ v} = Fintype.card V - 1 := by
    simp [Fintype.card_subtype_compl (fun w : V ↦ w = v)]
  have hcols : Fintype.card {i // ¬PrivateAt c v i} + (privateColors c v).card =
      Fintype.card C := by
    rw [show (privateColors c v).card = Fintype.card {i // PrivateAt c v i} from by
      simp [privateColors, Fintype.card_subtype]]
    rw [Fintype.card_subtype_compl]
    exact Nat.sub_add_cancel (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)
  rw [hverts] at h
  omega

/-- The graph of edges whose color is private to at least one vertex. -/
noncomputable def privateGraph {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) : SimpleGraph V :=
  fromEdgeSet {e | ∃ h : e ∈ (⊤ : SimpleGraph V).edgeSet, ∃ v, PrivateAt c v (c ⟨e, h⟩)}

lemma mem_privateGraph_edgeSet {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (e : (⊤ : SimpleGraph V).edgeSet) :
    e.val ∈ (privateGraph c).edgeSet ↔ ∃ v, PrivateAt c v (c e) := by
  rw [privateGraph, edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨⟨he, v, hv⟩, _⟩
    exact ⟨v, hv⟩
  · intro h
    exact ⟨⟨e.property, h⟩, (⊤ : SimpleGraph V).not_isDiag_of_mem_edgeSet e.property⟩

/-- The private representative used in the structural cycle argument:
it is rainbow, every edge has a private endpoint, and every vertex retains
at least as many incident edges as it has private colors. -/
theorem exists_private_representative {V C : Type*} [Finite V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c) :
    ∃ R : SimpleGraph V,
      Set.InjOn (extendColor c) R.edgeSet ∧
      (∀ e : R.edgeSet, ∃ v, PrivateAt c v
        (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩)) ∧
      (∀ v, (privateColors c v).card ≤ Nat.card (R.neighborSet v)) ∧
      (∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i) := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨R₀, hR₀, hr₀, e, he⟩ := exists_representative c hc
  let R := R₀ ⊓ privateGraph c
  have hR : R ≤ R₀ := inf_le_left
  have hcol (i : C) : c ⟨(e i).val, edgeSet_mono hR₀ (e i).property⟩ = i := by
    apply Option.some.inj
    rw [← extendColor_edge c ⟨(e i).val, edgeSet_mono hR₀ (e i).property⟩]
    exact he i
  refine ⟨R, hr₀.mono (edgeSet_mono hR), ?_, ?_, ?_⟩
  · intro x
    have hx : x.val ∈ (privateGraph c).edgeSet :=
      edgeSet_mono (show R ≤ privateGraph c from inf_le_right) x.property
    exact (mem_privateGraph_edgeSet c ⟨x.val, edgeSet_mono le_top x.property⟩).mp hx
  · intro v
    have hinc (i : privateColors c v) : (e i.val).val ∈ R.incidenceSet v := by
      have hip : PrivateAt c v i.val := (mem_privateColors c v i.val).mp i.property
      refine ⟨?_, hip ⟨(e i.val).val, edgeSet_mono hR₀ (e i.val).property⟩ (hcol i.val)⟩
      change (e i.val).val ∈ (R₀ ⊓ privateGraph c).edgeSet
      rw [edgeSet_inf]
      refine ⟨(e i.val).property, ?_⟩
      apply (mem_privateGraph_edgeSet c
        ⟨(e i.val).val, edgeSet_mono hR₀ (e i.val).property⟩).mpr
      exact ⟨v, by rwa [hcol]⟩
    let g : privateColors c v → R.incidenceSet v := fun i ↦ ⟨(e i.val).val, hinc i⟩
    have hg : Function.Injective g := by
      intro i j hij
      apply Subtype.ext
      apply e.injective
      exact Subtype.ext (congrArg (fun x : R.incidenceSet v ↦ x.val) hij)
    have h := Fintype.card_le_of_injective g hg
    rw [Fintype.card_coe, Fintype.card_congr (R.incidenceSetEquivNeighborSet v)] at h
    simpa only [Nat.card_eq_fintype_card] using h
  · intro i hi
    have hmem : (e i).val ∈ R.edgeSet := by
      change (e i).val ∈ (R₀ ⊓ privateGraph c).edgeSet
      rw [edgeSet_inf]
      refine ⟨(e i).property, ?_⟩
      apply (mem_privateGraph_edgeSet c ⟨(e i).val, edgeSet_mono hR₀ (e i).property⟩).mpr
      rwa [hcol]
    exact ⟨⟨(e i).val, hmem⟩, he i⟩

end Erdos1105
