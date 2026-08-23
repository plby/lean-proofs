import ErdosProblems.Erdos1105.SwapRepresentative

namespace Erdos1105

open SimpleGraph

/-- A spanning rainbow graph containing one edge of every color. -/
structure IsFullRepresentative {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V) : Prop where
  rainbow : Set.InjOn (extendColor c) R.edgeSet
  palette : ∀ i, ∃ e : R.edgeSet, extendColor c e.val = some i

theorem exists_fullRepresentative {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c) :
    ∃ R, IsFullRepresentative c R := by
  obtain ⟨R, _, hr, e, he⟩ := exists_representative c hc
  exact ⟨R, hr, fun i ↦ ⟨e i, he i⟩⟩

theorem IsFullRepresentative.swap {V C : Type*}
    {c : (⊤ : SimpleGraph V).edgeSet → C} {R : SimpleGraph V}
    (hR : IsFullRepresentative c R) (e : R.edgeSet) (d : (⊤ : SimpleGraph V).edgeSet)
    (hcol : extendColor c d.val = extendColor c e.val) :
    IsFullRepresentative c (swapRepresentative R e.val d.val) := by
  refine ⟨swapRepresentative_rainbow c R hR.rainbow e d hcol, ?_⟩
  intro i
  obtain ⟨⟨a, ha⟩, hca⟩ := hR.palette i
  by_cases he : a = e.val
  · exact ⟨⟨d.val, (mem_swapRepresentative R e.val d d.val).mpr (Or.inr rfl)⟩,
      hcol.trans (he ▸ hca)⟩
  · exact ⟨⟨a, (mem_swapRepresentative R e.val d a).mpr (Or.inl ⟨ha, he⟩)⟩, hca⟩

def representativeColor {V C : Type*} (c : (⊤ : SimpleGraph V).edgeSet → C)
    (R : SimpleGraph V) : R.edgeSet → C :=
  fun e ↦ c ⟨e.val, edgeSet_mono le_top e.property⟩

theorem IsFullRepresentative.color_bijective {V C : Type*}
    {c : (⊤ : SimpleGraph V).edgeSet → C} {R : SimpleGraph V}
    (hR : IsFullRepresentative c R) : Function.Bijective (representativeColor c R) := by
  classical
  let f := representativeColor c R
  have hcolor (e : R.edgeSet) : extendColor c e.val = some (f e) :=
    extendColor_edge c ⟨e.val, edgeSet_mono le_top e.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e d hed
      apply Subtype.ext
      apply hR.rainbow e.property d.property
      simpa only [hcolor] using congrArg some hed
    · intro i
      obtain ⟨e, he⟩ := hR.palette i
      refine ⟨e, ?_⟩
      apply Option.some.inj
      rw [← he]
      exact (extendColor_edge c ⟨e.val, edgeSet_mono le_top e.property⟩).symm
  exact hf

theorem isFullRepresentative_of_color_bijective {V C : Type*}
    {c : (⊤ : SimpleGraph V).edgeSet → C} {R : SimpleGraph V}
    (h : Function.Bijective (representativeColor c R)) : IsFullRepresentative c R := by
  have hcolor (e : R.edgeSet) : extendColor c e.val = some (representativeColor c R e) :=
    extendColor_edge c ⟨e.val, edgeSet_mono le_top e.property⟩
  constructor
  · intro a ha b hb hab
    have heq : representativeColor c R ⟨a, ha⟩ = representativeColor c R ⟨b, hb⟩ := by
      apply Option.some.inj
      rw [← hcolor ⟨a, ha⟩, ← hcolor ⟨b, hb⟩]
      exact hab
    exact congrArg Subtype.val (h.1 heq)
  · intro i
    obtain ⟨e, he⟩ := h.2 i
    exact ⟨e, (hcolor e).trans (congrArg some he)⟩

theorem IsFullRepresentative.card_edges {V C : Type*} [Fintype V] [Fintype C]
    {c : (⊤ : SimpleGraph V).edgeSet → C} {R : SimpleGraph V} [DecidableRel R.Adj]
    (hR : IsFullRepresentative c R) : R.edgeFinset.card = Fintype.card C := by
  rw [edgeFinset_card]
  exact Fintype.card_congr (Equiv.ofBijective (representativeColor c R) hR.color_bijective)

def restrictVertexColoring {V C : Type*} (c : (⊤ : SimpleGraph V).edgeSet → C) (v : V) :
    (⊤ : SimpleGraph {w // w ≠ v}).edgeSet → C := c ∘ (deleteVertexCopy v).mapEdgeSet

theorem restrictVertexColoring_free {V C A : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (v : V) {H : SimpleGraph A}
    (hfree : ∀ f : H.Copy (⊤ : SimpleGraph V), ¬IsRainbow f c) :
    ∀ f : H.Copy (⊤ : SimpleGraph {w // w ≠ v}), ¬IsRainbow f (restrictVertexColoring c v) := by
  intro f hf
  apply hfree ((deleteVertexCopy v).comp f)
  rw [rainbow_comp_iff]
  exact hf

theorem IsFullRepresentative.delete_isolated {V C : Type*}
    {c : (⊤ : SimpleGraph V).edgeSet → C} {R : SimpleGraph V}
    (hR : IsFullRepresentative c R) {v : V} (hv : R.IsIsolated v) :
    IsFullRepresentative (restrictVertexColoring c v) (R.induce {w | w ≠ v}) := by
  let f := Copy.induce R {w | w ≠ v}
  have hsurj : Function.Surjective f.mapEdgeSet := by
    intro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ a b =>
      have ha : a ≠ v := fun h ↦ hv b (h ▸ he)
      have hb : b ≠ v := fun h ↦ hv a (h ▸ (show R.Adj a b from he).symm)
      exact ⟨⟨s(⟨a, ha⟩, ⟨b, hb⟩), he⟩, rfl⟩
  apply isFullRepresentative_of_color_bijective
  have heq : representativeColor (restrictVertexColoring c v) (R.induce {w | w ≠ v}) =
      representativeColor c R ∘ f.mapEdgeSet := by
    funext e
    rfl
  rw [heq]
  exact hR.color_bijective.comp ⟨f.mapEdgeSet.injective, hsurj⟩

theorem IsFullRepresentative.free {V C A : Type*}
    {c : (⊤ : SimpleGraph V).edgeSet → C} {R : SimpleGraph V}
    (hR : IsFullRepresentative c R) {H : SimpleGraph A}
    (hfree : ∀ f : H.Copy (⊤ : SimpleGraph V), ¬IsRainbow f c) : ¬H ⊑ R :=
  representative_free le_top c hR.rainbow hfree

theorem IsFullRepresentative.neighbor_of_private {V C : Type*}
    {c : (⊤ : SimpleGraph V).edgeSet → C} {R : SimpleGraph V}
    (hR : IsFullRepresentative c R) {v : V} {i : C} (hpriv : PrivateAt c v i) :
    ∃ w, R.Adj v w := by
  obtain ⟨⟨e, he⟩, hcol⟩ := hR.palette i
  have hraw : c ⟨e, edgeSet_mono le_top he⟩ = i := by
    apply Option.some.inj
    rw [← extendColor_edge c ⟨e, edgeSet_mono le_top he⟩]
    exact hcol
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp (hpriv ⟨e, edgeSet_mono le_top he⟩ hraw)
  exact ⟨w, he⟩

theorem IsFullRepresentative.no_isolated_of_private {V C : Type*} [Fintype C]
    {c : (⊤ : SimpleGraph V).edgeSet → C} {R : SimpleGraph V}
    (hR : IsFullRepresentative c R) (hpriv : ∀ v, 0 < (privateColors c v).card) :
    ∀ v, ∃ w, R.Adj v w := by
  intro v
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (hpriv v)
  exact hR.neighbor_of_private ((mem_privateColors c v i).mp hi)

end Erdos1105

#print axioms Erdos1105.IsFullRepresentative.card_edges
