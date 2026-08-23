import ErdosProblems.Erdos1105.PrivateColors

namespace Erdos1105

open SimpleGraph

/-- If all private representative neighbors of a vertex lie in `S`, its
private-color count is bounded by its degree inside `S`. -/
theorem private_colors_le_induced_neighbors {V C : Type*} [Finite V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (S : Set V) (v : V) (hv : v ∈ S)
    (hwithin : ∀ w (hvw : R.Adj v w),
      PrivateAt c v (c ⟨s(v, w), hvw.ne⟩) → w ∈ S) :
    (privateColors c v).card ≤ Nat.card ((R.induce S).neighborSet ⟨v, hv⟩) := by
  classical
  let := Fintype.ofFinite V
  have hex (i : privateColors c v) : ∃ w, ∃ hw : R.Adj v w,
      w ∈ S ∧ c ⟨s(v, w), hw.ne⟩ = i.val := by
    have hi : PrivateAt c v i.val := (mem_privateColors c v i.val).mp i.property
    obtain ⟨⟨e, he⟩, hcol⟩ := hpalette i.val ⟨v, hi⟩
    have hraw : c ⟨e, edgeSet_mono le_top he⟩ = i.val := by
      apply Option.some.inj
      rw [← extendColor_edge c ⟨e, edgeSet_mono le_top he⟩]
      exact hcol
    have hmem := hi ⟨e, edgeSet_mono le_top he⟩ hraw
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hmem
    have hw : R.Adj v w := he
    have hpriv : PrivateAt c v (c ⟨s(v, w), hw.ne⟩) := by rwa [hraw]
    exact ⟨w, hw, hwithin w hw hpriv, hraw⟩
  choose w hw hws hc using hex
  let g : privateColors c v → (R.induce S).neighborSet ⟨v, hv⟩ :=
    fun i ↦ ⟨⟨w i, hws i⟩, hw i⟩
  have hg : Function.Injective g := by
    intro i j hij
    have hw_eq : w i = w j := congrArg (fun x : (R.induce S).neighborSet ⟨v, hv⟩ ↦ x.val.val) hij
    have hcol : c ⟨s(v, w i), (hw i).ne⟩ = c ⟨s(v, w j), (hw j).ne⟩ :=
      congrArg c (Subtype.ext (congrArg (fun x ↦ s(v, x)) hw_eq))
    exact Subtype.ext ((hc i).symm.trans (hcol.trans (hc j)))
  have h := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using h

/-- Too many private colors force an external privately colored representative edge. -/
theorem exists_private_neighbor_outside {V C : Type*} [Finite V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (S : Set V) (v : V) (hv : v ∈ S)
    (hlarge : Nat.card ((R.induce S).neighborSet ⟨v, hv⟩) < (privateColors c v).card) :
    ∃ w, ∃ hw : R.Adj v w, w ∉ S ∧ PrivateAt c v (c ⟨s(v, w), hw.ne⟩) := by
  classical
  by_contra h
  have hwithin : ∀ w (hw : R.Adj v w), PrivateAt c v (c ⟨s(v, w), hw.ne⟩) → w ∈ S := by
    intro w hw hp
    by_contra hnot
    exact h ⟨w, hw, hnot, hp⟩
  exact hlarge.not_ge (private_colors_le_induced_neighbors c R hpalette S v hv hwithin)

/-- Count private colors by indices of their representative neighbors.
This form keeps path-index arithmetic separate from induced graph degrees. -/
theorem private_colors_le_neighbor_indices {I V C : Type*} [Fintype I] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V) [DecidableRel R.Adj]
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (v : I ↪ V) (a : I) (P : I → Prop) [DecidablePred P]
    (hwithin : ∀ w (hw : R.Adj (v a) w),
      PrivateAt c (v a) (c ⟨s(v a, w), hw.ne⟩) → ∃ j, P j ∧ v j = w) :
    (privateColors c (v a)).card ≤
      (Finset.univ.filter (fun j ↦ R.Adj (v a) (v j) ∧ P j)).card := by
  classical
  have hex (i : privateColors c (v a)) : ∃ j, ∃ hj : R.Adj (v a) (v j),
      P j ∧ c ⟨s(v a, v j), hj.ne⟩ = i.val := by
    have hi : PrivateAt c (v a) i.val := (mem_privateColors c (v a) i.val).mp i.property
    obtain ⟨⟨e, he⟩, hcol⟩ := hpalette i.val ⟨v a, hi⟩
    have hraw : c ⟨e, edgeSet_mono le_top he⟩ = i.val := by
      apply Option.some.inj
      rw [← extendColor_edge c ⟨e, edgeSet_mono le_top he⟩]
      exact hcol
    have hmem := hi ⟨e, edgeSet_mono le_top he⟩ hraw
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hmem
    have hw : R.Adj (v a) w := he
    have hpriv : PrivateAt c (v a) (c ⟨s(v a, w), hw.ne⟩) := by rwa [hraw]
    obtain ⟨j, hj, heq⟩ := hwithin w hw hpriv
    subst w
    exact ⟨j, hw, hj, hraw⟩
  choose j hj hP hcol using hex
  let f : privateColors c (v a) →
      {j // j ∈ Finset.univ.filter (fun j ↦ R.Adj (v a) (v j) ∧ P j)} :=
    fun i ↦ ⟨j i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj i, hP i⟩⟩
  have hf : Function.Injective f := by
    intro i k hik
    have heq : j i = j k := congrArg Subtype.val hik
    apply Subtype.ext
    calc
      i.val = c ⟨s(v a, v (j i)), (hj i).ne⟩ := (hcol i).symm
      _ = c ⟨s(v a, v (j k)), (hj k).ne⟩ :=
        congrArg c (Subtype.ext (congrArg (fun j ↦ s(v a, v j)) heq))
      _ = k.val := hcol k
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

end Erdos1105
