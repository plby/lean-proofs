import ErdosProblems.Erdos1105.RemainderColoring

namespace Erdos1105

open SimpleGraph Finset

/-- A full representative with some bridges removed. Every ambient
edge crossing the remaining components has a color absent from each of
the two components it joins. -/
structure SeparatedRepresentative {V C : Type*} (G : SimpleGraph V) (c : Sym2 V → C)
    (R H : SimpleGraph V) : Prop where
  representative : ColorRepresentative G c R
  le : H ≤ R
  removed_bridge : ∀ e ∈ R.edgeSet, e ∉ H.edgeSet → R.IsBridge e
  fresh : ∀ a b, G.Adj a b → ¬H.Reachable a b →
    ∀ x y, H.Adj x y → H.Reachable a x → c s(x, y) ≠ c s(a, b)

theorem separated_splice {V C : Type*} [Fintype V] [DecidableEq V]
    {G R : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S)
    (X : Set (Sym2 (S : Set V))) (hXsub : X ⊆ (R.induce (S : Set V)).edgeSet)
    (hXbridge : ∀ e ∈ X, (R.induce (S : Set V)).IsBridge e)
    (hinside : ∀ a b : (S : Set V), G.Adj a.val b.val →
      ¬((R.induce (S : Set V)).deleteEdges X).Reachable a b →
        ∃ e ∈ X, inducedColor c S e = c s(a.val, b.val))
    (hcross : ∀ a ∈ S, ∀ b ∉ S, G.Adj a b → ∃ e ∈ X, inducedColor c S e = c s(a, b))
    {B D : SimpleGraph (↑(Sᶜ) : Set V)}
    (hBD : SeparatedRepresentative (remainderGraph G R c S)
      (inducedColor c (↑(Sᶜ) : Set V)) B D) :
    SeparatedRepresentative G c (spliceGraphs S (R.induce (S : Set V)) B)
      (spliceGraphs S ((R.induce (S : Set V)).deleteEdges X) D) := by
  classical
  let A := R.induce (S : Set V)
  let A' := A.deleteEdges X
  let Q := spliceGraphs S A B
  let H := spliceGraphs S A' D
  have hleft : ∀ (x y : (S : Set V)), A'.Adj x y → ∀ e ∈ X,
      inducedColor c S s(x, y) ≠ inducedColor c S e := by
    intro x y hxy e he hcol
    have hxy' := deleteEdges_adj.mp hxy
    have heq := @hmax.induced_representative.rainbow s(x, y) hxy'.1 e (hXsub he) hcol
    exact hxy'.2 (heq ▸ he)
  have hright : ∀ (x y : (↑(Sᶜ) : Set V)), D.Adj x y →
      ∀ e ∈ R.edgeSet, e.toFinset ⊆ S → c e ≠ c s(x.val, y.val) :=
    fun x y hxy ↦ (hBD.representative.le (hBD.le hxy)).2
  refine ⟨hmax.splice_representative hBD.representative, ?_, ?_, ?_⟩
  · intro a b hab
    rcases hab with ⟨ha, hb, hab⟩ | ⟨ha, hb, hab⟩
    · exact Or.inl ⟨ha, hb, (deleteEdges_adj.mp hab).1⟩
    · exact Or.inr ⟨ha, hb, hBD.le hab⟩
  · intro e he hnot
    induction e using Sym2.inductionOn with
    | _ a b =>
      rcases he with ⟨ha, hb, hab⟩ | ⟨ha, hb, hab⟩
      · have heX : s(⟨a, ha⟩, ⟨b, hb⟩) ∈ X := by
          by_contra heX
          exact hnot (Or.inl ⟨ha, hb, deleteEdges_adj.mpr ⟨hab, heX⟩⟩)
        exact spliceGraphs_bridge_left S A B _ (hXbridge _ heX)
      · have hnotD : s(⟨a, ha⟩, ⟨b, hb⟩) ∉ D.edgeSet :=
          fun h ↦ hnot (Or.inr ⟨ha, hb, h⟩)
        exact spliceGraphs_bridge_right S A B _ (hBD.removed_bridge _ hab hnotD)
  · intro a b hab hnot x y hxy hax hcol
    by_cases ha : a ∈ S
    · have hx : x ∈ S := mem_of_reachable_closed (spliceGraphs_left_closed S A' D) ha hax
      have hy : y ∈ S := spliceGraphs_left_closed S A' D x hx y hxy
      have hxy' : A'.Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
        have h : (H.induce (S : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hxy
        simpa only [H, spliceGraphs_induce_left] using h
      have hc : ∃ e ∈ X, inducedColor c S e = c s(a, b) := by
        by_cases hb : b ∈ S
        · exact hinside ⟨a, ha⟩ ⟨b, hb⟩ hab (fun h ↦ hnot
            ((spliceGraphs_reachable_left S A' D ⟨a, ha⟩ ⟨b, hb⟩).mpr h))
        · exact hcross a ha b hb hab
      obtain ⟨e, he, hc⟩ := hc
      exact hleft ⟨x, hx⟩ ⟨y, hy⟩ hxy' e he (hcol.trans hc.symm)
    · have ha' : a ∈ Sᶜ := mem_compl.mpr ha
      have hx : x ∈ Sᶜ := mem_of_reachable_closed (spliceGraphs_right_closed S A' D) ha' hax
      have hy : y ∈ Sᶜ := spliceGraphs_right_closed S A' D x hx y hxy
      have hxy' : D.Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
        have h : (H.induce (↑(Sᶜ) : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hxy
        simpa only [H, spliceGraphs_induce_right] using h
      have hbad : (∃ e ∈ R.edgeSet, e.toFinset ⊆ S ∧ c e = c s(a, b)) → False := by
        rintro ⟨e, he, heS, hc⟩
        exact hright ⟨x, hx⟩ ⟨y, hy⟩ hxy' e he heS (hc.trans hcol.symm)
      by_cases hb : b ∈ S
      · obtain ⟨e, he, hc⟩ := hcross b hb a ha hab.symm
        induction e using Sym2.inductionOn with
        | _ u v =>
          apply hbad
          refine ⟨s(u.val, v.val), hXsub he, pair_toFinset_subset.mpr ⟨u.property, v.property⟩, ?_⟩
          simpa only [inducedColor, Function.comp_apply, Sym2.map_mk, Sym2.eq_swap] using hc
      · have hb' : b ∈ Sᶜ := mem_compl.mpr hb
        have havoid : ∀ e ∈ R.edgeSet, e.toFinset ⊆ S → c e ≠ c s(a, b) := by
          intro e he heS hc
          exact hbad ⟨e, he, heS, hc⟩
        have hab' : (remainderGraph G R c S).Adj ⟨a, ha'⟩ ⟨b, hb'⟩ := ⟨hab, havoid⟩
        have hnot' : ¬D.Reachable ⟨a, ha'⟩ ⟨b, hb'⟩ := fun h ↦ hnot
          ((spliceGraphs_reachable_right S A' D ⟨a, ha'⟩ ⟨b, hb'⟩).mpr h)
        have hax' := (spliceGraphs_reachable_right S A' D ⟨a, ha'⟩ ⟨x, hx⟩).mp hax
        exact hBD.fresh ⟨a, ha'⟩ ⟨b, hb'⟩ hab' hnot' ⟨x, hx⟩ ⟨y, hy⟩ hxy' hax' hcol

/-- Every finite colored graph admits the bridge decomposition used in
the disconnected-representative part of the path proof. -/
theorem exists_separatedRepresentative {V C : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : Sym2 V → C) :
    ∃ R H, SeparatedRepresentative G c R H := by
  classical
  induction hsize : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    cases isEmpty_or_nonempty V with
    | inl hV =>
      obtain ⟨R, hR⟩ := exists_colorRepresentative G c
      exact ⟨R, R, hR, le_rfl, fun e he hnot ↦ (hnot he).elim, fun a ↦ isEmptyElim a⟩
    | inr hV =>
      obtain ⟨R, S, hmax⟩ := exists_maxRepresentativeComponent G c
      obtain ⟨X, hsub, hbridge, hinside, hcross⟩ := hmax.good_bridge_set
      have hlt : Fintype.card (↑(Sᶜ) : Set V) < n := by
        have hc : Fintype.card (↑(Sᶜ) : Set V) = Sᶜ.card :=
          Fintype.card_of_finset' Sᶜ (fun _ ↦ Iff.rfl)
        rw [hc, card_compl]
        have hpos := hmax.component.nonempty.card_pos
        have hle := S.card_le_univ
        omega
      obtain ⟨B, D, hBD⟩ := ih _ hlt (remainderGraph G R c S)
        (inducedColor c (↑(Sᶜ) : Set V)) rfl
      exact ⟨_, _, separated_splice hmax X hsub hbridge hinside hcross hBD⟩

end Erdos1105

#print axioms Erdos1105.exists_separatedRepresentative
