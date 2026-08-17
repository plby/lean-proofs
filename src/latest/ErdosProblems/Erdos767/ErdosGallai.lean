import ErdosProblems.Erdos767.EGApi

namespace E767EGConditional

open scoped Sym2

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

/-- Every genuine cycle has length at most `c`. -/
def CycleLengthAtMost {V : Type u} (G : SimpleGraph V) (c : ℕ) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length ≤ c

/-- The only geometric input required by the Erdős--Gallai induction: in a
finite two-connected graph whose order exceeds the cycle bound, some vertex
has doubled degree at most that bound.  Dirac's circumference theorem gives
this immediately from `circumference ≥ min(order, 2 * minimumDegree)`. -/
def DiracCircumferencePrinciple : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (c : ℕ),
    2 ≤ c → c < Fintype.card W → H.Preconnected →
    (∀ w, (E767EGApi.deleteVertex H w).Preconnected) →
    CycleLengthAtMost H c → ∃ w, 2 * H.degree w ≤ c

lemma cycleLengthAtMost_induce {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : ℕ) (h : CycleLengthAtMost G c) (S : Set V) :
    CycleLengthAtMost (G.induce S) c := by
  intro v p hp
  let f : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  have hm : (p.map f.toHom).IsCycle := hp.map f.injective
  simpa using h (f v) (p.map f.toHom) hm

private lemma twice_card_edgeFinset_le_complete {V : Type u}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) := by
  calc
    2 * G.edgeFinset.card ≤ 2 * (Fintype.card V).choose 2 :=
      Nat.mul_le_mul_left 2 G.card_edgeFinset_le_card_choose_two
    _ = Fintype.card V * (Fintype.card V - 1) := by
      rw [Nat.choose_two_right, Nat.mul_comm 2,
        Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self _)]

private lemma component_support_toFinset_ne_univ
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C : G.ConnectedComponent) (hC : C.supp ≠ Set.univ) :
    C.supp.toFinset ≠ (Finset.univ : Finset V) := by
  intro h
  apply hC
  ext x
  have hx := Finset.ext_iff.mp h x
  simpa using hx

private lemma component_support_toFinset_nonempty
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C : G.ConnectedComponent) (hC : C.supp.Nonempty) :
    C.supp.toFinset.Nonempty := by
  obtain ⟨x, hx⟩ := hC
  exact ⟨x, Set.mem_toFinset.mpr hx⟩

private lemma compl_nonempty_of_ne_univ {V : Type u} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : S ≠ Finset.univ) : Sᶜ.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hEmpty
  apply hS
  ext x
  have hx : x ∉ Sᶜ := by simp [hEmpty]
  simpa using hx

private lemma compl_ne_univ_of_nonempty {V : Type u} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : S.Nonempty) : Sᶜ ≠ Finset.univ := by
  obtain ⟨x, hx⟩ := hS
  intro h
  have hxc : x ∈ Sᶜ := by simp [h]
  exact (Finset.mem_compl.mp hxc) hx

private lemma exists_disconnected_partition
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hpre : ¬ G.Preconnected) :
    ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
      S ≠ Finset.univ ∧ Sᶜ ≠ Finset.univ ∧
      ∀ u v, G.Adj u v → (u ∈ S ↔ v ∈ S) := by
  obtain ⟨C, hCnon, hCproper⟩ :=
    E767EGApi.exists_component_with_nonempty_proper_support G hpre
  have hSnon : C.supp.toFinset.Nonempty :=
    component_support_toFinset_nonempty G C hCnon
  have hSproper : C.supp.toFinset ≠ Finset.univ :=
    component_support_toFinset_ne_univ G C hCproper
  have hSCnon : C.supp.toFinsetᶜ.Nonempty :=
    compl_nonempty_of_ne_univ C.supp.toFinset hSproper
  have hSCproper : C.supp.toFinsetᶜ ≠ Finset.univ :=
    compl_ne_univ_of_nonempty C.supp.toFinset hSnon
  refine ⟨C.supp.toFinset, hSnon, hSCnon, hSproper, hSCproper, ?_⟩
  intro u v huv
  simpa using E767EGApi.component_closed G C u v huv

private lemma combine_disconnected_bounds
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) (S : Finset V)
    (hSnon : S.Nonempty) (hSCnon : Sᶜ.Nonempty)
    (hedge : G.edgeFinset.card =
      (G.induce (S : Set V)).edgeFinset.card +
        (G.induce (↑(Sᶜ) : Set V)).edgeFinset.card)
    (ihS : 2 * (G.induce (S : Set V)).edgeFinset.card ≤ c * (S.card - 1))
    (ihT : 2 * (G.induce (↑(Sᶜ) : Set V)).edgeFinset.card ≤ c * (Sᶜ.card - 1)) :
    2 * G.edgeFinset.card ≤ c * (Fintype.card V - 1) := by
  have hparts : (S.card - 1) + (Sᶜ.card - 1) ≤ Fintype.card V - 1 :=
    E767EGApi.card_sub_one_add_card_sub_one_le_of_separation
      S Sᶜ (by ext; simp) (by simp) hSnon hSCnon
  calc
    2 * G.edgeFinset.card =
        2 * (G.induce (S : Set V)).edgeFinset.card +
          2 * (G.induce (↑(Sᶜ) : Set V)).edgeFinset.card := by
      rw [hedge]
      omega
    _ ≤ c * (S.card - 1) + c * (Sᶜ.card - 1) := Nat.add_le_add ihS ihT
    _ = c * ((S.card - 1) + (Sᶜ.card - 1)) := by rw [Nat.mul_add]
    _ ≤ c * (Fintype.card V - 1) := Nat.mul_le_mul_left c hparts

/-- Conditional finite Erdős--Gallai circumference bound.  All separation,
edge-count, subtype-cardinality, and induction work is internal; the sole
input is `DiracCircumferencePrinciple`. -/
theorem erdosGallai_cycle_conditional (hDirac : DiracCircumferencePrinciple.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ)
    (hc : 2 ≤ c) (hcycle : CycleLengthAtMost G c) :
    2 * G.edgeFinset.card ≤ c * (Fintype.card V - 1) := by
  induction n : Fintype.card V using Nat.strong_induction_on generalizing V G with
  | h n ih =>
      rw [← n]
      by_cases hnsmall : Fintype.card V ≤ c
      · exact (twice_card_edgeFinset_le_complete G).trans
          (Nat.mul_le_mul_right (Fintype.card V - 1) hnsmall)
      have hcn : c < Fintype.card V := by omega
      have hnthree : 3 ≤ Fintype.card V := by omega
      by_cases hpre : G.Preconnected
      · by_cases hdelete : ∀ v, (E767EGApi.deleteVertex G v).Preconnected
        · obtain ⟨v, hv⟩ := hDirac G c hc hcn hpre hdelete hcycle
          let H := E767EGApi.deleteVertex G v
          have hcardH : Fintype.card ↑(({v} : Set V)ᶜ) < Fintype.card V := by
            rw [E767EGApi.card_deleteVertex_type]
            omega
          have hind : 2 * H.edgeFinset.card ≤
              c * (Fintype.card ↑(({v} : Set V)ᶜ) - 1) :=
            ih _ (by simpa only [n] using hcardH) H
              (cycleLengthAtMost_induce G c hcycle _) rfl
          have hedge := E767EGApi.card_edgeFinset_eq_deleteVertex_add_degree G v
          have hcard : Fintype.card ↑(({v} : Set V)ᶜ) = Fintype.card V - 1 :=
            E767EGApi.card_deleteVertex_type v
          rw [hcard] at hind
          calc
            2 * G.edgeFinset.card = 2 * H.edgeFinset.card + 2 * G.degree v := by
              change 2 * G.edgeFinset.card =
                2 * (E767EGApi.deleteVertex G v).edgeFinset.card + 2 * G.degree v
              rw [hedge]
              omega
            _ ≤ c * (Fintype.card V - 1 - 1) + c := Nat.add_le_add hind hv
            _ = c * (Fintype.card V - 1) := by
              have hn : Fintype.card V - 1 = (Fintype.card V - 1 - 1) + 1 := by
                omega
              rw [hn, Nat.mul_add]
              simp
        · push Not at hdelete
          obtain ⟨v, hvdelete⟩ := hdelete
          let H := E767EGApi.deleteVertex G v
          obtain ⟨C, hCnon, hCproper⟩ :=
            E767EGApi.exists_component_with_nonempty_proper_support H hvdelete
          let e : ↑(({v} : Set V)ᶜ) ↪ V := Function.Embedding.subtype _
          let D : Finset V := C.supp.toFinset.map e
          let A : Finset V := insert v D
          let B : Finset V := Dᶜ
          have hvD : v ∉ D := by simp [D, e]
          have hmemD (x : V) :
              x ∈ D ↔ ∃ hx : x ≠ v, (⟨x, hx⟩ : ↑(({v} : Set V)ᶜ)) ∈ C.supp := by
            simp only [D, Finset.mem_map, Set.mem_toFinset]
            constructor
            · rintro ⟨y, hy, rfl⟩
              refine ⟨y.2, ?_⟩
              simpa [e] using hy
            · rintro ⟨hx, hxC⟩
              refine ⟨⟨x, hx⟩, ?_, ?_⟩
              · simpa using hxC
              · rfl
          have hDclosed {x y : V} (hxy : G.Adj x y) (hx : x ≠ v) (hy : y ≠ v) :
              (x ∈ D ↔ y ∈ D) := by
            rw [hmemD x, hmemD y]
            have hadjH : H.Adj ⟨x, hx⟩ ⟨y, hy⟩ :=
              SimpleGraph.induce_adj.mpr hxy
            have hclose := E767EGApi.component_closed H C ⟨x, hx⟩ ⟨y, hy⟩ hadjH
            constructor
            · rintro ⟨hx', hxC⟩
              refine ⟨hy, ?_⟩
              apply hclose.mp
              simpa using hxC
            · rintro ⟨hy', hyC⟩
              refine ⟨hx, ?_⟩
              apply hclose.mpr
              simpa using hyC
          have hcover : ∀ x y, G.Adj x y →
              (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) := by
            intro x y hxy
            by_cases hxv : x = v
            · subst x
              by_cases hyD : y ∈ D
              · exact Or.inl ⟨by simp [A], by simp [A, hyD]⟩
              · exact Or.inr ⟨by simp [B, hvD], by simp [B, hyD]⟩
            · by_cases hyv : y = v
              · subst y
                by_cases hxD : x ∈ D
                · exact Or.inl ⟨by simp [A, hxD], by simp [A]⟩
                · exact Or.inr ⟨by simp [B, hxD], by simp [B, hvD]⟩
              · have hiff := hDclosed hxy hxv hyv
                by_cases hxD : x ∈ D
                · have hyD : y ∈ D := hiff.mp hxD
                  exact Or.inl ⟨by simp [A, hxD], by simp [A, hyD]⟩
                · have hyD : y ∉ D := fun hyD ↦ hxD (hiff.mpr hyD)
                  exact Or.inr ⟨by simp [B, hxD], by simp [B, hyD]⟩
          have hunion : A ∪ B = Finset.univ := by
            ext x
            by_cases hxD : x ∈ D <;> simp [A, B, hxD]
          have hinterEq : A ∩ B = {v} := by
            ext x
            by_cases hxv : x = v
            · subst x
              simp [A, B, hvD]
            · by_cases hxD : x ∈ D <;> simp [A, B, hxv, hxD]
          have hinter : (A ∩ B).card ≤ 1 := by simp [hinterEq]
          have hAnon : A.Nonempty := ⟨v, by simp [A]⟩
          have hBnon : B.Nonempty := ⟨v, by simp [B, hvD]⟩
          have hAproper : A ≠ Finset.univ := by
            have hnotall : ¬ ∀ z, z ∈ C.supp := by
              intro hall
              apply hCproper
              exact Set.eq_univ_of_forall hall
            push Not at hnotall
            obtain ⟨z, hz⟩ := hnotall
            intro hA
            have hzA : (z : V) ∈ A := by simp [hA]
            have hzv : (z : V) ≠ v := z.2
            have hzD : (z : V) ∈ D := by simpa [A, hzv] using hzA
            exact hz ((hmemD z).mp hzD |>.2)
          have hBproper : B ≠ Finset.univ := by
            obtain ⟨z, hz⟩ := hCnon
            have hzD : (z : V) ∈ D := by
              apply (hmemD z).mpr
              exact ⟨z.2, by simpa using hz⟩
            intro hB
            have hzB : (z : V) ∈ B := by simp [hB]
            exact (Finset.mem_compl.mp hzB) hzD
          have hAcard : Fintype.card ↑A < Fintype.card V :=
            E767EGApi.card_coe_lt_card_of_ne_univ A hAproper
          have hBcard : Fintype.card ↑B < Fintype.card V :=
            E767EGApi.card_coe_lt_card_of_ne_univ B hBproper
          let GA := G.induce (A : Set V)
          let GB := G.induce (B : Set V)
          have ihA : 2 * GA.edgeFinset.card ≤ c * (Fintype.card ↑A - 1) :=
            ih _ (by simpa only [n] using hAcard) GA
              (cycleLengthAtMost_induce G c hcycle _) rfl
          have ihB : 2 * GB.edgeFinset.card ≤ c * (Fintype.card ↑B - 1) :=
            ih _ (by simpa only [n] using hBcard) GB
              (cycleLengthAtMost_induce G c hcycle _) rfl
          have hedge :=
            E767EGApi.card_edgeFinset_eq_card_induce_add_card_induce_of_separation
              G A B hcover hinter
          have hparts : (A.card - 1) + (B.card - 1) ≤ Fintype.card V - 1 :=
            E767EGApi.card_sub_one_add_card_sub_one_le_of_separation
              A B hunion hinter hAnon hBnon
          simp only [Fintype.card_coe] at ihA ihB
          calc
            2 * G.edgeFinset.card = 2 * GA.edgeFinset.card + 2 * GB.edgeFinset.card := by
              change 2 * G.edgeFinset.card =
                2 * (G.induce (A : Set V)).edgeFinset.card +
                  2 * (G.induce (B : Set V)).edgeFinset.card
              rw [hedge]
              omega
            _ ≤ c * (A.card - 1) + c * (B.card - 1) := Nat.add_le_add ihA ihB
            _ = c * ((A.card - 1) + (B.card - 1)) := by rw [Nat.mul_add]
            _ ≤ c * (Fintype.card V - 1) := Nat.mul_le_mul_left c hparts
      · obtain ⟨S, hSnon, hSCnon, hSproper, hSCproper, hclosed⟩ :=
          exists_disconnected_partition G hpre
        have hScard : Fintype.card ↑S < Fintype.card V :=
          E767EGApi.card_coe_lt_card_of_ne_univ S hSproper
        have hSCcard : Fintype.card ↑Sᶜ < Fintype.card V :=
          E767EGApi.card_coe_lt_card_of_ne_univ Sᶜ hSCproper
        let GS := G.induce (S : Set V)
        let GT := G.induce (↑(Sᶜ) : Set V)
        have hScard' : Fintype.card ↑(S : Set V) < Fintype.card V := by
          exact hScard
        have hSCcard' : Fintype.card ↑(↑(Sᶜ) : Set V) < Fintype.card V := by
          exact hSCcard
        have ihS := ih _ (by simpa only [n] using hScard') GS
          (cycleLengthAtMost_induce G c hcycle _) rfl
        have ihT := ih _ (by simpa only [n] using hSCcard') GT
          (cycleLengthAtMost_induce G c hcycle _) rfl
        dsimp [GS, GT] at ihS ihT
        simp only [Fintype.card_coe] at ihS ihT
        have hedge :=
          E767EGApi.card_edgeFinset_eq_card_induce_add_card_induce_compl G S hclosed
        exact combine_disconnected_bounds G c S hSnon hSCnon hedge ihS ihT

end

end E767EGConditional

