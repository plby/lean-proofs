/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Greedy embedding of a finite tree in a graph of large minimum degree

This is Fact 1.1 in Zhao's paper, exposed in a dependency-safe module for
the Claim 6.10 dense-core argument.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoTreeMinDegreeEmbedding

open Finset Fintype SimpleGraph

private theorem exists_copy_aux {A B : Type*}
    [Fintype A] [Fintype B] [Nonempty B]
    (T : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card A = n + 1) (hT : T.IsTree)
    (hdeg : ∀ v, n ≤ G.degree v) : Nonempty (T.Copy G) := by
  classical
  induction n generalizing A B with
  | zero =>
      obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hcard
      let b : B := Classical.choice (inferInstance : Nonempty B)
      refine ⟨⟨⟨fun _ ↦ b, ?_⟩, ?_⟩⟩
      · intro u v huv
        exact False.elim (T.ne_of_adj huv (by rw [ha u, ha v]))
      · intro u v _
        rw [ha u, ha v]
  | succ n ih =>
      have hcard_large : 1 < Fintype.card A := by omega
      have hnontrivial : Nontrivial A :=
        Fintype.one_lt_card_iff_nontrivial.mp hcard_large
      obtain ⟨x, hx⟩ :=
        @IsTree.exists_vert_degree_one_of_nontrivial A T _ hnontrivial _ hT
      obtain ⟨p, hxp, hp_unique⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
      let s : Set A := {x}ᶜ
      let T' : SimpleGraph s := T.induce s
      have hcard' : Fintype.card s = n + 1 := by
        have hc := Fintype.card_subtype_compl (fun a : A ↦ a = x)
        change Fintype.card {a : A // ¬a = x} = n + 1
        rw [hc, hcard]
        simp
      have hT' : T'.IsTree := by
        exact ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hx,
          hT.isAcyclic.induce s⟩
      have hdeg' : ∀ v, n ≤ G.degree v := fun v ↦
        le_trans (Nat.le_succ n) (hdeg v)
      obtain ⟨f⟩ := ih T' G hcard' hT' hdeg'
      let ps : s := ⟨p, by simpa [s] using hxp.ne'⟩
      let usedWithoutParent : Finset B := (Finset.univ.erase ps).image f
      have hused_card : usedWithoutParent.card = n := by
        dsimp only [usedWithoutParent]
        change (Finset.image (fun a : s ↦ f a) (Finset.univ.erase ps)).card = n
        calc
          _ = (Finset.univ.erase ps).card :=
            Finset.card_image_iff.mpr fun _ _ _ _ h ↦ f.injective h
          _ = n := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ ps),
              Finset.card_univ, hcard']
            omega
      have hneighbor_card : n < (G.neighborFinset (f ps)).card := by
        rw [G.card_neighborFinset_eq_degree]
        exact lt_of_lt_of_le (Nat.lt_succ_self n) (hdeg (f ps))
      obtain ⟨w, hw_neighbor, hw_unused⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card (hused_card ▸ hneighbor_card)
      have hw_adj : G.Adj (f ps) w :=
        (G.mem_neighborFinset (f ps) w).mp hw_neighbor
      have hw_not_range : ∀ a : s, w ≠ f a := by
        intro a hwa
        by_cases ha : a = ps
        · subst a
          exact hw_adj.ne' hwa
        · apply hw_unused
          exact Finset.mem_image.mpr ⟨a,
            Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩, hwa.symm⟩
      let F : A → B := fun a ↦
        if h : a = x then w else f ⟨a, by simpa [s] using h⟩
      refine ⟨⟨⟨F, ?_⟩, ?_⟩⟩
      · intro u v huv
        by_cases hu : u = x
        · subst u
          have hvp : v = p := hp_unique v huv
          subst v
          simpa [F, ps, hxp.ne, hxp.ne'] using hw_adj.symm
        · by_cases hv : v = x
          · subst v
            have hup : u = p := hp_unique u huv.symm
            subst u
            simpa [F, ps, hxp.ne, hxp.ne'] using hw_adj
          · let us : s := ⟨u, by simpa [s] using hu⟩
            let vs : s := ⟨v, by simpa [s] using hv⟩
            have huv' : T'.Adj us vs := by simpa [T', us, vs] using huv
            have hmap := f.toHom.map_adj huv'
            simpa [F, hu, hv, us, vs] using hmap
      · intro u v huv
        by_cases hu : u = x
        · subst u
          by_cases hv : v = x
          · exact hv.symm
          · exfalso
            apply hw_not_range ⟨v, by simpa [s] using hv⟩
            simpa [F, hv] using huv
        · by_cases hv : v = x
          · subst v
            exfalso
            apply hw_not_range ⟨u, by simpa [s] using hu⟩
            simpa [F, hu] using huv.symm
          · have hsub : (⟨u, by simpa [s] using hu⟩ : s) =
                ⟨v, by simpa [s] using hv⟩ := by
              apply f.injective
              simpa [F, hu, hv] using huv
            exact Subtype.ext_iff.mp hsub

/-- A finite tree embeds in every nonempty finite graph whose minimum degree
is at least one less than the tree order. -/
theorem exists_copy {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (T : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (hT : T.IsTree)
    (hdeg : ∀ v, Fintype.card A - 1 ≤ G.degree v) :
    Nonempty (T.Copy G) := by
  classical
  apply exists_copy_aux T G (Fintype.card A - 1)
  · have hpos : 0 < Fintype.card A :=
      Fintype.card_pos_iff.mpr hT.connected.nonempty
    omega
  · exact hT
  · exact hdeg

/-- Containment-form wrapper around `exists_copy`. -/
theorem isContained {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (T : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (hT : T.IsTree)
    (hdeg : ∀ v, Fintype.card A - 1 ≤ G.degree v) :
    T.IsContained G := by
  obtain ⟨f⟩ := exists_copy T G hT hdeg
  exact f.isContained

end Erdos547b.ZhaoTreeMinDegreeEmbedding

#print axioms Erdos547b.ZhaoTreeMinDegreeEmbedding.exists_copy
#print axioms Erdos547b.ZhaoTreeMinDegreeEmbedding.isContained
