import ErdosProblems.Erdos547.Attachment

/-!
# Finite augmentation with an embedding invariant

This form permits constraints relating two already embedded vertices, as
needed for paired neighbourhoods in the leaf-rich case.
-/

namespace Erdos547

open Finset SimpleGraph

open scoped Classical in
theorem exists_full_copy_of_augmentation {U V : Type*} [Fintype U]
    (T : SimpleGraph U) (G : SimpleGraph V)
    (good : ∀ Q : Finset U, (T.induce (Q : Set U)).Copy G → Prop)
    (S : Finset U) (e : (T.induce (S : Set U)).Copy G) (he : good S e)
    (hnext : ∀ (Q : Finset U) (f : (T.induce (Q : Set U)).Copy G),
      good Q f → Q.card < Fintype.card U →
      ∃ Q' : Finset U, Q.card < Q'.card ∧ ∃ f' : (T.induce (Q' : Set U)).Copy G, good Q' f') :
    ∃ f : (T.induce (↑(Finset.univ : Finset U) : Set U)).Copy G, good Finset.univ f := by
  classical
  let candidates := (Finset.univ : Finset (Finset U)).filter fun Q ↦ ∃ f, good Q f
  have hstart : S ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he⟩
  obtain ⟨Q, hQ, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨S, hstart⟩
  obtain ⟨f, hf⟩ := (Finset.mem_filter.mp hQ).2
  have hcard : Q.card = Fintype.card U := by
    by_contra hne
    have hlt : Q.card < Fintype.card U := lt_of_le_of_ne (Finset.card_le_univ Q) hne
    obtain ⟨Q', hQQ', f', hf'⟩ := hnext Q f hf hlt
    have hmem : Q' ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, f', hf'⟩
    exact (not_lt_of_ge (hmax Q' hmem)) hQQ'
  have hfull : Q = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ Q)
    (by simpa using hcard.ge)
  subst Q
  exact ⟨f, hf⟩

end Erdos547

#print axioms Erdos547.exists_full_copy_of_augmentation
