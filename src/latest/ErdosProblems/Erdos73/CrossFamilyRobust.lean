import ErdosProblems.Erdos73.BrickStripNetworks

/-! Two nonempty families of robust sets glue when every cross-pair overlaps twice. -/

namespace Erdos73
noncomputable section

open SimpleGraph Finset

theorem deletionOneConnected_twoFamilyUnion
    {V I J : Type*} [DecidableEq V] [DecidableEq I] [DecidableEq J] {G : SimpleGraph V}
    (A : Finset I) (B : Finset J) (R : I → Finset V) (C : J → Finset V)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hR : ∀ a ∈ A, DeletionOneConnected G (R a))
    (hC : ∀ b ∈ B, DeletionOneConnected G (C b))
    (hover : ∀ a ∈ A, ∀ b ∈ B, 2 ≤ (R a ∩ C b).card) :
    DeletionOneConnected G (A.biUnion R ∪ B.biUnion C) := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hfirst : DeletionOneConnected G (C b ∪ A.biUnion R) := by
    apply (hC b hb).union_biUnion A R hR
    intro a' ha'
    rw [inter_comm]
    exact hover a' ha' b hb
  have hsecond := hfirst.union_biUnion B C hC (by
    intro j hj
    apply (hover a ha j hj).trans
    apply card_le_card
    apply inter_subset_inter _ subset_rfl
    intro x hx
    exact mem_union_right _ (mem_biUnion.mpr ⟨a, ha, hx⟩))
  have he : (C b ∪ A.biUnion R) ∪ B.biUnion C = A.biUnion R ∪ B.biUnion C := by
    ext x
    have hh : x ∈ C b → x ∈ B.biUnion C := fun hx => mem_biUnion.mpr ⟨b, hb, hx⟩
    simp only [mem_union]
    tauto
  exact he ▸ hsecond

end
end Erdos73
