import ErdosProblems.Erdos19.MatchingPartner

/-! # Reservoir neighbors whose matching partners avoid forbidden vertices -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem exists_matching_partner_neighbor_set {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching)
    (R : _root_.SimpleGraph V) (u : V) (Z : Finset V) :
    ∃ X : Finset V,
      R.degree u ≤ X.card + 2 * Z.card + M.vertsᶜ.ncard ∧
      ∀ x ∈ X, M.Adj x (matchingPartner M hM x) ∧
        R.Adj u (matchingPartner M hM x) ∧ x ∉ Z ∧ matchingPartner M hM x ∉ Z := by
  classical
  let p := matchingPartner M hM
  let D := (Z ∪ Z.image p) ∪ M.vertsᶜ.toFinset
  let A := R.neighborFinset u \ D
  let X := A.image p
  have hD : D.card ≤ 2 * Z.card + M.vertsᶜ.ncard := by
    have h₁ := card_union_le (Z ∪ Z.image p) M.vertsᶜ.toFinset
    have h₂ := card_union_le Z (Z.image p)
    have h₃ : (Z.image p).card ≤ Z.card := card_image_le
    have h₄ : M.vertsᶜ.toFinset.card = M.vertsᶜ.ncard :=
      (Set.ncard_eq_toFinset_card' _).symm
    dsimp only [D]
    omega
  have hXcard : X.card = A.card := card_image_of_injective _ p.injective
  have hA : R.degree u ≤ A.card + D.card := by
    have h := card_le_card_sdiff_add_card (s := R.neighborFinset u) (t := D)
    simpa only [card_neighborFinset_eq_degree] using h
  refine ⟨X, by omega, ?_⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
  obtain ⟨haR, haD⟩ := mem_sdiff.mp ha
  have haZ : a ∉ Z := fun h ↦ haD (mem_union_left _ (mem_union_left _ h))
  have haimage : a ∉ Z.image p := fun h ↦ haD (mem_union_left _ (mem_union_right _ h))
  have haM : a ∈ M.verts := by
    by_contra haM
    exact haD (mem_union_right _ (Set.mem_toFinset.mpr haM))
  have hpaM : p a ∈ M.verts := (matchingPartner_mem_iff M hM a).mpr haM
  have hppa : p (p a) = a := matchingPartner_apply_apply M hM a
  have hpaZ : p a ∉ Z := by
    intro h
    exact haimage (mem_image.mpr ⟨p a, h, hppa⟩)
  refine ⟨matchingPartner_adj M hM hpaM, ?_, hpaZ, ?_⟩
  · change R.Adj u (p (p a))
    rw [hppa]
    simpa only [mem_neighborFinset] using haR
  · change p (p a) ∉ Z
    simpa only [hppa] using haZ

#print axioms exists_matching_partner_neighbor_set

end Erdos19
