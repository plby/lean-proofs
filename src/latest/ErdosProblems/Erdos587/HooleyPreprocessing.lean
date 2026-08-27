import ErdosProblems.Erdos587.HooleyMassBalance
import ErdosProblems.Erdos587.SubgroupStability

/-! # Mass balancing and subgroup stabilization with one deletion budget -/

open scoped BigOperators

namespace Erdos587.CFP

theorem delta_exists_balanced_stable_subset {G : Type*} [AddGroup G]
    (φ : ℤ → G) (A : Finset ℤ) (L s r I : ℕ) (hs : 0 < s)
    (hpos : ∀ a ∈ A, 0 ≤ a) (hsum : ∑ a ∈ A, a ≤ (2 : ℤ) ^ L)
    (hindex : ∀ D ⊆ A, A.card ≤ 3 * D.card →
      (generatedSubgroup φ D).FiniteIndex ∧ (generatedSubgroup φ D).index ≤ I)
    (hbudget : 3 * (4 * s * (L + 1) + (I + 1) * r) ≤ 2 * A.card)
    (hreserve : I * r + r ≤ s) :
    ∃ C ⊆ A, A.card ≤ C.card + (4 * s * (L + 1) + I * r) ∧
      (generatedSubgroup φ C).FiniteIndex ∧ (generatedSubgroup φ C).index ≤ I ∧
      (∀ D ⊆ C, C.card ≤ D.card + r → generatedSubgroup φ D = generatedSubgroup φ C) ∧
      ∀ S ⊆ C, S.card ≤ r → ∑ a ∈ S, a ≤ ∑ a ∈ C \ S, a := by
  classical
  obtain ⟨B, hBA, hcostB, hbalanced⟩ := delta_exists_mass_balanced_subset A (4 * s) L hpos hsum
  have hindexB (D : Finset ℤ) (hDB : D ⊆ B) (hcostD : B.card ≤ D.card + (I + 1) * r) :
      (generatedSubgroup φ D).FiniteIndex ∧ (generatedSubgroup φ D).index ≤ I := by
    apply hindex D (hDB.trans hBA)
    omega
  let ψ : Unit → ℤ → G := fun _ => φ
  obtain ⟨C, hCB, hcostC, hstable⟩ := exists_subset_with_stable_generatedSubgroups ψ B r I
    (fun D hDB hcost _ => hindexB D hDB (by simpa only [Fintype.card_unit, one_mul] using hcost))
  simp only [Fintype.card_unit, one_mul] at hcostC
  have hcostC' : B.card ≤ C.card + (I + 1) * r := by nlinarith
  obtain ⟨hfinite, hI⟩ := hindexB C hCB hcostC'
  refine ⟨C, hCB.trans hBA, by omega, hfinite, hI,
    (fun D hDC hcost => hstable D hDC hcost ()), ?_⟩
  intro S hSC hScard
  let W := (B \ C) ∪ S
  have hWB : W ⊆ B := Finset.union_subset Finset.sdiff_subset (hSC.trans hCB)
  have hWcard : W.card ≤ s := by
    have hrem : (B \ C).card ≤ I * r := by
      rw [Finset.card_sdiff_of_subset hCB]
      omega
    exact (Finset.card_union_le _ _).trans ((Nat.add_le_add hrem hScard).trans hreserve)
  have hremaining : B \ W = C \ S := by
    ext a
    simp only [W, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨haB, ha⟩
      exact ⟨by by_contra haC; exact ha (Or.inl ⟨haB, haC⟩), fun haS => ha (Or.inr haS)⟩
    · rintro ⟨haC, haS⟩
      exact ⟨hCB haC, fun ha => ha.elim (fun h => h.2 haC) haS⟩
  have hmass := delta_small_reserve_mass B W s hs hWB hWcard
    (fun a ha => hpos a (hBA ha)) (by
      intro a ha
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbalanced a ha)
  rw [hremaining] at hmass
  have hsumS : (∑ a ∈ S, a) ≤ ∑ a ∈ W, a :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      (fun a ha _ => hpos a (hBA (hWB ha)))
  have hsumW : 0 ≤ ∑ a ∈ W, a := Finset.sum_nonneg (fun a ha => hpos a (hBA (hWB ha)))
  linarith

end Erdos587.CFP
