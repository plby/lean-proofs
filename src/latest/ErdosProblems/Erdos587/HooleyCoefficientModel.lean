import ErdosProblems.Erdos587.HooleyModelBudget

/-! # Exact transfer from an integer model to its coefficient vectors -/

open scoped Pointwise
open Erdos587.GeneralizedAP

namespace Erdos587.CFP

lemma delta_generatedSubgroup_image {α G : Type*} [AddGroup G] [DecidableEq G]
    (φ : α → G) (A : Finset α) : generatedSubgroup id (A.image φ) = generatedSubgroup φ A := by
  simp only [generatedSubgroup, Finset.coe_image, Set.image_id]

lemma delta_centeredCoordinates_injOn (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) : Set.InjOn P.centeredCoordinates A := by
  intro a ha b hb h
  have hh := congrArg P.nvLinearEvalHom h
  rwa [P.linearEval_centeredCoordinates hzero (hA ha),
    P.linearEval_centeredCoordinates hzero (hA hb)] at hh

lemma delta_eval_centered_image (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) :
    (A.image P.centeredCoordinates).image P.nvLinearEvalHom = A := by
  rw [Finset.image_image]
  calc
    _ = A.image id :=
      Finset.image_congr (fun a ha => P.linearEval_centeredCoordinates hzero (hA ha))
    _ = A := Finset.image_id

lemma delta_eval_injOn_centered_image (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) :
    Set.InjOn P.nvLinearEvalHom (A.image P.centeredCoordinates) := by
  intro u hu v hv h
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  rw [P.linearEval_centeredCoordinates hzero (hA ha),
    P.linearEval_centeredCoordinates hzero (hA hb)] at h
  exact congrArg P.centeredCoordinates h

lemma delta_centeredCoordinates_abs_bound (P : GeneralizedAP) (a : ℤ) (i : Fin P.rank) :
    |P.centeredCoordinates a i| ≤ (P.length i : ℤ) := by
  have hb := P.centeredCoordinates_bounds a i
  have hz : (P.coordinates 0 i : ℤ) ≤ (P.length i : ℤ) := by
    exact_mod_cast Nat.le_of_lt_succ (P.coordinates 0 i).isLt
  have hzpos : (0 : ℤ) ≤ (P.coordinates 0 i : ℤ) := by positivity
  rw [abs_le]
  constructor <;> omega

lemma delta_subset_centered_image (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier)
    (V : Finset (Fin P.rank → ℤ)) (hV : V ⊆ A.image P.centeredCoordinates) :
    ∃ B ⊆ A, B.image P.centeredCoordinates = V ∧ B.card = V.card := by
  obtain ⟨B, hBA, hBV⟩ := Finset.subset_image_iff.mp hV
  refine ⟨B, hBA, hBV, ?_⟩
  rw [← hBV, Finset.card_image_of_injOn ((delta_centeredCoordinates_injOn P A hzero hA).mono hBA)]

theorem delta_centered_image_robust_spanning (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) (k : ℕ)
    (hspan : ∀ B ⊆ A, k ≤ B.card →
      Submodule.span ℝ ((intCastVec ∘ P.centeredCoordinates) '' (B : Set ℤ)) = ⊤) :
    ∀ V ⊆ A.image P.centeredCoordinates, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin P.rank → ℤ))) = ⊤ := by
  intro V hV hcard
  obtain ⟨B, hBA, hBV, hBcard⟩ := delta_subset_centered_image P A hzero hA V hV
  have hs := hspan B hBA (by rwa [hBcard])
  rw [← hBV, Finset.coe_image, Set.image_image]
  exact hs

theorem delta_centered_image_stability (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) (r : ℕ)
    (hstable : ∀ B ⊆ A, A.card ≤ B.card + r →
      generatedSubgroup P.centeredCoordinates B = generatedSubgroup P.centeredCoordinates A) :
    ∀ V ⊆ A.image P.centeredCoordinates, (A.image P.centeredCoordinates).card ≤ V.card + r →
      generatedSubgroup id V = generatedSubgroup id (A.image P.centeredCoordinates) := by
  intro V hV hcard
  obtain ⟨B, hBA, hBV, hBcard⟩ := delta_subset_centered_image P A hzero hA V hV
  rw [Finset.card_image_of_injOn (delta_centeredCoordinates_injOn P A hzero hA)] at hcard
  rw [← hBV, delta_generatedSubgroup_image, delta_generatedSubgroup_image]
  exact hstable B hBA (by rwa [hBcard])

theorem delta_centered_image_density (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) (h M r : ℕ)
    (hdense : ∀ B ⊆ A, A.card ≤ B.card + r →
      2 * (P.dilate h).boxCard < M * (h • insert 0 B).card) :
    ∀ V ⊆ A.image P.centeredCoordinates, (A.image P.centeredCoordinates).card ≤ V.card + r →
      2 * (nvCoordBox (fun i => 2 * (h * P.length i))).card <
        (2 ^ P.rank * M) * (h • insert 0 V).card := by
  intro V hV hcard
  obtain ⟨B, hBA, hBV, hBcard⟩ := delta_subset_centered_image P A hzero hA V hV
  rw [Finset.card_image_of_injOn (delta_centeredCoordinates_injOn P A hzero hA)] at hcard
  have hd := hdense B hBA (by rwa [hBcard])
  have himage : (h • insert 0 B).card ≤ (h • insert 0 V).card := by
    have hh := P.card_nsmul_le_iterated_centeredCoordinates B hzero (hBA.trans hA) h
    simpa only [iteratedImageSums, hBV] using hh
  calc
    _ ≤ 2 * (2 ^ P.rank * (P.dilate h).boxCard) :=
      Nat.mul_le_mul_left _ (delta_symmetric_model_box_card_le P h)
    _ = 2 ^ P.rank * (2 * (P.dilate h).boxCard) := by ring
    _ < 2 ^ P.rank * (M * (h • insert 0 B).card) :=
      Nat.mul_lt_mul_of_pos_left hd (by positivity)
    _ ≤ 2 ^ P.rank * (M * (h • insert 0 V).card) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ himage)
    _ = _ := by ring

lemma delta_sum_centered_image (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) :
    ∑ u ∈ A.image P.centeredCoordinates, P.nvLinearEvalHom u = ∑ a ∈ A, a := by
  rw [Finset.sum_image (delta_centeredCoordinates_injOn P A hzero hA)]
  exact Finset.sum_congr rfl (fun a ha => P.linearEval_centeredCoordinates hzero (hA ha))

theorem delta_centered_image_reserve_mass (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) (r : ℕ)
    (hreserve : ∀ B ⊆ A, B.card ≤ r → ∑ a ∈ B, a ≤ ∑ a ∈ A \ B, a) :
    ∀ V ⊆ A.image P.centeredCoordinates, V.card ≤ r →
      ∑ u ∈ V, P.nvLinearEvalHom u ≤
        ∑ u ∈ A.image P.centeredCoordinates \ V, P.nvLinearEvalHom u := by
  intro V hV hcard
  obtain ⟨B, hBA, hBV, hBcard⟩ := delta_subset_centered_image P A hzero hA V hV
  have hdiff : (A \ B).image P.centeredCoordinates = A.image P.centeredCoordinates \ V := by
    rw [Finset.image_sdiff_of_injOn (delta_centeredCoordinates_injOn P A hzero hA) hBA, hBV]
  rw [← hBV, delta_sum_centered_image P B hzero (hBA.trans hA)]
  rw [hBV, ← hdiff, delta_sum_centered_image P (A \ B) hzero (Finset.sdiff_subset.trans hA)]
  exact hreserve B hBA (by rwa [hBcard])

lemma delta_model_rank_pos (P : GeneralizedAP) (A : Finset ℤ)
    (hA : A ⊆ P.carrier) (hcard : 2 ≤ A.card) : 0 < P.rank := by
  have hbound : A.card ≤ P.boxCard := (Finset.card_le_card hA).trans P.card_carrier_le_box
  by_contra hnot
  have hz : P.boxCard = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have hi := i.isLt
    omega
  omega

end Erdos587.CFP
