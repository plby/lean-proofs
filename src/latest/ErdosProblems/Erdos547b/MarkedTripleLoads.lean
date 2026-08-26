/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.MarkedTripleEmbedding

/-!
# Occupancy accounting for marked branches and four private pairs

Only the branch root and prescribed marks use the intermediate cluster.
Four disjoint pairs retain a usable pair below the three-cluster load.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoMarkedTripleLoads

open Finset

theorem image_inter_eq_marked
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (f : A → B) (root : A) (special : Finset A) (C X Y : Finset B)
    (hroot : f root ∈ C) (hspecial : ∀ a ∈ special, f a ∈ C)
    (hother : ∀ a, a ≠ root → a ∉ special → f a ∈ X ∪ Y)
    (hCX : Disjoint C X) (hCY : Disjoint C Y) :
    (Finset.univ.image f) ∩ C = (insert root special).image f := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).1
    have haC := (Finset.mem_inter.mp hv).2
    apply Finset.mem_image.mpr
    refine ⟨a, ?_, rfl⟩
    by_contra hnot
    have ha : a ≠ root ∧ a ∉ special := by simpa only [Finset.mem_insert, not_or] using hnot
    rcases Finset.mem_union.mp (hother a ha.1 ha.2) with hx | hy
    · exact Finset.disjoint_left.mp hCX haC hx
    · exact Finset.disjoint_left.mp hCY haC hy
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, ?_⟩
    rcases Finset.mem_insert.mp ha with ha | ha
    · simpa only [ha] using hroot
    · exact hspecial a ha

theorem intermediate_load_bound
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (f : A → B) (root : A) (special : Finset A) (C X Y : Finset B)
    (hroot : f root ∈ C) (hspecial : ∀ a ∈ special, f a ∈ C)
    (hother : ∀ a, a ≠ root → a ∉ special → f a ∈ X ∪ Y)
    (hCX : Disjoint C X) (hCY : Disjoint C Y) :
    ((Finset.univ.image f) ∩ C).card ≤ 1 + special.card := by
  rw [image_inter_eq_marked f root special C X Y hroot hspecial hother hCX hCY]
  have h := Finset.card_image_le (s := insert root special) (f := f)
  have hi := Finset.card_insert_le root special
  omega

theorem three_mul_intermediate_load_le
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (f : A → B) (root : A) (special : Finset A) (C X Y : Finset B)
    (hroot : f root ∈ C) (hspecial : ∀ a ∈ special, f a ∈ C)
    (hother : ∀ a, a ≠ root → a ∉ special → f a ∈ X ∪ Y)
    (hCX : Disjoint C X) (hCY : Disjoint C Y) (hsize : 3 ≤ Fintype.card A) :
    3 * ((Finset.univ.image f) ∩ C).card ≤ Fintype.card A + 3 * special.card := by
  have h := intermediate_load_bound f root special C X Y hroot hspecial hother hCX hCY
  omega

theorem image_subset_three_sets
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (f : A → B) (root : A) (special : Finset A) (C X Y : Finset B)
    (hroot : f root ∈ C) (hspecial : ∀ a ∈ special, f a ∈ C)
    (hother : ∀ a, a ≠ root → a ∉ special → f a ∈ X ∪ Y) :
    Finset.univ.image f ⊆ C ∪ X ∪ Y := by
  intro v hv
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
  by_cases har : a = root
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (har ▸ hroot))
  by_cases ha : a ∈ special
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hspecial a ha))
  rcases Finset.mem_union.mp (hother a har ha) with hx | hy
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  · exact Finset.mem_union_right _ hy

theorem exists_private_pair_with_two_large_sides
    {B : Type*} [DecidableEq B] (whole : Fin 4 → Fin 2 → Finset B)
    (used : Finset B) (N : ℕ) (γ : ℝ) (hγ : γ ≤ 1 / 4)
    (hcard : ∀ i c, (whole i c).card = N)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (whole i 0 ∪ whole i 1) (whole j 0 ∪ whole j 1))
    (hused : used.card ≤ 3 * N) :
    ∃ i : Fin 4, ∀ c : Fin 2, γ * N ≤ ((whole i c \ used).card : ℝ) := by
  by_contra! h
  choose side hside using h
  let pair := fun i : Fin 4 => whole i 0 ∪ whole i 1
  let occupied := fun i : Fin 4 => used ∩ pair i
  have hlower (i : Fin 4) : (1 - γ) * N < ((occupied i).card : ℝ) := by
    have hsplit := Finset.card_sdiff_add_card_inter (whole i (side i)) used
    rw [hcard] at hsplit
    have hsplitR : ((whole i (side i) \ used).card : ℝ) + (whole i (side i) ∩ used).card = N := by
      exact_mod_cast hsplit
    have hsub : whole i (side i) ∩ used ⊆ occupied i := by
      intro v hv
      refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).2, ?_⟩
      rcases Erdos547b.RegularPair.OrderedRootedForest.fin_two_eq_zero_or_one (side i) with hs | hs
      · exact Finset.mem_union_left _ (by simpa only [hs] using (Finset.mem_inter.mp hv).1)
      · exact Finset.mem_union_right _ (by simpa only [hs] using (Finset.mem_inter.mp hv).1)
    have hsubR : ((whole i (side i) ∩ used).card : ℝ) ≤ (occupied i).card := by exact_mod_cast Finset.card_le_card hsub
    linarith only [hsplitR, hsubR, hside i]
  have hoccDisj : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ∀ j ∈ Finset.univ, i ≠ j → Disjoint (occupied i) (occupied j) := by
    intro i _ j _ hij
    exact (hdisjoint i j hij).mono Finset.inter_subset_right Finset.inter_subset_right
  have hsum : (∑ i : Fin 4, (occupied i).card) ≤ used.card := by
    rw [← Finset.card_biUnion hoccDisj]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun i _ => Finset.inter_subset_left))
  have hsumR : (∑ i : Fin 4, ((occupied i).card : ℝ)) ≤ used.card := by exact_mod_cast hsum
  have hstrict := Finset.sum_lt_sum_of_nonempty
    (show (Finset.univ : Finset (Fin 4)).Nonempty by simp)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hlower i)
  have hstrictR : 4 * ((1 - γ) * N) < ∑ i : Fin 4, ((occupied i).card : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hstrict
  have husedR : (used.card : ℝ) ≤ 3 * N := by exact_mod_cast hused
  have hγN := mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith only [hsumR, hstrictR, husedR, hγN]

end Erdos547b.ZhaoMarkedTripleLoads

#print axioms Erdos547b.ZhaoMarkedTripleLoads.image_inter_eq_marked
#print axioms Erdos547b.ZhaoMarkedTripleLoads.three_mul_intermediate_load_le
#print axioms Erdos547b.ZhaoMarkedTripleLoads.exists_private_pair_with_two_large_sides
