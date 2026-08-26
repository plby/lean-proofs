import ErdosProblems.Erdos556.CubeInequality

/-!
# The proposed equality configurations of the cube inequality

A tiling consists of disjoint edge profiles of weight one and face
profiles of weight two. Total weight four then forces these profiles
to cover all eight cube vertices.
-/

namespace Erdos556

open Finset

structure IsCubeTiling (w : CubeProfile → ℝ) : Prop where
  normalized : ∀ p, 0 < w p →
    (profileDimension p = 1 ∧ w p = 1) ∨ (profileDimension p = 2 ∧ w p = 2)
  disjoint : ∀ p q, p ≠ q → 0 < w p → 0 < w q →
    Disjoint (profileVertices p) (profileVertices q)

open scoped Classical in
noncomputable def positiveCubeProfiles (w : CubeProfile → ℝ) : Finset CubeProfile :=
  univ.filter (fun p => 0 < w p)

theorem IsCubeWeight.eq_zero_of_not_pos {w : CubeProfile → ℝ} (hw : IsCubeWeight w)
    (p : CubeProfile) (hp : ¬ 0 < w p) : w p = 0 :=
  le_antisymm (le_of_not_gt hp) (hw.nonneg p)

theorem IsCubeWeight.sum_positive_profiles {w : CubeProfile → ℝ} (hw : IsCubeWeight w) :
    (∑ p ∈ positiveCubeProfiles w, w p) = 4 := by
  classical
  calc
    (∑ p ∈ positiveCubeProfiles w, w p) = ∑ p, w p := by
      apply sum_subset (subset_univ _)
      intro p _ hp
      apply hw.eq_zero_of_not_pos
      intro h
      exact hp (mem_filter.mpr ⟨mem_univ p, h⟩)
    _ = 4 := hw.sum_four

theorem IsCubeTiling.card_eq_twice_weight {w : CubeProfile → ℝ} (ht : IsCubeTiling w)
    (p : CubeProfile) (hp : 0 < w p) : ((profileVertices p).card : ℝ) = 2 * w p := by
  rcases ht.normalized p hp with ⟨hd, hw⟩ | ⟨hd, hw⟩ <;>
    rw [profileVertices_card, hd, hw] <;> norm_num

theorem IsCubeTiling.cover {w : CubeProfile → ℝ} (ht : IsCubeTiling w) (hw : IsCubeWeight w) :
    (positiveCubeProfiles w).biUnion profileVertices = univ := by
  classical
  have hdisj : (positiveCubeProfiles w : Set CubeProfile).Pairwise
      (fun p q => Disjoint (profileVertices p) (profileVertices q)) := by
    intro p hp q hq hpq
    exact ht.disjoint p q hpq (mem_filter.mp hp).2 (mem_filter.mp hq).2
  have hsumR : (∑ p ∈ positiveCubeProfiles w, ((profileVertices p).card : ℝ)) = 8 := by
    calc
      (∑ p ∈ positiveCubeProfiles w, ((profileVertices p).card : ℝ)) =
          ∑ p ∈ positiveCubeProfiles w, 2 * w p :=
        sum_congr rfl (fun p hp => ht.card_eq_twice_weight p (mem_filter.mp hp).2)
      _ = 2 * ∑ p ∈ positiveCubeProfiles w, w p := (mul_sum _ _ _).symm
      _ = 8 := by rw [hw.sum_positive_profiles]; norm_num
  have hsum : (∑ p ∈ positiveCubeProfiles w, (profileVertices p).card) = 8 := by exact_mod_cast hsumR
  have hcard : ((positiveCubeProfiles w).biUnion profileVertices).card = 8 := by
    rw [card_biUnion hdisj, hsum]
  have huniv : (univ : Finset CubeVertex).card = 8 := by decide
  exact eq_of_subset_of_card_le (subset_univ _) (by omega)

theorem IsCubeTiling.sum_intersection_cards {w : CubeProfile → ℝ}
    (ht : IsCubeTiling w) (hw : IsCubeWeight w) (S : Finset CubeVertex) :
    (∑ p ∈ positiveCubeProfiles w, (profileVertices p ∩ S).card) = S.card := by
  classical
  have hdisj : (positiveCubeProfiles w : Set CubeProfile).Pairwise
      (fun p q => Disjoint (profileVertices p ∩ S) (profileVertices q ∩ S)) := by
    intro p hp q hq hpq
    exact (ht.disjoint p q hpq (mem_filter.mp hp).2 (mem_filter.mp hq).2).mono
      inter_subset_left inter_subset_left
  have hcover : (positiveCubeProfiles w).biUnion (fun p => profileVertices p ∩ S) = S := by
    ext v
    constructor
    · intro hv
      obtain ⟨p, hp, hvp⟩ := mem_biUnion.mp hv
      exact (mem_inter.mp hvp).2
    · intro hv
      have hall : v ∈ (positiveCubeProfiles w).biUnion profileVertices := by
        rw [ht.cover hw]
        exact mem_univ v
      obtain ⟨p, hp, hvp⟩ := mem_biUnion.mp hall
      exact mem_biUnion.mpr ⟨p, hp, mem_inter.mpr ⟨hvp, hv⟩⟩
  rw [← card_biUnion hdisj, hcover]

#print axioms IsCubeTiling.cover
#print axioms IsCubeTiling.sum_intersection_cards

end Erdos556
