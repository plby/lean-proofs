import ErdosProblems.Erdos556.CubeEdgeEquality
import ErdosProblems.Erdos556.CubeFaceEquality
import ErdosProblems.Erdos556.CubeTilingGradients

/-!
# Equality in the weighted cube inequality

The only zero-energy admissible weights are cube tilings. Terminal
equality is classified directly; strict derivatives at tilings exclude
every nontrivial preceding compression step.
-/

namespace Erdos556

open Finset

theorem cube_tiling_of_zero_energy_disjoint_high_support (w : CubeProfile → ℝ) (hw : IsCubeWeight w)
    (hdisj : (positiveHighProfiles w : Set CubeProfile).Pairwise
      (fun p q => Disjoint (profileVertices p) (profileVertices q)))
    (hzero : cubeEnergy w = 0) : IsCubeTiling w := by
  classical
  by_cases hface : ∃ p : CubeProfile, profileDimension p = 2 ∧ 0 < w p
  · obtain ⟨p, hpdim, hp⟩ := hface
    obtain ⟨i, b, rfl⟩ := (profileDimension_two_iff p).mp hpdim
    apply hw.tiling_of_zero_energy_face_support i b hp ?_ hzero
    intro r hr hrp hrq
    by_contra hrzero
    have hrpos : 0 < w r := lt_of_le_of_ne (hw.nonneg r) (Ne.symm hrzero)
    have hpH : cubeFace i b ∈ positiveHighProfiles w :=
      mem_filter.mpr ⟨mem_univ _, by rw [cubeFace_dimension], hp⟩
    have hrH : r ∈ positiveHighProfiles w := mem_filter.mpr ⟨mem_univ _, hr, hrpos⟩
    exact hrq (high_profile_disjoint_from_face i b r hr (hdisj hpH hrH hrp.symm))
  · apply hw.tiling_of_zero_energy_high_support ?_ hzero
    intro p hpdim hpne
    have hdim3 : profileDimension p ≠ 3 := fun h => hpne ((profileDimension_three_iff p).mp h)
    have hmax := profileDimension_le_three p
    have hdim2 : profileDimension p = 2 := by omega
    exact hw.eq_zero_of_not_pos p (fun h => hface ⟨p, hdim2, h⟩)

theorem cubeTransfer_energy_lt_of_tiling {w : CubeProfile → ℝ} (hw : IsCubeWeight w)
    (p q : CubeProfile) (hpq : p ≠ q) (hp : 0 < w p) (hq : 0 < w q)
    (hpdim : 2 ≤ profileDimension p) (hqdim : 2 ≤ profileDimension q)
    (hover : cubeOverlap p q = 1) (ht : IsCubeTiling (cubeTransfer w p q)) :
    cubeEnergy (cubeTransfer w p q) < cubeEnergy w := by
  have hw' := hw.transfer p q hpq hp hpdim hqdim
  have hp' : 0 < cubeTransfer w p q p := by
    rw [cubeTransfer_at_target w p q hpq]
    exact add_pos hp hq
  have hgrad := ht.gradient_high_profile_gt hw' p q hp' hpdim hqdim hpq hover
  have hdiff := cubeGradient_shift_difference w p q (w q) hover
  change cubeGradient (cubeTransfer w p q) p - cubeGradient (cubeTransfer w p q) q =
    cubeGradient w p - cubeGradient w q at hdiff
  have hneg : cubeGradient w p - cubeGradient w q < 0 := by linarith
  have hprod := mul_neg_of_pos_of_neg hq hneg
  rw [cubeTransfer, cubeEnergy_shift w p q (w q) hover]
  linarith

theorem cube_tiling_of_zero_energy (w : CubeProfile → ℝ) (hw : IsCubeWeight w)
    (hzero : cubeEnergy w = 0) : IsCubeTiling w := by
  classical
  have aux : ∀ M : ℕ, ∀ w : CubeProfile → ℝ, IsCubeWeight w →
      (positiveHighProfiles w).card = M → cubeEnergy w = 0 → IsCubeTiling w := by
    intro M
    induction M using Nat.strong_induction_on with
    | h M ih =>
        intro w hw hM hzero
        by_cases hd : (positiveHighProfiles w : Set CubeProfile).Pairwise
            (fun p q => Disjoint (profileVertices p) (profileVertices q))
        · exact cube_tiling_of_zero_energy_disjoint_high_support w hw hd hzero
        simp only [Set.Pairwise] at hd
        push Not at hd
        obtain ⟨p, hpH, q, hqH, hpq, hnot⟩ := hd
        have hpdim := (mem_filter.mp hpH).2.1
        have hqdim := (mem_filter.mp hqH).2.1
        have hp := (mem_filter.mp hpH).2.2
        have hq := (mem_filter.mp hqH).2.2
        have hover : cubeOverlap p q = 1 := by simp only [cubeOverlap, if_neg hnot]
        have impossible (p q : CubeProfile) (hpq : p ≠ q) (hp : 0 < w p) (hq : 0 < w q)
            (hpdim : 2 ≤ profileDimension p) (hqdim : 2 ≤ profileDimension q)
            (hover : cubeOverlap p q = 1)
            (hE : cubeEnergy (cubeTransfer w p q) ≤ cubeEnergy w) : False := by
          have hw' := hw.transfer p q hpq hp hpdim hqdim
          have hcard := positiveHighProfiles_transfer_card_lt hw p q hpq hp hq hpdim hqdim
          have hz : cubeEnergy (cubeTransfer w p q) = 0 :=
            le_antisymm (by rwa [hzero] at hE) (cube_energy_nonneg _ hw')
          have ht := ih (positiveHighProfiles (cubeTransfer w p q)).card (by omega)
            (cubeTransfer w p q) hw' rfl hz
          have hlt := cubeTransfer_energy_lt_of_tiling hw p q hpq hp hq hpdim hqdim hover ht
          rw [hz, hzero] at hlt
          exact hlt.false
        rcases cubeTransfer_nonincrease_or_reverse w p q (hw.nonneg p) (hw.nonneg q) hover with hE | hE
        · exact (impossible p q hpq hp hq hpdim hqdim hover hE).elim
        · have hqp : cubeOverlap q p = 1 := (cubeOverlap_symm q p).trans hover
          exact (impossible q p hpq.symm hq hp hqdim hpdim hqp hE).elim
  exact aux (positiveHighProfiles w).card w hw rfl hzero

theorem IsCubeTiling.energy_eq_zero {w : CubeProfile → ℝ} (ht : IsCubeTiling w)
    (hw : IsCubeWeight w) : cubeEnergy w = 0 := by
  classical
  have hdiag (p q : CubeProfile) (hpq : p ≠ q) : cubeOverlap p q * w p * w q = 0 := by
    by_cases hp : 0 < w p
    · by_cases hq : 0 < w q
      · simp only [cubeOverlap, if_pos (ht.disjoint p q hpq hp hq), zero_mul]
      · rw [hw.eq_zero_of_not_pos q hq, mul_zero]
    · rw [hw.eq_zero_of_not_pos p hp, mul_zero, zero_mul]
  rw [cubeEnergy_eq, cubeBilinear_eq_diagonal w hdiag, cubeLinear, ← sum_sub_distrib]
  apply sum_eq_zero
  intro p _
  by_cases hp : 0 < w p
  · rcases ht.normalized p hp with ⟨hd, he⟩ | ⟨hd, he⟩ <;> rw [hd, he] <;> norm_num
  · rw [hw.eq_zero_of_not_pos p hp]
    ring

theorem cube_energy_eq_zero_iff (w : CubeProfile → ℝ) (hw : IsCubeWeight w) :
    cubeEnergy w = 0 ↔ IsCubeTiling w :=
  ⟨cube_tiling_of_zero_energy w hw, fun ht => ht.energy_eq_zero hw⟩

#print axioms cube_energy_eq_zero_iff

end Erdos556
