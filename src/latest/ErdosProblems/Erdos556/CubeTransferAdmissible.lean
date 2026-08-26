import ErdosProblems.Erdos556.CubeWeightTransfer

/-!
# Admissibility and support reduction under a cube transfer
-/

namespace Erdos556

open Finset

theorem cubeShift_sum (w : CubeProfile → ℝ) (p q : CubeProfile) (t : ℝ) :
    (∑ r, cubeShift w p q t r) = ∑ r, w r := by
  classical
  simp [cubeShift, Pi.add_apply, sum_add_distrib]

theorem cubeTransfer_positive_before {w : CubeProfile → ℝ} {p q r : CubeProfile}
    (hpq : p ≠ q) (hp : 0 < w p) (hr : 0 < cubeTransfer w p q r) : 0 < w r := by
  by_cases hrp : r = p
  · exact hrp ▸ hp
  by_cases hrq : r = q
  · rw [hrq, cubeTransfer_at_source w p q hpq] at hr
    exact hr.false.elim
  · rwa [cubeTransfer_at_other w p q r hrp hrq] at hr

theorem IsCubeWeight.transfer {w : CubeProfile → ℝ} (hw : IsCubeWeight w)
    (p q : CubeProfile) (hpq : p ≠ q) (hp : 0 < w p)
    (hpdim : 2 ≤ profileDimension p) (hqdim : 2 ≤ profileDimension q) :
    IsCubeWeight (cubeTransfer w p q) := by
  constructor
  · intro r
    by_cases hrp : r = p
    · rw [hrp, cubeTransfer_at_target w p q hpq]
      exact add_nonneg (hw.nonneg p) (hw.nonneg q)
    by_cases hrq : r = q
    · rw [hrq, cubeTransfer_at_source w p q hpq]
    · rw [cubeTransfer_at_other w p q r hrp hrq]
      exact hw.nonneg r
  · rw [cubeTransfer, cubeShift_sum]
    exact hw.sum_four
  · intro r hr
    have hrp : r ≠ p := by intro h; subst r; omega
    have hrq : r ≠ q := by intro h; subst r; omega
    rw [cubeTransfer_at_other w p q r hrp hrq]
    exact hw.vertex_zero r hr
  · intro r hr
    have hrp : r ≠ p := by intro h; subst r; omega
    have hrq : r ≠ q := by intro h; subst r; omega
    rw [cubeTransfer_at_other w p q r hrp hrq]
    exact hw.edge_le_one r hr
  · intro r s hr hs
    exact hw.compatible r s (cubeTransfer_positive_before hpq hp hr)
      (cubeTransfer_positive_before hpq hp hs)

open scoped Classical in
noncomputable def positiveHighProfiles (w : CubeProfile → ℝ) : Finset CubeProfile :=
  univ.filter (fun p => 2 ≤ profileDimension p ∧ 0 < w p)

theorem positiveHighProfiles_transfer {w : CubeProfile → ℝ} (hw : IsCubeWeight w)
    (p q : CubeProfile) (hpq : p ≠ q) (hp : 0 < w p)
    (hpdim : 2 ≤ profileDimension p) :
    positiveHighProfiles (cubeTransfer w p q) = (positiveHighProfiles w).erase q := by
  classical
  ext r
  simp only [positiveHighProfiles, mem_filter, mem_univ, true_and, mem_erase]
  by_cases hrp : r = p
  · subst r
    rw [cubeTransfer_at_target w p q hpq]
    have hpos : 0 < w p + w q := add_pos_of_pos_of_nonneg hp (hw.nonneg q)
    exact ⟨fun _ => ⟨hpq, hpdim, hp⟩, fun _ => ⟨hpdim, hpos⟩⟩
  by_cases hrq : r = q
  · subst r
    rw [cubeTransfer_at_source w p q hpq]
    simp
  · rw [cubeTransfer_at_other w p q r hrp hrq]
    exact ⟨fun h => ⟨hrq, h⟩, fun h => h.2⟩

theorem positiveHighProfiles_transfer_card_lt {w : CubeProfile → ℝ} (hw : IsCubeWeight w)
    (p q : CubeProfile) (hpq : p ≠ q) (hp : 0 < w p) (hq : 0 < w q)
    (hpdim : 2 ≤ profileDimension p) (hqdim : 2 ≤ profileDimension q) :
    (positiveHighProfiles (cubeTransfer w p q)).card < (positiveHighProfiles w).card := by
  classical
  rw [positiveHighProfiles_transfer hw p q hpq hp hpdim]
  exact card_erase_lt_of_mem (mem_filter.mpr ⟨mem_univ q, hqdim, hq⟩)

#print axioms IsCubeWeight.transfer
#print axioms positiveHighProfiles_transfer_card_lt

end Erdos556
