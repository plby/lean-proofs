import ErdosProblems.Erdos587.NVDevelopment

/-!
Remove collapsed GAP coordinates without losing dilation properness or volume.
The resulting dimension is controlled by polynomial ambient growth.
-/

namespace Erdos587.GeneralizedAP

theorem proper_of_card_carrier_eq_boxCard (P : GeneralizedAP)
    (hcard : P.carrier.card = P.boxCard) : P.Proper := by
  have hparam : (Finset.univ : Finset P.Param).card = P.boxCard := by
    simp [Param, boxCard]
  have hi : Set.InjOn P.eval (Finset.univ : Finset P.Param) :=
    Finset.card_image_iff.mp (hcard.trans hparam.symm)
  intro x y hxy
  exact hi (Finset.mem_univ x) (Finset.mem_univ y) hxy

theorem boxCard_dilate_trimZeroSides (P : GeneralizedAP) (h : ℕ) :
    (P.trimZeroSides.dilate h).boxCard = (P.dilate h).boxCard := by
  classical
  let f : Fin P.rank → ℕ := fun i => h * P.length i + 1
  change (∏ j : Fin (Fintype.card (PositiveSide P)),
      f ((Fintype.equivFin (PositiveSide P)).symm j).1) = ∏ i : Fin P.rank, f i
  calc
    (∏ j : Fin (Fintype.card (PositiveSide P)),
        f ((Fintype.equivFin (PositiveSide P)).symm j).1) =
        ∏ i : PositiveSide P, f i.1 :=
      (Fintype.equivFin (PositiveSide P)).symm.prod_comp (fun i => f i.1)
    _ = ∏ i : Fin P.rank, f i := by
      symm
      apply Finset.prod_congr_set {i : Fin P.rank | 0 < P.length i} f (fun i => f i.1)
      · intro i hi
        rfl
      · intro i hi
        have hz : P.length i = 0 := Nat.eq_zero_of_not_pos hi
        simp [f, hz]

theorem boxCard_trimZeroSides (P : GeneralizedAP) :
    P.trimZeroSides.boxCard = P.boxCard := by
  simpa only [dilate_one] using P.boxCard_dilate_trimZeroSides 1

theorem tProper_trimZeroSides (P : GeneralizedAP) {h : ℕ} (hP : P.TProper h) :
    P.trimZeroSides.TProper h := by
  apply (P.trimZeroSides.dilate h).proper_of_card_carrier_eq_boxCard
  rw [P.carrier_dilate_trimZeroSides, P.boxCard_dilate_trimZeroSides]
  exact (P.dilate h).card_carrier_of_proper hP

theorem pow_rank_le_boxCard_dilate (P : GeneralizedAP)
    (hpos : ∀ i, 0 < P.length i) (h : ℕ) : h ^ P.rank ≤ (P.dilate h).boxCard := by
  calc
    h ^ P.rank = ∏ _i : Fin P.rank, h := by simp
    _ ≤ ∏ i : Fin P.rank, (h * P.length i + 1) := by
      apply Finset.prod_le_prod'
      intro i hi
      have hm : h ≤ h * P.length i := by
        calc
          h = h * 1 := by simp
          _ ≤ h * P.length i := Nat.mul_le_mul_left h (by have hli := hpos i; omega)
      omega
    _ = (P.dilate h).boxCard := rfl

theorem pow_mul_boxCard_le_two_pow_mul_dilate_boxCard (P : GeneralizedAP)
    (hpos : ∀ i, 0 < P.length i) (h : ℕ) :
    h ^ P.rank * P.boxCard ≤ 2 ^ P.rank * (P.dilate h).boxCard := by
  calc
    h ^ P.rank * P.boxCard ≤ h ^ P.rank * (2 ^ P.rank * P.volume) :=
      Nat.mul_le_mul_left _ (P.boxCard_le_two_pow_mul_volume hpos)
    _ = 2 ^ P.rank * (P.dilate h).volume := by rw [volume_dilate]; ring
    _ ≤ 2 ^ P.rank * (P.dilate h).boxCard :=
      Nat.mul_le_mul_left _ (P.dilate h).volume_le_boxCard

/-- A noncollapsed model of a polynomial-sized interval has bounded rank
once the dilation is larger than the fixed volume loss. -/
theorem rank_le_of_polynomial_dilate_bound (P : GeneralizedAP)
    (hpos : ∀ i, 0 < P.length i) (h N b C : ℕ) (hlarge : 2 * C < h)
    (hN : N ≤ h ^ b) (hbox : (P.dilate h).boxCard ≤ C * (h * N + 1)) :
    P.rank ≤ b + 1 := by
  have hh : 0 < h := by omega
  have hp : 0 < h ^ (b + 1) := Nat.pow_pos hh
  have hamb : h * N + 1 ≤ 2 * h ^ (b + 1) := by
    have hm := Nat.mul_le_mul_left h hN
    have hp' : 0 < h * h ^ b := Nat.mul_pos hh (Nat.pow_pos hh)
    rw [pow_succ]
    nlinarith
  by_contra hnot
  have hr : b + 2 ≤ P.rank := by omega
  have hpow : h ^ (b + 2) ≤ h ^ P.rank := Nat.pow_le_pow_right hh hr
  have hchain : h ^ (b + 1) * h ≤ h ^ (b + 1) * (2 * C) := by
    calc
      h ^ (b + 1) * h = h ^ (b + 2) := (pow_succ h (b + 1)).symm
      _ ≤ h ^ P.rank := hpow
      _ ≤ (P.dilate h).boxCard := P.pow_rank_le_boxCard_dilate hpos h
      _ ≤ C * (h * N + 1) := hbox
      _ ≤ C * (2 * h ^ (b + 1)) := Nat.mul_le_mul_left C hamb
      _ = h ^ (b + 1) * (2 * C) := by ring
  have hc := Nat.le_of_mul_le_mul_left hchain hp
  omega

end Erdos587.GeneralizedAP
