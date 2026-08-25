import ErdosProblems.Erdos157.TargetBlocks

/-! Choosing a level for each large integer, with a controlled top digit. -/

namespace Erdos157.Elementary

open AuxiliaryModuli Filter

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem level_le_initialPlace (k : ℕ) : k ≤ blockPlace K 0 k := by
  calc
    k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ Fintype.card K ^ k := Nat.pow_le_pow_left Fintype.one_lt_card _
    _ ≤ Fintype.card K ^ (k ^ 2) := Nat.pow_le_pow_right Fintype.card_pos (by nlinarith)
    _ ≤ _ := initialPlace_ge_fieldPower K k

noncomputable def targetLevel (m : ℕ) : ℕ :=
  Nat.findGreatest (fun k => 6 * blockPlace K 0 k ≤ m) m

theorem targetLevel_window (m : ℕ) (hm : 6 ≤ m) :
    6 * blockPlace K 0 (targetLevel K m) ≤ m ∧
      m < 6 * blockPlace K 0 (targetLevel K m + 1) := by
  classical
  have hlo : 6 * blockPlace K 0 (targetLevel K m) ≤ m :=
    Nat.findGreatest_spec (P := fun k => 6 * blockPlace K 0 k ≤ m)
      (Nat.zero_le m) (by simpa [blockPlace] using hm)
  refine ⟨hlo, ?_⟩
  by_contra h
  have hp : 6 * blockPlace K 0 (targetLevel K m + 1) ≤ m := by omega
  have hidx := level_le_initialPlace K (targetLevel K m + 1)
  have hmidx : targetLevel K m + 1 ≤ m := by omega
  have hle : targetLevel K m + 1 ≤ targetLevel K m := Nat.le_findGreatest hmidx hp
  omega

theorem tendsto_targetLevel : Tendsto (targetLevel K) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (6 * blockPlace K 0 k)] with m hm
  have hk := level_le_initialPlace K k
  exact Nat.le_findGreatest (by omega) hm

theorem target_expansion_in_window (m : ℕ) (hm : 6 ≤ m) :
    ∃ d : (∀ i : Fin (targetLevel K m), BlockTarget K i), ∃ z : ℕ,
      m = levelTargetValue K d + blockPlace K 0 (targetLevel K m) * z ∧
        4 ≤ z ∧ z < 6 * blockRadix K (targetLevel K m) := by
  have hw := targetLevel_window K m hm
  obtain ⟨d, z, he, hz⟩ := exists_level_target_expansion K (targetLevel K m) m (by omega)
  refine ⟨d, z, he, hz, ?_⟩
  have hp := blockPlace_pos K 0 (targetLevel K m)
  rw [blockPlace_snoc] at hw
  nlinarith [hw.2]

theorem two_blockRadix_le_topCapacity (hq : 721 ^ 8 ≤ Fintype.card K) (k : ℕ) (hk : 3 ≤ k) :
    2 * blockRadix K k ≤ Fintype.card K ^ (3 * k) := by
  have hqpos : 0 < Fintype.card K := Fintype.card_pos
  have hsub : Nat.card (ResidueField K k)ˣ ≤ Fintype.card K ^ (2 * k + 1) := by
    rw [residueField_units_natCard, Nat.card_eq_fintype_card]
    exact Nat.sub_le _ _
  have hsmall : 721 ^ (2 * k + 5) ≤ Fintype.card K ^ (k - 1) := by
    calc
      _ ≤ 721 ^ (8 * (k - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = (721 ^ 8) ^ (k - 1) := pow_mul _ _ _
      _ ≤ _ := Nat.pow_le_pow_left hq _
  calc
    _ ≤ Fintype.card K ^ (2 * k + 1) * 721 ^ (2 * k + 5) := by
      rw [show 2 * k + 5 = (2 * k + 4) + 1 by omega, pow_succ 721 (2 * k + 4)]
      unfold blockRadix
      have hm := Nat.mul_le_mul_right (721 ^ (2 * k + 4)) hsub
      calc
        _ = 206 * (Nat.card (ResidueField K k)ˣ * 721 ^ (2 * k + 4)) := by ring
        _ ≤ 721 * (Fintype.card K ^ (2 * k + 1) * 721 ^ (2 * k + 4)) :=
          Nat.mul_le_mul (by decide) hm
        _ = _ := by ring
    _ ≤ Fintype.card K ^ (2 * k + 1) * Fintype.card K ^ (k - 1) :=
      Nat.mul_le_mul_left _ hsmall
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem coefficientField_topCapacity (k : ℕ) (hk : 3 ≤ k) :
    2 * blockRadix CoefficientField k ≤ Fintype.card CoefficientField ^ (3 * k) := by
  apply two_blockRadix_le_topCapacity CoefficientField _ k hk
  rw [card_coefficientField]
  calc
    721 ^ 8 ≤ (2 ^ 10) ^ 8 := Nat.pow_le_pow_left (by decide) 8
    _ = 2 ^ 80 := by rw [← pow_mul]
    _ ≤ 2 ^ 1024 := Nat.pow_le_pow_right (by decide) (by decide)

end Erdos157.Elementary
