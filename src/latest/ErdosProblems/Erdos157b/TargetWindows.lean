import ErdosProblems.Erdos157b.TargetBlocks

/-! Choosing a level for each large integer, with a controlled top digit. -/

namespace Erdos157.Binary

open Erdos157.Elementary

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


end Erdos157.Binary
