import ErdosProblems.Erdos587.MultiplicativeRemoval

/-! The volume-decrease preprocessing step, with explicit logarithmic deletion loss. -/

open scoped BigOperators

namespace Erdos587.CFP

variable {α ι : Type*} [Fintype ι]

def volumePotential (V : ι → Finset α → ℕ) (B : Finset α) : ℕ := ∏ i, V i B

def HasStableVolumes (V : ι → Finset α → ℕ) (B : Finset α) (r : ℕ) : Prop :=
  ∀ D ⊆ B, B.card ≤ D.card + r → ∀ i, 3 * V i B < 4 * V i D

theorem volumePotential_pos {V : ι → Finset α → ℕ} {B : Finset α}
    (hpos : ∀ i, 0 < V i B) : 0 < volumePotential V B :=
  Finset.prod_pos (fun i _hi => hpos i)

theorem volumePotential_decreases {V : ι → Finset α → ℕ} {D B : Finset α}
    (hmono : ∀ i, V i D ≤ V i B) (hdecrease : ∃ i, 4 * V i D ≤ 3 * V i B) :
    4 * volumePotential V D ≤ 3 * volumePotential V B := by
  classical
  obtain ⟨i, hi⟩ := hdecrease
  have hrest : (∏ j ∈ Finset.univ.erase i, V j D) ≤ ∏ j ∈ Finset.univ.erase i, V j B :=
    Finset.prod_le_prod (fun _j _hj => Nat.zero_le _) (fun j _hj => hmono j)
  rw [volumePotential, volumePotential,
    ← Finset.mul_prod_erase Finset.univ (fun j => V j D) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => V j B) (Finset.mem_univ i)]
  calc
    4 * (V i D * ∏ j ∈ Finset.univ.erase i, V j D) =
        (4 * V i D) * ∏ j ∈ Finset.univ.erase i, V j D := by ring
    _ ≤ (3 * V i B) * ∏ j ∈ Finset.univ.erase i, V j B := Nat.mul_le_mul hi hrest
    _ = 3 * (V i B * ∏ j ∈ Finset.univ.erase i, V j B) := by ring

theorem exists_subset_with_stable_volumes (V : ι → Finset α → ℕ) (A : Finset α) (r : ℕ)
    (hpos : ∀ B ⊆ A, ∀ i, 0 < V i B)
    (hmono : ∀ B ⊆ A, ∀ D ⊆ B, ∀ i, V i D ≤ V i B) :
    ∃ B ⊆ A, A.card ≤ B.card + volumeDescentLength (volumePotential V A) * r ∧
      HasStableVolumes V B r := by
  classical
  apply exists_good_subset_of_multiplicative_potential (volume := volumePotential V)
  · intro B hBA _hcost
    exact volumePotential_pos (hpos B hBA)
  · intro B hBA _hcost hnot
    simp only [HasStableVolumes] at hnot
    push Not at hnot
    obtain ⟨D, hDB, hremove, i, hcut⟩ := hnot
    exact ⟨D, hDB, hremove, volumePotential_decreases (hmono B hBA D hDB) ⟨i, hcut⟩⟩

theorem volumeDescentLength_le_of_power_bound {V N d : ℕ} (hV : V ≤ N ^ d) :
    volumeDescentLength V ≤ 3 * (d * (Nat.log 2 N + 1) + 1) := by
  have hN := Nat.lt_pow_succ_log_self Nat.one_lt_two N
  have hpow := Nat.pow_le_pow_left hN.le d
  rw [← pow_mul] at hpow
  have hlog := Nat.log_mono_right (b := 2) (hV.trans hpow)
  rw [Nat.log_pow Nat.one_lt_two] at hlog
  dsimp only [volumeDescentLength]
  nlinarith

theorem volumePotential_le_pow {V : ι → Finset α → ℕ} {A : Finset α} {N : ℕ}
    (hV : ∀ i, V i A ≤ N) : volumePotential V A ≤ N ^ Fintype.card ι := by
  calc
    volumePotential V A ≤ ∏ _i : ι, N :=
      Finset.prod_le_prod (fun _i _hi => Nat.zero_le _) (fun i _hi => hV i)
    _ = N ^ Fintype.card ι := by simp

/-- Uniformly bounded initial volumes give logarithmic, rather than polynomial,
loss in the ambient bound. -/
theorem exists_subset_with_stable_volumes_log_bound (V : ι → Finset α → ℕ)
    (A : Finset α) (r N : ℕ) (hpos : ∀ B ⊆ A, ∀ i, 0 < V i B)
    (hmono : ∀ B ⊆ A, ∀ D ⊆ B, ∀ i, V i D ≤ V i B)
    (hinitial : ∀ i, V i A ≤ N) :
    ∃ B ⊆ A, A.card ≤ B.card + (3 * (Fintype.card ι * (Nat.log 2 N + 1) + 1)) * r ∧
      HasStableVolumes V B r := by
  obtain ⟨B, hBA, hcost, hstable⟩ := exists_subset_with_stable_volumes V A r hpos hmono
  have hlength := volumeDescentLength_le_of_power_bound (volumePotential_le_pow hinitial)
  exact ⟨B, hBA, hcost.trans (Nat.add_le_add (le_refl _) (Nat.mul_le_mul_right r hlength)),
    hstable⟩

end Erdos587.CFP
