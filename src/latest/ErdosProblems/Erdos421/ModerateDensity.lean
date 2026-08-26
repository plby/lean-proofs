import ErdosProblems.Erdos421.BoundedMass
import ErdosProblems.Erdos421.GeometricDensity

/-! # Density zero of rejected gaps up to the power `19/180` -/

namespace Erdos421

/-- This larger cutoff supplements the original one-twentieth-power cutoff. -/
def ModerateGap (k : ℕ) : Prop := gapLength k ^ 180 ≤ prime k ^ 19

theorem ModerateGap.length_le_scale {k u : ℕ} (hk : ModerateGap k)
    (hX : prime (k + 1) ≤ 2 ^ (180 * u)) : gapLength k ≤ 2 ^ (19 * u) := by
  have hp : prime k ≤ 2 ^ (180 * u) :=
    (prime_strictMono (Nat.lt_succ_self k)).le.trans hX
  have heq : (2 ^ (180 * u)) ^ 19 = (2 ^ (19 * u)) ^ 180 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hpow : gapLength k ^ 180 ≤ (2 ^ (19 * u)) ^ 180 :=
    hk.trans ((Nat.pow_le_pow_left hp 19).trans_eq heq)
  exact (Nat.pow_le_pow_iff_left (by decide : 180 ≠ 0)).mp hpow

def moderateOmissions : Set ℕ :=
  {n | ∃ k, Rejected k ∧ ModerateGap k ∧ prime k < n ∧ n < prime (k + 1)}

theorem prefixCount_moderateOmissions_le {B u : ℕ} (hX : 2 * B ≤ 2 ^ (180 * u)) :
    prefixCount moderateOmissions B ≤
      ∑ k ∈ boundedRejections (2 ^ (180 * u)) (2 ^ (19 * u)), gapLength k := by
  classical
  let I := boundedRejections (2 ^ (180 * u)) (2 ^ (19 * u))
  have hsub : (Finset.range B).filter (· ∈ moderateOmissions) ⊆
      I.biUnion (fun k ↦ Finset.Ioo (prime k) (prime (k + 1))) := by
    intro n hn
    obtain ⟨hnB, hnm⟩ := Finset.mem_filter.mp hn
    obtain ⟨k, hk, hs, hpn, hnq⟩ := hnm
    have hnB' := Finset.mem_range.mp hnB
    have hp : prime k ≤ B := by omega
    have hqX : prime (k + 1) ≤ 2 ^ (180 * u) :=
      (prime_succ_le_two_mul k).trans ((Nat.mul_le_mul_left 2 hp).trans hX)
    exact Finset.mem_biUnion.mpr ⟨k,
      mem_boundedRejections.mpr ⟨hk, hqX, hs.length_le_scale hqX⟩,
      Finset.mem_Ioo.mpr ⟨hpn, hnq⟩⟩
  calc
    _ ≤ (I.biUnion (fun k ↦ Finset.Ioo (prime k) (prime (k + 1)))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ k ∈ I, (Finset.Ioo (prime k) (prime (k + 1))).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ I, gapLength k := by
      apply Finset.sum_le_sum
      intro k _
      rw [Nat.card_Ioo]
      unfold gapLength
      omega

theorem moderateOmissions_prefix_scale {u : ℕ} (hu : 12 ≤ u) :
    prefixCount moderateOmissions (2 ^ (180 * u)) ≤ 7 * 2 ^ (179 * (u + 1)) := by
  apply (prefixCount_moderateOmissions_le (u := u + 1) ?_).trans
    (boundedRejections_mass_scale (by omega))
  calc
    2 * 2 ^ (180 * u) = 2 ^ (180 * u + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (180 * (u + 1)) := Nat.pow_le_pow_right (by decide) (by omega)

theorem moderateOmissions_hasDensity_zero : moderateOmissions.HasDensity 0 := by
  apply hasDensity_zero_of_geometric_bound moderateOmissions
    (a := 2 ^ 179) (b := 2 ^ 180) (C := 7 * 2 ^ 179) (N₀ := 12)
    (by norm_num) (by norm_num)
  intro u hu
  have h := moderateOmissions_prefix_scale hu
  have hb : (2 ^ 180) ^ u = 2 ^ (180 * u) := (pow_mul 2 180 u).symm
  have ha : 7 * 2 ^ (179 * (u + 1)) = (7 * 2 ^ 179) * (2 ^ 179) ^ u := by
    rw [Nat.mul_add, Nat.mul_one, pow_add, pow_mul]
    ring
  rwa [hb, ← ha]

end Erdos421
