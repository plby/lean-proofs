import ErdosProblems.Erdos941.TrajectoryCount
import ErdosProblems.Erdos941.SphereMass
import ErdosProblems.Erdos941.MassCollisionImpossible

/-! # A sufficiently-large hitting theorem for a positive fraction of a sphere -/

namespace Erdos941

theorem exists_large_dense_trajectory_hit (p : ℕ) [NeZero (p ^ 2)]
    (t : ZMod (p ^ 2)) (target : ModularTriple p → Prop) (ht : 3 * t = 1)
    (K : ℕ) (hK : 0 < K)
    (havoid : ∀ (j : ℕ) (s : (Axis × ModularTriple p) × Bool),
      modularAvoidance p t target (K * j) s ≤ (3 ^ K - 1) ^ j)
    (d : ℝ) (hd : 0 < d) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ¬4 ∣ n → n % 8 ≠ 7 → n % 3 = 2 →
      ∀ (A : Type) [Fintype A] (o : A → OrientedTriple),
        Function.Injective (fun a => (o a).1.2) →
        (∀ a, tripleNorm (o a).1.2 = n) →
        (sphereCount n : ℝ) ≤ d * Fintype.card A →
        ∃ L a i, i < 2 * L ∧ modularBadTurn p target
          (orientedModState p (centeredState L (o a) i))
          (orientedChoice (centeredState L (o a) i)) := by
  let Q := 3 ^ (2 * K)
  let P : ℝ := ((3 ^ K - 1 : ℕ) : ℝ) ^ 2
  have hQ : 1 < Q := Nat.one_lt_pow (by omega) (by decide)
  have hP : 0 ≤ P := sq_nonneg _
  have hPQ : P < Q := by
    have hb : 3 ^ K - 1 < 3 ^ K := by have := pow_pos (by decide : 0 < (3 : ℕ)) K; omega
    have hsq := Nat.pow_lt_pow_left hb (by decide : 2 ≠ 0)
    have he : (3 ^ K) ^ 2 = Q := by dsimp [Q]; rw [← pow_mul, Nat.mul_comm K 2]
    rw [he] at hsq
    dsimp [P]
    exact_mod_cast hsq
  obtain ⟨δ, hδ, hgap⟩ := Analytic.exists_small_power_gap
    (by exact_mod_cast (zero_lt_one.trans hQ)) hPQ
  obtain ⟨c, hc, hmass⟩ := exists_sphereCount_lower_four_free hδ
  obtain ⟨C, hC, hshadow⟩ := exists_three_power_shadowPairs_bound hδ
  let D : ℝ := d ^ 2 * Fintype.card (Axis × ModularTriple p)
  have hD : 0 < D := mul_pos (sq_pos_of_pos hd) (by exact_mod_cast Fintype.card_pos)
  obtain ⟨N, hN, hno⟩ := Analytic.exists_no_mass_collision hQ hP hδ hgap hc hC.le hD
  refine ⟨N, hN, ?_⟩
  intro n hn h4 h8 h3 A _ o hinj hnorm hsize
  by_contra hbad
  push_neg at hbad
  apply hno n (sphereCount n) hn (hmass n (hN.trans_le hn) h4 h8)
  intro j
  have hB : ∀ s : Axis × ModularTriple p,
      modularAvoidance p t target (2 * (K * j)) (s, false) ≤ (3 ^ K - 1) ^ (2 * j) := by
    intro s
    have h := havoid (2 * j) (s, false)
    simpa only [Nat.mul_left_comm, Nat.mul_assoc] using h
  have hcount := card_sq_le_avoidance_mul_shadow p t target ht (K * j) n
    ((3 ^ K - 1) ^ (2 * j)) o hinj h3 hnorm hB (hbad (K * j))
  have hcountR : (Fintype.card A : ℝ) ^ 2 ≤
      (Fintype.card (Axis × ModularTriple p) * (((3 ^ K - 1) ^ (2 * j) : ℕ) : ℝ)) *
        (shadowPairs n (3 ^ (2 * (K * j)))).card := by exact_mod_cast hcount
  have hsize2 : (sphereCount n : ℝ) ^ 2 ≤ d ^ 2 * (Fintype.card A : ℝ) ^ 2 := by
    nlinarith only [mul_self_le_mul_self (Nat.cast_nonneg (sphereCount n)) hsize]
  have hshadow' := hshadow n (K * j) h3
  have heB : ((((3 ^ K - 1) ^ (2 * j) : ℕ) : ℝ)) = P ^ j := by
    dsimp [P]
    rw [Nat.cast_pow, ← pow_mul]
  have heQ : (3 : ℝ) ^ (2 * (K * j)) = (Q : ℝ) ^ j := by
    dsimp [Q]
    rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Nat.mul_assoc]
  rw [heB] at hcountR
  rw [heQ] at hshadow'
  calc
    _ ≤ d ^ 2 * (Fintype.card A : ℝ) ^ 2 := hsize2
    _ ≤ d ^ 2 * ((Fintype.card (Axis × ModularTriple p) * P ^ j) *
        (shadowPairs n (3 ^ (2 * (K * j)))).card) :=
      mul_le_mul_of_nonneg_left hcountR (sq_nonneg d)
    _ = (D * P ^ j) * (shadowPairs n (3 ^ (2 * (K * j)))).card := by dsimp [D]; ring
    _ ≤ (D * P ^ j) * (2 * sphereCount n + C * ((n : ℝ) / (Q : ℝ) ^ j) * (n : ℝ) ^ δ) :=
      mul_le_mul_of_nonneg_left hshadow' (mul_nonneg hD.le (pow_nonneg hP j))

end Erdos941
