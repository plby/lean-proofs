import ErdosProblems.Erdos394.HierarchyParameters
import ErdosProblems.Erdos394.GeneralGlobalMediumSieve
import ErdosProblems.Erdos394.GeometricSpecialization

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Numerator estimate on the sparse hierarchy grid
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace Erdos394

/-- Elementary exponential domination used in the parameter audit. -/
theorem hierarchy_self_le_two_pow : ∀ n : ℕ, n ≤ 2 ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ]
      have ih := hierarchy_self_le_two_pow n
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      omega

/-- A fixed natural constant is eventually at most `2^j`. -/
theorem eventually_const_le_two_pow (C : ℕ) :
    ∀ᶠ j : ℕ in atTop, C ≤ 2 ^ j :=
  (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by norm_num)).eventually
    (eventually_ge_atTop C)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- F-074 specialized to the sparse polynomial grid. The factorial tail is
absorbed into a second copy of the Euler main term. -/
theorem eventually_hierarchy_numerator_bound (K : ℕ) (hK : 2 ≤ K) :
    ∀ᶠ j : ℕ in atTop,
      let L := K + 1
      let X := hierarchyX K j
      let z := hierarchyZ K j
      let y := hierarchyY K j
      let Z := hierarchyRootHeight K j
      let R := hierarchyOrder K j
      let P := primeInterval z y
      let V := localEulerProduct P (fun p ↦ 1 / (p : ℝ))
      let E := ∏ p ∈ P, (1 + 1 / ((L : ℝ) * (p : ℝ)))
      let W := generalRootMeanFactor L R
      (∑ n ∈ Finset.Icc 1 X, (t L n : ℝ)) ≤
        (X : ℝ) ^ 2 / (z : ℝ) +
        2 * (X : ℝ) ^ 2 * V * (W * E) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (W * ((y ^ R : ℕ) : ℝ) * ((y ^ R + 1 : ℕ) : ℝ)) := by
  obtain ⟨Jmin, hJmin, hbrun⟩ := exists_geometric_primeInterval_brun_tail
  let L := K + 1
  have hL : 1 < L := by dsimp [L]; omega
  have horder := eventually_hierarchyOrder_le K
  have hLtwo := eventually_const_le_two_pow L
  have hCtwo := eventually_const_le_two_pow (8 * (L * L - 1))
  filter_upwards [eventually_ge_atTop (max (max Jmin (L * L)) 4),
    horder, hLtwo, hCtwo] with j hj hRj hL2 hC2
  let X := hierarchyX K j
  let z := hierarchyZ K j
  let y := hierarchyY K j
  let Z := hierarchyRootHeight K j
  let R := hierarchyOrder K j
  let P := primeInterval z y
  let V := localEulerProduct P (fun p ↦ 1 / (p : ℝ))
  let E := ∏ p ∈ P, (1 + 1 / ((L : ℝ) * (p : ℝ)))
  let W := generalRootMeanFactor L R
  have hj4 : 4 ≤ j := (le_max_right (max Jmin (L * L)) 4).trans hj
  have hjJmin : Jmin ≤ j :=
    (le_max_left Jmin (L * L)).trans
      ((le_max_left (max Jmin (L * L)) 4).trans hj)
  have hjL2 : L * L ≤ j :=
    (le_max_right Jmin (L * L)).trans
      ((le_max_left (max Jmin (L * L)) 4).trans hj)
  have hj1 : 1 ≤ j := by omega
  have hJzmin : Jmin ≤ hierarchyLowerExponent K j := by
    calc
      Jmin ≤ j := hjJmin
      _ ≤ j ^ 2 := Nat.le_pow (by omega)
      _ = hierarchyLowerExponent K j := rfl
  have hJzy : hierarchyLowerExponent K j ≤ hierarchyUpperExponent K j :=
    hierarchyLower_le_upper_exponent K hj1
  have hzpos : 0 < z := by simp [z, hierarchyZ]
  have hypos : 0 < y := by simp [y, hierarchyY]
  have hzy : z ≤ y := by simpa [z, y] using hierarchyZ_le_Y K hj1
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeInterval hp
  have hPinterval : ∀ p ∈ P, z < p ∧ p ≤ y := by
    intro p hp
    exact mem_primeInterval_bounds hp
  have hPcard : P.card ≤ y := card_primeInterval_le hypos
  have htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤ V := by
    dsimp [P, R, V, z, y]
    exact hbrun (hierarchyLowerExponent K j)
      (hierarchyUpperExponent K j) hJzmin hJzy
  have h2j : 2 * j ≤ 2 ^ (j * j) := by
    calc
      2 * j ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 (hierarchy_self_le_two_pow j)
      _ = 2 ^ (j + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (j * j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have h4j : 4 * j ≤ 2 ^ (j * j) := by
    calc
      4 * j ≤ 4 * 2 ^ j := Nat.mul_le_mul_left 4 (hierarchy_self_le_two_pow j)
      _ = 2 ^ (j + 2) := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ 2 ^ (j * j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hLpow : L ^ R ≤ 2 ^ (j * j) := by
    calc
      L ^ R ≤ (2 ^ j) ^ R := Nat.pow_le_pow_left hL2 R
      _ = 2 ^ (j * R) := (pow_mul 2 j R).symm
      _ ≤ 2 ^ (j * j) := Nat.pow_le_pow_right (by omega)
        (Nat.mul_le_mul_left j hRj)
  have hLsmall : L ≤ 2 ^ (j * j) := by
    exact hL2.trans (Nat.pow_le_pow_right (by omega) (by nlinarith : j ≤ j * j))
  have hfourPow : 4 ^ (j * j) ≤ 16 ^ (j * j) :=
    Nat.pow_le_pow_left (by norm_num) (j * j)
  have hareaZ : 2 * R * L ^ R ≤ z := by
    calc
      2 * R * L ^ R ≤ (2 * j) * 2 ^ (j * j) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hRj) hLpow
      _ ≤ 2 ^ (j * j) * 2 ^ (j * j) :=
        Nat.mul_le_mul_right _ h2j
      _ = 4 ^ (j * j) := by rw [← Nat.mul_pow]
      _ ≤ 16 ^ (j * j) := hfourPow
      _ = z := by simp [z, hierarchyZ, hierarchyLowerExponent, pow_two]
  have hratZ : 4 * R * L ≤ z := by
    calc
      4 * R * L ≤ (4 * j) * 2 ^ (j * j) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 hRj) hLsmall
      _ ≤ 2 ^ (j * j) * 2 ^ (j * j) :=
        Nat.mul_le_mul_right _ h4j
      _ = 4 ^ (j * j) := by rw [← Nat.mul_pow]
      _ ≤ 16 ^ (j * j) := hfourPow
      _ = z := by simp [z, hierarchyZ, hierarchyLowerExponent, pow_two]
  have hZsizeNat : 8 * R * (L * L - 1) ≤ Z := by
    calc
      8 * R * (L * L - 1) = R * (8 * (L * L - 1)) := by ring
      _ ≤ j * 2 ^ j := Nat.mul_le_mul hRj hC2
      _ ≤ 2 ^ j * 2 ^ j :=
        Nat.mul_le_mul_right _ (hierarchy_self_le_two_pow j)
      _ = 4 ^ j := by rw [← Nat.mul_pow]
      _ ≤ 16 ^ j := Nat.pow_le_pow_left (by norm_num) j
      _ = Z := rfl
  have hZpow : Z ^ (L * L) ≤ z := by
    calc
      Z ^ (L * L) = 16 ^ (j * (L * L)) := by
        dsimp [Z, hierarchyRootHeight]
        rw [← pow_mul]
      _ ≤ 16 ^ (j * j) := Nat.pow_le_pow_right (by omega)
        (Nat.mul_le_mul_left j hjL2)
      _ = z := by simp [z, hierarchyZ, hierarchyLowerExponent, pow_two]
  have hZle : Z ≤ z := by
    calc
      Z = 16 ^ j := rfl
      _ ≤ 16 ^ (j * j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      _ = z := by simp [z, hierarchyZ, hierarchyLowerExponent, pow_two]
  have hZ2le : Z * Z ≤ z := by
    calc
      Z * Z = 16 ^ (2 * j) := by
        dsimp [Z, hierarchyRootHeight]
        rw [← pow_add]
        congr 1
        omega
      _ ≤ 16 ^ (j * j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      _ = z := by simp [z, hierarchyZ, hierarchyLowerExponent, pow_two]
  have hLz : L * L < z := by
    have hL2pow : L * L ≤ 2 ^ (j * j) := by
      exact (hjL2.trans (hierarchy_self_le_two_pow j)).trans
        (Nat.pow_le_pow_right (by omega) (by nlinarith : j ≤ j * j))
    have hpstrict : 2 ^ (j * j) < 16 ^ (j * j) :=
      Nat.pow_lt_pow_left (by norm_num) (by positivity)
    exact hL2pow.trans_lt (hpstrict.trans_eq
      (by simp [z, hierarchyZ, hierarchyLowerExponent, pow_two]))
  have hLleSq : L ≤ L * L := by nlinarith [show 1 ≤ L by omega]
  have hfinite := finite_general_card_medium_sieve_bound
    L Z P R X R y z hL (by
      dsimp [Z, hierarchyRootHeight]
      exact Nat.one_le_pow j 16 (by norm_num)) hprime
    hzpos.ne' hzy hPinterval
    (fun p hp ↦ (hLleSq.trans_lt hLz).trans (hPinterval p hp).1)
    (fun p hp ↦ hLz.trans (hPinterval p hp).1)
    (fun p hp ↦ hZpow.trans (hPinterval p hp).1.le)
    (fun p hp ↦ hZle.trans (hPinterval p hp).1.le)
    (fun p hp ↦ hZ2le.trans (hPinterval p hp).1.le)
    (fun p hp ↦ by
      have ht : 2 * R * L ^ R < p := hareaZ.trans_lt (hPinterval p hp).1
      omega)
    (fun p hp ↦ by
      have ht : 4 * R * L < p := hratZ.trans_lt (hPinterval p hp).1
      omega)
    hZsizeNat (by omega) hPcard (hierarchyOrder_even K j) htail
  have hV0 : 0 ≤ V := by
    dsimp [V]
    apply localEulerProduct_nonneg P (fun p ↦ 1 / (p : ℝ))
    · intro p hp; positivity
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
      exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
  have hE1 : 1 ≤ E := by
    dsimp [E]
    apply Finset.one_le_prod
    intro p hp
    have : 0 ≤ 1 / ((L : ℝ) * (p : ℝ)) := by positivity
    linarith
  have hW2 : 2 ≤ W := by
    dsimp [W, generalRootMeanFactor]
    have hn : 0 ≤ (R : ℝ) *
        (2 + ((((80 : ℝ) * ((L * L - 1 : ℕ) : ℝ) +
          160 * (L : ℝ)) + 2) + 88) * ((L : ℝ) + 1)) := by positivity
    linarith
  have htailAbsorb : (X : ℝ) ^ 2 *
      ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
        ((R + 1).factorial : ℝ)) ≤
      (X : ℝ) ^ 2 * V * (W * E) := by
    have hVE : V ≤ V * (W * E) := by
      have hW0 : 0 ≤ W := generalRootMeanFactor_nonneg L R
      have hW1 : 1 ≤ W := by linarith
      have hWE : 1 ≤ W * E := by
        calc
          1 ≤ W := hW1
          _ = W * 1 := by ring
          _ ≤ W * E := mul_le_mul_of_nonneg_left hE1 hW0
      calc
        V = V * 1 := by ring
        _ ≤ V * (W * E) := mul_le_mul_of_nonneg_left hWE hV0
    have hs := mul_le_mul_of_nonneg_left (htail.trans hVE)
      (show 0 ≤ (X : ℝ) ^ 2 by positivity)
    simpa only [mul_assoc] using hs
  dsimp [L, X, z, y, Z, R, P, V, E, W] at hfinite ⊢
  linarith

end Erdos394
