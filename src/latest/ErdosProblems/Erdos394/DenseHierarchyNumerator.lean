import ErdosProblems.Erdos394.DenseHierarchyParameters
import ErdosProblems.Erdos394.HierarchyNumerator

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Numerator bound on the dense hierarchy grid
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace Erdos394

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- F-074 specialized to the dense hierarchy parameters, uniformly in the
summatory cutoff `X`. -/
theorem eventually_dense_hierarchy_numerator_bound_uniform (K : ℕ) (hK : 2 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ X : ℕ,
      let L := K + 1
      let z := denseHierarchyZ N
      let y := denseHierarchyY N
      let Z := denseRootHeight N
      let R := denseHierarchyOrder N
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
  have horder := eventually_denseHierarchyOrder_le
  have hlowup := eventually_denseLower_le_upper
  have hJyTop := tendsto_denseUpperExponent_atTop.eventually
    (eventually_ge_atTop Jmin)
  have hhlarge := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_ge_atTop (max (max Jmin (L * L)) 4))
  have hbase := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_const_le_two_pow (L ^ 1000))
  have hcoef := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_const_le_two_pow 2000)
  have hzcoef := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_const_le_two_pow (8000 * (L * L - 1)))
  filter_upwards [eventually_gt_atTop 0, horder, hlowup, hJyTop,
    hhlarge, hbase, hcoef, hzcoef] with N hN hR hzyExp hJyMin
      hh hbase2 hcoef2 hzcoef2
  intro X
  let h := denseHierarchyLog N
  let z := denseHierarchyZ N
  let y := denseHierarchyY N
  let Z := denseRootHeight N
  let R := denseHierarchyOrder N
  let P := primeInterval z y
  let V := localEulerProduct P (fun p ↦ 1 / (p : ℝ))
  let E := ∏ p ∈ P, (1 + 1 / ((L : ℝ) * (p : ℝ)))
  let W := generalRootMeanFactor L R
  have hh4 : 4 ≤ h := (le_max_right (max Jmin (L * L)) 4).trans hh
  have hhL2 : L * L ≤ h :=
    (le_max_right Jmin (L * L)).trans
      ((le_max_left (max Jmin (L * L)) 4).trans hh)
  have hJzMin : Jmin ≤ denseLowerExponent N := by
    calc
      Jmin ≤ h := (le_max_left Jmin (L * L)).trans
        ((le_max_left (max Jmin (L * L)) 4).trans hh)
      _ ≤ h ^ 2 := Nat.le_pow (by omega)
      _ = denseLowerExponent N := rfl
  have hRbound : R ≤ 1000 * h := by simpa [R, h] using hR
  have hzpos : 0 < z := by simp [z, denseHierarchyZ]
  have hypos : 0 < y := by simp [y, denseHierarchyY]
  have hzy : z ≤ y := by
    dsimp [z, y, denseHierarchyZ, denseHierarchyY]
    exact Nat.pow_le_pow_right (by omega) hzyExp
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
    dsimp [P, R, V, z, y, denseHierarchyZ, denseHierarchyY]
    exact hbrun (denseLowerExponent N) (denseUpperExponent N)
      hJzMin hzyExp
  have hLpow : L ^ R ≤ 2 ^ (h * h) := by
    calc
      L ^ R ≤ L ^ (1000 * h) := Nat.pow_le_pow_right (by omega) hRbound
      _ = (L ^ 1000) ^ h := by rw [← pow_mul]
      _ ≤ (2 ^ h) ^ h := Nat.pow_le_pow_left hbase2 h
      _ = 2 ^ (h * h) := (pow_mul 2 h h).symm
  have h2R : 2 * R ≤ 2 ^ (h * h) := by
    calc
      2 * R ≤ 2000 * h := by nlinarith
      _ ≤ 2 ^ h * 2 ^ h := Nat.mul_le_mul hcoef2 (hierarchy_self_le_two_pow h)
      _ = 4 ^ h := by rw [← Nat.mul_pow]
      _ = 2 ^ (2 * h) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
      _ ≤ 2 ^ (h * h) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hfourSq : 4 ^ (h * h) ≤ 16 ^ (h * h) :=
    Nat.pow_le_pow_left (by norm_num) (h * h)
  have hareaZ : 2 * R * L ^ R ≤ z := by
    calc
      2 * R * L ^ R ≤ 2 ^ (h * h) * 2 ^ (h * h) :=
        Nat.mul_le_mul h2R hLpow
      _ = 4 ^ (h * h) := by rw [← Nat.mul_pow]
      _ ≤ 16 ^ (h * h) := hfourSq
      _ = z := by simp [z, denseHierarchyZ, denseLowerExponent, h, pow_two]
  have hLsmall : L ≤ 2 ^ (h * h) := by
    calc
      L ≤ L * L := by nlinarith [show 1 ≤ L by omega]
      _ ≤ h := hhL2
      _ ≤ 2 ^ h := hierarchy_self_le_two_pow h
      _ ≤ 2 ^ (h * h) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have h4R : 4 * R ≤ 2 ^ (h * h) := by
    calc
      4 * R ≤ 4000 * h := by nlinarith
      _ = 2 * (2000 * h) := by ring
      _ ≤ 2 * (2 ^ h * 2 ^ h) :=
        Nat.mul_le_mul_left 2
          (Nat.mul_le_mul hcoef2 (hierarchy_self_le_two_pow h))
      _ = 2 ^ (1 + h + h) := by
        rw [pow_add, pow_add]
        norm_num
        ring
      _ ≤ 2 ^ (h * h) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hratZ : 4 * R * L ≤ z := by
    calc
      4 * R * L ≤ 2 ^ (h * h) * 2 ^ (h * h) :=
        Nat.mul_le_mul h4R hLsmall
      _ = 4 ^ (h * h) := by rw [← Nat.mul_pow]
      _ ≤ 16 ^ (h * h) := hfourSq
      _ = z := by simp [z, denseHierarchyZ, denseLowerExponent, h, pow_two]
  have hZsize : 8 * R * (L * L - 1) ≤ Z := by
    calc
      8 * R * (L * L - 1) ≤
          h * (8000 * (L * L - 1)) := by nlinarith
      _ ≤ 2 ^ h * 2 ^ h := Nat.mul_le_mul (hierarchy_self_le_two_pow h) hzcoef2
      _ = 4 ^ h := by rw [← Nat.mul_pow]
      _ ≤ 16 ^ h := Nat.pow_le_pow_left (by norm_num) h
      _ = Z := rfl
  have hZpow : Z ^ (L * L) ≤ z := by
    calc
      Z ^ (L * L) = 16 ^ (h * (L * L)) := by
        dsimp [Z, denseRootHeight]
        rw [← pow_mul]
      _ ≤ 16 ^ (h * h) := Nat.pow_le_pow_right (by omega)
        (Nat.mul_le_mul_left h hhL2)
      _ = z := by simp [z, denseHierarchyZ, denseLowerExponent, h, pow_two]
  have hZle : Z ≤ z := by
    calc
      Z = 16 ^ h := rfl
      _ ≤ 16 ^ (h * h) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      _ = z := by simp [z, denseHierarchyZ, denseLowerExponent, h, pow_two]
  have hZ2le : Z * Z ≤ z := by
    calc
      Z * Z = 16 ^ (2 * h) := by
        dsimp [Z, denseRootHeight]
        rw [← pow_add]
        congr 1
        omega
      _ ≤ 16 ^ (h * h) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      _ = z := by simp [z, denseHierarchyZ, denseLowerExponent, h, pow_two]
  have hLz : L * L < z := by
    have hpowpos : 0 < h * h := by positivity
    calc
      L * L ≤ h := hhL2
      _ ≤ 2 ^ (h * h) := (hierarchy_self_le_two_pow h).trans
        (Nat.pow_le_pow_right (by omega) (by nlinarith))
      _ < 16 ^ (h * h) := Nat.pow_lt_pow_left (by norm_num) hpowpos.ne'
      _ = z := by simp [z, denseHierarchyZ, denseLowerExponent, h, pow_two]
  have hLleSq : L ≤ L * L := by nlinarith [show 1 ≤ L by omega]
  have hfinite := finite_general_card_medium_sieve_bound
    L Z P R X R y z hL (by
      dsimp [Z, denseRootHeight]
      exact Nat.one_le_pow h 16 (by norm_num)) hprime
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
    hZsize (by omega) hPcard (denseHierarchyOrder_even N) htail
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
  have hW0 : 0 ≤ W := generalRootMeanFactor_nonneg L R
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
    have hW1 : 1 ≤ W := by linarith
    have hWE : 1 ≤ W * E := by
      calc
        1 ≤ W := hW1
        _ = W * 1 := by ring
        _ ≤ W * E := mul_le_mul_of_nonneg_left hE1 hW0
    have hVE : V ≤ V * (W * E) := by
      calc
        V = V * 1 := by ring
        _ ≤ V * (W * E) := mul_le_mul_of_nonneg_left hWE hV0
    have hs := mul_le_mul_of_nonneg_left (htail.trans hVE)
      (show 0 ≤ (X : ℝ) ^ 2 by positivity)
    simpa only [mul_assoc] using hs
  dsimp [L, z, y, Z, R, P, V, E, W] at hfinite ⊢
  linarith

/-- Dense-grid specialization of the uniform numerator bound. -/
theorem eventually_dense_hierarchy_numerator_bound (K : ℕ) (hK : 2 ≤ K) :
    ∀ᶠ N : ℕ in atTop,
      let L := K + 1
      let X := denseHierarchyX N
      let z := denseHierarchyZ N
      let y := denseHierarchyY N
      let Z := denseRootHeight N
      let R := denseHierarchyOrder N
      let P := primeInterval z y
      let V := localEulerProduct P (fun p ↦ 1 / (p : ℝ))
      let E := ∏ p ∈ P, (1 + 1 / ((L : ℝ) * (p : ℝ)))
      let W := generalRootMeanFactor L R
      (∑ n ∈ Finset.Icc 1 X, (t L n : ℝ)) ≤
        (X : ℝ) ^ 2 / (z : ℝ) +
        2 * (X : ℝ) ^ 2 * V * (W * E) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (W * ((y ^ R : ℕ) : ℝ) * ((y ^ R + 1 : ℕ) : ℝ)) := by
  filter_upwards [eventually_dense_hierarchy_numerator_bound_uniform K hK]
    with N hN
  exact hN (denseHierarchyX N)

end Erdos394
