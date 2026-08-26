import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A finite-mesh lemma for monotone random clocks

This deterministic lemma is the arithmetic core of the process-level
continued-fraction time change.  A monotone clock is controlled on an entire
linear window by finitely many mesh values.  All floor/division errors are
kept explicitly.
-/

open Filter Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- A monotone real-valued sequence is uniformly close to a linear function
on `0 ≤ n ≤ C L` once it is close at the finite mesh
`j * (L / M)`, `0 ≤ j ≤ C M + 1`, and one mesh step has small linear
drift. -/
theorem monotone_mesh_linear_window
    (u : ℕ → ℝ) (hu : Monotone u)
    {mean epsilon : ℝ} (hmean : 0 ≤ mean)
    {C M L : ℕ} (hC : 0 < C) (hM : 0 < M)
    (hmeshLong : C * M ≤ L / M)
    (hmesh : ∀ j : ℕ, j ≤ C * M + 1 →
      |u (j * (L / M)) - (j * (L / M) : ℕ) * mean| ≤
        epsilon * (L : ℝ) / 2)
    (hstep : (L / M : ℕ) * mean ≤ epsilon * (L : ℝ) / 2) :
    ∀ n : ℕ, n ≤ C * L →
      |u n - (n : ℝ) * mean| ≤ epsilon * (L : ℝ) := by
  let K : ℕ := L / M
  let D : ℕ := C * M
  have hDpos : 0 < D := by
    dsimp only [D]
    exact Nat.mul_pos hC hM
  have hKpos : 0 < K := hDpos.trans_le hmeshLong
  have hLmesh : L < M * (K + 1) := by
    dsimp only [K]
    exact Nat.lt_mul_div_succ L hM
  have hCLmesh : C * L < D * (K + 1) := by
    calc
      C * L < C * (M * (K + 1)) :=
        (Nat.mul_lt_mul_left hC).2 hLmesh
      _ = D * (K + 1) := by simp only [D]; ring
  have hDleK : D ≤ K := hmeshLong
  have hDtoNext : D * (K + 1) ≤ (D + 1) * K := by
    calc
      D * (K + 1) = D * K + D := by ring
      _ ≤ D * K + K := Nat.add_le_add_left hDleK _
      _ = (D + 1) * K := by ring
  intro n hn
  let j : ℕ := n / K
  have hjK : j * K ≤ n := by
    dsimp only [j]
    simpa only [mul_comm] using! Nat.div_mul_le_self n K
  have hnNext : n < (j + 1) * K := by
    dsimp only [j]
    simpa only [mul_comm] using! Nat.lt_mul_div_succ n hKpos
  have hnBound : n < (D + 1) * K := by
    exact lt_of_le_of_lt hn (hCLmesh.trans_le hDtoNext)
  have hjlt : j < D + 1 := by
    exact (Nat.div_lt_iff_lt_mul hKpos).2 (by
      simpa only [mul_comm] using! hnBound)
  have hjle : j ≤ D := by omega
  have hjMesh :
      |u (j * K) - (j * K : ℕ) * mean| ≤
        epsilon * (L : ℝ) / 2 := by
    simpa only [K, D] using! hmesh j (by omega)
  have hjNextMesh :
      |u ((j + 1) * K) - ((j + 1) * K : ℕ) * mean| ≤
        epsilon * (L : ℝ) / 2 := by
    simpa only [K, D] using! hmesh (j + 1) (by omega)
  have hstep' : (K : ℝ) * mean ≤ epsilon * (L : ℝ) / 2 := by
    simpa only [K, Nat.cast_mul] using! hstep
  have huLower : u (j * K) ≤ u n := hu hjK
  have huUpper : u n ≤ u ((j + 1) * K) := hu hnNext.le
  have hgapLowerNat : n - j * K ≤ K := by
    apply (Nat.sub_le_iff_le_add').2
    calc
      n ≤ (j + 1) * K := hnNext.le
      _ = j * K + K := by ring
  have hgapUpperNat : (j + 1) * K - n ≤ K := by
    apply (Nat.sub_le_iff_le_add).2
    calc
      (j + 1) * K = K + j * K := by ring
      _ ≤ K + n := Nat.add_le_add_left hjK K
  have hgapLower : ((n : ℝ) - (j * K : ℕ)) * mean ≤
      (K : ℝ) * mean := by
    have hcast : (n : ℝ) - (j * K : ℕ) ≤ (K : ℝ) := by
      have hcastNat : ((n - j * K : ℕ) : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast hgapLowerNat
      rwa [Nat.cast_sub hjK] at hcastNat
    exact mul_le_mul_of_nonneg_right hcast hmean
  have hgapUpper :
      ((((j + 1) * K : ℕ) : ℝ) - (n : ℝ)) * mean ≤
      (K : ℝ) * mean := by
    have hcast : (((j + 1) * K : ℕ) : ℝ) - n ≤ (K : ℝ) := by
      have hcastNat : ((((j + 1) * K - n : ℕ)) : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast hgapUpperNat
      rwa [Nat.cast_sub hnNext.le] at hcastNat
    exact mul_le_mul_of_nonneg_right hcast hmean
  apply abs_le.mpr
  constructor
  · have hmeshLower :
        -epsilon * (L : ℝ) / 2 ≤
          u (j * K) - (j * K : ℕ) * mean := by
      have := (abs_le.mp hjMesh).1
      linarith
    have hlinear :
        (n : ℝ) * mean - u n ≤
          ((n : ℝ) - (j * K : ℕ)) * mean +
            ((j * K : ℕ) * mean - u (j * K)) := by
      linarith
    nlinarith [hlinear, hgapLower, hstep']
  · have hmeshUpper :
        u ((j + 1) * K) - ((j + 1) * K : ℕ) * mean ≤
          epsilon * (L : ℝ) / 2 :=
      (abs_le.mp hjNextMesh).2
    have hlinear :
        u n - (n : ℝ) * mean ≤
          (u ((j + 1) * K) -
            ((j + 1) * K : ℕ) * mean) +
          ((((j + 1) * K : ℕ) : ℝ) - n) * mean := by
      linarith
    nlinarith [hlinear, hgapUpper, hstep']

end

end Erdos1002
