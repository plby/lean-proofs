import ErdosProblems.Erdos633b.CornerAngles
import ErdosProblems.Erdos633b.Specification
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! Initial restrictions from the proved corner equations: rational tile
angles propagate to the outer triangle, and independent tile angles force
the outer angle triple to be a permutation. -/

namespace Erdos633b

theorem nat_matrix_permutation {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ι → ℕ)
    (hc : ∀ j, ∑ i, m i j = 1) (hr : ∀ i, ∃ j, 0 < m i j) :
    ∃ e : Equiv.Perm ι, ∀ i j, m i j = if e i = j then 1 else 0 := by
  classical
  choose g hg using hr
  have hle (i j : ι) : m i j ≤ 1 := by
    rw [← hc j]
    exact Finset.single_le_sum (f := fun k => m k j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpair (i k j : ι) (hik : i ≠ k) : m i j + m k j ≤ 1 := by
    calc
      _ = ∑ a ∈ ({i, k} : Finset ι), m a j := by simp [hik]
      _ ≤ ∑ a, m a j := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = 1 := hc j
  have hginj : Function.Injective g := by
    intro i k he
    by_contra hik
    have h := hpair i k (g i) hik
    have hi := hg i
    have hk := hg k
    rw [← he] at hk
    omega
  have hgsurj : Function.Surjective g := Finite.surjective_of_injective hginj
  let e : Equiv.Perm ι := Equiv.ofBijective g ⟨hginj, hgsurj⟩
  refine ⟨e, ?_⟩
  intro i j
  change m i j = if g i = j then 1 else 0
  by_cases h : g i = j
  · rw [if_pos h]
    have hp := hg i
    rw [h] at hp
    have hb := hle i j
    omega
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := hgsurj j
    have hik : i ≠ k := by intro he; subst k; exact h hk
    have hp := hg k
    rw [hk] at hp
    have hb := hpair i k j hik
    omega

namespace Tiling

theorem rational_angles_of_tile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ j, IsRational (d.tile.angle j / Real.pi)) :
    ∀ i, IsRational (T.angle i / Real.pi) := by
  choose q hq using h
  intro i
  refine ⟨∑ j : Fin 3, (d.cornerAngleCount i j : ℚ) * q j, ?_⟩
  push_cast
  simp_rw [hq, ← mul_div_assoc]
  rw [← Finset.sum_div, ← d.angle_eq_sum_counts]

theorem corner_column_sum_of_linearIndependent {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hli : LinearIndependent ℚ d.tile.angle) (j : Fin 3) :
    ∑ i : Fin 3, d.cornerAngleCount i j = 1 := by
  have heq : ∑ j : Fin 3, ((∑ i : Fin 3, d.cornerAngleCount i j : ℕ) : ℚ) • d.tile.angle j =
      ∑ j : Fin 3, (1 : ℚ) • d.tile.angle j := by
    calc
      _ = ∑ j : Fin 3, ∑ i : Fin 3, (d.cornerAngleCount i j : ℝ) * d.tile.angle j := by
        simp only [Rat.smul_def, Rat.cast_natCast, Nat.cast_sum, Rat.cast_sum, Finset.sum_mul]
      _ = ∑ i : Fin 3, T.angle i := by
        rw [Finset.sum_comm]
        simp only [← d.angle_eq_sum_counts]
      _ = Real.pi := by simpa only [Fin.sum_univ_three] using T.angle_sum
      _ = ∑ j : Fin 3, (1 : ℚ) • d.tile.angle j := by
        simpa only [one_smul, Fin.sum_univ_three] using d.tile.angle_sum.symm
  have h := hli.eq_coords_of_eq heq j
  exact_mod_cast h

theorem corner_row_positive {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    ∃ j, 0 < d.cornerAngleCount i j := by
  by_contra h
  have hz (j : Fin 3) : d.cornerAngleCount i j = 0 := Nat.eq_zero_of_not_pos
    (fun hj => h ⟨j, hj⟩)
  have he := d.angle_eq_sum_counts i
  simp only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at he
  exact (T.angle_pos i).ne' he

theorem angles_permuted_of_linearIndependent {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hli : LinearIndependent ℚ d.tile.angle) :
    ∃ e : Equiv.Perm (Fin 3), ∀ i, T.angle i = d.tile.angle (e i) := by
  obtain ⟨e, he⟩ := nat_matrix_permutation d.cornerAngleCount
    (d.corner_column_sum_of_linearIndependent hli) d.corner_row_positive
  refine ⟨e, ?_⟩
  intro i
  rw [d.angle_eq_sum_counts]
  simp only [he]
  simp

theorem not_linearIndependent_of_angles_not_permuted {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ¬ ∃ e : Equiv.Perm (Fin 3), ∀ i, T.angle i = d.tile.angle (e i)) :
    ¬ LinearIndependent ℚ d.tile.angle := fun hli =>
  h (d.angles_permuted_of_linearIndependent hli)

end Tiling

end Erdos633b
