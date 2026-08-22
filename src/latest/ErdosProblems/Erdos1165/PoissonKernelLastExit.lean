/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.GreenProbability

/-!
# Last-exit factorization across a finite cut

For a finite killed domain `D` and a finite cut `C`, this file decomposes a
killed path at its first entrance into `C`.  Reversing a symmetric kernel
turns the same identity into the last-exit factorization: the dependence on
the initial point occurs only through Green functions from that point to the
cut.  We then pass to the infinite Green series in `ENNReal` and specialize
to planar simple random walk.
-/

open scoped BigOperators ENNReal

namespace Erdos1165
namespace PoissonKernelLastExit

open GreenFunction GreenProbability PlanarPotential

variable {State R : Type*} [DecidableEq State] [CommSemiring R]

/-- Weight of paths which enter `C` for the first time exactly at time `n`,
at the specified point `z`, while remaining in `D` through that time. -/
def firstCutWeight (κ : State → State → R) (D C : Finset State) :
    ℕ → State → State → R
  | 0, x, z => if x ∈ D ∧ x ∈ C ∧ x = z then 1 else 0
  | n + 1, x, z =>
      if x ∈ D ∧ x ∉ C then
        ∑ w ∈ D, κ x w * firstCutWeight κ D C n w z
      else 0

@[simp] theorem firstCutWeight_zero (κ : State → State → R)
    (D C : Finset State) (x z : State) :
    firstCutWeight κ D C 0 x z =
      if x ∈ D ∧ x ∈ C ∧ x = z then 1 else 0 := by
  rfl

theorem firstCutWeight_succ (κ : State → State → R)
    (D C : Finset State) (n : ℕ) (x z : State) :
    firstCutWeight κ D C (n + 1) x z =
      if x ∈ D ∧ x ∉ C then
        ∑ w ∈ D, κ x w * firstCutWeight κ D C n w z
      else 0 := by
  rfl

@[simp] theorem firstCutWeight_eq_zero_of_notMem_domain
    (κ : State → State → R) (D C : Finset State) {x : State}
    (hx : x ∉ D) (n : ℕ) (z : State) :
    firstCutWeight κ D C n x z = 0 := by
  cases n <;> simp [firstCutWeight, hx]

@[simp] theorem firstCutWeight_eq_zero_of_notMem_target
    (κ : State → State → R) (D C : Finset State) {z : State}
    (hzD : z ∉ D ∨ z ∉ C) (n : ℕ) (x : State) :
    firstCutWeight κ D C n x z = 0 := by
  induction n generalizing x with
  | zero =>
      rw [firstCutWeight]
      split_ifs with h
      · rcases hzD with hzD | hzC
        · exact (hzD (h.2.2 ▸ h.1)).elim
        · exact (hzC (h.2.2 ▸ h.2.1)).elim
      · rfl
  | succ n ih => simp [firstCutWeight, ih]

lemma sum_firstCutWeight_zero_mul (κ : State → State → R)
    (D C : Finset State) (x : State) (f : State → R) :
    (∑ z ∈ D ∩ C, firstCutWeight κ D C 0 x z * f z) =
      if x ∈ D ∩ C then f x else 0 := by
  by_cases hx : x ∈ D ∩ C
  · rw [if_pos hx, Finset.sum_eq_single x]
    · simp [firstCutWeight, Finset.mem_inter.mp hx]
    · intro z hz hzx
      rw [firstCutWeight]
      split_ifs with h
      · exact (hzx h.2.2.symm).elim
      · simp
    · exact fun h ↦ (h hx).elim
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro z hz
    rw [firstCutWeight]
    split_ifs with h
    · exfalso
      apply hx
      simpa [h.2.2] using Finset.mem_inter.mpr ⟨h.1, h.2.1⟩
    · simp

/-- Fixed-time first-entrance decomposition across a finite cut. -/
theorem killedPower_eq_avoiding_add_firstCut
    (κ : State → State → R) (D C : Finset State) (n : ℕ) (x y : State) :
    killedPower κ D n x y =
      killedPower κ (D \ C) n x y +
        ∑ k ∈ Finset.range (n + 1), ∑ z ∈ D ∩ C,
          firstCutWeight κ D C k x z * killedPower κ D (n - k) z y := by
  induction n generalizing x with
  | zero =>
      rw [show Finset.range (0 + 1) = {0} by ext k; simp]
      simp only [Finset.sum_singleton, Nat.zero_sub]
      rw [sum_firstCutWeight_zero_mul]
      by_cases hxD : x ∈ D <;> by_cases hxC : x ∈ C <;>
        simp [killedPower, hxD, hxC]
  | succ n ih =>
      by_cases hxD : x ∈ D
      · by_cases hxC : x ∈ C
        · rw [Finset.sum_range_succ']
          rw [sum_firstCutWeight_zero_mul]
          simp [killedPower, firstCutWeight, hxD, hxC]
        · have hxB : x ∈ D \ C := Finset.mem_sdiff.mpr ⟨hxD, hxC⟩
          rw [killedPower_succ, if_pos hxD]
          simp_rw [ih]
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          have havoid :
              (∑ w ∈ D, κ x w * killedPower κ (D \ C) n w y) =
                ∑ w ∈ D \ C, κ x w * killedPower κ (D \ C) n w y := by
            symm
            apply Finset.sum_subset Finset.sdiff_subset
            intro w hwD hwB
            rw [killedPower_eq_zero_of_notMem_left]
            · simp
            · exact hwB
          rw [havoid]
          have hsuccB : killedPower κ (D \ C) (n + 1) x y =
              ∑ w ∈ D \ C, κ x w * killedPower κ (D \ C) n w y := by
            rw [killedPower_succ, if_pos hxB]
          rw [← hsuccB]
          rw [Finset.sum_range_succ']
          simp only [firstCutWeight_zero, hxD, hxC, false_and, if_false,
            and_false, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
          simp only [firstCutWeight_succ, hxD, hxC, not_false_eq_true,
            and_self, if_true]
          simp_rw [Finset.mul_sum]
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          have hkN : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          rw [Nat.succ_sub_succ_eq_sub]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro z hz
          apply Finset.sum_congr rfl
          intro w hw
          ac_rfl
      · simp [killedPower, firstCutWeight, hxD]

/-! ## Reversal and the fixed-time last-exit form -/

/-- Killing preserves the symmetry of a symmetric one-step kernel. -/
theorem killedPower_symm_of_kernel_symm
    (κ : State → State → R) (hκ : ∀ u v, κ u v = κ v u)
    (D : Finset State) (n : ℕ) (x y : State) :
    killedPower κ D n x y = killedPower κ D n y x := by
  induction n generalizing x y with
  | zero =>
      by_cases hxy : x = y
      · subst y
        rfl
      · simp [killedPower, hxy, Ne.symm hxy]
  | succ n ih =>
      by_cases hx : x ∈ D
      · by_cases hy : y ∈ D
        · rw [killedPower_succ, if_pos hx]
          rw [killedPower_succ_right, if_pos hx]
          apply Finset.sum_congr rfl
          intro z hz
          rw [ih z y, hκ x z]
          ac_rfl
        · simp [killedPower_eq_zero_of_notMem_right, hy,
            killedPower_eq_zero_of_notMem_left]
      · simp [killedPower_eq_zero_of_notMem_left, hx,
          killedPower_eq_zero_of_notMem_right]

/-- Fixed-time last-exit decomposition.  The coefficient multiplying the
Green mass from `x` to the cut depends only on the reversed tail from `a` to
that cut. -/
theorem killedPower_eq_avoiding_add_lastExit_of_kernel_symm
    (κ : State → State → R) (hκ : ∀ u v, κ u v = κ v u)
    (D C : Finset State) (n : ℕ) (x a : State) :
    killedPower κ D n x a =
      killedPower κ (D \ C) n x a +
        ∑ k ∈ Finset.range (n + 1), ∑ z ∈ D ∩ C,
          killedPower κ D (n - k) x z * firstCutWeight κ D C k a z := by
  rw [killedPower_symm_of_kernel_symm κ hκ D n x a]
  rw [killedPower_eq_avoiding_add_firstCut κ D C n a x]
  rw [killedPower_symm_of_kernel_symm κ hκ (D \ C) n a x]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro z hz
  rw [killedPower_symm_of_kernel_symm κ hκ D (n - k) z x]
  ac_rfl

/-! ## Planar symmetry -/

/-- The four-neighbour planar transition kernel is symmetric. -/
lemma eq_add_direction_iff_reverse (x y : Point) (d : Direction) :
    y = x + directionVector d ↔
      x = y + directionVector (reverseDirection d) := by
  fin_cases d <;>
    simp [directionVector, reverseDirection, Prod.ext_iff] <;> omega

theorem planarKernel_symm (x y : Point) :
    planarKernel x y = planarKernel y x := by
  by_cases hxy : ∃ d : Direction, y = x + directionVector d
  · obtain ⟨d, rfl⟩ := hxy
    have hreverse : x =
        (x + directionVector d) + directionVector (reverseDirection d) := by
      exact (eq_add_direction_iff_reverse x (x + directionVector d) d).1 rfl
    calc
      planarKernel x (x + directionVector d) = (4 : ℝ≥0∞)⁻¹ :=
        planarKernel_eq_of_direction x d
      _ = planarKernel (x + directionVector d) x := by
        have h := (planarKernel_eq_of_direction
          (x + directionVector d) (reverseDirection d)).symm
        rw [← hreverse] at h
        exact h
  · have hyx : ∀ d : Direction, x ≠ y + directionVector d := by
      intro d h
      apply hxy
      refine ⟨reverseDirection d, ?_⟩
      exact (eq_add_direction_iff_reverse y x d).1 h
    have hxy' : ∀ d : Direction, y ≠ x + directionVector d := by
      intro d hd
      exact hxy ⟨d, hd⟩
    rw [planarKernel_eq_zero_of_not_neighbor hxy',
      planarKernel_eq_zero_of_not_neighbor hyx]

theorem planar_killedPower_symm (D : Finset Point) (n : ℕ) (x y : Point) :
    killedPower planarKernel D n x y = killedPower planarKernel D n y x :=
  killedPower_symm_of_kernel_symm planarKernel planarKernel_symm D n x y

/-! ## Infinite planar Green factorization -/

/-- Total mass of first entrances into `C` at `z` before leaving `D`. -/
noncomputable def infiniteFirstCutMass
    (D C : Finset Point) (x z : Point) : ℝ≥0∞ :=
  ∑' n, firstCutWeight planarKernel D C n x z

private lemma tsum_mul_tsum_eq_tsum_antidiagonal
    (f g : ℕ → ℝ≥0∞) :
    (∑' n, f n) * (∑' n, g n) =
      ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        f kl.1 * g kl.2 := by
  let F : ℕ × ℕ → ℝ≥0∞ := fun p ↦ f p.1 * g p.2
  let S : ℕ → Type := fun n ↦
    (Finset.HasAntidiagonal.antidiagonal n : Set (ℕ × ℕ))
  let H : (Σ n, S n) → ℝ≥0∞ := fun q ↦ F q.2
  have hequiv : (∑' p : ℕ × ℕ, F p) = ∑' q : Σ n, S n, H q := by
    exact (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq F).symm
  have hsigma : (∑' q : Σ n, S n, H q) =
      ∑' n, ∑' kl : S n, H ⟨n, kl⟩ := by
    exact ENNReal.summable.tsum_sigma' (fun _ ↦ ENNReal.summable)
  calc
    (∑' n, f n) * (∑' n, g n) =
        ∑' k, f k * (∑' n, g n) := ENNReal.tsum_mul_right.symm
    _ = ∑' k, ∑' m, f k * g m := by
      congr 1
      funext k
      rw [ENNReal.tsum_mul_left]
    _ = ∑' p : ℕ × ℕ, f p.1 * g p.2 := by
      simpa using (ENNReal.tsum_prod'
        (f := fun p : ℕ × ℕ ↦ f p.1 * g p.2)).symm
    _ = ∑' q : Σ n : ℕ,
        (Finset.HasAntidiagonal.antidiagonal n : Set (ℕ × ℕ)),
        f (q.2 : ℕ × ℕ).1 * g (q.2 : ℕ × ℕ).2 := by
      simpa [F, S, H] using hequiv
    _ = ∑' n : ℕ, ∑' kl :
        (Finset.HasAntidiagonal.antidiagonal n : Set (ℕ × ℕ)),
        f (kl : ℕ × ℕ).1 * g (kl : ℕ × ℕ).2 := by
      simpa [F, S, H] using hsigma
    _ = ∑' n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        f kl.1 * g kl.2 := by
      congr 1
      funext n
      rw [tsum_fintype]
      exact (Finset.sum_subtype (Finset.HasAntidiagonal.antidiagonal n)
        (fun _ ↦ Iff.rfl) (fun kl ↦ f kl.1 * g kl.2)).symm

private lemma tsum_sum_range_mul_sub
    (f g : ℕ → ℝ≥0∞) :
    (∑' n, ∑ k ∈ Finset.range (n + 1), f k * g (n - k)) =
      (∑' k, f k) * ∑' l, g l := by
  rw [tsum_mul_tsum_eq_tsum_antidiagonal]
  congr 1
  funext n
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l ↦ f k * g l) n).symm

/-- Exact infinite first-entrance factorization across a finite cut. -/
theorem infiniteGreen_eq_avoiding_add_firstCut
    (D C : Finset Point) (x y : Point) :
    infiniteGreen D x y =
      infiniteGreen (D \ C) x y +
        ∑ z ∈ D ∩ C,
          infiniteFirstCutMass D C x z * infiniteGreen D z y := by
  simp only [infiniteGreen]
  conv_lhs =>
    congr
    ext n
    rw [killedPower_eq_avoiding_add_firstCut]
  rw [ENNReal.tsum_add]
  congr 1
  calc
    (∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), ∑ z ∈ D ∩ C,
        firstCutWeight planarKernel D C k x z *
          killedPower planarKernel D (n - k) z y) =
        ∑' n : ℕ, ∑ z ∈ D ∩ C, ∑ k ∈ Finset.range (n + 1),
          firstCutWeight planarKernel D C k x z *
            killedPower planarKernel D (n - k) z y := by
      congr 1
      funext n
      rw [Finset.sum_comm]
    _ = ∑ z ∈ D ∩ C, ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1),
          firstCutWeight planarKernel D C k x z *
            killedPower planarKernel D (n - k) z y := by
      rw [Summable.tsum_finsetSum]
      intro z hz
      exact ENNReal.summable
    _ = ∑ z ∈ D ∩ C,
          infiniteFirstCutMass D C x z * infiniteGreen D z y := by
      apply Finset.sum_congr rfl
      intro z hz
      simpa only [infiniteFirstCutMass, infiniteGreen] using
        (tsum_sum_range_mul_sub
          (fun k ↦ firstCutWeight planarKernel D C k x z)
          (fun l ↦ killedPower planarKernel D l z y))

/-- The killed planar Green function is symmetric. -/
theorem infiniteGreen_symm (D : Finset Point) (x y : Point) :
    infiniteGreen D x y = infiniteGreen D y x := by
  unfold infiniteGreen
  congr 1
  funext n
  exact planar_killedPower_symm D n x y

/-- Exact infinite last-exit factorization across a finite cut. -/
theorem infiniteGreen_eq_avoiding_add_lastExit
    (D C : Finset Point) (x a : Point) :
    infiniteGreen D x a =
      infiniteGreen (D \ C) x a +
        ∑ z ∈ D ∩ C,
          infiniteGreen D x z * infiniteFirstCutMass D C a z := by
  rw [infiniteGreen_symm D x a]
  rw [infiniteGreen_eq_avoiding_add_firstCut D C a x]
  rw [infiniteGreen_symm (D \ C) a x]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [infiniteGreen_symm D z x]
  ac_rfl

/-- A comparison on the cut propagates to every target separated from both
starting points by that cut.  This is the inequality form of the exact
last-exit factorization. -/
theorem infiniteGreen_le_mul_of_cut
    (D C : Finset Point) (x y a : Point) (c : ℝ≥0∞)
    (hxAvoid : infiniteGreen (D \ C) x a = 0)
    (hyAvoid : infiniteGreen (D \ C) y a = 0)
    (hcut : ∀ z ∈ D ∩ C,
      infiniteGreen D x z ≤ c * infiniteGreen D y z) :
    infiniteGreen D x a ≤ c * infiniteGreen D y a := by
  rw [infiniteGreen_eq_avoiding_add_lastExit D C x a, hxAvoid, zero_add]
  rw [infiniteGreen_eq_avoiding_add_lastExit D C y a, hyAvoid, zero_add]
  calc
    (∑ z ∈ D ∩ C,
        infiniteGreen D x z * infiniteFirstCutMass D C a z) ≤
        ∑ z ∈ D ∩ C,
          (c * infiniteGreen D y z) * infiniteFirstCutMass D C a z := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_right (hcut z hz) bot_le
    _ = c * ∑ z ∈ D ∩ C,
        infiniteGreen D y z * infiniteFirstCutMass D C a z := by
      simp_rw [mul_assoc]
      rw [Finset.mul_sum]

end PoissonKernelLastExit
end Erdos1165
