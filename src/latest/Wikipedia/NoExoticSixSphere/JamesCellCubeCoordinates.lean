import Wikipedia.NoExoticSixSphere.SmoothCubeSphereQuotient
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Max-norm disk coordinates for the James cell maps

The closed max-norm disk is identified with the native finite unit cube
by coordinatewise affine rescaling. Projection to the unit interval
extends the disk map continuously to the whole ambient vector space.
-/

noncomputable section

open Set Metric Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesCellCube

def interval (r : ℝ) : I := projIcc 0 1 zero_le_one ((r + 1) / 2)

theorem continuous_interval : Continuous interval :=
  continuous_projIcc.comp ((continuous_id.add continuous_const).div_const 2)

theorem interval_eq_zero_iff (r : ℝ) : interval r = 0 ↔ r ≤ -1 := by
  rw [interval, projIcc_eq_zero]
  constructor <;> intro h <;> linarith

theorem interval_eq_one_iff (r : ℝ) : interval r = 1 ↔ 1 ≤ r := by
  rw [interval, projIcc_eq_one]
  constructor <;> intro h <;> linarith

theorem interval_interior_iff (r : ℝ) :
    interval r ≠ 0 ∧ interval r ≠ 1 ↔ -1 < r ∧ r < 1 := by
  rw [ne_eq, ne_eq, interval_eq_zero_iff, interval_eq_one_iff, not_le, not_le]

theorem interval_unscale (t : I) : interval (2 * (t : ℝ) - 1) = t := by
  have he : (2 * (t : ℝ) - 1 + 1) / 2 = t := by ring
  change projIcc 0 1 zero_le_one ((2 * (t : ℝ) - 1 + 1) / 2) = t
  rw [he]
  exact projIcc_val zero_le_one t

theorem unscale_interval {r : ℝ} (hr : -1 ≤ r ∧ r ≤ 1) :
    2 * (interval r : ℝ) - 1 = r := by
  have ht : (r + 1) / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
  change 2 * ((projIcc 0 1 zero_le_one ((r + 1) / 2) : I) : ℝ) - 1 = r
  rw [projIcc_of_mem zero_le_one ht]
  ring

def cube (m : ℕ) (x : Fin m → ℝ) : Fin m → I := fun i ↦ interval (x i)

def unscale (m : ℕ) (u : Fin m → I) : Fin m → ℝ := fun i ↦ 2 * (u i : ℝ) - 1

theorem continuous_cube (m : ℕ) : Continuous (cube m) :=
  continuous_pi (fun i ↦ continuous_interval.comp (continuous_apply i))

theorem continuous_unscale (m : ℕ) : Continuous (unscale m) :=
  continuous_pi (fun i ↦ (continuous_const.mul
    (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const)

theorem cube_unscale (m : ℕ) (u : Fin m → I) : cube m (unscale m u) = u := by
  funext i
  exact interval_unscale (u i)

theorem mem_ball_iff (m : ℕ) (x : Fin m → ℝ) :
    x ∈ ball 0 1 ↔ ∀ i, -1 < x i ∧ x i < 1 := by
  rw [ball_pi _ (by norm_num : (0 : ℝ) < 1)]
  simp only [mem_pi, mem_univ, forall_const, mem_ball, Pi.zero_apply,
    dist_zero_right, Real.norm_eq_abs, abs_lt]

theorem mem_closedBall_iff (m : ℕ) (x : Fin m → ℝ) :
    x ∈ closedBall 0 1 ↔ ∀ i, -1 ≤ x i ∧ x i ≤ 1 := by
  rw [closedBall_pi _ (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [mem_pi, mem_univ, forall_const, mem_closedBall, Pi.zero_apply,
    dist_zero_right, Real.norm_eq_abs, abs_le]

theorem unscale_mem_closedBall (m : ℕ) (u : Fin m → I) :
    unscale m u ∈ closedBall 0 1 := by
  apply (mem_closedBall_iff m _).mpr
  intro i
  change -1 ≤ 2 * (u i : ℝ) - 1 ∧ 2 * (u i : ℝ) - 1 ≤ 1
  constructor <;> linarith [(u i).property.1, (u i).property.2]

theorem unscale_cube_of_mem_closedBall (m : ℕ) {x : Fin m → ℝ}
    (hx : x ∈ closedBall 0 1) : unscale m (cube m x) = x := by
  funext i
  exact unscale_interval ((mem_closedBall_iff m x).mp hx i)

theorem cube_not_boundary_iff (m : ℕ) (x : Fin m → ℝ) :
    cube m x ∉ Cube.boundary (Fin m) ↔ x ∈ ball 0 1 := by
  change (¬ ∃ i, cube m x i = 0 ∨ cube m x i = 1) ↔ _
  rw [mem_ball_iff]
  simp only [not_exists, not_or, cube, interval_interior_iff]

theorem cube_injOn_closedBall (m : ℕ) : Set.InjOn (cube m) (closedBall 0 1) := by
  intro x hx y hy h
  have he := congrArg (unscale m) h
  rwa [unscale_cube_of_mem_closedBall m hx, unscale_cube_of_mem_closedBall m hy] at he

def block (n k : ℕ) (u : Fin (k * n) → I) (i : Fin k) : Fin n → I :=
  fun j ↦ u (finProdFinEquiv (i, j))

def pack (n k : ℕ) (v : Fin k → Fin n → I) : Fin (k * n) → I :=
  fun l ↦ v (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2

theorem block_pack (n k : ℕ) (v : Fin k → Fin n → I) (i : Fin k) :
    block n k (pack n k v) i = v i := by
  funext j
  simp only [block, pack, Equiv.symm_apply_apply]

theorem pack_block (n k : ℕ) (u : Fin (k * n) → I) :
    pack n k (block n k u) = u := by
  funext l
  simp only [pack, block, Prod.mk.eta, Equiv.apply_symm_apply]

theorem block_not_boundary_iff (n k : ℕ) (u : Fin (k * n) → I) :
    (∀ i, block n k u i ∉ Cube.boundary (Fin n)) ↔ u ∉ Cube.boundary (Fin (k * n)) := by
  change (∀ i, ¬ ∃ j, u (finProdFinEquiv (i, j)) = 0 ∨
    u (finProdFinEquiv (i, j)) = 1) ↔ ¬ ∃ l, u l = 0 ∨ u l = 1
  constructor
  · intro h hu
    obtain ⟨l, hl⟩ := hu
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective l
    exact h i ⟨j, hl⟩
  · intro h i hi
    obtain ⟨j, hj⟩ := hi
    exact h ⟨finProdFinEquiv (i, j), hj⟩

end NoExoticSixSphere.JamesCellCube
