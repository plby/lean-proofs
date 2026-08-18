/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# The finite dyadic flow identity for circle squaring

This file formalizes the algebraic core of the flow construction in
Marks--Unger, *A New Proof of Laczkovich's Circle Squaring Theorem I*,
Lemma 3.1.  No convergence, discrepancy, or integral-flow argument is used
here.

For an additive action of `ℤ^d`, `cubeAverage f n x` is the average of `f`
over the negatively translated `n`-cube based at `x`.  The scale-`n` flow
pushes this average along each nonzero direction in `{0,1}^d`.  Its
divergence changes the `n`-cube average into the `2n`-cube average.  We also
sum this identity over the dyadic scales `1, 2, ..., 2^(m-1)`.

The definitions sum over all bit directions because this makes the cube
partition transparent.  The zero direction contributes zero to divergence;
`divergence_eq_sum_erase_zero` records the exact reduction to the nonzero
generating set used in the paper.
-/

open scoped BigOperators

namespace Erdos1124.Flow

noncomputable section

/-- The acting lattice `ℤ^d`. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

/-- The `2^d` bit directions used to split a doubled cube. -/
abbrev BitDirection (d : ℕ) := Fin d → Fin 2

/-- Regard a bit direction as a vector in `ℤ^d`. -/
def bitVector {d : ℕ} (g : BitDirection d) : Lattice d :=
  fun i ↦ ((g i : ℕ) : ℤ)

/-- Regard a point of the finite coordinate cube as a vector in `ℤ^d`. -/
def cubeIndex {d n : ℕ} (q : Fin d → Fin n) : Lattice d :=
  fun i ↦ ((q i : ℕ) : ℤ)

/-- Coordinatewise quotient/remainder gives the partition of a `2n`-cube
into `2^d` translates of an `n`-cube. -/
def doubleCubeEquiv (d n : ℕ) :
    BitDirection d × (Fin d → Fin n) ≃ (Fin d → Fin (2 * n)) where
  toFun p i := finProdFinEquiv (p.1 i, p.2 i)
  invFun q :=
    (fun i ↦ (finProdFinEquiv.symm (q i)).1,
      fun i ↦ (finProdFinEquiv.symm (q i)).2)
  left_inv p := by
    ext i <;> simp
  right_inv q := by
    funext i
    exact finProdFinEquiv.apply_symm_apply (q i)

@[simp]
lemma cubeIndex_doubleCubeEquiv {d n : ℕ} (g : BitDirection d)
    (q : Fin d → Fin n) :
    cubeIndex (doubleCubeEquiv d n (g, q)) =
      n • bitVector g + cubeIndex q := by
  ext i
  simp [cubeIndex, doubleCubeEquiv, bitVector, nsmul_eq_mul]
  ring

section CubeAverage

variable {d : ℕ} {X 𝕜 : Type*}
variable [AddAction (Lattice d) X]
variable [Field 𝕜] [CharZero 𝕜]

/-- The unnormalized sum of `f` on the negative `n`-cube based at `x`. -/
def cubeSum (f : X → 𝕜) (n : ℕ) (x : X) : 𝕜 :=
  ∑ q : Fin d → Fin n, f (-cubeIndex q +ᵥ x)

/-- The average of `f` on the negative `n`-cube based at `x`. -/
def cubeAverage (f : X → 𝕜) (n : ℕ) (x : X) : 𝕜 :=
  (((n : 𝕜) ^ d)⁻¹) * cubeSum (d := d) f n x

@[simp]
lemma cubeSum_one (f : X → 𝕜) (x : X) : cubeSum (d := d) f 1 x = f x := by
  have hz : cubeIndex (fun _ : Fin d ↦ (0 : Fin 1)) = 0 := by
    ext i
    simp [cubeIndex]
  simp [cubeSum, hz]

@[simp]
lemma cubeAverage_one (f : X → 𝕜) (x : X) : cubeAverage (d := d) f 1 x = f x := by
  simp [cubeAverage]

/-- The unnormalized doubled cube is the sum of its `2^d` translated
subcubes. -/
lemma cubeSum_two_mul (f : X → 𝕜) (n : ℕ) (x : X) :
    cubeSum (d := d) f (2 * n) x =
      ∑ g : BitDirection d, cubeSum (d := d) f n (-(n • bitVector g) +ᵥ x) := by
  rw [cubeSum]
  calc
    (∑ q : Fin d → Fin (2 * n), f (-cubeIndex q +ᵥ x)) =
        ∑ p : BitDirection d × (Fin d → Fin n),
          f (-cubeIndex (doubleCubeEquiv d n p) +ᵥ x) := by
            exact (Equiv.sum_comp (doubleCubeEquiv d n)
              (fun q ↦ f (-cubeIndex q +ᵥ x))).symm
    _ = ∑ g : BitDirection d, ∑ q : Fin d → Fin n,
          f (-cubeIndex (doubleCubeEquiv d n (g, q)) +ᵥ x) := by
            rw [Fintype.sum_prod_type]
    _ = ∑ g : BitDirection d, cubeSum f n (-(n • bitVector g) +ᵥ x) := by
      apply Fintype.sum_congr
      intro g
      rw [cubeSum]
      apply Fintype.sum_congr
      intro q
      rw [cubeIndex_doubleCubeEquiv]
      simp only [neg_add_rev, ← vadd_assoc]
      congr 1

/-- The normalized version of `cubeSum_two_mul`: a doubled cube average is
the average of the `2^d` translated smaller cube averages. -/
lemma cubeAverage_two_mul (f : X → 𝕜) (n : ℕ) (x : X) :
    cubeAverage (d := d) f (2 * n) x =
      (((2 : 𝕜) ^ d)⁻¹) *
        ∑ g : BitDirection d, cubeAverage (d := d) f n (-(n • bitVector g) +ᵥ x) := by
  rw [cubeAverage, cubeSum_two_mul (d := d)]
  simp_rw [cubeAverage]
  rw [← Finset.mul_sum]
  push_cast
  rw [mul_pow, mul_inv_rev]
  ring

end CubeAverage

section DyadicFlow

variable {d : ℕ} {X 𝕜 : Type*}
variable [AddAction (Lattice d) X]
variable [Field 𝕜] [CharZero 𝕜]

/-- The factor `2^{-d}` appearing at every dyadic scale. -/
def dyadicFactor : 𝕜 := ((2 : 𝕜) ^ d)⁻¹

/-- A flow is recorded by its bit direction and its initial vertex. -/
abbrev DirectionalFlow := BitDirection d → X → 𝕜

/-- Incoming minus outgoing flow.  The zero direction is harmless and is
removed by `divergence_eq_sum_erase_zero`. -/
def divergence (φ : DirectionalFlow (d := d) (X := X) (𝕜 := 𝕜)) (x : X) : 𝕜 :=
  ∑ g : BitDirection d, (φ g (-bitVector g +ᵥ x) - φ g x)

/-- The zero bit direction contributes nothing, so this is exactly the sum
over `({0,1}^d \ {0})` used in the circle-squaring flow. -/
lemma divergence_eq_sum_erase_zero
    (φ : DirectionalFlow (d := d) (X := X) (𝕜 := 𝕜)) (x : X) :
    divergence φ x =
      ∑ g ∈ (Finset.univ.erase (0 : BitDirection d)),
        (φ g (-bitVector g +ᵥ x) - φ g x) := by
  rw [divergence, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : BitDirection d))]
  have hz : bitVector (0 : BitDirection d) = 0 := by
    ext i
    simp [bitVector]
  simp [hz]

/-- The length-`n` path flow in direction `g`, built from a potential `F`. -/
def pathFlow (F : X → 𝕜) (n : ℕ) : DirectionalFlow (d := d) (X := X) (𝕜 := 𝕜) :=
  fun g x ↦ dyadicFactor (d := d) (𝕜 := 𝕜) *
    ∑ m ∈ Finset.range n, F (-(m • bitVector g) +ᵥ x)

/-- The one-dimensional sum along a path telescopes after shifting the base
point back by one step. -/
lemma path_sum_telescope (F : X → 𝕜) (n : ℕ) (g : BitDirection d) (x : X) :
    (∑ m ∈ Finset.range n,
        F (-(m • bitVector g) +ᵥ (-bitVector g +ᵥ x))) -
      (∑ m ∈ Finset.range n, F (-(m • bitVector g) +ᵥ x)) =
        F (-(n • bitVector g) +ᵥ x) - F x := by
  rw [← Finset.sum_sub_distrib]
  convert Finset.sum_range_sub
    (fun m ↦ F (-(m • bitVector g) +ᵥ x)) n using 1
  · apply Finset.sum_congr rfl
    intro m hm
    congr 1
    simp only [← vadd_assoc]
    congr 1
    rw [add_nsmul]
    abel
    rfl
  · simp

/-- Divergence of the path flow, before using the cube-partition identity. -/
lemma divergence_pathFlow (F : X → 𝕜) (n : ℕ) (x : X) :
    divergence (d := d) (pathFlow (d := d) F n) x =
      dyadicFactor (d := d) (𝕜 := 𝕜) *
        ∑ g : BitDirection d, (F (-(n • bitVector g) +ᵥ x) - F x) := by
  rw [divergence, Finset.mul_sum]
  apply Fintype.sum_congr
  intro g
  rw [pathFlow, pathFlow, ← mul_sub, path_sum_telescope]

/-- The scale-`n` flow is the path flow built from the `n`-cube average. -/
def scaleFlow (f : X → 𝕜) (n : ℕ) :
    DirectionalFlow (d := d) (X := X) (𝕜 := 𝕜) :=
  pathFlow (d := d) (cubeAverage (d := d) f n) n

/-- **Dyadic flow identity.**  The divergence of the scale-`n` flow changes
the `n`-cube average into the `2n`-cube average. -/
theorem divergence_scaleFlow_add_cubeAverage (f : X → 𝕜) (n : ℕ) (x : X) :
    divergence (d := d) (scaleFlow (d := d) f n) x + cubeAverage (d := d) f n x =
      cubeAverage (d := d) f (2 * n) x := by
  rw [scaleFlow, divergence_pathFlow (d := d), cubeAverage_two_mul (d := d)]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul]
  change dyadicFactor (d := d) (𝕜 := 𝕜) *
      ((∑ g : BitDirection d, cubeAverage (d := d) f n (-(n • bitVector g) +ᵥ x)) -
        (2 ^ d : ℕ) * cubeAverage (d := d) f n x) + cubeAverage (d := d) f n x =
    dyadicFactor (d := d) (𝕜 := 𝕜) *
      ∑ g : BitDirection d, cubeAverage (d := d) f n (-(n • bitVector g) +ᵥ x)
  have htwo : (((2 : 𝕜) ^ d)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfactor : dyadicFactor (d := d) (𝕜 := 𝕜) * (2 : 𝕜) ^ d = 1 := by
    exact inv_mul_cancel₀ htwo
  push_cast
  rw [mul_sub]
  rw [← mul_assoc, hfactor, one_mul]
  abel

/-- Sum the scale flows over `1, 2, ..., 2^(m-1)`. -/
def dyadicPartialFlow (f : X → 𝕜) (m : ℕ) :
    DirectionalFlow (d := d) (X := X) (𝕜 := 𝕜) :=
  fun g x ↦ ∑ q ∈ Finset.range m, scaleFlow (d := d) f (2 ^ q) g x

/-- Divergence commutes with the finite sum defining `dyadicPartialFlow`. -/
lemma divergence_dyadicPartialFlow (f : X → 𝕜) (m : ℕ) (x : X) :
    divergence (d := d) (dyadicPartialFlow (d := d) f m) x =
      ∑ q ∈ Finset.range m, divergence (d := d) (scaleFlow (d := d) f (2 ^ q)) x := by
  simp only [divergence, dyadicPartialFlow]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

/-- **Finite dyadic partial-sum identity.**  After the first `m` dyadic
scales, the residual potential is the average on the cube of side `2^m`. -/
theorem divergence_dyadicPartialFlow_add (f : X → 𝕜) (m : ℕ) (x : X) :
    divergence (d := d) (dyadicPartialFlow (d := d) f m) x + f x =
      cubeAverage (d := d) f (2 ^ m) x := by
  rw [divergence_dyadicPartialFlow (d := d)]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ q ∈ Finset.range m,
              divergence (d := d) (scaleFlow (d := d) f (2 ^ q)) x) +
              divergence (d := d) (scaleFlow (d := d) f (2 ^ m)) x + f x =
            divergence (d := d) (scaleFlow (d := d) f (2 ^ m)) x +
              ((∑ q ∈ Finset.range m,
                divergence (d := d) (scaleFlow (d := d) f (2 ^ q)) x) + f x) := by
                  abel
        _ = divergence (d := d) (scaleFlow (d := d) f (2 ^ m)) x +
              cubeAverage (d := d) f (2 ^ m) x := by rw [ih]
        _ = cubeAverage (d := d) f (2 ^ (m + 1)) x := by
          simpa [pow_succ, mul_comm] using
            divergence_scaleFlow_add_cubeAverage (d := d) f (2 ^ m) x

end DyadicFlow

end

end Erdos1124.Flow
