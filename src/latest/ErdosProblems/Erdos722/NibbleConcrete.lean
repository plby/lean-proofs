/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.NibbleScalar
import ErdosProblems.Erdos722.BoostAsymptotic
import Mathlib

/-!
# Concrete parameters for the bounded-leave nibble

Write `K = choose q r` and `d = (6K)^2`.  The integer scale `T` is the
floor of `n^(3K/d)`.  We stop with approximately `g/T` host edges.  The
reciprocal degree-profile error starts at `T^(-(5K-1))`; at stopping
density `1/T` its amplification by `density^(-(4K-1))` leaves a full
factor `T^-K` against the mean-field degree.
-/

namespace Erdos722.NibbleConcrete

open Erdos722.Asymptotics
open Erdos722.Boost
open Erdos722.NibbleProfiles
open Erdos722.NibbleProfileAlgebra

noncomputable section

def K (q r : ℕ) : ℕ := Nat.choose q r

def den (q r : ℕ) : ℕ := (6 * K q r) ^ 2

def scaleMultiplier : ℕ := 64

def scale (n q r : ℕ) : ℕ :=
  scaleMultiplier * rationalPowerThreshold (3 * K q r) (den q r) n

def profileA (n q r : ℕ) : ℝ :=
  1 / (scale n q r : ℝ) ^ (5 * K q r - 1)

def centerDegree (n q r : ℕ) : ℝ :=
  (extensionScale n q r : ℝ) / 2

/-- We stop a full clique-size above `g / T`; this avoids a zero residual
and makes every prescribed transition legal at the level of host size. -/
def stopTarget (g n q r : ℕ) : ℕ :=
  Nat.ceil ((g : ℝ) / (scale n q r : ℝ)) + K q r

def depth (g n q r : ℕ) : ℕ :=
  (g - stopTarget g n q r) / K q r

def upperProfile (g n q r i : ℕ) : ℝ :=
  degreeUpper (profileA n q r) (centerDegree n q r) g (K q r) i

def lowerProfile (g n q r i : ℕ) : ℝ :=
  degreeLower (profileA n q r) (centerDegree n q r) g (K q r) i

def cliqueUpperProfile (g n q r i : ℕ) : ℝ :=
  cliqueUpper (profileA n q r) (centerDegree n q r) g (K q r) i

def cliqueLowerProfile (g n q r i : ℕ) : ℝ :=
  cliqueLower (profileA n q r) (centerDegree n q r) g (K q r) i

def upperNat (g n q r i : ℕ) : ℕ :=
  Nat.ceil (upperProfile g n q r i)

def lowerNat (g n q r i : ℕ) : ℕ :=
  Nat.floor (lowerProfile g n q r i)

def faceSlack (n q r : ℕ) : ℝ :=
  (n : ℝ) / (scale n q r : ℝ) ^ 2

def faceEps (n q r : ℕ) : ℝ :=
  8 / (scale n q r : ℝ)

/-- Exact quotient-remainder description of the terminal host size. -/
lemma remaining_depth_eq
    {g target K₀ : ℕ} (hK : 0 < K₀) (htarget : target ≤ g) :
    g - K₀ * ((g - target) / K₀) =
      target + (g - target) % K₀ := by
  have hsplit := Nat.div_add_mod (g - target) K₀
  have htg : target + (g - target) = g := Nat.add_sub_of_le htarget
  omega

lemma remaining_depth_lower
    {g target K₀ : ℕ} (hK : 0 < K₀) (htarget : target ≤ g) :
    target ≤ g - K₀ * ((g - target) / K₀) := by
  rw [remaining_depth_eq hK htarget]
  omega

lemma remaining_depth_lt
    {g target K₀ : ℕ} (hK : 0 < K₀) (htarget : target ≤ g) :
    g - K₀ * ((g - target) / K₀) < target + K₀ := by
  rw [remaining_depth_eq hK htarget]
  have hmod := Nat.mod_lt (g - target) hK
  omega

/-- Every step strictly before `depth` leaves at least one further complete
clique-size of host edges. -/
lemma mul_succ_lt_of_lt_depth
    {g target K₀ i : ℕ} (hK : 0 < K₀) (htarget : 0 < target)
    (hi : i < (g - target) / K₀) :
    K₀ * (i + 1) < g := by
  have hdiv : K₀ * ((g - target) / K₀) ≤ g - target := by
    exact Nat.mul_div_le (g - target) K₀
  have histep : K₀ * (i + 1) ≤
      K₀ * ((g - target) / K₀) := by
    exact Nat.mul_le_mul_left K₀ (by omega)
  have hdiffpos : 0 < g - target := by
    have hmulpos : 0 < K₀ * ((g - target) / K₀) := by
      exact Nat.mul_pos hK (by omega)
    omega
  have hsub : g - target < g := Nat.sub_lt (by omega) htarget
  omega

lemma density_le_one_of_mul_le
    {g K₀ i : ℕ} (hg : 0 < g) (hi : K₀ * i ≤ g) :
    density g K₀ i ≤ 1 := by
  unfold density remaining
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hiR : (K₀ : ℝ) * i ≤ g := by exact_mod_cast hi
  have hprod : (0 : ℝ) ≤ (K₀ : ℝ) * i := by positivity
  apply (div_le_iff₀ hgR).2
  push_cast
  linarith

/-- Before the prescribed endpoint the density is at least `1 / T`. -/
lemma one_div_scale_le_density
    {g n q r i : ℕ} (hg : 0 < g) (hK : 0 < K q r)
    (hscale : 0 < scale n q r)
    (htarget : stopTarget g n q r ≤ g)
    (hi : i ≤ depth g n q r) :
    1 / (scale n q r : ℝ) ≤ density g (K q r) i := by
  let target := stopTarget g n q r
  let d := depth g n q r
  have hdrem : target ≤ g - K q r * d := by
    simpa [d, depth, target] using
      (remaining_depth_lower hK htarget)
  have hirem : g - K q r * d ≤ g - K q r * i := by
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left (K q r) hi) g
  have htargetRem : target ≤ g - K q r * i := hdrem.trans hirem
  have hdMul : K q r * d ≤ g := by
    calc
      K q r * d ≤ g - target := by
        dsimp [d, depth, target]
        exact Nat.mul_div_le _ _
      _ ≤ g := Nat.sub_le _ _
  have himul : K q r * i ≤ g :=
    (Nat.mul_le_mul_left (K q r) hi).trans hdMul
  have hceil : (g : ℝ) / scale n q r ≤
      (Nat.ceil ((g : ℝ) / (scale n q r : ℝ)) : ℝ) :=
    Nat.le_ceil _
  have htargetReal : (g : ℝ) / scale n q r ≤ (target : ℝ) := by
    dsimp [target, stopTarget]
    push_cast
    linarith
  have hremReal : (g : ℝ) / scale n q r ≤
      (g : ℝ) - K q r * i := by
    have hcast : (target : ℝ) ≤ ((g - K q r * i : ℕ) : ℝ) := by
      exact_mod_cast htargetRem
    rw [Nat.cast_sub himul] at hcast
    push_cast at hcast
    exact htargetReal.trans hcast
  unfold density remaining
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hscaleR : (0 : ℝ) < scale n q r := by exact_mod_cast hscale
  apply (div_le_div_iff₀ hscaleR hgR).2
  have hmul := (div_le_iff₀ hscaleR).mp hremReal
  simpa using hmul

/-- The endpoint density differs from `1/T` only by the ceiling and one
division remainder. -/
lemma density_depth_lt
    {g n q r : ℕ} (hg : 0 < g) (hK : 0 < K q r)
    (hscale : 0 < scale n q r)
    (htarget : stopTarget g n q r ≤ g) :
    density g (K q r) (depth g n q r) <
      1 / (scale n q r : ℝ) + (2 * K q r + 1 : ℕ) / g := by
  let target := stopTarget g n q r
  let d := depth g n q r
  have hrem : g - K q r * d < target + K q r := by
    simpa [d, depth, target] using remaining_depth_lt hK htarget
  have hmul : K q r * d ≤ g := by
    calc
      K q r * d ≤ g - target := by
        dsimp [d, depth, target]
        exact Nat.mul_div_le _ _
      _ ≤ g := Nat.sub_le _ _
  have hceil :
      (Nat.ceil ((g : ℝ) / (scale n q r : ℝ)) : ℝ) <
        (g : ℝ) / scale n q r + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hremReal : (g : ℝ) - K q r * d <
      (g : ℝ) / scale n q r + (2 * K q r + 1 : ℕ) := by
    have hcast : ((g - K q r * d : ℕ) : ℝ) <
        ((target + K q r : ℕ) : ℝ) := by exact_mod_cast hrem
    rw [Nat.cast_sub hmul] at hcast
    dsimp [target, stopTarget] at hcast
    push_cast at hcast ⊢
    linarith
  unfold density remaining
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  apply (div_lt_iff₀ hgR).2
  calc
    (g : ℝ) - K q r * d <
        (g : ℝ) / scale n q r + (2 * K q r + 1 : ℕ) := hremReal
    _ = (1 / (scale n q r : ℝ) + (2 * K q r + 1 : ℕ) / g) * g := by
      field_simp

lemma upperProfile_le_upperNat (g n q r i : ℕ)
    (hupper : 0 ≤ upperProfile g n q r i) :
    upperProfile g n q r i ≤ upperNat g n q r i := by
  exact Nat.le_ceil _

lemma lowerNat_le_lowerProfile (g n q r i : ℕ)
    (hlower : 0 ≤ lowerProfile g n q r i) :
    (lowerNat g n q r i : ℝ) ≤ lowerProfile g n q r i := by
  exact Nat.floor_le hlower

private lemma density_step_data
    {g K₀ i : ℕ} (hg : 0 < g) (hstep : K₀ * (i + 1) < g) :
    0 < density g K₀ i ∧
      0 ≤ (K₀ : ℝ) / g ∧
      (K₀ : ℝ) / g < density g K₀ i := by
  have hii : K₀ * i ≤ K₀ * (i + 1) :=
    Nat.mul_le_mul_left K₀ (by omega)
  have hx := density_pos hg (hii.trans_lt hstep)
  have hynext := density_pos hg hstep
  have hs := density_succ g K₀ i
  constructor
  · exact hx
  constructor
  · positivity
  · rw [hs] at hynext
    linarith

def degreeErrorGrowth (g n q r i : ℕ) : ℝ :=
  (profileA n q r * centerDegree n q r) *
    ((((4 * K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
        density g (K q r) (i + 1) ^ (4 * K q r - 1 - 1)) /
      (density g (K q r) i ^ (4 * K q r - 1) *
        density g (K q r) (i + 1) ^ (4 * K q r - 1)))

/-- The upper-endpoint derivative bound for the one-step increase of the
reciprocal degree error.  Unlike `degreeErrorGrowth`, which is the lower
derivative used in the drift inequalities, this quantity controls absolute
jumps. -/
def degreeErrorUpperGrowth (g n q r i : ℕ) : ℝ :=
  (profileA n q r * centerDegree n q r) *
    ((((4 * K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
        density g (K q r) i ^ (4 * K q r - 1 - 1)) /
      (density g (K q r) i ^ (4 * K q r - 1) *
        density g (K q r) (i + 1) ^ (4 * K q r - 1)))

def cliqueErrorGrowth (g n q r i : ℕ) : ℝ :=
  (profileA n q r * (g : ℝ) * centerDegree n q r / K q r) *
    ((((4 * K q r - 2 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
        density g (K q r) (i + 1) ^ (4 * K q r - 2 - 1)) /
      (density g (K q r) i ^ (4 * K q r - 2) *
        density g (K q r) (i + 1) ^ (4 * K q r - 2)))

def cliqueErrorUpperGrowth (g n q r i : ℕ) : ℝ :=
  (profileA n q r * (g : ℝ) * centerDegree n q r / K q r) *
    ((((4 * K q r - 2 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
        density g (K q r) i ^ (4 * K q r - 2 - 1)) /
      (density g (K q r) i ^ (4 * K q r - 2) *
        density g (K q r) (i + 1) ^ (4 * K q r - 2)))

lemma cliqueUpperProfile_eq_remaining_mul
    {g n q r i : ℕ} (hg : 0 < g) (hK : 1 < K q r)
    (hi : K q r * i < g) :
    cliqueUpperProfile g n q r i =
      remaining g (K q r) i / K q r * upperProfile g n q r i := by
  have hx := density_pos hg hi
  have hx0 := hx.ne'
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
  have hexp : 4 * K q r - 1 = (4 * K q r - 2) + 1 := by omega
  have hrem : remaining g (K q r) i =
      (g : ℝ) * density g (K q r) i := by
    unfold density
    field_simp [hg0]
  unfold cliqueUpperProfile upperProfile cliqueUpper degreeUpper cliqueCenter
    degreeCenter cliqueError degreeError
  rw [hrem]
  rw [hexp, pow_succ]
  have hpow : density g (K q r) i ^ K q r *
      density g (K q r) i ^ (4 * K q r - 2) =
        density g (K q r) i * density g (K q r) i ^ (4 * K q r - 2) *
          density g (K q r) i ^ (K q r - 1) := by
    calc
      _ = density g (K q r) i ^ (K q r + (4 * K q r - 2)) := by
        rw [pow_add]
      _ = density g (K q r) i ^
          (1 + (4 * K q r - 2) + (K q r - 1)) := by congr 1 <;> omega
      _ = _ := by rw [pow_add, pow_add, pow_one]
  field_simp [hx0, hg0, hK0]
  rw [hpow]
  ring

lemma cliqueLowerProfile_eq_remaining_mul
    {g n q r i : ℕ} (hg : 0 < g) (hK : 1 < K q r)
    (hi : K q r * i < g) :
    cliqueLowerProfile g n q r i =
      remaining g (K q r) i / K q r * lowerProfile g n q r i := by
  have hx := density_pos hg hi
  have hx0 := hx.ne'
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
  have hexp : 4 * K q r - 1 = (4 * K q r - 2) + 1 := by omega
  have hrem : remaining g (K q r) i =
      (g : ℝ) * density g (K q r) i := by
    unfold density
    field_simp [hg0]
  unfold cliqueLowerProfile lowerProfile cliqueLower degreeLower cliqueCenter
    degreeCenter cliqueError degreeError
  rw [hrem]
  rw [hexp, pow_succ]
  have hpow : density g (K q r) i ^ K q r *
      density g (K q r) i ^ (4 * K q r - 2) =
        density g (K q r) i * density g (K q r) i ^ (4 * K q r - 2) *
          density g (K q r) i ^ (K q r - 1) := by
    calc
      _ = density g (K q r) i ^ (K q r + (4 * K q r - 2)) := by
        rw [pow_add]
      _ = density g (K q r) i ^
          (1 + (4 * K q r - 2) + (K q r - 1)) := by congr 1 <;> omega
      _ = _ := by rw [pow_add, pow_add, pow_one]
  field_simp [hx0, hg0, hK0]
  rw [hpow]
  ring

lemma cliqueError_eq_remaining_mul
    {g n q r i : ℕ} (hg : 0 < g) (hK : 1 < K q r)
    (hi : K q r * i < g) :
    cliqueError (profileA n q r) (centerDegree n q r) g (K q r) i =
      remaining g (K q r) i / K q r *
        degreeError (profileA n q r) (centerDegree n q r) g (K q r) i := by
  have hu := cliqueUpperProfile_eq_remaining_mul
    (n := n) (q := q) (r := r) (i := i) hg hK hi
  have hl := cliqueLowerProfile_eq_remaining_mul
    (n := n) (q := q) (r := r) (i := i) hg hK hi
  unfold cliqueUpperProfile upperProfile cliqueUpper degreeUpper at hu
  unfold cliqueLowerProfile lowerProfile cliqueLower degreeLower at hl
  linarith

/-- The total-clique error growth is the edge error times its reciprocal
density derivative. -/
lemma cliqueErrorGrowth_eq
    {g n q r i : ℕ} (hg : 0 < g) (hK : 1 < K q r)
    (hstep : K q r * (i + 1) < g) :
    cliqueErrorGrowth g n q r i =
      (4 * K q r - 2 : ℕ) *
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i *
        (density g (K q r) i / density g (K q r) (i + 1)) := by
  have hii : K q r * i ≤ K q r * (i + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hx := density_pos hg (hii.trans_lt hstep)
  have hy := density_pos hg hstep
  have hx0 := hx.ne'
  have hy0 := hy.ne'
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
  have hexp : 4 * K q r - 1 = (4 * K q r - 2) + 1 := by omega
  have hyPow : density g (K q r) (i + 1) *
      density g (K q r) (i + 1) ^ (4 * K q r - 2 - 1) =
        density g (K q r) (i + 1) ^ (4 * K q r - 2) := by
    rw [← pow_succ']
    congr 2
    omega
  unfold cliqueErrorGrowth degreeError
  rw [hexp, pow_succ]
  field_simp [hx0, hy0, hg0, hK0]
  have hscaled := congrArg (fun z : ℝ ↦
    z * profileA n q r * centerDegree n q r * (4 * K q r - 2 : ℕ)) hyPow
  simpa [mul_assoc, mul_left_comm, mul_comm, Nat.add_comm] using hscaled

lemma cliqueError_succ_sub_le_upperGrowth
    {g n q r i : ℕ} (hg : 0 < g) (hK : 0 < K q r)
    (hstep : K q r * (i + 1) < g) :
    cliqueError (profileA n q r) (centerDegree n q r) g (K q r) (i + 1) -
        cliqueError (profileA n q r) (centerDegree n q r) g (K q r) i ≤
      cliqueErrorUpperGrowth g n q r i := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have hA : 0 ≤
      profileA n q r * (g : ℝ) * centerDegree n q r / K q r := by
    unfold profileA centerDegree
    positivity
  have h := reciprocal_pow_growth_upper (4 * K q r - 2) hA hx hh hhx
  rw [← hs] at h
  simpa [cliqueError, cliqueErrorUpperGrowth] using h

lemma cliqueErrorUpperGrowth_eq
    {g n q r i : ℕ} (hg : 0 < g) (hK : 1 < K q r)
    (hstep : K q r * (i + 1) < g) :
    cliqueErrorUpperGrowth g n q r i =
      (4 * K q r - 2 : ℕ) *
        cliqueError (profileA n q r) (centerDegree n q r)
          g (K q r) (i + 1) *
        ((K q r : ℝ) / g) *
        (1 / density g (K q r) i) := by
  have hii : K q r * i ≤ K q r * (i + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hx := density_pos hg (hii.trans_lt hstep)
  have hy := density_pos hg hstep
  have hx0 := hx.ne'
  have hy0 := hy.ne'
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
  have hexp : 4 * K q r - 2 = (4 * K q r - 2 - 1) + 1 := by omega
  have hxPow : density g (K q r) i *
      density g (K q r) i ^ (4 * K q r - 2 - 1) =
        density g (K q r) i ^ (4 * K q r - 2) := by
    rw [← pow_succ']
    congr 2
    omega
  unfold cliqueErrorUpperGrowth cliqueError
  rw [hexp, pow_succ]
  field_simp [hx0, hy0, hg0, hK0]
  have hscaled := congrArg (fun z : ℝ ↦
    z * profileA n q r * centerDegree n q r * (4 * K q r - 2 : ℕ)) hxPow
  simpa [mul_assoc, mul_left_comm, mul_comm, Nat.add_comm] using hscaled

lemma cliqueError_succ_sub_nonneg
    {g n q r i : ℕ} (hg : 0 < g) (hK : 0 < K q r)
    (hstep : K q r * (i + 1) < g) :
    0 ≤ cliqueError (profileA n q r) (centerDegree n q r) g (K q r) (i + 1) -
        cliqueError (profileA n q r) (centerDegree n q r) g (K q r) i := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have hy : 0 < density g (K q r) (i + 1) := by
    rw [hs]
    exact sub_pos.mpr hhx
  have hyx : density g (K q r) (i + 1) ≤ density g (K q r) i := by
    rw [hs]
    linarith
  have hpow : density g (K q r) (i + 1) ^ (4 * K q r - 2) ≤
      density g (K q r) i ^ (4 * K q r - 2) :=
    pow_le_pow_left₀ hy.le hyx _
  have hA : 0 ≤
      profileA n q r * (g : ℝ) * centerDegree n q r / K q r := by
    unfold profileA centerDegree
    positivity
  unfold cliqueError
  exact sub_nonneg.mpr
    (div_le_div_of_nonneg_left hA (pow_pos hy _) hpow)

lemma degreeErrorGrowth_eq
    {g n q r i : ℕ} (hg : 0 < g) (hK : 1 < K q r)
    (hstep : K q r * (i + 1) < g) :
    degreeErrorGrowth g n q r i =
      (4 * K q r - 1 : ℕ) *
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i *
        ((K q r : ℝ) / g) *
        (1 / density g (K q r) (i + 1)) := by
  have hii : K q r * i ≤ K q r * (i + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hx := density_pos hg (hii.trans_lt hstep)
  have hy := density_pos hg hstep
  have hx0 := hx.ne'
  have hy0 := hy.ne'
  have hexp : 4 * K q r - 1 = (4 * K q r - 1 - 1) + 1 := by omega
  have hyPow : density g (K q r) (i + 1) *
      density g (K q r) (i + 1) ^ (4 * K q r - 1 - 1) =
        density g (K q r) (i + 1) ^ (4 * K q r - 1) := by
    rw [← pow_succ']
    congr 2
    omega
  unfold degreeErrorGrowth degreeError
  rw [hexp, pow_succ]
  field_simp [hx0, hy0]
  have hinner : 4 * K q r - 1 - 1 + 1 - 1 = 4 * K q r - 1 - 1 := by omega
  have hright : 4 * K q r - 1 - 1 + 1 = 4 * K q r - 1 := by omega
  rw [hinner, hright]
  calc
    profileA n q r * centerDegree n q r *
        density g (K q r) (i + 1) ^ (4 * K q r - 1 - 1) *
          density g (K q r) (i + 1) =
      profileA n q r * centerDegree n q r *
        (density g (K q r) (i + 1) *
          density g (K q r) (i + 1) ^ (4 * K q r - 1 - 1)) := by ring
    _ = profileA n q r * centerDegree n q r *
        density g (K q r) (i + 1) ^ (4 * K q r - 1) := by rw [hyPow]

lemma degreeError_succ_sub_le_upperGrowth
    {g n q r i : ℕ} (hg : 0 < g)
    (hstep : K q r * (i + 1) < g) :
    degreeError (profileA n q r) (centerDegree n q r) g (K q r) (i + 1) -
        degreeError (profileA n q r) (centerDegree n q r) g (K q r) i ≤
      degreeErrorUpperGrowth g n q r i := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have hA : 0 ≤ profileA n q r * centerDegree n q r := by
    unfold profileA centerDegree
    positivity
  have h := reciprocal_pow_growth_upper (4 * K q r - 1) hA hx hh hhx
  rw [← hs] at h
  simpa [degreeError, degreeErrorUpperGrowth] using h

lemma degreeErrorUpperGrowth_eq
    {g n q r i : ℕ} (hg : 0 < g) (hK : 1 < K q r)
    (hstep : K q r * (i + 1) < g) :
    degreeErrorUpperGrowth g n q r i =
      (4 * K q r - 1 : ℕ) *
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) (i + 1) *
        ((K q r : ℝ) / g) *
        (1 / density g (K q r) i) := by
  have hii : K q r * i ≤ K q r * (i + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hx := density_pos hg (hii.trans_lt hstep)
  have hy := density_pos hg hstep
  have hx0 := hx.ne'
  have hy0 := hy.ne'
  have hexp : 4 * K q r - 1 = (4 * K q r - 1 - 1) + 1 := by omega
  have hxPow : density g (K q r) i *
      density g (K q r) i ^ (4 * K q r - 1 - 1) =
        density g (K q r) i ^ (4 * K q r - 1) := by
    rw [← pow_succ']
    congr 2
    omega
  unfold degreeErrorUpperGrowth degreeError
  rw [hexp, pow_succ]
  field_simp [hx0, hy0]
  have hscaled := congrArg (fun z : ℝ ↦
    z * profileA n q r * centerDegree n q r * (4 * K q r - 1 : ℕ)) hxPow
  simpa [mul_assoc, mul_left_comm, mul_comm, Nat.add_comm] using hscaled

lemma degreeError_succ_sub_nonneg
    {g n q r i : ℕ} (hg : 0 < g)
    (hstep : K q r * (i + 1) < g) :
    0 ≤ degreeError (profileA n q r) (centerDegree n q r) g (K q r) (i + 1) -
        degreeError (profileA n q r) (centerDegree n q r) g (K q r) i := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have hy : 0 < density g (K q r) (i + 1) := by
    rw [hs]
    exact sub_pos.mpr hhx
  have hyx : density g (K q r) (i + 1) ≤ density g (K q r) i := by
    rw [hs]
    linarith
  have hpow : density g (K q r) (i + 1) ^ (4 * K q r - 1) ≤
      density g (K q r) i ^ (4 * K q r - 1) :=
    pow_le_pow_left₀ hy.le hyx _
  have hA : 0 ≤ profileA n q r * centerDegree n q r := by
    unfold profileA centerDegree
    positivity
  unfold degreeError
  exact sub_nonneg.mpr
    (div_le_div_of_nonneg_left hA (pow_pos hy _) hpow)

lemma degreeCenter_sub_succ_nonneg
    {g n q r i : ℕ} (hg : 0 < g)
    (hstep : K q r * (i + 1) < g) :
    0 ≤ degreeCenter (centerDegree n q r) g (K q r) i -
      degreeCenter (centerDegree n q r) g (K q r) (i + 1) := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have hpow := pow_sub_pow_nonneg (K q r - 1) hh hhx.le
  rw [← hs] at hpow
  unfold degreeCenter
  have hD : 0 ≤ centerDegree n q r := by
    unfold centerDegree
    positivity
  simpa [mul_sub] using mul_nonneg hD hpow

lemma degreeCenter_sub_succ_le
    {g n q r i : ℕ} (hg : 0 < g)
    (hstep : K q r * (i + 1) < g) :
    degreeCenter (centerDegree n q r) g (K q r) i -
        degreeCenter (centerDegree n q r) g (K q r) (i + 1) ≤
      centerDegree n q r *
        (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
          density g (K q r) i ^ (K q r - 2)) := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have h := pow_sub_pow_le_mul_pow_pred (K q r - 1) hh hhx.le
  have hD : 0 ≤ centerDegree n q r := by unfold centerDegree; positivity
  have hscaled := mul_le_mul_of_nonneg_left h hD
  rw [← hs] at hscaled
  have hexp : K q r - 1 - 1 = K q r - 2 := by omega
  rw [hexp] at hscaled
  unfold degreeCenter
  linarith

lemma cliqueCenter_sub_succ_nonneg
    {g n q r i : ℕ} (hg : 0 < g) (hK : 0 < K q r)
    (hstep : K q r * (i + 1) < g) :
    0 ≤ cliqueCenter (centerDegree n q r) g (K q r) i -
      cliqueCenter (centerDegree n q r) g (K q r) (i + 1) := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have hpow := pow_sub_pow_nonneg (K q r) hh hhx.le
  rw [← hs] at hpow
  unfold cliqueCenter
  have hD : 0 ≤ (g : ℝ) * centerDegree n q r / K q r := by
    unfold centerDegree
    positivity
  simpa [mul_sub] using mul_nonneg hD hpow

lemma cliqueCenter_sub_succ_le
    {g n q r i : ℕ} (hg : 0 < g) (hK : 0 < K q r)
    (hstep : K q r * (i + 1) < g) :
    cliqueCenter (centerDegree n q r) g (K q r) i -
        cliqueCenter (centerDegree n q r) g (K q r) (i + 1) ≤
      ((g : ℝ) * centerDegree n q r / K q r) *
        ((K q r : ℝ) * ((K q r : ℝ) / g) *
          density g (K q r) i ^ (K q r - 1)) := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have h := pow_sub_pow_le_mul_pow_pred (K q r) hh hhx.le
  have hD : 0 ≤ (g : ℝ) * centerDegree n q r / K q r := by
    unfold centerDegree
    positivity
  have hscaled := mul_le_mul_of_nonneg_left h hD
  rw [← hs] at hscaled
  have hexp : K q r - 1 = K q r - 1 := rfl
  unfold cliqueCenter
  linarith

lemma degreeProfiles_step_abs_le
    {g n q r i : ℕ} (hg : 0 < g)
    (hstep : K q r * (i + 1) < g) :
    |upperProfile g n q r (i + 1) - upperProfile g n q r i| ≤
        centerDegree n q r *
            (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
              density g (K q r) i ^ (K q r - 2)) +
          degreeErrorUpperGrowth g n q r i ∧
    |lowerProfile g n q r (i + 1) - lowerProfile g n q r i| ≤
        centerDegree n q r *
            (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
              density g (K q r) i ^ (K q r - 2)) +
          degreeErrorUpperGrowth g n q r i := by
  let c := degreeCenter (centerDegree n q r) g (K q r) i -
    degreeCenter (centerDegree n q r) g (K q r) (i + 1)
  let e := degreeError (profileA n q r) (centerDegree n q r)
      g (K q r) (i + 1) -
    degreeError (profileA n q r) (centerDegree n q r) g (K q r) i
  let C := centerDegree n q r *
    (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
      density g (K q r) i ^ (K q r - 2))
  let G := degreeErrorUpperGrowth g n q r i
  have hc0 : 0 ≤ c := by
    simpa [c] using degreeCenter_sub_succ_nonneg hg hstep
  have he0 : 0 ≤ e := by
    simpa [e] using degreeError_succ_sub_nonneg hg hstep
  have hc : c ≤ C := by
    simpa [c, C] using degreeCenter_sub_succ_le hg hstep
  have he : e ≤ G := by
    simpa [e, G] using degreeError_succ_sub_le_upperGrowth hg hstep
  constructor
  · calc
      |upperProfile g n q r (i + 1) - upperProfile g n q r i| = |e - c| := by
        dsimp [e, c]
        unfold upperProfile degreeUpper
        congr 1
        ring
      _ ≤ |e| + |c| := abs_sub e c
      _ = e + c := by rw [abs_of_nonneg he0, abs_of_nonneg hc0]
      _ ≤ C + G := by linarith
      _ = _ := by rfl
  · calc
      |lowerProfile g n q r (i + 1) - lowerProfile g n q r i| = |-(c + e)| := by
        dsimp [e, c]
        unfold lowerProfile degreeLower
        congr 1
        ring
      _ = c + e := by rw [abs_neg, abs_of_nonneg (add_nonneg hc0 he0)]
      _ ≤ C + G := by linarith
      _ = _ := by rfl

lemma cliqueProfiles_step_abs_le
    {g n q r i : ℕ} (hg : 0 < g) (hK : 0 < K q r)
    (hstep : K q r * (i + 1) < g) :
    |cliqueUpperProfile g n q r (i + 1) - cliqueUpperProfile g n q r i| ≤
        ((g : ℝ) * centerDegree n q r / K q r) *
            ((K q r : ℝ) * ((K q r : ℝ) / g) *
              density g (K q r) i ^ (K q r - 1)) +
          cliqueErrorUpperGrowth g n q r i ∧
    |cliqueLowerProfile g n q r (i + 1) - cliqueLowerProfile g n q r i| ≤
        ((g : ℝ) * centerDegree n q r / K q r) *
            ((K q r : ℝ) * ((K q r : ℝ) / g) *
              density g (K q r) i ^ (K q r - 1)) +
          cliqueErrorUpperGrowth g n q r i := by
  let c := cliqueCenter (centerDegree n q r) g (K q r) i -
    cliqueCenter (centerDegree n q r) g (K q r) (i + 1)
  let e := cliqueError (profileA n q r) (centerDegree n q r)
      g (K q r) (i + 1) -
    cliqueError (profileA n q r) (centerDegree n q r) g (K q r) i
  let C := ((g : ℝ) * centerDegree n q r / K q r) *
    ((K q r : ℝ) * ((K q r : ℝ) / g) *
      density g (K q r) i ^ (K q r - 1))
  let G := cliqueErrorUpperGrowth g n q r i
  have hc0 : 0 ≤ c := by
    simpa [c] using cliqueCenter_sub_succ_nonneg hg hK hstep
  have he0 : 0 ≤ e := by
    simpa [e] using cliqueError_succ_sub_nonneg hg hK hstep
  have hc : c ≤ C := by
    simpa [c, C] using cliqueCenter_sub_succ_le hg hK hstep
  have he : e ≤ G := by
    simpa [e, G] using cliqueError_succ_sub_le_upperGrowth hg hK hstep
  constructor
  · calc
      |cliqueUpperProfile g n q r (i + 1) - cliqueUpperProfile g n q r i| =
          |e - c| := by
        dsimp [e, c]
        unfold cliqueUpperProfile cliqueUpper
        congr 1
        ring
      _ ≤ |e| + |c| := abs_sub e c
      _ = e + c := by rw [abs_of_nonneg he0, abs_of_nonneg hc0]
      _ ≤ C + G := by linarith
      _ = _ := by rfl
  · calc
      |cliqueLowerProfile g n q r (i + 1) - cliqueLowerProfile g n q r i| =
          |-(c + e)| := by
        dsimp [e, c]
        unfold cliqueLowerProfile cliqueLower
        congr 1
        ring
      _ = c + e := by rw [abs_neg, abs_of_nonneg (add_nonneg hc0 he0)]
      _ ≤ C + G := by linarith
      _ = _ := by rfl

/-- Throughout the stopped interval, the reciprocal error is at most a
`1/T` fraction of the mean-field degree. -/
lemma degreeError_le_center_div_scale
    {g n q r i : ℕ} (hK : 1 < K q r) (hT : 0 < scale n q r)
    (hx : 0 < density g (K q r) i)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i) :
    degreeError (profileA n q r) (centerDegree n q r) g (K q r) i ≤
      degreeCenter (centerDegree n q r) g (K q r) i /
        scale n q r := by
  let T : ℝ := scale n q r
  let x : ℝ := density g (K q r) i
  let D : ℝ := centerDegree n q r
  have hTR : 0 < T := by
    dsimp [T]
    exact_mod_cast hT
  have hD : 0 ≤ D := by
    dsimp [D, centerDegree]
    positivity
  have hTx : 1 ≤ T * x := by
    have := mul_le_mul_of_nonneg_left hlower hTR.le
    simpa [T, x, hTR.ne'] using this
  let m := 5 * K q r - 2
  have hm : 0 < m := by dsimp [m]; omega
  have hpowOne : (1 : ℝ) ≤ (T * x) ^ m := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hTx m
  have hP : 5 * K q r - 1 = 1 + m := by dsimp [m]; omega
  have hs : (4 * K q r - 1) + (K q r - 1) = m := by dsimp [m]; omega
  have hpower : T ≤
      T ^ (5 * K q r - 1) * x ^ (4 * K q r - 1) * x ^ (K q r - 1) := by
    calc
      T ≤ T * (T * x) ^ m := by
        simpa using mul_le_mul_of_nonneg_left hpowOne hTR.le
      _ = T ^ (5 * K q r - 1) * x ^ (4 * K q r - 1) *
          x ^ (K q r - 1) := by
        have hxpow : x ^ m = x ^ (4 * K q r - 1) * x ^ (K q r - 1) := by
          rw [← pow_add, hs]
        rw [hP, pow_add, pow_one, mul_pow, hxpow]
        ring
  have hden : 0 < T ^ (5 * K q r - 1) * x ^ (4 * K q r - 1) := by
    positivity
  have heq : degreeError (profileA n q r) D g (K q r) i =
      D / (T ^ (5 * K q r - 1) * x ^ (4 * K q r - 1)) := by
    dsimp [degreeError, profileA, T, x]
    field_simp
  rw [heq]
  apply (div_le_iff₀ hden).2
  dsimp [degreeCenter, x, T]
  calc
    D ≤ (D * density g (K q r) i ^ (K q r - 1) *
        ((scale n q r : ℝ) ^ (5 * K q r - 1) *
          density g (K q r) i ^ (4 * K q r - 1))) /
          scale n q r := by
      apply (le_div_iff₀ hTR).2
      exact mul_le_mul_of_nonneg_left hpower hD |>.trans_eq (by ring)
    _ = D * density g (K q r) i ^ (K q r - 1) /
        scale n q r *
          ((scale n q r : ℝ) ^ (5 * K q r - 1) *
            density g (K q r) i ^ (4 * K q r - 1)) := by
      field_simp

/-- On a density at most one, the reciprocal degree error is at least its
initial value. -/
lemma initial_degreeError_le
    {g n q r i : ℕ} (hK : 0 < K q r) (hT : 0 < scale n q r)
    (hx : 0 < density g (K q r) i)
    (hupper : density g (K q r) i ≤ 1) :
    centerDegree n q r /
        (scale n q r : ℝ) ^ (5 * K q r - 1) ≤
      degreeError (profileA n q r) (centerDegree n q r)
        g (K q r) i := by
  have hD : 0 ≤ centerDegree n q r := by
    unfold centerDegree
    positivity
  have hTreal : (0 : ℝ) < scale n q r := by exact_mod_cast hT
  have hpow : density g (K q r) i ^ (4 * K q r - 1) ≤ 1 := by
    exact pow_le_one₀ hx.le hupper
  have hpowPos : 0 < density g (K q r) i ^ (4 * K q r - 1) :=
    pow_pos hx _
  unfold degreeError profileA
  rw [one_div]
  calc
    centerDegree n q r /
          (scale n q r : ℝ) ^ (5 * K q r - 1) =
        ((scale n q r : ℝ) ^ (5 * K q r - 1))⁻¹ *
          centerDegree n q r := by ring
    _ ≤ (((scale n q r : ℝ) ^ (5 * K q r - 1))⁻¹ *
          centerDegree n q r) /
        density g (K q r) i ^ (4 * K q r - 1) := by
      have hbase : 0 ≤
          ((scale n q r : ℝ) ^ (5 * K q r - 1))⁻¹ *
            centerDegree n q r :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg hTreal.le _)) hD
      exact (le_div_iff₀ hpowPos).2 (by
        nlinarith [mul_nonneg hbase (sub_nonneg.mpr hpow)])
    _ = _ := by ring

/-- The total-clique error growth contains at least its displayed
reciprocal derivative multiple of the current edge error. -/
lemma degreeError_mul_le_cliqueErrorGrowth
    {g n q r i : ℕ} (hg : 0 < g) (hK : 1 < K q r)
    (hstep : K q r * (i + 1) < g) :
    ((4 * K q r - 2 : ℕ) : ℝ) *
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i ≤
      cliqueErrorGrowth g n q r i := by
  have hii : K q r * i ≤ K q r * (i + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hx := density_pos hg (hii.trans_lt hstep)
  have hy := density_pos hg hstep
  have hs := density_succ g (K q r) i
  have hyx : density g (K q r) (i + 1) ≤ density g (K q r) i := by
    rw [hs]
    have : (0 : ℝ) ≤ (K q r : ℝ) / g := by positivity
    linarith
  have hratio : 1 ≤
      density g (K q r) i / density g (K q r) (i + 1) := by
    exact (le_div_iff₀ hy).2 (by simpa using hyx)
  rw [cliqueErrorGrowth_eq hg hK hstep]
  have hE : 0 ≤
      degreeError (profileA n q r) (centerDegree n q r)
        g (K q r) i := by
    unfold degreeError profileA centerDegree
    positivity
  have hc : (0 : ℝ) ≤ (4 * K q r - 2 : ℕ) := by positivity
  simpa using mul_le_mul_of_nonneg_left hratio (mul_nonneg hc hE)

/-- Checked upper degree-profile finite difference. -/
lemma upperProfile_sub_succ_le
    {g n q r i : ℕ} (hg : 0 < g)
    (hstep : K q r * (i + 1) < g) :
    upperProfile g n q r i - upperProfile g n q r (i + 1) ≤
      centerDegree n q r *
          (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
            density g (K q r) i ^ (K q r - 2)) -
        degreeErrorGrowth g n q r i := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have hD : 0 ≤ centerDegree n q r := by
    unfold centerDegree
    positivity
  have hexp : K q r - 1 - 1 = K q r - 2 := by omega
  have h := reciprocal_power_upper_sub_next_le
    (E := profileA n q r * centerDegree n q r)
    (D := centerDegree n q r) (x := density g (K q r) i)
    (h := (K q r : ℝ) / g) (K q r - 1) (4 * K q r - 1)
    (by unfold profileA; positivity) hD hx hh hhx
  rw [← hs] at h
  rw [hexp] at h
  simpa [upperProfile, degreeUpper, degreeCenter, degreeError,
    degreeErrorGrowth] using h

/-- Checked lower degree-profile finite difference. -/
lemma lowerProfile_sub_succ_ge
    {g n q r i : ℕ} (hg : 0 < g)
    (hstep : K q r * (i + 1) < g) :
        centerDegree n q r *
          (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
            density g (K q r) (i + 1) ^ (K q r - 2)) +
        degreeErrorGrowth g n q r i ≤
      lowerProfile g n q r i - lowerProfile g n q r (i + 1) := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have hD : 0 ≤ centerDegree n q r := by
    unfold centerDegree
    positivity
  have hexp : K q r - 1 - 1 = K q r - 2 := by omega
  have h := reciprocal_power_lower_sub_next_ge
    (E := profileA n q r * centerDegree n q r)
    (D := centerDegree n q r) (x := density g (K q r) i)
    (h := (K q r : ℝ) / g) (K q r - 1) (4 * K q r - 1)
    (by unfold profileA; positivity) hD hx hh hhx
  rw [← hs] at h
  rw [hexp] at h
  simpa [lowerProfile, degreeLower, degreeCenter, degreeError,
    degreeErrorGrowth] using h

/-- Checked upper total-clique profile finite difference. -/
lemma cliqueUpperProfile_sub_succ_le
    {g n q r i : ℕ} (hg : 0 < g) (hK : 0 < K q r)
    (hstep : K q r * (i + 1) < g) :
    cliqueUpperProfile g n q r i - cliqueUpperProfile g n q r (i + 1) ≤
      ((g : ℝ) * centerDegree n q r / K q r) *
          ((K q r : ℝ) * ((K q r : ℝ) / g) *
            density g (K q r) i ^ (K q r - 1)) -
        cliqueErrorGrowth g n q r i := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have hD : 0 ≤ (g : ℝ) * centerDegree n q r / K q r := by
    unfold centerDegree
    positivity
  have hA : 0 ≤ profileA n q r := by
    unfold profileA
    positivity
  have hE : 0 ≤
      profileA n q r * (g : ℝ) * centerDegree n q r / K q r := by
    calc
      0 ≤ profileA n q r *
          ((g : ℝ) * centerDegree n q r / K q r) := mul_nonneg hA hD
      _ = profileA n q r * (g : ℝ) * centerDegree n q r / K q r := by ring
  have h := reciprocal_power_upper_sub_next_le
    (E := profileA n q r * (g : ℝ) * centerDegree n q r / K q r)
    (D := (g : ℝ) * centerDegree n q r / K q r)
    (x := density g (K q r) i) (h := (K q r : ℝ) / g)
    (K q r) (4 * K q r - 2)
    hE hD hx hh hhx
  rw [← hs] at h
  simpa [cliqueUpperProfile, cliqueUpper, cliqueCenter, cliqueError,
    cliqueErrorGrowth] using h

/-- Checked lower total-clique profile finite difference. -/
lemma cliqueLowerProfile_sub_succ_ge
    {g n q r i : ℕ} (hg : 0 < g) (hK : 0 < K q r)
    (hstep : K q r * (i + 1) < g) :
    ((g : ℝ) * centerDegree n q r / K q r) *
          ((K q r : ℝ) * ((K q r : ℝ) / g) *
            density g (K q r) (i + 1) ^ (K q r - 1)) +
        cliqueErrorGrowth g n q r i ≤
      cliqueLowerProfile g n q r i - cliqueLowerProfile g n q r (i + 1) := by
  obtain ⟨hx, hh, hhx⟩ := density_step_data hg hstep
  have hs := density_succ g (K q r) i
  have hD : 0 ≤ (g : ℝ) * centerDegree n q r / K q r := by
    unfold centerDegree
    positivity
  have hA : 0 ≤ profileA n q r := by
    unfold profileA
    positivity
  have hE : 0 ≤
      profileA n q r * (g : ℝ) * centerDegree n q r / K q r := by
    calc
      0 ≤ profileA n q r *
          ((g : ℝ) * centerDegree n q r / K q r) := mul_nonneg hA hD
      _ = profileA n q r * (g : ℝ) * centerDegree n q r / K q r := by ring
  have h := reciprocal_power_lower_sub_next_ge
    (E := profileA n q r * (g : ℝ) * centerDegree n q r / K q r)
    (D := (g : ℝ) * centerDegree n q r / K q r)
    (x := density g (K q r) i) (h := (K q r : ℝ) / g)
    (K q r) (4 * K q r - 2)
    hE hD hx hh hhx
  rw [← hs] at h
  simpa [cliqueLowerProfile, cliqueLower, cliqueCenter, cliqueError,
    cliqueErrorGrowth] using h

/-- A transparent pointwise margin implies the rounded upper total-clique
drift inequality.  The margin is later supplied uniformly by the
asymptotic codegree estimate. -/
lemma cliqueUpper_scalar_of_error_margin
    {g n q r i C : ℕ} (hg : 0 < g) (hK : 2 < K q r)
    (hC : 0 < C) (hstep : K q r * (i + 1) < g)
    (hmargin :
      ((K q r : ℝ) * (K q r + 1) * C) ≤
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i) :
    cliqueUpperProfile g n q r i -
        cliqueUpperProfile g n q r (i + 1) ≤
      (K q r : ℝ) *
        (lowerProfile g n q r i - 1 - (K q r : ℝ) * C) := by
  let E := degreeError (profileA n q r) (centerDegree n q r)
    g (K q r) i
  let Z := degreeCenter (centerDegree n q r) g (K q r) i
  have hdiff := cliqueUpperProfile_sub_succ_le
    (n := n) (q := q) (r := r) (i := i) hg (by omega) hstep
  have hcenter :
      ((g : ℝ) * centerDegree n q r / K q r) *
          ((K q r : ℝ) * ((K q r : ℝ) / g) *
            density g (K q r) i ^ (K q r - 1)) =
        (K q r : ℝ) * Z := by
    dsimp [Z, degreeCenter]
    have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
    field_simp [hg0, hK0]
  have hgrowth : ((4 * K q r - 2 : ℕ) : ℝ) * E ≤
      cliqueErrorGrowth g n q r i := by
    simpa [E] using degreeError_mul_le_cliqueErrorGrowth hg (by omega) hstep
  have hCReal : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hKReal : (3 : ℝ) ≤ K q r := by exact_mod_cast hK
  have hcoef : ((4 * K q r - 2 : ℕ) : ℝ) =
      4 * (K q r : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 4 * K q r)]
    norm_num
  have hsurplus :
      (K q r : ℝ) * E +
          (K q r : ℝ) * (1 + (K q r : ℝ) * C) ≤
        ((4 * K q r - 2 : ℕ) : ℝ) * E := by
    have hE : 0 ≤ E := by
      dsimp [E]
      have hii : K q r * i ≤ K q r * (i + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hx := density_pos hg (hii.trans_lt hstep)
      unfold degreeError profileA centerDegree
      positivity
    change ((K q r : ℝ) * (K q r + 1) * C) ≤ E at hmargin
    have htarget :
        (K q r : ℝ) * (1 + (K q r : ℝ) * C) ≤ E := by
      nlinarith
    have hcoefE : E ≤ ((K q r : ℝ) - 2) * E := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith :
        (0 : ℝ) ≤ K q r - 3)) hE]
    rw [hcoef]
    nlinarith
  have hmain :
      cliqueUpperProfile g n q r i -
          cliqueUpperProfile g n q r (i + 1) ≤
        (K q r : ℝ) * Z -
          ((4 * K q r - 2 : ℕ) : ℝ) * E := by
    rw [hcenter] at hdiff
    linarith
  dsimp [lowerProfile, degreeLower, Z, E]
  linarith

/-- If the host is large compared with the fixed profile scale, movement
of the mean-field degree centre in one step costs at most half of the
current reciprocal error. -/
lemma degreeCenter_step_cost_le_half_error
    {g n q r i : ℕ} (hg : 0 < g) (hK : 1 < K q r)
    (hT : 0 < scale n q r)
    (hstep : K q r * (i + 1) < g)
    (hupper : density g (K q r) i ≤ 1)
    (hhost :
      2 * (K q r : ℝ) ^ 2 * (K q r - 1 : ℕ) *
          (scale n q r : ℝ) ^ (5 * K q r - 1) ≤ g) :
    (K q r : ℝ) *
          (degreeCenter (centerDegree n q r) g (K q r) i -
            degreeCenter (centerDegree n q r) g (K q r) (i + 1)) ≤
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i / 2 := by
  let x := density g (K q r) i
  let y := density g (K q r) (i + 1)
  let T : ℝ := scale n q r
  let D := centerDegree n q r
  let P := 5 * K q r - 1
  let Q := 4 * K q r - 1
  let m := K q r - 1
  have hii : K q r * i ≤ K q r * (i + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hx : 0 < x := by
    dsimp [x]
    exact density_pos hg (hii.trans_lt hstep)
  have hy : 0 < y := by
    dsimp [y]
    exact density_pos hg hstep
  have hTreal : 0 < T := by dsimp [T]; exact_mod_cast hT
  have hgReal : (0 : ℝ) < g := by exact_mod_cast hg
  have hD : 0 ≤ D := by dsimp [D, centerDegree]; positivity
  have hs : y = x - (K q r : ℝ) / g := by
    simpa [x, y] using density_succ g (K q r) i
  have hh : 0 ≤ (K q r : ℝ) / g := by positivity
  have hhx : (K q r : ℝ) / g ≤ x := by
    linarith
  have hpowdiff : x ^ m - y ^ m ≤
      (m : ℝ) * ((K q r : ℝ) / g) * x ^ (m - 1) := by
    rw [hs]
    exact pow_sub_pow_le_mul_pow_pred m hh hhx
  have hcenterDiff :
      D * (x ^ m - y ^ m) ≤
        D * ((m : ℝ) * ((K q r : ℝ) / g) * x ^ (m - 1)) :=
    mul_le_mul_of_nonneg_left hpowdiff hD
  have hcoef :
      (K q r : ℝ) ^ 2 * (m : ℝ) / g ≤
        1 / (2 * T ^ P) := by
    have hden : 0 < 2 * T ^ P := by positivity
    apply (div_le_iff₀ hgReal).2
    calc
      (K q r : ℝ) ^ 2 * (m : ℝ) ≤ g / (2 * T ^ P) := by
        apply (le_div_iff₀ hden).2
        dsimp [T, P, m] at hhost ⊢
        nlinarith
      _ = 1 / (2 * T ^ P) * g := by ring
  have hxpow : x ^ (m - 1) ≤ 1 := by
    exact pow_le_one₀ hx.le (by simpa [x] using hupper)
  have hqpow : 0 < x ^ Q := pow_pos hx _
  have honeInv : (1 : ℝ) ≤ 1 / x ^ Q := by
    apply (le_div_iff₀ hqpow).2
    have : x ^ Q ≤ 1 := pow_le_one₀ hx.le (by simpa [x] using hupper)
    simpa using this
  have hscaleFactor : 0 ≤ 1 / (2 * T ^ P) := by
    exact div_nonneg (by norm_num) (by positivity)
  have hmain :
      (K q r : ℝ) * D * (x ^ m - y ^ m) ≤
        D / (2 * T ^ P * x ^ Q) := by
    calc
      (K q r : ℝ) * D * (x ^ m - y ^ m) ≤
          (K q r : ℝ) * D *
            ((m : ℝ) * ((K q r : ℝ) / g) * x ^ (m - 1)) := by
        gcongr
      _ = D * ((K q r : ℝ) ^ 2 * (m : ℝ) / g) * x ^ (m - 1) := by ring
      _ ≤ D * (1 / (2 * T ^ P)) * x ^ (m - 1) := by gcongr
      _ ≤ D * (1 / (2 * T ^ P)) := by
        simpa using mul_le_mul_of_nonneg_left hxpow
          (mul_nonneg hD hscaleFactor)
      _ ≤ D * (1 / (2 * T ^ P)) * (1 / x ^ Q) := by
        simpa using mul_le_mul_of_nonneg_left honeInv
          (mul_nonneg hD hscaleFactor)
      _ = D / (2 * T ^ P * x ^ Q) := by field_simp
  dsimp [degreeCenter, degreeError, profileA, x, y, T, D, P, Q, m]
  convert hmain using 1 <;> ring

/-- The upper edge-profile scalar inequality follows from an error margin
of four times the rounding/codegree cost and a critical window no wider
than one quarter of the current reciprocal error. -/
lemma upperEdge_profile_scalar_of_error_margin
    {g n q r i C : ℕ} {window : ℝ}
    (hg : 0 < g) (hK : 2 < K q r) (hstep : K q r * (i + 1) < g)
    (hwindow0 : 0 ≤ window)
    (hwindowE : window ≤
      degreeError (profileA n q r) (centerDegree n q r)
        g (K q r) i / 4)
    (herrorCenter :
      degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i ≤
        degreeCenter (centerDegree n q r) g (K q r) i)
    (hmargin :
      4 * (1 + (K q r : ℝ) * C) ≤
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i) :
    cliqueUpperProfile g n q r i *
        (upperProfile g n q r i - upperProfile g n q r (i + 1)) ≤
      (upperProfile g n q r i - window) * (K q r - 1 : ℕ) *
        ((lowerNat g n q r i : ℝ) - (K q r : ℝ) * C) := by
  let x := density g (K q r) i
  let y := density g (K q r) (i + 1)
  let E := degreeError (profileA n q r) (centerDegree n q r)
    g (K q r) i
  let Z := degreeCenter (centerDegree n q r) g (K q r) i
  let P := upperProfile g n q r i
  let m := K q r - 1
  let Q := cliqueUpperProfile g n q r i
  have hii : K q r * i ≤ K q r * (i + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hx : 0 < x := by dsimp [x]; exact density_pos hg (hii.trans_lt hstep)
  have hy : 0 < y := by dsimp [y]; exact density_pos hg hstep
  have hxy : y ≤ x := by
    rw [show y = x - (K q r : ℝ) / g by
      simpa [x, y] using density_succ g (K q r) i]
    have : (0 : ℝ) ≤ (K q r : ℝ) / g := by positivity
    linarith
  have hP : P = Z + E := by
    rfl
  have hE : 0 ≤ E := by
    dsimp [E]
    unfold degreeError profileA centerDegree
    positivity
  have hZ : 0 ≤ Z := by
    dsimp [Z, degreeCenter, centerDegree]
    positivity
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hQ0 : 0 ≤ Q := by
    dsimp [Q, cliqueUpperProfile, cliqueUpper, cliqueCenter, cliqueError,
      centerDegree, profileA]
    positivity
  have hfactor : Q = remaining g (K q r) i / K q r * P := by
    simpa [Q, P] using cliqueUpperProfile_eq_remaining_mul hg (by omega)
      (hii.trans_lt hstep)
  have hrem : remaining g (K q r) i = (g : ℝ) * x := by
    dsimp [x, density]
    field_simp
  have hdiff := upperProfile_sub_succ_le
    (n := n) (q := q) (r := r) (i := i) hg hstep
  have hgrowth := degreeErrorGrowth_eq
    (n := n) (q := q) (r := r) (i := i) hg (by omega) hstep
  have hcenterTerm :
      Q * (centerDegree n q r *
          (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
            x ^ (K q r - 2))) = (m : ℝ) * P * Z := by
    rw [hfactor, hrem]
    dsimp [Z, m, degreeCenter]
    have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
    have hexp : K q r - 1 = (K q r - 2) + 1 := by omega
    rw [hexp, pow_succ]
    field_simp [hg0, hK0]
    ring
  have hratio : 1 ≤ x / y := (le_div_iff₀ hy).2 (by simpa using hxy)
  have hgrowthProduct :
      ((4 * K q r - 1 : ℕ) : ℝ) * E * P ≤
        Q * degreeErrorGrowth g n q r i := by
    rw [hgrowth, hfactor, hrem]
    have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
    have hcoeff : (0 : ℝ) ≤ (4 * K q r - 1 : ℕ) := by positivity
    have hbase : 0 ≤ ((4 * K q r - 1 : ℕ) : ℝ) * E * P := by positivity
    calc
      ((4 * K q r - 1 : ℕ) : ℝ) * E * P ≤
          ((4 * K q r - 1 : ℕ) : ℝ) * E * P * (x / y) := by
        simpa using mul_le_mul_of_nonneg_left hratio hbase
      _ = (↑g * x / ↑(K q r) * P) *
          (↑(4 * K q r - 1) * E * (↑(K q r) / ↑g) * (1 / y)) := by
        field_simp [hg0, hK0, hy.ne']
  have hlhs :
      Q * (upperProfile g n q r i - upperProfile g n q r (i + 1)) ≤
        (m : ℝ) * P * Z - ((4 * K q r - 1 : ℕ) : ℝ) * E * P := by
    calc
      _ ≤ Q * (centerDegree n q r *
          (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
            density g (K q r) i ^ (K q r - 2)) -
          degreeErrorGrowth g n q r i) :=
        mul_le_mul_of_nonneg_left hdiff hQ0
      _ = (m : ℝ) * P * Z - Q * degreeErrorGrowth g n q r i := by
        rw [mul_sub, hcenterTerm]
      _ ≤ _ := by linarith
  have hlower : Z - E - 1 < (lowerNat g n q r i : ℝ) := by
    have hnonneg : 0 ≤ lowerProfile g n q r i := by
      dsimp [lowerProfile, degreeLower]
      change E ≤ Z at herrorCenter
      linarith
    simpa [lowerNat, lowerProfile, degreeLower, Z, E] using
      Erdos722.NibbleScalar.floor_profile_sub_one_lt hnonneg
  have hwindowP : window ≤ P := by
    rw [hP]
    nlinarith
  have hm0 : (0 : ℝ) ≤ (m : ℕ) := by positivity
  have hrhs :
      (P - window) * (m : ℝ) * (Z - E - 1 - (K q r : ℝ) * C) ≤
        (P - window) * (m : ℝ) *
          ((lowerNat g n q r i : ℝ) - (K q r : ℝ) * C) := by
    gcongr
  have hcoef : ((4 * K q r - 1 : ℕ) : ℝ) =
      4 * (K q r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * K q r)]
    norm_num
  have hmcast : ((m : ℕ) : ℝ) = (K q r : ℝ) - 1 := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 1 ≤ K q r)]
    norm_num
  have halgebra :
      (m : ℝ) * P * Z - ((4 * K q r - 1 : ℕ) : ℝ) * E * P ≤
        (P - window) * (m : ℝ) *
          (Z - E - 1 - (K q r : ℝ) * C) := by
    rw [hcoef, hmcast]
    have hKReal : (3 : ℝ) ≤ K q r := by exact_mod_cast hK
    have hc : 0 ≤ 1 + (K q r : ℝ) * C := by positivity
    have hmReal : (0 : ℝ) ≤ (K q r : ℝ) - 1 := by linarith
    have hcE : 1 + (K q r : ℝ) * C ≤ E / 4 := by linarith
    have hmc : ((K q r : ℝ) - 1) * (1 + (K q r : ℝ) * C) ≤
        ((K q r : ℝ) - 1) * (E / 4) :=
      mul_le_mul_of_nonneg_left hcE hmReal
    have hmw : ((K q r : ℝ) - 1) * window ≤
        ((K q r : ℝ) - 1) * (E / 4) :=
      mul_le_mul_of_nonneg_left hwindowE hmReal
    have hcost : 0 ≤ (3 * (K q r : ℝ)) * E -
        ((K q r : ℝ) - 1) * (1 + (K q r : ℝ) * C) -
        ((K q r : ℝ) - 1) * window := by
      have hsum :
          ((K q r : ℝ) - 1) * (1 + (K q r : ℝ) * C) +
              ((K q r : ℝ) - 1) * window ≤
            ((K q r : ℝ) - 1) * (E / 2) := by
        linarith only [hmc, hmw]
      have hfactorNonneg : 0 ≤
          (3 * (K q r : ℝ)) - ((K q r : ℝ) - 1) / 2 := by
        linarith only [hKReal]
      have hbase := mul_nonneg hfactorNonneg hE
      nlinarith only [hsum, hbase]
    have hinner : Z - E - 1 - (K q r : ℝ) * C ≤ P := by
      rw [hP]
      nlinarith only [hE, hc]
    have hwm : 0 ≤ window * ((K q r : ℝ) - 1) :=
      mul_nonneg hwindow0 hmReal
    have hinnerMul := mul_le_mul_of_nonneg_left hinner hwm
    have hcostMul := mul_nonneg hP0 hcost
    have hgap : 0 ≤
        (P - window) * ((K q r : ℝ) - 1) *
            (Z - E - 1 - (K q r : ℝ) * C) -
          (((K q r : ℝ) - 1) * P * Z -
            (4 * (K q r : ℝ) - 1) * E * P) := by
      calc
        0 ≤ P * ((3 * (K q r : ℝ)) * E -
            ((K q r : ℝ) - 1) * (1 + (K q r : ℝ) * C) -
            ((K q r : ℝ) - 1) * window) := hcostMul
        _ = P * ((3 * (K q r : ℝ)) * E -
              ((K q r : ℝ) - 1) * (1 + (K q r : ℝ) * C)) -
            window * ((K q r : ℝ) - 1) * P := by ring
        _ ≤ P * ((3 * (K q r : ℝ)) * E -
              ((K q r : ℝ) - 1) * (1 + (K q r : ℝ) * C)) -
            window * ((K q r : ℝ) - 1) *
              (Z - E - 1 - (K q r : ℝ) * C) := by
          exact sub_le_sub_left hinnerMul _
        _ = _ := by ring
    linarith only [hgap]
  change Q * (upperProfile g n q r i - upperProfile g n q r (i + 1)) ≤ _
  exact hlhs.trans (halgebra.trans hrhs)

/-- The reciprocal error remains a small fraction of the centre throughout
the stopped interval, so both degree profiles are nonnegative. -/
lemma degreeProfiles_nonneg
    {g n q r i : ℕ} (hK : 1 < K q r) (hT : 4 ≤ scale n q r)
    (hx : 0 < density g (K q r) i)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i) :
    0 ≤ lowerProfile g n q r i ∧ 0 ≤ upperProfile g n q r i := by
  let E := degreeError (profileA n q r) (centerDegree n q r)
    g (K q r) i
  let Z := degreeCenter (centerDegree n q r) g (K q r) i
  have hTpos : 0 < scale n q r := by omega
  have hEZ := degreeError_le_center_div_scale hK hTpos hx hlower
  have hZ : 0 ≤ Z := by
    dsimp [Z, degreeCenter, centerDegree]
    positivity
  have hTR : (4 : ℝ) ≤ scale n q r := by exact_mod_cast hT
  have hE : 0 ≤ E := by
    dsimp [E]
    unfold degreeError profileA centerDegree
    positivity
  have hEZ' : E ≤ Z := by
    change E ≤ Z / scale n q r at hEZ
    have hdiv : Z / (scale n q r : ℝ) ≤ Z := by
      apply (div_le_self hZ)
      linarith
    exact hEZ.trans hdiv
  constructor
  · dsimp [lowerProfile, degreeLower, Z, E]
    linarith
  · dsimp [upperProfile, degreeUpper, Z, E]
    linarith

/-- A power lower bound on the ambient extension scale supplies the centre
lower bound used to absorb floor and ceiling errors. -/
lemma scale_le_degreeCenter
    {g n q r i : ℕ} (hK : 0 < K q r) (hT : 0 < scale n q r)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i)
    (hpower : (scale n q r : ℝ) ^ K q r ≤ centerDegree n q r) :
    (scale n q r : ℝ) ≤
      degreeCenter (centerDegree n q r) g (K q r) i := by
  let T : ℝ := scale n q r
  let x := density g (K q r) i
  let D := centerDegree n q r
  have hTR : 0 < T := by dsimp [T]; exact_mod_cast hT
  have hx : 0 ≤ x := (by simpa [x] using hlower.trans' (by positivity))
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / T)
    (by simpa [T, x] using hlower) (K q r - 1)
  have hpowT : (1 / T) ^ (K q r - 1) =
      T / T ^ K q r := by
    have hs : K q r = (K q r - 1) + 1 := by omega
    rw [one_div_pow, hs, pow_succ]
    field_simp
    congr 1 <;> omega
  have hD : 0 ≤ D := by dsimp [D, centerDegree]; positivity
  have hmul : T ^ K q r * (1 / T) ^ (K q r - 1) ≤
      D * x ^ (K q r - 1) :=
    mul_le_mul hpower hpow (by positivity) hD
  rw [hpowT] at hmul
  dsimp [T, x, D] at hmul ⊢
  unfold degreeCenter
  have hTK : 0 < (scale n q r : ℝ) ^ K q r := by positivity
  calc
    (scale n q r : ℝ) =
        (scale n q r : ℝ) ^ K q r *
          ((scale n q r : ℝ) / (scale n q r : ℝ) ^ K q r) := by
      field_simp
    _ ≤ centerDegree n q r *
          density g (K q r) i ^ (K q r - 1) := hmul

/-- A quantitative centre lower bound converts the floor/ceiling profiles
to the relative discrepancy required by the weighted lower-face drift. -/
lemma lowerNat_upperNat_ratio
    {g n q r i : ℕ} (hK : 1 < K q r) (hT : 4 ≤ scale n q r)
    (hx : 0 < density g (K q r) i)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i)
    (hcenter : (scale n q r : ℝ) ≤
      degreeCenter (centerDegree n q r) g (K q r) i) :
    0 < upperNat g n q r i ∧
      lowerNat g n q r i ≤ upperNat g n q r i ∧
      1 - (lowerNat g n q r i : ℝ) / upperNat g n q r i ≤
        faceEps n q r := by
  let T : ℝ := scale n q r
  let E := degreeError (profileA n q r) (centerDegree n q r)
    g (K q r) i
  let Z := degreeCenter (centerDegree n q r) g (K q r) i
  let U := upperNat g n q r i
  let L := lowerNat g n q r i
  have hTpos : 0 < scale n q r := by omega
  have hTR : (4 : ℝ) ≤ T := by
    change (4 : ℝ) ≤ (scale n q r : ℝ)
    exact_mod_cast hT
  have hEZ := degreeError_le_center_div_scale hK hTpos hx hlower
  change E ≤ Z / T at hEZ
  have hZpos : 0 < Z := lt_of_lt_of_le (by exact_mod_cast hTpos) hcenter
  have hprofiles := degreeProfiles_nonneg hK hT hx hlower
  have hPZ : Z ≤ upperProfile g n q r i := by
    dsimp [upperProfile, degreeUpper, Z, E]
    have hE : 0 ≤ E := by
      dsimp [E]
      unfold degreeError profileA centerDegree
      positivity
    linarith
  have hPU : upperProfile g n q r i ≤ U := by
    dsimp [U, upperNat]
    exact Nat.le_ceil _
  have hUposReal : (0 : ℝ) < U := hZpos.trans_le (hPZ.trans hPU)
  have hUpos : 0 < U := by exact_mod_cast hUposReal
  have hLP : (L : ℝ) ≤ lowerProfile g n q r i := by
    dsimp [L, lowerNat]
    exact Nat.floor_le hprofiles.1
  have hLUReal : (L : ℝ) ≤ U := by
    exact hLP.trans (by
      dsimp [lowerProfile, upperProfile, degreeLower, degreeUpper]
      have hE : 0 ≤ E := by
        dsimp [E]
        unfold degreeError profileA centerDegree
        positivity
      calc
        _ ≤ degreeCenter (centerDegree n q r) g (K q r) i +
            degreeError (profileA n q r) (centerDegree n q r)
              g (K q r) i := by linarith
        _ ≤ U := hPU)
  have hLU : L ≤ U := by exact_mod_cast hLUReal
  have hUupper : (U : ℝ) < Z + E + 1 := by
    have := Erdos722.NibbleScalar.ceil_profile_lt_add_one hprofiles.2
    simpa [U, upperNat, upperProfile, degreeUpper, Z, E] using this
  have hLlower : Z - E - 1 < (L : ℝ) := by
    have := Erdos722.NibbleScalar.floor_profile_sub_one_lt hprofiles.1
    simpa [L, lowerNat, lowerProfile, degreeLower, Z, E] using this
  have hdiff : (U : ℝ) - L ≤ 2 * E + 2 := by linarith
  have hEbound : E ≤ Z / T := hEZ
  have hOne : (1 : ℝ) ≤ Z / T := by
    exact (le_div_iff₀ (by linarith : 0 < T)).2 (by simpa using hcenter)
  have hdiffBound : (U : ℝ) - L ≤ 4 * Z / T := by
    have haux : 2 * E + 2 ≤ 4 * (Z / T) := by
      linarith only [hEbound, hOne]
    calc
      (U : ℝ) - L ≤ 2 * E + 2 := hdiff
      _ ≤ 4 * (Z / T) := haux
      _ = 4 * Z / T := by ring
  have hratio : 1 - (L : ℝ) / U = ((U : ℝ) - L) / U := by
    field_simp
  rw [hratio]
  have hquot : ((U : ℝ) - L) / U ≤ (4 * Z / T) / Z := by
    calc
      ((U : ℝ) - L) / U ≤ (4 * Z / T) / U :=
        div_le_div_of_nonneg_right hdiffBound hUposReal.le
      _ ≤ (4 * Z / T) / Z := by
        apply div_le_div_of_nonneg_left (by positivity) hZpos
        exact hPZ.trans hPU
  refine ⟨hUpos, hLU, ?_⟩
  calc
    ((U : ℝ) - L) / U ≤ (4 * Z / T) / Z := hquot
    _ = 4 / T := by field_simp
    _ ≤ 8 / T := by
      exact div_le_div_of_nonneg_right (by norm_num) (by linarith)
    _ = faceEps n q r := by rfl

/-- If the residual host is large compared with the fixed reciprocal
exponent, the reciprocal edge error grows by at most one sixth in one
clique-removal step. -/
lemma degreeError_succ_sub_le_one_sixth
    {g n q r i : ℕ} (hg : 0 < g) (hK : 2 < K q r)
    (hstep : K q r * (i + 1) < g)
    (hremaining :
      (6 : ℝ) * (4 * (K q r : ℝ) - 1) * K q r *
          (2 : ℝ) ^ (4 * K q r - 2) ≤
        remaining g (K q r) (i + 1)) :
    degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) (i + 1) -
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i ≤
      degreeError (profileA n q r) (centerDegree n q r)
        g (K q r) i / 6 := by
  let x := density g (K q r) i
  let y := density g (K q r) (i + 1)
  let h : ℝ := (K q r : ℝ) / g
  let s := 4 * K q r - 1
  let A := profileA n q r * centerDegree n q r
  have hii : K q r * i ≤ K q r * (i + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hx : 0 < x := by dsimp [x]; exact density_pos hg (hii.trans_lt hstep)
  have hy : 0 < y := by dsimp [y]; exact density_pos hg hstep
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hsxy : y = x - h := by
    simpa [x, y, h] using density_succ g (K q r) i
  have hhx : h < x := by linarith
  have hA : 0 ≤ A := by
    dsimp [A]
    unfold profileA centerDegree
    positivity
  have hrem : remaining g (K q r) (i + 1) = (g : ℝ) * y := by
    dsimp [y, density]
    field_simp
  have hcoefPos : (0 : ℝ) < 4 * K q r - 1 := by
    have hKR : (3 : ℝ) ≤ K q r := by exact_mod_cast hK
    linarith
  have hpowOne : (1 : ℝ) ≤ 2 ^ (4 * K q r - 2) := by
    exact one_le_pow₀ (by norm_num)
  have hKrem : (K q r : ℝ) ≤ remaining g (K q r) (i + 1) := by
    have hcoefOne : (1 : ℝ) ≤ 4 * K q r - 1 := by
      have hKR : (3 : ℝ) ≤ K q r := by exact_mod_cast hK
      linarith
    have hprodOne : (1 : ℝ) ≤
        (4 * (K q r : ℝ) - 1) * 2 ^ (4 * K q r - 2) := by
      nlinarith [mul_le_mul hcoefOne hpowOne (by norm_num)
        (by linarith : (0 : ℝ) ≤ 4 * K q r - 1)]
    have hfactor : (1 : ℝ) ≤
        6 * (4 * (K q r : ℝ) - 1) * 2 ^ (4 * K q r - 2) := by
      nlinarith
    have hK0 : (0 : ℝ) ≤ K q r := by positivity
    calc
      (K q r : ℝ) ≤
          (6 * (4 * (K q r : ℝ) - 1) * 2 ^ (4 * K q r - 2)) * K q r :=
        by simpa using mul_le_mul_of_nonneg_right hfactor hK0
      _ ≤ remaining g (K q r) (i + 1) := by
        nlinarith [hremaining]
  have hhy : h ≤ y := by
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg
    apply (div_le_iff₀ hgR).2
    calc
      (K q r : ℝ) ≤ remaining g (K q r) (i + 1) := hKrem
      _ = y * g := by rw [hrem]; ring
  have hxyTwo : x ≤ 2 * y := by
    rw [hsxy]
    linarith
  have hpow : x ^ (s - 1) ≤ (2 * y) ^ (s - 1) := by
    exact pow_le_pow_left₀ hx.le hxyTwo _
  have hcoefficient :
      6 * (s : ℝ) * h * (2 : ℝ) ^ (s - 1) ≤ y := by
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg
    rw [show 6 * (s : ℝ) * h * (2 : ℝ) ^ (s - 1) =
        (6 * (s : ℝ) * (K q r : ℝ) * 2 ^ (s - 1)) / g by
      dsimp [h]
      field_simp]
    apply (div_le_iff₀ hgR).2
    rw [show y * (g : ℝ) = (g : ℝ) * y by ring, ← hrem]
    dsimp [s]
    have hscast : ((4 * K q r - 1 : ℕ) : ℝ) =
        4 * (K q r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 4 * K q r)]
      norm_num
    rw [hscast]
    have hexp : 4 * K q r - 1 - 1 = 4 * K q r - 2 := by omega
    rw [hexp]
    nlinarith [hremaining]
  have hfactor :
      6 * (s : ℝ) * h * x ^ (s - 1) ≤ y ^ s := by
    have hleft : 6 * (s : ℝ) * h * x ^ (s - 1) ≤
        6 * (s : ℝ) * h * (2 * y) ^ (s - 1) := by
      gcongr
    have hexp : s = (s - 1) + 1 := by dsimp [s]; omega
    calc
      6 * (s : ℝ) * h * x ^ (s - 1) ≤
          6 * (s : ℝ) * h * (2 * y) ^ (s - 1) := hleft
      _ = (6 * (s : ℝ) * h * (2 : ℝ) ^ (s - 1)) * y ^ (s - 1) := by
        rw [mul_pow]
        ring
      _ ≤ y * y ^ (s - 1) := by gcongr
      _ = y ^ s := by
        rw [← pow_succ']
        congr 1
        omega
  have herr := reciprocal_pow_growth_le_one_sixth s hA hx hh hhx
    (by simpa [hsxy] using hfactor)
  simpa [degreeError, A, x, y, h, s, hsxy] using herr

/-- The product of the lower total-clique profile and the one-step lower
edge-profile drop contains both the mean-field contribution and the full
reciprocal-error derivative.  The displayed form is tailored to the final
rounded lower-edge scalar inequality. -/
lemma lowerEdge_profile_product_lower
    {g n q r i : ℕ} (hg : 0 < g) (hK : 2 < K q r)
    (hstep : K q r * (i + 1) < g)
    (hcenterCost :
      (K q r : ℝ) *
          (degreeCenter (centerDegree n q r) g (K q r) i -
            degreeCenter (centerDegree n q r) g (K q r) (i + 1)) ≤
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i / 2)
    (hsmall :
      degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i ≤
        degreeCenter (centerDegree n q r) g (K q r) i) :
    ((K q r : ℝ) - 1) *
          (degreeCenter (centerDegree n q r) g (K q r) i -
            degreeError (profileA n q r) (centerDegree n q r)
              g (K q r) i) *
          (degreeCenter (centerDegree n q r) g (K q r) i -
            degreeError (profileA n q r) (centerDegree n q r)
              g (K q r) i / (2 * K q r)) +
        (4 * (K q r : ℝ) - 1) *
          degreeError (profileA n q r) (centerDegree n q r)
            g (K q r) i *
          (degreeCenter (centerDegree n q r) g (K q r) i -
            degreeError (profileA n q r) (centerDegree n q r)
              g (K q r) i) ≤
      cliqueLowerProfile g n q r i *
        (lowerProfile g n q r i - lowerProfile g n q r (i + 1)) := by
  let x := density g (K q r) i
  let y := density g (K q r) (i + 1)
  let E := degreeError (profileA n q r) (centerDegree n q r)
    g (K q r) i
  let Z := degreeCenter (centerDegree n q r) g (K q r) i
  let Y := degreeCenter (centerDegree n q r) g (K q r) (i + 1)
  let Q := cliqueLowerProfile g n q r i
  let m := K q r - 1
  have hii : K q r * i ≤ K q r * (i + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hx : 0 < x := by dsimp [x]; exact density_pos hg (hii.trans_lt hstep)
  have hy : 0 < y := by dsimp [y]; exact density_pos hg hstep
  have hxy : y ≤ x := by
    rw [show y = x - (K q r : ℝ) / g by
      simpa [x, y] using density_succ g (K q r) i]
    have : (0 : ℝ) ≤ (K q r : ℝ) / g := by positivity
    linarith
  have hE : 0 ≤ E := by
    dsimp [E]
    unfold degreeError profileA centerDegree
    positivity
  have hZ : 0 ≤ Z := by
    dsimp [Z, degreeCenter, centerDegree]
    positivity
  have hZE : 0 ≤ Z - E := by
    change E ≤ Z at hsmall
    linarith
  have hfactor : Q = remaining g (K q r) i / K q r * (Z - E) := by
    rw [show Q = remaining g (K q r) i / K q r *
        lowerProfile g n q r i by
      simpa [Q] using cliqueLowerProfile_eq_remaining_mul hg (by omega)
        (hii.trans_lt hstep)]
    rfl
  have hrem : remaining g (K q r) i = (g : ℝ) * x := by
    dsimp [x, density]
    field_simp
  have hQ0 : 0 ≤ Q := by
    rw [hfactor, hrem]
    positivity
  have hdiff := lowerProfile_sub_succ_ge
    (n := n) (q := q) (r := r) (i := i) hg hstep
  let centerTerm := centerDegree n q r *
    (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
      y ^ (K q r - 2))
  have hcenterEq : Q * centerTerm =
      (m : ℝ) * (Z - E) *
        (centerDegree n q r * x * y ^ (K q r - 2)) := by
    rw [hfactor, hrem]
    dsimp [centerTerm, m]
    have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
    field_simp [hg0, hK0]
  have hYle : Y ≤ centerDegree n q r * x * y ^ (K q r - 2) := by
    have hD : 0 ≤ centerDegree n q r := by
      unfold centerDegree
      positivity
    have hexp : K q r - 1 = (K q r - 2) + 1 := by omega
    dsimp [Y, degreeCenter]
    rw [hexp, pow_succ]
    have hpow : 0 ≤ y ^ (K q r - 2) := by positivity
    nlinarith [mul_nonneg hD (mul_nonneg hpow (sub_nonneg.mpr hxy))]
  have hYlower : Z - E / (2 * K q r) ≤ Y := by
    have hKR : (0 : ℝ) < K q r := by exact_mod_cast (by omega : 0 < K q r)
    change (K q r : ℝ) * (Z - Y) ≤ E / 2 at hcenterCost
    have hden : (0 : ℝ) < 2 * K q r := by positivity
    have hquot : Z - Y ≤ E / (2 * K q r) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    linarith
  have hcenterLower :
      (m : ℝ) * (Z - E) * (Z - E / (2 * K q r)) ≤
        Q * centerTerm := by
    rw [hcenterEq]
    have hm0 : (0 : ℝ) ≤ (m : ℕ) := by positivity
    gcongr
    exact hYlower.trans hYle
  have hgrowth := degreeErrorGrowth_eq
    (n := n) (q := q) (r := r) (i := i) hg (by omega) hstep
  have hratio : 1 ≤ x / y := (le_div_iff₀ hy).2 (by simpa using hxy)
  have hpcast : ((4 * K q r - 1 : ℕ) : ℝ) =
      4 * (K q r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * K q r)]
    norm_num
  have hgrowthLower :
      (4 * (K q r : ℝ) - 1) * E * (Z - E) ≤
        Q * degreeErrorGrowth g n q r i := by
    rw [hgrowth, hfactor, hrem, hpcast]
    have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
    have hp0 : 0 ≤ 4 * (K q r : ℝ) - 1 := by
      have hKR : (3 : ℝ) ≤ K q r := by exact_mod_cast hK
      linarith
    have hbase : 0 ≤ (4 * (K q r : ℝ) - 1) * E * (Z - E) := by
      positivity
    calc
      (4 * (K q r : ℝ) - 1) * E * (Z - E) ≤
          (4 * (K q r : ℝ) - 1) * E * (Z - E) * (x / y) := by
        simpa using mul_le_mul_of_nonneg_left hratio hbase
      _ = ((g : ℝ) * x / K q r * (Z - E)) *
          ((4 * (K q r : ℝ) - 1) * E *
            ((K q r : ℝ) / g) * (1 / y)) := by
        field_simp [hg0, hK0, hy.ne']
  have hterms :
      (m : ℝ) * (Z - E) * (Z - E / (2 * K q r)) +
          (4 * (K q r : ℝ) - 1) * E * (Z - E) ≤
        Q * (centerTerm + degreeErrorGrowth g n q r i) := by
    rw [mul_add]
    exact add_le_add hcenterLower hgrowthLower
  have hQdiff :
      (m : ℝ) * (Z - E) * (Z - E / (2 * K q r)) +
          (4 * (K q r : ℝ) - 1) * E * (Z - E) ≤
        Q * (lowerProfile g n q r i - lowerProfile g n q r (i + 1)) := by
    exact hterms.trans (mul_le_mul_of_nonneg_left (by simpa [centerTerm, y] using hdiff) hQ0)
  have hmcast : ((m : ℕ) : ℝ) = (K q r : ℝ) - 1 := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 1 ≤ K q r)]
    norm_num
  rw [hmcast] at hQdiff
  simpa [Z, E, Q] using hQdiff

/-- Quantitative small-error and one-step-cost margins imply the real
profile inequality needed for the rounded lower edge-degree drift. -/
lemma lowerEdge_profile_scalar_of_error_margins
    {g n q r i : ℕ} (hg : 0 < g) (hK : 2 < K q r)
    (hstep : K q r * (i + 1) < g)
    (hcenterCost :
      (K q r : ℝ) *
          (degreeCenter (centerDegree n q r) g (K q r) i -
            degreeCenter (centerDegree n q r) g (K q r) (i + 1)) ≤
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i / 2)
    (hsmall :
      16 * (K q r : ℝ) *
          degreeError (profileA n q r) (centerDegree n q r)
            g (K q r) i ≤
        degreeCenter (centerDegree n q r) g (K q r) i)
    (hround : (2 * K q r : ℕ) ≤
      degreeError (profileA n q r) (centerDegree n q r)
        g (K q r) i)
    (hdrop :
      (upperNat g n q r i : ℝ) *
          (lowerProfile g n q r i - lowerProfile g n q r (i + 1)) ≤
        degreeError (profileA n q r) (centerDegree n q r)
            g (K q r) i *
          degreeCenter (centerDegree n q r) g (K q r) i) :
    (upperNat g n q r i : ℝ) * (K q r - 1 : ℕ) *
          upperNat g n q r i +
        (cliqueLowerProfile g n q r i - upperNat g n q r i) *
          (lowerProfile g n q r (i + 1) - lowerProfile g n q r i) ≤ 0 := by
  let k : ℝ := K q r
  let E := degreeError (profileA n q r) (centerDegree n q r)
    g (K q r) i
  let Z := degreeCenter (centerDegree n q r) g (K q r) i
  let U : ℝ := upperNat g n q r i
  let d := lowerProfile g n q r i - lowerProfile g n q r (i + 1)
  let Q := cliqueLowerProfile g n q r i
  have hk : (3 : ℝ) ≤ k := by
    dsimp [k]
    exact_mod_cast hK
  have hk0 : 0 < k := by linarith
  have hii : K q r * i ≤ K q r * (i + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hxpos : 0 < density g (K q r) i :=
    density_pos hg (hii.trans_lt hstep)
  have hE : 0 ≤ E := by
    dsimp [E]
    unfold degreeError profileA centerDegree
    positivity
  have hZ : 0 ≤ Z := by
    dsimp [Z, degreeCenter, centerDegree]
    positivity
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hsmall' : 16 * k * E ≤ Z := by simpa [k, E, Z] using hsmall
  have herrorCenter : E ≤ Z := by
    calc
      E ≤ 16 * k * E := by nlinarith
      _ ≤ Z := hsmall'
  have hround' : 2 * k ≤ E := by
    change ((2 * K q r : ℕ) : ℝ) ≤ E at hround
    simpa [k] using hround
  have hupperNonneg : 0 ≤ upperProfile g n q r i := by
    dsimp [upperProfile, degreeUpper, Z, E]
    positivity
  have hU : U ≤ Z + E + 1 := by
    have hu := Erdos722.NibbleScalar.ceil_profile_lt_add_one hupperNonneg
    have hu' : U < Z + E + 1 := by
      simpa [U, upperNat, upperProfile, degreeUpper, Z, E] using hu
    exact hu'.le
  have hQd :
      (k - 1) * (Z - E) * (Z - E / (2 * k)) +
          (4 * k - 1) * E * (Z - E) ≤ Q * d := by
    simpa [k, E, Z, Q, d] using
      lowerEdge_profile_product_lower hg hK hstep hcenterCost herrorCenter
  have hdrop' : U * d ≤ E * Z := by simpa [U, d, E, Z] using hdrop
  have hEhalf : 1 ≤ E / 2 := by nlinarith
  have hU' : U ≤ Z + 3 * E / 2 := by linarith
  have hZE : 0 ≤ Z - E := by linarith
  have hm0 : 0 ≤ k - 1 := by linarith
  have hUsq : U * (k - 1) * U ≤
      (Z + 3 * E / 2) * (k - 1) * (Z + 3 * E / 2) := by
    nlinarith [mul_nonneg hm0 (sq_nonneg (Z + 3 * E / 2 - U))]
  have hsmall48 : 48 * E ≤ Z := by
    nlinarith
  have hsmallScaled : 16 * k ^ 2 * E ^ 2 ≤ k * E * Z := by
    have := mul_le_mul_of_nonneg_left hsmall' (mul_nonneg hk0.le hE)
    nlinarith
  have hbase : 0 ≤
      (k - 1) * (Z - E) * (Z - E / (2 * k)) +
          (4 * k - 1) * E * (Z - E) -
        ((Z + 3 * E / 2) * (k - 1) * (Z + 3 * E / 2) + E * Z) := by
    have hden : 2 * k ≠ 0 := by positivity
    apply (mul_nonneg_iff_of_pos_left (by positivity : 0 < 2 * k)).mp
    field_simp [hden]
    nlinarith [hsmallScaled, mul_nonneg hE (sub_nonneg.mpr hsmall48)]
  have hmain : U * (k - 1) * U ≤ (Q - U) * d := by
    nlinarith
  have hmcast : (((K q r - 1 : ℕ) : ℝ)) = k - 1 := by
    dsimp [k]
    rw [Nat.cast_sub (by omega : 1 ≤ K q r)]
    norm_num
  rw [show lowerProfile g n q r (i + 1) - lowerProfile g n q r i = -d by
    dsimp [d]; ring]
  push_cast [hmcast]
  dsimp [U, Q] at hmain ⊢
  nlinarith

/-- A residual-host lower bound supplies the final one-step cost in
`lowerEdge_profile_scalar_of_error_margins`. -/
lemma lowerEdge_profile_scalar_of_host_margin
    {g n q r i : ℕ} (hg : 0 < g) (hK : 2 < K q r)
    (hstep : K q r * (i + 1) < g)
    (hcenterCost :
      (K q r : ℝ) *
          (degreeCenter (centerDegree n q r) g (K q r) i -
            degreeCenter (centerDegree n q r) g (K q r) (i + 1)) ≤
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i / 2)
    (hsmall :
      16 * (K q r : ℝ) *
          degreeError (profileA n q r) (centerDegree n q r)
            g (K q r) i ≤
        degreeCenter (centerDegree n q r) g (K q r) i)
    (hround : (2 * K q r : ℕ) ≤
      degreeError (profileA n q r) (centerDegree n q r)
        g (K q r) i)
    (hremaining :
      (6 : ℝ) * (4 * (K q r : ℝ) - 1) * K q r *
          (2 : ℝ) ^ (4 * K q r - 2) ≤
        remaining g (K q r) (i + 1)) :
    (upperNat g n q r i : ℝ) * (K q r - 1 : ℕ) *
          upperNat g n q r i +
        (cliqueLowerProfile g n q r i - upperNat g n q r i) *
          (lowerProfile g n q r (i + 1) - lowerProfile g n q r i) ≤ 0 := by
  let E := degreeError (profileA n q r) (centerDegree n q r)
    g (K q r) i
  let Z := degreeCenter (centerDegree n q r) g (K q r) i
  let Y := degreeCenter (centerDegree n q r) g (K q r) (i + 1)
  let U : ℝ := upperNat g n q r i
  let d := lowerProfile g n q r i - lowerProfile g n q r (i + 1)
  have hE : 0 ≤ E := by
    dsimp [E]
    have hii : K q r * i ≤ K q r * (i + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hx := density_pos hg (hii.trans_lt hstep)
    unfold degreeError profileA centerDegree
    positivity
  have hZ : 0 ≤ Z := by
    dsimp [Z]
    have hii : K q r * i ≤ K q r * (i + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hx := density_pos hg (hii.trans_lt hstep)
    unfold degreeCenter centerDegree
    positivity
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hcenterDrop : Z - Y ≤ E / 6 := by
    have hKR : (3 : ℝ) ≤ K q r := by exact_mod_cast hK
    change (K q r : ℝ) * (Z - Y) ≤ E / 2 at hcenterCost
    by_cases hZY : 0 ≤ Z - Y
    · have hmul := mul_nonneg
        (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ K q r - 3)) hZY
      nlinarith
    · linarith
  have herrorDrop := degreeError_succ_sub_le_one_sixth
    (n := n) (q := q) (r := r) (i := i) hg hK hstep hremaining
  have hd : d ≤ E / 3 := by
    change lowerProfile g n q r i - lowerProfile g n q r (i + 1) ≤ E / 3
    dsimp [lowerProfile, degreeLower, Z, Y, E] at herrorDrop ⊢
    nlinarith
  have herrorCenter : E ≤ Z := by
    have hsmall' : 16 * (K q r : ℝ) * E ≤ Z := by
      simpa [E, Z] using hsmall
    have hKR : (3 : ℝ) ≤ K q r := by exact_mod_cast hK
    nlinarith
  have hround' : (1 : ℝ) ≤ E := by
    change ((2 * K q r : ℕ) : ℝ) ≤ E at hround
    have hKR : (3 : ℝ) ≤ K q r := by exact_mod_cast hK
    push_cast at hround
    linarith
  have hupperNonneg : 0 ≤ upperProfile g n q r i := by
    dsimp [upperProfile, degreeUpper, Z, E]
    positivity
  have hU : U ≤ 2 * Z := by
    have hu := Erdos722.NibbleScalar.ceil_profile_lt_add_one hupperNonneg
    have hu' : U < Z + E + 1 := by
      simpa [U, upperNat, upperProfile, degreeUpper, Z, E] using hu
    have hsmall' : 16 * (K q r : ℝ) * E ≤ Z := by
      simpa [E, Z] using hsmall
    have hKR : (3 : ℝ) ≤ K q r := by exact_mod_cast hK
    have htwo : 2 * E ≤ Z := by nlinarith
    nlinarith
  have hdrop : U * d ≤ E * Z := by
    calc
      U * d ≤ U * (E / 3) := mul_le_mul_of_nonneg_left hd hU0
      _ ≤ (2 * Z) * (E / 3) := by gcongr
      _ ≤ E * Z := by nlinarith [mul_nonneg hE hZ]
  exact lowerEdge_profile_scalar_of_error_margins hg hK hstep hcenterCost
    hsmall hround (by simpa [U, d, E, Z] using hdrop)

/-- The two quantitative costs in the lower total-clique drift are the
one-step movement of its mean-field centre and the integer ceiling.  Once
each costs at most half of the current reciprocal error, the remaining
error derivative supplies the rounded lower barrier. -/
lemma cliqueLower_scalar_of_error_margins
    {g n q r i : ℕ} (hg : 0 < g) (hK : 2 < K q r)
    (hstep : K q r * (i + 1) < g)
    (hcenterCost :
      (K q r : ℝ) *
          (degreeCenter (centerDegree n q r) g (K q r) i -
            degreeCenter (centerDegree n q r) g (K q r) (i + 1)) ≤
        degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) i / 2)
    (hroundCost : (2 * K q r : ℕ) ≤
      degreeError (profileA n q r) (centerDegree n q r)
        g (K q r) i) :
    (K q r : ℝ) * (upperProfile g n q r i + 1) ≤
      cliqueLowerProfile g n q r i -
        cliqueLowerProfile g n q r (i + 1) := by
  let E := degreeError (profileA n q r) (centerDegree n q r)
    g (K q r) i
  let X := degreeCenter (centerDegree n q r) g (K q r) i
  let Y := degreeCenter (centerDegree n q r) g (K q r) (i + 1)
  have hdiff := cliqueLowerProfile_sub_succ_ge
    (n := n) (q := q) (r := r) (i := i) hg (by omega) hstep
  have hcenter :
      ((g : ℝ) * centerDegree n q r / K q r) *
          ((K q r : ℝ) * ((K q r : ℝ) / g) *
            density g (K q r) (i + 1) ^ (K q r - 1)) =
        (K q r : ℝ) * Y := by
    dsimp [Y, degreeCenter]
    have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
    field_simp [hg0, hK0]
  have hgrowth : ((4 * K q r - 2 : ℕ) : ℝ) * E ≤
      cliqueErrorGrowth g n q r i := by
    simpa [E] using degreeError_mul_le_cliqueErrorGrowth hg (by omega) hstep
  have hcoef : ((4 * K q r - 2 : ℕ) : ℝ) =
      4 * (K q r : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 4 * K q r)]
    norm_num
  have hKReal : (3 : ℝ) ≤ K q r := by exact_mod_cast hK
  have hroundCost' : (K q r : ℝ) ≤ E / 2 := by
    change ((2 * K q r : ℕ) : ℝ) ≤ E at hroundCost
    push_cast at hroundCost
    linarith
  have hcost :
      (K q r : ℝ) * (X - Y) + (K q r : ℝ) ≤ E := by
    change (K q r : ℝ) * (X - Y) ≤ E / 2 at hcenterCost
    linarith
  have hmain :
      (K q r : ℝ) * Y + ((4 * K q r - 2 : ℕ) : ℝ) * E ≤
        cliqueLowerProfile g n q r i -
          cliqueLowerProfile g n q r (i + 1) := by
    rw [hcenter] at hdiff
    linarith
  dsimp [upperProfile, degreeUpper, X, E]
  rw [hcoef] at hmain
  nlinarith

end

end Erdos722.NibbleConcrete
