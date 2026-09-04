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

import ErdosProblems.Erdos1165.Annulus
import ErdosProblems.Erdos1165.PotentialGradient

/-!
# A finite-domain Harnack chain for planar simple random walk

This file proves the part of the annular Harnack argument which follows only
from positivity and the four-neighbour mean-value property.  It is useful to
separate this exact graph-theoretic step from the sharper planar estimate used
by Hao--Li--Okada--Zheng.

For a finite domain `D` and target boundary set `B`, `finiteExitMass D B n x`
is the exact depth-`n` four-ary-tree mass that the walk started at `x`, frozen
on first leaving `D`, is in `B` at time `n`.  Its increasing-horizon envelope
`exitMass D B x` is an `ENNReal` quantity.  A path of `L` nearest-neighbour
steps through `D` gives the uniform comparison

`exitMass D B y ≤ 4^L * exitMass D B x`.

The factor `4^L` is the exact universal Harnack-chain loss obtained from
positivity.  It is deliberately not advertised as HLOZ's sharp annular
estimate: their application needs a relative error tending to zero, whereas a
chain along a lattice boundary has length comparable to the radius.  Closing
that gap requires a uniform off-diagonal potential-kernel expansion (and its
Poisson-kernel consequence), not merely convergence for each fixed endpoint.
-/

open Filter
open scoped BigOperators ENNReal Topology

namespace Erdos1165
namespace AnnulusHarnack

open EndpointDiagonal Annulus PotentialKernel PotentialConvergence PotentialGradient

noncomputable section

/-! ## Positivity of the stopped four-ary-tree expectation -/

theorem stoppedExpectation_nonneg (D : Finset Point) {f : Point → ℝ}
    (hf : ∀ x, 0 ≤ f x) (n : ℕ) (x : Point) :
    0 ≤ stoppedExpectation D n f x := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
      rw [stoppedExpectation_succ]
      exact div_nonneg (Finset.sum_nonneg fun d _ ↦ ih _) (by norm_num)

theorem stoppedExpectation_le_one (D : Finset Point) {f : Point → ℝ}
    (hf : ∀ x, f x ≤ 1) (n : ℕ) (x : Point) :
    stoppedExpectation D n f x ≤ 1 := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
      rw [stoppedExpectation_succ]
      calc
        (∑ d : Direction, stoppedExpectation D n f (absorbedStep D x d)) / 4 ≤
            (∑ _d : Direction, (1 : ℝ)) / 4 := by
          gcongr with d
          exact ih _
        _ = 1 := by simp

/-! ## Interior nearest-neighbour paths -/

/-- A path from `x` to `y` whose departing vertex at every step lies in `D`.
The final vertex may lie on the outer boundary. -/
inductive InteriorPath (D : Finset Point) : ℕ → Point → Point → Prop
  | nil (x : Point) : InteriorPath D 0 x x
  | cons {L : ℕ} {x y z : Point} (hx : x ∈ D)
      (hxy : ∃ d : Direction, y = neighbor x d)
      (hyz : InteriorPath D L y z) : InteriorPath D (L + 1) x z

/-- Connectivity through at most `L` interior nearest-neighbour steps. -/
def ConnectedWithin (D : Finset Point) (L : ℕ) (x y : Point) : Prop :=
  ∃ ℓ ≤ L, InteriorPath D ℓ x y

theorem InteriorPath.trans {D : Finset Point} {L M : ℕ} {x y z : Point}
    (hxy : InteriorPath D L x y) (hyz : InteriorPath D M y z) :
    InteriorPath D (L + M) x z := by
  induction hxy with
  | nil => simpa using hyz
  | @cons L x w y hx hxw hwy ih =>
      convert InteriorPath.cons hx hxw (ih hyz) using 1 <;> omega

theorem InteriorPath.start_mem_of_end_mem
    {D : Finset Point} {L : ℕ} {x y : Point}
    (hxy : InteriorPath D L x y) (hy : y ∈ D) : x ∈ D := by
  cases hxy with
  | nil => exact hy
  | cons hx _ _ => exact hx

theorem neighbor_symmetric {x y : Point}
    (hxy : ∃ d : Direction, y = neighbor x d) :
    ∃ d : Direction, x = neighbor y d := by
  rcases hxy with ⟨d, rfl⟩
  fin_cases d
  · exact ⟨1, by ext <;> simp [neighbor, directionVector]⟩
  · exact ⟨0, by ext <;> simp [neighbor, directionVector]⟩
  · exact ⟨3, by ext <;> simp [neighbor, directionVector]⟩
  · exact ⟨2, by ext <;> simp [neighbor, directionVector]⟩

theorem InteriorPath.reverse
    {D : Finset Point} {L : ℕ} {x y : Point}
    (hxy : InteriorPath D L x y) (hy : y ∈ D) : InteriorPath D L y x := by
  induction hxy with
  | nil => exact InteriorPath.nil _
  | @cons L x z y hx hxz hzy ih =>
      have hz : z ∈ D := hzy.start_mem_of_end_mem hy
      have hyz : InteriorPath D L y z := ih hy
      have hzx : InteriorPath D 1 z x := by
        simpa using InteriorPath.cons hz (neighbor_symmetric hxz) (InteriorPath.nil x)
      simpa using hyz.trans hzx

/-! ## Concrete paths inside lattice discs -/

/-- Every nonzero lattice point has a nearest neighbour one unit closer in
taxicab distance and no farther from the origin in squared Euclidean radius. -/
lemma exists_neighbor_toward_zero {x : Point} (hx : x ≠ 0) :
    ∃ y : Point, (∃ d : Direction, y = neighbor x d) ∧
      manhattanNorm y + 1 = manhattanNorm x ∧
      radiusSqInt y ≤ radiusSqInt x := by
  rcases x with ⟨a, b⟩
  by_cases ha : 0 < a
  · refine ⟨(a - 1, b), ⟨1, ?_⟩, ?_, ?_⟩
    · ext <;> simp [neighbor, directionVector] <;> ring
    · apply Nat.cast_injective (R := ℤ)
      simp only [manhattanNorm, Nat.cast_add, Nat.cast_one]
      rw [Int.natAbs_of_nonneg (by omega : 0 ≤ a - 1),
        Int.natAbs_of_nonneg (by omega : 0 ≤ a)]
      ring
    · simp only [radiusSqInt]
      nlinarith
  · by_cases ha' : a < 0
    · refine ⟨(a + 1, b), ⟨0, ?_⟩, ?_, ?_⟩
      · ext <;> simp [neighbor, directionVector]
      · apply Nat.cast_injective (R := ℤ)
        simp only [manhattanNorm, Nat.cast_add, Nat.cast_one]
        rw [← Int.natAbs_neg (a + 1), ← Int.natAbs_neg a,
          Int.natAbs_of_nonneg (show 0 ≤ -(a + 1) by omega),
          Int.natAbs_of_nonneg (show 0 ≤ -a by omega)]
        ring
      · simp only [radiusSqInt]
        nlinarith
    · have ha0 : a = 0 := by omega
      subst a
      by_cases hb : 0 < b
      · refine ⟨(0, b - 1), ⟨3, ?_⟩, ?_, ?_⟩
        · ext <;> simp [neighbor, directionVector] <;> ring
        · apply Nat.cast_injective (R := ℤ)
          simp only [manhattanNorm, Nat.cast_add, Nat.cast_one]
          rw [Int.natAbs_of_nonneg (by omega : 0 ≤ b - 1),
            Int.natAbs_of_nonneg (by omega : 0 ≤ b)]
          ring
        · simp only [radiusSqInt]
          nlinarith
      · have hb' : b < 0 := by
          rcases lt_trichotomy b 0 with hb' | hb0 | hb'
          · exact hb'
          · exfalso
            apply hx
            simpa [hb0]
          · exact (hb hb').elim
        refine ⟨(0, b + 1), ⟨2, ?_⟩, ?_, ?_⟩
        · ext <;> simp [neighbor, directionVector]
        · apply Nat.cast_injective (R := ℤ)
          simp only [manhattanNorm, Nat.cast_add, Nat.cast_one]
          rw [← Int.natAbs_neg (b + 1), ← Int.natAbs_neg b,
            Int.natAbs_of_nonneg (show 0 ≤ -(b + 1) by omega),
            Int.natAbs_of_nonneg (show 0 ≤ -b by omega)]
          ring
        · simp only [radiusSqInt]
          nlinarith

/-- Radial descent gives a path from every point of a closed lattice disc to
the origin which stays in that disc and has exactly its taxicab length. -/
theorem interiorPath_to_zero (R : ℕ) {x : Point} (hxR : x ∈ closedDisc R) :
    InteriorPath (closedDisc R) (manhattanNorm x) x 0 := by
  generalize hn : manhattanNorm x = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hx0 : x = 0
      · subst x
        simp at hn
        subst n
        exact InteriorPath.nil (0 : Point)
      · obtain ⟨y, hxy, hnorm, hradius⟩ := exists_neighbor_toward_zero hx0
        have hyR : y ∈ closedDisc R := by
          rw [mem_closedDisc_iff_radiusSqInt_le] at hxR ⊢
          exact hradius.trans hxR
        have hyn : manhattanNorm y < n := by omega
        have hyPath := ih (manhattanNorm y) hyn hyR rfl
        convert InteriorPath.cons hxR hxy hyPath using 1 <;> omega

/-- A point in the radius-`R` disc has taxicab norm at most `2R`.  This coarse
constant is enough to make the universal Harnack loss completely explicit. -/
theorem manhattanNorm_le_two_mul_of_mem_closedDisc
    (R : ℕ) {x : Point} (hx : x ∈ closedDisc R) :
    manhattanNorm x ≤ 2 * R := by
  have hbox := (mem_closedDisc R x).mp hx |>.1
  rw [mem_coordinateBox] at hbox
  have hx1Z : (x.1.natAbs : ℤ) ≤ (R : ℤ) := by
    rw [Int.natCast_natAbs]
    exact abs_le.mpr ⟨hbox.1, hbox.2.1⟩
  have hx2Z : (x.2.natAbs : ℤ) ≤ (R : ℤ) := by
    rw [Int.natCast_natAbs]
    exact abs_le.mpr ⟨hbox.2.2.1, hbox.2.2.2⟩
  have hx1 : x.1.natAbs ≤ R := by exact_mod_cast hx1Z
  have hx2 : x.2.natAbs ≤ R := by exact_mod_cast hx2Z
  unfold manhattanNorm
  omega

/-- Any two points of the closed radius-`R` disc are connected inside the
disc in at most `4R` nearest-neighbour steps. -/
theorem closedDisc_connectedWithin (R : ℕ) {x y : Point}
    (hx : x ∈ closedDisc R) (hy : y ∈ closedDisc R) :
    ConnectedWithin (closedDisc R) (4 * R) x y := by
  have hzero : (0 : Point) ∈ closedDisc R := by
    rw [mem_closedDisc_iff_radiusSqInt_le]
    simp [radiusSqInt]
  have hx0 := interiorPath_to_zero R hx
  have hy0 := interiorPath_to_zero R hy
  have h0y := hy0.reverse hzero
  refine ⟨manhattanNorm x + manhattanNorm y, ?_, hx0.trans h0y⟩
  have hxnorm := manhattanNorm_le_two_mul_of_mem_closedDisc R hx
  have hynorm := manhattanNorm_le_two_mul_of_mem_closedDisc R hy
  omega

/-! ## The exact Harnack-chain inequality -/

/-- One nearest-neighbour step costs at most the reciprocal one-step mass,
namely a factor four.  Notice the one-unit shift in the time horizon. -/
theorem stoppedExpectation_neighbor_le_four
    (D : Finset Point) {f : Point → ℝ} (hf : ∀ z, 0 ≤ f z)
    {x y : Point} (hx : x ∈ D)
    (hxy : ∃ d : Direction, y = neighbor x d) (n : ℕ) :
    stoppedExpectation D n f y ≤
      4 * stoppedExpectation D (n + 1) f x := by
  rcases hxy with ⟨d, rfl⟩
  rw [stoppedExpectation_succ]
  simp_rw [absorbedStep_of_mem D hx]
  have hterm : stoppedExpectation D n f (neighbor x d) ≤
      ∑ e : Direction, stoppedExpectation D n f (neighbor x e) := by
    exact Finset.single_le_sum
      (fun e _ ↦ stoppedExpectation_nonneg D hf n (neighbor x e))
      (Finset.mem_univ d)
  linarith

/-- Iterating the one-step inequality along an interior path gives a finite
Harnack chain.  The statement is uniform in the terminal datum `f`. -/
theorem stoppedExpectation_path_le
    (D : Finset Point) {f : Point → ℝ} (hf : ∀ z, 0 ≤ f z)
    {L n : ℕ} {x y : Point} (hpath : InteriorPath D L x y) :
    stoppedExpectation D n f y ≤
      (4 : ℝ) ^ L * stoppedExpectation D (n + L) f x := by
  induction hpath generalizing n with
  | nil => simp
  | @cons L x z y hx hxz hzy ih =>
      have htail := ih (n := n)
      have hhead := stoppedExpectation_neighbor_le_four D hf hx hxz (n + L)
      calc
        stoppedExpectation D n f y ≤
            (4 : ℝ) ^ L * stoppedExpectation D (n + L) f z := htail
        _ ≤ (4 : ℝ) ^ L *
            (4 * stoppedExpectation D (n + L + 1) f x) := by
          gcongr
        _ = (4 : ℝ) ^ (L + 1) *
            stoppedExpectation D (n + (L + 1)) f x := by
          rw [pow_succ]
          ring_nf

/-! ## Exit masses and a uniform boundary comparison -/

/-- Indicator of a finite collection of possible exit vertices. -/
def boundaryIndicator (B : Finset Point) (x : Point) : ℝ :=
  if x ∈ B then 1 else 0

theorem boundaryIndicator_nonneg (B : Finset Point) (x : Point) :
    0 ≤ boundaryIndicator B x := by
  by_cases hx : x ∈ B <;> simp [boundaryIndicator, hx]

theorem boundaryIndicator_le_one (B : Finset Point) (x : Point) :
    boundaryIndicator B x ≤ 1 := by
  by_cases hx : x ∈ B <;> simp [boundaryIndicator, hx]

/-- Exact finite-horizon exit mass, expressed through the stopped tree from
`Annulus.lean`. -/
def finiteExitMass (D B : Finset Point) (n : ℕ) (x : Point) : ℝ :=
  stoppedExpectation D n (boundaryIndicator B) x

theorem finiteExitMass_nonneg (D B : Finset Point) (n : ℕ) (x : Point) :
    0 ≤ finiteExitMass D B n x :=
  stoppedExpectation_nonneg D (boundaryIndicator_nonneg B) n x

theorem finiteExitMass_le_one (D B : Finset Point) (n : ℕ) (x : Point) :
    finiteExitMass D B n x ≤ 1 :=
  stoppedExpectation_le_one D (boundaryIndicator_le_one B) n x

theorem boundaryIndicator_eq_zero_of_mem_of_disjoint
    {D B : Finset Point} (hDB : Disjoint D B) {x : Point} (hx : x ∈ D) :
    boundaryIndicator B x = 0 := by
  have hxB : x ∉ B := fun hxB ↦ Finset.disjoint_left.mp hDB hx hxB
  simp [boundaryIndicator, hxB]

/-- Once the target boundary is disjoint from the interior, increasing the
time horizon can only add exit mass. -/
theorem finiteExitMass_mono_succ {D B : Finset Point} (hDB : Disjoint D B)
    (n : ℕ) (x : Point) :
    finiteExitMass D B n x ≤ finiteExitMass D B (n + 1) x := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ D
      · rw [finiteExitMass, stoppedExpectation_zero,
          boundaryIndicator_eq_zero_of_mem_of_disjoint hDB hx]
        exact finiteExitMass_nonneg D B 1 x
      · simp [finiteExitMass, stoppedExpectation_of_notMem D hx]
  | succ n ih =>
      by_cases hx : x ∈ D
      · rw [finiteExitMass, finiteExitMass, stoppedExpectation_succ,
          stoppedExpectation_succ]
        simp_rw [absorbedStep_of_mem D hx]
        gcongr with d
        exact ih _
      · simp [finiteExitMass, stoppedExpectation_of_notMem D hx]

theorem monotone_finiteExitMass {D B : Finset Point} (hDB : Disjoint D B)
    (x : Point) : Monotone (fun n ↦ finiteExitMass D B n x) := by
  exact monotone_nat_of_le_succ (finiteExitMass_mono_succ hDB (x := x))

theorem outerBoundary_disjoint (D : Finset Point) :
    Disjoint D (outerBoundary D) := by
  rw [Finset.disjoint_left]
  intro x hxD hxout
  exact (mem_outerBoundary D x).mp hxout |>.1 hxD

theorem monotone_finiteExitMass_outerBoundary (D : Finset Point) (x : Point) :
    Monotone (fun n ↦ finiteExitMass D (outerBoundary D) n x) :=
  monotone_finiteExitMass (outerBoundary_disjoint D) x

/-- The increasing-horizon envelope of the finite exit masses.  If `B` lies
in `outerBoundary D`, absorption makes the finite masses monotone, so this is
the usual eventual exit-through-`B` mass. -/
def exitMass (D B : Finset Point) (x : Point) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (finiteExitMass D B n x)

theorem exitMass_le_one (D B : Finset Point) (x : Point) :
    exitMass D B x ≤ 1 := by
  apply iSup_le
  intro n
  rw [ENNReal.ofReal_le_one]
  exact finiteExitMass_le_one D B n x

/-- The finite Harnack-chain comparison after taking the increasing-horizon
envelope. -/
theorem exitMass_path_le (D B : Finset Point)
    {L : ℕ} {x y : Point} (hpath : InteriorPath D L x y) :
    exitMass D B y ≤ (4 : ℝ≥0∞) ^ L * exitMass D B x := by
  apply iSup_le
  intro n
  have hreal := stoppedExpectation_path_le D (boundaryIndicator_nonneg B)
    (n := n) hpath
  have hnonneg : 0 ≤ (4 : ℝ) ^ L := by positivity
  calc
    ENNReal.ofReal (finiteExitMass D B n y) ≤
        ENNReal.ofReal ((4 : ℝ) ^ L * finiteExitMass D B (n + L) x) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = (4 : ℝ≥0∞) ^ L *
        ENNReal.ofReal (finiteExitMass D B (n + L) x) := by
      rw [ENNReal.ofReal_mul hnonneg, ENNReal.ofReal_pow (by norm_num)]
      norm_num
    _ ≤ (4 : ℝ≥0∞) ^ L * exitMass D B x := by
      gcongr
      exact le_iSup (fun k : ℕ ↦ ENNReal.ofReal (finiteExitMass D B k x)) (n + L)

theorem exitMass_connectedWithin_le (D B : Finset Point)
    {L : ℕ} {x y : Point} (hxy : ConnectedWithin D L x y) :
    exitMass D B y ≤ (4 : ℝ≥0∞) ^ L * exitMass D B x := by
  rcases hxy with ⟨ℓ, hℓL, hpath⟩
  refine (exitMass_path_le D B hpath).trans ?_
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 4) hℓL)
    bot_le

/-- **Uniform finite-boundary Harnack comparison.**  If every ordered pair of
entrance points can be joined inside `D` in at most `L` steps, then every exit
distribution is uniformly comparable at those entrance points.  The target
set `B` is arbitrary, so the estimate holds simultaneously for every boundary
event. -/
theorem uniform_exitMass_compare
    (D E : Finset Point) (L : ℕ)
    (hconnected : ∀ x ∈ E, ∀ y ∈ E, ConnectedWithin D L x y)
    (B : Finset Point) {x y : Point} (hx : x ∈ E) (hy : y ∈ E) :
    exitMass D B y ≤ (4 : ℝ≥0∞) ^ L * exitMass D B x :=
  exitMass_connectedWithin_le D B (hconnected x hx y hy)

/-- Symmetric form of the uniform comparison. -/
theorem uniform_exitMass_compare_two_sided
    (D E : Finset Point) (L : ℕ)
    (hconnected : ∀ x ∈ E, ∀ y ∈ E, ConnectedWithin D L x y)
    (B : Finset Point) {x y : Point} (hx : x ∈ E) (hy : y ∈ E) :
    exitMass D B y ≤ (4 : ℝ≥0∞) ^ L * exitMass D B x ∧
      exitMass D B x ≤ (4 : ℝ≥0∞) ^ L * exitMass D B y :=
  ⟨uniform_exitMass_compare D E L hconnected B hx hy,
    uniform_exitMass_compare D E L hconnected B hy hx⟩

/-- Concrete radius-uniform comparison for the planar disc.  This is the
strongest bound obtainable from the bare four-neighbour Harnack chain: it is
uniform in the exit event `B` and in both starting points, but its factor is
exponential in the radius. -/
theorem closedDisc_exitMass_compare
    (R : ℕ) (B : Finset Point) {x y : Point}
    (hx : x ∈ closedDisc R) (hy : y ∈ closedDisc R) :
    exitMass (closedDisc R) B y ≤
      (4 : ℝ≥0∞) ^ (4 * R) * exitMass (closedDisc R) B x :=
  exitMass_connectedWithin_le (closedDisc R) B
    (closedDisc_connectedWithin R hx hy)

/-! ## Exact harmonicity of the planar potential kernel -/

/-- At odd-parity points, summation of the paired one-step identity gives
the mean-value property in the subtraction convention used by the endpoint
recurrence. -/
theorem potential_subNeighbor_harmonic_of_not_even {x : Point}
    (hx : ¬Even (x.1 + x.2)) :
    planarPotentialKernel x = (1 / 4 : ℝ) * ∑ d : Direction,
      planarPotentialKernel (x - directionVector d) := by
  unfold planarPotentialKernel
  calc
    ∑' n : ℕ, potentialPair x n =
        ∑' n : ℕ, (1 / 4 : ℝ) * ∑ d : Direction,
          potentialPair (x - directionVector d) n := by
      apply tsum_congr
      intro n
      exact potentialPair_eq_neighbor_average_of_not_even hx n
    _ = (1 / 4 : ℝ) * ∑' n : ℕ, ∑ d : Direction,
          potentialPair (x - directionVector d) n := by rw [tsum_mul_left]
    _ = (1 / 4 : ℝ) * ∑ d : Direction, ∑' n : ℕ,
          potentialPair (x - directionVector d) n := by
      rw [Summable.tsum_finsetSum (f := fun d n ↦
        potentialPair (x - directionVector d) n)
        (fun d _ ↦ summable_potentialPair _)]

lemma neighbor_not_even_of_even {x : Point} (hx : Even (x.1 + x.2))
    (d : Direction) :
    ¬Even ((x - directionVector d).1 + (x - directionVector d).2) := by
  rcases x with ⟨a, b⟩
  rcases hx with ⟨k, hk⟩
  rintro ⟨l, hl⟩
  fin_cases d <;> norm_num [directionVector] at hl <;> omega

/-- Every fixed even-time endpoint mass tends to zero.  The proof is uniform
enough for the telescoping harmonicity argument: the displaced mass is
bounded above by the return mass, which is at most `1/(n+1)`. -/
theorem tendsto_endpointProbability_even_zero (x : Point) :
    Tendsto (fun n : ℕ ↦ endpointProbability (2 * n) x) atTop (nhds 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n ↦ endpointProbability_nonneg (2 * n) x)
    (Filter.Eventually.of_forall fun n ↦ ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases hx : Even (x.1 + x.2)
  · rw [endpointProbability_even_eq_diagonalProductMass_of_even hx]
    have hmass := diagonalProductLoss_nonneg
      (firstDiagonalOffset x) (secondDiagonalOffset x) n
    unfold diagonalProductLoss at hmass
    rw [diagonalProductMass_center] at hmass
    exact (sub_nonneg.mp hmass).trans (planarReturnProbability_upper_bound n)
  · rw [endpointProbability_even_eq_zero_of_not_even hx]
    positivity

/-- For an even-parity point, the defect between its paired potential term
and the neighbor average is an exact telescoping endpoint difference. -/
lemma potentialPair_sub_average_eq_endpoint_diff_of_even {x : Point}
    (hx : Even (x.1 + x.2)) (n : ℕ) :
    potentialPair x n - (1 / 4 : ℝ) * ∑ d : Direction,
        potentialPair (x - directionVector d) n =
      endpointProbability (2 * n + 2) x - endpointProbability (2 * n) x := by
  have hnbr (d : Direction) := neighbor_not_even_of_even hx d
  unfold potentialPair potentialTerm
  rw [endpointProbability_even_zero, endpointProbability_odd_zero,
    endpointProbability_odd_eq_zero_of_even hx]
  simp_rw [endpointProbability_even_eq_zero_of_not_even (hnbr _)]
  rw [endpointProbability_succ (2 * n + 1) x]
  simp only [sub_zero, zero_sub, add_zero]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hcard : ∑ _d : Direction, planarReturnProbability n =
      4 * planarReturnProbability n := by simp
  rw [hcard]
  ring

lemma endpointProbability_zero_of_ne_zero {x : Point} (hx : x ≠ 0) :
    endpointProbability 0 x = 0 := by
  unfold endpointProbability
  apply div_eq_zero_iff.mpr
  left
  norm_cast
  apply Finset.card_eq_zero.mpr
  ext u
  constructor
  · intro hu
    rw [mem_endpointBlocks] at hu
    exfalso
    apply hx
    calc
      x = blockDisplacement u := hu.symm
      _ = 0 := by
        unfold blockDisplacement
        simp
  · intro hu
    cases hu

lemma sum_endpointProbability_even_diff {x : Point} (n : ℕ) :
    ∑ i ∈ Finset.range n,
        (endpointProbability (2 * i + 2) x - endpointProbability (2 * i) x) =
      endpointProbability (2 * n) x - endpointProbability 0 x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring_nf

theorem hasSum_endpointProbability_even_diff_of_ne_zero {x : Point}
    (hx : x ≠ 0) :
    HasSum (fun n : ℕ ↦
      endpointProbability (2 * n + 2) x - endpointProbability (2 * n) x) 0 := by
  have havg : Summable (fun n : ℕ ↦ (1 / 4 : ℝ) * ∑ d : Direction,
      potentialPair (x - directionVector d) n) := by
    apply Summable.mul_left
    apply summable_sum
    intro d hd
    exact summable_potentialPair _
  have hdiff : Summable (fun n : ℕ ↦
      potentialPair x n - (1 / 4 : ℝ) * ∑ d : Direction,
        potentialPair (x - directionVector d) n) :=
    (summable_potentialPair x).sub havg
  by_cases hxeven : Even (x.1 + x.2)
  · have hseries : Summable (fun n : ℕ ↦
        endpointProbability (2 * n + 2) x - endpointProbability (2 * n) x) :=
      hdiff.congr fun n ↦ potentialPair_sub_average_eq_endpoint_diff_of_even hxeven n
    apply (hasSum_iff_tendsto_nat_of_summable_norm hseries.norm).2
    simp_rw [sum_endpointProbability_even_diff]
    rw [endpointProbability_zero_of_ne_zero hx]
    simpa only [sub_zero] using tendsto_endpointProbability_even_zero x
  · have hz (n : ℕ) : endpointProbability (2 * n) x = 0 :=
      endpointProbability_even_eq_zero_of_not_even hxeven
    convert (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0) using 1
    funext n
    rw [show 2 * n + 2 = 2 * (n + 1) by omega, hz (n + 1), hz n]
    ring

/-- At a nonzero even-parity point, the endpoint defect telescopes to zero,
giving the missing half of potential-kernel harmonicity. -/
theorem potential_subNeighbor_harmonic_of_even_ne_zero {x : Point}
    (hx : Even (x.1 + x.2)) (hx0 : x ≠ 0) :
    planarPotentialKernel x = (1 / 4 : ℝ) * ∑ d : Direction,
      planarPotentialKernel (x - directionVector d) := by
  have havg : Summable (fun n : ℕ ↦ (1 / 4 : ℝ) * ∑ d : Direction,
      potentialPair (x - directionVector d) n) := by
    apply Summable.mul_left
    apply summable_sum
    intro d hd
    exact summable_potentialPair _
  have hdiff := hasSum_endpointProbability_even_diff_of_ne_zero hx0
  have hzero : ∑' n : ℕ,
      (potentialPair x n - (1 / 4 : ℝ) * ∑ d : Direction,
        potentialPair (x - directionVector d) n) = 0 := by
    rw [← hdiff.tsum_eq]
    apply tsum_congr
    intro n
    exact potentialPair_sub_average_eq_endpoint_diff_of_even hx n
  unfold planarPotentialKernel
  have havg_tsum : (∑' n : ℕ, (1 / 4 : ℝ) * ∑ d : Direction,
        potentialPair (x - directionVector d) n) =
      (1 / 4 : ℝ) * ∑ d : Direction, ∑' n : ℕ,
        potentialPair (x - directionVector d) n := by
    rw [tsum_mul_left]
    rw [Summable.tsum_finsetSum (f := fun d n ↦
      potentialPair (x - directionVector d) n)
      (fun d _ ↦ summable_potentialPair _)]
  have hsub := (summable_potentialPair x).tsum_sub havg
  rw [hzero] at hsub
  rw [havg_tsum] at hsub
  linarith

lemma sum_sub_direction_eq_sum_neighbor (f : Point → ℝ) (x : Point) :
    ∑ d : Direction, f (x - directionVector d) =
      ∑ d : Direction, f (neighbor x d) := by
  rcases x with ⟨a, b⟩
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  simp [neighbor, directionVector]
  ring_nf

/-- **Exact potential-kernel harmonicity.**  The paired planar potential
kernel satisfies the discrete mean-value property at every point other than
its pole. -/
theorem planarPotentialKernel_harmonicAt_of_ne_zero {x : Point} (hx : x ≠ 0) :
    neighborAverage planarPotentialKernel x = planarPotentialKernel x := by
  by_cases hparity : Even (x.1 + x.2)
  · have h := potential_subNeighbor_harmonic_of_even_ne_zero hparity hx
    rw [sum_sub_direction_eq_sum_neighbor] at h
    unfold neighborAverage
    linarith
  · have h := potential_subNeighbor_harmonic_of_not_even hparity
    rw [sum_sub_direction_eq_sum_neighbor] at h
    unfold neighborAverage
    linarith

/-- The potential kernel is harmonic on every finite domain avoiding its
pole, in exactly the form consumed by `finite_optionalStopping`. -/
theorem planarPotentialKernel_harmonicOn {D : Finset Point}
    (hD : (0 : Point) ∉ D) : HarmonicOn D planarPotentialKernel := by
  intro x hx
  exact planarPotentialKernel_harmonicAt_of_ne_zero (fun h ↦ hD (h ▸ hx))

@[simp] theorem endpointProbability_zero_zero : endpointProbability 0 0 = 1 := by
  simpa [planarReturnProbability, Nat.centralBinom] using endpointProbability_even_zero 0

@[simp] theorem planarPotentialKernel_zero : planarPotentialKernel 0 = 0 := by
  unfold planarPotentialKernel potentialPair potentialTerm
  simp

theorem hasSum_endpointProbability_even_diff_zero :
    HasSum (fun n : ℕ ↦ endpointProbability (2 * n + 2) 0 -
      endpointProbability (2 * n) 0) (-1) := by
  have hzeroEven : Even (((0 : Point).1) + (0 : Point).2) := by simp
  have havg : Summable (fun n : ℕ ↦ (1 / 4 : ℝ) * ∑ d : Direction,
      potentialPair ((0 : Point) - directionVector d) n) := by
    apply Summable.mul_left
    apply summable_sum
    intro d hd
    exact summable_potentialPair _
  have hdiff : Summable (fun n : ℕ ↦
      potentialPair 0 n - (1 / 4 : ℝ) * ∑ d : Direction,
        potentialPair ((0 : Point) - directionVector d) n) :=
    (summable_potentialPair 0).sub havg
  have hseries : Summable (fun n : ℕ ↦
      endpointProbability (2 * n + 2) 0 - endpointProbability (2 * n) 0) :=
    hdiff.congr fun n ↦ potentialPair_sub_average_eq_endpoint_diff_of_even hzeroEven n
  apply (hasSum_iff_tendsto_nat_of_summable_norm hseries.norm).2
  simp_rw [sum_endpointProbability_even_diff]
  rw [endpointProbability_zero_zero]
  simpa using (tendsto_endpointProbability_even_zero 0).sub tendsto_const_nhds

/-- The potential kernel has unit discrete drift at its pole. -/
theorem neighborAverage_planarPotentialKernel_zero :
    neighborAverage planarPotentialKernel 0 = 1 := by
  have havg : Summable (fun n : ℕ ↦ (1 / 4 : ℝ) * ∑ d : Direction,
      potentialPair ((0 : Point) - directionVector d) n) := by
    apply Summable.mul_left
    apply summable_sum
    intro d hd
    exact summable_potentialPair _
  have hdef : ∑' n : ℕ,
      (potentialPair 0 n - (1 / 4 : ℝ) * ∑ d : Direction,
        potentialPair ((0 : Point) - directionVector d) n) = -1 := by
    rw [← hasSum_endpointProbability_even_diff_zero.tsum_eq]
    apply tsum_congr
    intro n
    exact potentialPair_sub_average_eq_endpoint_diff_of_even (by simp) n
  have havg_tsum : (∑' n : ℕ, (1 / 4 : ℝ) * ∑ d : Direction,
        potentialPair ((0 : Point) - directionVector d) n) =
      (1 / 4 : ℝ) * ∑ d : Direction, ∑' n : ℕ,
        potentialPair ((0 : Point) - directionVector d) n := by
    rw [tsum_mul_left]
    rw [Summable.tsum_finsetSum (f := fun d n ↦
      potentialPair ((0 : Point) - directionVector d) n)
      (fun d _ ↦ summable_potentialPair _)]
  have hsub := (summable_potentialPair 0).tsum_sub havg
  rw [hdef] at hsub
  change -1 = planarPotentialKernel 0 -
    ∑' n : ℕ, (1 / 4 : ℝ) * ∑ d : Direction,
      potentialPair ((0 : Point) - directionVector d) n at hsub
  rw [planarPotentialKernel_zero] at hsub
  rw [havg_tsum] at hsub
  have hsubNeighbors : ∑ d : Direction,
      planarPotentialKernel ((0 : Point) - directionVector d) =
      ∑ d : Direction, planarPotentialKernel (neighbor 0 d) :=
    sum_sub_direction_eq_sum_neighbor _ 0
  change -1 = 0 - (1 / 4 : ℝ) * ∑ d : Direction,
    planarPotentialKernel ((0 : Point) - directionVector d) at hsub
  rw [hsubNeighbors] at hsub
  unfold neighborAverage
  linarith

/-- Full Poisson equation for the planar potential kernel. -/
theorem drift_planarPotentialKernel (x : Point) :
    drift planarPotentialKernel x = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst x
    simp [drift, neighborAverage_planarPotentialKernel_zero]
  · rw [if_neg hx, drift, planarPotentialKernel_harmonicAt_of_ne_zero hx]
    ring

/-- Translate the pole of the planar potential kernel. -/
noncomputable def potentialAt (y z : Point) : ℝ :=
  planarPotentialKernel (z - y)

lemma neighbor_sub_right (x y : Point) (d : Direction) :
    neighbor x d - y = neighbor (x - y) d := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, e⟩
  ext <;> simp [neighbor] <;> ring

lemma neighborAverage_potentialAt (y x : Point) :
    neighborAverage (potentialAt y) x =
      neighborAverage planarPotentialKernel (x - y) := by
  unfold neighborAverage potentialAt
  simp_rw [neighbor_sub_right]

/-- Poisson equation with an arbitrary pole. -/
theorem drift_potentialAt (y x : Point) :
    drift (potentialAt y) x = if x = y then 1 else 0 := by
  rw [drift, neighborAverage_potentialAt]
  change drift planarPotentialKernel (x - y) = _
  rw [drift_planarPotentialKernel]
  by_cases hxy : x = y
  · subst x
    simp
  · rw [if_neg hxy, if_neg (sub_ne_zero.mpr hxy)]

theorem potentialAt_harmonicOn {D : Finset Point} {y : Point}
    (hy : y ∉ D) : HarmonicOn D (potentialAt y) := by
  intro x hx
  have hxy : x ≠ y := fun h ↦ hy (h ▸ hx)
  rw [neighborAverage_potentialAt,
    planarPotentialKernel_harmonicAt_of_ne_zero (sub_ne_zero.mpr hxy)]
  rfl

/-- Exact finite optional stopping for a potential kernel whose pole lies
outside the domain. -/
theorem finite_optionalStopping_potentialAt (D : Finset Point) {y : Point}
    (hy : y ∉ D) (n : ℕ) (x : Point) :
    stoppedExpectation D n (potentialAt y) x = potentialAt y x :=
  finite_optionalStopping D (potentialAt_harmonicOn hy) n x

/-- Exact finite Green--potential identity: the stopped expectation of the
translated potential kernel is its initial value plus expected occupation of
the pole. -/
theorem finite_potentialOccupation_identity (D : Finset Point)
    (y : Point) (n : ℕ) (x : Point) :
    stoppedExpectation D n (potentialAt y) x =
      potentialAt y x + stoppedOccupation D n (fun z ↦ if z = y then 1 else 0) x := by
  rw [finite_dynkin]
  congr 2
  funext z
  exact drift_potentialAt y z

/-- Move a lattice point to the even sublattice by changing it by at most one
nearest-neighbor step.  This lets the sharp even-parity potential-gradient
estimate be used without a parity hypothesis on the original points. -/
noncomputable def evenAnchor (x : Point) : Point :=
  if Even (x.1 + x.2) then x else x - directionVector 0

theorem even_evenAnchor (x : Point) :
    Even ((evenAnchor x).1 + (evenAnchor x).2) := by
  by_cases hx : Even (x.1 + x.2)
  · simpa [evenAnchor, hx] using hx
  · simp only [evenAnchor, if_neg hx]
    exact neighbor_even_of_not_even hx 0

/-- The parity-correction step has the sharp inverse-radius potential cost. -/
theorem abs_planarPotentialKernel_sub_evenAnchor_le {x : Point}
    (hR : 2 < max (firstDiagonalOffset (evenAnchor x))
      (secondDiagonalOffset (evenAnchor x))) :
    |planarPotentialKernel x - planarPotentialKernel (evenAnchor x)| ≤
      300 / ((max (firstDiagonalOffset (evenAnchor x))
        (secondDiagonalOffset (evenAnchor x)) - 2 : ℕ) : ℝ) := by
  by_cases hx : Even (x.1 + x.2)
  · simp [evenAnchor, hx]
    positivity
  · have h := abs_planarPotentialKernel_odd_sub_neighbor_le_radius hx 0
    have hR' : 2 < max (firstDiagonalOffset (x - directionVector 0))
        (secondDiagonalOffset (x - directionVector 0)) := by
      simpa only [evenAnchor, if_neg hx] using hR
    simpa only [evenAnchor, if_neg hx] using h hR'

/-- Whole-lattice finite-displacement estimate.  Each point is moved by at
most one step to the even sublattice; the central comparison is the sharp
`O(L / (R - L))` potential-gradient estimate. -/
theorem abs_planarPotentialKernel_sub_le_via_evenAnchors {x y : Point}
    (hxR : 2 < max (firstDiagonalOffset (evenAnchor x))
      (secondDiagonalOffset (evenAnchor x)))
    (hyR : 2 < max (firstDiagonalOffset (evenAnchor y))
      (secondDiagonalOffset (evenAnchor y)))
    (hgap : natGap (firstDiagonalOffset (evenAnchor x))
          (firstDiagonalOffset (evenAnchor y)) +
        natGap (secondDiagonalOffset (evenAnchor x))
          (secondDiagonalOffset (evenAnchor y)) <
      max (firstDiagonalOffset (evenAnchor x))
        (secondDiagonalOffset (evenAnchor x))) :
    |planarPotentialKernel y - planarPotentialKernel x| ≤
      300 / ((max (firstDiagonalOffset (evenAnchor y))
          (secondDiagonalOffset (evenAnchor y)) - 2 : ℕ) : ℝ) +
      150 * ((natGap (firstDiagonalOffset (evenAnchor x))
            (firstDiagonalOffset (evenAnchor y)) : ℝ) +
          natGap (secondDiagonalOffset (evenAnchor x))
            (secondDiagonalOffset (evenAnchor y))) /
        ((max (firstDiagonalOffset (evenAnchor x))
          (secondDiagonalOffset (evenAnchor x)) -
            (natGap (firstDiagonalOffset (evenAnchor x))
                (firstDiagonalOffset (evenAnchor y)) +
              natGap (secondDiagonalOffset (evenAnchor x))
                (secondDiagonalOffset (evenAnchor y))) : ℕ) : ℝ) +
      300 / ((max (firstDiagonalOffset (evenAnchor x))
          (secondDiagonalOffset (evenAnchor x)) - 2 : ℕ) : ℝ) := by
  have hxlocal := abs_planarPotentialKernel_sub_evenAnchor_le hxR
  have hylocal := abs_planarPotentialKernel_sub_evenAnchor_le hyR
  have hmiddle := abs_planarPotentialKernel_sub_le_radius_sub_gap_of_even
    (even_evenAnchor x) (even_evenAnchor y) hgap
  calc
    |planarPotentialKernel y - planarPotentialKernel x| =
        |(planarPotentialKernel y - planarPotentialKernel (evenAnchor y)) +
          (planarPotentialKernel (evenAnchor y) -
            planarPotentialKernel (evenAnchor x)) +
          (planarPotentialKernel (evenAnchor x) - planarPotentialKernel x)| := by ring_nf
    _ ≤ |planarPotentialKernel y - planarPotentialKernel (evenAnchor y)| +
        |planarPotentialKernel (evenAnchor y) -
          planarPotentialKernel (evenAnchor x)| +
        |planarPotentialKernel (evenAnchor x) - planarPotentialKernel x| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [abs_sub_comm (planarPotentialKernel (evenAnchor x))
        (planarPotentialKernel x)]
      exact add_le_add (add_le_add hylocal hmiddle) hxlocal

/-- Two Green-type quantities which lie in the same translated potential
window differ by the width of that window plus the starting-point potential
oscillation.  This is the algebraic form used in annular Harnack estimates. -/
theorem abs_sub_le_of_common_potential_window
    {gx gy ax ay lower upper : ℝ}
    (hxLower : lower - ax ≤ gx) (hxUpper : gx ≤ upper - ax)
    (hyLower : lower - ay ≤ gy) (hyUpper : gy ≤ upper - ay) :
    |gy - gx| ≤ (upper - lower) + |ay - ax| := by
  rw [abs_le]
  constructor
  · have habs := le_abs_self (ay - ax)
    linarith
  · have habs := neg_abs_le (ay - ax)
    linarith

/-- An additive Harnack bound becomes a multiplicative one once the reference
quantity has a positive lower bound. -/
theorem multiplicative_compare_of_additive
    {p q error lower : ℝ} (herror : 0 ≤ error) (hlower : 0 < lower)
    (hp : lower ≤ p) (hdiff : |q - p| ≤ error) :
    (1 - error / lower) * p ≤ q ∧
      q ≤ (1 + error / lower) * p := by
  have hscale : error ≤ (error / lower) * p := by
    calc
      error = (error / lower) * lower := by field_simp
      _ ≤ (error / lower) * p := by
        gcongr
  rw [abs_le] at hdiff
  constructor <;> nlinarith

end

end AnnulusHarnack
end Erdos1165
