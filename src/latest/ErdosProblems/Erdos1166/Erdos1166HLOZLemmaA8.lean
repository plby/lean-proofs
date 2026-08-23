/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# The discrete Gaussian path sum in HLOZ Lemma A.8

This file isolates the finite, purely analytic object occurring in Lemma A.8
of Hao--Li--Okada--Zheng.  In particular, there is no probability-space or
random-walk hypothesis hidden in the definitions below.

The final estimate in Lemma A.8 is a small-ball estimate: its strength comes
from summing over exponentially many paths.  The last theorem in this file
records the unconditional one-path baseline.  It is useful both as a sanity
check on normalizations and as a precise marker of why a small-ball argument
is indispensable: the baseline has exponent `length * log n`, whereas the
source has exponent of order `n^3 / radius^2`.
-/

namespace Erdos1166.HLOZLemmaA8

open scoped BigOperators ENNReal
open MeasureTheory

/-- The (unnormalized only with respect to counting measure) Gaussian
transition kernel used in HLOZ Lemma A.8.  Its variance as a density on
`ℝ` is `4 * ℓ^2`. -/
noncomputable def b (ℓ : ℕ) (k₁ k₂ : ℤ) : ℝ :=
  (Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ)))⁻¹ *
    Real.exp (-(((k₁ : ℝ) - (k₂ : ℝ)) ^ 2 / (8 * (ℓ : ℝ) ^ 2)))

/-- Continuous version of `b`, used when comparing an integer lattice cell
with the Gaussian path integral. -/
noncomputable def realB (ℓ : ℕ) (x y : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ)))⁻¹ *
    Real.exp (-((x - y) ^ 2 / (8 * (ℓ : ℝ) ^ 2)))

lemma b_pos {ℓ : ℕ} (hℓ : 0 < ℓ) (k₁ k₂ : ℤ) : 0 < b ℓ k₁ k₂ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (mul_pos (by norm_num) hpi)
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  unfold b
  positivity

lemma b_nonneg (ℓ : ℕ) (k₁ k₂ : ℤ) : 0 ≤ b ℓ k₁ k₂ := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp [b]
  · exact (b_pos (Nat.pos_of_ne_zero hℓ) k₁ k₂).le

lemma b_zero_zero (ℓ : ℕ) :
    b ℓ 0 0 = (Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ)))⁻¹ := by
  simp [b]

lemma b_symmetric (ℓ : ℕ) (k₁ k₂ : ℤ) : b ℓ k₁ k₂ = b ℓ k₂ k₁ := by
  unfold b
  congr 3
  ring_nf

lemma b_eq_realB (ℓ : ℕ) (k₁ k₂ : ℤ) :
    b ℓ k₁ k₂ = realB ℓ k₁ k₂ := by
  rfl

lemma realB_nonneg (ℓ : ℕ) (x y : ℝ) : 0 ≤ realB ℓ x y := by
  unfold realB
  positivity

/-- One-cell comparison.  If `k₁,k₂` are within one of the real coordinates
`x,y`, respectively, and both real coordinates have magnitude at most `R`,
then replacing `x,y` by `k₁,k₂` costs at most the displayed Gaussian factor.
The deliberately loose constant makes the lemma easy to sum over a block. -/
lemma exp_cellCost_mul_realB_le_b {ℓ : ℕ} (hℓ : 0 < ℓ)
    {R x y : ℝ} (hR : 0 ≤ R) {k₁ k₂ : ℤ}
    (hk₁ : |(k₁ : ℝ) - x| ≤ 1) (hk₂ : |(k₂ : ℝ) - y| ≤ 1)
    (hx : |x| ≤ R) (hy : |y| ≤ R) :
    Real.exp (-((8 * R + 4) / (8 * (ℓ : ℝ) ^ 2))) * realB ℓ x y ≤
      b ℓ k₁ k₂ := by
  let A : ℝ := (k₁ : ℝ) - (k₂ : ℝ)
  let B : ℝ := x - y
  have hB : |B| ≤ 2 * R := by
    dsimp [B]
    calc
      |x - y| ≤ |x| + |y| := abs_sub x y
      _ ≤ R + R := add_le_add hx hy
      _ = 2 * R := by ring
  have hAB : |A - B| ≤ 2 := by
    dsimp [A, B]
    have heq : ((k₁ : ℝ) - (k₂ : ℝ)) - (x - y) =
        ((k₁ : ℝ) - x) - ((k₂ : ℝ) - y) := by ring
    rw [heq]
    calc
      |((k₁ : ℝ) - x) - ((k₂ : ℝ) - y)| ≤
          |(k₁ : ℝ) - x| + |(k₂ : ℝ) - y| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hk₁ hk₂
      _ = 2 := by norm_num
  have hsq : A ^ 2 ≤ B ^ 2 + (8 * R + 4) := by
    have hdecomp : A = B + (A - B) := by ring
    rw [hdecomp]
    have hBnonneg : 0 ≤ |B| := abs_nonneg B
    have hABnonneg : 0 ≤ |A - B| := abs_nonneg (A - B)
    have hBsquare : B ^ 2 = |B| ^ 2 := by rw [sq_abs]
    have hABsquare : (A - B) ^ 2 = |A - B| ^ 2 := by rw [sq_abs]
    rw [add_sq, hBsquare, hABsquare]
    have hcross : B * (A - B) ≤ |B| * |A - B| := le_abs_self (B * (A - B)) |>.trans_eq
      (abs_mul B (A - B))
    nlinarith
  have hden : 0 < 8 * (ℓ : ℝ) ^ 2 := by
    have : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    positivity
  have hexp :
      Real.exp (-((8 * R + 4) / (8 * (ℓ : ℝ) ^ 2))) *
          Real.exp (-(B ^ 2 / (8 * (ℓ : ℝ) ^ 2))) ≤
        Real.exp (-(A ^ 2 / (8 * (ℓ : ℝ) ^ 2))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have hinv : 0 ≤ (8 * (ℓ : ℝ) ^ 2)⁻¹ := by positivity
    nlinarith
  rw [b_eq_realB]
  unfold realB
  dsimp [A, B] at hexp ⊢
  calc
    Real.exp (-((8 * R + 4) / (8 * (ℓ : ℝ) ^ 2))) *
        ((Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ)))⁻¹ *
          Real.exp (-((x - y) ^ 2 / (8 * (ℓ : ℝ) ^ 2)))) =
      (Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ)))⁻¹ *
        (Real.exp (-((8 * R + 4) / (8 * (ℓ : ℝ) ^ 2))) *
          Real.exp (-((x - y) ^ 2 / (8 * (ℓ : ℝ) ^ 2)))) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ)))⁻¹ *
        Real.exp (-(((k₁ : ℝ) - (k₂ : ℝ)) ^ 2 / (8 * (ℓ : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)

/-- A path with `N` transitions, indexed by its `N + 1` vertices. -/
abbrev Path (N : ℕ) := Fin (N + 1) → ℤ

/-- Product of the HLOZ kernels along a finite path.  The first transition
uses scale `m`; the last uses scale `m + N - 1`. -/
noncomputable def pathWeight (m N : ℕ) (p : Path N) : ℝ :=
  ∏ i : Fin N, b (m + i) (p i.castSucc) (p i.succ)

/-- Continuous path density with the same normalizations as `pathWeight`. -/
noncomputable def realPathWeight (m N : ℕ) (p : Fin (N + 1) → ℝ) : ℝ :=
  ∏ i : Fin N, realB (m + i) (p i.castSucc) (p i.succ)

/-- Accumulated exponent in the integer-cell comparison. -/
noncomputable def cellCostSum (m N : ℕ) (R : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (8 * R i + 4) / (8 * ((m + i : ℕ) : ℝ) ^ 2)

/-- Product form of `exp_cellCost_mul_realB_le_b`. -/
theorem exp_neg_cellCostSum_mul_realPathWeight_le_pathWeight
    {m N : ℕ} (hm : 0 < m) {p : Fin (N + 1) → ℝ} {k : Path N}
    (R : Fin N → ℝ) (hR : ∀ i, 0 ≤ R i)
    (hcell : ∀ i, |(k i : ℝ) - p i| ≤ 1)
    (hp : ∀ i : Fin N, |p i.castSucc| ≤ R i ∧ |p i.succ| ≤ R i) :
    Real.exp (-cellCostSum m N R) * realPathWeight m N p ≤ pathWeight m N k := by
  have hpoint : ∀ i : Fin N,
      Real.exp (-((8 * R i + 4) / (8 * ((m + i : ℕ) : ℝ) ^ 2))) *
          realB (m + i) (p i.castSucc) (p i.succ) ≤
        b (m + i) (k i.castSucc) (k i.succ) := by
    intro i
    apply exp_cellCost_mul_realB_le_b (by omega) (hR i)
    · exact hcell i.castSucc
    · exact hcell i.succ
    · exact (hp i).1
    · exact (hp i).2
  calc
    Real.exp (-cellCostSum m N R) * realPathWeight m N p =
        ∏ i : Fin N,
          (Real.exp (-((8 * R i + 4) / (8 * ((m + i : ℕ) : ℝ) ^ 2))) *
            realB (m + i) (p i.castSucc) (p i.succ)) := by
      rw [cellCostSum, realPathWeight, Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 1
      simp
    _ ≤ ∏ i : Fin N, b (m + i) (k i.castSucc) (k i.succ) := by
      exact Finset.prod_le_prod
        (fun i hi ↦ mul_nonneg (Real.exp_pos _).le (realB_nonneg _ _ _))
        (fun i hi ↦ hpoint i)
    _ = pathWeight m N k := rfl

/-- A uniform radius estimate for the accumulated lattice-cell loss.  This
is the form used on one variance-budgeted block: every scale in the block is
at least `m`, so the loss is bounded by the number of transitions times the
worst numerator divided by `8 m²`. -/
lemma cellCostSum_le_of_radius_le {m N : ℕ} (hm : 0 < m)
    {R : Fin N → ℝ} {Q : ℝ} (hRnonneg : ∀ i, 0 ≤ R i)
    (hRQ : ∀ i, R i ≤ Q) :
    cellCostSum m N R ≤
      (N : ℝ) * ((8 * Q + 4) / (8 * (m : ℝ) ^ 2)) := by
  unfold cellCostSum
  calc
    ∑ i : Fin N, (8 * R i + 4) / (8 * ((m + i : ℕ) : ℝ) ^ 2) ≤
        ∑ _i : Fin N, (8 * Q + 4) / (8 * (m : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hmiR : (m : ℝ) ≤ (m + (i : ℕ) : ℕ) := by
        exact_mod_cast Nat.le_add_right m i
      have hnum : 0 ≤ 8 * R i + 4 := by nlinarith [hRnonneg i]
      have hden : 0 < 8 * (m : ℝ) ^ 2 := by positivity
      have hdenle : 8 * (m : ℝ) ^ 2 ≤ 8 * ((m + i : ℕ) : ℝ) ^ 2 := by
        nlinarith
      calc
        (8 * R i + 4) / (8 * ((m + i : ℕ) : ℝ) ^ 2) ≤
            (8 * R i + 4) / (8 * (m : ℝ) ^ 2) := by
          exact div_le_div_of_nonneg_left hnum hden hdenle
        _ ≤ (8 * Q + 4) / (8 * (m : ℝ) ^ 2) := by
          exact div_le_div_of_nonneg_right (by nlinarith [hRQ i]) hden.le
    _ = (N : ℝ) * ((8 * Q + 4) / (8 * (m : ℝ) ^ 2)) := by simp

/-- Sum of path weights over an arbitrary finite admissible family.  Taking
the family to be the integer paths in the HLOZ corridor recovers the left
side of Lemma A.8 (after reindexing). -/
noncomputable def pathSum (m N : ℕ) (P : Finset (Path N)) : ℝ :=
  ∑ p ∈ P, pathWeight m N p

/-- The identically-zero path. -/
def zeroPath (N : ℕ) : Path N := fun _ ↦ 0

/-- The finite box of integer paths with coordinatewise radii `R`. -/
noncomputable def corridorPaths (N : ℕ) (R : Fin (N + 1) → ℕ) : Finset (Path N) :=
  Fintype.piFinset fun i ↦ Finset.Icc (-(R i : ℤ)) (R i : ℤ)

@[simp] lemma mem_corridorPaths {N : ℕ} {R : Fin (N + 1) → ℕ} {p : Path N} :
    p ∈ corridorPaths N R ↔ ∀ i, |p i| ≤ R i := by
  simp [corridorPaths, abs_le]

@[simp] lemma zeroPath_mem_corridorPaths (N : ℕ) (R : Fin (N + 1) → ℕ) :
    zeroPath N ∈ corridorPaths N R := by
  rw [mem_corridorPaths]
  intro i
  change |(0 : ℤ)| ≤ (R i : ℤ)
  simp

/-- Integer radius corresponding to `ℓ^(1+δ)` in HLOZ Lemma A.8. -/
noncomputable def corridorRadius (δ : ℝ) (ℓ : ℕ) : ℕ :=
  ⌊(ℓ : ℝ) ^ (1 + δ)⌋₊

/-- The literal finite family of integer paths in the HLOZ corridor on a
block starting at scale `m`. -/
noncomputable def hlozCorridorPaths (δ : ℝ) (m N : ℕ) : Finset (Path N) :=
  corridorPaths N fun i ↦ corridorRadius δ (m + i)

@[simp] lemma zeroPath_mem_hlozCorridorPaths (δ : ℝ) (m N : ℕ) :
    zeroPath N ∈ hlozCorridorPaths δ m N := by
  exact zeroPath_mem_corridorPaths N _

/-- The exact finite discrete-Gaussian sum on an HLOZ block. -/
noncomputable def hlozPathSum (δ : ℝ) (m N : ℕ) : ℝ :=
  pathSum m N (hlozCorridorPaths δ m N)

lemma pathWeight_nonneg (m N : ℕ) (p : Path N) : 0 ≤ pathWeight m N p := by
  unfold pathWeight
  exact Finset.prod_nonneg fun i hi ↦ b_nonneg _ _ _

lemma pathSum_nonneg (m N : ℕ) (P : Finset (Path N)) : 0 ≤ pathSum m N P := by
  unfold pathSum
  exact Finset.sum_nonneg fun p hp ↦ pathWeight_nonneg m N p

/-- Every admissible family containing the zero path has mass at least the
weight of that path. -/
lemma pathWeight_zero_le_pathSum {m N : ℕ} {P : Finset (Path N)}
    (hzero : zeroPath N ∈ P) :
    pathWeight m N (zeroPath N) ≤ pathSum m N P := by
  unfold pathSum
  exact Finset.single_le_sum (fun p hp ↦ pathWeight_nonneg m N p) hzero

lemma pathWeight_zero (m N : ℕ) :
    pathWeight m N (zeroPath N) =
      ∏ i : Fin N, (Real.sqrt (2 * Real.pi) * (2 * ((m + i : ℕ) : ℝ)))⁻¹ := by
  simp [pathWeight, zeroPath, b_zero_zero]

lemma sqrt_two_pi_le_four : Real.sqrt (2 * Real.pi) ≤ 4 := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hpi : Real.pi < 4 := Real.pi_lt_four
    nlinarith

/-- A deliberately safe pointwise normalization bound. -/
lemma one_div_eight_mul_upper_le_b_zero {ℓ n : ℕ} (hℓ : 0 < ℓ) (hℓn : ℓ ≤ n) :
    (8 * (n : ℝ))⁻¹ ≤ b ℓ 0 0 := by
  rw [b_zero_zero]
  have hn : (0 : ℝ) < n := by exact_mod_cast hℓ.trans_le hℓn
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  apply (inv_le_inv₀ (by positivity) (by positivity)).2
  calc
      Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ))
          ≤ 4 * (2 * (ℓ : ℝ)) :=
            mul_le_mul_of_nonneg_right sqrt_two_pi_le_four (by positivity)
      _ = 8 * (ℓ : ℝ) := by ring
      _ ≤ 8 * (n : ℝ) := by exact mul_le_mul_of_nonneg_left (by exact_mod_cast hℓn) (by norm_num)

/-- The zero-path baseline for an arbitrary admissible finite path family.
This theorem is entirely unconditional and has no hidden analytic input. -/
theorem pow_inv_le_pathSum {m N n : ℕ} {P : Finset (Path N)}
    (hm : 0 < m) (hupper : m + N ≤ n) (hzero : zeroPath N ∈ P) :
    ((8 * (n : ℝ))⁻¹) ^ N ≤ pathSum m N P := by
  refine le_trans ?_ (pathWeight_zero_le_pathSum hzero)
  rw [pathWeight_zero]
  calc
    ((8 * (n : ℝ))⁻¹) ^ N = ∏ _i : Fin N, (8 * (n : ℝ))⁻¹ := by simp
    _ ≤ ∏ i : Fin N, (Real.sqrt (2 * Real.pi) * (2 * ((m + i : ℕ) : ℝ)))⁻¹ := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        simpa [b_zero_zero] using
          (one_div_eight_mul_upper_le_b_zero (ℓ := m + (i : ℕ)) (n := n)
            (by omega) (by omega))

/-- Exponential form of the zero-path baseline.  In the intended application
`N` is the length of a block and `n` is its upper scale. -/
theorem exp_neg_length_log_le_pathSum {m N n : ℕ} {P : Finset (Path N)}
    (hm : 0 < m) (hupper : m + N ≤ n) (hzero : zeroPath N ∈ P) :
    Real.exp (-(N : ℝ) * Real.log (8 * (n : ℝ))) ≤ pathSum m N P := by
  have hn : (0 : ℝ) < 8 * n := by
    have : 0 < n := lt_of_lt_of_le hm (Nat.le_add_right m N) |>.trans_le hupper
    positivity
  rw [show Real.exp (-(N : ℝ) * Real.log (8 * (n : ℝ))) =
      ((8 * (n : ℝ))⁻¹) ^ N by
    calc
      Real.exp (-(N : ℝ) * Real.log (8 * (n : ℝ))) =
          Real.exp ((N : ℝ) * (-Real.log (8 * (n : ℝ)))) := by congr 1; ring
      _ = Real.exp (-Real.log (8 * (n : ℝ))) ^ N := by rw [Real.exp_nat_mul]
      _ = ((8 * (n : ℝ))⁻¹) ^ N := by rw [Real.exp_neg, Real.exp_log hn]]
  exact pow_inv_le_pathSum hm hupper hzero

/-- Unconditional baseline specialized to the literal HLOZ corridor. -/
theorem exp_neg_length_log_le_hlozPathSum (δ : ℝ) {m N n : ℕ}
    (hm : 0 < m) (hupper : m + N ≤ n) :
    Real.exp (-(N : ℝ) * Real.log (8 * (n : ℝ))) ≤ hlozPathSum δ m N := by
  exact exp_neg_length_log_le_pathSum hm hupper
    (zeroPath_mem_hlozCorridorPaths δ m N)

/-! ## Block iteration

The source proof groups Gaussian increments into variance-budgeted blocks.
The following recursion and lemma isolate the entirely finite multiplication
step: a uniform lower bound `c` for the mass of returning from the central set
to the central set on each block gives total mass at least `c ^ q` after `q`
blocks.
-/

section Blocks

variable {α : Type*}

/-- Total mass of a time-inhomogeneous finite kernel chain, restricted after
each step to the finite set `S`. -/
noncomputable def restrictedChainMass (S : Finset α) (K : ℕ → α → α → ℝ) :
    ℕ → α → ℝ
  | 0, _ => 1
  | q + 1, x =>
      ∑ y ∈ S, K 0 x y *
        restrictedChainMass S (fun i ↦ K (i + 1)) q y

lemma restrictedChainMass_nonneg (S : Finset α) (K : ℕ → α → α → ℝ)
    (hK : ∀ i x y, 0 ≤ K i x y) (q : ℕ) (x : α) :
    0 ≤ restrictedChainMass S K q x := by
  induction q generalizing x K with
  | zero => simp [restrictedChainMass]
  | succ q ih =>
      simp only [restrictedChainMass]
      exact Finset.sum_nonneg fun y hy ↦
        mul_nonneg (hK _ _ _)
          (ih (fun i ↦ K (i + 1)) (fun i ↦ hK (i + 1)) y)

/-- Uniform one-block mass bounds multiply without loss. -/
theorem pow_le_restrictedChainMass (S : Finset α) (K : ℕ → α → α → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hK : ∀ i x y, 0 ≤ K i x y)
    {q : ℕ} (hrow : ∀ i < q, ∀ x ∈ S, c ≤ ∑ y ∈ S, K i x y)
    {x : α} (hx : x ∈ S) :
    c ^ q ≤ restrictedChainMass S K q x := by
  induction q generalizing x K with
  | zero => simp [restrictedChainMass]
  | succ q ih =>
      simp only [restrictedChainMass, pow_succ]
      calc
        c ^ q * c ≤ c ^ q * ∑ y ∈ S, K 0 x y := by
          exact mul_le_mul_of_nonneg_left (hrow 0 (by omega) x hx) (pow_nonneg hc q)
        _ = ∑ y ∈ S, K 0 x y * c ^ q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ ≤ ∑ y ∈ S, K 0 x y *
            restrictedChainMass S (fun i ↦ K (i + 1)) q y := by
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left
            (ih (K := fun i ↦ K (i + 1))
              (fun i z w ↦ hK (i + 1) z w)
              (fun i hi z hz ↦ hrow (i + 1) (by omega) z hz) hy)
            (hK 0 x y)

end Blocks

/-! The same multiplication principle for a continuum state space.  This is
the form used for Gaussian block endpoints: the restriction to `S` forces
every endpoint back into the narrow central interval. -/

noncomputable def restrictedMeasureChainMass {α : Type*} [MeasurableSpace α]
    (S : Set α) (K : ℕ → α → Measure α) : ℕ → α → ℝ≥0∞
  | 0, _ => 1
  | q + 1, x => ∫⁻ y in S,
      restrictedMeasureChainMass S (fun i ↦ K (i + 1)) q y ∂K 0 x

theorem pow_le_restrictedMeasureChainMass {α : Type*} [MeasurableSpace α]
    (S : Set α) (hS : MeasurableSet S) (K : ℕ → α → Measure α)
    {c : ℝ≥0∞} {q : ℕ}
    (hrow : ∀ i < q, ∀ x ∈ S, c ≤ K i x S)
    {x : α} (hx : x ∈ S) :
    c ^ q ≤ restrictedMeasureChainMass S K q x := by
  induction q generalizing x K with
  | zero => simp [restrictedMeasureChainMass]
  | succ q ih =>
      simp only [restrictedMeasureChainMass, pow_succ]
      calc
        c ^ q * c ≤ c ^ q * K 0 x S := by
          gcongr
          exact hrow 0 (by omega) x hx
        _ = ∫⁻ _y in S, c ^ q ∂K 0 x := by rw [setLIntegral_const]
        _ ≤ ∫⁻ y in S,
            restrictedMeasureChainMass S (fun i ↦ K (i + 1)) q y ∂K 0 x := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hS] with y hy
          exact ih (K := fun i ↦ K (i + 1))
            (fun i hi z hz ↦ hrow (i + 1) (by omega) z hz) hy

/-! A version of the same multiplication argument which retains all sampled
block increments.  This is the form needed to embed the iterated reset event
into the single finite Gaussian increment corridor. -/

variable {Ω α : Type*} [MeasurableSpace Ω]

def sampledChainGood (S : Set α) (G : ℕ → α → Set Ω)
    (step : ℕ → α → Ω → α) : (q : ℕ) → α → Set (Fin q → Ω)
  | 0, _ => Set.univ
  | q + 1, x => {ω |
      ω 0 ∈ G 0 x ∧ step 0 x (ω 0) ∈ S ∧
        Fin.tail ω ∈ sampledChainGood S (fun i ↦ G (i + 1))
          (fun i ↦ step (i + 1)) q (step 0 x (ω 0))}

/-- Uniform lower bounds for the mass of a good block, including its return
to the central state set, multiply on the finite product of the block sample
spaces.  No Markov-process premise is hidden here: the conclusion is a
literal finite product-measure estimate. -/
theorem pow_le_measure_sampledChainGood
    (S : Set α) (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (G : ℕ → α → Set Ω) (step : ℕ → α → Ω → α)
    {c : ℝ≥0∞} {q : ℕ}
    (hmeas : ∀ (k r : ℕ) (x : α),
      MeasurableSet (sampledChainGood S (fun i ↦ G (k + i))
        (fun i ↦ step (k + i)) r x))
    (hrowMeas : ∀ i x,
      MeasurableSet (G i x ∩ {ω | step i x ω ∈ S}))
    (hrow : ∀ i < q, ∀ x ∈ S, c ≤ μ i (G i x ∩ {ω | step i x ω ∈ S}))
    {x : α} (hx : x ∈ S) :
    c ^ q ≤ (Measure.pi fun i : Fin q ↦ μ i)
      (sampledChainGood S G step q x) := by
  induction q generalizing μ G step x with
  | zero => simp [sampledChainGood]
  | succ q ih =>
      let E : Set (Fin (q + 1) → Ω) := sampledChainGood S G step (q + 1) x
      let P : Set (Ω × (Fin q → Ω)) := {z |
        z.1 ∈ G 0 x ∧ step 0 x z.1 ∈ S ∧
          z.2 ∈ sampledChainGood S (fun i ↦ G (i + 1))
            (fun i ↦ step (i + 1)) q (step 0 x z.1)}
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q + 1) ↦ Ω) 0
      have hEP : E = e ⁻¹' P := by
        ext ω
        simp [E, P, e, sampledChainGood,
          MeasurableEquiv.piFinSuccAbove_apply]
      have hE : MeasurableSet E := by simpa [E] using hmeas 0 (q + 1) x
      have hP : MeasurableSet P := by
        have heq : P = e.symm ⁻¹' E := by
          rw [hEP]
          ext z
          simp
        rw [heq]
        exact e.symm.measurable hE
      have hmeasure :
          (Measure.pi fun i : Fin (q + 1) ↦ μ i) E =
            ∫⁻ a, (Measure.pi fun j : Fin q ↦ μ (j + 1)) (Prod.mk a ⁻¹' P) ∂μ 0 := by
        rw [hEP,
          (measurePreserving_piFinSuccAbove (fun i : Fin (q + 1) ↦ μ i) 0).measure_preimage
            hP.nullMeasurableSet,
          Measure.prod_apply hP]
        simp
      have hrow0 : c ≤ μ 0 (G 0 x ∩ {a | step 0 x a ∈ S}) :=
        hrow 0 (by omega) x hx
      calc
        c ^ (q + 1) = c ^ q * c := pow_succ c q
        _ ≤ c ^ q * μ 0 (G 0 x ∩ {a | step 0 x a ∈ S}) := by gcongr
        _ = ∫⁻ _a in G 0 x ∩ {a | step 0 x a ∈ S}, c ^ q ∂μ 0 := by
          rw [setLIntegral_const]
        _ ≤ ∫⁻ a in G 0 x ∩ {a | step 0 x a ∈ S},
            (Measure.pi fun j : Fin q ↦ μ (j + 1))
              (sampledChainGood S (fun i ↦ G (i + 1))
                (fun i ↦ step (i + 1)) q (step 0 x a)) ∂μ 0 := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (hrowMeas 0 x)] with a ha
          exact ih
            (μ := fun i ↦ μ (i + 1)) (G := fun i ↦ G (i + 1))
            (step := fun i ↦ step (i + 1))
            (fun k r z ↦ by
              simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                hmeas (k + 1) r z)
            (fun i z ↦ hrowMeas (i + 1) z)
            (fun i hi z hz ↦ hrow (i + 1) (by omega) z hz) ha.2
        _ = ∫⁻ a,
            (Measure.pi fun j : Fin q ↦ μ (j + 1)) (Prod.mk a ⁻¹' P) ∂μ 0 := by
          rw [← lintegral_indicator (hrowMeas 0 x)]
          apply lintegral_congr
          intro a
          by_cases ha : a ∈ G 0 x ∩ {a | step 0 x a ∈ S}
          · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at ha
            simp [P, ha.1, ha.2]
          · have hnot : ¬(a ∈ G 0 x ∧ step 0 x a ∈ S) := by simpa using ha
            have hempty : Prod.mk a ⁻¹' P = ∅ := by
              ext z
              simp only [Set.mem_preimage, Set.mem_ofPred_eq, P,
                Set.mem_empty_iff_false, iff_false]
              intro hz
              exact hnot ⟨hz.1, hz.2.1⟩
            rw [hempty, measure_empty]
            simp [ha]
        _ = (Measure.pi fun i : Fin (q + 1) ↦ μ i) E := hmeasure.symm

variable [MeasurableSpace α]

/-- Joint measurability of the retained-sample chain event.  The joint form
is essential because the initial state of each tail is the measurable random
endpoint of the preceding block. -/
lemma measurableSet_sampledChainGood_joint
    (S : Set α) (hS : MeasurableSet S)
    (G : ℕ → α → Set Ω) (step : ℕ → α → Ω → α)
    (hG : ∀ i, MeasurableSet {z : α × Ω | z.2 ∈ G i z.1})
    (hstep : ∀ i, Measurable fun z : α × Ω ↦ step i z.1 z.2) :
    ∀ (k q : ℕ), MeasurableSet {z : α × (Fin q → Ω) |
      z.2 ∈ sampledChainGood S (fun i ↦ G (k + i))
        (fun i ↦ step (k + i)) q z.1} := by
  intro k q
  induction q generalizing k with
  | zero => simp [sampledChainGood]
  | succ q ih =>
      let head : α × (Fin (q + 1) → Ω) → α × Ω := fun z ↦ (z.1, z.2 0)
      let next : α × (Fin (q + 1) → Ω) → α × (Fin q → Ω) := fun z ↦
        (step k z.1 (z.2 0), Fin.tail z.2)
      have hhead : Measurable head := by fun_prop
      have hnext : Measurable next := by
        dsimp [next]
        apply Measurable.prodMk
        · exact (hstep k).comp (measurable_fst.prodMk
            ((measurable_pi_apply 0).comp measurable_snd))
        · refine measurable_pi_lambda _ fun j ↦ ?_
          exact (measurable_pi_apply j.succ).comp measurable_snd
      have hfirst : MeasurableSet {z : α × (Fin (q + 1) → Ω) |
          z.2 0 ∈ G k z.1} := by
        simpa [head] using hhead (hG k)
      have hcentral : MeasurableSet {z : α × (Fin (q + 1) → Ω) |
          step k z.1 (z.2 0) ∈ S} := by
        exact ((hstep k).comp (measurable_fst.prodMk
          ((measurable_pi_apply 0).comp measurable_snd))) hS
      have htail : MeasurableSet {z : α × (Fin (q + 1) → Ω) |
          Fin.tail z.2 ∈ sampledChainGood S (fun i ↦ G (k + 1 + i))
            (fun i ↦ step (k + 1 + i)) q (step k z.1 (z.2 0))} := by
        have hh := hnext (ih (k + 1))
        convert hh using 1 <;>
          simp only [next, Set.preimage_ofPred_eq, Nat.add_assoc]
      convert hfirst.inter (hcentral.inter htail) using 1
      ext z
      simp only [sampledChainGood, Set.mem_ofPred_eq, Set.mem_inter_iff,
        Nat.add_zero, Nat.add_assoc]
      simpa only [Nat.add_comm]

lemma measurableSet_sampledChainGood
    (S : Set α) (hS : MeasurableSet S)
    (G : ℕ → α → Set Ω) (step : ℕ → α → Ω → α)
    (hG : ∀ i, MeasurableSet {z : α × Ω | z.2 ∈ G i z.1})
    (hstep : ∀ i, Measurable fun z : α × Ω ↦ step i z.1 z.2)
    (k q : ℕ) (x : α) :
    MeasurableSet (sampledChainGood S (fun i ↦ G (k + i))
      (fun i ↦ step (k + i)) q x) := by
  have hj := measurableSet_sampledChainGood_joint S hS G step hG hstep k q
  exact (measurable_const.prodMk measurable_id) hj

/-- Exponential form of the block-product cost at the safe constant `1/4`. -/
lemma quarter_pow_eq_exp (q : ℕ) :
    (1 / 4 : ℝ) ^ q = Real.exp (-(q : ℝ) * Real.log 4) := by
  calc
    (1 / 4 : ℝ) ^ q = (Real.exp (-Real.log 4)) ^ q := by
      congr 1
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      norm_num
    _ = Real.exp ((q : ℝ) * (-Real.log 4)) := by rw [Real.exp_nat_mul]
    _ = Real.exp (-(q : ℝ) * Real.log 4) := by congr 1; ring

/-- Exponential form of the block-product cost at the reset constant proved
below. -/
lemma one_twentyfifth_pow_eq_exp (q : ℕ) :
    (1 / 25 : ℝ) ^ q = Real.exp (-(q : ℝ) * Real.log 25) := by
  calc
    (1 / 25 : ℝ) ^ q = (Real.exp (-Real.log 25)) ^ q := by
      congr 1
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 25)]
      norm_num
    _ = Real.exp ((q : ℝ) * (-Real.log 25)) := by rw [Real.exp_nat_mul]
    _ = Real.exp (-(q : ℝ) * Real.log 25) := by congr 1; ring

/-- End-to-end finite block iteration at the constant delivered by the
Gaussian reset lemma. -/
theorem exp_neg_blockCost_le_restrictedChainMass {α : Type*}
    (S : Finset α) (K : ℕ → α → α → ℝ)
    (hK : ∀ i x y, 0 ≤ K i x y) {q : ℕ}
    (hrow : ∀ i < q, ∀ x ∈ S, (1 / 25 : ℝ) ≤ ∑ y ∈ S, K i x y)
    {x : α} (hx : x ∈ S) :
    Real.exp (-(q : ℝ) * Real.log 25) ≤ restrictedChainMass S K q x := by
  rw [← one_twentyfifth_pow_eq_exp]
  exact pow_le_restrictedChainMass S K (by norm_num) hK hrow hx

/-! ## One-block reset assembly

For a Gaussian block, `A` will be the event that the endpoint returns to a
narrow central interval and `B` the event that all intermediate positions
remain in the wider corridor.  A Gaussian interval estimate supplies the
lower bound for `A`; Kolmogorov's maximal inequality supplies the upper bound
for `Bᶜ`.  The elementary subtraction below combines the two estimates and
does not use a reflection principle.
-/

open MeasureTheory Set ProbabilityTheory

theorem measureReal_sub_compl_le_inter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A B : Set Ω) :
    μ.real A - μ.real Bᶜ ≤ μ.real (A ∩ B) := by
  have hsubset : A ⊆ (A ∩ B) ∪ Bᶜ := by
    intro ω hω
    by_cases hB : ω ∈ B
    · exact Or.inl ⟨hω, hB⟩
    · exact Or.inr hB
  have hle : μ.real A ≤ μ.real (A ∩ B) + μ.real Bᶜ :=
    (measureReal_mono hsubset).trans (measureReal_union_le _ _)
  linarith

/-- Safe numerical form used when iterating blocks. -/
theorem quarter_le_measureReal_inter_of_endpoint_and_exit {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (A B : Set Ω)
    (hendpoint : (1 / 2 : ℝ) ≤ μ.real A)
    (hexit : μ.real Bᶜ ≤ 1 / 4) :
    (1 / 4 : ℝ) ≤ μ.real (A ∩ B) := by
  have h := measureReal_sub_compl_le_inter μ A B
  linarith

/-- Constants matched to the direct Gaussian estimate below. -/
theorem one_twentyfifth_le_measureReal_inter_of_endpoint_and_exit {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (A B : Set Ω)
    (hendpoint : (1 / 20 : ℝ) ≤ μ.real A)
    (hexit : μ.real Bᶜ ≤ 1 / 100) :
    (1 / 25 : ℝ) ≤ μ.real (A ∩ B) := by
  have h := measureReal_sub_compl_le_inter μ A B
  linarith

/-- Squaring a real `L²` martingale gives a nonnegative submartingale.  This
is the conditional-Jensen step needed to derive Kolmogorov's maximal
inequality from Mathlib's Doob inequality. -/
theorem sq_submartingale_of_martingale {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ 𝒢] {S : ℕ → Ω → ℝ}
    (hS : Martingale S 𝒢 μ) (h2 : ∀ n, MemLp (S n) 2 μ) :
    Submartingale (fun n ω ↦ (S n ω) ^ 2) 𝒢 μ := by
  refine ⟨?_, ?_, fun n ↦ (h2 n).integrable_sq⟩
  · convert hS.stronglyAdapted.mul hS.stronglyAdapted using 1
    funext n ω
    simp [pow_two]
  · intro i j hij
    have hjensen := (even_two.convexOn_pow (𝕜 := ℝ)).map_condExp_le_univ
      (𝒢.le i) (continuous_pow 2).lowerSemicontinuous
      ((h2 j).integrable one_le_two) (h2 j).integrable_sq
    filter_upwards [hS.condExp_ae_eq hij, hjensen] with ω hcond hj
    dsimp only [Function.comp_apply] at hj
    rw [hcond] at hj
    exact hj

/-- A convenient consequence of Mathlib's Doob maximal inequality.  This is
the exact library-facing form needed for the blockwise Kolmogorov argument:
once the squared partial sums have been registered as a nonnegative
submartingale, their exit mass is controlled by the terminal second moment. -/
theorem maximal_ineq_le_terminal_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    {f : ℕ → Ω → ℝ} (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    (ε : NNReal) (n : ℕ) :
    (ε : ENNReal) * μ {ω |
        (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ f k ω} ≤
      ENNReal.ofReal (∫ ω, f n ω ∂μ) := by
  calc
    _ ≤ ENNReal.ofReal
        (∫ ω in {ω |
          (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ f k ω},
          f n ω ∂μ) := maximal_ineq hsub hnonneg n
    _ ≤ ENNReal.ofReal (∫ ω, f n ω ∂μ) := by
      exact ENNReal.ofReal_le_ofReal
        (setIntegral_le_integral (hsub.integrable n) (Filter.Eventually.of_forall (hnonneg n)))

/-- Kolmogorov/Doob maximal inequality for an arbitrary real `L²`
martingale, stated at the squared threshold so that no square-root or
absolute-value conversion is hidden. -/
theorem martingale_sq_maximal_ineq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ 𝒢] {S : ℕ → Ω → ℝ}
    (hS : Martingale S 𝒢 μ) (h2 : ∀ n, MemLp (S n) 2 μ)
    (ε : NNReal) (n : ℕ) :
    (ε : ENNReal) * μ {ω |
        (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k ↦ (S k ω) ^ 2} ≤
      ENNReal.ofReal (∫ ω, (S n ω) ^ 2 ∂μ) := by
  exact maximal_ineq_le_terminal_integral
    (sq_submartingale_of_martingale hS h2) (fun _ _ ↦ sq_nonneg _) ε n

/-- The numerical exit estimate used in one HLOZ block.  If the terminal
second moment uses at most one percent of the squared corridor radius, then
the probability of crossing that radius anywhere in the block is at most
one percent. -/
theorem martingale_exit_measureReal_le_one_hundredth {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ 𝒢]
    {S : ℕ → Ω → ℝ} (hS : Martingale S 𝒢 μ)
    (h2 : ∀ n, MemLp (S n) 2 μ) {r : ℝ} (hr : 0 < r) (n : ℕ)
    (hsecond : (∫ ω, (S n ω) ^ 2 ∂μ) ≤ r ^ 2 / 100) :
    μ.real {ω |
        r ^ 2 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k ↦ (S k ω) ^ 2} ≤ 1 / 100 := by
  let ε : NNReal := ⟨r ^ 2, sq_nonneg r⟩
  have hmax := martingale_sq_maximal_ineq hS h2 ε n
  have hbound : ENNReal.ofReal (∫ ω, (S n ω) ^ 2 ∂μ) ≤
      ENNReal.ofReal (r ^ 2 / 100) := ENNReal.ofReal_le_ofReal hsecond
  have h := hmax.trans hbound
  have htop : ENNReal.ofReal (r ^ 2 / 100) ≠ ⊤ := by simp
  have hreal := ENNReal.toReal_mono htop h
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ 2 / 100)] at hreal
  dsimp [ε] at hreal
  change r ^ 2 * μ.real {ω |
        r ^ 2 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k ↦ (S k ω) ^ 2} ≤ r ^ 2 / 100 at hreal
  nlinarith [sq_pos_of_pos hr]

/-- The same maximal estimate with a quarter of the squared radius as the
variance budget.  This looser version is useful for a possibly short final
variance block. -/
theorem martingale_exit_measureReal_le_one_quarter {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ 𝒢]
    {S : ℕ → Ω → ℝ} (hS : Martingale S 𝒢 μ)
    (h2 : ∀ n, MemLp (S n) 2 μ) {r : ℝ} (hr : 0 < r) (n : ℕ)
    (hsecond : (∫ ω, (S n ω) ^ 2 ∂μ) ≤ r ^ 2 / 4) :
    μ.real {ω |
        r ^ 2 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k ↦ (S k ω) ^ 2} ≤ 1 / 4 := by
  let ε : NNReal := ⟨r ^ 2, sq_nonneg r⟩
  have hmax := martingale_sq_maximal_ineq hS h2 ε n
  have hbound : ENNReal.ofReal (∫ ω, (S n ω) ^ 2 ∂μ) ≤
      ENNReal.ofReal (r ^ 2 / 4) := ENNReal.ofReal_le_ofReal hsecond
  have h := hmax.trans hbound
  have htop : ENNReal.ofReal (r ^ 2 / 4) ≠ ⊤ := by simp
  have hreal := ENNReal.toReal_mono htop h
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ 2 / 4)] at hreal
  dsimp [ε] at hreal
  change r ^ 2 * μ.real {ω |
        r ^ 2 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k ↦ (S k ω) ^ 2} ≤ r ^ 2 / 4 at hreal
  nlinarith [sq_pos_of_pos hr]

/-! ## A direct Gaussian endpoint estimate

The next estimate is intentionally coarse.  It is designed for the block
argument: if the variance of a block is between `r^2 / 1600` and
`r^2 / 1000`, then, uniformly over starting points in the central interval
`[-r/100,r/100]`, at least `1/20` of the Gaussian endpoint mass returns to
that interval.
-/

/-- Centered Gaussian transition density with variance `v`. -/
noncomputable def gaussianDensity (v x y : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * v))⁻¹ *
    Real.exp (-((y - x) ^ 2 / (2 * v)))

lemma gaussianDensity_continuous {v x : ℝ} :
    Continuous (gaussianDensity v x) := by
  unfold gaussianDensity
  fun_prop

lemma gaussianDensity_central_pointwise {r v x y : ℝ}
    (hr : 0 < r) (hvlow : r ^ 2 / 1600 ≤ v) (hvup : v ≤ r ^ 2 / 1000)
    (hx : |x| ≤ r / 100) (hy : |y| ≤ r / 100) :
    5 / (2 * r) ≤ gaussianDensity v x y := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hv : 0 < v := lt_of_lt_of_le (div_pos hr2 (by norm_num)) hvlow
  have hdiff : |y - x| ≤ r / 50 := by
    calc
      |y - x| ≤ |y| + |x| := abs_sub y x
      _ ≤ r / 100 + r / 100 := add_le_add hy hx
      _ = r / 50 := by ring
  have hdiffsq : (y - x) ^ 2 ≤ r ^ 2 / 2500 := by
    rw [sq, sq, ← abs_mul_abs_self (y - x), ← abs_mul_abs_self r]
    nlinarith [abs_nonneg (y - x), abs_of_pos hr]
  have hratio : (y - x) ^ 2 / (2 * v) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : r ^ 2 / 2500 ≤ 2 * (r ^ 2 / 1600) := by
      nlinarith [sq_nonneg r]
    nlinarith
  have hsqrt : Real.sqrt (2 * Real.pi * v) ≤ r / 10 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hpi : Real.pi < 4 := Real.pi_lt_four
      have harg : 2 * Real.pi * v ≤ r ^ 2 / 100 := by
        calc
          2 * Real.pi * v ≤ 8 * v := by nlinarith
          _ ≤ 8 * (r ^ 2 / 1000) := by gcongr
          _ ≤ r ^ 2 / 100 := by nlinarith [sq_nonneg r]
      nlinarith
  have hsqrtpos : 0 < Real.sqrt (2 * Real.pi * v) := by
    apply Real.sqrt_pos.2
    positivity
  have hnorm : 10 / r ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    have hinv := (inv_le_inv₀ (by positivity : 0 < r / 10) hsqrtpos).2 hsqrt
    have heq : (r / 10)⁻¹ = 10 / r := by
      field_simp [hr.ne']
    rwa [heq] at hinv
  have hexp : (1 / 4 : ℝ) ≤ Real.exp (-((y - x) ^ 2 / (2 * v))) := by
    have hquarter : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
      linarith [Real.exp_neg_one_gt_d9]
    exact hquarter.trans (Real.exp_le_exp.mpr (by linarith))
  unfold gaussianDensity
  calc
    5 / (2 * r) = (10 / r) * (1 / 4) := by field_simp; ring
    _ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ *
        Real.exp (-((y - x) ^ 2 / (2 * v))) :=
      mul_le_mul hnorm hexp (by positivity) (by positivity)

theorem one_twentieth_le_integral_gaussianDensity_central {r v x : ℝ}
    (hr : 0 < r) (hvlow : r ^ 2 / 1600 ≤ v) (hvup : v ≤ r ^ 2 / 1000)
    (hx : |x| ≤ r / 100) :
    (1 / 20 : ℝ) ≤
      ∫ y in Icc (-r / 100) (r / 100), gaussianDensity v x y := by
  have hv : 0 < v := lt_of_lt_of_le (div_pos (sq_pos_of_pos hr) (by norm_num)) hvlow
  have hconst : IntegrableOn (fun _y : ℝ ↦ 5 / (2 * r)) (Icc (-r / 100) (r / 100)) :=
    continuous_const.integrableOn_Icc
  have hdensity : IntegrableOn (gaussianDensity v x) (Icc (-r / 100) (r / 100)) :=
    gaussianDensity_continuous.integrableOn_Icc
  have hmono := setIntegral_mono_on hconst hdensity measurableSet_Icc
    (fun y hy ↦ gaussianDensity_central_pointwise hr hvlow hvup hx (by
      rw [mem_Icc] at hy
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]))
  have hmeasure : volume.real (Icc (-r / 100) (r / 100)) = r / 50 := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
    · ring
    · linarith
  rw [setIntegral_const, hmeasure, smul_eq_mul] at hmono
  calc
    (1 / 20 : ℝ) = r / 50 * (5 / (2 * r)) := by
      field_simp [hr.ne']
      norm_num
    _ ≤ _ := hmono

lemma gaussianDensity_eq_gaussianPDFReal {v x : ℝ} (hv : 0 ≤ v) :
    gaussianDensity v x = gaussianPDFReal x (NNReal.mk v hv) := by
  funext y
  rw [gaussianPDFReal_def]
  unfold gaussianDensity
  change (Real.sqrt (2 * Real.pi * v))⁻¹ *
      Real.exp (-((y - x) ^ 2 / (2 * v))) =
    (Real.sqrt (2 * Real.pi * v))⁻¹ *
      Real.exp (-((y - x) ^ 2) / (2 * v))
  congr 2
  ring

/-- Measure-theoretic form of the endpoint reset estimate.  Thus the direct
density calculation above applies without any unformalized identification
between an integral and a Gaussian law. -/
theorem one_twentieth_le_gaussianReal_central {r v x : ℝ}
    (hr : 0 < r) (hvlow : r ^ 2 / 1600 ≤ v) (hvup : v ≤ r ^ 2 / 1000)
    (hx : |x| ≤ r / 100) :
    (1 / 20 : ℝ) ≤
      (gaussianReal x (NNReal.mk v
        ((div_nonneg (sq_nonneg r) (by norm_num)).trans hvlow))).real
        (Icc (-r / 100) (r / 100)) := by
  have hv : 0 < v := lt_of_lt_of_le (div_pos (sq_pos_of_pos hr) (by norm_num)) hvlow
  let vn : NNReal := NNReal.mk v hv.le
  have hvn : vn ≠ 0 := by
    intro h
    apply hv.ne'
    have hc := congrArg (fun z : NNReal ↦ (z : ℝ)) h
    change v = 0 at hc
    exact hc
  have hmeasure := gaussianReal_apply_eq_integral x (v := vn) hvn
    (Icc (-r / 100) (r / 100))
  rw [measureReal_def]
  rw [hmeasure, ENNReal.toReal_ofReal]
  · rw [← gaussianDensity_eq_gaussianPDFReal hv.le]
    exact one_twentieth_le_integral_gaussianDensity_central hr hvlow hvup hx
  · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y ↦
      gaussianPDFReal_nonneg x vn y)

/-! ## The canonical inhomogeneous Gaussian process

The source density is the joint density of independent centered Gaussian
increments whose variances are allowed to vary with time.  We construct that
process on Mathlib's infinite product probability space and verify, without
any stochastic premise, its independence, martingale property, Gaussian
endpoint law, and terminal second moment.
-/

noncomputable def gaussianIncrementMeasure (v : ℕ → NNReal) (i : ℕ) : Measure ℝ :=
  gaussianReal 0 (v i)

noncomputable instance instProbabilityGaussianIncrementMeasure
    (v : ℕ → NNReal) (i : ℕ) :
    IsProbabilityMeasure (gaussianIncrementMeasure v i) := by
  unfold gaussianIncrementMeasure
  infer_instance

noncomputable def gaussianProductMeasure (v : ℕ → NNReal) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (gaussianIncrementMeasure v)

noncomputable instance instProbabilityGaussianProductMeasure (v : ℕ → NNReal) :
    IsProbabilityMeasure (gaussianProductMeasure v) := by
  unfold gaussianProductMeasure
  infer_instance

def gaussianCoordinate (i : ℕ) (ω : ℕ → ℝ) : ℝ := ω i

@[fun_prop] lemma measurable_gaussianCoordinate (i : ℕ) :
    Measurable (gaussianCoordinate i) := by
  exact measurable_pi_apply i

noncomputable def gaussianNaturalFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  Filtration.natural gaussianCoordinate fun i ↦
    (measurable_pi_apply i).stronglyMeasurable

/-- The zeroth value includes coordinate zero.  This indexing is convenient
for a block with variables `Δ_(m+1),…,Δ_n`: coordinate zero is the
initial increment with variance `4m²`. -/
def gaussianPartialSum (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), gaussianCoordinate i ω

lemma gaussianCoordinate_iIndepFun (v : ℕ → NNReal) :
    iIndepFun gaussianCoordinate (gaussianProductMeasure v) := by
  exact iIndepFun_infinitePi (X := fun _ ↦ id) (by fun_prop)

lemma gaussianCoordinate_hasLaw (v : ℕ → NNReal) (i : ℕ) :
    HasLaw (gaussianCoordinate i) (gaussianReal 0 (v i))
      (gaussianProductMeasure v) := by
  constructor
  · exact (measurable_gaussianCoordinate i).aemeasurable
  · exact Measure.infinitePi_map_eval (gaussianIncrementMeasure v) i

lemma integral_gaussianCoordinate (v : ℕ → NNReal) (i : ℕ) :
    ∫ ω, gaussianCoordinate i ω ∂gaussianProductMeasure v = 0 := by
  calc
    ∫ ω, gaussianCoordinate i ω ∂gaussianProductMeasure v =
        ∫ y, id y ∂(gaussianProductMeasure v).map (gaussianCoordinate i) :=
      (integral_map (measurable_gaussianCoordinate i).aemeasurable
        aestronglyMeasurable_id).symm
    _ = ∫ y, id y ∂gaussianReal 0 (v i) := by
      rw [(gaussianCoordinate_hasLaw v i).map_eq]
    _ = 0 := integral_id_gaussianReal

lemma gaussianCoordinate_memLp_two (v : ℕ → NNReal) (i : ℕ) :
    MemLp (gaussianCoordinate i) 2 (gaussianProductMeasure v) := by
  exact (gaussianCoordinate_hasLaw v i).hasGaussianLaw.memLp_two

lemma gaussianPartialSum_memLp_two (v : ℕ → NNReal) (n : ℕ) :
    MemLp (gaussianPartialSum n) 2 (gaussianProductMeasure v) := by
  unfold gaussianPartialSum
  convert memLp_finsetSum' (Finset.range (n + 1))
    (fun i hi ↦ gaussianCoordinate_memLp_two v i) using 1
  ext ω
  simp

lemma gaussianPartialSum_stronglyAdapted :
    StronglyAdapted gaussianNaturalFiltration gaussianPartialSum := by
  have hnat : StronglyAdapted gaussianNaturalFiltration gaussianCoordinate := by
    unfold gaussianNaturalFiltration
    exact Filtration.stronglyAdapted_natural
      (u := gaussianCoordinate) (fun i ↦ (measurable_pi_apply i).stronglyMeasurable)
  intro n
  unfold gaussianPartialSum
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  have hXi : StronglyMeasurable[gaussianNaturalFiltration i]
      (gaussianCoordinate i) := hnat i
  exact hXi.mono (gaussianNaturalFiltration.mono
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))

theorem gaussianPartialSum_martingale (v : ℕ → NNReal) :
    Martingale gaussianPartialSum gaussianNaturalFiltration
      (gaussianProductMeasure v) := by
  apply martingale_nat gaussianPartialSum_stronglyAdapted
    (fun n ↦ (gaussianPartialSum_memLp_two v n).integrable one_le_two)
  intro n
  have hcond := (gaussianCoordinate_iIndepFun v).condExp_natural_ae_eq_of_lt
    (fun i ↦ (measurable_pi_apply i).stronglyMeasurable) (Nat.lt_succ_self n)
  change (gaussianProductMeasure v)[gaussianCoordinate (n + 1) |
      gaussianNaturalFiltration n] =ᵐ[gaussianProductMeasure v]
    fun _ ↦ ∫ ω, gaussianCoordinate (n + 1) ω ∂gaussianProductMeasure v at hcond
  rw [integral_gaussianCoordinate v (n + 1)] at hcond
  have hSn : (gaussianProductMeasure v)[gaussianPartialSum n |
      gaussianNaturalFiltration n] =ᵐ[gaussianProductMeasure v] gaussianPartialSum n := by
    rw [condExp_of_stronglyMeasurable (gaussianNaturalFiltration.le n)
      (gaussianPartialSum_stronglyAdapted n)
      ((gaussianPartialSum_memLp_two v n).integrable one_le_two)]
  have hadd : (gaussianProductMeasure v)[gaussianPartialSum (n + 1) |
      gaussianNaturalFiltration n] =ᵐ[gaussianProductMeasure v]
      (gaussianProductMeasure v)[gaussianPartialSum n | gaussianNaturalFiltration n] +
        (gaussianProductMeasure v)[gaussianCoordinate (n + 1) |
          gaussianNaturalFiltration n] := by
    have heq : gaussianPartialSum (n + 1) =
        gaussianPartialSum n + gaussianCoordinate (n + 1) := by
      funext ω
      unfold gaussianPartialSum
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, Finset.sum_range_succ]
      rfl
    rw [heq]
    exact condExp_add
      ((gaussianPartialSum_memLp_two v n).integrable one_le_two)
      ((gaussianCoordinate_memLp_two v (n + 1)).integrable one_le_two)
      (gaussianNaturalFiltration n)
  filter_upwards [hadd, hSn, hcond] with ω ha hs hx
  rw [ha]
  change gaussianPartialSum n ω =
    (gaussianProductMeasure v)[gaussianPartialSum n | gaussianNaturalFiltration n] ω +
      (gaussianProductMeasure v)[gaussianCoordinate (n + 1) |
        gaussianNaturalFiltration n] ω
  rw [hs, hx]
  simp

noncomputable def gaussianVarianceSum (v : ℕ → NNReal) (n : ℕ) : NNReal :=
  ∑ i ∈ Finset.range (n + 1), v i

theorem gaussianPartialSum_hasLaw (v : ℕ → NNReal) (n : ℕ) :
    HasLaw (gaussianPartialSum n) (gaussianReal 0 (gaussianVarianceSum v n))
      (gaussianProductMeasure v) := by
  induction n with
  | zero =>
      constructor
      · exact (gaussianPartialSum_memLp_two v 0).aestronglyMeasurable.aemeasurable
      · rw [show gaussianPartialSum 0 = gaussianCoordinate 0 by
            funext ω
            simp [gaussianPartialSum, gaussianCoordinate]]
        simpa [gaussianVarianceSum] using (gaussianCoordinate_hasLaw v 0).map_eq
  | succ n ih =>
      have hind0 := (gaussianCoordinate_iIndepFun v).indepFun_finsetSum_of_notMem
        (fun i ↦ measurable_gaussianCoordinate i)
        (s := Finset.range (n + 1)) (i := n + 1) (by simp)
      have hind : IndepFun (gaussianPartialSum n) (gaussianCoordinate (n + 1))
          (gaussianProductMeasure v) := by
        convert hind0 using 1
        funext ω
        simp [gaussianPartialSum]
      have hmap := gaussianReal_add_gaussianReal_of_indepFun hind ih.map_eq
        (gaussianCoordinate_hasLaw v (n + 1)).map_eq
      constructor
      · exact (gaussianPartialSum_memLp_two v (n + 1)).aestronglyMeasurable.aemeasurable
      · rw [show gaussianPartialSum (n + 1) =
            gaussianPartialSum n + gaussianCoordinate (n + 1) by
          funext ω
          unfold gaussianPartialSum
          rw [show n + 1 + 1 = (n + 1) + 1 by omega, Finset.sum_range_succ]
          rfl]
        simpa [gaussianVarianceSum, Finset.sum_range_succ] using hmap

theorem integral_sq_gaussianPartialSum (v : ℕ → NNReal) (n : ℕ) :
    ∫ ω, (gaussianPartialSum n ω) ^ 2 ∂gaussianProductMeasure v =
      (gaussianVarianceSum v n : ℝ) := by
  calc
    ∫ ω, (gaussianPartialSum n ω) ^ 2 ∂gaussianProductMeasure v =
        ∫ y, y ^ 2 ∂(gaussianProductMeasure v).map (gaussianPartialSum n) := by
      symm
      exact integral_map (gaussianPartialSum_hasLaw v n).aemeasurable
        (continuous_pow 2).aestronglyMeasurable
    _ = ∫ y, y ^ 2 ∂gaussianReal 0 (gaussianVarianceSum v n) := by
      rw [(gaussianPartialSum_hasLaw v n).map_eq]
    _ = (gaussianVarianceSum v n : ℝ) := by
      have hvar := variance_fun_id_gaussianReal
        (μ := (0 : ℝ)) (v := gaussianVarianceSum v n)
      rw [variance_eq_integral (X := fun x : ℝ ↦ x) measurable_id.aemeasurable,
        integral_id_gaussianReal] at hvar
      simpa using hvar

/-- Complete one-block reset estimate.  A Gaussian `L²` martingale whose
block variance lies in the displayed window has probability at least `1/25`
to return to the narrow central interval while never leaving the radius-`r`
corridor.  This packages the endpoint calculation and Kolmogorov bound into
the uniform constant needed by `pow_le_restrictedChainMass`. -/
theorem one_twentyfifth_le_gaussian_martingale_reset {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ 𝒢]
    {S : ℕ → Ω → ℝ} (hS : Martingale S 𝒢 μ)
    {r x : ℝ} (hr : 0 < r) {v : NNReal} {n : ℕ}
    (hvlow : r ^ 2 / 1600 ≤ (v : ℝ)) (hvup : (v : ℝ) ≤ r ^ 2 / 1000)
    (hx : |x| ≤ r / 100) (hLaw : HasLaw (S n) (gaussianReal x v) μ)
    (h2 : ∀ j, MemLp (fun ω ↦ S j ω - x) 2 μ)
    (hsecond : (∫ ω, (S n ω - x) ^ 2 ∂μ) ≤ r ^ 2 / 100) :
    (1 / 25 : ℝ) ≤ μ.real (
      {ω | S n ω ∈ Icc (-r / 100) (r / 100)} ∩
      {ω | (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ (S k ω - x) ^ 2) < r ^ 2}) := by
  let A : Set Ω := {ω | S n ω ∈ Icc (-r / 100) (r / 100)}
  let B : Set Ω := {ω | (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k ↦ (S k ω - x) ^ 2) < r ^ 2}
  have hD : Martingale (fun j ω ↦ S j ω - x) 𝒢 μ := by
    convert hS.sub (martingale_const 𝒢 μ x) using 1
    funext j ω
    rfl
  have hendpoint : (1 / 20 : ℝ) ≤ μ.real A := by
    rw [show μ.real A = (gaussianReal x v).real (Icc (-r / 100) (r / 100)) by
      exact hLaw.measureReal_eq measurableSet_Icc]
    simpa only [NNReal.mk_coe] using
      (one_twentieth_le_gaussianReal_central hr hvlow hvup hx)
  have hexit : μ.real Bᶜ ≤ (1 / 100 : ℝ) := by
    have he := martingale_exit_measureReal_le_one_hundredth hD h2 hr n hsecond
    simpa only [B, Set.compl_ofPred, not_lt] using he
  exact one_twentyfifth_le_measureReal_inter_of_endpoint_and_exit μ A B hendpoint hexit

/-- Premise-free specialization of the reset estimate to the canonical
inhomogeneous product of centered Gaussian increments. -/
theorem one_twentyfifth_le_gaussianProduct_reset (v : ℕ → NNReal)
    {r x : ℝ} (hr : 0 < r) (n : ℕ)
    (hvlow : r ^ 2 / 1600 ≤ (gaussianVarianceSum v n : ℝ))
    (hvup : (gaussianVarianceSum v n : ℝ) ≤ r ^ 2 / 1000)
    (hx : |x| ≤ r / 100) :
    (1 / 25 : ℝ) ≤ (gaussianProductMeasure v).real (
      {ω | x + gaussianPartialSum n ω ∈ Icc (-r / 100) (r / 100)} ∩
      {ω | (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ (gaussianPartialSum k ω) ^ 2) < r ^ 2}) := by
  let T : ℕ → (ℕ → ℝ) → ℝ := fun j ω ↦ x + gaussianPartialSum j ω
  have hT : Martingale T gaussianNaturalFiltration (gaussianProductMeasure v) := by
    have hc := martingale_const gaussianNaturalFiltration (gaussianProductMeasure v) x
    convert hc.add (gaussianPartialSum_martingale v) using 1
    funext j ω
    rfl
  have hLaw : HasLaw (T n) (gaussianReal x (gaussianVarianceSum v n))
      (gaussianProductMeasure v) := by
    simpa [T] using gaussianReal_const_add (gaussianPartialSum_hasLaw v n) x
  have h2 : ∀ j, MemLp (fun ω ↦ T j ω - x) 2 (gaussianProductMeasure v) := by
    intro j
    convert gaussianPartialSum_memLp_two v j using 1
    funext ω
    simp [T]
  have hsecond : (∫ ω, (T n ω - x) ^ 2 ∂gaussianProductMeasure v) ≤
      r ^ 2 / 100 := by
    rw [show (fun ω ↦ (T n ω - x) ^ 2) =
        fun ω ↦ (gaussianPartialSum n ω) ^ 2 by
      funext ω
      simp [T], integral_sq_gaussianPartialSum]
    nlinarith [sq_nonneg r]
  simpa [T] using one_twentyfifth_le_gaussian_martingale_reset
    hT hr hvlow hvup hx hLaw h2 hsecond

/-! ### Residual blocks

The greedy variance partition used below can end with a block of arbitrarily
small positive variance.  A lower variance cutoff is therefore inconvenient.
Gaussian symmetry and Chebyshev's inequality give a uniform inward-half
estimate which only needs an upper variance bound. -/

lemma gaussianReal_zero_half_symm (v : NNReal) {a : ℝ} (_ha : 0 ≤ a) :
    (gaussianReal 0 v).real (Icc (-a) 0) =
      (gaussianReal 0 v).real (Icc 0 a) := by
  rw [measureReal_def, measureReal_def]
  apply congrArg ENNReal.toReal
  have hmap := gaussianReal_map_neg (μ := (0 : ℝ)) (v := v)
  have hs : MeasurableSet (Icc (-a) 0) := measurableSet_Icc
  have happ := congrArg (fun ν : Measure ℝ ↦ ν (Icc (-a) 0)) hmap
  rw [Measure.map_apply (by fun_prop) hs] at happ
  have hpre : (fun x : ℝ ↦ -x) ⁻¹' Icc (-a) 0 = Icc 0 a := by
    ext z
    simp [and_comm]
  rw [hpre] at happ
  simpa using happ.symm

lemma gaussianReal_zero_abs_ge_le_quarter (v : NNReal) {a : ℝ} (ha : 0 < a)
    (hv : (v : ℝ) ≤ a ^ 2 / 4) :
    (gaussianReal 0 v).real {y | a ≤ |y|} ≤ 1 / 4 := by
  let μ : Measure ℝ := gaussianReal 0 v
  have hmem : MemLp (fun y : ℝ ↦ y) 2 μ := IsGaussian.memLp_two_id
  have h := meas_ge_le_variance_div_sq hmem ha
  rw [integral_id_gaussianReal, variance_fun_id_gaussianReal] at h
  have hbound : ENNReal.ofReal ((v : ℝ) / a ^ 2) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
    apply ENNReal.ofReal_le_ofReal
    have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
    apply (div_le_iff₀ ha2).2
    nlinarith
  have hh := h.trans hbound
  have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal (1 / 4 : ℝ) ≠ ⊤) hh
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hreal
  change (gaussianReal 0 v).real {y | a ≤ |y|} ≤ 1 / 4
  rw [measureReal_def]
  simpa [μ] using hreal

lemma three_eighths_le_gaussianReal_zero_half (v : NNReal) {a : ℝ} (ha : 0 < a)
    (hv : (v : ℝ) ≤ a ^ 2 / 4) :
    (3 / 8 : ℝ) ≤ (gaussianReal 0 v).real (Icc (-a) 0) := by
  let μ : Measure ℝ := gaussianReal 0 v
  have htail := gaussianReal_zero_abs_ge_le_quarter v ha hv
  have hcover : (Set.univ : Set ℝ) ⊆ Icc (-a) a ∪ {y | a ≤ |y|} := by
    intro y _hy
    by_cases h : |y| ≤ a
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr (le_of_not_ge h)
  have hmass : (1 : ℝ) ≤ μ.real (Icc (-a) a) + μ.real {y | a ≤ |y|} := by
    calc
      (1 : ℝ) = μ.real Set.univ := by simp [μ]
      _ ≤ μ.real (Icc (-a) a ∪ {y | a ≤ |y|}) := measureReal_mono hcover
      _ ≤ μ.real (Icc (-a) a) + μ.real {y | a ≤ |y|} := measureReal_union_le _ _
  have hcentral : (3 / 4 : ℝ) ≤ μ.real (Icc (-a) a) := by
    change (gaussianReal 0 v).real {y | a ≤ |y|} ≤ 1 / 4 at htail
    linarith
  have hsplit : μ.real (Icc (-a) a) ≤
      μ.real (Icc (-a) 0) + μ.real (Icc 0 a) := by
    have hsub : Icc (-a) a ⊆ Icc (-a) 0 ∪ Icc 0 a := by
      intro y hy
      by_cases h : y ≤ 0
      · exact Or.inl ⟨hy.1, h⟩
      · exact Or.inr ⟨le_of_not_ge h, hy.2⟩
    exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hsymm := gaussianReal_zero_half_symm v ha.le
  have hsplit' : (gaussianReal 0 v).real (Icc (-a) a) ≤
      (gaussianReal 0 v).real (Icc (-a) 0) +
        (gaussianReal 0 v).real (Icc 0 a) := by simpa [μ] using hsplit
  have hcentral' : (3 / 4 : ℝ) ≤ (gaussianReal 0 v).real (Icc (-a) a) := by
    simpa [μ] using hcentral
  rw [hsymm] at hsplit'
  linarith

lemma three_eighths_le_gaussianReal_central_of_variance_le {r x : ℝ}
    (hr : 0 < r) (v : NNReal) (hv : (v : ℝ) ≤ r ^ 2 / 40000)
    (hx : |x| ≤ r / 100) :
    (3 / 8 : ℝ) ≤ (gaussianReal x v).real (Icc (-r / 100) (r / 100)) := by
  let a : ℝ := r / 100
  have ha : 0 < a := div_pos hr (by norm_num)
  have hv' : (v : ℝ) ≤ a ^ 2 / 4 := by
    dsimp [a]
    nlinarith
  have hneg := three_eighths_le_gaussianReal_zero_half v ha hv'
  have hsymm := gaussianReal_zero_half_symm v ha.le
  have hpos : (3 / 8 : ℝ) ≤ (gaussianReal 0 v).real (Icc 0 a) := by
    rw [← hsymm]
    exact hneg
  have hmap := gaussianReal_map_const_add (μ := (0 : ℝ)) (v := v) x
  have ht : MeasurableSet (Icc (-a) a) := measurableSet_Icc
  have happ := congrArg (fun ν : Measure ℝ ↦ ν (Icc (-a) a)) hmap
  rw [Measure.map_apply (by fun_prop) ht] at happ
  have hmeasure : (gaussianReal x v).real (Icc (-a) a) =
      (gaussianReal 0 v).real ((fun y : ℝ ↦ x + y) ⁻¹' Icc (-a) a) := by
    rw [measureReal_def, measureReal_def]
    simpa using congrArg ENNReal.toReal happ.symm
  have hfinal : (3 / 8 : ℝ) ≤ (gaussianReal x v).real (Icc (-a) a) := by
    rw [hmeasure]
    rw [abs_le] at hx
    have hxa : -a ≤ x ∧ x ≤ a := by simpa [a, neg_div] using hx
    by_cases hx0 : 0 ≤ x
    · exact hneg.trans (measureReal_mono (by
        intro y hy
        change -a ≤ x + y ∧ x + y ≤ a
        constructor <;> linarith [hy.1, hy.2, hxa.1, hxa.2]))
    · exact hpos.trans (measureReal_mono (by
        intro y hy
        change -a ≤ x + y ∧ x + y ≤ a
        constructor <;> linarith [hy.1, hy.2, hxa.1, hxa.2]))
  simpa [a, neg_div] using hfinal

theorem one_third_le_measureReal_inter_of_endpoint_and_exit {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (A B : Set Ω)
    (hendpoint : (3 / 8 : ℝ) ≤ μ.real A)
    (hexit : μ.real Bᶜ ≤ 1 / 100) :
    (1 / 3 : ℝ) ≤ μ.real (A ∩ B) := by
  have h := measureReal_sub_compl_le_inter μ A B
  linarith

/-- Premise-free reset estimate for every block whose total variance is at
most `r²/40000`.  Unlike the earlier windowed version, this includes the
possibly tiny residual block of a greedy partition. -/
theorem one_third_le_gaussianProduct_reset_of_variance_le (v : ℕ → NNReal)
    {r x : ℝ} (hr : 0 < r) (n : ℕ)
    (hvup : (gaussianVarianceSum v n : ℝ) ≤ r ^ 2 / 40000)
    (hx : |x| ≤ r / 100) :
    (1 / 3 : ℝ) ≤ (gaussianProductMeasure v).real (
      {ω | x + gaussianPartialSum n ω ∈ Icc (-r / 100) (r / 100)} ∩
      {ω | (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ (gaussianPartialSum k ω) ^ 2) < r ^ 2}) := by
  let A : Set (ℕ → ℝ) :=
    {ω | x + gaussianPartialSum n ω ∈ Icc (-r / 100) (r / 100)}
  let B : Set (ℕ → ℝ) :=
    {ω | (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k ↦ (gaussianPartialSum k ω) ^ 2) < r ^ 2}
  have hendpoint : (3 / 8 : ℝ) ≤ (gaussianProductMeasure v).real A := by
    have hLaw : HasLaw (fun ω ↦ x + gaussianPartialSum n ω)
        (gaussianReal x (gaussianVarianceSum v n)) (gaussianProductMeasure v) := by
      simpa using gaussianReal_const_add (gaussianPartialSum_hasLaw v n) x
    rw [show (gaussianProductMeasure v).real A =
        (gaussianReal x (gaussianVarianceSum v n)).real
          (Icc (-r / 100) (r / 100)) by
      exact hLaw.measureReal_eq measurableSet_Icc]
    exact three_eighths_le_gaussianReal_central_of_variance_le hr _ hvup hx
  have hexit : (gaussianProductMeasure v).real Bᶜ ≤ (1 / 100 : ℝ) := by
    have he := martingale_exit_measureReal_le_one_hundredth
      (gaussianPartialSum_martingale v) (gaussianPartialSum_memLp_two v) hr n
      (by
        rw [integral_sq_gaussianPartialSum]
        nlinarith [sq_nonneg r])
    simpa only [B, Set.compl_ofPred, not_lt] using he
  exact one_third_le_measureReal_inter_of_endpoint_and_exit
    (gaussianProductMeasure v) A B hendpoint hexit

/-! ### Large individual increments

An individual variance can exceed the small-block budget.  The next direct
density estimate charges such an increment by `exp (-C * v / r²)`.  Hence
large increments contribute their variance, rather than their count, to the
final exponent. -/

lemma gaussianDensity_large_variance_pointwise {r v x y : ℝ}
    (hr : 0 < r) (hvlow : r ^ 2 / 40000 ≤ v)
    (hx : |x| ≤ r / 100) (hy : |y| ≤ r / 100) :
    (4 * Real.sqrt v)⁻¹ * Real.exp (-8) ≤ gaussianDensity v x y := by
  have hv : 0 < v := lt_of_lt_of_le (div_pos (sq_pos_of_pos hr) (by norm_num)) hvlow
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hsqrtv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hnorm : Real.sqrt (2 * Real.pi * v) ≤ 4 * Real.sqrt v := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hs : (4 * Real.sqrt v) ^ 2 = 16 * v := by
        rw [mul_pow, Real.sq_sqrt hv.le]
        norm_num
      rw [hs]
      nlinarith
  have hinv : (4 * Real.sqrt v)⁻¹ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hnorm
  have hdist : (y - x) ^ 2 / (2 * v) ≤ 8 := by
    have hxy : |y - x| ≤ r / 50 := by
      calc
        |y - x| ≤ |y| + |x| := abs_sub _ _
        _ ≤ r / 100 + r / 100 := add_le_add hy hx
        _ = r / 50 := by ring
    have hsabs0 := mul_le_mul hxy hxy (abs_nonneg (y - x)) (by positivity : 0 ≤ r / 50)
    have hsabs : |y - x| ^ 2 ≤ (r / 50) ^ 2 := by simpa [pow_two] using hsabs0
    have hs : (y - x) ^ 2 ≤ (r / 50) ^ 2 := by simpa [sq_abs] using hsabs
    have hden : 0 < 2 * v := by positivity
    apply (div_le_iff₀ hden).2
    nlinarith
  unfold gaussianDensity
  exact mul_le_mul hinv (Real.exp_le_exp.mpr (by linarith))
    (Real.exp_pos _).le (by positivity)

lemma large_variance_prefactor_le_integral_gaussianDensity {r v x : ℝ}
    (hr : 0 < r) (hvlow : r ^ 2 / 40000 ≤ v)
    (hx : |x| ≤ r / 100) :
    r / (200 * Real.sqrt v) * Real.exp (-8) ≤
      ∫ y in Icc (-r / 100) (r / 100), gaussianDensity v x y := by
  have hv : 0 < v := lt_of_lt_of_le (div_pos (sq_pos_of_pos hr) (by norm_num)) hvlow
  have hconst : IntegrableOn (fun _y : ℝ ↦
      (4 * Real.sqrt v)⁻¹ * Real.exp (-8)) (Icc (-r / 100) (r / 100)) :=
    continuous_const.integrableOn_Icc
  have hdensity : IntegrableOn (gaussianDensity v x) (Icc (-r / 100) (r / 100)) :=
    gaussianDensity_continuous.integrableOn_Icc
  have hmono := setIntegral_mono_on hconst hdensity measurableSet_Icc
    (fun y hy ↦ gaussianDensity_large_variance_pointwise hr hvlow hx (by
      rw [mem_Icc] at hy
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]))
  have hmeasure : volume.real (Icc (-r / 100) (r / 100)) = r / 50 := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
    · ring
    · linarith
  rw [setIntegral_const, hmeasure, smul_eq_mul] at hmono
  calc
    r / (200 * Real.sqrt v) * Real.exp (-8) =
        r / 50 * ((4 * Real.sqrt v)⁻¹ * Real.exp (-8)) := by ring
    _ ≤ _ := hmono

lemma large_variance_prefactor_le_gaussianReal_central {r v x : ℝ}
    (hr : 0 < r) (hvlow : r ^ 2 / 40000 ≤ v)
    (hx : |x| ≤ r / 100) :
    r / (200 * Real.sqrt v) * Real.exp (-8) ≤
      (gaussianReal x (NNReal.mk v (le_trans (by positivity) hvlow))).real
        (Icc (-r / 100) (r / 100)) := by
  have hv : 0 < v := lt_of_lt_of_le (div_pos (sq_pos_of_pos hr) (by norm_num)) hvlow
  let vn : NNReal := NNReal.mk v hv.le
  have hvn : vn ≠ 0 := by
    intro h
    apply hv.ne'
    have hc := congrArg (fun z : NNReal ↦ (z : ℝ)) h
    change v = 0 at hc
    exact hc
  have hmeasure := gaussianReal_apply_eq_integral x (v := vn) hvn
    (Icc (-r / 100) (r / 100))
  rw [measureReal_def]
  rw [hmeasure, ENNReal.toReal_ofReal]
  · rw [← gaussianDensity_eq_gaussianPDFReal hv.le]
    exact large_variance_prefactor_le_integral_gaussianDensity hr hvlow hx
  · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y ↦
      gaussianPDFReal_nonneg x vn y)

lemma exp_eight_ge_two_hundred : (200 : ℝ) ≤ Real.exp 8 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  calc
    (200 : ℝ) ≤ 2 ^ (8 : ℕ) := by norm_num
    _ ≤ (Real.exp 1) ^ (8 : ℕ) := pow_le_pow_left₀ (by norm_num) htwo 8
    _ = Real.exp 8 := by
      rw [← Real.exp_nat_mul]
      norm_num

lemma exp_large_variance_cost_le_prefactor {r v : ℝ}
    (hr : 0 < r) (hvlow : r ^ 2 / 40000 ≤ v) :
    Real.exp (-660000 * (v / r ^ 2)) ≤
      r / (200 * Real.sqrt v) * Real.exp (-8) := by
  have hv : 0 < v := lt_of_lt_of_le (div_pos (sq_pos_of_pos hr) (by norm_num)) hvlow
  let u : ℝ := v / r ^ 2
  have hu : 0 < u := div_pos hv (sq_pos_of_pos hr)
  have hulow : (1 / 40000 : ℝ) ≤ u := by
    dsimp [u]
    apply (le_div_iff₀ (sq_pos_of_pos hr)).2
    simpa [div_eq_mul_inv, mul_comm] using hvlow
  have hsqrtlinear : Real.sqrt v ≤ r * (20000 * u) := by
    have hrv : r ^ 2 ≤ 40000 * v := by nlinarith
    have hsq : v ≤ (r * (20000 * u)) ^ 2 := by
      dsimp [u]
      field_simp [hr.ne']
      nlinarith [mul_nonneg hv.le (sub_nonneg.mpr hrv)]
    exact (Real.sqrt_le_iff).2
      ⟨by positivity, by simpa [Real.sq_sqrt hv.le] using hsq⟩
  have hselfexp : 20000 * u ≤ Real.exp (20000 * u) := by
    calc
      20000 * u ≤ 20000 * u + 1 := by linarith
      _ ≤ Real.exp (20000 * u) := Real.add_one_le_exp _
  have hsqrtExp : Real.sqrt v ≤ r * Real.exp (20000 * u) :=
    hsqrtlinear.trans (mul_le_mul_of_nonneg_left hselfexp hr.le)
  have hden : 200 * Real.sqrt v * Real.exp 8 ≤
      r * Real.exp (16 + 20000 * u) := by
    calc
      200 * Real.sqrt v * Real.exp 8 ≤
          Real.exp 8 * (r * Real.exp (20000 * u)) * Real.exp 8 := by
        gcongr
        exact exp_eight_ge_two_hundred
      _ = r * (Real.exp 8 * Real.exp (20000 * u) * Real.exp 8) := by ring
      _ = r * Real.exp (8 + 20000 * u + 8) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ = r * Real.exp (16 + 20000 * u) := by
        congr 2
        ring
  have hexponent : 16 + 20000 * u ≤ 660000 * u := by nlinarith
  have hden' : 200 * Real.sqrt v * Real.exp 8 ≤
      r * Real.exp (660000 * u) :=
    hden.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hr.le)
  have hbase : 200 * Real.sqrt v ≤
      r * Real.exp (660000 * u) * Real.exp (-8) := by
    have hh : 200 * Real.sqrt v ≤
        (r * Real.exp (660000 * u)) / Real.exp 8 :=
      (le_div_iff₀ (Real.exp_pos 8)).2 (by simpa only [mul_assoc] using hden')
    rw [div_eq_mul_inv, ← Real.exp_neg] at hh
    exact hh
  rw [show r / (200 * Real.sqrt v) * Real.exp (-8) =
      (r * Real.exp (-8)) * (200 * Real.sqrt v)⁻¹ by ring]
  apply (le_mul_inv_iff₀ (by positivity : 0 < 200 * Real.sqrt v)).2
  calc
    Real.exp (-660000 * (v / r ^ 2)) * (200 * Real.sqrt v) =
        Real.exp (-660000 * u) * (200 * Real.sqrt v) := by rfl
    _ ≤ Real.exp (-660000 * u) *
        (r * Real.exp (660000 * u) * Real.exp (-8)) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    _ = r * (Real.exp (-660000 * u) * Real.exp (660000 * u)) *
        Real.exp (-8) := by ring
    _ = r * Real.exp (-8) := by
      rw [← Real.exp_add]
      simp

theorem exp_large_variance_cost_le_gaussianReal_central {r v x : ℝ}
    (hr : 0 < r) (hvlow : r ^ 2 / 40000 ≤ v)
    (hx : |x| ≤ r / 100) :
    Real.exp (-660000 * (v / r ^ 2)) ≤
      (gaussianReal x (NNReal.mk v (le_trans (by positivity) hvlow))).real
        (Icc (-r / 100) (r / 100)) :=
  (exp_large_variance_cost_le_prefactor hr hvlow).trans
    (large_variance_prefactor_le_gaussianReal_central hr hvlow hx)

/-! ### Safe block transition measures

These measures retain both pieces of information needed for composition:
the block endpoint and the event that every intermediate partial sum remains
inside the wide corridor. -/

def gaussianBlockSafeEvent (n : ℕ) (r : ℝ) : Set (ℕ → ℝ) :=
  {ω | (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k ↦ (gaussianPartialSum k ω) ^ 2) < r ^ 2}

@[fun_prop] lemma measurable_gaussianPartialSum (n : ℕ) :
    Measurable (gaussianPartialSum n) := by
  unfold gaussianPartialSum
  fun_prop

lemma measurableSet_gaussianBlockSafeEvent (n : ℕ) (r : ℝ) :
    MeasurableSet (gaussianBlockSafeEvent n r) := by
  unfold gaussianBlockSafeEvent
  exact measurableSet_lt
    (Finset.measurable_range_sup'' fun k _hk ↦ (measurable_gaussianPartialSum k).pow_const 2)
    measurable_const

noncomputable def gaussianSafeBlockMeasure (v : ℕ → NNReal)
    (n : ℕ) (r x : ℝ) : Measure ℝ :=
  ((gaussianProductMeasure v).restrict (gaussianBlockSafeEvent n r)).map
    (fun ω ↦ x + gaussianPartialSum n ω)

lemma gaussianSafeBlockMeasure_apply_central (v : ℕ → NNReal)
    (n : ℕ) {r x : ℝ} :
    gaussianSafeBlockMeasure v n r x (Icc (-r / 100) (r / 100)) =
      (gaussianProductMeasure v) (
        {ω | x + gaussianPartialSum n ω ∈ Icc (-r / 100) (r / 100)} ∩
          gaussianBlockSafeEvent n r) := by
  unfold gaussianSafeBlockMeasure
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc]
  have hpre : MeasurableSet
      ((fun ω ↦ x + gaussianPartialSum n ω) ⁻¹' Icc (-r / 100) (r / 100)) :=
    (measurable_const.add (measurable_gaussianPartialSum n)) measurableSet_Icc
  rw [Measure.restrict_apply hpre]
  congr 1

/-- ENNReal row-mass form of the residual-block reset theorem, directly
usable by `pow_le_restrictedMeasureChainMass`. -/
theorem one_third_le_gaussianSafeBlockMeasure_central (v : ℕ → NNReal)
    {r x : ℝ} (hr : 0 < r) (n : ℕ)
    (hvup : (gaussianVarianceSum v n : ℝ) ≤ r ^ 2 / 40000)
    (hx : |x| ≤ r / 100) :
    (1 / 3 : ℝ≥0∞) ≤
      gaussianSafeBlockMeasure v n r x (Icc (-r / 100) (r / 100)) := by
  rw [gaussianSafeBlockMeasure_apply_central]
  have h := one_third_le_gaussianProduct_reset_of_variance_le v hr n hvup hx
  have hh := ENNReal.ofReal_le_ofReal h
  rw [measureReal_def] at hh
  rw [ENNReal.ofReal_toReal (measure_ne_top (gaussianProductMeasure v) _)] at hh
  simpa [gaussianBlockSafeEvent] using hh

/-! ### Increment-cell comparison

Rounding increments (rather than cumulative positions) keeps the Gaussian
product measure factorized.  The accumulated rounding error is deterministic,
and each coordinate pays the following explicit density cost. -/

noncomputable def hlozIncrementVariance (ℓ : ℕ) : NNReal :=
  ⟨4 * (ℓ : ℝ) ^ 2, by positivity⟩

/-- The total variance of the `N` HLOZ Gaussian increments starting at scale
`m` is bounded by the length times the largest variance. -/
lemma gaussianVarianceSum_hloz_le {m N : ℕ} (hN : 0 < N) :
    ((gaussianVarianceSum (fun i ↦ hlozIncrementVariance (m + i)) (N - 1) : NNReal) : ℝ) ≤
      4 * (N : ℝ) * ((m + N : ℕ) : ℝ) ^ 2 := by
  rw [gaussianVarianceSum, Nat.sub_add_cancel hN,
    NNReal.coe_sum (Finset.range N)]
  simp only [hlozIncrementVariance, NNReal.coe_mk]
  calc
    ∑ i ∈ Finset.range N, 4 * ((m + i : ℕ) : ℝ) ^ 2 ≤
        ∑ _i ∈ Finset.range N, 4 * ((m + N : ℕ) : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i ≤ N := (Finset.mem_range.1 hi).le
      have hcast : ((m + i : ℕ) : ℝ) ≤ (m + N : ℕ) := by
        exact_mod_cast Nat.add_le_add_left hiN m
      nlinarith [sq_nonneg (((m + N : ℕ) : ℝ) - (m + i : ℕ))]
    _ = 4 * (N : ℝ) * ((m + N : ℕ) : ℝ) ^ 2 := by
      simp [Nat.cast_add]
      ring

/-- Source-scale form of the preceding estimate.  This is the explicit
`O(n^3)` total-variance input in the exponent of HLOZ Lemma A.8. -/
lemma gaussianVarianceSum_hloz_le_four_cube {m N n : ℕ} (hN : 0 < N)
    (hupper : m + N ≤ n) :
    ((gaussianVarianceSum (fun i ↦ hlozIncrementVariance (m + i)) (N - 1) : NNReal) : ℝ) ≤
      4 * (n : ℝ) ^ 3 := by
  calc
    _ ≤ 4 * (N : ℝ) * ((m + N : ℕ) : ℝ) ^ 2 :=
      gaussianVarianceSum_hloz_le hN
    _ ≤ 4 * (n : ℝ) * (n : ℝ) ^ 2 := by
      have hNr : (N : ℝ) ≤ n := by
        exact_mod_cast (Nat.le_trans (Nat.le_add_left N m) hupper)
      have hsum : ((m + N : ℕ) : ℝ) ≤ n := by exact_mod_cast hupper
      gcongr
    _ = 4 * (n : ℝ) ^ 3 := by ring

/-! ### Rectangular block products and the chronological increment sequence

The next equivalence sends the first `L` coordinates of block `i` to the
chronological indices `i * L, …, i * L + L - 1`.  Its action on the unused
tails makes it a genuine equivalence with `ℕ`; those tails carry variance
zero below. -/

noncomputable def blockIndexEquiv (q L : ℕ) [NeZero q] : Fin q × ℕ ≃ ℕ :=
  (Equiv.prodCongr (Equiv.refl (Fin q)) (finSumNatEquiv L).symm).trans <|
    (Equiv.prodSumDistrib (Fin q) (Fin L) ℕ).trans <|
      (Equiv.sumCongr finProdFinEquiv
        ((Equiv.prodComm (Fin q) ℕ).trans (Nat.divModEquiv q).symm)).trans <|
        finSumNatEquiv (q * L)

@[simp] lemma blockIndexEquiv_apply_lt (q L : ℕ) [NeZero q]
    (i : Fin q) {j : ℕ} (hj : j < L) :
    blockIndexEquiv q L (i, j) = j + L * i := by
  simp [blockIndexEquiv, finSumNatEquiv_symm_apply_of_lt hj,
    finProdFinEquiv]

/-- The HLOZ variance sequence stopped after its first `N` increments. -/
noncomputable def paddedHlozVariance (m N : ℕ) (i : ℕ) : NNReal :=
  if i < N then hlozIncrementVariance (m + i) else 0

/-- The stopped sequence regrouped into `q` chronological blocks of length
`L`.  Coordinates after `L` in a block necessarily belong to the zero
variance tail when `N ≤ qL`. -/
noncomputable def hlozBlockVariance (m N q L : ℕ) [NeZero q]
    (i : Fin q) (j : ℕ) : NNReal :=
  paddedHlozVariance m N (blockIndexEquiv q L (i, j))

noncomputable def blockMergeEquiv (q L : ℕ) [NeZero q] :
    (Fin q → ℕ → ℝ) ≃ᵐ (ℕ → ℝ) :=
  (MeasurableEquiv.curry (Fin q) ℕ ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : ℕ ↦ ℝ) (blockIndexEquiv q L))

/-- Regrouping the independent Gaussian increments by chronological blocks
preserves their joint law.  This is the exact distributional bridge between
block iteration and the one-sequence lattice transfer. -/
lemma map_pi_gaussianBlocks_blockMerge (m N q L : ℕ) [NeZero q] :
    (Measure.pi fun i : Fin q ↦
      gaussianProductMeasure (hlozBlockVariance m N q L i)).map
        (blockMergeEquiv q L) =
      gaussianProductMeasure (paddedHlozVariance m N) := by
  rw [← Measure.infinitePi_eq_pi]
  unfold blockMergeEquiv gaussianProductMeasure gaussianIncrementMeasure hlozBlockVariance
  simp only [MeasurableEquiv.coe_trans]
  rw [← Measure.map_map]
  · rw [Measure.infinitePi_map_curry_symm]
    exact Measure.infinitePi_map_piCongrLeft
      (fun k ↦ gaussianReal 0 (paddedHlozVariance m N k)) (blockIndexEquiv q L)
  all_goals fun_prop

/-- Every fixed chronological block has variance at most its length times
the largest HLOZ increment variance before the upper scale `n`.  Padding
past `N` only replaces increments by variance-zero Gaussians. -/
lemma gaussianVarianceSum_hlozBlock_le {m N n q L : ℕ} [NeZero q]
    (hL : 0 < L) (hupper : m + N ≤ n) (i : Fin q) :
    ((gaussianVarianceSum (hlozBlockVariance m N q L i) (L - 1) : NNReal) : ℝ) ≤
      4 * (L : ℝ) * (n : ℝ) ^ 2 := by
  rw [gaussianVarianceSum, Nat.sub_add_cancel hL,
    NNReal.coe_sum (Finset.range L)]
  calc
    ∑ j ∈ Finset.range L, ((hlozBlockVariance m N q L i j : NNReal) : ℝ) ≤
        ∑ _j ∈ Finset.range L, 4 * (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjL : j < L := Finset.mem_range.1 hj
      rw [hlozBlockVariance, blockIndexEquiv_apply_lt q L i hjL]
      unfold paddedHlozVariance
      split_ifs with hk
      · change 4 * ((m + (j + L * (i : ℕ)) : ℕ) : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2
        have hscale : m + (j + L * (i : ℕ)) ≤ n := by
          exact (Nat.add_le_add_left hk.le m).trans hupper
        have hscaleR : ((m + (j + L * (i : ℕ)) : ℕ) : ℝ) ≤ n := by
          exact_mod_cast hscale
        nlinarith [sq_nonneg ((n : ℝ) - (m + (j + L * (i : ℕ)) : ℕ))]
      · simp
    _ = 4 * (L : ℝ) * (n : ℝ) ^ 2 := by simp; ring

noncomputable def hlozBlockGood (L : ℕ) (r : ℝ) (_i : ℕ) (_x : ℝ) :
    Set (ℕ → ℝ) := gaussianBlockSafeEvent (L - 1) r

def hlozBlockStep (L : ℕ) (_i : ℕ) (x : ℝ) (ω : ℕ → ℝ) : ℝ :=
  x + gaussianPartialSum (L - 1) ω

def gaussianCentralSet (r : ℝ) : Set ℝ := Set.Icc (-r / 100) (r / 100)

lemma measurableSet_hlozBlockGood_joint (L : ℕ) (r : ℝ) (i : ℕ) :
    MeasurableSet {z : ℝ × (ℕ → ℝ) | z.2 ∈ hlozBlockGood L r i z.1} := by
  exact measurable_snd (measurableSet_gaussianBlockSafeEvent (L - 1) r)

lemma measurable_hlozBlockStep_joint (L : ℕ) (i : ℕ) :
    Measurable fun z : ℝ × (ℕ → ℝ) ↦ hlozBlockStep L i z.1 z.2 := by
  exact measurable_fst.add ((measurable_gaussianPartialSum (L - 1)).comp measurable_snd)

/-- The full retained-sample block event has mass at least `(1/3)^q`.
Together with `map_pi_gaussianBlocks_blockMerge`, this is the quantitative
block-composition core of the Brownian small-ball estimate: it controls
exponentially many paths, not merely the zero path. -/
theorem one_third_pow_le_hlozBlockChain
    {m N n q L : ℕ} [NeZero q] {r : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hupper : m + N ≤ n)
    (hbudget : 4 * (L : ℝ) * (n : ℝ) ^ 2 ≤ r ^ 2 / 40000) :
    (1 / 3 : ℝ≥0∞) ^ q ≤
      (Measure.pi fun i : Fin q ↦
        gaussianProductMeasure (hlozBlockVariance m N q L i))
        (sampledChainGood (gaussianCentralSet r) (hlozBlockGood L r)
          (hlozBlockStep L) q 0) := by
  let μ : ℕ → Measure (ℕ → ℝ) := fun i ↦
    gaussianProductMeasure (hlozBlockVariance m N q L (Fin.ofNat q i))
  have hchain := pow_le_measure_sampledChainGood
    (gaussianCentralSet r) μ (hlozBlockGood L r) (hlozBlockStep L)
    (c := (1 / 3 : ℝ≥0∞)) (q := q)
  have h := hchain (x := 0) ?_ ?_ ?_ ?_
  simpa [μ] using h
  · intro k s x
    exact measurableSet_sampledChainGood (gaussianCentralSet r) measurableSet_Icc
      (hlozBlockGood L r) (hlozBlockStep L)
      (measurableSet_hlozBlockGood_joint L r)
      (measurable_hlozBlockStep_joint L) k s x
  · intro i x
    exact (measurableSet_gaussianBlockSafeEvent (L - 1) r).inter
      ((measurable_const.add (measurable_gaussianPartialSum (L - 1))) measurableSet_Icc)
  · intro i hi x hx
    have hv : ((gaussianVarianceSum
        (hlozBlockVariance m N q L (Fin.ofNat q i)) (L - 1) : NNReal) : ℝ) ≤
        r ^ 2 / 40000 :=
      (gaussianVarianceSum_hlozBlock_le hL hupper (Fin.ofNat q i)).trans hbudget
    have hreset := one_third_le_gaussianSafeBlockMeasure_central
      (hlozBlockVariance m N q L (Fin.ofNat q i)) (x := x) hr (L - 1) hv (by
        rw [gaussianCentralSet, Set.mem_Icc] at hx
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2])
    rw [gaussianSafeBlockMeasure_apply_central] at hreset
    simpa [μ, hlozBlockGood, hlozBlockStep, gaussianCentralSet, Set.inter_comm] using hreset
  · simp only [gaussianCentralSet, Set.mem_Icc]
    constructor <;> linarith

/-! A recursive view of the chronological block merge.  It is convenient
for deterministic corridor estimates because it exposes the first block and
the remaining tail in exactly the same shape as `sampledChainGood`. -/

def recursiveBlockFlatten (L : ℕ) : (q : ℕ) → (Fin q → ℕ → ℝ) → ℕ → ℝ
  | 0, _ => fun _ ↦ 0
  | q + 1, ω => fun k ↦
      if k < L then ω 0 k else recursiveBlockFlatten L q (Fin.tail ω) (k - L)

lemma blockMergeEquiv_apply (q L : ℕ) [NeZero q]
    (ω : Fin q → ℕ → ℝ) (k : ℕ) :
    blockMergeEquiv q L ω k =
      ω ((blockIndexEquiv q L).symm k).1 ((blockIndexEquiv q L).symm k).2 := by
  simp [blockMergeEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.curry, Function.uncurry]

lemma blockIndexEquiv_mul_le_apply_of_le (q L : ℕ) [NeZero q]
    (i : Fin q) {j : ℕ} (hj : L ≤ j) :
    q * L ≤ blockIndexEquiv q L (i, j) := by
  simp [blockIndexEquiv, finSumNatEquiv_symm_apply_of_ge hj]

lemma blockMergeEquiv_apply_first {q L : ℕ} [NeZero (q + 1)]
    (ω : Fin (q + 1) → ℕ → ℝ) {k : ℕ} (hk : k < L) :
    blockMergeEquiv (q + 1) L ω k = ω 0 k := by
  rw [blockMergeEquiv_apply]
  let j : Fin L := ⟨k, hk⟩
  have he : blockIndexEquiv (q + 1) L ((0 : Fin (q + 1)), (j : ℕ)) = k := by
    simpa [j] using blockIndexEquiv_apply_lt (q + 1) L (0 : Fin (q + 1)) hk
  have hinv : (blockIndexEquiv (q + 1) L).symm k =
      ((0 : Fin (q + 1)), (j : ℕ)) := by
    apply (blockIndexEquiv (q + 1) L).injective
    simp [he]
  rw [hinv]

lemma blockMergeEquiv_apply_tail {q L : ℕ} [NeZero q] [NeZero (q + 1)]
    (ω : Fin (q + 1) → ℕ → ℝ) {k : ℕ}
    (hkL : L ≤ k) (hk : k < (q + 1) * L) :
    blockMergeEquiv (q + 1) L ω k =
      blockMergeEquiv q L (Fin.tail ω) (k - L) := by
  rw [blockMergeEquiv_apply, blockMergeEquiv_apply]
  let p : Fin q × ℕ := (blockIndexEquiv q L).symm (k - L)
  have hpj : p.2 < L := by
    by_contra h
    have hge : L ≤ p.2 := Nat.le_of_not_gt h
    have hbound := blockIndexEquiv_mul_le_apply_of_le q L p.1 hge
    have hp := (blockIndexEquiv q L).apply_symm_apply (k - L)
    change blockIndexEquiv q L p = k - L at hp
    rw [hp] at hbound
    have hkl : k - L < q * L := by
      simp only [Nat.add_mul, one_mul] at hk
      omega
    omega
  let ps : Fin (q + 1) := p.1.succ
  have he : blockIndexEquiv (q + 1) L (ps, p.2) = k := by
    rw [blockIndexEquiv_apply_lt (q + 1) L ps hpj]
    have hp := (blockIndexEquiv q L).apply_symm_apply (k - L)
    rw [blockIndexEquiv_apply_lt q L p.1 hpj] at hp
    simp only [ps, Fin.val_succ, Nat.mul_succ]
    omega
  have hinv : (blockIndexEquiv (q + 1) L).symm k = (ps, p.2) := by
    apply (blockIndexEquiv (q + 1) L).injective
    simp [he]
  rw [hinv]
  change ω p.1.succ p.2 = _
  rw [show (blockIndexEquiv q L).symm (k - L) = p by rfl]
  rfl

lemma blockMergeEquiv_eq_recursiveBlockFlatten (q L : ℕ) (hq : 0 < q)
    (ω : Fin q → ℕ → ℝ) {k : ℕ} (hk : k < q * L) :
    @blockMergeEquiv q L ⟨Nat.ne_of_gt hq⟩ ω k =
      recursiveBlockFlatten L q ω k := by
  induction q generalizing k with
  | zero => simp at hk
  | succ q ih =>
      change @blockMergeEquiv (q + 1) L _ ω k =
        if k < L then ω 0 k else recursiveBlockFlatten L q (Fin.tail ω) (k - L)
      split_ifs with hkL
      · simpa only using @blockMergeEquiv_apply_first q L ⟨by omega⟩ ω k hkL
      · have hLk : L ≤ k := Nat.le_of_not_gt hkL
        by_cases hq : q = 0
        · subst q
          simp at hk hLk
          omega
        · rw [@blockMergeEquiv_apply_tail q L ⟨hq⟩ ⟨by omega⟩ ω k hLk hk]
          apply ih (Nat.pos_of_ne_zero hq) (ω := Fin.tail ω)
          simp only [Nat.add_mul, one_mul] at hk
          omega

lemma abs_le_r_div_hundred_of_central {r x : ℝ}
    (hx : x ∈ gaussianCentralSet r) : |x| ≤ r / 100 := by
  rw [gaussianCentralSet, Set.mem_Icc] at hx
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

lemma recursiveBlockFlatten_first {q L : ℕ} (ω : Fin (q + 1) → ℕ → ℝ)
    {k : ℕ} (hk : k < L) :
    recursiveBlockFlatten L (q + 1) ω k = ω 0 k := by
  simp [recursiveBlockFlatten, hk]

lemma recursiveBlockFlatten_tail {q L : ℕ} (ω : Fin (q + 1) → ℕ → ℝ)
    {k : ℕ} (hk : L ≤ k) :
    recursiveBlockFlatten L (q + 1) ω k =
      recursiveBlockFlatten L q (Fin.tail ω) (k - L) := by
  simp [recursiveBlockFlatten, Nat.not_lt.mpr hk]

lemma gaussianBlockSafeEvent_partialSum_le {L : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {ω : ℕ → ℝ} (hω : ω ∈ gaussianBlockSafeEvent (L - 1) r)
    {t : ℕ} (ht : t ≤ L) :
    |∑ k ∈ Finset.range t, ω k| ≤ r := by
  by_cases ht0 : t = 0
  · subst t
    simpa using hr
  · have hL : 0 < L := lt_of_lt_of_le (Nat.pos_of_ne_zero ht0) ht
    have htpos : 0 < t := Nat.pos_of_ne_zero ht0
    have hjmem : t - 1 ∈ Finset.range (L - 1 + 1) := by simp; omega
    have hsqle : (gaussianPartialSum (t - 1) ω) ^ 2 ≤
        (Finset.range (L - 1 + 1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ (gaussianPartialSum k ω) ^ 2) :=
      Finset.le_sup' (fun k ↦ (gaussianPartialSum k ω) ^ 2) hjmem
    have hsq : (gaussianPartialSum (t - 1) ω) ^ 2 < r ^ 2 := hsqle.trans_lt hω
    have habs := (abs_lt_of_sq_lt_sq hsq hr).le
    have hpartial : gaussianPartialSum (t - 1) ω =
        ∑ k ∈ Finset.range t, ω k := by
      unfold gaussianPartialSum gaussianCoordinate
      rw [Nat.sub_add_cancel htpos]
    simpa [hpartial] using habs

/-- Deterministic composition of the local safe-block estimates: every
prefix of the chronologically flattened good chain is within `2r` of its
initial state. -/
theorem recursiveBlockFlatten_partialSum_le
    {q L : ℕ} {r x : ℝ} (hr : 0 < r) (hL : 0 < L)
    (ω : Fin q → ℕ → ℝ)
    (hgood : ω ∈ sampledChainGood (gaussianCentralSet r) (hlozBlockGood L r)
      (hlozBlockStep L) q x)
    (hx : x ∈ gaussianCentralSet r) {t : ℕ} (ht : t ≤ q * L) :
    |x + ∑ k ∈ Finset.range t, recursiveBlockFlatten L q ω k| ≤ 2 * r := by
  induction q generalizing x t with
  | zero =>
      have hxabs := abs_le_r_div_hundred_of_central hx
      simp at ht
      subst t
      simp [recursiveBlockFlatten]
      linarith
  | succ q ih =>
      rw [sampledChainGood] at hgood
      rcases hgood with ⟨hsafe, hxnext, htail⟩
      by_cases htL : t ≤ L
      · have hflat : (∑ k ∈ Finset.range t,
            recursiveBlockFlatten L (q + 1) ω k) =
            ∑ k ∈ Finset.range t, ω 0 k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [recursiveBlockFlatten_first]
          exact (Finset.mem_range.1 hk).trans_le htL
        rw [hflat]
        have hlocal := gaussianBlockSafeEvent_partialSum_le hr.le hsafe htL
        have hxabs := abs_le_r_div_hundred_of_central hx
        calc
          |x + ∑ k ∈ Finset.range t, ω 0 k| ≤
              |x| + |∑ k ∈ Finset.range t, ω 0 k| := abs_add_le _ _
          _ ≤ r / 100 + r := add_le_add hxabs hlocal
          _ ≤ 2 * r := by linarith
      · have hLt : L ≤ t := Nat.le_of_not_ge htL
        have hsum : (∑ k ∈ Finset.range t,
              recursiveBlockFlatten L (q + 1) ω k) =
            (∑ k ∈ Finset.range L, ω 0 k) +
              ∑ k ∈ Finset.range (t - L),
                recursiveBlockFlatten L q (Fin.tail ω) k := by
          rw [show t = L + (t - L) by omega, Finset.sum_range_add]
          simp only [Nat.add_sub_cancel_left]
          congr 1
          · apply Finset.sum_congr rfl
            intro k hk
            rw [recursiveBlockFlatten_first]
            exact Finset.mem_range.1 hk
          · apply Finset.sum_congr rfl
            intro k hk
            rw [recursiveBlockFlatten_tail]
            · congr 1
              omega
            · omega
        rw [hsum]
        have hfull : gaussianPartialSum (L - 1) (ω 0) =
            ∑ k ∈ Finset.range L, ω 0 k := by
          unfold gaussianPartialSum gaussianCoordinate
          rw [Nat.sub_add_cancel hL]
        rw [← hfull]
        rw [show x + (gaussianPartialSum (L - 1) (ω 0) +
            ∑ k ∈ Finset.range (t - L), recursiveBlockFlatten L q (Fin.tail ω) k) =
          (x + gaussianPartialSum (L - 1) (ω 0)) +
            ∑ k ∈ Finset.range (t - L), recursiveBlockFlatten L q (Fin.tail ω) k by
          ring]
        change |hlozBlockStep L 0 x (ω 0) +
          ∑ k ∈ Finset.range (t - L), recursiveBlockFlatten L q (Fin.tail ω) k| ≤
            2 * r
        have htail' : Fin.tail ω ∈
            sampledChainGood (gaussianCentralSet r) (hlozBlockGood L r)
              (hlozBlockStep L) q (hlozBlockStep L 0 x (ω 0)) := by
          have hG : (fun i ↦ hlozBlockGood L r (i + 1)) = hlozBlockGood L r := by
            funext i y z
            rfl
          have hs : (fun i ↦ hlozBlockStep L (i + 1)) = hlozBlockStep L := by
            funext i y z
            rfl
          simpa only [hG, hs] using htail
        apply ih (x := hlozBlockStep L 0 x (ω 0)) (ω := Fin.tail ω) htail' hxnext
        simp only [Nat.add_mul, one_mul] at ht
        omega

/-- The measurable image of the full good block chain in the single stopped
Gaussian increment sequence. -/
noncomputable def hlozBlockChainImage (q L : ℕ) [NeZero q] (r : ℝ) :
    Set (ℕ → ℝ) :=
  blockMergeEquiv q L ''
    sampledChainGood (gaussianCentralSet r) (hlozBlockGood L r)
      (hlozBlockStep L) q 0

lemma measurableSet_hlozBlockChainImage (q L : ℕ) [NeZero q] (r : ℝ) :
    MeasurableSet (hlozBlockChainImage q L r) := by
  rw [hlozBlockChainImage, (blockMergeEquiv q L).measurableSet_image]
  exact measurableSet_sampledChainGood (gaussianCentralSet r) measurableSet_Icc
    (hlozBlockGood L r) (hlozBlockStep L)
    (measurableSet_hlozBlockGood_joint L r)
    (measurable_hlozBlockStep_joint L) 0 q 0

lemma gaussianPadded_blockChainImage (m N q L : ℕ) [NeZero q] (r : ℝ) :
    gaussianProductMeasure (paddedHlozVariance m N) (hlozBlockChainImage q L r) =
      (Measure.pi fun i : Fin q ↦
        gaussianProductMeasure (hlozBlockVariance m N q L i))
        (sampledChainGood (gaussianCentralSet r) (hlozBlockGood L r)
          (hlozBlockStep L) q 0) := by
  rw [← map_pi_gaussianBlocks_blockMerge m N q L,
    Measure.map_apply (blockMergeEquiv q L).measurable
      (measurableSet_hlozBlockChainImage q L r)]
  exact congrArg _ (Equiv.preimage_image (blockMergeEquiv q L).toEquiv _)

theorem one_third_pow_le_gaussianPadded_blockChainImage
    {m N n q L : ℕ} [NeZero q] {r : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hupper : m + N ≤ n)
    (hbudget : 4 * (L : ℝ) * (n : ℝ) ^ 2 ≤ r ^ 2 / 40000) :
    (1 / 3 : ℝ≥0∞) ^ q ≤
      gaussianProductMeasure (paddedHlozVariance m N) (hlozBlockChainImage q L r) := by
  rw [gaussianPadded_blockChainImage]
  exact one_third_pow_le_hlozBlockChain hr hL hupper hbudget

lemma gaussianPDFReal_hlozIncrementVariance {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ℝ) :
    gaussianPDFReal 0 (hlozIncrementVariance ℓ) z = realB ℓ 0 z := by
  unfold hlozIncrementVariance
  change gaussianPDFReal 0 (NNReal.mk (4 * (ℓ : ℝ) ^ 2) (by positivity)) z = realB ℓ 0 z
  rw [← gaussianDensity_eq_gaussianPDFReal (show 0 ≤ 4 * (ℓ : ℝ) ^ 2 by positivity)]
  unfold gaussianDensity realB
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hsqrt : Real.sqrt (2 * Real.pi * (4 * (ℓ : ℝ) ^ 2)) =
      Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ)) := by
    rw [show 2 * Real.pi * (4 * (ℓ : ℝ) ^ 2) =
        (2 * Real.pi) * (2 * (ℓ : ℝ)) ^ 2 by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi), Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * ℓ)]
  rw [hsqrt]
  congr 2
  field_simp [hℓR.ne']
  ring

lemma abs_intFloor_cast_sub_le_one (z : ℝ) : |((⌊z⌋ : ℤ) : ℝ) - z| ≤ 1 := by
  rw [abs_le]
  constructor
  · have h := Int.lt_floor_add_one z
    linarith
  · have h := Int.floor_le z
    linarith

lemma exp_incrementCellCost_mul_gaussianPDF_le_b {ℓ : ℕ} (hℓ : 0 < ℓ)
    {R z : ℝ} (hR : 0 ≤ R) (hz : |z| ≤ 2 * R) :
    Real.exp (-((16 * R + 4) / (8 * (ℓ : ℝ) ^ 2))) *
        gaussianPDFReal 0 (hlozIncrementVariance ℓ) z ≤
      b ℓ 0 ⌊z⌋ := by
  rw [gaussianPDFReal_hlozIncrementVariance hℓ]
  rw [show 16 * R + 4 = 8 * (2 * R) + 4 by ring]
  apply exp_cellCost_mul_realB_le_b (x := 0) (y := z) (k₁ := 0) (k₂ := ⌊z⌋)
    hℓ (show 0 ≤ 2 * R by positivity)
  · simp
  · exact abs_intFloor_cast_sub_le_one z
  · simp [hR]
  · exact hz

lemma incrementCellCostSum_le {m N : ℕ} (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R) :
    cellCostSum m N (fun _ ↦ 2 * R) ≤
      (N : ℝ) * ((16 * R + 4) / (8 * (m : ℝ) ^ 2)) := by
  simpa [show 8 * (2 * R) + 4 = 16 * R + 4 by ring] using
    (cellCostSum_le_of_radius_le (m := m) (N := N) hm
      (R := fun _ ↦ 2 * R) (Q := 2 * R) (fun _ ↦ by positivity) (fun _ ↦ le_rfl))

/-! ### From rounded increments to an admissible integer path -/

def pathOfIncrements {N : ℕ} (h : Fin N → ℤ) : Path N := fun i ↦
  ∑ j : Fin i.val, h ⟨j.val, j.isLt.trans_le (Nat.le_of_lt_succ i.isLt)⟩

@[simp] lemma pathOfIncrements_zero {N : ℕ} (h : Fin N → ℤ) :
    pathOfIncrements h 0 = 0 := by
  change (∑ j : Fin 0, h ⟨j.val, by omega⟩) = 0
  simp

lemma pathOfIncrements_succ_sub {N : ℕ} (h : Fin N → ℤ) (i : Fin N) :
    pathOfIncrements h i.succ - pathOfIncrements h i.castSucc = h i := by
  change (∑ j : Fin (i.val + 1), h ⟨j.val, by omega⟩) -
      (∑ j : Fin i.val, h ⟨j.val, by omega⟩) = h i
  rw [Fin.sum_univ_castSucc]
  simp

lemma b_eq_of_sub_eq {ℓ : ℕ} {a y d : ℤ} (h : y - a = d) :
    b ℓ a y = b ℓ 0 d := by
  unfold b
  congr 3
  have hr : (y : ℝ) - a = d := by exact_mod_cast h
  rw [show (a : ℝ) - y = -d by linarith]
  ring

/-- The path construction preserves exactly the product of increment
kernels; there is no normalization loss in passing to cumulative positions. -/
lemma pathWeight_pathOfIncrements {m N : ℕ} (h : Fin N → ℤ) :
    pathWeight m N (pathOfIncrements h) = ∏ i : Fin N, b (m + i) 0 (h i) := by
  unfold pathWeight
  apply Finset.prod_congr rfl
  intro i _hi
  exact b_eq_of_sub_eq (pathOfIncrements_succ_sub h i)

def realPathOfIncrements {N : ℕ} (z : Fin N → ℝ) : Fin (N + 1) → ℝ := fun i ↦
  ∑ j : Fin i.val, z ⟨j.val, j.isLt.trans_le (Nat.le_of_lt_succ i.isLt)⟩

/-- Rounding each real increment down changes its cumulative sum after `i`
steps by at most `i`. -/
lemma pathOfFloorIncrements_sub_realPath_abs_le {N : ℕ} (z : Fin N → ℝ)
    (i : Fin (N + 1)) :
    |(pathOfIncrements (fun j ↦ ⌊z j⌋) i : ℝ) - realPathOfIncrements z i| ≤ i := by
  have hrewrite : (pathOfIncrements (fun j ↦ ⌊z j⌋) i : ℝ) -
      realPathOfIncrements z i =
      ∑ j : Fin i.val,
        ((((⌊z ⟨j.val, j.isLt.trans_le (Nat.le_of_lt_succ i.isLt)⟩⌋ : ℤ) : ℝ)) -
          z ⟨j.val, j.isLt.trans_le (Nat.le_of_lt_succ i.isLt)⟩) := by
    simp only [pathOfIncrements, realPathOfIncrements, Int.cast_sum]
    rw [Finset.sum_sub_distrib]
  rw [hrewrite]
  calc
    |∑ j : Fin i.val,
        ((((⌊z ⟨j.val, j.isLt.trans_le (Nat.le_of_lt_succ i.isLt)⟩⌋ : ℤ) : ℝ)) -
          z ⟨j.val, j.isLt.trans_le (Nat.le_of_lt_succ i.isLt)⟩)| ≤
        ∑ _j : Fin i.val, (1 : ℝ) := Finset.abs_sum_le_sum_abs _ _ |>.trans <| by
          apply Finset.sum_le_sum
          intro j _hj
          exact abs_intFloor_cast_sub_le_one _
    _ = i := by simp

lemma pathOfFloorIncrements_abs_le {N : ℕ} (z : Fin N → ℝ) {R : ℝ}
    (_hR : 0 ≤ R) (hpartial : ∀ i, |realPathOfIncrements z i| ≤ R)
    (hN : (N : ℝ) ≤ R) (i : Fin (N + 1)) :
    |(pathOfIncrements (fun j ↦ ⌊z j⌋) i : ℝ)| ≤ 2 * R := by
  calc
    |(pathOfIncrements (fun j ↦ ⌊z j⌋) i : ℝ)| =
        |((pathOfIncrements (fun j ↦ ⌊z j⌋) i : ℝ) - realPathOfIncrements z i) +
          realPathOfIncrements z i| := by
      congr 1
      ring
    _ ≤ |(pathOfIncrements (fun j ↦ ⌊z j⌋) i : ℝ) - realPathOfIncrements z i| +
          |realPathOfIncrements z i| := abs_add_le _ _
    _ ≤ (i : ℝ) + R :=
      add_le_add (pathOfFloorIncrements_sub_realPath_abs_le z i) (hpartial i)
    _ ≤ 2 * R := by
      have hi : (i : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ i.isLt
      linarith

/-- If the source corridor dominates twice the continuous radius and the
number of rounding operations, the rounded cumulative-increment path is one
of the exact paths summed by `hlozPathSum`. -/
theorem pathOfFloorIncrements_mem_hlozCorridorPaths {m N : ℕ} {δ R : ℝ}
    (z : Fin N → ℝ) (hR : 0 ≤ R)
    (hpartial : ∀ i, |realPathOfIncrements z i| ≤ R)
    (hN : (N : ℝ) ≤ R)
    (hradius : ∀ i : Fin (N + 1),
      2 * R ≤ (corridorRadius δ (m + i) : ℝ)) :
    pathOfIncrements (fun j ↦ ⌊z j⌋) ∈ hlozCorridorPaths δ m N := by
  rw [hlozCorridorPaths, mem_corridorPaths]
  intro i
  have hp := pathOfFloorIncrements_abs_le z hR hpartial hN i
  have hpr : |(pathOfIncrements (fun j ↦ ⌊z j⌋) i : ℝ)| ≤
      (corridorRadius δ (m + i) : ℝ) := hp.trans (hradius i)
  exact_mod_cast hpr

noncomputable def incrementGaussianDensityProduct (m N : ℕ) (z : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, gaussianPDFReal 0 (hlozIncrementVariance (m + i)) (z i)

/-- Pointwise, the factorized Gaussian density of a real increment vector is
bounded by the exact HLOZ weight of its rounded cumulative path, with only
the explicit accumulated cell cost. -/
theorem exp_neg_incrementCellCost_mul_density_le_pathWeight
    {m N : ℕ} (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (z : Fin N → ℝ) (hz : ∀ i, |z i| ≤ 2 * R) :
    Real.exp (-cellCostSum m N (fun _ ↦ 2 * R)) *
        incrementGaussianDensityProduct m N z ≤
      pathWeight m N (pathOfIncrements fun i ↦ ⌊z i⌋) := by
  have hpoint : ∀ i : Fin N,
      Real.exp (-((16 * R + 4) / (8 * ((m + i : ℕ) : ℝ) ^ 2))) *
          gaussianPDFReal 0 (hlozIncrementVariance (m + i)) (z i) ≤
        b (m + i) 0 ⌊z i⌋ := by
    intro i
    exact exp_incrementCellCost_mul_gaussianPDF_le_b (by omega) hR (hz i)
  rw [pathWeight_pathOfIncrements]
  calc
    Real.exp (-cellCostSum m N (fun _ ↦ 2 * R)) *
        incrementGaussianDensityProduct m N z =
      ∏ i : Fin N,
        (Real.exp (-((16 * R + 4) / (8 * ((m + i : ℕ) : ℝ) ^ 2))) *
          gaussianPDFReal 0 (hlozIncrementVariance (m + i)) (z i)) := by
      rw [cellCostSum, incrementGaussianDensityProduct, Finset.prod_mul_distrib,
        ← Real.exp_sum]
      congr 1
      rw [← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      congr 2
      ring
    _ ≤ ∏ i : Fin N, b (m + i) 0 ⌊z i⌋ := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact mul_nonneg (Real.exp_pos _).le (gaussianPDFReal_nonneg _ _ _)
      · intro i _hi
        exact hpoint i

/-- Integrated one-dimensional cell comparison.  The extra `+1` in the
radius makes the estimate valid on the whole unit cell once its integer
label is known to lie in `[-(2R+1),2R+1]`. -/
lemma exp_incrementCellCost_mul_gaussianReal_Ico_le_b {ℓ : ℕ} (hℓ : 0 < ℓ)
    {R : ℝ} (hR : 0 ≤ R) (h : ℤ) (hh : |(h : ℝ)| ≤ 2 * R + 1) :
    Real.exp (-((16 * (R + 1) + 4) / (8 * (ℓ : ℝ) ^ 2))) *
        (gaussianReal 0 (hlozIncrementVariance ℓ)).real
          (Ico (h : ℝ) ((h : ℝ) + 1)) ≤
      b ℓ 0 h := by
  have hv : hlozIncrementVariance ℓ ≠ 0 := by
    intro hv0
    have hc := congrArg (fun v : NNReal ↦ (v : ℝ)) hv0
    change 4 * (ℓ : ℝ) ^ 2 = 0 at hc
    have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    nlinarith
  have hmeasure := gaussianReal_apply_eq_integral 0 (v := hlozIncrementVariance ℓ) hv
    (Ico (h : ℝ) ((h : ℝ) + 1))
  rw [measureReal_def, hmeasure, ENNReal.toReal_ofReal]
  · rw [← integral_const_mul]
    have hpdf : IntegrableOn (gaussianPDFReal 0 (hlozIncrementVariance ℓ))
        (Ico (h : ℝ) ((h : ℝ) + 1)) :=
      (integrable_gaussianPDFReal 0 (hlozIncrementVariance ℓ)).integrableOn
    have hconst : IntegrableOn (fun _z : ℝ ↦ b ℓ 0 h)
        (Ico (h : ℝ) ((h : ℝ) + 1)) :=
      continuous_const.integrableOn_Icc.mono_set Ico_subset_Icc_self
    calc
      ∫ z in Ico (h : ℝ) ((h : ℝ) + 1),
          Real.exp (-((16 * (R + 1) + 4) / (8 * (ℓ : ℝ) ^ 2))) *
            gaussianPDFReal 0 (hlozIncrementVariance ℓ) z ≤
          ∫ _z in Ico (h : ℝ) ((h : ℝ) + 1), b ℓ 0 h := by
        apply setIntegral_mono_on (hpdf.const_mul _) hconst measurableSet_Ico
        intro z hz
        have hzabs : |z| ≤ 2 * (R + 1) := by
          rw [mem_Ico] at hz
          calc
            |z| ≤ |(h : ℝ)| + 1 := by
              rw [abs_le]
              constructor
              · have habs := neg_abs_le (h : ℝ)
                linarith
              · have habs := le_abs_self (h : ℝ)
                linarith
            _ ≤ 2 * R + 1 + 1 := by
              simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hh 1
            _ = 2 * (R + 1) := by ring
        have hp := exp_incrementCellCost_mul_gaussianPDF_le_b hℓ
          (show 0 ≤ R + 1 by linarith) hzabs
        have hfloor : ⌊z⌋ = h := by
          rw [Int.floor_eq_iff]
          exact ⟨hz.1, hz.2⟩
        simpa [hfloor] using hp
      _ = b ℓ 0 h := by
        rw [setIntegral_const, measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal]
        · simp
        · norm_num
  · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun z ↦
      gaussianPDFReal_nonneg 0 (hlozIncrementVariance ℓ) z)

/-- Product of the independent Gaussian probabilities of the unit increment
cells labelled by an integer increment vector. -/
noncomputable def incrementGaussianCellMassProduct (m N : ℕ) (h : Fin N → ℤ) : ℝ :=
  ∏ i : Fin N,
    (gaussianReal 0 (hlozIncrementVariance (m + i))).real
      (Ico (h i : ℝ) ((h i : ℝ) + 1))

/-- Integrated product-cell comparison.  Every Gaussian increment cube in
the indicated box contributes, after the explicit cell loss, at most the
weight of its exact rounded cumulative integer path. -/
theorem exp_neg_incrementCellCost_mul_cellMassProduct_le_pathWeight
    {m N : ℕ} (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (h : Fin N → ℤ) (hh : ∀ i, |(h i : ℝ)| ≤ 2 * R + 1) :
    Real.exp (-cellCostSum m N (fun _ ↦ 2 * (R + 1))) *
        incrementGaussianCellMassProduct m N h ≤
      pathWeight m N (pathOfIncrements h) := by
  have hpoint : ∀ i : Fin N,
      Real.exp (-((16 * (R + 1) + 4) / (8 * ((m + i : ℕ) : ℝ) ^ 2))) *
          (gaussianReal 0 (hlozIncrementVariance (m + i))).real
            (Ico (h i : ℝ) ((h i : ℝ) + 1)) ≤
        b (m + i) 0 (h i) := by
    intro i
    exact exp_incrementCellCost_mul_gaussianReal_Ico_le_b (by omega) hR (h i) (hh i)
  rw [pathWeight_pathOfIncrements]
  calc
    Real.exp (-cellCostSum m N (fun _ ↦ 2 * (R + 1))) *
        incrementGaussianCellMassProduct m N h =
      ∏ i : Fin N,
        (Real.exp (-((16 * (R + 1) + 4) / (8 * ((m + i : ℕ) : ℝ) ^ 2))) *
          (gaussianReal 0 (hlozIncrementVariance (m + i))).real
            (Ico (h i : ℝ) ((h i : ℝ) + 1))) := by
      rw [cellCostSum, incrementGaussianCellMassProduct, Finset.prod_mul_distrib,
        ← Real.exp_sum]
      congr 1
      rw [← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      congr 2
      ring
    _ ≤ ∏ i : Fin N, b (m + i) 0 (h i) := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact mul_nonneg (Real.exp_pos _).le measureReal_nonneg
      · intro i _hi
        exact hpoint i

/-- Cylinder in the canonical infinite product space corresponding to a
fixed vector of unit increment cells. -/
def incrementCellCylinder (N : ℕ) (h : Fin N → ℤ) : Set (ℕ → ℝ) :=
  ((↑(Finset.range N) : Set ℕ).pi fun i ↦
    if hi : i < N then Ico (h ⟨i, hi⟩ : ℝ) ((h ⟨i, hi⟩ : ℝ) + 1) else univ)

@[simp] lemma mem_incrementCellCylinder {N : ℕ} {h : Fin N → ℤ} {z : ℕ → ℝ} :
    z ∈ incrementCellCylinder N h ↔
      ∀ i : Fin N, z i ∈ Ico (h i : ℝ) ((h i : ℝ) + 1) := by
  rw [incrementCellCylinder, Set.mem_pi]
  constructor
  · intro hz i
    simpa [i.isLt] using hz i (by simp)
  · intro hz i hi
    have hiN : i < N := by simpa using hi
    simpa [hiN] using hz ⟨i, hiN⟩

lemma measurableSet_incrementCellCylinder (N : ℕ) (h : Fin N → ℤ) :
    MeasurableSet (incrementCellCylinder N h) := by
  unfold incrementCellCylinder
  apply MeasurableSet.pi
  · exact (Finset.finite_toSet (Finset.range N)).countable
  intro i hi
  split_ifs
  · exact measurableSet_Ico
  · exact MeasurableSet.univ

/-- The real mass of a finite increment-cell cylinder is exactly the product
of its one-dimensional Gaussian cell masses. -/
lemma gaussianProductMeasure_incrementCellCylinder_real
    (m N : ℕ) (h : Fin N → ℤ) :
    (gaussianProductMeasure fun i ↦ hlozIncrementVariance (m + i)).real
        (incrementCellCylinder N h) =
      incrementGaussianCellMassProduct m N h := by
  rw [measureReal_def, incrementCellCylinder, gaussianProductMeasure,
    Measure.infinitePi_pi (gaussianIncrementMeasure
      fun i ↦ hlozIncrementVariance (m + i))]
  · rw [ENNReal.toReal_prod]
    unfold incrementGaussianCellMassProduct gaussianIncrementMeasure
    rw [Finset.prod_range]
    apply Finset.prod_congr rfl
    intro i hi
    have hiN : (i : ℕ) < N := i.isLt
    simp [hiN, measureReal_def]
  · intro i hi
    have hiN : i < N := by simpa using hi
    simp [hiN]

lemma pathOfIncrements_injective {N : ℕ} :
    Function.Injective (@pathOfIncrements N) := by
  intro h k hhk
  funext i
  have hp := congrFun hhk i.succ
  have hq := congrFun hhk i.castSucc
  have hs : pathOfIncrements h i.succ - pathOfIncrements h i.castSucc =
      pathOfIncrements k i.succ - pathOfIncrements k i.castSucc := by rw [hp, hq]
  simpa [pathOfIncrements_succ_sub] using hs

/-- Finite lattice transfer.  Any real Gaussian event covered by increment
cells whose cumulative integer paths lie in the exact HLOZ corridor gives a
lower bound for the source path sum, with no probabilistic hypothesis left in
the conclusion. -/
theorem gaussianEvent_mass_le_hlozPathSum
    {m N : ℕ} (hm : 0 < m) {δ R : ℝ} (hR : 0 ≤ R)
    (H : Finset (Fin N → ℤ)) (A : Set (ℕ → ℝ))
    (hcover : A ⊆ ⋃ h ∈ H, incrementCellCylinder N h)
    (hbox : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ 2 * R + 1)
    (hadmissible : ∀ h ∈ H, pathOfIncrements h ∈ hlozCorridorPaths δ m N) :
    Real.exp (-cellCostSum m N (fun _ ↦ 2 * (R + 1))) *
        (gaussianProductMeasure fun i ↦ hlozIncrementVariance (m + i)).real A ≤
      hlozPathSum δ m N := by
  let μ : Measure (ℕ → ℝ) :=
    gaussianProductMeasure fun i ↦ hlozIncrementVariance (m + i)
  have hmeasure : μ A ≤ ∑ h ∈ H, μ (incrementCellCylinder N h) :=
    (measure_mono hcover).trans (measure_biUnion_finset_le H _)
  have hsumtop : (∑ h ∈ H, μ (incrementCellCylinder N h)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro h hh
    exact measure_ne_top μ _
  have hmeasureReal := ENNReal.toReal_mono hsumtop hmeasure
  rw [ENNReal.toReal_sum] at hmeasureReal
  · have hcell : μ.real A ≤ ∑ h ∈ H, incrementGaussianCellMassProduct m N h := by
      calc
        μ.real A ≤ ∑ h ∈ H, μ.real (incrementCellCylinder N h) := by
          simpa [measureReal_def] using hmeasureReal
        _ = ∑ h ∈ H, incrementGaussianCellMassProduct m N h := by
          apply Finset.sum_congr rfl
          intro h hh
          exact gaussianProductMeasure_incrementCellCylinder_real m N h
    calc
      Real.exp (-cellCostSum m N (fun _ ↦ 2 * (R + 1))) * μ.real A ≤
          Real.exp (-cellCostSum m N (fun _ ↦ 2 * (R + 1))) *
            ∑ h ∈ H, incrementGaussianCellMassProduct m N h :=
        mul_le_mul_of_nonneg_left hcell (Real.exp_pos _).le
      _ = ∑ h ∈ H,
          Real.exp (-cellCostSum m N (fun _ ↦ 2 * (R + 1))) *
            incrementGaussianCellMassProduct m N h := by
        rw [Finset.mul_sum]
      _ ≤ ∑ h ∈ H, pathWeight m N (pathOfIncrements h) := by
        apply Finset.sum_le_sum
        intro h hh
        exact exp_neg_incrementCellCost_mul_cellMassProduct_le_pathWeight
          hm hR h (hbox h hh)
      _ = ∑ p ∈ H.image pathOfIncrements, pathWeight m N p := by
        symm
        exact Finset.sum_image pathOfIncrements_injective.injOn
      _ ≤ ∑ p ∈ hlozCorridorPaths δ m N, pathWeight m N p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_image] at hp
          obtain ⟨h, hh, rfl⟩ := hp
          exact hadmissible h hh
        · intro p hp _hn
          exact pathWeight_nonneg m N p
      _ = hlozPathSum δ m N := rfl
  · intro h hh
    exact measure_ne_top μ _

/-- Finite coordinate box for integer increment labels. -/
noncomputable def incrementBox (N M : ℕ) : Finset (Fin N → ℤ) :=
  Fintype.piFinset fun _ ↦ Finset.Icc (-(M : ℤ)) (M : ℤ)

@[simp] lemma mem_incrementBox {N M : ℕ} {h : Fin N → ℤ} :
    h ∈ incrementBox N M ↔ ∀ i, |h i| ≤ M := by
  simp [incrementBox, abs_le]

/-- Increment cells whose cumulative integer paths are in the exact source
corridor. -/
noncomputable def admissibleIncrementCells (δ : ℝ) (m N M : ℕ) :
    Finset (Fin N → ℤ) :=
  (incrementBox N M).filter fun h ↦ pathOfIncrements h ∈ hlozCorridorPaths δ m N

@[simp] lemma mem_admissibleIncrementCells {δ : ℝ} {m N M : ℕ}
    {h : Fin N → ℤ} :
    h ∈ admissibleIncrementCells δ m N M ↔
      (∀ i, |h i| ≤ M) ∧ pathOfIncrements h ∈ hlozCorridorPaths δ m N := by
  simp [admissibleIncrementCells]

/-- A bounded real-increment event whose rounded cumulative paths are
admissible is covered by finitely many admissible unit-cell cylinders. -/
lemma event_subset_admissibleIncrementCell_union
    {δ R : ℝ} {m N M : ℕ} (hM : 2 * R + 1 ≤ (M : ℝ))
    (A : Set (ℕ → ℝ))
    (hincrement : ∀ ω ∈ A, ∀ i : Fin N, |ω i| ≤ 2 * R)
    (hadmissible : ∀ ω ∈ A,
      pathOfIncrements (fun i : Fin N ↦ ⌊ω i⌋) ∈ hlozCorridorPaths δ m N) :
    A ⊆ ⋃ h ∈ admissibleIncrementCells δ m N M, incrementCellCylinder N h := by
  intro ω hω
  let h : Fin N → ℤ := fun i ↦ ⌊ω i⌋
  have hbox : ∀ i, |h i| ≤ M := by
    intro i
    have hfloor : |((h i : ℤ) : ℝ)| ≤ 2 * R + 1 := by
      calc
        |((h i : ℤ) : ℝ)| =
            |(((h i : ℤ) : ℝ) - ω i) + ω i| := by congr 1; ring
        _ ≤ |((h i : ℤ) : ℝ) - ω i| + |ω i| := abs_add_le _ _
        _ ≤ 1 + 2 * R := add_le_add (abs_intFloor_cast_sub_le_one (ω i))
          (hincrement ω hω i)
        _ = 2 * R + 1 := by ring
    have hfloorM : |((h i : ℤ) : ℝ)| ≤ (M : ℝ) := hfloor.trans hM
    exact_mod_cast hfloorM
  have hh : h ∈ admissibleIncrementCells δ m N M := by
    rw [mem_admissibleIncrementCells]
    exact ⟨hbox, hadmissible ω hω⟩
  rw [Set.mem_iUnion]
  refine ⟨h, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hh, ?_⟩
  rw [mem_incrementCellCylinder]
  intro i
  change ω i ∈ Ico ((⌊ω i⌋ : ℤ) : ℝ) (((⌊ω i⌋ : ℤ) : ℝ) + 1)
  exact ⟨Int.floor_le (ω i), Int.lt_floor_add_one (ω i)⟩

lemma realPathOfIncrements_succ_sub {N : ℕ} (z : Fin N → ℝ) (i : Fin N) :
    realPathOfIncrements z i.succ - realPathOfIncrements z i.castSucc = z i := by
  change (∑ j : Fin (i.val + 1), z ⟨j.val, by omega⟩) -
      (∑ j : Fin i.val, z ⟨j.val, by omega⟩) = z i
  rw [Fin.sum_univ_castSucc]
  simp

/-- Real increment vectors whose every cumulative position, including the
initial zero, lies in the symmetric corridor of radius `R`. -/
def incrementCorridorEvent (N : ℕ) (R : ℝ) : Set (ℕ → ℝ) :=
  {ω | ∀ i : Fin (N + 1),
    |realPathOfIncrements (fun j : Fin N ↦ ω j) i| ≤ R}

def takeFin (N : ℕ) (ω : ℕ → ℝ) : Fin N → ℝ := fun i ↦ ω i

lemma measurable_takeFin (N : ℕ) : Measurable (takeFin N) := by
  unfold takeFin
  fun_prop

lemma map_gaussianProductMeasure_takeFin (v : ℕ → NNReal) (N : ℕ) :
    (gaussianProductMeasure v).map (takeFin N) =
      Measure.pi fun i : Fin N ↦ gaussianReal 0 (v i) := by
  have hind : iIndepFun (fun i : Fin N ↦ gaussianCoordinate (i : ℕ))
      (gaussianProductMeasure v) :=
    (gaussianCoordinate_iIndepFun v).precomp Fin.val_injective
  have hmap := hind.map_fun_eq_pi_map
    (fun i : Fin N ↦ (measurable_gaussianCoordinate i).aemeasurable)
  rw [show takeFin N = fun (ω : ℕ → ℝ) (i : Fin N) ↦
      gaussianCoordinate (i : ℕ) ω by
    funext ω i
    rfl, hmap]
  congr 1
  funext i
  exact (gaussianCoordinate_hasLaw v i).map_eq

def finiteIncrementCorridorEvent (N : ℕ) (R : ℝ) : Set (Fin N → ℝ) :=
  {z | ∀ i : Fin (N + 1), |realPathOfIncrements z i| ≤ R}

lemma measurableSet_finiteIncrementCorridorEvent (N : ℕ) (R : ℝ) :
    MeasurableSet (finiteIncrementCorridorEvent N R) := by
  rw [show finiteIncrementCorridorEvent N R =
      ⋂ i : Fin (N + 1), {z | |realPathOfIncrements z i| ≤ R} by
    ext z
    simp [finiteIncrementCorridorEvent]]
  apply MeasurableSet.iInter
  intro i
  have hp : Measurable (fun z : Fin N → ℝ ↦ realPathOfIncrements z i) := by
    unfold realPathOfIncrements
    fun_prop
  exact measurableSet_le hp.abs measurable_const

lemma incrementCorridorEvent_eq_preimage_takeFin (N : ℕ) (R : ℝ) :
    incrementCorridorEvent N R = takeFin N ⁻¹' finiteIncrementCorridorEvent N R := by
  rfl

/-- Any two independent Gaussian sequences with identical first `N`
variances give the same mass to the `N`-increment corridor. -/
lemma gaussianProductMeasure_incrementCorridorEvent_eq_of_first
    {v w : ℕ → NNReal} {N : ℕ} (hvw : ∀ i < N, v i = w i) (R : ℝ) :
    gaussianProductMeasure v (incrementCorridorEvent N R) =
      gaussianProductMeasure w (incrementCorridorEvent N R) := by
  rw [incrementCorridorEvent_eq_preimage_takeFin,
    ← Measure.map_apply (measurable_takeFin N) (measurableSet_finiteIncrementCorridorEvent N R),
    map_gaussianProductMeasure_takeFin,
    ← Measure.map_apply (measurable_takeFin N) (measurableSet_finiteIncrementCorridorEvent N R),
    map_gaussianProductMeasure_takeFin]
  congr with i
  rw [hvw i i.isLt]

lemma gaussianPadded_incrementCorridorEvent (m N : ℕ) (R : ℝ) :
    gaussianProductMeasure (paddedHlozVariance m N) (incrementCorridorEvent N R) =
      gaussianProductMeasure (fun i ↦ hlozIncrementVariance (m + i))
        (incrementCorridorEvent N R) := by
  apply gaussianProductMeasure_incrementCorridorEvent_eq_of_first
  intro i hi
  simp [paddedHlozVariance, hi]

/-- Every path in the good block-chain image belongs to the global
`N`-increment corridor. -/
lemma hlozBlockChainImage_subset_incrementCorridorEvent
    {q L N : ℕ} [NeZero q] {r : ℝ} (hr : 0 < r) (hL : 0 < L)
    (hN : N ≤ q * L) :
    hlozBlockChainImage q L r ⊆ incrementCorridorEvent N (2 * r) := by
  intro z hz
  rw [hlozBlockChainImage] at hz
  obtain ⟨ω, hgood, rfl⟩ := hz
  intro i
  have hiN : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  have hiq : i.val ≤ q * L := hiN.trans hN
  have hsum : realPathOfIncrements
        (fun j : Fin N ↦ blockMergeEquiv q L ω j) i =
      ∑ k ∈ Finset.range i.val, recursiveBlockFlatten L q ω k := by
    change (∑ j : Fin i.val, blockMergeEquiv q L ω j.val) = _
    rw [Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    apply blockMergeEquiv_eq_recursiveBlockFlatten q L (NeZero.pos q) ω
    have hki := Finset.mem_range.1 hk
    omega
  rw [hsum]
  have hbound := recursiveBlockFlatten_partialSum_le hr hL ω hgood (by
    simp only [gaussianCentralSet, Set.mem_Icc]
    constructor <;> linarith) hiq
  simpa using hbound

/-- The deterministic block construction gives a premise-free Gaussian
small-ball lower bound with exactly `q` blocks. -/
theorem one_third_pow_le_gaussianIncrementCorridor
    {m N n q L : ℕ} [NeZero q] {r : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hupper : m + N ≤ n)
    (hcover : N ≤ q * L)
    (hbudget : 4 * (L : ℝ) * (n : ℝ) ^ 2 ≤ r ^ 2 / 40000) :
    (1 / 3 : ℝ≥0∞) ^ q ≤
      gaussianProductMeasure (fun i ↦ hlozIncrementVariance (m + i))
        (incrementCorridorEvent N (2 * r)) := by
  rw [← gaussianPadded_incrementCorridorEvent m N (2 * r)]
  exact (one_third_pow_le_gaussianPadded_blockChainImage hr hL hupper hbudget).trans
    (measure_mono (hlozBlockChainImage_subset_incrementCorridorEvent hr hL hcover))

lemma increment_abs_le_of_mem_incrementCorridorEvent {N : ℕ} {R : ℝ}
    {ω : ℕ → ℝ} (hω : ω ∈ incrementCorridorEvent N R) (i : Fin N) :
    |ω i| ≤ 2 * R := by
  have hs := realPathOfIncrements_succ_sub (fun j : Fin N ↦ ω j) i
  rw [← hs]
  calc
    |realPathOfIncrements (fun j : Fin N ↦ ω j) i.succ -
        realPathOfIncrements (fun j : Fin N ↦ ω j) i.castSucc| ≤
      |realPathOfIncrements (fun j : Fin N ↦ ω j) i.succ| +
        |realPathOfIncrements (fun j : Fin N ↦ ω j) i.castSucc| := abs_sub _ _
    _ ≤ R + R := add_le_add (hω i.succ) (hω i.castSucc)
    _ = 2 * R := by ring

noncomputable def boundedAdmissibleIncrementCells
    (δ R : ℝ) (m N M : ℕ) : Finset (Fin N → ℤ) :=
  (incrementBox N M).filter fun h ↦
    (∀ i, |(h i : ℝ)| ≤ 2 * R + 1) ∧
      pathOfIncrements h ∈ hlozCorridorPaths δ m N

@[simp] lemma mem_boundedAdmissibleIncrementCells
    {δ R : ℝ} {m N M : ℕ} {h : Fin N → ℤ} :
    h ∈ boundedAdmissibleIncrementCells δ R m N M ↔
      (∀ i, |h i| ≤ M) ∧ (∀ i, |(h i : ℝ)| ≤ 2 * R + 1) ∧
        pathOfIncrements h ∈ hlozCorridorPaths δ m N := by
  simp [boundedAdmissibleIncrementCells]

lemma incrementCorridorEvent_subset_cell_union
    {δ R : ℝ} {m N M : ℕ} (hR : 0 ≤ R) (hM : 2 * R + 1 ≤ (M : ℝ))
    (hN : (N : ℝ) ≤ R)
    (hradius : ∀ i : Fin (N + 1),
      2 * R ≤ (corridorRadius δ (m + i) : ℝ)) :
    incrementCorridorEvent N R ⊆
      ⋃ h ∈ boundedAdmissibleIncrementCells δ R m N M,
        incrementCellCylinder N h := by
  intro ω hω
  let h : Fin N → ℤ := fun i ↦ ⌊ω i⌋
  have hrealbox : ∀ i, |(h i : ℝ)| ≤ 2 * R + 1 := by
    intro i
    calc
      |(h i : ℝ)| = |(h i : ℝ) - ω i + ω i| := by congr 1; ring
      _ ≤ |(h i : ℝ) - ω i| + |ω i| := abs_add_le _ _
      _ ≤ 1 + 2 * R := add_le_add (abs_intFloor_cast_sub_le_one (ω i))
        (increment_abs_le_of_mem_incrementCorridorEvent hω i)
      _ = 2 * R + 1 := by ring
  have hintbox : ∀ i, |h i| ≤ M := by
    intro i
    have hh : |(h i : ℝ)| ≤ (M : ℝ) := (hrealbox i).trans hM
    exact_mod_cast hh
  have hpath : pathOfIncrements h ∈ hlozCorridorPaths δ m N :=
    pathOfFloorIncrements_mem_hlozCorridorPaths
      (fun i : Fin N ↦ ω i) hR hω hN hradius
  have hh : h ∈ boundedAdmissibleIncrementCells δ R m N M := by
    rw [mem_boundedAdmissibleIncrementCells]
    exact ⟨hintbox, hrealbox, hpath⟩
  rw [Set.mem_iUnion]
  refine ⟨h, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hh, ?_⟩
  rw [mem_incrementCellCylinder]
  intro i
  change ω i ∈ Ico ((⌊ω i⌋ : ℤ) : ℝ) (((⌊ω i⌋ : ℤ) : ℝ) + 1)
  exact ⟨Int.floor_le (ω i), Int.lt_floor_add_one (ω i)⟩

/-- Exact lattice transfer for the whole finite Gaussian increment corridor.
The only hypotheses are the explicit geometric relations required by the
increment-rounding construction. -/
theorem gaussianIncrementCorridor_mass_le_hlozPathSum
    {m N : ℕ} (hm : 0 < m) {δ R : ℝ} (hR : 0 ≤ R)
    (hN : (N : ℝ) ≤ R)
    (hradius : ∀ i : Fin (N + 1),
      2 * R ≤ (corridorRadius δ (m + i) : ℝ)) :
    Real.exp (-cellCostSum m N (fun _ ↦ 2 * (R + 1))) *
        (gaussianProductMeasure fun i ↦ hlozIncrementVariance (m + i)).real
          (incrementCorridorEvent N R) ≤
      hlozPathSum δ m N := by
  let M : ℕ := ⌈2 * R + 1⌉₊
  let H := boundedAdmissibleIncrementCells δ R m N M
  apply gaussianEvent_mass_le_hlozPathSum hm hR H (incrementCorridorEvent N R)
  · exact incrementCorridorEvent_subset_cell_union hR (Nat.le_ceil (2 * R + 1)) hN hradius
  · intro h hh i
    exact (mem_boundedAdmissibleIncrementCells.1 hh).2.1 i
  · intro h hh
    exact (mem_boundedAdmissibleIncrementCells.1 hh).2.2

lemma one_third_pow_eq_exp (q : ℕ) :
    (1 / 3 : ℝ) ^ q = Real.exp (-(q : ℝ) * Real.log 3) := by
  calc
    (1 / 3 : ℝ) ^ q = (Real.exp (-Real.log 3)) ^ q := by
      congr 1
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      norm_num
    _ = Real.exp ((q : ℝ) * (-Real.log 3)) := by rw [Real.exp_nat_mul]
    _ = Real.exp (-(q : ℝ) * Real.log 3) := by congr 1; ring

theorem one_third_real_pow_le_gaussianIncrementCorridor
    {m N n q L : ℕ} [NeZero q] {r : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hupper : m + N ≤ n)
    (hcover : N ≤ q * L)
    (hbudget : 4 * (L : ℝ) * (n : ℝ) ^ 2 ≤ r ^ 2 / 40000) :
    (1 / 3 : ℝ) ^ q ≤
      (gaussianProductMeasure fun i ↦ hlozIncrementVariance (m + i)).real
        (incrementCorridorEvent N (2 * r)) := by
  have h := one_third_pow_le_gaussianIncrementCorridor hr hL hupper hcover hbudget
  have hreal := ENNReal.toReal_mono
    (measure_ne_top (gaussianProductMeasure fun i ↦ hlozIncrementVariance (m + i))
      (incrementCorridorEvent N (2 * r))) h
  simpa [measureReal_def, ENNReal.toReal_pow] using hreal

/-- Fixed-length variance-budget form of HLOZ Lemma A.8.  The exponent
displays separately the block small-ball cost and the exact accumulated
lattice-cell cost. -/
theorem exp_neg_block_and_cellCost_le_hlozPathSum
    {m N n q L : ℕ} [NeZero q] {δ r : ℝ}
    (hm : 0 < m) (hr : 0 < r) (hL : 0 < L) (hupper : m + N ≤ n)
    (hcover : N ≤ q * L)
    (hbudget : 4 * (L : ℝ) * (n : ℝ) ^ 2 ≤ r ^ 2 / 40000)
    (hN : (N : ℝ) ≤ 2 * r)
    (hradius : ∀ i : Fin (N + 1),
      4 * r ≤ (corridorRadius δ (m + i) : ℝ)) :
    Real.exp (-(cellCostSum m N (fun _ ↦ 2 * (2 * r + 1)) +
        (q : ℝ) * Real.log 3)) ≤
      hlozPathSum δ m N := by
  have hmass := one_third_real_pow_le_gaussianIncrementCorridor
    hr hL hupper hcover hbudget
  have hlattice := gaussianIncrementCorridor_mass_le_hlozPathSum
    (δ := δ) (R := 2 * r) hm (show 0 ≤ 2 * r by positivity) hN (by
      simpa only [show 2 * (2 * r) = 4 * r by ring] using hradius)
  calc
    Real.exp (-(cellCostSum m N (fun _ ↦ 2 * (2 * r + 1)) +
        (q : ℝ) * Real.log 3)) =
        Real.exp (-cellCostSum m N (fun _ ↦ 2 * (2 * r + 1))) *
          (1 / 3 : ℝ) ^ q := by
      rw [one_third_pow_eq_exp, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-cellCostSum m N (fun _ ↦ 2 * (2 * r + 1))) *
        (gaussianProductMeasure fun i ↦ hlozIncrementVariance (m + i)).real
          (incrementCorridorEvent N (2 * r)) :=
      mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
    _ ≤ hlozPathSum δ m N := hlattice


/-- The natural fixed block length corresponding to the variance budget
`4 L n² ≤ r² / 40000`. -/
noncomputable def varianceBlockRatio (n : ℕ) (r : ℝ) : ℝ :=
  r ^ 2 / (160000 * (n : ℝ) ^ 2)

noncomputable def varianceBlockLength (n : ℕ) (r : ℝ) : ℕ :=
  ⌊varianceBlockRatio n r⌋₊

noncomputable def varianceBlockCount (N n : ℕ) (r : ℝ) : ℕ :=
  ⌈(N : ℝ) / (varianceBlockLength n r : ℝ)⌉₊

lemma varianceBlockLength_pos {n : ℕ} {r : ℝ}
    (hratio : 2 ≤ varianceBlockRatio n r) :
    0 < varianceBlockLength n r := by
  rw [varianceBlockLength, Nat.floor_pos]
  linarith

lemma varianceBlockLength_le_ratio {n : ℕ} {r : ℝ} :
    (varianceBlockLength n r : ℝ) ≤ varianceBlockRatio n r := by
  exact Nat.floor_le (by unfold varianceBlockRatio; positivity)

lemma half_ratio_le_varianceBlockLength {n : ℕ} {r : ℝ}
    (hratio : 2 ≤ varianceBlockRatio n r) :
    varianceBlockRatio n r / 2 ≤ (varianceBlockLength n r : ℝ) := by
  have hlt := Nat.lt_floor_add_one (varianceBlockRatio n r)
  have hL := varianceBlockLength_pos hratio
  change varianceBlockRatio n r < (varianceBlockLength n r : ℝ) + 1 at hlt
  have hLr : (1 : ℝ) ≤ varianceBlockLength n r := by exact_mod_cast hL
  linarith

lemma varianceBlockLength_budget {n : ℕ} {r : ℝ} (hn : 0 < n) :
    4 * (varianceBlockLength n r : ℝ) * (n : ℝ) ^ 2 ≤ r ^ 2 / 40000 := by
  have hle := varianceBlockLength_le_ratio (n := n) (r := r)
  unfold varianceBlockRatio at hle
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hle (show 0 ≤ 4 * (n : ℝ) ^ 2 by positivity)
  calc
    4 * (varianceBlockLength n r : ℝ) * (n : ℝ) ^ 2 =
        (varianceBlockLength n r : ℝ) * (4 * (n : ℝ) ^ 2) := by ring
    _ ≤ (r ^ 2 / (160000 * (n : ℝ) ^ 2)) * (4 * (n : ℝ) ^ 2) := hmul
    _ = r ^ 2 / 40000 := by field_simp; ring

lemma varianceBlockCount_pos {N n : ℕ} {r : ℝ} (hN : 0 < N)
    (hL : 0 < varianceBlockLength n r) :
    0 < varianceBlockCount N n r := by
  rw [varianceBlockCount, Nat.ceil_pos]
  positivity

lemma varianceBlockCount_cover {N n : ℕ} {r : ℝ}
    (hL : 0 < varianceBlockLength n r) :
    N ≤ varianceBlockCount N n r * varianceBlockLength n r := by
  have hc := Nat.le_ceil ((N : ℝ) / (varianceBlockLength n r : ℝ))
  have hLr : (0 : ℝ) < varianceBlockLength n r := by exact_mod_cast hL
  have hm := (div_le_iff₀ hLr).mp hc
  exact_mod_cast hm

lemma varianceBlockCount_real_lt {N n : ℕ} {r : ℝ}
    (hL : 0 < varianceBlockLength n r) :
    (varianceBlockCount N n r : ℝ) <
      (N : ℝ) / varianceBlockLength n r + 1 := by
  exact Nat.ceil_lt_add_one (by positivity)

lemma varianceBlockCount_le_source {N n : ℕ} {r : ℝ}
    (hn : 0 < n) (hNn : N ≤ n) (hr : 0 < r)
    (hratio : 2 ≤ varianceBlockRatio n r) :
    (varianceBlockCount N n r : ℝ) ≤
      320000 * (n : ℝ) ^ 3 / r ^ 2 + 1 := by
  have hL := varianceBlockLength_pos hratio
  have hhalf := half_ratio_le_varianceBlockLength hratio
  have hq := (varianceBlockCount_real_lt (N := N) hL).le
  have hNr : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratioPos : 0 < varianceBlockRatio n r := lt_of_lt_of_le (by norm_num) hratio
  have hLr : (0 : ℝ) < varianceBlockLength n r := by exact_mod_cast hL
  calc
    (varianceBlockCount N n r : ℝ) ≤
        (N : ℝ) / varianceBlockLength n r + 1 := hq
    _ ≤ (N : ℝ) / (varianceBlockRatio n r / 2) + 1 := by
      gcongr
    _ ≤ (n : ℝ) / (varianceBlockRatio n r / 2) + 1 := by
      gcongr
    _ = 320000 * (n : ℝ) ^ 3 / r ^ 2 + 1 := by
      unfold varianceBlockRatio
      field_simp
      ring

/-- Deterministic variance-budget partition and composition, with the source
small-ball exponent `O(n³/r²)` and the lattice-cell loss still displayed
exactly. -/
theorem exp_neg_source_block_and_cellCost_le_hlozPathSum
    {m N n : ℕ} {δ r : ℝ}
    (hm : 0 < m) (hNpos : 0 < N) (hr : 0 < r) (hupper : m + N ≤ n)
    (hratio : 2 ≤ varianceBlockRatio n r)
    (hN : (N : ℝ) ≤ 2 * r)
    (hradius : ∀ i : Fin (N + 1),
      4 * r ≤ (corridorRadius δ (m + i) : ℝ)) :
    Real.exp (-(cellCostSum m N (fun _ ↦ 2 * (2 * r + 1)) +
        (640000 * (n : ℝ) ^ 3 / r ^ 2 + 2))) ≤
      hlozPathSum δ m N := by
  have hn : 0 < n := lt_of_lt_of_le hm (Nat.le_add_right m N) |>.trans_le hupper
  have hNn : N ≤ n := (Nat.le_add_left N m).trans hupper
  let L := varianceBlockLength n r
  let q := varianceBlockCount N n r
  have hL : 0 < L := varianceBlockLength_pos hratio
  have hq : 0 < q := varianceBlockCount_pos hNpos hL
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hcover : N ≤ q * L := varianceBlockCount_cover hL
  have hbudget : 4 * (L : ℝ) * (n : ℝ) ^ 2 ≤ r ^ 2 / 40000 :=
    varianceBlockLength_budget hn
  have hfixed := exp_neg_block_and_cellCost_le_hlozPathSum
    hm hr hL hupper hcover hbudget hN hradius
  have hqbound : (q : ℝ) ≤ 320000 * (n : ℝ) ^ 3 / r ^ 2 + 1 :=
    varianceBlockCount_le_source hn hNn hr hratio
  have hlog : Real.log 3 ≤ (2 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at this ⊢
    exact this
  have hlogpos : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
  have hcost : (q : ℝ) * Real.log 3 ≤
      640000 * (n : ℝ) ^ 3 / r ^ 2 + 2 := by
    calc
      (q : ℝ) * Real.log 3 ≤ (q : ℝ) * 2 := by gcongr
      _ ≤ (320000 * (n : ℝ) ^ 3 / r ^ 2 + 1) * 2 := by gcongr
      _ = 640000 * (n : ℝ) ^ 3 / r ^ 2 + 2 := by ring
  exact (Real.exp_le_exp.mpr (by
    apply neg_le_neg
    linarith [hcost])).trans hfixed
/-- Explicit `O(Nr/m²)` bound for the accumulated unit-cell comparison
cost. -/
lemma blockCellCost_le {m N : ℕ} {r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    cellCostSum m N (fun _ ↦ 2 * (2 * r + 1)) ≤
      (N : ℝ) * (4 * r + 3) / (m : ℝ) ^ 2 := by
  have hbase := cellCostSum_le_of_radius_le hm
    (R := fun _ : Fin N ↦ 2 * (2 * r + 1))
    (Q := 2 * (2 * r + 1)) (fun _ ↦ by positivity) (fun _ ↦ le_rfl)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    cellCostSum m N (fun _ ↦ 2 * (2 * r + 1)) ≤
        (N : ℝ) * ((8 * (2 * (2 * r + 1)) + 4) /
          (8 * (m : ℝ) ^ 2)) := hbase
    _ ≤ (N : ℝ) * ((4 * r + 3) / (m : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (div_le_iff₀ (show 0 < 8 * (m : ℝ) ^ 2 by positivity)).2
      rw [show ((4 * r + 3) / (m : ℝ) ^ 2) * (8 * (m : ℝ) ^ 2) =
        8 * (4 * r + 3) by field_simp]
      nlinarith
    _ = (N : ℝ) * (4 * r + 3) / (m : ℝ) ^ 2 := by ring

/-- Fully explicit many-path lower bound.  Its two leading terms are the
source small-ball cost `n³/r²` and the lattice-cell cost `Nr/m²`. -/
theorem exp_neg_source_explicit_le_hlozPathSum
    {m N n : ℕ} {δ r : ℝ}
    (hm : 0 < m) (hNpos : 0 < N) (hr : 0 < r) (hupper : m + N ≤ n)
    (hratio : 2 ≤ varianceBlockRatio n r)
    (hN : (N : ℝ) ≤ 2 * r)
    (hradius : ∀ i : Fin (N + 1),
      4 * r ≤ (corridorRadius δ (m + i) : ℝ)) :
    Real.exp (-(640000 * (n : ℝ) ^ 3 / r ^ 2 +
        (N : ℝ) * (4 * r + 3) / (m : ℝ) ^ 2 + 2)) ≤
      hlozPathSum δ m N := by
  have hsource := exp_neg_source_block_and_cellCost_le_hlozPathSum
    hm hNpos hr hupper hratio hN hradius
  have hcell := blockCellCost_le (N := N) hm hr
  apply (Real.exp_le_exp.mpr ?_).trans hsource
  apply neg_le_neg
  linarith
/-- The integer corridor radius dominates half the starting-scale power once
that power is at least two. -/
lemma half_rpow_le_corridorRadius {m : ℕ} {δ : ℝ}
    (hm : 0 < m) (hδ : -1 ≤ δ)
    (hpow : 2 ≤ (m : ℝ) ^ (1 + δ)) (i : ℕ) :
    (m : ℝ) ^ (1 + δ) / 2 ≤ (corridorRadius δ (m + i) : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmi : (m : ℝ) ≤ (m + i : ℕ) := by exact_mod_cast Nat.le_add_right m i
  have hexp : 0 ≤ 1 + δ := by linarith
  have hmono := Real.rpow_le_rpow hmR.le hmi hexp
  have hfloor := Nat.lt_floor_add_one (((m + i : ℕ) : ℝ) ^ (1 + δ))
  change ((m + i : ℕ) : ℝ) ^ (1 + δ) <
    (corridorRadius δ (m + i) : ℝ) + 1 at hfloor
  nlinarith

/-- Literal HLOZ power-radius specialization.  The first displayed cost is
`n³ / m^(2(1+δ))`; the second is the explicit rounding-cell cost
`N(m^(1+δ)/2+3)/m²`. -/
theorem exp_neg_power_radius_le_hlozPathSum
    {m N n : ℕ} {δ : ℝ}
    (hm : 0 < m) (hNpos : 0 < N) (hδ : -1 ≤ δ) (hupper : m + N ≤ n)
    (hpow : 2 ≤ (m : ℝ) ^ (1 + δ))
    (hratio : 2 ≤ varianceBlockRatio n ((m : ℝ) ^ (1 + δ) / 8))
    (hN : (N : ℝ) ≤ (m : ℝ) ^ (1 + δ) / 4) :
    Real.exp (-(40960000 * (n : ℝ) ^ 3 / ((m : ℝ) ^ (1 + δ)) ^ 2 +
        (N : ℝ) * ((m : ℝ) ^ (1 + δ) / 2 + 3) / (m : ℝ) ^ 2 + 2)) ≤
      hlozPathSum δ m N := by
  let a : ℝ := (m : ℝ) ^ (1 + δ)
  have ha : 0 < a := Real.rpow_pos_of_pos (by exact_mod_cast hm) _
  have hsource := exp_neg_source_explicit_le_hlozPathSum
    (δ := δ) (r := a / 8) hm hNpos (by positivity) hupper hratio (by
      dsimp [a]
      linarith) (fun i ↦ by
        dsimp [a]
        have hh := half_rpow_le_corridorRadius hm hδ hpow (i : ℕ)
        linarith)
  convert hsource using 1 <;> dsimp [a]
  · congr 2
    field_simp
    ring

/-! ### The literal `n^ρ` exponent -/

/-- If the integer block start is at least half of `n^ρ`, the variance-block
cost has exactly the source power `n^(3-2ρ(1+δ))`, with a safe numerical
constant independent of all parameters. -/
lemma blockCost_le_rhoPower
    {m n : ℕ} {rho delta : ℝ}
    (hn : 1 ≤ n) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hd0 : -1 ≤ delta) (hd1 : delta ≤ 1 / 3)
    (hmlower : (n : ℝ) ^ rho / 2 ≤ (m : ℝ)) :
    40960000 * (n : ℝ) ^ 3 / ((m : ℝ) ^ (1 + delta)) ^ 2 ≤
      655360000 * (n : ℝ) ^ (3 - 2 * rho * (1 + delta)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have he0 : 0 ≤ 1 + delta := by linarith
  have he2 : 1 + delta ≤ 2 := by linarith
  have hxpos : 0 < (n : ℝ) ^ rho := Real.rpow_pos_of_pos hnpos _
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (half_pos hxpos) hmlower
  have htwo : (2 : ℝ) ^ (1 + delta) ≤ 4 := by
    calc
      (2 : ℝ) ^ (1 + delta) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) he2
      _ = 4 := by norm_num [Real.rpow_two]
  have hpowmono : ((n : ℝ) ^ rho / 2) ^ (1 + delta) ≤
      (m : ℝ) ^ (1 + delta) :=
    Real.rpow_le_rpow (by positivity) hmlower he0
  have hquarter : (n : ℝ) ^ (rho * (1 + delta)) / 4 ≤
      (m : ℝ) ^ (1 + delta) := by
    rw [Real.rpow_mul hnpos.le]
    rw [Real.div_rpow (Real.rpow_nonneg hnpos.le rho)
      (by norm_num : (0 : ℝ) ≤ 2)] at hpowmono
    have hdenpos : 0 < (2 : ℝ) ^ (1 + delta) :=
      Real.rpow_pos_of_pos (by norm_num) _
    calc
      ((n : ℝ) ^ rho) ^ (1 + delta) / 4 ≤
          ((n : ℝ) ^ rho) ^ (1 + delta) / (2 : ℝ) ^ (1 + delta) := by
        exact div_le_div_of_nonneg_left
          (Real.rpow_nonneg (Real.rpow_nonneg hnpos.le rho) (1 + delta))
          hdenpos htwo
      _ ≤ (m : ℝ) ^ (1 + delta) := hpowmono
  let y : ℝ := (n : ℝ) ^ (rho * (1 + delta))
  have hypos : 0 < y := by dsimp [y]; positivity
  have hsq : y ^ 2 / 16 ≤ ((m : ℝ) ^ (1 + delta)) ^ 2 := by
    have hq : y / 4 ≤ (m : ℝ) ^ (1 + delta) := by
      simpa [y] using hquarter
    nlinarith [sq_nonneg ((m : ℝ) ^ (1 + delta) - y / 4)]
  have hA : 0 ≤ 3 - 2 * rho * (1 + delta) := by nlinarith
  have hid : (n : ℝ) ^ 3 =
      (n : ℝ) ^ (3 - 2 * rho * (1 + delta)) * y ^ 2 := by
    dsimp [y]
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul hnpos.le]
    rw [← Real.rpow_add hnpos]
    rw [show 3 - 2 * rho * (1 + delta) + rho * (1 + delta) * 2 = 3 by ring]
    norm_num [Real.rpow_natCast]
  have hdenpos : 0 < ((m : ℝ) ^ (1 + delta)) ^ 2 := by positivity
  have hbase : y ^ 2 / ((m : ℝ) ^ (1 + delta)) ^ 2 ≤ 16 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [hsq]
  have hAn : 0 ≤ (n : ℝ) ^ (3 - 2 * rho * (1 + delta)) :=
    Real.rpow_nonneg hnpos.le _
  have hh := mul_le_mul_of_nonneg_left hbase
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40960000) hAn)
  calc
    40960000 * (n : ℝ) ^ 3 / ((m : ℝ) ^ (1 + delta)) ^ 2 =
      40960000 *
        ((n : ℝ) ^ (3 - 2 * rho * (1 + delta)) * y ^ 2) /
          ((m : ℝ) ^ (1 + delta)) ^ 2 := by rw [hid]
    _ = (40960000 * (n : ℝ) ^ (3 - 2 * rho * (1 + delta))) *
        (y ^ 2 / ((m : ℝ) ^ (1 + delta)) ^ 2) := by ring
    _ ≤ (40960000 * (n : ℝ) ^ (3 - 2 * rho * (1 + delta))) * 16 := hh
    _ = 655360000 * (n : ℝ) ^ (3 - 2 * rho * (1 + delta)) := by ring

/-- The explicit lattice-cell cost is absorbed by the same source power.
The restriction `δ ≤ 1/3` is the range used in Appendix A and makes
`2+δ-2ρ ≤ 3-2ρ(1+δ)` uniformly for `0 ≤ ρ ≤ 1`. -/
lemma cellCostTerm_le_rhoPower
    {m N n : ℕ} {rho delta : ℝ}
    (hn : 1 ≤ n) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hd0 : -1 ≤ delta) (hd1 : delta ≤ 1 / 3)
    (hmlower : (n : ℝ) ^ rho / 2 ≤ (m : ℝ))
    (hmupper : m ≤ n) (hNupper : N ≤ n) :
    (N : ℝ) * ((m : ℝ) ^ (1 + delta) / 2 + 3) / (m : ℝ) ^ 2 ≤
      16 * (n : ℝ) ^ (3 - 2 * rho * (1 + delta)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have he0 : 0 ≤ 1 + delta := by linarith
  have hxpos : 0 < (n : ℝ) ^ rho := Real.rpow_pos_of_pos hnpos _
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (half_pos hxpos) hmlower
  have hmleR : (m : ℝ) ≤ n := by exact_mod_cast hmupper
  have hNleR : (N : ℝ) ≤ n := by exact_mod_cast hNupper
  have hmpow : (m : ℝ) ^ (1 + delta) ≤ (n : ℝ) ^ (1 + delta) :=
    Real.rpow_le_rpow hmpos.le hmleR he0
  have hnone : (1 : ℝ) ≤ (n : ℝ) ^ (1 + delta) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hnR he0
    simpa using h
  have hnum : (N : ℝ) * ((m : ℝ) ^ (1 + delta) / 2 + 3) ≤
      4 * (n : ℝ) ^ (2 + delta) := by
    have hadd : (m : ℝ) ^ (1 + delta) / 2 + 3 ≤
        4 * (n : ℝ) ^ (1 + delta) := by nlinarith
    calc
      (N : ℝ) * ((m : ℝ) ^ (1 + delta) / 2 + 3) ≤
          (n : ℝ) * (4 * (n : ℝ) ^ (1 + delta)) := by
        exact mul_le_mul hNleR hadd (by positivity) (by positivity)
      _ = 4 * (n : ℝ) ^ (2 + delta) := by
        have hp : (n : ℝ) ^ (2 + delta) =
            (n : ℝ) * (n : ℝ) ^ (1 + delta) := by
          calc
            (n : ℝ) ^ (2 + delta) = (n : ℝ) ^ (1 + (1 + delta)) := by
              congr 1 <;> ring
            _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 + delta) :=
              Real.rpow_add hnpos 1 (1 + delta)
            _ = (n : ℝ) * (n : ℝ) ^ (1 + delta) := by rw [Real.rpow_one]
        rw [hp]
        ring
  have hmsq : (n : ℝ) ^ (2 * rho) / 4 ≤ (m : ℝ) ^ 2 := by
    have hs : (n : ℝ) ^ rho / 2 ≤ (m : ℝ) := hmlower
    have hs0 : 0 ≤ (n : ℝ) ^ rho / 2 := by positivity
    nlinarith [sq_nonneg ((m : ℝ) - (n : ℝ) ^ rho / 2),
      sq_nonneg ((m : ℝ) + (n : ℝ) ^ rho / 2),
      show ((n : ℝ) ^ rho) ^ 2 = (n : ℝ) ^ (2 * rho) by
        rw [← Real.rpow_two, ← Real.rpow_mul hnpos.le]; congr 1; ring]
  have hmden : 0 < (m : ℝ) ^ 2 := by positivity
  have hdiv : (N : ℝ) * ((m : ℝ) ^ (1 + delta) / 2 + 3) / (m : ℝ) ^ 2 ≤
      16 * (n : ℝ) ^ (2 + delta - 2 * rho) := by
    rw [div_le_iff₀ hmden]
    have hpnonneg : 0 ≤ (n : ℝ) ^ (2 + delta - 2 * rho) :=
      Real.rpow_nonneg hnpos.le _
    have hident : 4 * (n : ℝ) ^ (2 + delta) =
        (16 * (n : ℝ) ^ (2 + delta - 2 * rho)) *
          ((n : ℝ) ^ (2 * rho) / 4) := by
      calc
        4 * (n : ℝ) ^ (2 + delta) =
            4 * (n : ℝ) ^ ((2 + delta - 2 * rho) + 2 * rho) := by
          congr 2 <;> ring
        _ = 4 * ((n : ℝ) ^ (2 + delta - 2 * rho) *
            (n : ℝ) ^ (2 * rho)) := by rw [Real.rpow_add hnpos]
        _ = (16 * (n : ℝ) ^ (2 + delta - 2 * rho)) *
            ((n : ℝ) ^ (2 * rho) / 4) := by ring
    calc
      (N : ℝ) * ((m : ℝ) ^ (1 + delta) / 2 + 3) ≤
          4 * (n : ℝ) ^ (2 + delta) := hnum
      _ = (16 * (n : ℝ) ^ (2 + delta - 2 * rho)) *
          ((n : ℝ) ^ (2 * rho) / 4) := hident
      _ ≤ (16 * (n : ℝ) ^ (2 + delta - 2 * rho)) * (m : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hmsq (by positivity)
  have hexp : 2 + delta - 2 * rho ≤ 3 - 2 * rho * (1 + delta) := by
    nlinarith [mul_nonneg hrho0 (show 0 ≤ 1 / 3 - delta by linarith),
      mul_nonneg (show 0 ≤ 1 - rho by linarith)
        (show 0 ≤ 1 / 3 - delta by linarith)]
  exact hdiv.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hnR hexp) (by norm_num))

/-- Literal source-exponent form of Lemma A.8.  The finite-scale geometric
hypotheses are exactly those needed by the checked variance partition; the
conclusion has the published exponent
`max (3 - 2ρ(1+δ)) (2δ)`. -/
theorem exp_neg_rho_power_le_hlozPathSum
    {m N n : ℕ} {rho delta : ℝ}
    (hn : 1 ≤ n) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hd0 : -1 ≤ delta) (hd1 : delta ≤ 1 / 3)
    (hm : 0 < m) (hNpos : 0 < N) (hupper : m + N ≤ n)
    (hmlower : (n : ℝ) ^ rho / 2 ≤ (m : ℝ))
    (hmupper : m ≤ n) (hNupper : N ≤ n)
    (hpow : 2 ≤ (m : ℝ) ^ (1 + delta))
    (hratio : 2 ≤ varianceBlockRatio n ((m : ℝ) ^ (1 + delta) / 8))
    (hN : (N : ℝ) ≤ (m : ℝ) ^ (1 + delta) / 4) :
    Real.exp (-(655360100 *
        (n : ℝ) ^ max (3 - 2 * rho * (1 + delta)) (2 * delta))) ≤
      hlozPathSum delta m N := by
  have hsource := exp_neg_power_radius_le_hlozPathSum
    hm hNpos hd0 hupper hpow hratio hN
  have hblock := blockCost_le_rhoPower hn hrho0 hrho1 hd0 hd1 hmlower
  have hcell := cellCostTerm_le_rhoPower hn hrho0 hrho1 hd0 hd1
    hmlower hmupper hNupper
  let A : ℝ := 3 - 2 * rho * (1 + delta)
  have hA : 0 ≤ A := by dsimp [A]; nlinarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hone : 1 ≤ (n : ℝ) ^ A := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hnR hA
    simpa using h
  have hcost :
      40960000 * (n : ℝ) ^ 3 / ((m : ℝ) ^ (1 + delta)) ^ 2 +
          (N : ℝ) * ((m : ℝ) ^ (1 + delta) / 2 + 3) / (m : ℝ) ^ 2 + 2 ≤
        655360100 * (n : ℝ) ^ A := by
    dsimp [A] at hblock hcell ⊢
    nlinarith
  have hpowmax : (n : ℝ) ^ A ≤
      (n : ℝ) ^ max A (2 * delta) :=
    Real.rpow_le_rpow_of_exponent_le hnR (le_max_left _ _)
  calc
    Real.exp (-(655360100 *
        (n : ℝ) ^ max (3 - 2 * rho * (1 + delta)) (2 * delta))) ≤
        Real.exp (-(655360100 * (n : ℝ) ^ A)) := by
      apply Real.exp_le_exp.mpr
      dsimp [A] at hpowmax ⊢
      nlinarith
    _ ≤ Real.exp (-(40960000 * (n : ℝ) ^ 3 /
          ((m : ℝ) ^ (1 + delta)) ^ 2 +
          (N : ℝ) * ((m : ℝ) ^ (1 + delta) / 2 + 3) /
            (m : ℝ) ^ 2 + 2)) := by
      exact Real.exp_le_exp.mpr (by linarith)
    _ ≤ hlozPathSum delta m N := hsource

/-- Integer starting scale used in the literal source block
`(n^ρ,n]`. -/
noncomputable def rhoBlockStart (rho : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ rho⌋₊

lemma rhoBlockStart_lower {rho : ℝ} {n : ℕ}
    (hscale : 2 ≤ (n : ℝ) ^ rho) :
    (n : ℝ) ^ rho / 2 ≤ (rhoBlockStart rho n : ℝ) := by
  have hfloor := Nat.lt_floor_add_one ((n : ℝ) ^ rho)
  change (n : ℝ) ^ rho < (rhoBlockStart rho n : ℝ) + 1 at hfloor
  linarith

lemma rhoBlockStart_pos {rho : ℝ} {n : ℕ}
    (hscale : 2 ≤ (n : ℝ) ^ rho) : 0 < rhoBlockStart rho n := by
  rw [rhoBlockStart, Nat.floor_pos]
  linarith

lemma rhoBlockStart_le {rho : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (_hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    rhoBlockStart rho n ≤ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := Real.rpow_le_rpow_of_exponent_le hnR hrho1
  have hfloor := Nat.floor_le
    (Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) rho)
  rw [Real.rpow_one] at hp
  have hreal : (rhoBlockStart rho n : ℝ) ≤ n := by
    change (⌊(n : ℝ) ^ rho⌋₊ : ℝ) ≤ n
    exact hfloor.trans hp
  exact_mod_cast hreal

lemma rhoBlockStart_lt {rho : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (_hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    rhoBlockStart rho n < n := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hp : (n : ℝ) ^ rho < (n : ℝ) ^ (1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hnR hrho1
  have hfloor := Nat.floor_le
    (Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) rho)
  rw [Real.rpow_one] at hp
  have hreal : (rhoBlockStart rho n : ℝ) < n := by
    change (⌊(n : ℝ) ^ rho⌋₊ : ℝ) < n
    exact hfloor.trans_lt hp
  exact_mod_cast hreal

/-- Finite literal source block.  A single transparent growth inequality
discharges the block length, variance budget, and rounding-corridor
requirements of the general estimate. -/
theorem exp_neg_rho_floor_le_hlozPathSum
    {n : ℕ} {rho delta : ℝ}
    (hn : 2 ≤ n) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hd0 : -1 ≤ delta) (hd1 : delta ≤ 1 / 3)
    (hscale : 2 ≤ (n : ℝ) ^ rho)
    (hlarge : 5000 * (n : ℝ) ≤
      (rhoBlockStart rho n : ℝ) ^ (1 + delta)) :
    Real.exp (-(655360100 *
        (n : ℝ) ^ max (3 - 2 * rho * (1 + delta)) (2 * delta))) ≤
      hlozPathSum delta (rhoBlockStart rho n) (n - rhoBlockStart rho n) := by
  let m := rhoBlockStart rho n
  let N := n - m
  have hm : 0 < m := rhoBlockStart_pos hscale
  have hmle : m ≤ n := rhoBlockStart_le (by omega) hrho0 hrho1.le
  have hmlt : m < n := rhoBlockStart_lt hn hrho0 hrho1
  have hNpos : 0 < N := by dsimp [N]; omega
  have hupper : m + N ≤ n := by dsimp [N]; omega
  have hmlower : (n : ℝ) ^ rho / 2 ≤ (m : ℝ) := rhoBlockStart_lower hscale
  have hNupper : N ≤ n := by dsimp [N]; omega
  have hpow : 2 ≤ (m : ℝ) ^ (1 + delta) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [m] at hlarge ⊢
    nlinarith
  have hN : (N : ℝ) ≤ (m : ℝ) ^ (1 + delta) / 4 := by
    have hNR : (N : ℝ) ≤ n := by exact_mod_cast hNupper
    dsimp [m] at hlarge ⊢
    nlinarith
  have hratio : 2 ≤ varianceBlockRatio n ((m : ℝ) ^ (1 + delta) / 8) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 5000 * (n : ℝ) ≤ (m : ℝ) ^ (1 + delta) := by
      simpa [m] using hlarge
    have ha0 : 0 ≤ (m : ℝ) ^ (1 + delta) := Real.rpow_nonneg (by positivity) _
    have hsq : (5000 * (n : ℝ)) ^ 2 ≤ ((m : ℝ) ^ (1 + delta)) ^ 2 := by
      nlinarith [sq_nonneg ((m : ℝ) ^ (1 + delta) - 5000 * (n : ℝ))]
    unfold varianceBlockRatio
    rw [show (((m : ℝ) ^ (1 + delta) / 8) ^ 2 /
        (160000 * (n : ℝ) ^ 2)) =
        ((m : ℝ) ^ (1 + delta)) ^ 2 /
          (10240000 * (n : ℝ) ^ 2) by ring]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 10240000 * (n : ℝ) ^ 2)]
    nlinarith
  exact exp_neg_rho_power_le_hlozPathSum
    (show 1 ≤ n by omega) hrho0 hrho1.le hd0 hd1 hm hNpos hupper
    hmlower hmle hNupper hpow hratio hN

/-- The scale inequality in `exp_neg_rho_floor_le_hlozPathSum` holds
eventually whenever the corridor grows faster than the block length, i.e.
`ρ(1+δ)>1`. -/
theorem eventually_rhoBlockStart_growth
    {rho delta : ℝ} (hrho : 0 < rho) (hd0 : -1 ≤ delta)
    (hd1 : delta ≤ 1 / 3) (hcritical : 1 < rho * (1 + delta)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 ≤ (n : ℝ) ^ rho ∧
        5000 * (n : ℝ) ≤ (rhoBlockStart rho n : ℝ) ^ (1 + delta) := by
  let c : ℝ := rho * (1 + delta) - 1
  have hc : 0 < c := by dsimp [c]; linarith
  have htC : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ c)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hc).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have htR : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ rho)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hrho).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hevC := htC.eventually (Filter.eventually_ge_atTop (20000 : ℝ))
  have hevR := htR.eventually (Filter.eventually_ge_atTop (2 : ℝ))
  filter_upwards [hevC, hevR, Filter.eventually_ge_atTop (1 : ℕ)] with n hnC hnR hn
  refine ⟨hnR, ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he0 : 0 ≤ 1 + delta := by linarith
  have he2 : 1 + delta ≤ 2 := by linarith
  have hstart := rhoBlockStart_lower hnR
  have hpowmono : ((n : ℝ) ^ rho / 2) ^ (1 + delta) ≤
      (rhoBlockStart rho n : ℝ) ^ (1 + delta) :=
    Real.rpow_le_rpow (by positivity) hstart he0
  have htwo : (2 : ℝ) ^ (1 + delta) ≤ 4 := by
    calc
      (2 : ℝ) ^ (1 + delta) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) he2
      _ = 4 := by norm_num [Real.rpow_two]
  have hquarter : (n : ℝ) ^ (rho * (1 + delta)) / 4 ≤
      (rhoBlockStart rho n : ℝ) ^ (1 + delta) := by
    rw [Real.rpow_mul hnpos.le]
    rw [Real.div_rpow (Real.rpow_nonneg hnpos.le rho)
      (by norm_num : (0 : ℝ) ≤ 2)] at hpowmono
    exact (div_le_div_of_nonneg_left
      (Real.rpow_nonneg (Real.rpow_nonneg hnpos.le rho) (1 + delta))
      (Real.rpow_pos_of_pos (by norm_num) _) htwo).trans hpowmono
  have hid : (n : ℝ) ^ (rho * (1 + delta)) =
      (n : ℝ) ^ c * (n : ℝ) := by
    calc
      (n : ℝ) ^ (rho * (1 + delta)) = (n : ℝ) ^ (c + 1) := by
        congr 1
        dsimp [c]
        ring
      _ = (n : ℝ) ^ c * (n : ℝ) ^ (1 : ℝ) := Real.rpow_add hnpos c 1
      _ = (n : ℝ) ^ c * (n : ℝ) := by rw [Real.rpow_one]
  have hmul : 20000 * (n : ℝ) ≤ (n : ℝ) ^ c * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hnC (by positivity)
  rw [hid] at hquarter
  linarith

/-- Premise-free eventual form of the published Lemma A.8 block estimate,
including the integer floor in the starting scale. -/
theorem eventually_exp_neg_rho_floor_le_hlozPathSum
    {rho delta : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hd0 : -1 ≤ delta) (hd1 : delta ≤ 1 / 3)
    (hcritical : 1 < rho * (1 + delta)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (-(655360100 *
          (n : ℝ) ^ max (3 - 2 * rho * (1 + delta)) (2 * delta))) ≤
        hlozPathSum delta (rhoBlockStart rho n) (n - rhoBlockStart rho n) := by
  filter_upwards [eventually_rhoBlockStart_growth hrho0 hd0 hd1 hcritical,
    Filter.eventually_ge_atTop (2 : ℕ)] with n hgrowth hn
  exact exp_neg_rho_floor_le_hlozPathSum hn hrho0.le hrho1 hd0 hd1
    hgrowth.1 hgrowth.2


lemma realPathOfIncrements_eq_gaussianPartialSum {n : ℕ} (ω : ℕ → ℝ)
    (i : Fin (n + 1)) :
    realPathOfIncrements (fun j : Fin (n + 1) ↦ ω j) i.succ =
      gaussianPartialSum i ω := by
  change (∑ j : Fin (i.val + 1), ω j) =
    ∑ j ∈ Finset.range (i.val + 1), ω j
  exact Fin.sum_univ_eq_sum_range (fun j ↦ ω j) (i.val + 1)

/-- The maximal-partial-sum event used by the Gaussian block estimate is a
subset of the cumulative-increment corridor used by the lattice transfer. -/
lemma gaussianBlockSafeEvent_subset_incrementCorridorEvent
    (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    gaussianBlockSafeEvent n R ⊆ incrementCorridorEvent (n + 1) R := by
  intro ω hω i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change |∑ j : Fin 0, ω j.val| ≤ R
    simpa using hR
  · rw [realPathOfIncrements_eq_gaussianPartialSum]
    have hjmem : j.val ∈ Finset.range (n + 1) := by simp [j.isLt]
    have hsqle : (gaussianPartialSum j ω) ^ 2 ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ (gaussianPartialSum k ω) ^ 2) :=
      Finset.le_sup' (fun k ↦ (gaussianPartialSum k ω) ^ 2) hjmem
    have hsq : (gaussianPartialSum j ω) ^ 2 < R ^ 2 := hsqle.trans_lt hω
    exact (abs_lt_of_sq_lt_sq hsq hR).le

/-- A checked interface from the maximal-partial-sum event furnished by the
Gaussian estimates to the literal source lattice sum. -/
theorem gaussianBlockSafeEvent_mass_le_hlozPathSum
    {m n : ℕ} (hm : 0 < m) {δ R : ℝ} (hR : 0 ≤ R)
    (hN : ((n + 1 : ℕ) : ℝ) ≤ R)
    (hradius : ∀ i : Fin (n + 2),
      2 * R ≤ (corridorRadius δ (m + i) : ℝ)) :
    Real.exp (-cellCostSum m (n + 1) (fun _ ↦ 2 * (R + 1))) *
        (gaussianProductMeasure fun i ↦ hlozIncrementVariance (m + i)).real
          (gaussianBlockSafeEvent n R) ≤
      hlozPathSum δ m (n + 1) := by
  have hmass :
      (gaussianProductMeasure fun i ↦ hlozIncrementVariance (m + i)).real
          (gaussianBlockSafeEvent n R) ≤
        (gaussianProductMeasure fun i ↦ hlozIncrementVariance (m + i)).real
          (incrementCorridorEvent (n + 1) R) :=
    measureReal_mono (gaussianBlockSafeEvent_subset_incrementCorridorEvent n hR)
  exact (mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le).trans
    (gaussianIncrementCorridor_mass_le_hlozPathSum hm hR hN hradius)

/-! ## Exact A.12 block concatenation

The source obtains a full corridor estimate by deleting finitely many bridge
transitions, applying Lemma A.8 independently on the resulting blocks, and
then restoring the bridges.  The results below formalize the exact finite
factorization and an explicit uniform cost for one restored bridge.
-/

/-- Concatenate two paths separated by one transition. -/
def joinPath {N₁ N₂ : ℕ} (p : Path N₁) (q : Path N₂) :
    Path (N₁ + 1 + N₂) :=
  fun i ↦ Fin.append p q (Fin.cast (by omega) i)

@[simp] lemma joinPath_left {N₁ N₂ : ℕ} (p : Path N₁) (q : Path N₂)
    (i : Fin (N₁ + 1)) :
    joinPath p q (Fin.castAdd (N₂ + 1) i) = p i := by
  unfold joinPath
  have hi : Fin.cast (by omega) (Fin.castAdd (N₂ + 1) i) =
      Fin.castAdd (N₂ + 1) i := by apply Fin.ext; rfl
  rw [hi]
  exact Fin.append_left p q i

@[simp] lemma joinPath_right {N₁ N₂ : ℕ} (p : Path N₁) (q : Path N₂)
    (i : Fin (N₂ + 1)) :
    joinPath p q (Fin.natAdd (N₁ + 1) i) = q i := by
  unfold joinPath
  have hi : Fin.cast (by omega) (Fin.natAdd (N₁ + 1) i) =
      Fin.natAdd (N₁ + 1) i := by apply Fin.ext; rfl
  rw [hi]
  exact Fin.append_right p q i

lemma joinPath_injective {N₁ N₂ : ℕ} :
    Function.Injective (fun pq : Path N₁ × Path N₂ ↦ joinPath pq.1 pq.2) := by
  intro a b h
  apply Prod.ext
  · funext i
    have := congrFun h (Fin.castAdd (N₂ + 1) i)
    simpa using this
  · funext i
    have := congrFun h (Fin.natAdd (N₁ + 1) i)
    simpa using this

lemma joinPath_mem_hlozCorridorPaths_iff {delta : ℝ} {m N₁ N₂ : ℕ}
    (p : Path N₁) (q : Path N₂) :
    joinPath p q ∈ hlozCorridorPaths delta m (N₁ + 1 + N₂) ↔
      p ∈ hlozCorridorPaths delta m N₁ ∧
      q ∈ hlozCorridorPaths delta (m + N₁ + 1) N₂ := by
  simp only [hlozCorridorPaths, mem_corridorPaths]
  constructor
  · intro h
    constructor
    · intro i
      have hi := h (Fin.castAdd (N₂ + 1) i)
      simpa [joinPath, Nat.add_assoc] using hi
    · intro i
      have hi := h (Fin.natAdd (N₁ + 1) i)
      simpa [joinPath, Nat.add_assoc, Nat.add_left_comm] using hi
  · rintro ⟨hp, hq⟩ i
    refine Fin.addCases (m := N₁ + 1) (n := N₂ + 1) ?_ ?_ i
    · intro j
      simpa [joinPath, Nat.add_assoc] using hp j
    · intro j
      simpa [joinPath, Nat.add_assoc, Nat.add_left_comm] using hq j

/-- The weight of a concatenated path is the two block weights times the
single transition across their gap. -/
lemma pathWeight_joinPath {m N₁ N₂ : ℕ} (p : Path N₁) (q : Path N₂) :
    pathWeight m (N₁ + 1 + N₂) (joinPath p q) =
      pathWeight m N₁ p * b (m + N₁) (p (Fin.last N₁)) (q 0) *
        pathWeight (m + N₁ + 1) N₂ q := by
  unfold pathWeight
  rw [Fin.prod_univ_add]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.coe_castAdd, Fin.coe_castSucc,
    Fin.coe_natAdd, Fin.val_last]
  congr 1
  · congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      have h₁ : (Fin.castAdd N₂ i.castSucc).castSucc =
          Fin.castAdd (N₂ + 1) i.castSucc := by apply Fin.ext; rfl
      have h₂ : (Fin.castAdd N₂ i.castSucc).succ =
          Fin.castAdd (N₂ + 1) i.succ := by apply Fin.ext; rfl
      rw [h₁, h₂, joinPath_left, joinPath_left]
    ·
      have h₁ : (Fin.castAdd N₂ (Fin.last N₁)).castSucc =
          Fin.castAdd (N₂ + 1) (Fin.last N₁) := by apply Fin.ext; rfl
      have h₂ : (Fin.castAdd N₂ (Fin.last N₁)).succ =
          Fin.natAdd (N₁ + 1) (0 : Fin (N₂ + 1)) := by apply Fin.ext; rfl
      rw [h₁, h₂, joinPath_left, joinPath_right]
  · apply Finset.prod_congr rfl
    intro i hi
    congr 1
    · omega
    ·
      have h₁ : (Fin.natAdd (N₁ + 1) i).castSucc =
          Fin.natAdd (N₁ + 1) i.castSucc := by apply Fin.ext; rfl
      rw [h₁, joinPath_right]
    ·
      have h₂ : (Fin.natAdd (N₁ + 1) i).succ =
          Fin.natAdd (N₁ + 1) i.succ := by apply Fin.ext; rfl
      rw [h₂, joinPath_right]

noncomputable def joinPathFamily {N₁ N₂ : ℕ}
    (P : Finset (Path N₁)) (Q : Finset (Path N₂)) :
    Finset (Path (N₁ + 1 + N₂)) := by
  classical
  exact (P ×ˢ Q).image (fun pq ↦ joinPath pq.1 pq.2)

lemma joinPathFamily_subset_hlozCorridorPaths {delta : ℝ} {m N₁ N₂ : ℕ} :
    joinPathFamily (hlozCorridorPaths delta m N₁)
        (hlozCorridorPaths delta (m + N₁ + 1) N₂) ⊆
      hlozCorridorPaths delta m (N₁ + 1 + N₂) := by
  classical
  intro r hr
  rw [joinPathFamily, Finset.mem_image] at hr
  rcases hr with ⟨pq, hpq, rfl⟩
  rw [joinPath_mem_hlozCorridorPaths_iff]
  exact Finset.mem_product.mp hpq

lemma pathSum_joinPathFamily {m N₁ N₂ : ℕ}
    (P : Finset (Path N₁)) (Q : Finset (Path N₂)) :
    pathSum m (N₁ + 1 + N₂) (joinPathFamily P Q) =
      ∑ p ∈ P, ∑ q ∈ Q,
        pathWeight m N₁ p * b (m + N₁) (p (Fin.last N₁)) (q 0) *
          pathWeight (m + N₁ + 1) N₂ q := by
  classical
  unfold pathSum joinPathFamily
  rw [Finset.sum_image (joinPath_injective.injOn)]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact pathWeight_joinPath p q

/-- Abstract two-block lower bound: a uniform lower bound on the deleted
bridge transition multiplies the two independent corridor sums. -/
theorem mul_hlozPathSum_le_hlozPathSum_of_bridge
    {delta c : ℝ} {m N₁ N₂ : ℕ}
    (hbridge : ∀ p ∈ hlozCorridorPaths delta m N₁,
      ∀ q ∈ hlozCorridorPaths delta (m + N₁ + 1) N₂,
        c ≤ b (m + N₁) (p (Fin.last N₁)) (q 0)) :
    c * hlozPathSum delta m N₁ *
        hlozPathSum delta (m + N₁ + 1) N₂ ≤
      hlozPathSum delta m (N₁ + 1 + N₂) := by
  let P := hlozCorridorPaths delta m N₁
  let Q := hlozCorridorPaths delta (m + N₁ + 1) N₂
  calc
    c * hlozPathSum delta m N₁ *
        hlozPathSum delta (m + N₁ + 1) N₂ =
        ∑ p ∈ P, ∑ q ∈ Q,
          c * pathWeight m N₁ p * pathWeight (m + N₁ + 1) N₂ q := by
      simp only [hlozPathSum, pathSum, P, Q]
      calc
        c * (∑ p ∈ hlozCorridorPaths delta m N₁, pathWeight m N₁ p) *
            ∑ q ∈ hlozCorridorPaths delta (m + N₁ + 1) N₂,
              pathWeight (m + N₁ + 1) N₂ q =
            (∑ p ∈ hlozCorridorPaths delta m N₁, pathWeight m N₁ p) *
              (c * ∑ q ∈ hlozCorridorPaths delta (m + N₁ + 1) N₂,
                pathWeight (m + N₁ + 1) N₂ q) := by ring
        _ = (∑ p ∈ hlozCorridorPaths delta m N₁, pathWeight m N₁ p) *
              (∑ q ∈ hlozCorridorPaths delta (m + N₁ + 1) N₂,
                c * pathWeight (m + N₁ + 1) N₂ q) := by rw [Finset.mul_sum]
        _ = ∑ p ∈ hlozCorridorPaths delta m N₁,
              ∑ q ∈ hlozCorridorPaths delta (m + N₁ + 1) N₂,
                c * pathWeight m N₁ p * pathWeight (m + N₁ + 1) N₂ q := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
    _ ≤ ∑ p ∈ P, ∑ q ∈ Q,
        pathWeight m N₁ p * b (m + N₁) (p (Fin.last N₁)) (q 0) *
          pathWeight (m + N₁ + 1) N₂ q := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have h := mul_le_mul_of_nonneg_left
        (hbridge p (by simpa [P] using hp) q (by simpa [Q] using hq))
        (pathWeight_nonneg m N₁ p)
      have h' := mul_le_mul_of_nonneg_right h
        (pathWeight_nonneg (m + N₁ + 1) N₂ q)
      nlinarith
    _ = pathSum m (N₁ + 1 + N₂) (joinPathFamily P Q) := by
      rw [pathSum_joinPathFamily]
    _ ≤ hlozPathSum delta m (N₁ + 1 + N₂) := by
      unfold hlozPathSum pathSum
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by simpa [P, Q] using
          (joinPathFamily_subset_hlozCorridorPaths
            (delta := delta) (m := m) (N₁ := N₁) (N₂ := N₂)))
        (fun i hi hnot ↦ pathWeight_nonneg _ _ _)

/-- Uniform lower bound for a Gaussian bridge between two integer windows. -/
lemma exp_neg_log_add_radiusCost_le_b {ell n R₁ R₂ : ℕ} {k₁ k₂ : ℤ}
    (hell : 0 < ell) (helln : ell ≤ n)
    (hk₁ : |k₁| ≤ (R₁ : ℤ)) (hk₂ : |k₂| ≤ (R₂ : ℤ)) :
    Real.exp (-(Real.log (8 * (n : ℝ)) +
        ((R₁ + R₂ : ℕ) : ℝ) ^ 2 / (8 * (ell : ℝ) ^ 2))) ≤
      b ell k₁ k₂ := by
  have hn : (0 : ℝ) < 8 * n := by
    have : 0 < n := hell.trans_le helln
    positivity
  have hnorm : (8 * (n : ℝ))⁻¹ ≤
      (Real.sqrt (2 * Real.pi) * (2 * (ell : ℝ)))⁻¹ := by
    simpa [b_zero_zero] using
      (one_div_eight_mul_upper_le_b_zero (ℓ := ell) (n := n) hell helln)
  have hk₁R : |(k₁ : ℝ)| ≤ R₁ := by exact_mod_cast hk₁
  have hk₂R : |(k₂ : ℝ)| ≤ R₂ := by exact_mod_cast hk₂
  have habs : |(k₁ : ℝ) - k₂| ≤ (R₁ + R₂ : ℕ) := by
    calc
      |(k₁ : ℝ) - k₂| ≤ |(k₁ : ℝ)| + |(k₂ : ℝ)| := abs_sub _ _
      _ ≤ R₁ + R₂ := add_le_add hk₁R hk₂R
      _ = (R₁ + R₂ : ℕ) := by norm_num
  have hden : 0 < 8 * (ell : ℝ) ^ 2 := by positivity
  have haction :
      (((k₁ : ℝ) - k₂) ^ 2 / (8 * (ell : ℝ) ^ 2)) ≤
        ((R₁ + R₂ : ℕ) : ℝ) ^ 2 / (8 * (ell : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_right ?_ hden.le
    rw [sq_le_sq]
    have hRnonneg : (0 : ℝ) ≤ ((R₁ + R₂ : ℕ) : ℝ) := by positivity
    rw [abs_of_nonneg hRnonneg]
    exact habs
  unfold b
  calc
    Real.exp (-(Real.log (8 * (n : ℝ)) +
        ((R₁ + R₂ : ℕ) : ℝ) ^ 2 / (8 * (ell : ℝ) ^ 2))) =
        (8 * (n : ℝ))⁻¹ * Real.exp
          (-(((R₁ + R₂ : ℕ) : ℝ) ^ 2 / (8 * (ell : ℝ) ^ 2))) := by
      rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hn]
    _ ≤ (Real.sqrt (2 * Real.pi) * (2 * (ell : ℝ)))⁻¹ *
        Real.exp (-(((k₁ : ℝ) - k₂) ^ 2 / (8 * (ell : ℝ) ^ 2))) := by
      exact mul_le_mul hnorm (Real.exp_le_exp.mpr (by linarith))
        (Real.exp_pos _).le (by positivity)

/-- Exact one-cut form of the source's A.12 decomposition.  Removing the
transition at scale `m + N₁` factorizes the two corridor sums; restoring it
costs only the displayed uniform lower bound for that single Gaussian
kernel. -/
theorem exp_bridgeCost_mul_hlozPathSums_le
    {delta : ℝ} {m N₁ N₂ n : ℕ} (hm : 0 < m)
    (hupper : m + N₁ ≤ n) :
    Real.exp (-(Real.log (8 * (n : ℝ)) +
        ((corridorRadius delta (m + N₁) +
          corridorRadius delta (m + N₁ + 1) : ℕ) : ℝ) ^ 2 /
            (8 * ((m + N₁ : ℕ) : ℝ) ^ 2))) *
        hlozPathSum delta m N₁ *
          hlozPathSum delta (m + N₁ + 1) N₂ ≤
      hlozPathSum delta m (N₁ + 1 + N₂) := by
  apply mul_hlozPathSum_le_hlozPathSum_of_bridge
  intro p hp q hq
  apply exp_neg_log_add_radiusCost_le_b (by omega) hupper
  · have h := mem_corridorPaths.mp hp (Fin.last N₁)
    simpa [Fin.val_last] using h
  · have h := mem_corridorPaths.mp hq (0 : Fin (N₂ + 1))
    simpa using h

/-- The floored source radius at one bridge has the expected
`O(n^(2δ))` quadratic cost. -/
lemma corridorRadius_cast_le_self (delta : ℝ) (ell : ℕ) :
    (corridorRadius delta ell : ℝ) ≤ (ell : ℝ) ^ (1 + delta) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma bridgeRadiusCost_le_four_rpow {delta : ℝ}
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) {ell n : ℕ}
    (hell : 1 ≤ ell) (helln : ell + 1 ≤ n) :
    ((corridorRadius delta ell + corridorRadius delta (ell + 1) : ℕ) : ℝ) ^ 2 /
        (8 * (ell : ℝ) ^ 2) ≤
      4 * (n : ℝ) ^ (2 * delta) := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hell0 : (0 : ℝ) < ell := lt_of_lt_of_le zero_lt_one hellR
  have hnR : (ell : ℝ) ≤ n := by exact_mod_cast (by omega : ell ≤ n)
  have hexp0 : 0 ≤ 1 + delta := by linarith
  have hexp2 : 1 + delta ≤ 2 := by linarith
  have hsucc : ((ell + 1 : ℕ) : ℝ) ≤ 2 * ell := by
    norm_num
    linarith
  have hrpowSucc : ((ell + 1 : ℕ) : ℝ) ^ (1 + delta) ≤
      (2 * (ell : ℝ)) ^ (1 + delta) :=
    Real.rpow_le_rpow (by positivity) hsucc hexp0
  have htwoPow : (2 : ℝ) ^ (1 + delta) ≤ 4 := by
    calc
      (2 : ℝ) ^ (1 + delta) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp2
      _ = 4 := by norm_num [Real.rpow_two]
  have hrpowSucc' : ((ell + 1 : ℕ) : ℝ) ^ (1 + delta) ≤
      4 * (ell : ℝ) ^ (1 + delta) := by
    calc
      ((ell + 1 : ℕ) : ℝ) ^ (1 + delta) ≤
          (2 * (ell : ℝ)) ^ (1 + delta) := hrpowSucc
      _ = (2 : ℝ) ^ (1 + delta) * (ell : ℝ) ^ (1 + delta) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hell0.le]
      _ ≤ 4 * (ell : ℝ) ^ (1 + delta) := by
        gcongr
  have hRsum :
      ((corridorRadius delta ell + corridorRadius delta (ell + 1) : ℕ) : ℝ) ≤
        5 * (ell : ℝ) ^ (1 + delta) := by
    push_cast
    linarith [corridorRadius_cast_le_self delta ell,
      corridorRadius_cast_le_self delta (ell + 1)]
  have hpowId : ((ell : ℝ) ^ (1 + delta)) ^ 2 =
      (ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * delta) := by
    calc
      ((ell : ℝ) ^ (1 + delta)) ^ 2 =
          (ell : ℝ) ^ ((1 + delta) * 2) := by
        rw [Real.rpow_mul hell0.le]
        norm_num [Real.rpow_two]
      _ = (ell : ℝ) ^ (2 + 2 * delta) := by congr 1; ring
      _ = (ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * delta) := by
        rw [Real.rpow_add hell0]
        norm_num [Real.rpow_two]
  have hRsq :
      (((corridorRadius delta ell + corridorRadius delta (ell + 1) : ℕ) : ℝ) ^ 2) ≤
        25 * ((ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * delta)) := by
    have hs := sq_le_sq₀ (by positivity : (0 : ℝ) ≤
      ((corridorRadius delta ell + corridorRadius delta (ell + 1) : ℕ) : ℝ))
      (by positivity : (0 : ℝ) ≤ 5 * (ell : ℝ) ^ (1 + delta))
    have := hs.mpr hRsum
    rw [mul_pow, hpowId] at this
    norm_num at this ⊢
    exact this
  have hnPow : (ell : ℝ) ^ (2 * delta) ≤ (n : ℝ) ^ (2 * delta) :=
    Real.rpow_le_rpow hell0.le hnR (by positivity)
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (ell : ℝ) ^ 2)]
  have hellsq : 0 < (ell : ℝ) ^ 2 := sq_pos_of_pos hell0
  nlinarith

/-- The normalization and quadratic parts of one bridge together are still
of source order `n^(2δ)`.  The coefficient is explicit and is allowed to
depend on the fixed corridor exponent `δ`. -/
lemma bridgeCost_le_sourcePower {delta : ℝ}
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) {ell n : ℕ}
    (hell : 1 ≤ ell) (helln : ell + 1 ≤ n) :
    Real.log (8 * (n : ℝ)) +
        ((corridorRadius delta ell + corridorRadius delta (ell + 1) : ℕ) : ℝ) ^ 2 /
          (8 * (ell : ℝ) ^ 2) ≤
      (4 + 64 / (2 * delta)) * (n : ℝ) ^ (2 * delta) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have ha0 : 0 < 2 * delta := by positivity
  have ha2 : 2 * delta ≤ 2 := by linarith
  have h8pow : (8 : ℝ) ^ (2 * delta) ≤ 64 := by
    calc
      (8 : ℝ) ^ (2 * delta) ≤ (8 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2
      _ = 64 := by norm_num [Real.rpow_two]
  have hlog : Real.log (8 * (n : ℝ)) ≤
      (64 / (2 * delta)) * (n : ℝ) ^ (2 * delta) := by
    calc
      Real.log (8 * (n : ℝ)) ≤
          (8 * (n : ℝ)) ^ (2 * delta) / (2 * delta) :=
        Real.log_le_rpow_div (by positivity) ha0
      _ = ((8 : ℝ) ^ (2 * delta) * (n : ℝ) ^ (2 * delta)) /
          (2 * delta) := by rw [Real.mul_rpow (by norm_num) hn0]
      _ ≤ (64 * (n : ℝ) ^ (2 * delta)) / (2 * delta) := by
        apply div_le_div_of_nonneg_right ?_ ha0.le
        gcongr
      _ = (64 / (2 * delta)) * (n : ℝ) ^ (2 * delta) := by ring
  have hradius := bridgeRadiusCost_le_four_rpow hd0.le hd1 hell helln
  have hpow0 := Real.rpow_nonneg hn0 (2 * delta)
  nlinarith

/-- Source-scale one-cut A.12 bound, with the bridge cost already reduced to
the same `n^(2δ)` exponent that appears in Lemma A.8. -/
theorem exp_sourceBridgeCost_mul_hlozPathSums_le
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1)
    {m N₁ N₂ n : ℕ} (hm : 0 < m)
    (hupper : m + N₁ + 1 ≤ n) :
    Real.exp (-((4 + 64 / (2 * delta)) * (n : ℝ) ^ (2 * delta))) *
        hlozPathSum delta m N₁ *
          hlozPathSum delta (m + N₁ + 1) N₂ ≤
      hlozPathSum delta m (N₁ + 1 + N₂) := by
  have hcost := bridgeCost_le_sourcePower hd0 hd1
    (show 1 ≤ m + N₁ by omega) hupper
  have hexp :
      Real.exp (-((4 + 64 / (2 * delta)) * (n : ℝ) ^ (2 * delta))) ≤
        Real.exp (-(Real.log (8 * (n : ℝ)) +
          ((corridorRadius delta (m + N₁) +
            corridorRadius delta (m + N₁ + 1) : ℕ) : ℝ) ^ 2 /
              (8 * ((m + N₁ : ℕ) : ℝ) ^ 2))) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp (-((4 + 64 / (2 * delta)) * (n : ℝ) ^ (2 * delta))) *
        hlozPathSum delta m N₁ *
          hlozPathSum delta (m + N₁ + 1) N₂ ≤
      Real.exp (-(Real.log (8 * (n : ℝ)) +
          ((corridorRadius delta (m + N₁) +
            corridorRadius delta (m + N₁ + 1) : ℕ) : ℝ) ^ 2 /
              (8 * ((m + N₁ : ℕ) : ℝ) ^ 2))) *
        hlozPathSum delta m N₁ *
          hlozPathSum delta (m + N₁ + 1) N₂ := by
      gcongr <;> apply pathSum_nonneg
    _ ≤ _ := exp_bridgeCost_mul_hlozPathSums_le hm (by omega)

/-! ### Arbitrarily many A.12 blocks -/

/-- Total number of transitions after placing one deleted bridge between
successive blocks. -/
def separatedLength : List ℕ → ℕ
  | [] => 0
  | [N] => N
  | N :: N' :: Ns => N + 1 + separatedLength (N' :: Ns)

/-- Number of deleted transitions between a nonempty list of blocks. -/
def bridgeCount : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | _ :: N' :: Ns => 1 + bridgeCount (N' :: Ns)

/-- Product of the independent corridor sums after all selected bridge
transitions have been deleted. -/
noncomputable def separatedBlockProduct (delta : ℝ) : ℕ → List ℕ → ℝ
  | _, [] => 1
  | m, [N] => hlozPathSum delta m N
  | m, N :: N' :: Ns =>
      hlozPathSum delta m N *
        separatedBlockProduct delta (m + N + 1) (N' :: Ns)

lemma separatedBlockProduct_nonneg (delta : ℝ) (m : ℕ) (Ns : List ℕ) :
    0 ≤ separatedBlockProduct delta m Ns := by
  induction Ns generalizing m with
  | nil => simp [separatedBlockProduct]
  | cons N Ns ih =>
      cases Ns with
      | nil => exact pathSum_nonneg _ _ _
      | cons N' Ns =>
          simp only [separatedBlockProduct]
          exact mul_nonneg (pathSum_nonneg _ _ _) (ih (m + N + 1))

/-- Finite iteration of the exact A.12 decomposition.  Every block may have
an arbitrary length; one source-scale bridge cost is paid between consecutive
blocks.  This is the complete deterministic composition step behind A.12,
independent of the later choice of its real-power block endpoints. -/
theorem exp_multiBridgeCost_mul_separatedBlockProduct_le
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1)
    {m n : ℕ} (hm : 0 < m) (Ns : List ℕ) (hNs : Ns ≠ [])
    (hupper : m + separatedLength Ns ≤ n) :
    Real.exp (-((4 + 64 / (2 * delta)) * (n : ℝ) ^ (2 * delta) *
        (bridgeCount Ns : ℝ))) * separatedBlockProduct delta m Ns ≤
      hlozPathSum delta m (separatedLength Ns) := by
  induction Ns generalizing m with
  | nil => contradiction
  | cons N Ns ih =>
      cases Ns with
      | nil =>
          simp [bridgeCount, separatedLength, separatedBlockProduct]
      | cons N' Ns =>
          let tail := N' :: Ns
          have htail : tail ≠ [] := by simp [tail]
          have hm' : 0 < m + N + 1 := by omega
          have hupper' : m + N + 1 + separatedLength tail ≤ n := by
            simpa [tail, separatedLength, Nat.add_assoc] using hupper
          have hih := ih hm' htail hupper'
          let C : ℝ := (4 + 64 / (2 * delta)) * (n : ℝ) ^ (2 * delta)
          have hsplit :
              Real.exp (-(C * (bridgeCount (N :: tail) : ℝ))) =
                Real.exp (-C) * Real.exp (-(C * (bridgeCount tail : ℝ))) := by
            rw [← Real.exp_add]
            congr 1
            simp only [tail, bridgeCount, Nat.cast_add, Nat.cast_one]
            ring
          rw [show separatedLength (N :: tail) =
              N + 1 + separatedLength tail by simp [tail, separatedLength],
            show separatedBlockProduct delta m (N :: tail) =
              hlozPathSum delta m N *
                separatedBlockProduct delta (m + N + 1) tail by
              simp [tail, separatedBlockProduct], hsplit]
          calc
            Real.exp (-C) * Real.exp (-(C * (bridgeCount tail : ℝ))) *
                (hlozPathSum delta m N *
                  separatedBlockProduct delta (m + N + 1) tail) =
              Real.exp (-C) * hlozPathSum delta m N *
                (Real.exp (-(C * (bridgeCount tail : ℝ))) *
                  separatedBlockProduct delta (m + N + 1) tail) := by ring
            _ ≤ Real.exp (-C) * hlozPathSum delta m N *
                hlozPathSum delta (m + N + 1) (separatedLength tail) := by
              exact mul_le_mul_of_nonneg_left hih
                (mul_nonneg (Real.exp_pos _).le (pathSum_nonneg _ _ _))
            _ ≤ hlozPathSum delta m (N + 1 + separatedLength tail) := by
              exact exp_sourceBridgeCost_mul_hlozPathSums_le hd0 hd1 hm
                (by omega)

/-! ### The finite HLOZ scale iteration -/

/-- The literal real-power endpoint from HLOZ (A.12),
`q_j = floor(n^(3δ/ρ^j))`. -/
noncomputable def hlozScaleEndpoint
    (delta rho : ℝ) (n j : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (3 * delta / rho ^ j)⌋₊

/-- The published finite endpoint list `q₀,…,qₖ,n`.  Its low-scale
prefix is handled separately in Proposition A.7; the entries here mark the
A.8 blocks and the final endpoint. -/
noncomputable def hlozScaleEndpoints
    (delta rho : ℝ) (k n : ℕ) : List ℕ :=
  List.ofFn (fun j : Fin (k + 1) ↦ hlozScaleEndpoint delta rho n j) ++ [n]

@[simp] lemma hlozScaleEndpoint_zero (delta rho : ℝ) (n : ℕ) :
    hlozScaleEndpoint delta rho n 0 = ⌊(n : ℝ) ^ (3 * delta)⌋₊ := by
  simp [hlozScaleEndpoint]

@[simp] lemma length_hlozScaleEndpoints
    (delta rho : ℝ) (k n : ℕ) :
    (hlozScaleEndpoints delta rho k n).length = k + 2 := by
  simp [hlozScaleEndpoints]

@[simp] lemma get_hlozScaleEndpoints
    (delta rho : ℝ) (k n : ℕ) (j : Fin (k + 1)) :
    (hlozScaleEndpoints delta rho k n)[j] =
      hlozScaleEndpoint delta rho n j := by
  change (List.ofFn (fun j : Fin (k + 1) ↦
    hlozScaleEndpoint delta rho n j) ++ [n])[j.val] = _
  rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]

@[simp] lemma getLast_hlozScaleEndpoints
    (delta rho : ℝ) (k n : ℕ) :
    (hlozScaleEndpoints delta rho k n).getLast (by simp [hlozScaleEndpoints]) = n := by
  simp [hlozScaleEndpoints]

/-- Lowest starting scale after recursively cutting `k` source blocks from
the top.  The convention at zero blocks is `n+1`; consequently one block
starts at `floor(n^ρ)`, while the preceding block ends one scale below it.
This is the integer-safe version of the source list
`q_j = floor(n^(3δ/ρ^j))`. -/
noncomputable def iteratedRhoStart (rho : ℝ) : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | k + 1, n => iteratedRhoStart rho k (rhoBlockStart rho n - 1)

lemma tendsto_nat_sub_one_atTop {f : ℕ → ℕ}
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n ↦ f n - 1) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop] at hf ⊢
  intro N
  filter_upwards [hf (N + 1)] with n hn
  omega

lemma tendsto_rhoBlockStart_sub_one_atTop {rho : ℝ} (hrho : 0 < rho) :
    Filter.Tendsto (fun n ↦ rhoBlockStart rho n - 1)
      Filter.atTop Filter.atTop := by
  exact tendsto_nat_sub_one_atTop
    (tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop hrho).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))))

lemma tendsto_iteratedRhoStart_atTop {rho : ℝ} (hrho : 0 < rho) (k : ℕ) :
    Filter.Tendsto (iteratedRhoStart rho k) Filter.atTop Filter.atTop := by
  induction k with
  | zero =>
      simpa [iteratedRhoStart] using Filter.tendsto_add_atTop_nat 1
  | succ k ih =>
      change Filter.Tendsto
        (iteratedRhoStart rho k ∘ fun n ↦ rhoBlockStart rho n - 1)
        Filter.atTop Filter.atTop
      exact ih.comp (tendsto_rhoBlockStart_sub_one_atTop hrho)

/-- Recursive A.12 composition of any fixed number of Lemma-A.8 blocks.
Every analytic premise is discharged.  The output also records the exact
positive lowest endpoint, which is needed to transfer the resulting
Gaussian sum to the negative-binomial corridor. -/
theorem eventually_iteratedRhoStart_hlozPathSum_lower
    {rho delta : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 3)
    (hcritical : 1 < rho * (1 + delta)) (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      let m := iteratedRhoStart rho (k + 1) n
      let e := max (3 - 2 * rho * (1 + delta)) (2 * delta)
      let D := 655360100 + (4 + 64 / (2 * delta))
      0 < m ∧ m ≤ n ∧
        Real.exp (-(((k + 1 : ℕ) : ℝ) * D * (n : ℝ) ^ e)) ≤
          hlozPathSum delta m (n - m) := by
  induction k with
  | zero =>
      have hA8 := eventually_exp_neg_rho_floor_le_hlozPathSum
        hrho0 hrho1 (by linarith) hd1 hcritical
      filter_upwards [hA8, eventually_rhoBlockStart_growth hrho0
        (by linarith) hd1 hcritical,
        Filter.eventually_ge_atTop (2 : ℕ)] with n hA8n hgrowth hn
      dsimp only [iteratedRhoStart]
      have hspos := rhoBlockStart_pos hgrowth.1
      have hsle := rhoBlockStart_le (n := n) (by omega) hrho0.le hrho1.le
      have hsminus : rhoBlockStart rho n - 1 + 1 = rhoBlockStart rho n := by
        omega
      rw [hsminus]
      refine ⟨hspos, hsle, ?_⟩
      let e := max (3 - 2 * rho * (1 + delta)) (2 * delta)
      let B := 4 + 64 / (2 * delta)
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hpow : 0 ≤ (n : ℝ) ^ e := Real.rpow_nonneg (by positivity) _
      apply (Real.exp_le_exp.mpr ?_).trans hA8n
      dsimp [e, B]
      nlinarith
  | succ k ih =>
      let u : ℕ → ℕ := fun n ↦ rhoBlockStart rho n - 1
      have hu : Filter.Tendsto u Filter.atTop Filter.atTop := by
        exact tendsto_rhoBlockStart_sub_one_atTop hrho0
      have hih := hu.eventually ih
      have hA8 := eventually_exp_neg_rho_floor_le_hlozPathSum
        hrho0 hrho1 (by linarith) hd1 hcritical
      filter_upwards [hih, hA8, eventually_rhoBlockStart_growth hrho0
        (by linarith) hd1 hcritical,
        Filter.eventually_ge_atTop (2 : ℕ)] with n hihn hA8n hgrowth hn
      dsimp only [iteratedRhoStart]
      let s := rhoBlockStart rho n
      let m := iteratedRhoStart rho (k + 1) (s - 1)
      let e := max (3 - 2 * rho * (1 + delta)) (2 * delta)
      let B := 4 + 64 / (2 * delta)
      let D := 655360100 + B
      have hspos : 0 < s := rhoBlockStart_pos hgrowth.1
      have hsle : s ≤ n := rhoBlockStart_le (by omega) hrho0.le hrho1.le
      have hmpos : 0 < m := by simpa [m, s, u] using hihn.1
      have hmle : m ≤ s - 1 := by simpa [m, s, u] using hihn.2.1
      have hihbound :
          Real.exp (-(((k + 1 : ℕ) : ℝ) * D * ((s - 1 : ℕ) : ℝ) ^ e)) ≤
            hlozPathSum delta m ((s - 1) - m) := by
        simpa [m, s, u, e, D, B] using hihn.2.2
      have hA8bound : Real.exp (-(655360100 * (n : ℝ) ^ e)) ≤
          hlozPathSum delta s (n - s) := by
        simpa [s, e] using hA8n
      have he0 : 0 ≤ e := le_max_of_le_right (by linarith)
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hule : (((s - 1 : ℕ) : ℝ) ^ e) ≤ (n : ℝ) ^ e := by
        apply Real.rpow_le_rpow (by positivity) _ he0
        exact_mod_cast (show s - 1 ≤ n by omega)
      have h2de : 2 * delta ≤ e := le_max_right _ _
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hdeltaPow : (n : ℝ) ^ (2 * delta) ≤ (n : ℝ) ^ e :=
        Real.rpow_le_rpow_of_exponent_le hn1 h2de
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hD : 0 ≤ D := by dsimp [D]; positivity
      have hpow0 : 0 ≤ (n : ℝ) ^ e := Real.rpow_nonneg hn0 e
      have hkule : ((k + 1 : ℕ) : ℝ) * D *
          ((s - 1 : ℕ) : ℝ) ^ e ≤
          ((k + 1 : ℕ) : ℝ) * D * (n : ℝ) ^ e :=
        mul_le_mul_of_nonneg_left hule
          (mul_nonneg (by positivity) hD)
      have hBpow : B * (n : ℝ) ^ (2 * delta) ≤
          B * (n : ℝ) ^ e :=
        mul_le_mul_of_nonneg_left hdeltaPow hB
      have hcost : B * (n : ℝ) ^ (2 * delta) +
            ((k + 1 : ℕ) : ℝ) * D * ((s - 1 : ℕ) : ℝ) ^ e +
            655360100 * (n : ℝ) ^ e ≤
          ((k + 2 : ℕ) : ℝ) * D * (n : ℝ) ^ e := by
        calc
          _ ≤ B * (n : ℝ) ^ e +
                ((k + 1 : ℕ) : ℝ) * D * (n : ℝ) ^ e +
                655360100 * (n : ℝ) ^ e := by linarith
          _ = ((k + 2 : ℕ) : ℝ) * D * (n : ℝ) ^ e := by
            dsimp [D]
            push_cast
            ring
      have hexp :
          Real.exp (-((((k + 2 : ℕ) : ℝ) * D * (n : ℝ) ^ e))) ≤
            Real.exp (-(B * (n : ℝ) ^ (2 * delta))) *
              Real.exp (-(((k + 1 : ℕ) : ℝ) * D *
                ((s - 1 : ℕ) : ℝ) ^ e)) *
                Real.exp (-(655360100 * (n : ℝ) ^ e)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      have hcompose := exp_sourceBridgeCost_mul_hlozPathSums_le
        (N₂ := n - s) (n := n) hd0 (by linarith : delta ≤ 1) hmpos
        (show m + ((s - 1) - m) + 1 ≤ n by omega)
      refine ⟨hmpos, (hmle.trans (by omega)), ?_⟩
      calc
        Real.exp (-((↑(k + 1 + 1) *
            (655360100 + (4 + 64 / (2 * delta))) * (n : ℝ) ^
              max (3 - 2 * rho * (1 + delta)) (2 * delta)))) ≤
            Real.exp (-(B * (n : ℝ) ^ (2 * delta))) *
              Real.exp (-(((k + 1 : ℕ) : ℝ) * D *
                ((s - 1 : ℕ) : ℝ) ^ e)) *
                Real.exp (-(655360100 * (n : ℝ) ^ e)) := by
          simpa [e, D, B, Nat.add_assoc] using hexp
        _ ≤ Real.exp (-(B * (n : ℝ) ^ (2 * delta))) *
              hlozPathSum delta m ((s - 1) - m) *
                hlozPathSum delta s (n - s) := by
          calc
            Real.exp (-(B * (n : ℝ) ^ (2 * delta))) *
                Real.exp (-(((k + 1 : ℕ) : ℝ) * D *
                  ((s - 1 : ℕ) : ℝ) ^ e)) *
                  Real.exp (-(655360100 * (n : ℝ) ^ e)) ≤
                Real.exp (-(B * (n : ℝ) ^ (2 * delta))) *
                  hlozPathSum delta m ((s - 1) - m) *
                    Real.exp (-(655360100 * (n : ℝ) ^ e)) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hihbound (Real.exp_pos _).le)
                (Real.exp_pos _).le
            _ ≤ Real.exp (-(B * (n : ℝ) ^ (2 * delta))) *
                  hlozPathSum delta m ((s - 1) - m) *
                    hlozPathSum delta s (n - s) := by
              exact mul_le_mul_of_nonneg_left hA8bound
                (mul_nonneg (Real.exp_pos _).le (pathSum_nonneg _ _ _))
        _ ≤ hlozPathSum delta m (n - m) := by
          have hstart : m + ((s - 1) - m) + 1 = s := by omega
          have hlen : (s - 1) - m + 1 + (n - s) = n - m := by omega
          simpa only [B, hstart, hlen] using hcompose

end Erdos1166.HLOZLemmaA8
