/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 395.
https://www.erdosproblems.com/forum/thread/395

Informal authors:
- Xiaoyu He
- Tomasz Juškevičius
- Bhargav Narayanan
- Sam Spiro

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos395.md
-/
/-
# Erdős Problem 395

The uniform probability below is literal normalized counting measure on the
Boolean sign cube.  The main theorem proves the reverse Littlewood--Offord
lower bound at radius `√2`.

Mathematical source: X. He, T. Juškevičius, B. Narayanan, and S. Spiro,
"On the reverse Littlewood--Offord problem of Erdős" (2024).
-/

import Mathlib

open scoped BigOperators

namespace Erdos395

open Classical Finset
open ComplexConjugate

/-- A Rademacher sign encoded by a Boolean. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma sign_false : sign false = -1 := rfl
@[simp] lemma sign_true : sign true = 1 := rfl

@[simp] lemma sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> simp [sign]

/-- The signed sum associated to a point of the Boolean cube. -/
def signedSum {n : ℕ} (z : Fin n → ℂ) (ε : Fin n → Bool) : ℂ :=
  ∑ i, (sign (ε i) : ℂ) * z i

/-- Uniform probability on a nonempty finite type, as normalized cardinality. -/
noncomputable def uniformProbability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω

lemma uniformProbability_nonneg {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) : 0 ≤ uniformProbability P := by
  unfold uniformProbability
  positivity

lemma uniformProbability_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    uniformProbability P ≤ uniformProbability Q := by
  unfold uniformProbability
  rw [div_le_div_iff_of_pos_right
    (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card Ω)]
  exact_mod_cast Finset.card_le_card (by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω)

@[simp] lemma uniformProbability_true {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    uniformProbability (fun _ : Ω ↦ True) = 1 := by
  simp [uniformProbability, ne_of_gt
    (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card Ω)]

/-- If every good sign choice on a prefix has at least one good extension,
then the full good set has at least as many elements. -/
lemma card_filter_le_of_extensions {m k : ℕ}
    (P : (Fin m → Bool) → Prop) (Q : (Fin (m + k) → Bool) → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ ε, P ε → ∃ δ : Fin k → Bool, Q (Fin.append ε δ)) :
    (Finset.univ.filter P).card ≤ (Finset.univ.filter Q).card := by
  let chooseExt (x : {ε : Fin m → Bool // P ε}) : Fin k → Bool :=
    Classical.choose (h x.1 x.2)
  let f : {ε : Fin m → Bool // P ε} →
      {ε : Fin (m + k) → Bool // Q ε} := fun x ↦
    ⟨Fin.append x.1 (chooseExt x), Classical.choose_spec (h x.1 x.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hv := congrArg (fun q : {ε : Fin (m + k) → Bool // Q ε} ↦
      q.1 (Fin.castAdd k i)) hxy
    simpa [f] using hv
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_le_of_injective f hf

/-- Split a sum over a Boolean cube into the first coordinate and its tail. -/
lemma sum_cube_succ {n : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin (n + 1) → Bool) → M) :
    ∑ x : Fin (n + 1) → Bool, f x =
      ∑ b : Bool, ∑ y : Fin n → Bool, f (Fin.cons b y) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun x _ ↦ (x 0, x ∘ Fin.succ)) ?_ ?_ ?_ ?_ <;>
    simp +decide
  · exact fun a₁ a₂ h₁ h₂ ↦ funext fun i ↦ by
      induction i using Fin.inductionOn <;> simp_all +decide [funext_iff]
  · exact ⟨fun b ↦ ⟨Fin.cons false b, rfl, rfl⟩,
      fun b ↦ ⟨Fin.cons true b, rfl, rfl⟩⟩
  · exact fun x ↦ by
      congr
      ext i
      induction i using Fin.inductionOn <;> aesop

lemma signedSum_cons {n : ℕ} (z : Fin (n + 1) → ℂ) (b : Bool)
    (ε : Fin n → Bool) :
    signedSum z (Fin.cons b ε) =
      (sign b : ℂ) * z 0 + signedSum (fun i ↦ z i.succ) ε := by
  rw [signedSum, Fin.sum_univ_succ]
  simp [signedSum]

/-- Exact second moment of a complex Rademacher sum, in unnormalized form. -/
lemma sum_normSq_signedSum : ∀ n (z : Fin n → ℂ),
    (∑ ε : Fin n → Bool, Complex.normSq (signedSum z ε)) =
      (2 : ℝ) ^ n * ∑ i, Complex.normSq (z i) := by
  intro n
  induction n with
  | zero =>
      intro z
      simp [signedSum]
  | succ n ih =>
      intro z
      rw [sum_cube_succ]
      simp only [signedSum_cons]
      rw [show (∑ b : Bool, ∑ ε : Fin n → Bool,
          Complex.normSq ((sign b : ℂ) * z 0 +
            signedSum (fun i ↦ z i.succ) ε)) =
          ∑ ε : Fin n → Bool,
            (Complex.normSq ((-1 : ℂ) * z 0 +
                signedSum (fun i ↦ z i.succ) ε) +
              Complex.normSq ((1 : ℂ) * z 0 +
                signedSum (fun i ↦ z i.succ) ε)) by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ε _
        rw [Finset.sum_eq_add false true] <;> simp]
      have hpoint : ∀ w : ℂ,
          Complex.normSq ((-1 : ℂ) * z 0 + w) +
              Complex.normSq ((1 : ℂ) * z 0 + w) =
            2 * Complex.normSq (z 0) + 2 * Complex.normSq w := by
        intro w
        rw [neg_one_mul, one_mul, Complex.normSq_add, Complex.normSq_add]
        simp only [Complex.normSq_neg, neg_mul, mul_neg,
          Complex.neg_re]
        ring
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      rw [ih]
      rw [Fin.sum_univ_succ, pow_succ]
      push_cast
      ring

/-- Elementary counting form of Markov's inequality. -/
lemma counting_markov {Ω : Type*} [Fintype Ω] (g : Ω → ℝ) (c : ℝ)
    (_hc : 0 < c) (hg : ∀ ω, 0 ≤ g ω) :
    ((Finset.univ.filter fun ω ↦ c ≤ g ω).card : ℝ) * c ≤ ∑ ω, g ω := by
  have h := Finset.sum_le_sum fun x (_hx : x ∈ Finset.univ) ↦
    show (if c ≤ g x then c else 0) ≤ g x by split_ifs <;> linarith [hg x]
  simpa [Finset.sum_ite] using h

/-- Cauchy--Schwarz lower bound for the number of equal-image ordered pairs. -/
lemma card_sq_le_card_image_mul_card_eqPairs {Ω ι : Type*}
    [DecidableEq Ω] [DecidableEq ι] (s : Finset Ω) (f : Ω → ι) :
    s.card ^ 2 ≤ (s.image f).card *
      ((s.product s).filter fun p ↦ f p.1 = f p.2).card := by
  let t := s.image f
  let fiber : ι → Finset Ω := fun y ↦ s.filter fun x ↦ f x = y
  have hsum : s.card = ∑ y ∈ t, (fiber y).card := by
    simpa [t, fiber] using Finset.card_eq_sum_card_image f s
  have hpairs :
      ((s.product s).filter fun p ↦ f p.1 = f p.2).card =
        ∑ y ∈ t, (fiber y).card ^ 2 := by
    let P := (s.product s).filter fun p ↦ f p.1 = f p.2
    have hmaps : (P : Set (Ω × Ω)).MapsTo (fun p ↦ f p.1) t := by
      intro p hp
      change p ∈ P at hp
      simp only [P, Finset.mem_filter] at hp
      rcases Finset.mem_product.mp hp.1 with ⟨hp1, _hp2⟩
      exact Finset.mem_image.mpr ⟨p.1, hp1, rfl⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro y hy
    have heq : P.filter (fun p ↦ f p.1 = y) =
        (fiber y).product (fiber y) := by
      ext p
      simp only [P, fiber, Finset.mem_filter]
      aesop
    rw [heq]
    simp [Finset.card_product, pow_two]
  rw [hsum, hpairs]
  exact sq_sum_le_card_mul_sum_sq

@[simp] lemma card_signCube (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

@[simp] lemma card_univ_signCube (n : ℕ) :
    (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
  simp

/-- The second moment is at most `2^n n` when every summand is in the unit
disk.  This is the only analytic input to the collision argument. -/
lemma sum_normSq_signedSum_le {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, Complex.normSq (z i) ≤ 1) :
    (∑ ε : Fin n → Bool, Complex.normSq (signedSum z ε)) ≤
      (2 : ℝ) ^ n * n := by
  rw [sum_normSq_signedSum]
  gcongr
  simpa using Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) ↦ hz i

/-- At least half of all sign sums lie in the disk of squared radius `2n`. -/
lemma half_cube_le_card_good {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz : ∀ i, Complex.normSq (z i) ≤ 1) :
    (2 : ℝ) ^ n ≤ 2 *
      ((Finset.univ.filter fun ε : Fin n → Bool ↦
        Complex.normSq (signedSum z ε) < 2 * n).card : ℝ) := by
  let good := Finset.univ.filter fun ε : Fin n → Bool ↦
    Complex.normSq (signedSum z ε) < 2 * n
  let bad := Finset.univ.filter fun ε : Fin n → Bool ↦
    2 * n ≤ Complex.normSq (signedSum z ε)
  have hmarkov := counting_markov
    (fun ε : Fin n → Bool ↦ Complex.normSq (signedSum z ε))
    (2 * (n : ℝ)) (by positivity) (fun ε ↦ Complex.normSq_nonneg _)
  have hbad : 2 * (bad.card : ℝ) ≤ (2 : ℝ) ^ n := by
    have hmoment := sum_normSq_signedSum_le z hz
    change (bad.card : ℝ) * (2 * n) ≤
      ∑ ε : Fin n → Bool, Complex.normSq (signedSum z ε) at hmarkov
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith
  have hpartition : good.card + bad.card = 2 ^ n := by
    rw [← card_univ_signCube n]
    have hdisj : Disjoint good bad := by
      rw [Finset.disjoint_left]
      intro ε hgood hbad'
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hgood
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hbad'
      exact (not_le_of_gt hgood) hbad'
    have hunion : good ∪ bad = (Finset.univ : Finset (Fin n → Bool)) := by
      ext ε
      simp only [good, bad, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro _
        trivial
      · intro _
        exact lt_or_ge (Complex.normSq (signedSum z ε)) (2 * (n : ℝ))
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  change (2 : ℝ) ^ n ≤ 2 * (good.card : ℝ)
  have hpartition' : (good.card : ℝ) + bad.card = (2 : ℝ) ^ n := by
    exact_mod_cast hpartition
  linarith

/-- The integer grid cell used to discretize a complex number. -/
noncomputable def gridCell (L : ℕ) (w : ℂ) : ℤ × ℤ :=
  (⌊(L : ℝ) * w.re⌋, ⌊(L : ℝ) * w.im⌋)

/-- The elementary square-root estimate needed for the grid box. -/
lemma succ_sqrt_sq_le_four_mul (n : ℕ) (hn : 0 < n) :
    (Nat.sqrt n + 1) ^ 2 ≤ 4 * n := by
  nlinarith [Nat.sqrt_le' n, Nat.sqrt_le_self n]

lemma coord_abs_lt_two_succ_sqrt {n : ℕ} (hn : 0 < n) (w : ℂ)
    (hw : Complex.normSq w < 2 * n) :
    |w.re| < 2 * (Nat.sqrt n + 1) ∧
      |w.im| < 2 * (Nat.sqrt n + 1) := by
  have hqNat := Nat.lt_succ_sqrt' n
  have hq : (n : ℝ) < (Nat.sqrt n + 1 : ℝ) ^ 2 := by
    exact_mod_cast hqNat
  rw [Complex.normSq_apply] at hw
  constructor <;> rw [abs_lt] <;> constructor <;>
    nlinarith [sq_nonneg w.re, sq_nonneg w.im]

/-- A point whose two coordinates have absolute value less than `2q` lands
in the square of integer grid cells indexed from `-2Lq` to `2Lq`. -/
lemma gridCell_mem_Icc_product {L q : ℕ} (hL : 0 < L) (w : ℂ)
    (hre : |w.re| < 2 * q) (him : |w.im| < 2 * q) :
    gridCell L w ∈
      (Finset.Icc (-(2 * (L : ℤ) * q)) (2 * (L : ℤ) * q)).product
        (Finset.Icc (-(2 * (L : ℤ) * q)) (2 * (L : ℤ) * q)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have bound (x : ℝ) (hx : |x| < 2 * q) :
      -(2 * (L : ℤ) * q) ≤ ⌊(L : ℝ) * x⌋ ∧
        ⌊(L : ℝ) * x⌋ ≤ 2 * (L : ℤ) * q := by
    rw [abs_lt] at hx
    constructor
    · rw [Int.le_floor]
      push_cast
      nlinarith
    · rw [← Int.lt_add_one_iff, Int.floor_lt]
      push_cast
      nlinarith
  simpa [gridCell] using ⟨bound w.re hre, bound w.im him⟩

lemma card_grid_box (L q : ℕ) :
    ((Finset.Icc (-(2 * (L : ℤ) * q)) (2 * (L : ℤ) * q)).product
      (Finset.Icc (-(2 * (L : ℤ) * q)) (2 * (L : ℤ) * q))).card =
        (4 * L * q + 1) ^ 2 := by
  change ((Finset.Icc (-(2 * (L : ℤ) * q)) (2 * (L : ℤ) * q) ×ˢ
    Finset.Icc (-(2 * (L : ℤ) * q)) (2 * (L : ℤ) * q)).card = _)
  rw [Finset.card_product, Int.card_Icc]
  have hnonneg : (0 : ℤ) ≤ 1 + (L : ℤ) * q * 4 := by positivity
  have htoNat : (1 + (L : ℤ) * q * 4).toNat = 4 * L * q + 1 := by
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg hnonneg]
    push_cast
    ring
  have harg : 2 * (L : ℤ) * q + 1 - -(2 * (L : ℤ) * q) =
      1 + (L : ℤ) * q * 4 := by ring
  rw [harg]
  rw [htoNat]
  ring

lemma card_grid_box_le (n L : ℕ) (hn : 0 < n) (hL : 0 < L) :
    (4 * L * (Nat.sqrt n + 1) + 1) ^ 2 ≤ 100 * L ^ 2 * n := by
  let q := Nat.sqrt n + 1
  have hq : q ^ 2 ≤ 4 * n := succ_sqrt_sq_le_four_mul n hn
  have hLq : 1 ≤ L * q := by
    have hqpos : 0 < q := by simp [q]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt hL) (Nat.ne_of_gt hqpos))
  have hlinear : 4 * L * q + 1 ≤ 5 * L * q := by nlinarith
  calc
    (4 * L * q + 1) ^ 2 ≤ (5 * L * q) ^ 2 :=
      Nat.pow_le_pow_left hlinear 2
    _ = 25 * L ^ 2 * q ^ 2 := by ring
    _ ≤ 25 * L ^ 2 * (4 * n) := Nat.mul_le_mul_left (25 * L ^ 2) hq
    _ = 100 * L ^ 2 * n := by ring

/-- The good sign sums occupy at most `O(L²n)` grid cells. -/
lemma card_grid_image_good_le {n L : ℕ} (hn : 0 < n) (hL : 0 < L)
    (z : Fin n → ℂ) :
    ((Finset.univ.filter fun ε : Fin n → Bool ↦
        Complex.normSq (signedSum z ε) < 2 * n).image
      (fun ε ↦ gridCell L (signedSum z ε))).card ≤ 100 * L ^ 2 * n := by
  let q := Nat.sqrt n + 1
  let box := (Finset.Icc (-(2 * (L : ℤ) * q)) (2 * (L : ℤ) * q)).product
    (Finset.Icc (-(2 * (L : ℤ) * q)) (2 * (L : ℤ) * q))
  have hsub :
      (Finset.univ.filter fun ε : Fin n → Bool ↦
          Complex.normSq (signedSum z ε) < 2 * n).image
        (fun ε ↦ gridCell L (signedSum z ε)) ⊆ box := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨ε, hε, rfl⟩
    have hgood := (Finset.mem_filter.mp hε).2
    have hcoord := coord_abs_lt_two_succ_sqrt hn (signedSum z ε) hgood
    apply gridCell_mem_Icc_product hL (signedSum z ε)
    · simpa [q] using hcoord.1
    · simpa [q] using hcoord.2
  calc
    _ ≤ box.card := Finset.card_le_card hsub
    _ = (4 * L * q + 1) ^ 2 := card_grid_box L q
    _ ≤ 100 * L ^ 2 * n := card_grid_box_le n L hn hL

/-- Two complex numbers in the same `L`-grid cell are within squared
distance `2/L²`. -/
lemma normSq_sub_lt_of_gridCell_eq {L : ℕ} (hL : 0 < L) {w v : ℂ}
    (hcell : gridCell L w = gridCell L v) :
    Complex.normSq (w - v) < 2 * (1 / (L : ℝ)) ^ 2 := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hreFloor : ⌊(L : ℝ) * w.re⌋ = ⌊(L : ℝ) * v.re⌋ := by
    exact congrArg Prod.fst hcell
  have himFloor : ⌊(L : ℝ) * w.im⌋ = ⌊(L : ℝ) * v.im⌋ := by
    exact congrArg Prod.snd hcell
  have hre0 := Int.abs_sub_lt_one_of_floor_eq_floor hreFloor
  have him0 := Int.abs_sub_lt_one_of_floor_eq_floor himFloor
  have hre : |w.re - v.re| < 1 / (L : ℝ) := by
    rw [lt_div_iff₀ hL']
    calc
      |w.re - v.re| * (L : ℝ) = |(w.re - v.re) * L| := by
        rw [abs_mul, abs_of_pos hL']
      _ = |(L : ℝ) * w.re - L * v.re| := by congr 1 <;> ring
      _ < 1 := hre0
  have him : |w.im - v.im| < 1 / (L : ℝ) := by
    rw [lt_div_iff₀ hL']
    calc
      |w.im - v.im| * (L : ℝ) = |(w.im - v.im) * L| := by
        rw [abs_mul, abs_of_pos hL']
      _ = |(L : ℝ) * w.im - L * v.im| := by congr 1 <;> ring
      _ < 1 := him0
  have hinv : 0 < 1 / (L : ℝ) := by positivity
  have hreSq : (w.re - v.re) ^ 2 < (1 / (L : ℝ)) ^ 2 := by
    nlinarith [sq_abs (w.re - v.re), abs_nonneg (w.re - v.re)]
  have himSq : (w.im - v.im) ^ 2 < (1 / (L : ℝ)) ^ 2 := by
    nlinarith [sq_abs (w.im - v.im), abs_nonneg (w.im - v.im)]
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  nlinarith

/-- Quantitative collision lemma for bounded complex Rademacher sums.  It is
stated in unnormalized counting form so that no measure-theory interface is
needed later. -/
lemma collision_count {n L : ℕ} (hn : 0 < n) (hL : 0 < L)
    (z : Fin n → ℂ) (hz : ∀ i, Complex.normSq (z i) ≤ 1) :
    (2 : ℝ) ^ (2 * n) ≤ 400 * (L : ℝ) ^ 2 * n *
      (((Finset.univ : Finset (Fin n → Bool)).product Finset.univ).filter
        fun p ↦ Complex.normSq (signedSum z p.1 - signedSum z p.2) <
          2 * (1 / (L : ℝ)) ^ 2).card := by
  let good := Finset.univ.filter fun ε : Fin n → Bool ↦
    Complex.normSq (signedSum z ε) < 2 * n
  let f : (Fin n → Bool) → ℤ × ℤ := fun ε ↦ gridCell L (signedSum z ε)
  let same := (good.product good).filter fun p ↦ f p.1 = f p.2
  let close :=
    (((Finset.univ : Finset (Fin n → Bool)).product Finset.univ).filter
      fun p ↦ Complex.normSq (signedSum z p.1 - signedSum z p.2) <
        2 * (1 / (L : ℝ)) ^ 2)
  have hhalf : (2 : ℝ) ^ n ≤ 2 * (good.card : ℝ) := by
    simpa [good] using half_cube_le_card_good hn z hz
  have hcauchyNat : good.card ^ 2 ≤ (good.image f).card * same.card := by
    simpa [same] using card_sq_le_card_image_mul_card_eqPairs good f
  have himageNat : (good.image f).card ≤ 100 * L ^ 2 * n := by
    simpa [good, f] using card_grid_image_good_le hn hL z
  have hsameClose : same ⊆ close := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpGood := Finset.mem_product.mp hp'.1
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    · exact normSq_sub_lt_of_gridCell_eq hL hp'.2
  have hsameCardNat : same.card ≤ close.card := Finset.card_le_card hsameClose
  have hcauchy : (good.card : ℝ) ^ 2 ≤
      ((good.image f).card : ℝ) * same.card := by
    exact_mod_cast hcauchyNat
  have himage : ((good.image f).card : ℝ) ≤
      100 * (L : ℝ) ^ 2 * n := by
    exact_mod_cast himageNat
  have hsameCard : (same.card : ℝ) ≤ close.card := by
    exact_mod_cast hsameCardNat
  change (2 : ℝ) ^ (2 * n) ≤
    400 * (L : ℝ) ^ 2 * n * (close.card : ℝ)
  calc
    (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ n) ^ 2 := by
      rw [show 2 * n = n * 2 by omega, pow_mul]
    _ ≤ (2 * (good.card : ℝ)) ^ 2 := by gcongr
    _ = 4 * (good.card : ℝ) ^ 2 := by ring
    _ ≤ 4 * (((good.image f).card : ℝ) * same.card) := by gcongr
    _ ≤ 4 * ((100 * (L : ℝ) ^ 2 * n) * same.card) := by
      gcongr
    _ ≤ 4 * ((100 * (L : ℝ) ^ 2 * n) * close.card) := by
      gcongr
    _ = 400 * (L : ℝ) ^ 2 * n * close.card := by ring

/-- Shifted second moment.  The mixed term cancels by pairing the two values
of the first Boolean coordinate. -/
lemma sum_normSq_add_signedSum : ∀ n (z : Fin n → ℂ) (w : ℂ),
    (∑ ε : Fin n → Bool, Complex.normSq (w + signedSum z ε)) =
      (2 : ℝ) ^ n * (Complex.normSq w + ∑ i, Complex.normSq (z i)) := by
  intro n
  induction n with
  | zero =>
      intro z w
      simp [signedSum]
  | succ n ih =>
      intro z w
      rw [sum_cube_succ]
      simp only [signedSum_cons]
      rw [show (∑ b : Bool, ∑ ε : Fin n → Bool,
          Complex.normSq (w + ((sign b : ℂ) * z 0 +
            signedSum (fun i ↦ z i.succ) ε))) =
          ∑ ε : Fin n → Bool,
            (Complex.normSq ((w + signedSum (fun i ↦ z i.succ) ε) - z 0) +
              Complex.normSq ((w + signedSum (fun i ↦ z i.succ) ε) + z 0)) by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ε _
        rw [Finset.sum_eq_add false true] <;> simp <;> congr 1 <;> ring]
      have hpoint : ∀ x a : ℂ,
          Complex.normSq (x - a) + Complex.normSq (x + a) =
            2 * Complex.normSq x + 2 * Complex.normSq a := by
        intro x a
        rw [Complex.normSq_sub, Complex.normSq_add]
        ring
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      rw [ih]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
      rw [Fin.sum_univ_succ, pow_succ]
      push_cast
      ring

/-- Finite Markov estimate in the useful lower-tail form. -/
lemma shifted_smallBall_count {n : ℕ} (z : Fin n → ℂ) (w : ℂ)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (henergy : Complex.normSq w + ∑ i, Complex.normSq (z i) ≤ R - c) :
    c * (2 : ℝ) ^ n ≤ R *
      ((Finset.univ.filter fun ε : Fin n → Bool ↦
        Complex.normSq (w + signedSum z ε) < R).card : ℝ) := by
  let good := Finset.univ.filter fun ε : Fin n → Bool ↦
    Complex.normSq (w + signedSum z ε) < R
  let bad := Finset.univ.filter fun ε : Fin n → Bool ↦
    R ≤ Complex.normSq (w + signedSum z ε)
  have hmarkov := counting_markov
    (fun ε : Fin n → Bool ↦ Complex.normSq (w + signedSum z ε)) R hR
    (fun ε ↦ Complex.normSq_nonneg _)
  have hbad : (bad.card : ℝ) * R ≤ (2 : ℝ) ^ n * (R - c) := by
    change (bad.card : ℝ) * R ≤
      ∑ ε : Fin n → Bool, Complex.normSq (w + signedSum z ε) at hmarkov
    rw [sum_normSq_add_signedSum] at hmarkov
    exact hmarkov.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hpartition : good.card + bad.card = 2 ^ n := by
    rw [← card_univ_signCube n]
    have hdisj : Disjoint good bad := by
      rw [Finset.disjoint_left]
      intro ε hgood hbad'
      exact (not_le_of_gt (Finset.mem_filter.mp hgood).2)
        (Finset.mem_filter.mp hbad').2
    have hunion : good ∪ bad = (Finset.univ : Finset (Fin n → Bool)) := by
      ext ε
      simp only [good, bad, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro _
        trivial
      · intro _
        exact lt_or_ge _ _
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  change c * (2 : ℝ) ^ n ≤ R * (good.card : ℝ)
  have hpartition' : (good.card : ℝ) + bad.card = (2 : ℝ) ^ n := by
    exact_mod_cast hpartition
  nlinarith

abbrev SignVec (m : ℕ) := Fin m → Bool
abbrev SignPair (m : ℕ) := SignVec m × SignVec m
abbrev SignTriple (m : ℕ) := SignVec m × SignVec m × SignVec m

@[simp] lemma sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> simp [sign]

/-- The coordinatewise two-to-one map behind the pairing argument.  If `s`
and `t` differ, it emits equal signs; if they agree, the auxiliary sign `h`
chooses one of the two opposite-sign outputs. -/
def pairedOutput {m : ℕ} (s t h : SignVec m) : SignPair m :=
  (fun i ↦ if s i = t i then h i else s i,
   fun i ↦ if s i = t i then !h i else s i)

/-- The unused Boolean in each fiber of `pairedOutput`. -/
def pairedCode {m : ℕ} (s t h : SignVec m) : SignVec m :=
  fun i ↦ if s i = t i then s i else h i

/-- Explicit inverse to `(pairedOutput, pairedCode)`. -/
def pairedDecode {m : ℕ} (q : SignPair m) (k : SignVec m) : SignTriple m :=
  (fun i ↦ if q.1 i = q.2 i then q.1 i else k i,
   fun i ↦ if q.1 i = q.2 i then !q.1 i else k i,
   fun i ↦ if q.1 i = q.2 i then k i else q.1 i)

lemma pairedDecode_encode {m : ℕ} (x : SignTriple m) :
    pairedDecode (pairedOutput x.1 x.2.1 x.2.2)
      (pairedCode x.1 x.2.1 x.2.2) = x := by
  rcases x with ⟨s, t, h⟩
  ext i <;>
    simp only [pairedDecode, pairedOutput, pairedCode]
  all_goals
    cases hs : s i <;> cases ht : t i <;> cases hh : h i <;>
      simp [hs, ht, hh]

lemma pairedEncode_decode {m : ℕ} (y : SignPair m × SignVec m) :
    (pairedOutput (pairedDecode y.1 y.2).1 (pairedDecode y.1 y.2).2.1
        (pairedDecode y.1 y.2).2.2,
      pairedCode (pairedDecode y.1 y.2).1 (pairedDecode y.1 y.2).2.1
        (pairedDecode y.1 y.2).2.2) = y := by
  rcases y with ⟨⟨a, b⟩, k⟩
  ext i <;>
    simp only [pairedDecode, pairedOutput, pairedCode]
  all_goals
    cases ha : a i <;> cases hb : b i <;> cases hk : k i <;>
      simp [ha, hb, hk]

/-- `pairedOutput` has exactly `2^m` preimages, with `pairedCode` recording
the free Boolean in each coordinate. -/
def pairedEquiv (m : ℕ) : SignTriple m ≃ SignPair m × SignVec m where
  toFun x :=
    (pairedOutput x.1 x.2.1 x.2.2, pairedCode x.1 x.2.1 x.2.2)
  invFun y := pairedDecode y.1 y.2
  left_inv := pairedDecode_encode
  right_inv := pairedEncode_decode

/-- Algebraic identity relating the paired output to a collision of midpoint
sums plus a Rademacher sum of the selected pair differences. -/
lemma pairedOutput_sum_identity {m : ℕ} (u v : Fin m → ℂ)
    (s t h : SignVec m) :
    signedSum u (pairedOutput s t h).1 +
        signedSum v (pairedOutput s t h).2 =
      (signedSum (fun i ↦ (u i + v i) / 2) s -
        signedSum (fun i ↦ (u i + v i) / 2) t) +
        signedSum (fun i ↦ if s i = t i then u i - v i else 0) h := by
  simp only [signedSum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : s i <;> cases ht : t i <;> cases hh : h i <;>
    simp [pairedOutput, hs, ht, hh, sign] <;> ring

/-- Cardinal form of the fact that every paired sign vector has exactly
`2^m` triple preimages. -/
lemma card_filter_pairedOutput {m : ℕ} (P : SignPair m → Prop)
    [DecidablePred P] :
    ((Finset.univ.filter fun x : SignTriple m ↦
      P (pairedOutput x.1 x.2.1 x.2.2)).card) =
      2 ^ m * (Finset.univ.filter P).card := by
  let e₁ : {x : SignTriple m // P (pairedOutput x.1 x.2.1 x.2.2)} ≃
      {y : SignPair m × SignVec m // P y.1} :=
    (pairedEquiv m).subtypeEquiv (fun _ ↦ Iff.rfl)
  let e₂ : {y : SignPair m × SignVec m // P y.1} ≃
      {q : SignPair m // P q} × SignVec m :=
    { toFun := fun y ↦ (⟨y.1.1, y.2⟩, y.1.2)
      invFun := fun y ↦ ⟨(y.1.1, y.2), y.1.2⟩
      left_inv := by intro y; cases y; rfl
      right_inv := by intro y; cases y; rfl }
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  rw [Fintype.card_congr e₁, Fintype.card_congr e₂]
  simp [Fintype.card_prod, card_signCube, mul_comm]

lemma normSq_midpoint_le_one {u v : ℂ}
    (hu : Complex.normSq u ≤ 1) (hv : Complex.normSq v ≤ 1) :
    Complex.normSq ((u + v) / 2) ≤ 1 := by
  have hunorm : ‖u‖ ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq] at hu
    nlinarith [norm_nonneg u]
  have hvnorm : ‖v‖ ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq] at hv
    nlinarith [norm_nonneg v]
  have hmid : ‖(u + v) / 2‖ ≤ 1 := by
    rw [norm_div]
    norm_num
    have hadd := norm_add_le u v
    nlinarith
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg ((u + v) / 2)]

lemma sum_normSq_selected_diff_le {m : ℕ} (u v : Fin m → ℂ)
    (s t : SignVec m) :
    (∑ i, Complex.normSq (if s i = t i then u i - v i else 0)) ≤
      ∑ i, Complex.normSq (u i - v i) := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · simpa using Complex.normSq_nonneg (u i - v i)

lemma card_filter_product_eq_sum {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset A) (t : Finset B) (P : A × B → Prop) [DecidablePred P] :
    ((s.product t).filter P).card =
      ∑ a ∈ s, (t.filter fun b ↦ P (a, b)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_product s t (fun p ↦ if P p then 1 else 0)

def pairSignedSum {m : ℕ} (u v : Fin m → ℂ) (q : SignPair m) : ℂ :=
  signedSum u q.1 + signedSum v q.2

/-- Quantitative pairing lemma.  If the total squared distance inside the
pairs is below the target squared radius by `α`, then collision of the
midpoint sums and Markov on the selected differences give an explicit
`1/m` small-ball count. -/
lemma pairing_count {m L : ℕ} (hm : 0 < m) (hL : 0 < L)
    (u v : Fin m → ℂ) (hu : ∀ i, Complex.normSq (u i) ≤ 1)
    (hv : ∀ i, Complex.normSq (v i) ≤ 1)
    {R α : ℝ} (hR : 0 < R) (hα : 0 < α)
    (henergy : (∑ i, Complex.normSq (u i - v i)) ≤ R - α)
    (hscale : 2 * (1 / (L : ℝ)) ^ 2 ≤ α / 2) :
    (α / 2) * (2 : ℝ) ^ (2 * m) ≤
      400 * (L : ℝ) ^ 2 * m * R *
        ((Finset.univ.filter fun q : SignPair m ↦
          Complex.normSq (pairSignedSum u v q) < R).card : ℝ) := by
  let mid : Fin m → ℂ := fun i ↦ (u i + v i) / 2
  let close :=
    (((Finset.univ : Finset (SignVec m)).product Finset.univ).filter
      fun p ↦ Complex.normSq (signedSum mid p.1 - signedSum mid p.2) <
        2 * (1 / (L : ℝ)) ^ 2)
  let goodPair := Finset.univ.filter fun q : SignPair m ↦
    Complex.normSq (pairSignedSum u v q) < R
  let selected := (close.product (Finset.univ : Finset (SignVec m))).filter
    fun y ↦
      Complex.normSq
        ((signedSum mid y.1.1 - signedSum mid y.1.2) +
          signedSum (fun i ↦ if y.1.1 i = y.1.2 i then u i - v i else 0) y.2) < R
  let tripleGood := Finset.univ.filter fun x : SignTriple m ↦
    Complex.normSq (pairSignedSum u v (pairedOutput x.1 x.2.1 x.2.2)) < R
  have hmid : ∀ i, Complex.normSq (mid i) ≤ 1 := by
    intro i
    exact normSq_midpoint_le_one (hu i) (hv i)
  have hcollision : (2 : ℝ) ^ (2 * m) ≤
      400 * (L : ℝ) ^ 2 * m * (close.card : ℝ) := by
    simpa [close] using collision_count hm hL mid hmid
  have hfiber (p : SignPair m) (hp : p ∈ close) :
      (α / 2) * (2 : ℝ) ^ m ≤ R *
        (((Finset.univ : Finset (SignVec m)).filter fun h ↦
          Complex.normSq
            ((signedSum mid p.1 - signedSum mid p.2) +
              signedSum (fun i ↦ if p.1 i = p.2 i then u i - v i else 0) h) < R).card : ℝ) := by
    have hpclose := (Finset.mem_filter.mp hp).2
    have hselectedEnergy := sum_normSq_selected_diff_le u v p.1 p.2
    have htotal :
        Complex.normSq (signedSum mid p.1 - signedSum mid p.2) +
            ∑ i, Complex.normSq
              (if p.1 i = p.2 i then u i - v i else 0) ≤
          R - α / 2 := by
      linarith
    exact shifted_smallBall_count
      (fun i ↦ if p.1 i = p.2 i then u i - v i else 0)
      (signedSum mid p.1 - signedSum mid p.2) hR (by linarith) htotal
  have hselectedCard :
      (close.card : ℝ) * ((α / 2) * (2 : ℝ) ^ m) ≤
        R * (selected.card : ℝ) := by
    have hcardNat := card_filter_product_eq_sum close
      (Finset.univ : Finset (SignVec m))
      (fun y ↦
        Complex.normSq
          ((signedSum mid y.1.1 - signedSum mid y.1.2) +
            signedSum (fun i ↦ if y.1.1 i = y.1.2 i then u i - v i else 0) y.2) < R)
    have hcard : (selected.card : ℝ) =
        ∑ p ∈ close,
          ((((Finset.univ : Finset (SignVec m)).filter fun h ↦
            Complex.normSq
              ((signedSum mid p.1 - signedSum mid p.2) +
                signedSum (fun i ↦ if p.1 i = p.2 i then u i - v i else 0) h) < R).card : ℝ)) := by
      change (((close.product (Finset.univ : Finset (SignVec m))).filter _).card : ℝ) = _
      rw [hcardNat]
      push_cast
      rfl
    calc
      (close.card : ℝ) * ((α / 2) * (2 : ℝ) ^ m) =
          ∑ p ∈ close, (α / 2) * (2 : ℝ) ^ m := by
            simp
      _ ≤ ∑ p ∈ close, R *
          ((((Finset.univ : Finset (SignVec m)).filter fun h ↦
            Complex.normSq
              ((signedSum mid p.1 - signedSum mid p.2) +
                signedSum (fun i ↦ if p.1 i = p.2 i then u i - v i else 0) h) < R).card : ℝ)) := by
            exact Finset.sum_le_sum fun p hp ↦ hfiber p hp
      _ = R * (selected.card : ℝ) := by
            rw [hcard, Finset.mul_sum]
  let assocEmb : (SignPair m × SignVec m) ↪ SignTriple m :=
    ⟨fun y ↦ (y.1.1, y.1.2, y.2), by
      intro a b hab
      exact Prod.ext
        (Prod.ext
          (congrArg (fun x : SignTriple m ↦ x.1) hab)
          (congrArg (fun x : SignTriple m ↦ x.2.1) hab))
        (congrArg (fun x : SignTriple m ↦ x.2.2) hab)⟩
  have hselectedMap : selected.map assocEmb ⊆ tripleGood := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyGood := (Finset.mem_filter.mp hy).2
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · change Complex.normSq
        (pairSignedSum u v (pairedOutput y.1.1 y.1.2 y.2)) < R
      rw [pairSignedSum, pairedOutput_sum_identity]
      exact hyGood
  have hselected_le_triple : selected.card ≤ tripleGood.card := by
    rw [← Finset.card_map assocEmb]
    exact Finset.card_le_card hselectedMap
  have htripleCard : (tripleGood.card : ℝ) =
      (2 : ℝ) ^ m * (goodPair.card : ℝ) := by
    have h := card_filter_pairedOutput
      (fun q : SignPair m ↦ Complex.normSq (pairSignedSum u v q) < R)
    change (tripleGood.card : ℝ) = _
    rw [show tripleGood.card = 2 ^ m * goodPair.card by simpa [tripleGood, goodPair] using h]
    push_cast
    rfl
  have hselected_le_pair : (selected.card : ℝ) ≤
      (2 : ℝ) ^ m * (goodPair.card : ℝ) := by
    exact (by exact_mod_cast hselected_le_triple :
      (selected.card : ℝ) ≤ tripleGood.card).trans_eq htripleCard
  have hNpos : 0 < (2 : ℝ) ^ m := by positivity
  have hcombined :
      ((α / 2) * (2 : ℝ) ^ m) * (2 : ℝ) ^ (2 * m) ≤
        400 * (L : ℝ) ^ 2 * m * R *
          ((2 : ℝ) ^ m * (goodPair.card : ℝ)) := by
    calc
      ((α / 2) * (2 : ℝ) ^ m) * (2 : ℝ) ^ (2 * m) ≤
          ((α / 2) * (2 : ℝ) ^ m) *
            (400 * (L : ℝ) ^ 2 * m * close.card) := by
              gcongr
      _ = 400 * (L : ℝ) ^ 2 * m *
          ((close.card : ℝ) * ((α / 2) * (2 : ℝ) ^ m)) := by ring
      _ ≤ 400 * (L : ℝ) ^ 2 * m * (R * selected.card) := by
            gcongr
      _ ≤ 400 * (L : ℝ) ^ 2 * m *
          (R * ((2 : ℝ) ^ m * goodPair.card)) := by
            gcongr
      _ = 400 * (L : ℝ) ^ 2 * m * R *
          ((2 : ℝ) ^ m * goodPair.card) := by ring
  change (α / 2) * (2 : ℝ) ^ (2 * m) ≤
    400 * (L : ℝ) ^ 2 * m * R * (goodPair.card : ℝ)
  by_contra hgoal
  have hdiff : 0 < (2 : ℝ) ^ m *
      (((α / 2) * (2 : ℝ) ^ (2 * m)) -
        400 * (L : ℝ) ^ 2 * m * R * (goodPair.card : ℝ)) :=
    mul_pos hNpos (sub_pos.mpr (lt_of_not_ge hgoal))
  nlinarith [hcombined]

/-- Normalized-probability form of `pairing_count`. -/
lemma pairing_probability_lower_bound {m L : ℕ} (hm : 0 < m) (hL : 0 < L)
    (u v : Fin m → ℂ) (hu : ∀ i, Complex.normSq (u i) ≤ 1)
    (hv : ∀ i, Complex.normSq (v i) ≤ 1)
    {R α : ℝ} (hR : 0 < R) (hα : 0 < α)
    (henergy : (∑ i, Complex.normSq (u i - v i)) ≤ R - α)
    (hscale : 2 * (1 / (L : ℝ)) ^ 2 ≤ α / 2) :
    α / (800 * (L : ℝ) ^ 2 * m * R) ≤
      uniformProbability (fun q : SignPair m ↦
        Complex.normSq (pairSignedSum u v q) < R) := by
  have hcount := pairing_count hm hL u v hu hv hR hα henergy hscale
  unfold uniformProbability
  simp only [Fintype.card_prod, card_signCube]
  rw [show 2 ^ m * 2 ^ m = (2 : ℕ) ^ (2 * m) by
    rw [← pow_add]
    congr 1 <;> omega]
  have hden : 0 < 800 * (L : ℝ) ^ 2 * (m : ℝ) * R := by positivity
  have hpow : 0 < (2 : ℝ) ^ (2 * m) := by positivity
  push_cast
  rw [div_le_div_iff₀ hden hpow]
  calc
    α * (2 : ℝ) ^ (2 * m) =
        2 * ((α / 2) * (2 : ℝ) ^ (2 * m)) := by ring
    _ ≤ 2 * (400 * (L : ℝ) ^ 2 * m * R *
        ((Finset.univ.filter fun q : SignPair m ↦
          Complex.normSq (pairSignedSum u v q) < R).card : ℝ)) := by
      gcongr
    _ = ((Finset.univ.filter fun q : SignPair m ↦
          Complex.normSq (pairSignedSum u v q) < R).card : ℝ) *
        (800 * (L : ℝ) ^ 2 * m * R) := by ring

/-! ### Planar geometry for projective pairings -/

def dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
def det (x y : ℂ) : ℝ := x.re * y.im - x.im * y.re

lemma normSq_sub_eq (x y : ℂ) :
    Complex.normSq (x - y) =
      Complex.normSq x + Complex.normSq y - 2 * dot x y := by
  simp [Complex.normSq_apply, dot]
  ring

lemma dot_det_sq (x y : ℂ) :
    dot x y ^ 2 + det x y ^ 2 = Complex.normSq x * Complex.normSq y := by
  simp [dot, det, Complex.normSq_apply]
  ring

lemma pair_center_sum {u v : ℂ}
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1) :
    Complex.normSq (u + v) + Complex.normSq (u - v) = 4 := by
  rw [Complex.normSq_add, Complex.normSq_sub, hu, hv]
  ring

lemma pair_center_orthogonal {u v : ℂ}
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1) :
    dot (u + v) (u - v) = 0 := by
  simp [dot, Complex.normSq_apply] at hu hv ⊢
  nlinarith

lemma gram_identity (a b w : ℂ) :
    Complex.normSq b * dot w a ^ 2 +
        Complex.normSq a * dot w b ^ 2 -
        2 * dot a b * dot w a * dot w b =
      (Complex.normSq a * Complex.normSq b - dot a b ^ 2) *
        Complex.normSq w := by
  simp [dot, Complex.normSq_apply]
  ring

lemma pair_center_parseval {u v w : ℂ}
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1) :
    Complex.normSq (u - v) * dot w (u + v) ^ 2 +
      Complex.normSq (u + v) * dot w (u - v) ^ 2 =
      Complex.normSq (u + v) * Complex.normSq (u - v) *
        Complex.normSq w := by
  have hortho := pair_center_orthogonal hu hv
  have hgram := gram_identity (u + v) (u - v) w
  rw [hortho] at hgram
  simpa using hgram

lemma normSq_add_eq (x y : ℂ) :
    Complex.normSq (x + y) =
      Complex.normSq x + Complex.normSq y + 2 * dot x y := by
  simp [Complex.normSq_apply, dot]
  ring

lemma dot_neg_right (x y : ℂ) : dot x (-y) = -dot x y := by
  simp [dot]
  ring

/-- The four sums `±u ±v` cover the disk of squared radius `1/4` by
disks of squared radius `2`, in the case where `u+v` is the shorter center. -/
lemma four_center_cover_small_ordered {u v w : ℂ}
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hw : Complex.normSq w ≤ (1 : ℝ) / 4)
    (horder : Complex.normSq (u + v) ≤ Complex.normSq (u - v)) :
    ∃ c : ℂ,
      (c = u + v ∨ c = -(u + v) ∨ c = u - v ∨ c = -(u - v)) ∧
      Complex.normSq (w + c) ≤ 2 := by
  let a := u + v
  let b := u - v
  let p := Complex.normSq a
  let q := Complex.normSq b
  let T := Complex.normSq w
  have hT0 : 0 ≤ T := Complex.normSq_nonneg _
  have hp0 : 0 ≤ p := Complex.normSq_nonneg _
  have hq0 : 0 ≤ q := Complex.normSq_nonneg _
  have hsum : p + q = 4 := pair_center_sum hu hv
  have hp_le : p ≤ q := horder
  have hp2 : p ≤ 2 := by linarith
  have hq2 : 2 ≤ q := by linarith
  by_cases himmediate : T + p ≤ 2
  · by_cases hd : dot w a ≤ 0
    · refine ⟨a, Or.inl rfl, ?_⟩
      rw [normSq_add_eq]
      change T + p + 2 * dot w a ≤ 2
      linarith
    · refine ⟨-a, Or.inr (Or.inl rfl), ?_⟩
      rw [normSq_add_eq]
      change T + Complex.normSq (-a) + 2 * dot w (-a) ≤ 2
      rw [Complex.normSq_neg, dot_neg_right]
      change T + p + 2 * (-dot w a) ≤ 2
      linarith
  · push Not at himmediate
    by_contra hnone
    push Not at hnone
    have hpa := hnone a (Or.inl rfl)
    have hna := hnone (-a) (Or.inr (Or.inl rfl))
    have hpb := hnone b (Or.inr (Or.inr (Or.inl rfl)))
    have hnb := hnone (-b) (Or.inr (Or.inr (Or.inr rfl)))
    have hpa' : 2 < T + p + 2 * dot w a := by
      rw [normSq_add_eq] at hpa
      exact hpa
    have hna' : 2 < T + p - 2 * dot w a := by
      rw [normSq_add_eq, Complex.normSq_neg, dot_neg_right] at hna
      change 2 < T + p + 2 * (-dot w a) at hna
      linarith
    have hpb' : 2 < T + q + 2 * dot w b := by
      rw [normSq_add_eq] at hpb
      exact hpb
    have hnb' : 2 < T + q - 2 * dot w b := by
      rw [normSq_add_eq, Complex.normSq_neg, dot_neg_right] at hnb
      change 2 < T + q + 2 * (-dot w b) at hnb
      linarith
    have hsqa : 4 * dot w a ^ 2 < (T + p - 2) ^ 2 := by
      have h1 : 0 < (T + p - 2) - 2 * dot w a := by linarith
      have h2 : 0 < (T + p - 2) + 2 * dot w a := by linarith
      have hm := mul_pos h1 h2
      nlinarith
    have hsqb : 4 * dot w b ^ 2 < (T + q - 2) ^ 2 := by
      have h1 : 0 < (T + q - 2) - 2 * dot w b := by linarith
      have h2 : 0 < (T + q - 2) + 2 * dot w b := by linarith
      have hm := mul_pos h1 h2
      nlinarith
    have hp : 0 < p := by linarith
    have hq : 0 < q := lt_of_lt_of_le (by norm_num) hq2
    have hweighted :
        4 * (q * dot w a ^ 2 + p * dot w b ^ 2) <
          q * (T + p - 2) ^ 2 + p * (T + q - 2) ^ 2 := by
      have ha := mul_lt_mul_of_pos_left hsqa hq
      have hb := mul_lt_mul_of_pos_left hsqb hp
      nlinarith
    have hparseval : q * dot w a ^ 2 + p * dot w b ^ 2 = p * q * T := by
      simpa [a, b, p, q, T] using pair_center_parseval (w := w) hu hv
    have hrhs : q * (T + p - 2) ^ 2 + p * (T + q - 2) ^ 2 =
        4 * ((T - 2) ^ 2 + p * q * (T - 1)) := by
      calc
        _ = (p + q) * (T - 2) ^ 2 +
            4 * p * q * (T - 2) + p * q * (p + q) := by ring
        _ = _ := by rw [hsum]; ring
    rw [hparseval, hrhs] at hweighted
    have hupper : p * q < (T - 2) ^ 2 := by nlinarith
    have hp_lower : 2 - T < p := by linarith
    have hlinear : 2 * (2 - T) < p * q := by
      calc
        2 * (2 - T) < 2 * p := by linarith
        _ ≤ p * q := by nlinarith
    have hsquare : (2 - T) ^ 2 ≤ 2 * (2 - T) := by
      change T ≤ (1 : ℝ) / 4 at hw
      nlinarith only [hw, hT0]
    have hlower : (T - 2) ^ 2 < p * q := by
      calc
        (T - 2) ^ 2 = (2 - T) ^ 2 := by ring
        _ ≤ 2 * (2 - T) := hsquare
        _ < p * q := hlinear
    exact (not_lt_of_ge (le_of_lt hupper)) hlower

/-- For unit `u,v` and a vector in the disk of squared radius `1/4`, one of
the four additions `±u ±v` lands in the disk of squared radius `2`. -/
lemma four_center_cover_small {u v w : ℂ}
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hw : Complex.normSq w ≤ (1 : ℝ) / 4) :
    ∃ c : ℂ,
      (c = u + v ∨ c = -(u + v) ∨ c = u - v ∨ c = -(u - v)) ∧
      Complex.normSq (w + c) ≤ 2 := by
  rcases le_total (Complex.normSq (u + v)) (Complex.normSq (u - v)) with h | h
  · exact four_center_cover_small_ordered hu hv hw h
  · have hneg : Complex.normSq (-v) = 1 := by simpa using hv
    have hswap : Complex.normSq (u + -v) ≤ Complex.normSq (u - -v) := by
      rw [show u + -v = u - v by ring, show u - -v = u + v by ring]
      exact h
    obtain ⟨c, hc, hnorm⟩ :=
      four_center_cover_small_ordered (u := u) (v := -v) hu hneg hw hswap
    refine ⟨c, ?_, hnorm⟩
    rcases hc with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (by rw [h]; ring)))
    · exact Or.inr (Or.inr (Or.inr (by rw [h]; ring)))
    · exact Or.inl (by rw [h]; ring)
    · exact Or.inr (Or.inl (by rw [h]; ring))

lemma exists_two_signs_cover_small {u v w : ℂ}
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hw : Complex.normSq w ≤ (1 : ℝ) / 4) :
    ∃ δ : Fin 2 → Bool,
      Complex.normSq (w + signedSum ![u, v] δ) ≤ 2 := by
  obtain ⟨c, hc, hnorm⟩ := four_center_cover_small hu hv hw
  rcases hc with rfl | rfl | rfl | rfl
  · refine ⟨![true, true], ?_⟩
    convert hnorm using 1 <;> simp [signedSum, sign, Fin.sum_univ_two] <;> ring
  · refine ⟨![false, false], ?_⟩
    convert hnorm using 1 <;> simp [signedSum, sign, Fin.sum_univ_two] <;> ring
  · refine ⟨![true, false], ?_⟩
    convert hnorm using 1 <;> simp [signedSum, sign, Fin.sum_univ_two] <;> ring
  · refine ⟨![false, true], ?_⟩
    convert hnorm using 1 <;> simp [signedSum, sign, Fin.sum_univ_two] <;> ring

lemma pair_center_product (u v : ℂ)
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1) :
    Complex.normSq (u + v) * Complex.normSq (u - v) =
      4 * (1 - dot u v ^ 2) := by
  rw [normSq_add_eq, normSq_sub_eq, hu, hv]
  ring

lemma four_center_cover_large_ordered {u v w : ℂ}
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hw : Complex.normSq w ≤ (3 : ℝ))
    (hproduct : 1 ≤ Complex.normSq (u + v) * Complex.normSq (u - v))
    (horder : Complex.normSq (u + v) ≤ Complex.normSq (u - v)) :
    ∃ c : ℂ,
      (c = u + v ∨ c = -(u + v) ∨ c = u - v ∨ c = -(u - v)) ∧
      Complex.normSq (w + c) ≤ 2 := by
  let a := u + v
  let b := u - v
  let p := Complex.normSq a
  let q := Complex.normSq b
  let T := Complex.normSq w
  have hT0 : 0 ≤ T := Complex.normSq_nonneg _
  have hp0 : 0 ≤ p := Complex.normSq_nonneg _
  have hq0 : 0 ≤ q := Complex.normSq_nonneg _
  have hsum : p + q = 4 := pair_center_sum hu hv
  have hp_le : p ≤ q := horder
  have hp2 : p ≤ 2 := by linarith
  have hq2 : 2 ≤ q := by linarith
  have hpq : 1 ≤ p * q := hproduct
  by_cases himmediate : T + p ≤ 2
  · by_cases hd : dot w a ≤ 0
    · refine ⟨a, Or.inl rfl, ?_⟩
      rw [normSq_add_eq]
      change T + p + 2 * dot w a ≤ 2
      linarith
    · refine ⟨-a, Or.inr (Or.inl rfl), ?_⟩
      rw [normSq_add_eq, Complex.normSq_neg, dot_neg_right]
      change T + p + 2 * (-dot w a) ≤ 2
      linarith
  · push Not at himmediate
    by_contra hnone
    push Not at hnone
    have hpa := hnone a (Or.inl rfl)
    have hna := hnone (-a) (Or.inr (Or.inl rfl))
    have hpb := hnone b (Or.inr (Or.inr (Or.inl rfl)))
    have hnb := hnone (-b) (Or.inr (Or.inr (Or.inr rfl)))
    have hpa' : 2 < T + p + 2 * dot w a := by
      rw [normSq_add_eq] at hpa
      exact hpa
    have hna' : 2 < T + p - 2 * dot w a := by
      rw [normSq_add_eq, Complex.normSq_neg, dot_neg_right] at hna
      change 2 < T + p + 2 * (-dot w a) at hna
      linarith
    have hpb' : 2 < T + q + 2 * dot w b := by
      rw [normSq_add_eq] at hpb
      exact hpb
    have hnb' : 2 < T + q - 2 * dot w b := by
      rw [normSq_add_eq, Complex.normSq_neg, dot_neg_right] at hnb
      change 2 < T + q + 2 * (-dot w b) at hnb
      linarith
    have hsqa : 4 * dot w a ^ 2 < (T + p - 2) ^ 2 := by
      have h1 : 0 < (T + p - 2) - 2 * dot w a := by linarith
      have h2 : 0 < (T + p - 2) + 2 * dot w a := by linarith
      have hm := mul_pos h1 h2
      nlinarith
    have hsqb : 4 * dot w b ^ 2 < (T + q - 2) ^ 2 := by
      have h1 : 0 < (T + q - 2) - 2 * dot w b := by linarith
      have h2 : 0 < (T + q - 2) + 2 * dot w b := by linarith
      have hm := mul_pos h1 h2
      nlinarith
    have hp : 0 < p := by
      by_contra hpnot
      have : p = 0 := le_antisymm (le_of_not_gt hpnot) hp0
      rw [this, zero_mul] at hpq
      norm_num at hpq
    have hq : 0 < q := lt_of_lt_of_le (by norm_num) hq2
    have hweighted :
        4 * (q * dot w a ^ 2 + p * dot w b ^ 2) <
          q * (T + p - 2) ^ 2 + p * (T + q - 2) ^ 2 := by
      have ha := mul_lt_mul_of_pos_left hsqa hq
      have hb := mul_lt_mul_of_pos_left hsqb hp
      nlinarith
    have hparseval : q * dot w a ^ 2 + p * dot w b ^ 2 = p * q * T := by
      simpa [a, b, p, q, T] using pair_center_parseval (w := w) hu hv
    have hrhs : q * (T + p - 2) ^ 2 + p * (T + q - 2) ^ 2 =
        4 * ((T - 2) ^ 2 + p * q * (T - 1)) := by
      calc
        _ = (p + q) * (T - 2) ^ 2 +
            4 * p * q * (T - 2) + p * q * (p + q) := by ring
        _ = _ := by rw [hsum]; ring
    rw [hparseval, hrhs] at hweighted
    have hupper : p * q < (T - 2) ^ 2 := by nlinarith
    by_cases hT : 2 ≤ T
    · have hsquare : (T - 2) ^ 2 ≤ 1 := by
        change T ≤ 3 at hw
        nlinarith only [hw, hT]
      linarith
    · have hTlt : T < 2 := lt_of_not_ge hT
      have hp_lower : 2 - T < p := by linarith
      have hlinear : 2 * (2 - T) < p * q := by
        calc
          2 * (2 - T) < 2 * p := by linarith
          _ ≤ p * q := by
            simpa [mul_comm] using mul_le_mul_of_nonneg_left hq2 hp0
      have hsquare : (2 - T) ^ 2 ≤ 2 * (2 - T) := by
        nlinarith only [hT0, hTlt]
      have hlower : (T - 2) ^ 2 < p * q := by
        calc
          (T - 2) ^ 2 = (2 - T) ^ 2 := by ring
          _ ≤ 2 * (2 - T) := hsquare
          _ < p * q := hlinear
      exact (not_lt_of_ge (le_of_lt hupper)) hlower

lemma four_center_cover_large {u v w : ℂ}
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hw : Complex.normSq w ≤ (3 : ℝ))
    (hproduct : 1 ≤ Complex.normSq (u + v) * Complex.normSq (u - v)) :
    ∃ c : ℂ,
      (c = u + v ∨ c = -(u + v) ∨ c = u - v ∨ c = -(u - v)) ∧
      Complex.normSq (w + c) ≤ 2 := by
  rcases le_total (Complex.normSq (u + v)) (Complex.normSq (u - v)) with h | h
  · exact four_center_cover_large_ordered hu hv hw hproduct h
  · have hneg : Complex.normSq (-v) = 1 := by simpa using hv
    have hswap : Complex.normSq (u + -v) ≤ Complex.normSq (u - -v) := by
      rw [show u + -v = u - v by ring, show u - -v = u + v by ring]
      exact h
    have hproduct' : 1 ≤
        Complex.normSq (u + -v) * Complex.normSq (u - -v) := by
      simpa [show u + -v = u - v by ring, show u - -v = u + v by ring,
        mul_comm] using hproduct
    obtain ⟨c, hc, hnorm⟩ :=
      four_center_cover_large_ordered hu hneg hw hproduct' hswap
    refine ⟨c, ?_, hnorm⟩
    rcases hc with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (by rw [h]; ring)))
    · exact Or.inr (Or.inr (Or.inr (by rw [h]; ring)))
    · exact Or.inl (by rw [h]; ring)
    · exact Or.inr (Or.inl (by rw [h]; ring))

lemma exists_two_signs_cover_large {u v w : ℂ}
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hw : Complex.normSq w ≤ (3 : ℝ))
    (hproduct : 1 ≤ Complex.normSq (u + v) * Complex.normSq (u - v)) :
    ∃ δ : Fin 2 → Bool,
      Complex.normSq (w + signedSum ![u, v] δ) ≤ 2 := by
  obtain ⟨c, hc, hnorm⟩ := four_center_cover_large hu hv hw hproduct
  rcases hc with rfl | rfl | rfl | rfl
  · refine ⟨![true, true], ?_⟩
    convert hnorm using 1 <;> simp [signedSum, sign, Fin.sum_univ_two] <;> ring
  · refine ⟨![false, false], ?_⟩
    convert hnorm using 1 <;> simp [signedSum, sign, Fin.sum_univ_two] <;> ring
  · refine ⟨![true, false], ?_⟩
    convert hnorm using 1 <;> simp [signedSum, sign, Fin.sum_univ_two] <;> ring
  · refine ⟨![false, true], ?_⟩
    convert hnorm using 1 <;> simp [signedSum, sign, Fin.sum_univ_two] <;> ring

lemma exists_one_sign_normSq_le_add_one {u w : ℂ}
    (hu : Complex.normSq u = 1) :
    ∃ b : Bool, Complex.normSq (w + (sign b : ℂ) * u) ≤
      Complex.normSq w + 1 := by
  by_cases hdot : dot w u ≤ 0
  · refine ⟨true, ?_⟩
    rw [show (sign true : ℂ) * u = u by simp, normSq_add_eq, hu]
    linarith
  · refine ⟨false, ?_⟩
    rw [show (sign false : ℂ) * u = -u by simp, normSq_add_eq,
      Complex.normSq_neg, hu, dot_neg_right]
    linarith

lemma dot_through_unit {x y z : ℂ} (hy : Complex.normSq y = 1) :
    dot x z = dot x y * dot y z - det x y * det y z := by
  calc
    dot x z = dot x z * Complex.normSq y := by rw [hy, mul_one]
    _ = dot x y * dot y z - det x y * det y z := by
      simp [dot, det, Complex.normSq_apply]
      ring

/-- Local chord shortcut: if the oriented arcs from `x` to `y` and from `y`
to `z` go in the same direction and have combined length at most a
semicircle, replacing the two chords by the direct chord cannot increase
squared length. -/
lemma chord_shortcut {x y z : ℂ}
    (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1)
    (hz : Complex.normSq z = 1)
    (hdet₁ : 0 ≤ det x y) (hdet₂ : 0 ≤ det y z)
    (hdot : 0 ≤ dot x y + dot y z) :
    Complex.normSq (x - y) + Complex.normSq (y - z) ≤
      Complex.normSq (x - z) := by
  let a := dot x y
  let b := dot y z
  let p := det x y
  let q := det y z
  have ha : a ^ 2 + p ^ 2 = 1 := by
    simpa [a, p, hx, hy] using dot_det_sq x y
  have hb : b ^ 2 + q ^ 2 = 1 := by
    simpa [b, q, hy, hz] using dot_det_sq y z
  have ha₁ : a ≤ 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg p]
  have hb₁ : b ≤ 1 := by
    nlinarith [sq_nonneg (b - 1), sq_nonneg q]
  have hleft : 0 ≤ (1 - a) * (1 - b) :=
    mul_nonneg (sub_nonneg.mpr ha₁) (sub_nonneg.mpr hb₁)
  have hpq : 0 ≤ p * q := mul_nonneg hdet₁ hdet₂
  have hab₀ : 0 ≤ a + b := hdot
  have hsq : ((1 - a) * (1 - b)) ^ 2 ≤ (p * q) ^ 2 := by
    have hfactor :
        (p * q) ^ 2 - ((1 - a) * (1 - b)) ^ 2 =
          2 * (a + b) * (1 - a) * (1 - b) := by
      nlinarith
    have hright : 0 ≤ 2 * (a + b) * (1 - a) * (1 - b) := by positivity
    nlinarith
  have hab : (1 - a) * (1 - b) ≤ p * q :=
    (sq_le_sq₀ hleft hpq).mp hsq
  have hxz : dot x z = a * b - p * q := by
    simpa [a, b, p, q] using dot_through_unit (x := x) (y := y) (z := z) hy
  rw [normSq_sub_eq, normSq_sub_eq, normSq_sub_eq, hx, hy, hz, hxz]
  dsimp [a, b] at hdot ⊢
  nlinarith

lemma norm_eq_one_of_normSq_eq_one {z : ℂ} (hz : Complex.normSq z = 1) :
    ‖z‖ = 1 := by
  rw [Complex.normSq_eq_norm_sq] at hz
  nlinarith [norm_nonneg z]

lemma unit_eq_exp_arg {z : ℂ} (hz : Complex.normSq z = 1) :
    z = Complex.exp (z.arg * Complex.I) := by
  have hnorm := norm_eq_one_of_normSq_eq_one hz
  simpa [hnorm] using (Complex.norm_mul_exp_arg_mul_I z).symm

lemma dot_eq_cos_arg_sub {x y : ℂ}
    (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1) :
    dot x y = Real.cos (y.arg - x.arg) := by
  have hx' := unit_eq_exp_arg hx
  have hy' := unit_eq_exp_arg hy
  unfold dot
  conv_lhs => rw [hx', hy']
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [Real.cos_sub]
  ring

lemma det_eq_sin_arg_sub {x y : ℂ}
    (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1) :
    det x y = Real.sin (y.arg - x.arg) := by
  have hx' := unit_eq_exp_arg hx
  have hy' := unit_eq_exp_arg hy
  unfold det
  conv_lhs => rw [hx', hy']
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [Real.sin_sub]
  ring

lemma chord_shortcut_of_arg {x y z : ℂ}
    (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1)
    (hz : Complex.normSq z = 1)
    (hxy : x.arg ≤ y.arg) (hyz : y.arg ≤ z.arg)
    (hspan : z.arg - x.arg ≤ Real.pi) :
    Complex.normSq (x - y) + Complex.normSq (y - z) ≤
      Complex.normSq (x - z) := by
  let A := y.arg - x.arg
  let B := z.arg - y.arg
  have hA₀ : 0 ≤ A := sub_nonneg.mpr hxy
  have hB₀ : 0 ≤ B := sub_nonneg.mpr hyz
  have hAB : A + B ≤ Real.pi := by dsimp [A, B]; linarith
  have hAπ : A ≤ Real.pi := by linarith
  have hBπ : B ≤ Real.pi := by linarith
  have hdet₁ : 0 ≤ det x y := by
    rw [det_eq_sin_arg_sub hx hy]
    exact Real.sin_nonneg_of_nonneg_of_le_pi hA₀ hAπ
  have hdet₂ : 0 ≤ det y z := by
    rw [det_eq_sin_arg_sub hy hz]
    exact Real.sin_nonneg_of_nonneg_of_le_pi hB₀ hBπ
  have hcos₁ : 0 ≤ Real.cos ((A + B) / 2) := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have := Real.pi_pos.le
      linarith
    · linarith
  have hcos₂ : 0 ≤ Real.cos ((A - B) / 2) := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · linarith
    · linarith
  have hcos : 0 ≤ Real.cos A + Real.cos B := by
    calc
      0 ≤ 2 * Real.cos ((A + B) / 2) * Real.cos ((A - B) / 2) := by
        positivity
      _ = Real.cos A + Real.cos B := by
        rw [← Real.cos_add_cos]
  apply chord_shortcut hx hy hz hdet₁ hdet₂
  rw [dot_eq_cos_arg_sub hx hy, dot_eq_cos_arg_sub hy hz]
  simpa [A, B] using hcos

lemma normSq_sub_eq_four_sin_sq_half {x y : ℂ}
    (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1) :
    Complex.normSq (x - y) = 4 * Real.sin ((y.arg - x.arg) / 2) ^ 2 := by
  rw [normSq_sub_eq, hx, hy, dot_eq_cos_arg_sub hx hy]
  rw [show y.arg - x.arg = 2 * ((y.arg - x.arg) / 2) by ring]
  rw [Real.cos_two_mul']
  have hhalf : 2 * ((y.arg - x.arg) / 2) / 2 = (y.arg - x.arg) / 2 := by ring
  rw [hhalf]
  nlinarith [Real.sin_sq_add_cos_sq ((y.arg - x.arg) / 2)]

/-- Exact identity behind the quantitative three-direction deficit. -/
lemma three_half_sine_identity {x y z : ℝ} (hsum : x + y + z = Real.pi) :
    Real.sin (x / 2) ^ 2 + Real.sin (y / 2) ^ 2 + Real.sin (z / 2) ^ 2 =
      1 - 2 * Real.sin (x / 2) * Real.sin (y / 2) * Real.sin (z / 2) := by
  have hz : z / 2 = Real.pi / 2 - (x / 2 + y / 2) := by linarith
  rw [hz, Real.sin_pi_div_two_sub, Real.cos_add]
  have hx := Real.sin_sq_add_cos_sq (x / 2)
  have hy := Real.sin_sq_add_cos_sq (y / 2)
  ring_nf at hx hy ⊢
  nlinarith

lemma three_chord_deficit {x y z ρ : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = Real.pi)
    (hcx : ρ < 2 * Real.sin (x / 2))
    (hcy : ρ < 2 * Real.sin (y / 2))
    (hcz : ρ < 2 * Real.sin (z / 2)) (hρ : 0 ≤ ρ) :
    4 * Real.sin (x / 2) ^ 2 + 4 * Real.sin (y / 2) ^ 2 +
        4 * Real.sin (z / 2) ^ 2 ≤ 4 - ρ ^ 3 := by
  have hid := three_half_sine_identity hsum
  have hsx : 0 ≤ Real.sin (x / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  have hsy : 0 ≤ Real.sin (y / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  have hsz : 0 ≤ Real.sin (z / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  have hprod : ρ ^ 3 <
      8 * Real.sin (x / 2) * Real.sin (y / 2) * Real.sin (z / 2) := by
    calc
      ρ ^ 3 = ρ * ρ * ρ := by ring
      _ < (2 * Real.sin (x / 2)) * (2 * Real.sin (y / 2)) *
          (2 * Real.sin (z / 2)) := by gcongr
      _ = _ := by ring
  nlinarith

/-- Split a sum of `2m` consecutive terms into its even and odd positions. -/
lemma sum_range_even_odd {m : ℕ} (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (2 * m), f k) =
      (∑ i ∈ Finset.range m, f (2 * i)) +
        ∑ i ∈ Finset.range m, f (2 * i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [ih]
      ring

/-- Shortcut estimate on an arbitrary interval of a naturally indexed
argument-monotone unit chain. -/
lemma chain_range_le_chord (x : ℕ → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1)
    (hmono : Monotone fun i ↦ (x i).arg) {a d : ℕ}
    (hspan : (x (a + d)).arg - (x a).arg ≤ Real.pi) :
    (∑ k ∈ Finset.range d,
      Complex.normSq (x (a + k) - x (a + k + 1))) ≤
      Complex.normSq (x a - x (a + d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      have hpreSpan : (x (a + d)).arg - (x a).arg ≤ Real.pi := by
        have hle := hmono (show a + d ≤ a + (d + 1) by omega)
        linarith
      have hpre := ih hpreSpan
      have hlocal := chord_shortcut_of_arg (hx a) (hx (a + d))
        (hx (a + (d + 1))) (hmono (by omega)) (hmono (by omega))
        (by simpa [Nat.add_assoc] using hspan)
      calc
        (∑ k ∈ Finset.range d,
            Complex.normSq (x (a + k) - x (a + k + 1))) +
              Complex.normSq (x (a + d) - x (a + d + 1)) ≤
            Complex.normSq (x a - x (a + d)) +
              Complex.normSq (x (a + d) - x (a + d + 1)) := by gcongr
        _ ≤ Complex.normSq (x a - x (a + (d + 1))) := by
          simpa [Nat.add_assoc] using hlocal

lemma sum_range_split_three (f : ℕ → ℝ) {j k N : ℕ}
    (hjk : j ≤ k) (hkN : k ≤ N) :
    (∑ i ∈ Finset.range N, f i) =
      (∑ i ∈ Finset.range j, f i) +
      (∑ i ∈ Finset.range (k - j), f (j + i)) +
      (∑ i ∈ Finset.range (N - k), f (k + i)) := by
  have hN : N = j + (k - j) + (N - k) := by omega
  conv_lhs => rw [hN]
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have hj : j + (k - j) = k := by omega
  rw [hj]

/-- A sorted unit chain from argument `0` to argument `π` which passes through
three projectively separated gaps has a uniform energy deficit. -/
lemma chain_energy_le_of_three_gaps (x : ℕ → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1)
    (hmono : Monotone fun i ↦ (x i).arg)
    {j k N : ℕ} (hjk : j ≤ k) (hkN : k ≤ N)
    (harg0 : (x 0).arg = 0) (hargN : (x N).arg = Real.pi)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hfirst : ρ ^ 2 < Complex.normSq (x 0 - x j))
    (hmiddle : ρ ^ 2 < Complex.normSq (x j - x k))
    (hlast : ρ ^ 2 < Complex.normSq (x k - x N)) :
    (∑ i ∈ Finset.range N, Complex.normSq (x i - x (i + 1))) ≤
      4 - ρ ^ 3 := by
  let A := (x j).arg - (x 0).arg
  let B := (x k).arg - (x j).arg
  let C := (x N).arg - (x k).arg
  have hA : 0 ≤ A := sub_nonneg.mpr (hmono (by omega))
  have hB : 0 ≤ B := sub_nonneg.mpr (hmono hjk)
  have hC : 0 ≤ C := sub_nonneg.mpr (hmono hkN)
  have hsum : A + B + C = Real.pi := by dsimp [A, B, C]; linarith
  have hAπ : A ≤ Real.pi := by linarith
  have hBπ : B ≤ Real.pi := by linarith
  have hCπ : C ≤ Real.pi := by linarith
  have hsA : 0 ≤ Real.sin (A / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  have hsB : 0 ≤ Real.sin (B / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  have hsC : 0 ≤ Real.sin (C / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  have hcA : ρ < 2 * Real.sin (A / 2) := by
    rw [normSq_sub_eq_four_sin_sq_half (hx 0) (hx j)] at hfirst
    dsimp [A]
    nlinarith
  have hcB : ρ < 2 * Real.sin (B / 2) := by
    rw [normSq_sub_eq_four_sin_sq_half (hx j) (hx k)] at hmiddle
    dsimp [B]
    nlinarith
  have hcC : ρ < 2 * Real.sin (C / 2) := by
    rw [normSq_sub_eq_four_sin_sq_half (hx k) (hx N)] at hlast
    dsimp [C]
    nlinarith
  have hthree := three_chord_deficit hA hB hC hsum hcA hcB hcC hρ
  have hp := chain_range_le_chord x hx hmono (a := 0) (d := j) (by
    dsimp [A] at hAπ ⊢
    simpa using hAπ)
  have hm := chain_range_le_chord x hx hmono (a := j) (d := k - j) (by
    have : j + (k - j) = k := by omega
    simpa [this, B] using hBπ)
  have hl := chain_range_le_chord x hx hmono (a := k) (d := N - k) (by
    have : k + (N - k) = N := by omega
    simpa [this, C] using hCπ)
  rw [sum_range_split_three
    (fun i ↦ Complex.normSq (x i - x (i + 1))) hjk hkN]
  have hmidIndex : j + (k - j) = k := by omega
  have hlastIndex : k + (N - k) = N := by omega
  simp only [zero_add, hmidIndex, hlastIndex] at hp hm hl
  rw [normSq_sub_eq_four_sin_sq_half (hx 0) (hx j)] at hp
  rw [normSq_sub_eq_four_sin_sq_half (hx j) (hx k)] at hm
  rw [normSq_sub_eq_four_sin_sq_half (hx k) (hx N)] at hl
  dsimp [A, B, C] at hthree
  nlinarith

/-- The total squared chord length of an argument-sorted unit chain contained
in a semicircle is at most the squared chord between its endpoints. -/
lemma chain_energy_le_endpoint : ∀ n (x : Fin (n + 1) → ℂ),
    (∀ i, Complex.normSq (x i) = 1) →
    Monotone (fun i ↦ (x i).arg) →
    (x (Fin.last n)).arg - (x 0).arg ≤ Real.pi →
    (∑ i : Fin n, Complex.normSq (x i.castSucc - x i.succ)) ≤
      Complex.normSq (x 0 - x (Fin.last n)) := by
  intro n
  induction n with
  | zero =>
      intro x hx hmono hspan
      simp
  | succ n ih =>
      intro x hx hmono hspan
      let x' : Fin (n + 1) → ℂ := fun i ↦ x i.castSucc
      have hx' : ∀ i, Complex.normSq (x' i) = 1 := fun i ↦ hx i.castSucc
      have hmono' : Monotone (fun i ↦ (x' i).arg) := by
        intro i j hij
        exact hmono (by simpa using hij)
      have hlast_le : (x' (Fin.last n)).arg ≤ (x (Fin.last (n + 1))).arg := by
        apply hmono
        exact (Fin.castSucc_lt_last (Fin.last n)).le
      have hspan' : (x' (Fin.last n)).arg - (x' 0).arg ≤ Real.pi := by
        dsimp [x'] at hlast_le ⊢
        linarith
      have hinit := ih x' hx' hmono' hspan'
      have hlocal :
          Complex.normSq (x 0 - x' (Fin.last n)) +
              Complex.normSq (x' (Fin.last n) - x (Fin.last (n + 1))) ≤
            Complex.normSq (x 0 - x (Fin.last (n + 1))) := by
        apply chord_shortcut_of_arg (hx 0) (hx' (Fin.last n)) (hx (Fin.last (n + 1)))
        · exact hmono (Fin.zero_le _)
        · exact hlast_le
        · exact hspan
      rw [Fin.sum_univ_castSucc]
      have hprefix :
          (∑ i : Fin n,
            Complex.normSq (x i.castSucc.castSucc - x i.castSucc.succ)) =
            ∑ i : Fin n, Complex.normSq (x' i.castSucc - x' i.succ) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 3 <;> apply Fin.ext <;> rfl
      rw [hprefix]
      dsimp [x'] at hinit ⊢
      nlinarith

/-- Choose the representative of a projective direction in the closed upper
half-plane. -/
noncomputable def upperRep (z : ℂ) : ℂ := if 0 ≤ z.im then z else -z

lemma normSq_upperRep (z : ℂ) : Complex.normSq (upperRep z) = Complex.normSq z := by
  unfold upperRep
  split_ifs <;> simp

lemma upperRep_im_nonneg (z : ℂ) : 0 ≤ (upperRep z).im := by
  simp only [upperRep]
  split_ifs with h
  · exact h
  · simp only [Complex.neg_im]
    exact neg_nonneg.mpr (le_of_not_ge h)

lemma upperRep_arg_mem (z : ℂ) :
    0 ≤ (upperRep z).arg ∧ (upperRep z).arg ≤ Real.pi := by
  constructor
  · exact Complex.arg_nonneg_iff.mpr (upperRep_im_nonneg z)
  · have h := Complex.abs_arg_le_pi (upperRep z)
    exact (abs_le.mp h).2

/-- Two unit directions are separated in projective chord distance by more
than `ρ`.  The squared formulation avoids square roots. -/
def ProjectivelyFarSq (ρ : ℝ) (u v : ℂ) : Prop :=
  ρ ^ 2 < Complex.normSq (u - v) ∧
    ρ ^ 2 < Complex.normSq (u + v)

def ProjectivelyCloseSq (ρ : ℝ) (u v : ℂ) : Prop :=
  Complex.normSq (u - v) ≤ ρ ^ 2 ∨
    Complex.normSq (u + v) ≤ ρ ^ 2

lemma not_projectivelyCloseSq_iff {ρ : ℝ} {u v : ℂ} :
    ¬ProjectivelyCloseSq ρ u v ↔ ProjectivelyFarSq ρ u v := by
  simp [ProjectivelyCloseSq, ProjectivelyFarSq, not_or]

lemma projectivelyCloseSq_symm {ρ : ℝ} {u v : ℂ}
    (h : ProjectivelyCloseSq ρ u v) : ProjectivelyCloseSq ρ v u := by
  rcases h with h | h
  · left
    rw [show v - u = -(u - v) by ring, Complex.normSq_neg]
    exact h
  · right
    simpa [add_comm] using h

lemma projectivelyCloseSq_neg_left {ρ : ℝ} {u v : ℂ}
    (h : ProjectivelyCloseSq ρ u v) : ProjectivelyCloseSq ρ (-u) v := by
  rcases h with h | h
  · right
    rw [show -u + v = -(u - v) by ring, Complex.normSq_neg]
    exact h
  · left
    rw [show -u - v = -(u + v) by ring, Complex.normSq_neg]
    exact h

lemma projectivelyCloseSq_neg_right {ρ : ℝ} {u v : ℂ}
    (h : ProjectivelyCloseSq ρ u v) : ProjectivelyCloseSq ρ u (-v) := by
  exact projectivelyCloseSq_symm
    (projectivelyCloseSq_neg_left (projectivelyCloseSq_symm h))

lemma projectivelyCloseSq_mul {ρ : ℝ} {c u v : ℂ}
    (hc : Complex.normSq c = 1) (h : ProjectivelyCloseSq ρ u v) :
    ProjectivelyCloseSq ρ (c * u) (c * v) := by
  rcases h with h | h
  · left
    simpa [← mul_sub, Complex.normSq_mul, hc] using h
  · right
    simpa [← mul_add, Complex.normSq_mul, hc] using h

lemma projectivelyFarSq_symm {ρ : ℝ} {u v : ℂ}
    (h : ProjectivelyFarSq ρ u v) : ProjectivelyFarSq ρ v u := by
  constructor
  · rw [show v - u = -(u - v) by ring, Complex.normSq_neg]
    exact h.1
  · simpa [ProjectivelyFarSq, add_comm] using h.2

/-- Either three projective directions are pairwise far apart, or two
projective balls cover the entire nonempty sequence. -/
lemma three_far_or_two_cluster {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℂ) (ρ : ℝ) :
    (∃ a b c : Fin n,
      ProjectivelyFarSq ρ (z a) (z b) ∧
      ProjectivelyFarSq ρ (z a) (z c) ∧
      ProjectivelyFarSq ρ (z b) (z c)) ∨
    (∃ a b : Fin n, ∀ i,
      ProjectivelyCloseSq ρ (z a) (z i) ∨
      ProjectivelyCloseSq ρ (z b) (z i)) := by
  let a : Fin n := ⟨0, hn⟩
  by_cases ha : ∀ i, ProjectivelyCloseSq ρ (z a) (z i)
  · right
    exact ⟨a, a, fun i ↦ Or.inl (ha i)⟩
  · push_neg at ha
    obtain ⟨b, hab⟩ := ha
    by_cases hc : ∀ i,
        ProjectivelyCloseSq ρ (z a) (z i) ∨
        ProjectivelyCloseSq ρ (z b) (z i)
    · exact Or.inr ⟨a, b, hc⟩
    · push_neg at hc
      obtain ⟨c, hac, hbc⟩ := hc
      left
      exact ⟨a, b, c,
        not_projectivelyCloseSq_iff.mp hab,
        not_projectivelyCloseSq_iff.mp hac,
        not_projectivelyCloseSq_iff.mp hbc⟩

lemma projectivelyFarSq_neg_left {ρ : ℝ} {u v : ℂ}
    (h : ProjectivelyFarSq ρ u v) : ProjectivelyFarSq ρ (-u) v := by
  constructor
  · rw [show -u - v = -(u + v) by ring, Complex.normSq_neg]
    exact h.2
  · rw [show -u + v = -(u - v) by ring, Complex.normSq_neg]
    exact h.1

lemma projectivelyFarSq_neg_right {ρ : ℝ} {u v : ℂ}
    (h : ProjectivelyFarSq ρ u v) : ProjectivelyFarSq ρ u (-v) := by
  exact projectivelyFarSq_symm (projectivelyFarSq_neg_left (projectivelyFarSq_symm h))

lemma pair_center_product_ge_one_of_far_one_third {ρ : ℝ} {u v : ℂ}
    (hρ : ρ ^ 2 = (1 : ℝ) / 3)
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hfar : ProjectivelyFarSq ρ u v) :
    1 ≤ Complex.normSq (u + v) * Complex.normSq (u - v) := by
  have hminus := hfar.1
  rw [hρ, normSq_sub_eq, hu, hv] at hminus
  norm_num at hminus
  have hplus := hfar.2
  rw [hρ, normSq_add_eq, hu, hv] at hplus
  norm_num at hplus
  have hprod : 0 < ((5 : ℝ) / 6 - dot u v) *
      ((5 : ℝ) / 6 + dot u v) := by
    apply mul_pos <;> linarith
  rw [pair_center_product u v hu hv]
  nlinarith

lemma projectivelyFarSq_mul {ρ : ℝ} {c u v : ℂ}
    (hc : Complex.normSq c = 1) (h : ProjectivelyFarSq ρ u v) :
    ProjectivelyFarSq ρ (c * u) (c * v) := by
  constructor
  · simpa [ProjectivelyFarSq, ← mul_sub, Complex.normSq_mul, hc] using h.1
  · simpa [ProjectivelyFarSq, ← mul_add, Complex.normSq_mul, hc] using h.2

lemma projectivelyFarSq_upperRep {ρ : ℝ} {u v : ℂ}
    (h : ProjectivelyFarSq ρ u v) :
    ProjectivelyFarSq ρ (upperRep u) (upperRep v) := by
  unfold upperRep
  split_ifs
  · exact h
  · exact projectivelyFarSq_neg_right h
  · exact projectivelyFarSq_neg_left h
  · exact projectivelyFarSq_neg_right (projectivelyFarSq_neg_left h)

noncomputable def nearRep (ρ : ℝ) (z : ℂ) : ℂ :=
  if Complex.normSq (z - 1) ≤ ρ ^ 2 then z else -z

noncomputable def nearChoice (ρ : ℝ) (z : ℂ) : Bool :=
  decide (Complex.normSq (z - 1) ≤ ρ ^ 2)

lemma nearRep_eq_choice_mul (ρ : ℝ) (z : ℂ) :
    nearRep ρ z = (sign (nearChoice ρ z) : ℂ) * z := by
  by_cases h : Complex.normSq (z - 1) ≤ ρ ^ 2
  · simp [nearRep, nearChoice, h]
  · simp [nearRep, nearChoice, h]

lemma normSq_nearRep (ρ : ℝ) (z : ℂ) :
    Complex.normSq (nearRep ρ z) = Complex.normSq z := by
  unfold nearRep
  split_ifs <;> simp

lemma nearRep_close_one {ρ : ℝ} {z : ℂ}
    (hclose : ProjectivelyCloseSq ρ z 1) :
    Complex.normSq (nearRep ρ z - 1) ≤ ρ ^ 2 := by
  unfold nearRep
  split_ifs with h
  · exact h
  · rcases hclose with hclose | hclose
    · exact (h hclose).elim
    · rw [show -z - 1 = -(z + 1) by ring, Complex.normSq_neg]
      exact hclose

lemma nearRep_re_nonneg {ρ : ℝ} {z : ℂ}
    (hz : Complex.normSq z = 1) (hρ : ρ ^ 2 ≤ 2)
    (hclose : ProjectivelyCloseSq ρ z 1) : 0 ≤ (nearRep ρ z).re := by
  have hunit : Complex.normSq (nearRep ρ z) = 1 := by
    rw [normSq_nearRep, hz]
  have hdist := nearRep_close_one hclose
  rw [Complex.normSq_apply] at hunit hdist
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im] at hdist
  nlinarith [sq_nonneg ((nearRep ρ z).re - 1), sq_nonneg (nearRep ρ z).im]

lemma nearRep_arg_mem {ρ : ℝ} {z : ℂ}
    (hz : Complex.normSq z = 1) (hρ : ρ ^ 2 ≤ 2)
    (hclose : ProjectivelyCloseSq ρ z 1) :
    -(Real.pi / 2) ≤ (nearRep ρ z).arg ∧
      (nearRep ρ z).arg ≤ Real.pi / 2 := by
  have hre := nearRep_re_nonneg hz hρ hclose
  constructor
  · exact Complex.neg_pi_div_two_le_arg_iff.mpr (Or.inl hre)
  · exact Complex.arg_le_pi_div_two_iff.mpr (Or.inl hre)

noncomputable def centeredNearRep (ρ : ℝ) (a z : ℂ) : ℂ :=
  nearRep ρ (conj a * z)

noncomputable def towardRep (ρ : ℝ) (a z : ℂ) : ℂ :=
  a * centeredNearRep ρ a z

lemma towardRep_eq_choice_mul {ρ : ℝ} {a z : ℂ}
    (ha : Complex.normSq a = 1) :
    towardRep ρ a z = (sign (nearChoice ρ (conj a * z)) : ℂ) * z := by
  rw [towardRep, centeredNearRep, nearRep_eq_choice_mul]
  have haa : a * conj a = (1 : ℂ) := by
    rw [Complex.mul_conj]
    norm_cast
  calc
    a * ((sign (nearChoice ρ (conj a * z)) : ℂ) * (conj a * z)) =
        (sign (nearChoice ρ (conj a * z)) : ℂ) * ((a * conj a) * z) := by ring
    _ = (sign (nearChoice ρ (conj a * z)) : ℂ) * z := by rw [haa, one_mul]

lemma centeredNearRep_unit {ρ : ℝ} {a z : ℂ}
    (ha : Complex.normSq a = 1) (hz : Complex.normSq z = 1) :
    Complex.normSq (centeredNearRep ρ a z) = 1 := by
  simp [centeredNearRep, normSq_nearRep, Complex.normSq_mul,
    Complex.normSq_conj, ha, hz]

lemma centeredNearRep_close_one {ρ : ℝ} {a z : ℂ}
    (ha : Complex.normSq a = 1) (hclose : ProjectivelyCloseSq ρ a z) :
    Complex.normSq (centeredNearRep ρ a z - 1) ≤ ρ ^ 2 := by
  have hrot := projectivelyCloseSq_mul
    (c := conj a) (by simpa [Complex.normSq_conj] using ha) hclose
  have haa : conj a * a = (1 : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
  rw [haa] at hrot
  exact nearRep_close_one (projectivelyCloseSq_symm hrot)

/-- Within the projective ball of squared chord radius `1/3`, projective
closeness of two representatives is necessarily direct closeness. -/
lemma direct_close_of_close_one_third {ρ : ℝ} {x y : ℂ}
    (hρ : ρ ^ 2 = (1 : ℝ) / 3)
    (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1)
    (hx1 : Complex.normSq (x - 1) ≤ (1 : ℝ) / 3)
    (hy1 : Complex.normSq (y - 1) ≤ (1 : ℝ) / 3)
    (hxy : ProjectivelyCloseSq ρ x y) :
    Complex.normSq (x - y) ≤ (1 : ℝ) / 3 := by
  rcases hxy with hxy | hplus
  · simpa [hρ] using hxy
  · exfalso
    have hxre : (5 : ℝ) / 6 ≤ x.re := by
      simp [Complex.normSq_apply] at hx hx1
      nlinarith
    have hyre : (5 : ℝ) / 6 ≤ y.re := by
      simp [Complex.normSq_apply] at hy hy1
      nlinarith
    have hxim : x.im ^ 2 ≤ (11 : ℝ) / 36 := by
      simp [Complex.normSq_apply] at hx
      nlinarith
    have hyim : y.im ^ 2 ≤ (11 : ℝ) / 36 := by
      simp [Complex.normSq_apply] at hy
      nlinarith
    have hreprod : (25 : ℝ) / 36 ≤ x.re * y.re := by
      have hmul := mul_nonneg (sub_nonneg.mpr hxre) (sub_nonneg.mpr hyre)
      nlinarith
    have himprod : -(11 : ℝ) / 36 ≤ x.im * y.im := by
      nlinarith [sq_nonneg (x.im + y.im)]
    have hdotlow : (7 : ℝ) / 18 ≤ dot x y := by
      simp only [dot]
      linarith
    have hdotup : dot x y ≤ -(5 : ℝ) / 6 := by
      rw [normSq_add_eq, hx, hy, hρ] at hplus
      linarith
    linarith

lemma projectivelyCloseSq_centeredNearRep {ρ : ℝ} {a x y : ℂ}
    (ha : Complex.normSq a = 1) (hxy : ProjectivelyCloseSq ρ x y) :
    ProjectivelyCloseSq ρ (centeredNearRep ρ a x) (centeredNearRep ρ a y) := by
  have hrot := projectivelyCloseSq_mul
    (c := conj a) (by simpa [Complex.normSq_conj] using ha) hxy
  rw [centeredNearRep, centeredNearRep, nearRep_eq_choice_mul,
    nearRep_eq_choice_mul]
  cases hx : nearChoice ρ (conj a * x) <;>
    cases hy : nearChoice ρ (conj a * y)
  · simpa [hx, hy, sign] using projectivelyCloseSq_neg_right
      (projectivelyCloseSq_neg_left hrot)
  · simpa [hx, hy, sign] using projectivelyCloseSq_neg_left hrot
  · simpa [hx, hy, sign] using projectivelyCloseSq_neg_right hrot
  · simpa [hx, hy, sign] using hrot

lemma centeredNearRep_arg_mem {ρ : ℝ} {a z : ℂ}
    (ha : Complex.normSq a = 1) (hz : Complex.normSq z = 1)
    (hρ : ρ ^ 2 ≤ 2) (hclose : ProjectivelyCloseSq ρ a z) :
    -(Real.pi / 2) ≤ (centeredNearRep ρ a z).arg ∧
      (centeredNearRep ρ a z).arg ≤ Real.pi / 2 := by
  apply nearRep_arg_mem
  · simp [Complex.normSq_mul, Complex.normSq_conj, ha, hz]
  · exact hρ
  · have hrot := projectivelyCloseSq_mul
      (c := conj a) (by simpa [Complex.normSq_conj] using ha) hclose
    have haa : conj a * a = (1 : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
      norm_cast
    rw [haa] at hrot
    exact projectivelyCloseSq_symm hrot

structure SortIndex (n : ℕ) where
  val : Fin n
deriving Fintype, DecidableEq

def sortIndexEquivFin (n : ℕ) : SortIndex n ≃ Fin n where
  toFun := SortIndex.val
  invFun := SortIndex.mk
  left_inv := by intro i; cases i; rfl
  right_inv := by intro i; rfl

/-- Every finite sequence can be reindexed so that its arguments are
nondecreasing.  `SortIndex` keeps the lifted sorting order separate from the
standard order on the domain `Fin n`. -/
lemma exists_arg_sorted_equiv {n : ℕ} (x : Fin n → ℂ) :
    ∃ e : Fin n ≃ Fin n, Monotone (fun i ↦ (x (e i)).arg) := by
  classical
  let key : SortIndex n → ℝ ×ₗ ℕ :=
    fun i ↦ toLex ((x i.val).arg, i.val.val)
  have hkey : Function.Injective key := by
    intro i j hij
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    congr 1
    apply Fin.ext
    exact congrArg (fun p : ℝ ×ₗ ℕ ↦ (ofLex p).2) hij
  letI : LinearOrder (SortIndex n) := LinearOrder.lift' key hkey
  let ord : Fin n ≃o {i : SortIndex n //
      i ∈ (Finset.univ : Finset (SortIndex n))} :=
    (Finset.univ : Finset (SortIndex n)).orderIsoOfFin (k := n) (by
      simp only [Finset.card_univ]
      simpa using Fintype.card_congr (sortIndexEquivFin n))
  let forget : {i : SortIndex n //
      i ∈ (Finset.univ : Finset (SortIndex n))} ≃
      Fin n :=
    { toFun := fun i ↦ i.1.val
      invFun := fun i ↦ ⟨⟨i⟩, Finset.mem_univ _⟩
      left_inv := by intro i; cases i; rfl
      right_inv := by intro i; rfl }
  let e : Fin n ≃ Fin n := ord.toEquiv.trans forget
  refine ⟨e, ?_⟩
  intro i j hij
  have hord : ord i ≤ ord j := ord.monotone hij
  change key (ord i).1 ≤ key (ord j).1 at hord
  have hordKey := hord
  have hlex := Prod.Lex.toLex_le_toLex.mp hordKey
  change (x (e i)).arg ≤ (x (e j)).arg
  rcases hlex with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact le_of_eq heq

/-! ### Invariance of the finite sign model -/

lemma card_filter_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : B → Prop) [DecidablePred P] :
    (Finset.univ.filter fun a ↦ P (e a)).card =
      (Finset.univ.filter P).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv fun _ ↦ Iff.rfl)

def reindexSigns {n : ℕ} (e : Fin n ≃ Fin n) : SignVec n ≃ SignVec n where
  toFun ε := fun j ↦ ε (e.symm j)
  invFun ε := fun i ↦ ε (e i)
  left_inv := by intro ε; ext i; simp
  right_inv := by intro ε; ext i; simp

def reindexSignsGeneral {m n : ℕ} (e : Fin m ≃ Fin n) :
    SignVec m ≃ SignVec n where
  toFun ε := fun j ↦ ε (e.symm j)
  invFun ε := fun i ↦ ε (e i)
  left_inv := by intro ε; ext i; simp
  right_inv := by intro ε; ext i; simp

lemma signedSum_reindex {n : ℕ} (z : Fin n → ℂ) (e : Fin n ≃ Fin n)
    (ε : SignVec n) :
    signedSum (fun i ↦ z (e i)) ε = signedSum z (reindexSigns e ε) := by
  unfold signedSum reindexSigns
  simpa using e.sum_comp
    (fun j ↦ (sign (ε (e.symm j)) : ℂ) * z j)

lemma signedSum_reindex_general {m n : ℕ} (z : Fin n → ℂ)
    (e : Fin m ≃ Fin n) (ε : SignVec m) :
    signedSum (fun i ↦ z (e i)) ε =
      signedSum z (reindexSignsGeneral e ε) := by
  unfold signedSum reindexSignsGeneral
  simpa using e.sum_comp
    (fun j ↦ (sign (ε (e.symm j)) : ℂ) * z j)

lemma card_signedSum_reindex_general {m n : ℕ} (z : Fin n → ℂ)
    (e : Fin m ≃ Fin n) (P : ℂ → Prop) [DecidablePred P] :
    ((Finset.univ.filter fun ε : SignVec m ↦
      P (signedSum (fun i ↦ z (e i)) ε)).card) =
    ((Finset.univ.filter fun ε : SignVec n ↦ P (signedSum z ε)).card) := by
  have h := card_filter_comp_equiv (reindexSignsGeneral e)
    (fun ε : SignVec n ↦ P (signedSum z ε))
  simpa [signedSum_reindex_general] using h

def reindexSignPairGeneral {m n : ℕ} (e : Fin m ≃ Fin n) :
    SignPair m ≃ SignPair n :=
  Equiv.prodCongr (reindexSignsGeneral e) (reindexSignsGeneral e)

lemma pairSignedSum_reindex_general {m n : ℕ} (u v : Fin n → ℂ)
    (e : Fin m ≃ Fin n) (q : SignPair m) :
    pairSignedSum (fun i ↦ u (e i)) (fun i ↦ v (e i)) q =
      pairSignedSum u v (reindexSignPairGeneral e q) := by
  rcases q with ⟨x, y⟩
  simp [pairSignedSum, reindexSignPairGeneral, signedSum_reindex_general]

lemma card_pairSignedSum_reindex_general {m n : ℕ} (u v : Fin n → ℂ)
    (e : Fin m ≃ Fin n) (R : ℝ) :
    ((Finset.univ.filter fun q : SignPair m ↦
      Complex.normSq
        (pairSignedSum (fun i ↦ u (e i)) (fun i ↦ v (e i)) q) < R).card) =
    ((Finset.univ.filter fun q : SignPair n ↦
      Complex.normSq (pairSignedSum u v q) < R).card) := by
  have h := card_filter_comp_equiv (reindexSignPairGeneral e)
    (fun q : SignPair n ↦ Complex.normSq (pairSignedSum u v q) < R)
  simpa only [pairSignedSum_reindex_general] using h

def signMul (a b : Bool) : Bool := decide (a = b)

@[simp] lemma sign_signMul (a b : Bool) : sign (signMul a b) = sign a * sign b := by
  cases a <;> cases b <;> simp [signMul, sign]

def twistSigns {n : ℕ} (t : SignVec n) : SignVec n ≃ SignVec n where
  toFun ε := fun i ↦ signMul (ε i) (t i)
  invFun ε := fun i ↦ signMul (ε i) (t i)
  left_inv := by
    intro ε
    ext i
    cases hε : ε i <;> cases ht : t i <;> simp [signMul, hε, ht]
  right_inv := by
    intro ε
    ext i
    cases hε : ε i <;> cases ht : t i <;> simp [signMul, hε, ht]

def signedOrient {n : ℕ} (z : Fin n → ℂ) (t : SignVec n) : Fin n → ℂ :=
  fun i ↦ (sign (t i) : ℂ) * z i

lemma signedSum_signedOrient {n : ℕ} (z : Fin n → ℂ) (t ε : SignVec n) :
    signedSum (signedOrient z t) ε = signedSum z (twistSigns t ε) := by
  unfold signedSum signedOrient twistSigns
  apply Finset.sum_congr rfl
  intro i _
  change (sign (ε i) : ℂ) * ((sign (t i) : ℂ) * z i) =
    (sign (signMul (ε i) (t i)) : ℂ) * z i
  rw [sign_signMul]
  push_cast
  ring

lemma card_smallBall_reindex {n : ℕ} (z : Fin n → ℂ) (e : Fin n ≃ Fin n)
    (R : ℝ) :
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum (fun i ↦ z (e i)) ε) < R).card) =
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum z ε) < R).card) := by
  have h := card_filter_comp_equiv (reindexSigns e)
    (fun ε : SignVec n ↦ Complex.normSq (signedSum z ε) < R)
  simpa [signedSum_reindex] using h

lemma card_smallBall_reindex_general {m n : ℕ} (z : Fin n → ℂ)
    (e : Fin m ≃ Fin n) (R : ℝ) :
    ((Finset.univ.filter fun ε : SignVec m ↦
      Complex.normSq (signedSum (fun i ↦ z (e i)) ε) < R).card) =
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum z ε) < R).card) := by
  have h := card_filter_comp_equiv (reindexSignsGeneral e)
    (fun ε : SignVec n ↦ Complex.normSq (signedSum z ε) < R)
  simpa [signedSum_reindex_general] using h

lemma card_smallBall_signedOrient {n : ℕ} (z : Fin n → ℂ) (t : SignVec n)
    (R : ℝ) :
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum (signedOrient z t) ε) < R).card) =
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum z ε) < R).card) := by
  have h := card_filter_comp_equiv (twistSigns t)
    (fun ε : SignVec n ↦ Complex.normSq (signedSum z ε) < R)
  simpa [signedSum_signedOrient] using h

lemma card_smallBall_oriented_reindex_general {m n : ℕ} (z : Fin n → ℂ)
    (e : Fin m ≃ Fin n) (t : SignVec m) (R : ℝ) :
    ((Finset.univ.filter fun ε : SignVec m ↦
      Complex.normSq
        (signedSum (fun i ↦ (sign (t i) : ℂ) * z (e i)) ε) < R).card) =
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum z ε) < R).card) := by
  let w : Fin m → ℂ := fun i ↦ z (e i)
  change ((Finset.univ.filter fun ε : SignVec m ↦
      Complex.normSq (signedSum (signedOrient w t) ε) < R).card) = _
  rw [card_smallBall_signedOrient]
  exact card_smallBall_reindex_general z e R

lemma signedSum_append {m n : ℕ} (u : Fin m → ℂ) (v : Fin n → ℂ)
    (a : SignVec m) (b : SignVec n) :
    signedSum (Fin.append u v) (Fin.append a b) = signedSum u a + signedSum v b := by
  simp [signedSum, Fin.sum_univ_add]

lemma exists_three_signs_cover_large {u v x w : ℂ}
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hx : Complex.normSq x = 1) (hw : Complex.normSq w ≤ 2)
    (hproduct : 1 ≤ Complex.normSq (u + v) * Complex.normSq (u - v)) :
    ∃ δ : Fin 3 → Bool,
      Complex.normSq (w + signedSum ![u, v, x] δ) ≤ 2 := by
  obtain ⟨bx, hbx⟩ := exists_one_sign_normSq_le_add_one (w := w) hx
  have hw' : Complex.normSq (w + (sign bx : ℂ) * x) ≤ 3 := by linarith
  obtain ⟨d, hd⟩ := exists_two_signs_cover_large hu hv hw' hproduct
  refine ⟨![d 0, d 1, bx], ?_⟩
  have hsum :
      w + signedSum ![u, v, x] ![d 0, d 1, bx] =
        (w + (sign bx : ℂ) * x) + signedSum ![u, v] d := by
    simp [signedSum, Fin.sum_univ_succ, Fin.sum_univ_two, sign, mul_comm]
    abel
  rw [hsum]
  exact hd

lemma card_residual_le_one_extension {m : ℕ} (z : Fin m → ℂ)
    (u : ℂ) (hu : Complex.normSq u = 1) :
    ((Finset.univ.filter fun ε : SignVec m ↦
      Complex.normSq (signedSum z ε) < (1 : ℝ)).card) ≤
    ((Finset.univ.filter fun ε : SignVec (m + 1) ↦
      Complex.normSq (signedSum (Fin.append z ![u]) ε) ≤ 2).card) := by
  apply card_filter_le_of_extensions
  intro ε hε
  obtain ⟨b, hb⟩ := exists_one_sign_normSq_le_add_one (w := signedSum z ε) hu
  refine ⟨![b], ?_⟩
  rw [signedSum_append]
  have : signedSum ![u] ![b] = (sign b : ℂ) * u := by
    simp [signedSum]
  rw [this]
  linarith

lemma card_residual_le_three_extension {m : ℕ} (z : Fin m → ℂ)
    (u v x : ℂ) (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hx : Complex.normSq x = 1)
    (hproduct : 1 ≤ Complex.normSq (u + v) * Complex.normSq (u - v)) :
    ((Finset.univ.filter fun ε : SignVec m ↦
      Complex.normSq (signedSum z ε) ≤ 2).card) ≤
    ((Finset.univ.filter fun ε : SignVec (m + 3) ↦
      Complex.normSq (signedSum (Fin.append z ![u, v, x]) ε) ≤ 2).card) := by
  apply card_filter_le_of_extensions
  intro ε hε
  obtain ⟨d, hd⟩ := exists_three_signs_cover_large hu hv hx hε hproduct
  refine ⟨d, ?_⟩
  rw [signedSum_append]
  exact hd

lemma card_residual_le_two_extension {m : ℕ} (z : Fin m → ℂ)
    (u v : ℂ) (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1) :
    ((Finset.univ.filter fun ε : SignVec m ↦
      Complex.normSq (signedSum z ε) < (1 : ℝ) / 4).card) ≤
    ((Finset.univ.filter fun ε : SignVec (m + 2) ↦
      Complex.normSq (signedSum (Fin.append z ![u, v]) ε) ≤ 2).card) := by
  apply card_filter_le_of_extensions
  intro ε hε
  obtain ⟨δ, hδ⟩ := exists_two_signs_cover_small hu hv (le_of_lt hε)
  refine ⟨δ, ?_⟩
  rw [signedSum_append]
  exact hδ

lemma uniformProbability_pair_eq {m : ℕ} (u v : Fin m → ℂ)
    (z : Fin (2 * m) → ℂ) (R : ℝ)
    (hcard :
      ((Finset.univ.filter fun q : SignPair m ↦
        Complex.normSq (pairSignedSum u v q) < R).card) =
      ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
        Complex.normSq (signedSum z ε) < R).card)) :
    uniformProbability (fun q : SignPair m ↦
        Complex.normSq (pairSignedSum u v q) < R) =
      uniformProbability (fun ε : SignVec (2 * m) ↦
        Complex.normSq (signedSum z ε) < R) := by
  have hden : Fintype.card (SignPair m) =
      Fintype.card (SignVec (2 * m)) := by
    simp only [Fintype.card_prod, card_signCube]
    rw [← pow_add]
    congr 1
    omega
  unfold uniformProbability
  rw [hcard, hden]

lemma uniformProbability_pair_le_four_of_card_le {r : ℕ}
    (u v : Fin r → ℂ) (z : Fin (2 * (r + 1)) → ℂ)
    (hle :
      ((Finset.univ.filter fun q : SignPair r ↦
        Complex.normSq (pairSignedSum u v q) < (1 : ℝ) / 4).card) ≤
      ((Finset.univ.filter fun ε : SignVec (2 * (r + 1)) ↦
        Complex.normSq (signedSum z ε) ≤ 2).card)) :
    uniformProbability (fun q : SignPair r ↦
        Complex.normSq (pairSignedSum u v q) < (1 : ℝ) / 4) ≤
      4 * uniformProbability (fun ε : SignVec (2 * (r + 1)) ↦
        Complex.normSq (signedSum z ε) ≤ 2) := by
  unfold uniformProbability
  simp only [Fintype.card_prod, card_signCube]
  push_cast
  have hp : 0 < (2 : ℝ) ^ (2 * r) := by positivity
  have hcast :
      (((Finset.univ.filter fun q : SignPair r ↦
        Complex.normSq (pairSignedSum u v q) < (1 : ℝ) / 4).card : ℕ) : ℝ) ≤
      (((Finset.univ.filter fun ε : SignVec (2 * (r + 1)) ↦
        Complex.normSq (signedSum z ε) ≤ 2).card : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hsq : (2 : ℝ) ^ r * (2 : ℝ) ^ r = (2 : ℝ) ^ (2 * r) := by
    rw [← pow_add]
    congr 1
    omega
  have hfour : (2 : ℝ) ^ (2 * (r + 1)) =
      4 * (2 : ℝ) ^ (2 * r) := by
    rw [show 2 * (r + 1) = 2 * r + 2 by omega, pow_add]
    norm_num
    ring
  rw [hsq, hfour]
  refine (div_le_div_of_nonneg_right hcast hp.le).trans ?_
  field_simp
  exact le_rfl

lemma uniformProbability_le_two_of_card_le_one_extension {r : ℕ}
    (P : SignVec r → Prop) (Q : SignVec (r + 1) → Prop)
    (hle : (Finset.univ.filter P).card ≤ (Finset.univ.filter Q).card) :
    uniformProbability P ≤ 2 * uniformProbability Q := by
  unfold uniformProbability
  simp only [card_signCube]
  push_cast
  have hp : 0 < (2 : ℝ) ^ r := by positivity
  have hcast : ((Finset.univ.filter P).card : ℝ) ≤
      ((Finset.univ.filter Q).card : ℝ) := by exact_mod_cast hle
  have htwo : (2 : ℝ) ^ (r + 1) = 2 * (2 : ℝ) ^ r := by
    rw [pow_add]
    ring
  rw [htwo]
  refine (div_le_div_of_nonneg_right hcast hp.le).trans ?_
  field_simp
  exact le_rfl

lemma uniformProbability_le_eight_of_card_le_three_extension {r : ℕ}
    (P : SignVec r → Prop) (Q : SignVec (r + 3) → Prop)
    (hle : (Finset.univ.filter P).card ≤ (Finset.univ.filter Q).card) :
    uniformProbability P ≤ 8 * uniformProbability Q := by
  unfold uniformProbability
  simp only [card_signCube]
  push_cast
  have hp : 0 < (2 : ℝ) ^ r := by positivity
  have hcast : ((Finset.univ.filter P).card : ℝ) ≤
      ((Finset.univ.filter Q).card : ℝ) := by exact_mod_cast hle
  have height : (2 : ℝ) ^ (r + 3) = 8 * (2 : ℝ) ^ r := by
    rw [pow_add]
    norm_num
    ring
  rw [height]
  refine (div_le_div_of_nonneg_right hcast hp.le).trans ?_
  field_simp
  exact le_rfl

lemma card_smallBall_append_pair {m : ℕ} (u v : Fin m → ℂ) (R : ℝ) :
    ((Finset.univ.filter fun ε : SignVec (m + m) ↦
      Complex.normSq (signedSum (Fin.append u v) ε) < R).card) =
    ((Finset.univ.filter fun q : SignPair m ↦
      Complex.normSq (pairSignedSum u v q) < R).card) := by
  have h := card_filter_comp_equiv (Fin.appendEquiv m m)
    (fun ε : SignVec (m + m) ↦
      Complex.normSq (signedSum (Fin.append u v) ε) < R)
  have happ (q : SignPair m) :
      signedSum (Fin.append u v) (Fin.appendEquiv m m q) = pairSignedSum u v q := by
    rcases q with ⟨a, b⟩
    exact signedSum_append u v a b
  simpa only [happ] using h.symm

noncomputable def upperChoice (z : ℂ) : Bool := if 0 ≤ z.im then true else false

lemma upperRep_eq_choice_mul (z : ℂ) :
    upperRep z = (sign (upperChoice z) : ℂ) * z := by
  unfold upperRep upperChoice
  split_ifs <;> simp

lemma signedSum_const_mul {n : ℕ} (c : ℂ) (z : Fin n → ℂ) (ε : SignVec n) :
    signedSum (fun i ↦ c * z i) ε = c * signedSum z ε := by
  unfold signedSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma card_smallBall_unit_mul {n : ℕ} (c : ℂ) (hc : Complex.normSq c = 1)
    (z : Fin n → ℂ) (R : ℝ) :
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum (fun i ↦ c * z i) ε) < R).card) =
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum z ε) < R).card) := by
  apply congrArg Finset.card
  ext ε
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, signedSum_const_mul,
    Complex.normSq_mul, hc, one_mul]

noncomputable def anchoredRep (a z : ℂ) : ℂ := upperRep (conj a * z)

lemma projectivelyFarSq_anchoredRep {ρ : ℝ} {a u v : ℂ}
    (ha : Complex.normSq a = 1) (h : ProjectivelyFarSq ρ u v) :
    ProjectivelyFarSq ρ (anchoredRep a u) (anchoredRep a v) := by
  apply projectivelyFarSq_upperRep
  apply projectivelyFarSq_mul
  · simpa [Complex.normSq_conj] using ha
  · exact h

lemma card_smallBall_anchored_reindex {n : ℕ} (z : Fin n → ℂ)
    (a : ℂ) (ha : Complex.normSq a = 1) (e : Fin n ≃ Fin n) (R : ℝ) :
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq
        (signedSum (fun i ↦ anchoredRep a (z (e i))) ε) < R).card) =
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum z ε) < R).card) := by
  let w : Fin n → ℂ := fun i ↦ conj a * z (e i)
  let t : SignVec n := fun i ↦ upperChoice (w i)
  have hx : (fun i ↦ anchoredRep a (z (e i))) = signedOrient w t := by
    funext i
    exact upperRep_eq_choice_mul (w i)
  rw [hx, card_smallBall_signedOrient]
  change ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum (fun i ↦ conj a * z (e i)) ε) < R).card) = _
  rw [card_smallBall_unit_mul (conj a) (by simpa [Complex.normSq_conj] using ha)]
  exact card_smallBall_reindex z e R

lemma card_smallBall_centeredNear_reindex {n : ℕ} (ρ : ℝ) (z : Fin n → ℂ)
    (a : ℂ) (ha : Complex.normSq a = 1) (e : Fin n ≃ Fin n) (R : ℝ) :
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq
        (signedSum (fun i ↦ centeredNearRep ρ a (z (e i))) ε) < R).card) =
    ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum z ε) < R).card) := by
  let w : Fin n → ℂ := fun i ↦ conj a * z (e i)
  let t : SignVec n := fun i ↦ nearChoice ρ (w i)
  have hx : (fun i ↦ centeredNearRep ρ a (z (e i))) = signedOrient w t := by
    funext i
    exact nearRep_eq_choice_mul ρ (w i)
  rw [hx, card_smallBall_signedOrient]
  change ((Finset.univ.filter fun ε : SignVec n ↦
      Complex.normSq (signedSum (fun i ↦ conj a * z (e i)) ε) < R).card) = _
  rw [card_smallBall_unit_mul (conj a) (by simpa [Complex.normSq_conj] using ha)]
  exact card_smallBall_reindex z e R

lemma normSq_anchoredRep {a z : ℂ} (ha : Complex.normSq a = 1)
    (hz : Complex.normSq z = 1) : Complex.normSq (anchoredRep a z) = 1 := by
  simp [anchoredRep, normSq_upperRep, Complex.normSq_mul,
    Complex.normSq_conj, ha, hz]

lemma anchoredRep_self {a : ℂ} (ha : Complex.normSq a = 1) :
    anchoredRep a a = 1 := by
  have hmul : conj a * a = (1 : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
  simp [anchoredRep, hmul, upperRep]

/-- After a common unit rotation, projective sign choices, and a permutation,
the directions form an argument-sorted upper-semicircle sequence beginning at
`1`. -/
lemma exists_anchored_sorted {m : ℕ} (z : Fin (m + 1) → ℂ)
    (hz : ∀ i, Complex.normSq (z i) = 1) :
    ∃ e : Fin (m + 1) ≃ Fin (m + 1),
      let x := fun i ↦ anchoredRep (z 0) (z (e i))
      (∀ i, Complex.normSq (x i) = 1) ∧
      Monotone (fun i ↦ (x i).arg) ∧
      x 0 = 1 ∧
      (x (Fin.last m)).arg ≤ Real.pi := by
  let w : Fin (m + 1) → ℂ := fun i ↦ anchoredRep (z 0) (z i)
  obtain ⟨e, hmono⟩ := exists_arg_sorted_equiv w
  refine ⟨e, ?_⟩
  let x : Fin (m + 1) → ℂ := fun i ↦ w (e i)
  have hx : ∀ i, Complex.normSq (x i) = 1 := by
    intro i
    exact normSq_anchoredRep (hz 0) (hz (e i))
  have hargnonneg : ∀ i, 0 ≤ (x i).arg := by
    intro i
    exact (upperRep_arg_mem (conj (z 0) * z (e i))).1
  have hwzero : w 0 = 1 := anchoredRep_self (hz 0)
  let j : Fin (m + 1) := e.symm 0
  have hxj : x j = 1 := by simp [x, j, hwzero]
  have hargj : (x j).arg = 0 := by simp [hxj]
  have hargzero_le : (x 0).arg ≤ 0 := by
    have h := hmono (Fin.zero_le j)
    change (x 0).arg ≤ (x j).arg at h
    simpa [hargj] using h
  have hargzero : (x 0).arg = 0 := le_antisymm hargzero_le (hargnonneg 0)
  have hxzero : x 0 = 1 := by
    rw [unit_eq_exp_arg (hx 0), hargzero]
    simp
  refine ⟨hx, hmono, hxzero, ?_⟩
  exact (upperRep_arg_mem (conj (z 0) * z (e (Fin.last m)))).2

/-- Version of `exists_anchored_sorted` with an arbitrary chosen anchor. -/
lemma exists_anchored_sorted_at {m : ℕ} (z : Fin (m + 1) → ℂ)
    (hz : ∀ i, Complex.normSq (z i) = 1) (a : Fin (m + 1)) :
    ∃ e : Fin (m + 1) ≃ Fin (m + 1),
      let x := fun i ↦ anchoredRep (z a) (z (e i))
      (∀ i, Complex.normSq (x i) = 1) ∧
      Monotone (fun i ↦ (x i).arg) ∧
      x 0 = 1 ∧
      (x (Fin.last m)).arg ≤ Real.pi := by
  let w : Fin (m + 1) → ℂ := fun i ↦ anchoredRep (z a) (z i)
  obtain ⟨e, hmono⟩ := exists_arg_sorted_equiv w
  refine ⟨e, ?_⟩
  let x : Fin (m + 1) → ℂ := fun i ↦ w (e i)
  have hx : ∀ i, Complex.normSq (x i) = 1 := by
    intro i
    exact normSq_anchoredRep (hz a) (hz (e i))
  have hargnonneg : ∀ i, 0 ≤ (x i).arg := by
    intro i
    exact (upperRep_arg_mem (conj (z a) * z (e i))).1
  have hwanchor : w a = 1 := anchoredRep_self (hz a)
  let j : Fin (m + 1) := e.symm a
  have hxj : x j = 1 := by simp [x, j, hwanchor]
  have hargj : (x j).arg = 0 := by simp [hxj]
  have hargzero_le : (x 0).arg ≤ 0 := by
    have h := hmono (Fin.zero_le j)
    change (x 0).arg ≤ (x j).arg at h
    simpa [hargj] using h
  have hargzero : (x 0).arg = 0 := le_antisymm hargzero_le (hargnonneg 0)
  have hxzero : x 0 = 1 := by
    rw [unit_eq_exp_arg (hx 0), hargzero]
    simp
  refine ⟨hx, hmono, hxzero, ?_⟩
  exact (upperRep_arg_mem (conj (z a) * z (e (Fin.last m)))).2

lemma exists_anchored_sorted_nonempty {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1) (a : Fin N) :
    ∃ e : Fin N ≃ Fin N,
      let x := fun i ↦ anchoredRep (z a) (z (e i))
      (∀ i, Complex.normSq (x i) = 1) ∧
      Monotone (fun i ↦ (x i).arg) ∧
      x ⟨0, hN⟩ = 1 ∧
      ∀ i, (x i).arg ≤ Real.pi := by
  let w : Fin N → ℂ := fun i ↦ anchoredRep (z a) (z i)
  obtain ⟨e, hmono⟩ := exists_arg_sorted_equiv w
  refine ⟨e, ?_⟩
  let x : Fin N → ℂ := fun i ↦ w (e i)
  have hx : ∀ i, Complex.normSq (x i) = 1 := by
    intro i
    exact normSq_anchoredRep (hz a) (hz (e i))
  have hargnonneg : ∀ i, 0 ≤ (x i).arg := by
    intro i
    exact (upperRep_arg_mem (conj (z a) * z (e i))).1
  have hwanchor : w a = 1 := anchoredRep_self (hz a)
  let j : Fin N := e.symm a
  have hxj : x j = 1 := by simp [x, j, hwanchor]
  have hargj : (x j).arg = 0 := by simp [hxj]
  have hargzero_le : (x ⟨0, hN⟩).arg ≤ 0 := by
    have hzero : (⟨0, hN⟩ : Fin N) ≤ j := by
      change (0 : ℕ) ≤ j.val
      exact Nat.zero_le _
    have h := hmono hzero
    change (x ⟨0, hN⟩).arg ≤ (x j).arg at h
    simpa [hargj] using h
  have hargzero : (x ⟨0, hN⟩).arg = 0 :=
    le_antisymm hargzero_le (hargnonneg ⟨0, hN⟩)
  have hxzero : x ⟨0, hN⟩ = 1 := by
    rw [unit_eq_exp_arg (hx ⟨0, hN⟩), hargzero]
    simp
  refine ⟨hx, hmono, hxzero, ?_⟩
  intro i
  exact (upperRep_arg_mem (conj (z a) * z (e i))).2

lemma exists_centeredNear_sorted {N : ℕ} (z : Fin N → ℂ)
    (hz : ∀ i, Complex.normSq (z i) = 1) (a : ℂ)
    (ha : Complex.normSq a = 1) {ρ : ℝ} (hρ : ρ ^ 2 ≤ 2)
    (hclose : ∀ i, ProjectivelyCloseSq ρ a (z i)) :
    ∃ e : Fin N ≃ Fin N,
      let x := fun i ↦ centeredNearRep ρ a (z (e i))
      (∀ i, Complex.normSq (x i) = 1) ∧
      Monotone (fun i ↦ (x i).arg) ∧
      (∀ i, -(Real.pi / 2) ≤ (x i).arg) ∧
      (∀ i, (x i).arg ≤ Real.pi / 2) ∧
      ∀ i, Complex.normSq (x i - 1) ≤ ρ ^ 2 := by
  let w : Fin N → ℂ := fun i ↦ centeredNearRep ρ a (z i)
  obtain ⟨e, hmono⟩ := exists_arg_sorted_equiv w
  refine ⟨e, ?_⟩
  let x : Fin N → ℂ := fun i ↦ w (e i)
  have hx : ∀ i, Complex.normSq (x i) = 1 := by
    intro i
    exact centeredNearRep_unit ha (hz (e i))
  have hargs : ∀ i,
      -(Real.pi / 2) ≤ (x i).arg ∧ (x i).arg ≤ Real.pi / 2 := by
    intro i
    exact centeredNearRep_arg_mem ha (hz (e i)) hρ (hclose (e i))
  refine ⟨hx, hmono, fun i ↦ (hargs i).1, fun i ↦ (hargs i).2, ?_⟩
  intro i
  exact centeredNearRep_close_one ha (hclose (e i))

/-- Append the antipode of the first point to a finite sorted semicircle
chain, and keep that endpoint constant after the finite chain. -/
def closedChain {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ) (k : ℕ) : ℂ :=
  if hk : k < N then x ⟨k, hk⟩ else -x ⟨0, hN⟩

@[simp] lemma closedChain_of_lt {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ)
    {k : ℕ} (hk : k < N) : closedChain hN x k = x ⟨k, hk⟩ := by
  simp [closedChain, hk]

@[simp] lemma closedChain_of_ge {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ)
    {k : ℕ} (hk : N ≤ k) : closedChain hN x k = -x ⟨0, hN⟩ := by
  simp [closedChain, not_lt.mpr hk]

lemma closedChain_unit {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) :
    ∀ k, Complex.normSq (closedChain hN x k) = 1 := by
  intro k
  unfold closedChain
  split_ifs
  · exact hx _
  · simp [hx]

lemma closedChain_monotone {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ)
    (hx0 : x ⟨0, hN⟩ = 1)
    (hmono : Monotone fun i ↦ (x i).arg)
    (harg : ∀ i, (x i).arg ≤ Real.pi) :
    Monotone fun k ↦ (closedChain hN x k).arg := by
  intro a b hab
  change (if ha : a < N then x ⟨a, ha⟩ else -x ⟨0, hN⟩).arg ≤
    (if hb : b < N then x ⟨b, hb⟩ else -x ⟨0, hN⟩).arg
  split_ifs with ha hb
  · exact hmono (by simpa using hab)
  · rw [hx0]
    simpa using harg ⟨a, ha⟩
  · omega
  · rfl

lemma closedChain_arg_zero {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ)
    (hx0 : x ⟨0, hN⟩ = 1) : (closedChain hN x 0).arg = 0 := by
  simp [closedChain, hN, hx0]

lemma closedChain_arg_end {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ)
    (hx0 : x ⟨0, hN⟩ = 1) :
    (closedChain hN x N).arg = Real.pi := by
  simp [closedChain, hx0]

lemma closedChain_energy_of_far_positions {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (hmono : Monotone fun i ↦ (x i).arg)
    (hx0 : x ⟨0, hN⟩ = 1) (harg : ∀ i, (x i).arg ≤ Real.pi)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {j k : Fin N} (hjk : j ≤ k)
    (h0j : ProjectivelyFarSq ρ (x ⟨0, hN⟩) (x j))
    (hjkfar : ProjectivelyFarSq ρ (x j) (x k))
    (h0k : ProjectivelyFarSq ρ (x ⟨0, hN⟩) (x k)) :
    (∑ i ∈ Finset.range N,
      Complex.normSq (closedChain hN x i - closedChain hN x (i + 1))) ≤
      4 - ρ ^ 3 := by
  let y := closedChain hN x
  have hyunit := closedChain_unit hN x hx
  have hymono := closedChain_monotone hN x hx0 hmono harg
  have hy0 := closedChain_arg_zero hN x hx0
  have hyN := closedChain_arg_end hN x hx0
  apply chain_energy_le_of_three_gaps y hyunit hymono hjk (Nat.le_of_lt k.isLt)
    hy0 hyN hρ
  · change ρ ^ 2 < Complex.normSq (closedChain hN x 0 - closedChain hN x j)
    rw [closedChain_of_lt hN x hN, closedChain_of_lt hN x j.isLt]
    exact h0j.1
  · change ρ ^ 2 < Complex.normSq (closedChain hN x j - closedChain hN x k)
    rw [closedChain_of_lt hN x j.isLt, closedChain_of_lt hN x k.isLt]
    exact hjkfar.1
  · have hlast : ρ ^ 2 < Complex.normSq (x k + x ⟨0, hN⟩) := by
      simpa [add_comm] using h0k.2
    change ρ ^ 2 < Complex.normSq (closedChain hN x k - closedChain hN x N)
    rw [closedChain_of_lt hN x k.isLt, closedChain_of_ge hN x le_rfl]
    simpa using hlast

lemma normSq_sub_le_four_mul_sq {ρ : ℝ} (hρ : 0 ≤ ρ) {x y : ℂ}
    (hx : Complex.normSq (x - 1) ≤ ρ ^ 2)
    (hy : Complex.normSq (y - 1) ≤ ρ ^ 2) :
    Complex.normSq (x - y) ≤ 4 * ρ ^ 2 := by
  have hxnorm : ‖x - 1‖ ≤ ρ := by
    rw [Complex.normSq_eq_norm_sq] at hx
    nlinarith [norm_nonneg (x - 1)]
  have hynorm : ‖y - 1‖ ≤ ρ := by
    rw [Complex.normSq_eq_norm_sq] at hy
    nlinarith [norm_nonneg (y - 1)]
  have htri : ‖x - y‖ ≤ ‖x - 1‖ + ‖y - 1‖ := by
    have h := norm_sub_le (x - 1) (y - 1)
    simpa only [sub_sub_sub_cancel_right] using h
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (x - y)]

def endClampedChain {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ) (k : ℕ) : ℂ :=
  if hk : k < N then x ⟨k, hk⟩ else x ⟨N - 1, by omega⟩

lemma endClampedChain_unit {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) :
    ∀ k, Complex.normSq (endClampedChain hN x k) = 1 := by
  intro k
  unfold endClampedChain
  split_ifs <;> apply hx

lemma endClampedChain_monotone {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ)
    (hmono : Monotone fun i ↦ (x i).arg) :
    Monotone fun k ↦ (endClampedChain hN x k).arg := by
  intro a b hab
  change (if ha : a < N then x ⟨a, ha⟩ else x ⟨N - 1, by omega⟩).arg ≤
    (if hb : b < N then x ⟨b, hb⟩ else x ⟨N - 1, by omega⟩).arg
  split_ifs with ha hb
  · exact hmono (by simpa using hab)
  · apply hmono
    change a ≤ N - 1
    omega
  · omega
  · exact le_rfl

lemma sum_range_two_mul_sub_one {m : ℕ} (hm : 0 < m) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range (2 * m - 1), f i) =
      (∑ i ∈ Finset.range m, f (2 * i)) +
        ∑ i ∈ Finset.range (m - 1), f (2 * i + 1) := by
  have hfull := sum_range_even_odd (m := m) f
  have hlast : (∑ i ∈ Finset.range (2 * m), f i) =
      (∑ i ∈ Finset.range (2 * m - 1), f i) + f (2 * m - 1) := by
    have heq : 2 * m = (2 * m - 1) + 1 := by omega
    conv_lhs => rw [heq, Finset.sum_range_succ]
  have hodd : (∑ i ∈ Finset.range m, f (2 * i + 1)) =
      (∑ i ∈ Finset.range (m - 1), f (2 * i + 1)) + f (2 * m - 1) := by
    have heq : m = (m - 1) + 1 := by omega
    conv_lhs => rw [heq, Finset.sum_range_succ]
    congr 2 <;> omega
  linarith

/-- Index permutation which lists even positions first and odd positions
second. -/
def sumPairEquivProdFinTwo (m : ℕ) : Fin m ⊕ Fin m ≃ Fin m × Fin 2 where
  toFun s := Sum.elim (fun i ↦ (i, 0)) (fun i ↦ (i, 1)) s
  invFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  left_inv s := by rcases s with i | i <;> simp
  right_inv p := by rcases p with ⟨i, j⟩; fin_cases j <;> simp

def interleaveEquiv (m : ℕ) : Fin (m + m) ≃ Fin (2 * m) :=
  finSumFinEquiv.symm |>.trans (sumPairEquivProdFinTwo m) |>.trans
    finProdFinEquiv |>.trans (finCongr (Nat.mul_comm m 2))

@[simp] lemma interleaveEquiv_castAdd (m : ℕ) (i : Fin m) :
    (interleaveEquiv m (Fin.castAdd m i)).val = 2 * i.val := by
  simp [interleaveEquiv, sumPairEquivProdFinTwo, finProdFinEquiv]

@[simp] lemma interleaveEquiv_natAdd (m : ℕ) (i : Fin m) :
    (interleaveEquiv m (Fin.natAdd m i)).val = 2 * i.val + 1 := by
  simp only [interleaveEquiv, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
  simp [sumPairEquivProdFinTwo, finProdFinEquiv]
  omega

def evenPart {m : ℕ} (x : Fin (2 * m) → ℂ) (i : Fin m) : ℂ :=
  x ⟨2 * i.val, by omega⟩

def oddPart {m : ℕ} (x : Fin (2 * m) → ℂ) (i : Fin m) : ℂ :=
  x ⟨2 * i.val + 1, by omega⟩

lemma evenPart_energy_le_endpoint {m : ℕ} (hm : 0 < m)
    (x : Fin (2 * m) → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (hmono : Monotone fun i ↦ (x i).arg)
    (hspan : (x ⟨2 * m - 1, by omega⟩).arg -
      (x ⟨0, by omega⟩).arg ≤ Real.pi) :
    (∑ i, Complex.normSq (evenPart x i - oddPart x i)) ≤
      Complex.normSq (x ⟨0, by omega⟩ - x ⟨2 * m - 1, by omega⟩) := by
  let hN : 0 < 2 * m := by omega
  let y : ℕ → ℂ := endClampedChain hN x
  let f : ℕ → ℝ := fun i ↦ Complex.normSq (y i - y (i + 1))
  have hchain := chain_range_le_chord y (endClampedChain_unit hN x hx)
    (endClampedChain_monotone hN x hmono) (a := 0) (d := 2 * m - 1) (by
      simpa [y, endClampedChain, hN] using hspan)
  have heven : (∑ i, Complex.normSq (evenPart x i - oddPart x i)) =
      ∑ i ∈ Finset.range m, f (2 * i) := by
    calc
      (∑ i : Fin m, Complex.normSq (evenPart x i - oddPart x i)) =
          ∑ i : Fin m, f (2 * i.val) := by
        apply Finset.sum_congr rfl
        intro i hi
        unfold evenPart oddPart f y
        have hevenlt : 2 * i.val < 2 * m := by omega
        have hoddlt : 2 * i.val + 1 < 2 * m := by omega
        rw [show endClampedChain hN x (2 * i.val) =
            x ⟨2 * i.val, by omega⟩ by simp [endClampedChain, hevenlt]]
        rw [show endClampedChain hN x (2 * i.val + 1) =
            x ⟨2 * i.val + 1, by omega⟩ by simp [endClampedChain, hoddlt]]
      _ = _ := Fin.sum_univ_eq_sum_range (fun i ↦ f (2 * i)) m
  have hsplit := sum_range_two_mul_sub_one hm f
  have hgaps : 0 ≤ ∑ i ∈ Finset.range (m - 1), f (2 * i + 1) := by
    apply Finset.sum_nonneg
    intro i hi
    exact Complex.normSq_nonneg _
  rw [heven]
  have hzero : y 0 = x ⟨0, by omega⟩ := by simp [y, endClampedChain, hN]
  have hlast : y (2 * m - 1) = x ⟨2 * m - 1, by omega⟩ := by
    simp [y, endClampedChain, hN]
  simp only [zero_add] at hchain
  rw [hzero, hlast] at hchain
  linarith

lemma append_evenPart_oddPart {m : ℕ} (x : Fin (2 * m) → ℂ) :
    Fin.append (evenPart x) (oddPart x) = fun i ↦ x (interleaveEquiv m i) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Fin.append_left, evenPart]
    congr 1
    apply Fin.ext
    simp
  · intro j
    simp only [Fin.append_right, oddPart]
    apply congrArg x
    apply Fin.ext
    exact (interleaveEquiv_natAdd m j).symm

lemma card_pair_evenOdd_eq {m : ℕ} (x : Fin (2 * m) → ℂ) (R : ℝ) :
    ((Finset.univ.filter fun q : SignPair m ↦
      Complex.normSq (pairSignedSum (evenPart x) (oddPart x) q) < R).card) =
    ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
      Complex.normSq (signedSum x ε) < R).card) := by
  rw [← card_smallBall_append_pair]
  rw [append_evenPart_oddPart]
  exact card_smallBall_reindex_general x (interleaveEquiv m) R

lemma exists_pairing_of_projective_cluster {m : ℕ} (hm : 0 < m)
    (z : Fin (2 * m) → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1)
    (a : ℂ) (ha : Complex.normSq a = 1) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρsq : ρ ^ 2 ≤ 2)
    (hclose : ∀ i, ProjectivelyCloseSq ρ a (z i)) :
    ∃ u v : Fin m → ℂ,
      (∀ i, Complex.normSq (u i) = 1) ∧
      (∀ i, Complex.normSq (v i) = 1) ∧
      (∑ i, Complex.normSq (u i - v i)) ≤ 4 * ρ ^ 2 ∧
      ∀ R : ℝ,
        ((Finset.univ.filter fun q : SignPair m ↦
          Complex.normSq (pairSignedSum u v q) < R).card) =
        ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
          Complex.normSq (signedSum z ε) < R).card) := by
  obtain ⟨e, hx, hmono, harglow, harghigh, hdist⟩ :=
    exists_centeredNear_sorted z hz a ha hρsq hclose
  let x : Fin (2 * m) → ℂ := fun i ↦ centeredNearRep ρ a (z (e i))
  have hspan : (x ⟨2 * m - 1, by omega⟩).arg -
      (x ⟨0, by omega⟩).arg ≤ Real.pi := by
    have hlo := harglow ⟨0, by omega⟩
    have hhi := harghigh ⟨2 * m - 1, by omega⟩
    linarith
  have hpair := evenPart_energy_le_endpoint hm x hx hmono hspan
  have hend : Complex.normSq
      (x ⟨0, by omega⟩ - x ⟨2 * m - 1, by omega⟩) ≤ 4 * ρ ^ 2 :=
    normSq_sub_le_four_mul_sq hρ (hdist ⟨0, by omega⟩)
      (hdist ⟨2 * m - 1, by omega⟩)
  refine ⟨evenPart x, oddPart x, ?_, ?_, hpair.trans hend, ?_⟩
  · intro i
    exact hx _
  · intro i
    exact hx _
  · intro R
    rw [card_pair_evenOdd_eq x R]
    exact card_smallBall_centeredNear_reindex ρ z a ha e R

/-- If every pair of projective directions is close at squared chord radius
`1/3`, the even sequence has a distribution-preserving pairing of energy at
most `1/3`. -/
lemma exists_pairing_of_pairwise_close_one_third {m : ℕ} (hm : 0 < m)
    (z : Fin (2 * m) → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1)
    (a : Fin (2 * m)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρsq : ρ ^ 2 = (1 : ℝ) / 3)
    (hpairwise : ∀ i j, ProjectivelyCloseSq ρ (z i) (z j)) :
    ∃ u v : Fin m → ℂ,
      (∀ i, Complex.normSq (u i) = 1) ∧
      (∀ i, Complex.normSq (v i) = 1) ∧
      (∑ i, Complex.normSq (u i - v i)) ≤ (1 : ℝ) / 3 ∧
      ∀ R : ℝ,
        ((Finset.univ.filter fun q : SignPair m ↦
          Complex.normSq (pairSignedSum u v q) < R).card) =
        ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
          Complex.normSq (signedSum z ε) < R).card) := by
  have hρtwo : ρ ^ 2 ≤ 2 := by rw [hρsq]; norm_num
  obtain ⟨e, hx, hmono, harglow, harghigh, hdist⟩ :=
    exists_centeredNear_sorted z hz (z a) (hz a) hρtwo (fun i ↦ hpairwise a i)
  let x : Fin (2 * m) → ℂ := fun i ↦ centeredNearRep ρ (z a) (z (e i))
  have hspan : (x ⟨2 * m - 1, by omega⟩).arg -
      (x ⟨0, by omega⟩).arg ≤ Real.pi := by
    have hlo := harglow ⟨0, by omega⟩
    have hhi := harghigh ⟨2 * m - 1, by omega⟩
    linarith
  have hchain := evenPart_energy_le_endpoint hm x hx hmono hspan
  have hend : Complex.normSq
      (x ⟨0, by omega⟩ - x ⟨2 * m - 1, by omega⟩) ≤ (1 : ℝ) / 3 := by
    apply direct_close_of_close_one_third hρsq (hx _) (hx _)
    · simpa [hρsq] using hdist ⟨0, by omega⟩
    · simpa [hρsq] using hdist ⟨2 * m - 1, by omega⟩
    · exact projectivelyCloseSq_centeredNearRep (hz a)
        (hpairwise (e ⟨0, by omega⟩) (e ⟨2 * m - 1, by omega⟩))
  refine ⟨evenPart x, oddPart x, ?_, ?_, hchain.trans hend, ?_⟩
  · intro i
    exact hx _
  · intro i
    exact hx _
  · intro R
    rw [card_pair_evenOdd_eq x R]
    exact card_smallBall_centeredNear_reindex ρ z (z a) (hz a) e R

/-- A cluster pairing expressed back in the original plane.  The flattened
paired sequence is literally a signed permutation of the input sequence. -/
lemma exists_world_pairing_of_projective_cluster {m : ℕ} (hm : 0 < m)
    (z : Fin (2 * m) → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1)
    (a : ℂ) (ha : Complex.normSq a = 1) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρsq : ρ ^ 2 ≤ 2)
    (hclose : ∀ i, ProjectivelyCloseSq ρ a (z i)) :
    ∃ u v : Fin m → ℂ, ∃ e : Fin (m + m) ≃ Fin (2 * m), ∃ t : SignVec (m + m),
      (∀ i, Complex.normSq (u i) = 1) ∧
      (∀ i, Complex.normSq (v i) = 1) ∧
      (∑ i, Complex.normSq (u i - v i)) ≤ 4 * ρ ^ 2 ∧
      Fin.append u v = fun i ↦ (sign (t i) : ℂ) * z (e i) := by
  obtain ⟨s, hx, hmono, harglow, harghigh, hdist⟩ :=
    exists_centeredNear_sorted z hz a ha hρsq hclose
  let x : Fin (2 * m) → ℂ := fun i ↦ centeredNearRep ρ a (z (s i))
  let u : Fin m → ℂ := fun i ↦ a * evenPart x i
  let v : Fin m → ℂ := fun i ↦ a * oddPart x i
  let e : Fin (m + m) ≃ Fin (2 * m) := (interleaveEquiv m).trans s
  let t : SignVec (m + m) :=
    fun i ↦ nearChoice ρ (conj a * z (e i))
  have hspan : (x ⟨2 * m - 1, by omega⟩).arg -
      (x ⟨0, by omega⟩).arg ≤ Real.pi := by
    have hlo := harglow ⟨0, by omega⟩
    have hhi := harghigh ⟨2 * m - 1, by omega⟩
    linarith
  have hpair := evenPart_energy_le_endpoint hm x hx hmono hspan
  have hend : Complex.normSq
      (x ⟨0, by omega⟩ - x ⟨2 * m - 1, by omega⟩) ≤ 4 * ρ ^ 2 :=
    normSq_sub_le_four_mul_sq hρ (hdist ⟨0, by omega⟩)
      (hdist ⟨2 * m - 1, by omega⟩)
  have henergyLocal :
      (∑ i, Complex.normSq (evenPart x i - oddPart x i)) ≤ 4 * ρ ^ 2 :=
    hpair.trans hend
  have henergyWorld : (∑ i, Complex.normSq (u i - v i)) ≤ 4 * ρ ^ 2 := by
    calc
      (∑ i, Complex.normSq (u i - v i)) =
          ∑ i, Complex.normSq (evenPart x i - oddPart x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [u, v, ← mul_sub, Complex.normSq_mul, ha, one_mul]
      _ ≤ _ := henergyLocal
  refine ⟨u, v, e, t, ?_, ?_, henergyWorld, ?_⟩
  · intro i
    change Complex.normSq (a * evenPart x i) = 1
    rw [Complex.normSq_mul, ha, one_mul]
    exact hx _
  · intro i
    change Complex.normSq (a * oddPart x i) = 1
    rw [Complex.normSq_mul, ha, one_mul]
    exact hx _
  · have happ : Fin.append u v =
        fun i ↦ a * Fin.append (evenPart x) (oddPart x) i := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [Fin.append_left]
        change u j = a * evenPart x j
        rfl
      · intro j
        simp only [Fin.append_right]
        change v j = a * oddPart x j
        rfl
    rw [happ]
    funext i
    have hinter := congrFun (append_evenPart_oddPart x) i
    rw [hinter]
    simpa [x, e, t, towardRep] using
      (towardRep_eq_choice_mul (ρ := ρ) (a := a)
        (z := z (s (interleaveEquiv m i))) ha)

noncomputable def finsetIndexEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) : Fin s.card ≃ {x : α // x ∈ s} :=
  (finCongr (by simp)).trans (Fintype.equivFin {x : α // x ∈ s}).symm

noncomputable def finsetComplementIndexEquiv {α : Type*} [Fintype α]
    [DecidableEq α] (s : Finset α) :
    Fin (Finset.univ \ s).card ≃ {x : α // x ∉ s} :=
  (finCongr (by rw [Finset.card_sdiff]; simp)).trans
    (Fintype.equivFin {x : α // x ∉ s}).symm

def partitionSubtypeEquiv {α : Type*} [DecidableEq α] (s : Finset α) :
    {x : α // x ∈ s} ⊕ {x : α // x ∉ s} ≃ α where
  toFun q := Sum.elim Subtype.val Subtype.val q
  invFun x := if hx : x ∈ s then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, hx⟩
  left_inv q := by rcases q with x | x <;> simp [x.2]
  right_inv x := by simp only; split_ifs <;> rfl

noncomputable def partitionIndexEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) : Fin (s.card + (Finset.univ \ s).card) ≃ α :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr (finsetIndexEquiv s) (finsetComplementIndexEquiv s)) |>.trans
      (partitionSubtypeEquiv s)

noncomputable def indexedSubseq {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} (z : α → β) (s : Finset α) : Fin s.card → β :=
  fun i ↦ z (finsetIndexEquiv s i)

noncomputable def indexedComplement {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} (z : α → β) (s : Finset α) :
    Fin (Finset.univ \ s).card → β :=
  fun i ↦ z (finsetComplementIndexEquiv s i)

lemma append_indexed_partition {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} (z : α → β) (s : Finset α) :
    Fin.append (indexedSubseq z s) (indexedComplement z s) =
      fun i ↦ z (partitionIndexEquiv s i) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [indexedSubseq, partitionIndexEquiv, partitionSubtypeEquiv]
  · intro j
    simp [indexedComplement, partitionIndexEquiv, partitionSubtypeEquiv]

/-- Exchange the middle two blocks in a four-block finite index set. -/
def fourBlockSwapEquiv (A B C D : Type*) :
    (A ⊕ B) ⊕ (C ⊕ D) ≃ (A ⊕ C) ⊕ (B ⊕ D) where
  toFun q := match q with
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inl c) => Sum.inl (Sum.inr c)
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  invFun q := match q with
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr c) => Sum.inr (Sum.inl c)
    | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  left_inv q := by rcases q with (a | b) | (c | d) <;> rfl
  right_inv q := by rcases q with (a | c) | (b | d) <;> rfl

/-- Send the blocks `(u₁,u₂,v₁,v₂)` to `(u₁,v₁,u₂,v₂)`. -/
def pairBlockShuffle (k l : ℕ) :
    Fin ((k + l) + (k + l)) ≃ Fin ((k + k) + (l + l)) :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm) |>.trans
      (fourBlockSwapEquiv (Fin k) (Fin l) (Fin k) (Fin l)) |>.trans
        (Equiv.sumCongr finSumFinEquiv finSumFinEquiv) |>.trans
          finSumFinEquiv

lemma pairBlockShuffle_right_left {k l : ℕ} (c : Fin k) :
    pairBlockShuffle k l (Fin.natAdd (k + l) (Fin.castAdd l c)) =
      Fin.castAdd (l + l) (c.addNat k) := by
  unfold pairBlockShuffle
  simp only [Equiv.trans_apply]
  simp [fourBlockSwapEquiv]
  have hinput : (Fin.castAdd l c).addNat (k + l) =
      Fin.natAdd (k + l) (Fin.castAdd l c) := by
    apply Fin.ext
    simp [Fin.addNat, Fin.natAdd]
    omega
  rw [hinput]
  simp only [finSumFinEquiv_symm_apply_natAdd]
  simp only [Sum.map_inr, finSumFinEquiv_symm_apply_castAdd,
    fourBlockSwapEquiv, Sum.map_inl, finSumFinEquiv_apply_right,
    finSumFinEquiv_apply_left]
  congr 1
  apply Fin.ext
  simp [Fin.addNat, Fin.natAdd]
  omega

lemma pairBlockShuffle_right_right {k l : ℕ} (d : Fin l) :
    pairBlockShuffle k l (Fin.natAdd (k + l) (Fin.natAdd k d)) =
      Fin.natAdd (k + k) (d.addNat l) := by
  unfold pairBlockShuffle
  simp only [Equiv.trans_apply]
  simp [fourBlockSwapEquiv]
  have hinput : (Fin.natAdd k d).addNat (k + l) =
      Fin.natAdd (k + l) (Fin.natAdd k d) := by
    apply Fin.ext
    simp [Fin.addNat, Fin.natAdd]
    omega
  rw [hinput]
  simp only [finSumFinEquiv_symm_apply_natAdd]
  simp only [Sum.map_inr, finSumFinEquiv_symm_apply_natAdd,
    fourBlockSwapEquiv, finSumFinEquiv_apply_right]
  congr 1
  apply Fin.ext
  simp [Fin.addNat, Fin.natAdd]
  omega

lemma append_pairs_shuffle {A : Type*} {k l : ℕ}
    (u₁ v₁ : Fin k → A) (u₂ v₂ : Fin l → A) :
    Fin.append (Fin.append u₁ u₂) (Fin.append v₁ v₂) =
      fun i ↦ Fin.append (Fin.append u₁ v₁) (Fin.append u₂ v₂)
        (pairBlockShuffle k l i) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro q
    refine Fin.addCases ?_ ?_ q
    · intro a
      simp [pairBlockShuffle, fourBlockSwapEquiv]
    · intro b
      simp [pairBlockShuffle, fourBlockSwapEquiv]
  · intro q
    refine Fin.addCases ?_ ?_ q
    · intro c
      simp only [Fin.append_right, Fin.append_left]
      rw [pairBlockShuffle_right_left]
      have hc : c.addNat k = Fin.natAdd k c := by
        apply Fin.ext
        simp [Fin.addNat, Fin.natAdd]
        omega
      rw [Fin.append_left, hc]
      simp only [Fin.append_right]
    · intro d
      simp only [Fin.append_right]
      rw [pairBlockShuffle_right_right]
      have hd : d.addNat l = Fin.natAdd l d := by
        apply Fin.ext
        simp [Fin.addNat, Fin.natAdd]
        omega
      rw [hd]
      simp only [Fin.append_right]

/-- Two flattened world pairings concatenate to a world pairing after the
middle two blocks are shuffled. -/
lemma combine_world_pairings {k l : ℕ}
    (z₁ : Fin (2 * k) → ℂ) (z₂ : Fin (2 * l) → ℂ)
    (u₁ v₁ : Fin k → ℂ) (u₂ v₂ : Fin l → ℂ)
    (e₁ : Fin (k + k) ≃ Fin (2 * k)) (e₂ : Fin (l + l) ≃ Fin (2 * l))
    (t₁ : SignVec (k + k)) (t₂ : SignVec (l + l))
    (h₁ : Fin.append u₁ v₁ =
      fun i ↦ (sign (t₁ i) : ℂ) * z₁ (e₁ i))
    (h₂ : Fin.append u₂ v₂ =
      fun i ↦ (sign (t₂ i) : ℂ) * z₂ (e₂ i)) :
    ∃ e : Fin ((k + l) + (k + l)) ≃ Fin ((2 * k) + (2 * l)),
      ∃ t : SignVec ((k + l) + (k + l)),
        Fin.append (Fin.append u₁ u₂) (Fin.append v₁ v₂) =
          fun i ↦ (sign (t i) : ℂ) * Fin.append z₁ z₂ (e i) := by
  let merge : Fin ((k + k) + (l + l)) ≃ Fin ((2 * k) + (2 * l)) :=
    finSumFinEquiv.symm |>.trans
      (Equiv.sumCongr e₁ e₂) |>.trans finSumFinEquiv
  let e := (pairBlockShuffle k l).trans merge
  let t : SignVec ((k + l) + (k + l)) := fun i ↦
    match finSumFinEquiv.symm (pairBlockShuffle k l i) with
    | Sum.inl j => t₁ j
    | Sum.inr j => t₂ j
  refine ⟨e, t, ?_⟩
  rw [append_pairs_shuffle, h₁, h₂]
  funext i
  let p := pairBlockShuffle k l i
  generalize hq : finSumFinEquiv.symm p = q
  rcases q with j | j
  · have hp := congrArg finSumFinEquiv hq
    simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left] at hp
    simp [p, hp, e, merge, t, hq]
  · have hp := congrArg finSumFinEquiv hq
    simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right] at hp
    simp [p, hp, e, merge, t, hq]

/-- Pair two nonempty projective clusters.  The energy bounds add, while the
flattened signed-sum distribution is preserved exactly. -/
lemma exists_pairing_of_two_projective_clusters {k l : ℕ}
    (hk : 0 < k) (hl : 0 < l)
    (z₁ : Fin (2 * k) → ℂ) (z₂ : Fin (2 * l) → ℂ)
    (hz₁ : ∀ i, Complex.normSq (z₁ i) = 1)
    (hz₂ : ∀ i, Complex.normSq (z₂ i) = 1)
    (a b : ℂ) (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρsq : ρ ^ 2 ≤ 2)
    (hclose₁ : ∀ i, ProjectivelyCloseSq ρ a (z₁ i))
    (hclose₂ : ∀ i, ProjectivelyCloseSq ρ b (z₂ i)) :
    ∃ u v : Fin (k + l) → ℂ,
      (∀ i, Complex.normSq (u i) = 1) ∧
      (∀ i, Complex.normSq (v i) = 1) ∧
      (∑ i, Complex.normSq (u i - v i)) ≤ 8 * ρ ^ 2 ∧
      ∀ R : ℝ,
        ((Finset.univ.filter fun q : SignPair (k + l) ↦
          Complex.normSq (pairSignedSum u v q) < R).card) =
        ((Finset.univ.filter fun ε : SignVec ((2 * k) + (2 * l)) ↦
          Complex.normSq (signedSum (Fin.append z₁ z₂) ε) < R).card) := by
  obtain ⟨u₁, v₁, e₁, t₁, hu₁, hv₁, hE₁, hflat₁⟩ :=
    exists_world_pairing_of_projective_cluster hk z₁ hz₁ a ha hρ hρsq hclose₁
  obtain ⟨u₂, v₂, e₂, t₂, hu₂, hv₂, hE₂, hflat₂⟩ :=
    exists_world_pairing_of_projective_cluster hl z₂ hz₂ b hb hρ hρsq hclose₂
  obtain ⟨e, t, hflat⟩ := combine_world_pairings z₁ z₂ u₁ v₁ u₂ v₂
    e₁ e₂ t₁ t₂ hflat₁ hflat₂
  let u := Fin.append u₁ u₂
  let v := Fin.append v₁ v₂
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [u] using hu₁ j
    · intro j
      simpa [u] using hu₂ j
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [v] using hv₁ j
    · intro j
      simpa [v] using hv₂ j
  · calc
      (∑ i, Complex.normSq (u i - v i)) =
          (∑ i, Complex.normSq (u₁ i - v₁ i)) +
            ∑ i, Complex.normSq (u₂ i - v₂ i) := by
        simp [u, v, Fin.sum_univ_add]
      _ ≤ 4 * ρ ^ 2 + 4 * ρ ^ 2 := add_le_add hE₁ hE₂
      _ = 8 * ρ ^ 2 := by ring
  · intro R
    rw [← card_smallBall_append_pair]
    rw [show Fin.append u v =
        fun i ↦ (sign (t i) : ℂ) * Fin.append z₁ z₂ (e i) by
      simpa [u, v] using hflat]
    exact card_smallBall_oriented_reindex_general (Fin.append z₁ z₂) e t R

/-- The preceding two-cluster statement, allowing one cluster to be empty. -/
lemma exists_pairing_of_two_projective_clusters' {k l : ℕ}
    (hkl : 0 < k + l)
    (z₁ : Fin (2 * k) → ℂ) (z₂ : Fin (2 * l) → ℂ)
    (hz₁ : ∀ i, Complex.normSq (z₁ i) = 1)
    (hz₂ : ∀ i, Complex.normSq (z₂ i) = 1)
    (a b : ℂ) (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρsq : ρ ^ 2 ≤ 2)
    (hclose₁ : ∀ i, ProjectivelyCloseSq ρ a (z₁ i))
    (hclose₂ : ∀ i, ProjectivelyCloseSq ρ b (z₂ i)) :
    ∃ u v : Fin (k + l) → ℂ,
      (∀ i, Complex.normSq (u i) = 1) ∧
      (∀ i, Complex.normSq (v i) = 1) ∧
      (∑ i, Complex.normSq (u i - v i)) ≤ 8 * ρ ^ 2 ∧
      ∀ R : ℝ,
        ((Finset.univ.filter fun q : SignPair (k + l) ↦
          Complex.normSq (pairSignedSum u v q) < R).card) =
        ((Finset.univ.filter fun ε : SignVec ((2 * k) + (2 * l)) ↦
          Complex.normSq (signedSum (Fin.append z₁ z₂) ε) < R).card) := by
  by_cases hk : k = 0
  · subst k
    have hl : 0 < l := by simpa using hkl
    obtain ⟨u, v, hu, hv, hE, hcard⟩ :=
      exists_pairing_of_projective_cluster hl z₂ hz₂ b hb hρ hρsq hclose₂
    let e : Fin (0 + l) ≃ Fin l := finCongr (by omega)
    let eZ : Fin (2 * l) ≃ Fin ((2 * 0) + (2 * l)) := finCongr (by omega)
    let u' : Fin (0 + l) → ℂ := fun i ↦ u (e i)
    let v' : Fin (0 + l) → ℂ := fun i ↦ v (e i)
    have hE' : (∑ i, Complex.normSq (u' i - v' i)) =
        ∑ j, Complex.normSq (u j - v j) := by
      simpa [u', v'] using e.sum_comp
        (fun j ↦ Complex.normSq (u j - v j))
    have happ : (fun i ↦ Fin.append z₁ z₂ (eZ i)) = z₂ := by
      funext i
      simp [eZ, Fin.append_left_nil]
    refine ⟨u', v', fun i ↦ hu _, fun i ↦ hv _, ?_, ?_⟩
    · rw [hE']
      exact hE.trans (by nlinarith [sq_nonneg ρ])
    · intro R
      calc
        ((Finset.univ.filter fun q : SignPair (0 + l) ↦
          Complex.normSq (pairSignedSum u' v' q) < R).card) =
            ((Finset.univ.filter fun q : SignPair l ↦
              Complex.normSq (pairSignedSum u v q) < R).card) := by
                exact card_pairSignedSum_reindex_general u v e R
        _ = ((Finset.univ.filter fun ε : SignVec (2 * l) ↦
              Complex.normSq (signedSum z₂ ε) < R).card) := hcard R
        _ = ((Finset.univ.filter fun ε : SignVec ((2 * 0) + (2 * l)) ↦
              Complex.normSq (signedSum (Fin.append z₁ z₂) ε) < R).card) := by
                simpa only [happ] using
                  card_smallBall_reindex_general (Fin.append z₁ z₂) eZ R
  · by_cases hl : l = 0
    · subst l
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      obtain ⟨u, v, hu, hv, hE, hcard⟩ :=
        exists_pairing_of_projective_cluster hkpos z₁ hz₁ a ha hρ hρsq hclose₁
      have hresult : ∃ u v : Fin k → ℂ,
          (∀ i, Complex.normSq (u i) = 1) ∧
          (∀ i, Complex.normSq (v i) = 1) ∧
          (∑ i, Complex.normSq (u i - v i)) ≤ 8 * ρ ^ 2 ∧
          ∀ R : ℝ,
            ((Finset.univ.filter fun q : SignPair k ↦
              Complex.normSq (pairSignedSum u v q) < R).card) =
            ((Finset.univ.filter fun ε : SignVec (2 * k) ↦
              Complex.normSq (signedSum z₁ ε) < R).card) :=
        ⟨u, v, hu, hv, hE.trans (by nlinarith [sq_nonneg ρ]), hcard⟩
      simpa [Fin.append_right_nil] using hresult
    · exact exists_pairing_of_two_projective_clusters
        (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hl) z₁ z₂ hz₁ hz₂
        a b ha hb hρ hρsq hclose₁ hclose₂

/-- Apply the two-cluster pairing to a finite partition of an original even
sequence. -/
lemma exists_pairing_of_even_partition {m k l : ℕ}
    (hk : 0 < k) (hl : 0 < l)
    (z : Fin (2 * m) → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1)
    (s : Finset (Fin (2 * m)))
    (hs : s.card = 2 * k) (ht : (Finset.univ \ s).card = 2 * l)
    (a b : ℂ) (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρsq : ρ ^ 2 ≤ 2)
    (hclose₁ : ∀ i, i ∈ s → ProjectivelyCloseSq ρ a (z i))
    (hclose₂ : ∀ i, i ∉ s → ProjectivelyCloseSq ρ b (z i)) :
    ∃ u v : Fin (k + l) → ℂ,
      (∀ i, Complex.normSq (u i) = 1) ∧
      (∀ i, Complex.normSq (v i) = 1) ∧
      (∑ i, Complex.normSq (u i - v i)) ≤ 8 * ρ ^ 2 ∧
      ∀ R : ℝ,
        ((Finset.univ.filter fun q : SignPair (k + l) ↦
          Complex.normSq (pairSignedSum u v q) < R).card) =
        ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
          Complex.normSq (signedSum z ε) < R).card) := by
  let c₁ : Fin (2 * k) ≃ Fin s.card := finCongr hs.symm
  let c₂ : Fin (2 * l) ≃ Fin (Finset.univ \ s).card := finCongr ht.symm
  let z₁ : Fin (2 * k) → ℂ := fun i ↦ indexedSubseq z s (c₁ i)
  let z₂ : Fin (2 * l) → ℂ := fun i ↦ indexedComplement z s (c₂ i)
  have hz₁ : ∀ i, Complex.normSq (z₁ i) = 1 := fun i ↦ hz _
  have hz₂ : ∀ i, Complex.normSq (z₂ i) = 1 := fun i ↦ hz _
  have hc₁ : ∀ i, ProjectivelyCloseSq ρ a (z₁ i) := by
    intro i
    exact hclose₁ _ (finsetIndexEquiv s (c₁ i)).property
  have hc₂ : ∀ i, ProjectivelyCloseSq ρ b (z₂ i) := by
    intro i
    exact hclose₂ _ (finsetComplementIndexEquiv s (c₂ i)).property
  obtain ⟨u, v, hu, hv, hE, hcard⟩ :=
    exists_pairing_of_two_projective_clusters hk hl z₁ z₂ hz₁ hz₂
      a b ha hb hρ hρsq hc₁ hc₂
  let epart : Fin ((2 * k) + (2 * l)) ≃ Fin (2 * m) :=
    finSumFinEquiv.symm |>.trans (Equiv.sumCongr c₁ c₂) |>.trans
      finSumFinEquiv |>.trans (partitionIndexEquiv s)
  have happ : Fin.append z₁ z₂ = fun i ↦ z (epart i) := by
    rw [show Fin.append z₁ z₂ =
        Fin.append (fun i ↦ indexedSubseq z s (c₁ i))
          (fun i ↦ indexedComplement z s (c₂ i)) by rfl]
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [epart, c₁, c₂, partitionIndexEquiv, partitionSubtypeEquiv,
        indexedSubseq]
    · intro j
      simp [epart, c₁, c₂, partitionIndexEquiv, partitionSubtypeEquiv,
        indexedComplement]
  refine ⟨u, v, hu, hv, hE, ?_⟩
  intro R
  rw [hcard R, happ]
  exact card_smallBall_reindex_general z epart R

/-- Remove one member from each odd cluster, pair the even residual clusters,
and then restore the two removed vectors using `four_center_cover_small`. -/
lemma exists_pairing_of_odd_partition_with_extension {m k l : ℕ}
    (hkl : 0 < k + l)
    (z : Fin (2 * m) → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1)
    (s : Finset (Fin (2 * m)))
    (hs : s.card = 2 * k + 1)
    (ht : (Finset.univ \ s).card = 2 * l + 1)
    (ia ib : Fin (2 * m)) (hia : ia ∈ s) (hib : ib ∉ s)
    (a b : ℂ) (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρsq : ρ ^ 2 ≤ 2)
    (hclose₁ : ∀ i, i ∈ s → ProjectivelyCloseSq ρ a (z i))
    (hclose₂ : ∀ i, i ∉ s → ProjectivelyCloseSq ρ b (z i)) :
    ∃ u v : Fin (k + l) → ℂ,
      (∀ i, Complex.normSq (u i) = 1) ∧
      (∀ i, Complex.normSq (v i) = 1) ∧
      (∑ i, Complex.normSq (u i - v i)) ≤ 8 * ρ ^ 2 ∧
      ((Finset.univ.filter fun q : SignPair (k + l) ↦
        Complex.normSq (pairSignedSum u v q) < (1 : ℝ) / 4).card) ≤
      ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
        Complex.normSq (signedSum z ε) ≤ 2).card) := by
  let t := Finset.univ \ s
  let A := s.erase ia
  let B := t.erase ib
  let R := A ∪ B
  let L : Finset (Fin (2 * m)) := {ia, ib}
  have hibT : ib ∈ t := by simp [t, hib]
  have hiab : ia ≠ ib := by
    intro h
    subst ib
    exact hib hia
  have hAcard : A.card = 2 * k := by
    rw [show A.card = s.card - 1 by exact Finset.card_erase_of_mem hia]
    omega
  have hBcard : B.card = 2 * l := by
    rw [show B.card = t.card - 1 by exact Finset.card_erase_of_mem hibT]
    change t.card = 2 * l + 1 at ht
    omega
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hxs : x ∈ s := (Finset.mem_erase.mp hxA).2
    have hxt : x ∈ t := (Finset.mem_erase.mp hxB).2
    simp [t, hxs] at hxt
  have hRL : Disjoint R L := by
    rw [Finset.disjoint_left]
    intro x hxR hxL
    simp only [R, Finset.mem_union] at hxR
    simp only [L, Finset.mem_insert, Finset.mem_singleton] at hxL
    rcases hxL with hxia | hxib
    · subst x
      rcases hxR with hxA | hxB
      · exact (Finset.mem_erase.mp hxA).1 rfl
      · have hiaT : ia ∈ t := (Finset.mem_erase.mp hxB).2
        simp [t, hia] at hiaT
    · subst x
      rcases hxR with hxA | hxB
      · have hibS : ib ∈ s := (Finset.mem_erase.mp hxA).2
        exact hib hibS
      · exact (Finset.mem_erase.mp hxB).1 rfl
  have hcover : R ∪ L = (Finset.univ : Finset (Fin (2 * m))) := by
    ext x
    simp only [R, A, B, L, t, Finset.mem_union, Finset.mem_erase,
      Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro _
      trivial
    · intro _
      by_cases hxia : x = ia
      · exact Or.inr (Or.inl hxia)
      · by_cases hxib : x = ib
        · exact Or.inr (Or.inr hxib)
        · by_cases hxs : x ∈ s
          · exact Or.inl (Or.inl ⟨hxia, hxs⟩)
          · exact Or.inl (Or.inr ⟨hxib, hxs⟩)
  have hLcard : L.card = 2 := by simp [L, hiab]
  let cA : Fin (2 * k) ≃ Fin A.card := finCongr hAcard.symm
  let cB : Fin (2 * l) ≃ Fin B.card := finCongr hBcard.symm
  let cL : Fin 2 ≃ Fin L.card := finCongr hLcard.symm
  let eA : Fin (2 * k) ≃ {x : Fin (2 * m) // x ∈ A} :=
    cA.trans (finsetIndexEquiv A)
  let eB : Fin (2 * l) ≃ {x : Fin (2 * m) // x ∈ B} :=
    cB.trans (finsetIndexEquiv B)
  let eL : Fin 2 ≃ {x : Fin (2 * m) // x ∈ L} :=
    cL.trans (finsetIndexEquiv L)
  let eR : Fin ((2 * k) + (2 * l)) ≃ {x : Fin (2 * m) // x ∈ R} :=
    finSumFinEquiv.symm |>.trans (Equiv.sumCongr eA eB) |>.trans
      (Equiv.Finset.union A B hAB)
  let eAll : Fin (((2 * k) + (2 * l)) + 2) ≃ Fin (2 * m) :=
    finSumFinEquiv.symm |>.trans (Equiv.sumCongr eR eL) |>.trans
      (Equiv.Finset.union R L hRL) |>.trans
        (Equiv.setCongr (by
          ext x
          simp [hcover])) |>.trans (Equiv.Set.univ _)
  let zA : Fin (2 * k) → ℂ := fun i ↦ z (eA i)
  let zB : Fin (2 * l) → ℂ := fun i ↦ z (eB i)
  let zL : Fin 2 → ℂ := fun i ↦ z (eL i)
  have hzA : ∀ i, Complex.normSq (zA i) = 1 := fun i ↦ hz _
  have hzB : ∀ i, Complex.normSq (zB i) = 1 := fun i ↦ hz _
  have hzL : ∀ i, Complex.normSq (zL i) = 1 := fun i ↦ hz _
  have hcA : ∀ i, ProjectivelyCloseSq ρ a (zA i) := by
    intro i
    exact hclose₁ _ (Finset.mem_erase.mp (eA i).property).2
  have hcB : ∀ i, ProjectivelyCloseSq ρ b (zB i) := by
    intro i
    have hiT := (Finset.mem_erase.mp (eB i).property).2
    exact hclose₂ _ (by simpa [t] using hiT)
  obtain ⟨u, v, hu, hv, hE, hcard⟩ :=
    exists_pairing_of_two_projective_clusters' hkl zA zB hzA hzB
      a b ha hb hρ hρsq hcA hcB
  have hordered : Fin.append (Fin.append zA zB) zL = fun i ↦ z (eAll i) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro q
      refine Fin.addCases ?_ ?_ q
      · intro x
        simp [zA, eAll, eR, eA, eB, eL, cA, cB, cL]
        rfl
      · intro x
        simp [zB, eAll, eR, eA, eB, eL, cA, cB, cL]
        rfl
    · intro x
      simp [zL, eAll, eR, eA, eB, eL, cA, cB, cL]
      rfl
  have hext := card_residual_le_two_extension (Fin.append zA zB)
    (zL 0) (zL 1) (hzL 0) (hzL 1)
  have hreindex :
      ((Finset.univ.filter fun ε : SignVec (((2 * k) + (2 * l)) + 2) ↦
        Complex.normSq
          (signedSum (Fin.append (Fin.append zA zB) zL) ε) ≤ 2).card) =
      ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
        Complex.normSq (signedSum z ε) ≤ 2).card) := by
    rw [hordered]
    exact card_signedSum_reindex_general z eAll
      (fun w ↦ Complex.normSq w ≤ 2)
  refine ⟨u, v, hu, hv, hE, ?_⟩
  rw [hcard ((1 : ℝ) / 4)]
  have hzLvec : ![zL 0, zL 1] = zL := by
    funext i
    fin_cases i <;> rfl
  rw [hzLvec] at hext
  exact hext.trans_eq hreindex

def flipLast {N : ℕ} (i : Fin (N + 1)) : Bool := decide (i ≠ Fin.last N)

def shiftFlip {N : ℕ} (i : Fin N) : Bool := decide (i.val + 1 < N)

def shiftIndex {m : ℕ} (hm : 0 < m) (i : Fin (2 * m)) : Fin (2 * m) :=
  if h : i.val + 1 < 2 * m then ⟨i.val + 1, h⟩ else ⟨0, by omega⟩

lemma shiftIndex_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (shiftIndex hm) := by
  intro i j hij
  by_cases hi : i.val + 1 < 2 * m <;> by_cases hj : j.val + 1 < 2 * m
  · apply Fin.ext
    simpa [shiftIndex, hi, hj] using congrArg Fin.val hij
  · have hval := congrArg Fin.val hij
    simp [shiftIndex, hi, hj] at hval
  · have hval := congrArg Fin.val hij
    simp [shiftIndex, hi, hj] at hval
  · apply Fin.ext
    have hi' := i.isLt
    have hj' := j.isLt
    omega

lemma shiftIndex_surjective {m : ℕ} (hm : 0 < m) :
    Function.Surjective (shiftIndex hm) := by
  intro j
  by_cases hj : j.val = 0
  · let i : Fin (2 * m) := ⟨2 * m - 1, by omega⟩
    refine ⟨i, ?_⟩
    have hnot : ¬(i.val + 1 < 2 * m) := by dsimp [i]; omega
    apply Fin.ext
    simp [shiftIndex, i, hnot, hj]
  · let i : Fin (2 * m) := ⟨j.val - 1, by omega⟩
    refine ⟨i, ?_⟩
    have hi : i.val + 1 < 2 * m := by dsimp [i]; omega
    apply Fin.ext
    simp [shiftIndex, hi, i]
    omega

noncomputable def shiftEquiv {m : ℕ} (hm : 0 < m) : Equiv.Perm (Fin (2 * m)) :=
  Equiv.ofBijective (shiftIndex hm) ⟨shiftIndex_injective hm, shiftIndex_surjective hm⟩

@[simp] lemma shiftEquiv_apply {m : ℕ} (hm : 0 < m) (i : Fin (2 * m)) :
    shiftEquiv hm i = shiftIndex hm i := rfl

def shiftedClosedChain {m : ℕ} (hm : 0 < m) (x : Fin (2 * m) → ℂ)
    (i : Fin (2 * m)) : ℂ :=
  closedChain (by omega : 0 < 2 * m) x (i.val + 1)

lemma shiftedClosedChain_eq_orient_rotate {m : ℕ} (hm : 0 < m)
    (x : Fin (2 * m) → ℂ) :
    shiftedClosedChain hm x =
      signedOrient (fun i ↦ x (shiftEquiv hm i))
        (fun i ↦ shiftFlip i) := by
  funext i
  by_cases hs : i.val + 1 < 2 * m
  · rw [shiftedClosedChain, closedChain_of_lt _ _ hs]
    simp [signedOrient, shiftFlip, shiftIndex, hs]
  · rw [shiftedClosedChain]
    have hge : 2 * m ≤ i.val + 1 := by omega
    rw [closedChain_of_ge _ _ hge]
    let z : Fin (2 * m) := ⟨0, by omega⟩
    have hi0 : shiftEquiv hm i = z := by
      apply Fin.ext
      simp [shiftIndex, hs, z]
    change -x ⟨0, by omega⟩ = (sign (shiftFlip i) : ℂ) * x (shiftEquiv hm i)
    rw [hi0]
    simp [shiftFlip, hs, z]

lemma card_smallBall_shiftedClosedChain {m : ℕ} (hm : 0 < m)
    (x : Fin (2 * m) → ℂ) (R : ℝ) :
    ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
      Complex.normSq (signedSum (shiftedClosedChain hm x) ε) < R).card) =
    ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
      Complex.normSq (signedSum x ε) < R).card) := by
  rw [shiftedClosedChain_eq_orient_rotate]
  rw [card_smallBall_signedOrient]
  exact card_smallBall_reindex x (shiftEquiv hm) R

/-- The two alternating edge classes of a closed chain furnish a perfect
matching whose energy is at most half of the chain energy, while preserving
the exact signed-sum distribution. -/
lemma exists_pairing_of_closedChain_energy {m : ℕ} (hm : 0 < m)
    (x : Fin (2 * m) → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    {ρ : ℝ}
    (henergy : (∑ i ∈ Finset.range (2 * m),
      Complex.normSq
        (closedChain (by omega : 0 < 2 * m) x i -
          closedChain (by omega : 0 < 2 * m) x (i + 1))) ≤ 4 - ρ ^ 3) :
    ∃ u v : Fin m → ℂ,
      (∀ i, Complex.normSq (u i) = 1) ∧
      (∀ i, Complex.normSq (v i) = 1) ∧
      (∑ i, Complex.normSq (u i - v i)) ≤ 2 - ρ ^ 3 / 2 ∧
      ∀ R : ℝ,
        ((Finset.univ.filter fun q : SignPair m ↦
          Complex.normSq (pairSignedSum u v q) < R).card) =
        ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
          Complex.normSq (signedSum x ε) < R).card) := by
  let htwo : 0 < 2 * m := by omega
  let y : ℕ → ℂ := closedChain htwo x
  let r : Fin (2 * m) → ℂ := shiftedClosedChain hm x
  let E₀ := ∑ i, Complex.normSq (evenPart x i - oddPart x i)
  let E₁ := ∑ i, Complex.normSq (evenPart r i - oddPart r i)
  have heven : E₀ = ∑ i ∈ Finset.range m,
      Complex.normSq (y (2 * i) - y (2 * i + 1)) := by
    dsimp [E₀]
    calc
      (∑ i : Fin m, Complex.normSq (evenPart x i - oddPart x i)) =
          ∑ i : Fin m,
            Complex.normSq (y (2 * i.val) - y (2 * i.val + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        unfold evenPart oddPart
        rw [show y (2 * i.val) = x ⟨2 * i.val, by omega⟩ by
          apply closedChain_of_lt]
        rw [show y (2 * i.val + 1) = x ⟨2 * i.val + 1, by omega⟩ by
          apply closedChain_of_lt]
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun i ↦ Complex.normSq (y (2 * i) - y (2 * i + 1))) m
  have hodd : E₁ = ∑ i ∈ Finset.range m,
      Complex.normSq (y (2 * i + 1) - y (2 * i + 2)) := by
    dsimp [E₁]
    calc
      (∑ i : Fin m, Complex.normSq (evenPart r i - oddPart r i)) =
          ∑ i : Fin m,
            Complex.normSq (y (2 * i.val + 1) - y (2 * i.val + 2)) := by
        apply Finset.sum_congr rfl
        intro i hi
        unfold evenPart oddPart
        change Complex.normSq
          (shiftedClosedChain hm x ⟨2 * i.val, by omega⟩ -
            shiftedClosedChain hm x ⟨2 * i.val + 1, by omega⟩) = _
        simp only [shiftedClosedChain]
        congr 3 <;> omega
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun i ↦ Complex.normSq (y (2 * i + 1) - y (2 * i + 2))) m
  have hsplit : E₀ + E₁ =
      ∑ i ∈ Finset.range (2 * m), Complex.normSq (y i - y (i + 1)) := by
    rw [heven, hodd, sum_range_even_odd]
  have htotal : E₀ + E₁ ≤ 4 - ρ ^ 3 := by
    rw [hsplit]
    simpa [y, htwo] using henergy
  by_cases hE : E₀ ≤ 2 - ρ ^ 3 / 2
  · refine ⟨evenPart x, oddPart x, ?_, ?_, hE, ?_⟩
    · intro i
      exact hx _
    · intro i
      exact hx _
    · intro R
      exact card_pair_evenOdd_eq x R
  · have hE₁ : E₁ ≤ 2 - ρ ^ 3 / 2 := by linarith
    refine ⟨evenPart r, oddPart r, ?_, ?_, hE₁, ?_⟩
    · intro i
      exact closedChain_unit htwo x hx _
    · intro i
      exact closedChain_unit htwo x hx _
    · intro R
      rw [card_pair_evenOdd_eq r R]
      exact card_smallBall_shiftedClosedChain hm x R

lemma exists_pairing_of_three_projectively_far {m : ℕ} (hm : 0 < m)
    (z : Fin (2 * m) → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {a b c : Fin (2 * m)}
    (hab : ProjectivelyFarSq ρ (z a) (z b))
    (hac : ProjectivelyFarSq ρ (z a) (z c))
    (hbc : ProjectivelyFarSq ρ (z b) (z c)) :
    ∃ u v : Fin m → ℂ,
      (∀ i, Complex.normSq (u i) = 1) ∧
      (∀ i, Complex.normSq (v i) = 1) ∧
      (∑ i, Complex.normSq (u i - v i)) ≤ 2 - ρ ^ 3 / 2 ∧
      ∀ R : ℝ,
        ((Finset.univ.filter fun q : SignPair m ↦
          Complex.normSq (pairSignedSum u v q) < R).card) =
        ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
          Complex.normSq (signedSum z ε) < R).card) := by
  let hN : 0 < 2 * m := by omega
  obtain ⟨e, hx, hmono, hx0, harg⟩ :=
    exists_anchored_sorted_nonempty hN z hz a
  let x : Fin (2 * m) → ℂ := fun i ↦ anchoredRep (z a) (z (e i))
  let j : Fin (2 * m) := e.symm b
  let k : Fin (2 * m) := e.symm c
  have hxj : x j = anchoredRep (z a) (z b) := by simp [x, j]
  have hxk : x k = anchoredRep (z a) (z c) := by simp [x, k]
  have hfarab := projectivelyFarSq_anchoredRep (hz a) hab
  have hfarac := projectivelyFarSq_anchoredRep (hz a) hac
  have hfarbc := projectivelyFarSq_anchoredRep (hz a) hbc
  have hx0' : x ⟨0, hN⟩ = 1 := hx0
  have h0j : ProjectivelyFarSq ρ (x ⟨0, hN⟩) (x j) := by
    rw [hx0', hxj]
    simpa [anchoredRep_self (hz a)] using hfarab
  have h0k : ProjectivelyFarSq ρ (x ⟨0, hN⟩) (x k) := by
    rw [hx0', hxk]
    simpa [anchoredRep_self (hz a)] using hfarac
  have hjk : ProjectivelyFarSq ρ (x j) (x k) := by
    simpa [hxj, hxk] using hfarbc
  have hchain : (∑ i ∈ Finset.range (2 * m),
      Complex.normSq
        (closedChain hN x i - closedChain hN x (i + 1))) ≤ 4 - ρ ^ 3 := by
    by_cases horder : j ≤ k
    · exact closedChain_energy_of_far_positions hN x hx hmono hx0' harg hρ
        horder h0j hjk h0k
    · have hkorder : k ≤ j := le_of_not_ge horder
      exact closedChain_energy_of_far_positions hN x hx hmono hx0' harg hρ
        hkorder h0k (projectivelyFarSq_symm hjk) h0j
  obtain ⟨u, v, hu, hv, henergy, hcard⟩ :=
    exists_pairing_of_closedChain_energy hm x hx hchain
  refine ⟨u, v, hu, hv, henergy, ?_⟩
  intro R
  rw [hcard R]
  exact card_smallBall_anchored_reindex z (z a) (hz a) e R

def cycleSuccIndex (N : ℕ) (i : Fin (N + 1)) : Fin (N + 1) :=
  if h : i.val < N then ⟨i.val + 1, by omega⟩ else ⟨0, by omega⟩

lemma cycleSuccIndex_injective (N : ℕ) :
    Function.Injective (cycleSuccIndex N) := by
  intro i j hij
  by_cases hi : i.val < N <;> by_cases hj : j.val < N
  · apply Fin.ext
    simpa [cycleSuccIndex, hi, hj] using congrArg Fin.val hij
  · have hval := congrArg Fin.val hij
    simp [cycleSuccIndex, hi, hj] at hval
  · have hval := congrArg Fin.val hij
    simp [cycleSuccIndex, hi, hj] at hval
  · apply Fin.ext
    have hi' := i.isLt
    have hj' := j.isLt
    omega

noncomputable def cycleSuccEquiv (N : ℕ) : Fin (N + 1) ≃ Fin (N + 1) :=
  Equiv.ofBijective (cycleSuccIndex N)
    (cycleSuccIndex_injective N).bijective_of_finite

lemma append_tail_head_reindex {N : ℕ} (z : Fin (N + 1) → ℂ) :
    Fin.append (fun i : Fin N ↦ z i.succ) ![z 0] =
      fun i ↦ z (cycleSuccEquiv N i) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Fin.append_left]
    congr 1
    apply Fin.ext
    simp [cycleSuccEquiv, cycleSuccIndex]
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [cycleSuccEquiv, cycleSuccIndex]

/-! ### The even case -/

/-- A uniform quantitative bound for every nonempty even sequence.  The
constant is deliberately coarse; only its positivity and absoluteness matter. -/
theorem erdos395_even_normSq (m : ℕ) (hm : 0 < m)
    (z : Fin (2 * m) → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1) :
    ((1 : ℝ) / 1000000000000) / (2 * m) ≤
      uniformProbability (fun ε : SignVec (2 * m) ↦
        Complex.normSq (signedSum z ε) ≤ 2) := by
  have hunit : ∀ i, Complex.normSq (z i) ≤ 1 := fun i ↦ (hz i).le
  rcases three_far_or_two_cluster (by omega : 0 < 2 * m) z ((1 : ℝ) / 8) with
      hfar | ⟨a, b, hcover⟩
  · obtain ⟨i, j, k, hij, hik, hjk⟩ := hfar
    obtain ⟨u, v, hu, hv, hE, hcard⟩ :=
      exists_pairing_of_three_projectively_far hm z hz (by norm_num) hij hik hjk
    have hE' : (∑ i, Complex.normSq (u i - v i)) ≤
        (2 : ℝ) - (1 : ℝ) / 1024 := by
      convert hE using 1 <;> norm_num
    have hp := pairing_probability_lower_bound hm (by norm_num : 0 < 64)
      u v (fun i ↦ (hu i).le) (fun i ↦ (hv i).le)
      (R := 2) (α := (1 : ℝ) / 1024) (by norm_num) (by norm_num)
      hE' (by norm_num)
    have heq := uniformProbability_pair_eq u v z 2 (hcard 2)
    calc
      ((1 : ℝ) / 1000000000000) / (2 * m) ≤
          ((1 : ℝ) / 1024) /
            (800 * (64 : ℝ) ^ 2 * m * 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        norm_num
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        nlinarith
      _ ≤ uniformProbability (fun q : SignPair m ↦
          Complex.normSq (pairSignedSum u v q) < 2) := hp
      _ = uniformProbability (fun ε : SignVec (2 * m) ↦
          Complex.normSq (signedSum z ε) < 2) := heq
      _ ≤ uniformProbability (fun ε : SignVec (2 * m) ↦
          Complex.normSq (signedSum z ε) ≤ 2) :=
        uniformProbability_mono (fun _ h ↦ h.le)
  · let s : Finset (Fin (2 * m)) :=
      Finset.univ.filter fun i ↦ ProjectivelyCloseSq ((1 : ℝ) / 8) (z a) (z i)
    have hsa : ∀ i, i ∈ s →
        ProjectivelyCloseSq ((1 : ℝ) / 8) (z a) (z i) := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hsb : ∀ i, i ∉ s →
        ProjectivelyCloseSq ((1 : ℝ) / 8) (z b) (z i) := by
      intro i hi
      rcases hcover i with hai | hbi
      · exact False.elim (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩))
      · exact hbi
    have htotal : s.card + (Finset.univ \ s).card = 2 * m := by
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
      simp only [Finset.card_univ, Fintype.card_fin] at h
      omega
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' s.card
    · let l := m - k
      have hkc : s.card = 2 * k := hk
      have hlc : (Finset.univ \ s).card = 2 * l := by
        dsimp [l]
        omega
      have hkm : k + l = m := by
        dsimp [l]
        omega
      have hpair : ∃ u v : Fin (k + l) → ℂ,
          (∀ i, Complex.normSq (u i) = 1) ∧
          (∀ i, Complex.normSq (v i) = 1) ∧
          (∑ i, Complex.normSq (u i - v i)) ≤ (1 : ℝ) / 8 ∧
          ∀ R : ℝ,
            ((Finset.univ.filter fun q : SignPair (k + l) ↦
              Complex.normSq (pairSignedSum u v q) < R).card) =
            ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
              Complex.normSq (signedSum z ε) < R).card) := by
        by_cases hk0 : k = 0
        · have hs0 : s = ∅ := Finset.card_eq_zero.mp (by omega)
          have hall : ∀ i, ProjectivelyCloseSq ((1 : ℝ) / 8) (z b) (z i) := by
            intro i
            exact hsb i (by simp [hs0])
          obtain ⟨u, v, hu, hv, hE, hc⟩ :=
            exists_pairing_of_projective_cluster hm z hz (z b) (hz b)
              (by norm_num) (by norm_num) hall
          subst k
          have hlm : l = m := by omega
          rw [Nat.zero_add, hlm]
          exact ⟨u, v, hu, hv,
            hE.trans (by norm_num : 4 * ((1 : ℝ) / 8) ^ 2 ≤ (1 : ℝ) / 8), hc⟩
        · by_cases hl0 : l = 0
          · have ht0 : (Finset.univ \ s) = ∅ := Finset.card_eq_zero.mp (by omega)
            have hall : ∀ i, ProjectivelyCloseSq ((1 : ℝ) / 8) (z a) (z i) := by
              intro i
              by_contra hi
              have : i ∈ Finset.univ \ s := by
                simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
                intro his
                exact hi (hsa i his)
              simpa [ht0] using this
            obtain ⟨u, v, hu, hv, hE, hc⟩ :=
              exists_pairing_of_projective_cluster hm z hz (z a) (hz a)
                (by norm_num) (by norm_num) hall
            have hkm' : k = m := by omega
            rw [hl0, Nat.add_zero, hkm']
            exact ⟨u, v, hu, hv,
              hE.trans (by norm_num : 4 * ((1 : ℝ) / 8) ^ 2 ≤ (1 : ℝ) / 8), hc⟩
          · obtain ⟨u, v, hu, hv, hE, hc⟩ :=
              exists_pairing_of_even_partition (Nat.pos_of_ne_zero hk0)
                (Nat.pos_of_ne_zero hl0) z hz s hkc hlc (z a) (z b)
                (hz a) (hz b) (by norm_num) (by norm_num) hsa hsb
            exact ⟨u, v, hu, hv,
              hE.trans (by norm_num : 8 * ((1 : ℝ) / 8) ^ 2 ≤ (1 : ℝ) / 8), hc⟩
      obtain ⟨u, v, hu, hv, hE, hcard⟩ := hpair
      have hpos : 0 < k + l := by omega
      have hp := pairing_probability_lower_bound hpos (by norm_num : 0 < 6)
        u v (fun i ↦ (hu i).le) (fun i ↦ (hv i).le)
        (R := (1 : ℝ) / 4) (α := (1 : ℝ) / 8)
        (by norm_num) (by norm_num) (by linarith) (by norm_num)
      let e : Fin (2 * (k + l)) ≃ Fin (2 * m) := finCongr (by omega)
      let z' : Fin (2 * (k + l)) → ℂ := fun i ↦ z (e i)
      have hcard' :
          ((Finset.univ.filter fun q : SignPair (k + l) ↦
            Complex.normSq (pairSignedSum u v q) < (1 : ℝ) / 4).card) =
          ((Finset.univ.filter fun ε : SignVec (2 * (k + l)) ↦
            Complex.normSq (signedSum z' ε) <
              (1 : ℝ) / 4).card) := by
        exact (hcard ((1 : ℝ) / 4)).trans
          (card_smallBall_reindex_general z e ((1 : ℝ) / 4)).symm
      have heq := uniformProbability_pair_eq u v z' ((1 : ℝ) / 4) hcard'
      have horigEq : uniformProbability (fun ε : SignVec (2 * (k + l)) ↦
          Complex.normSq (signedSum z' ε) <
              (1 : ℝ) / 4) =
          uniformProbability (fun ε : SignVec (2 * m) ↦
            Complex.normSq (signedSum z ε) < (1 : ℝ) / 4) := by
        unfold uniformProbability
        rw [show z' = fun i ↦ z (e i) by rfl]
        rw [card_smallBall_reindex_general z e ((1 : ℝ) / 4)]
        have hden : Fintype.card (SignVec (2 * (k + l))) =
            Fintype.card (SignVec (2 * m)) := by
          simp only [card_signCube]
          rw [hkm]
        rw [hden]
      calc
        ((1 : ℝ) / 1000000000000) / (2 * m) ≤
            ((1 : ℝ) / 8) /
              (800 * (6 : ℝ) ^ 2 * (k + l) * ((1 : ℝ) / 4)) := by
          have hkmR : (k : ℝ) + l = m := by exact_mod_cast hkm
          rw [hkmR]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          norm_num
          have hmR : (0 : ℝ) < m := by exact_mod_cast hm
          nlinarith
        _ ≤ uniformProbability (fun q : SignPair (k + l) ↦
            Complex.normSq (pairSignedSum u v q) < (1 : ℝ) / 4) := by
          simpa only [Nat.cast_add, Nat.cast_ofNat] using hp
        _ = uniformProbability (fun ε : SignVec (2 * (k + l)) ↦
            Complex.normSq (signedSum z' ε) <
                (1 : ℝ) / 4) := heq
        _ = uniformProbability (fun ε : SignVec (2 * m) ↦
            Complex.normSq (signedSum z ε) < (1 : ℝ) / 4) := horigEq
        _ ≤ uniformProbability (fun ε : SignVec (2 * m) ↦
            Complex.normSq (signedSum z ε) ≤ 2) :=
          uniformProbability_mono (fun _ h ↦ by linarith)
    · let l := m - k - 1
      have hkc : s.card = 2 * k + 1 := hk
      have hlc : (Finset.univ \ s).card = 2 * l + 1 := by
        dsimp [l]
        omega
      have hkm : k + l + 1 = m := by
        dsimp [l]
        omega
      by_cases hres : k + l = 0
      · have hm1 : m = 1 := by omega
        let e₂ : Fin 2 ≃ Fin (2 * m) := finCongr (by omega)
        let z₂ : Fin 2 → ℂ := fun i ↦ z (e₂ i)
        obtain ⟨δ, hδ⟩ := exists_two_signs_cover_small (hz (e₂ 0)) (hz (e₂ 1))
          (by norm_num : Complex.normSq (0 : ℂ) ≤ (1 : ℝ) / 4)
        have hz₂vec : ![z₂ 0, z₂ 1] = z₂ := by
          funext i
          fin_cases i <;> rfl
        rw [hz₂vec] at hδ
        have hmem : δ ∈ (Finset.univ.filter fun ε : SignVec 2 ↦
            Complex.normSq (signedSum z₂ ε) ≤ 2) := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa using hδ
        have hcardpos : 1 ≤
            (Finset.univ.filter fun ε : SignVec 2 ↦
              Complex.normSq (signedSum z₂ ε) ≤ 2).card :=
          Finset.one_le_card.mpr ⟨δ, hmem⟩
        have hreindex :
            ((Finset.univ.filter fun ε : SignVec 2 ↦
              Complex.normSq (signedSum z₂ ε) ≤ 2).card) =
            ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
              Complex.normSq (signedSum z ε) ≤ 2).card) := by
          exact card_signedSum_reindex_general z e₂
            (fun w ↦ Complex.normSq w ≤ 2)
        have hcardpos' : 1 ≤
            (Finset.univ.filter fun ε : SignVec (2 * m) ↦
              Complex.normSq (signedSum z ε) ≤ 2).card := by
          rw [← hreindex]
          exact hcardpos
        unfold uniformProbability
        simp only [card_signCube]
        push_cast
        have hc : (1 : ℝ) ≤
            ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
              Complex.normSq (signedSum z ε) ≤ 2).card : ℝ) := by
          exact_mod_cast hcardpos'
        norm_num [hm1]
        linarith
      · have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
        have htne : (Finset.univ \ s).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨ia, hia⟩ := hsne
        obtain ⟨ib, hibT⟩ := htne
        have hib : ib ∉ s := (Finset.mem_sdiff.mp hibT).2
        obtain ⟨u, v, hu, hv, hE, hle⟩ :=
          exists_pairing_of_odd_partition_with_extension (Nat.pos_of_ne_zero hres)
            z hz s hkc hlc ia ib hia hib (z a) (z b) (hz a) (hz b)
            (by norm_num) (by norm_num) hsa hsb
        have hp := pairing_probability_lower_bound (Nat.pos_of_ne_zero hres)
          (by norm_num : 0 < 6) u v (fun i ↦ (hu i).le) (fun i ↦ (hv i).le)
          (R := (1 : ℝ) / 4) (α := (1 : ℝ) / 8)
          (by norm_num) (by norm_num)
          (hE.trans (by norm_num : 8 * ((1 : ℝ) / 8) ^ 2 ≤
            (1 : ℝ) / 4 - (1 : ℝ) / 8)) (by norm_num)
        let e : Fin (2 * ((k + l) + 1)) ≃ Fin (2 * m) := finCongr (by omega)
        let z' : Fin (2 * ((k + l) + 1)) → ℂ := fun i ↦ z (e i)
        have hreindexCard :
            ((Finset.univ.filter fun ε : SignVec (2 * ((k + l) + 1)) ↦
              Complex.normSq (signedSum z' ε) ≤ 2).card) =
            ((Finset.univ.filter fun ε : SignVec (2 * m) ↦
              Complex.normSq (signedSum z ε) ≤ 2).card) := by
          exact card_signedSum_reindex_general z e
            (fun w ↦ Complex.normSq w ≤ 2)
        have hle' :
            ((Finset.univ.filter fun q : SignPair (k + l) ↦
              Complex.normSq (pairSignedSum u v q) < (1 : ℝ) / 4).card) ≤
            ((Finset.univ.filter fun ε : SignVec (2 * ((k + l) + 1)) ↦
              Complex.normSq (signedSum z' ε) ≤ 2).card) :=
          hle.trans_eq hreindexCard.symm
        have hfour := uniformProbability_pair_le_four_of_card_le u v z' hle'
        have horigEq : uniformProbability (fun ε : SignVec (2 * ((k + l) + 1)) ↦
            Complex.normSq (signedSum z' ε) ≤ 2) =
            uniformProbability (fun ε : SignVec (2 * m) ↦
              Complex.normSq (signedSum z ε) ≤ 2) := by
          unfold uniformProbability
          rw [hreindexCard]
          have hden : Fintype.card (SignVec (2 * ((k + l) + 1))) =
              Fintype.card (SignVec (2 * m)) := by
            simp only [card_signCube]
            congr 1
            omega
          rw [hden]
        rw [horigEq] at hfour
        calc
          ((1 : ℝ) / 1000000000000) / (2 * m) ≤
              (1 / 4 : ℝ) *
                (((1 : ℝ) / 8) /
                  (800 * (6 : ℝ) ^ 2 * (k + l) * ((1 : ℝ) / 4))) := by
            rw [div_le_iff₀ (by positivity)]
            have hkmR : (k : ℝ) + l + 1 = m := by exact_mod_cast hkm
            rw [← hkmR]
            have hcast : (0 : ℝ) < k + l := by exact_mod_cast Nat.pos_of_ne_zero hres
            field_simp
            nlinarith
          _ ≤ (1 / 4 : ℝ) * uniformProbability
              (fun q : SignPair (k + l) ↦
                Complex.normSq (pairSignedSum u v q) < (1 : ℝ) / 4) := by
            apply mul_le_mul_of_nonneg_left
            · simpa only [Nat.cast_add, Nat.cast_ofNat] using hp
            · norm_num
          _ ≤ uniformProbability (fun ε : SignVec (2 * m) ↦
              Complex.normSq (signedSum z ε) ≤ 2) := by
            nlinarith

/-! ### The odd case -/

theorem erdos395_odd_normSq (m : ℕ)
    (z : Fin (2 * m + 1) → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1) :
    ((1 : ℝ) / 100000000000000) / (2 * m + 1) ≤
      uniformProbability (fun ε : SignVec (2 * m + 1) ↦
        Complex.normSq (signedSum z ε) ≤ 2) := by
  by_cases hm0 : m = 0
  · subst m
    have hevent : (fun ε : SignVec 1 ↦
        Complex.normSq (signedSum z ε) ≤ 2) = fun _ ↦ True := by
      funext ε
      apply propext
      simp [signedSum, Fin.sum_univ_succ, Complex.normSq_mul, hz]
      nlinarith [sign_sq (ε 0)]
    rw [hevent, uniformProbability_true]
    norm_num
  · have hm : 0 < m := Nat.pos_of_ne_zero hm0
    let ρ : ℝ := Real.sqrt ((1 : ℝ) / 3)
    have hρ : 0 ≤ ρ := Real.sqrt_nonneg _
    have hρsq : ρ ^ 2 = (1 : ℝ) / 3 := by
      dsimp [ρ]
      rw [Real.sq_sqrt]
      norm_num
    by_cases hclose : ∀ i j, ProjectivelyCloseSq ρ (z i) (z j)
    · let ztail : Fin (2 * m) → ℂ := fun i ↦ z i.succ
      have hztail : ∀ i, Complex.normSq (ztail i) = 1 := fun i ↦ hz _
      have htailclose : ∀ i j, ProjectivelyCloseSq ρ (ztail i) (ztail j) :=
        fun i j ↦ hclose i.succ j.succ
      obtain ⟨u, v, hu, hv, hE, hcard⟩ :=
        exists_pairing_of_pairwise_close_one_third hm ztail hztail
          ⟨0, by omega⟩ hρ hρsq htailclose
      have hp := pairing_probability_lower_bound hm (by norm_num : 0 < 3)
        u v (fun i ↦ (hu i).le) (fun i ↦ (hv i).le)
        (R := (1 : ℝ)) (α := (2 : ℝ) / 3)
        (by norm_num) (by norm_num) (by linarith) (by norm_num)
      have heq := uniformProbability_pair_eq u v ztail 1 (hcard 1)
      have hext := card_residual_le_one_extension ztail (z 0) (hz 0)
      have hreindex :
          ((Finset.univ.filter fun ε : SignVec (2 * m + 1) ↦
            Complex.normSq
              (signedSum (Fin.append ztail ![z 0]) ε) ≤ 2).card) =
          ((Finset.univ.filter fun ε : SignVec (2 * m + 1) ↦
            Complex.normSq (signedSum z ε) ≤ 2).card) := by
        rw [show Fin.append ztail ![z 0] =
            fun i ↦ z (cycleSuccEquiv (2 * m) i) by
          simpa [ztail] using append_tail_head_reindex z]
        exact card_signedSum_reindex_general z (cycleSuccEquiv (2 * m))
          (fun w ↦ Complex.normSq w ≤ 2)
      have hfactor := uniformProbability_le_two_of_card_le_one_extension
        (fun ε : SignVec (2 * m) ↦ Complex.normSq (signedSum ztail ε) < 1)
        (fun ε : SignVec (2 * m + 1) ↦ Complex.normSq (signedSum z ε) ≤ 2)
        (hext.trans_eq hreindex)
      calc
        ((1 : ℝ) / 100000000000000) / (2 * m + 1) ≤
            (1 / 2 : ℝ) * (((2 : ℝ) / 3) /
              (800 * (3 : ℝ) ^ 2 * m * 1)) := by
          rw [div_le_iff₀ (by positivity)]
          have hmR : (0 : ℝ) < m := by exact_mod_cast hm
          field_simp
          nlinarith
        _ ≤ (1 / 2 : ℝ) * uniformProbability
            (fun q : SignPair m ↦ Complex.normSq (pairSignedSum u v q) < 1) := by
          exact mul_le_mul_of_nonneg_left hp (by norm_num)
        _ = (1 / 2 : ℝ) * uniformProbability
            (fun ε : SignVec (2 * m) ↦ Complex.normSq (signedSum ztail ε) < 1) := by
          rw [heq]
        _ ≤ uniformProbability (fun ε : SignVec (2 * m + 1) ↦
            Complex.normSq (signedSum z ε) ≤ 2) := by
          nlinarith
    · push Not at hclose
      obtain ⟨i, j, hij⟩ := hclose
      have hfar : ProjectivelyFarSq ρ (z i) (z j) :=
        not_projectivelyCloseSq_iff.mp hij
      have hijne : i ≠ j := by
        intro h
        subst j
        have := hfar.1
        rw [hρsq] at this
        norm_num at this
      let P : Finset (Fin (2 * m + 1)) := {i, j}
      have hPcard : P.card = 2 := by simp [P, hijne]
      have hnot : ¬((Finset.univ : Finset (Fin (2 * m + 1))) ⊆ P) := by
        intro hsub
        have hc := Finset.card_le_card hsub
        simp only [Finset.card_univ, Fintype.card_fin, hPcard] at hc
        omega
      obtain ⟨k, _hkU, hkP⟩ := Finset.not_subset.mp hnot
      have hki : k ≠ i := by
        intro h
        subst k
        exact hkP (by simp [P])
      have hkj : k ≠ j := by
        intro h
        subst k
        exact hkP (by simp [P])
      let L : Finset (Fin (2 * m + 1)) := {i, j, k}
      let R : Finset (Fin (2 * m + 1)) := Finset.univ \ L
      have hji : j ≠ i := hijne.symm
      have hik : i ≠ k := hki.symm
      have hjk : j ≠ k := hkj.symm
      have hLcard : L.card = 3 := by
        simp [L, hijne, hji, hki, hik, hkj, hjk]
      have hRcard : R.card = 2 * (m - 1) := by
        change (Finset.univ \ L).card = 2 * (m - 1)
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ L)]
        simp only [Finset.card_univ, Fintype.card_fin, hLcard]
        omega
      have hRL : Disjoint R L := by
        rw [Finset.disjoint_left]
        intro x hxR hxL
        exact (Finset.mem_sdiff.mp hxR).2 hxL
      have hcover : R ∪ L = (Finset.univ : Finset (Fin (2 * m + 1))) := by
        ext x
        simp [R]
      let cR : Fin (2 * (m - 1)) ≃ Fin R.card := finCongr hRcard.symm
      let eR : Fin (2 * (m - 1)) ≃ {x : Fin (2 * m + 1) // x ∈ R} :=
        cR.trans (finsetIndexEquiv R)
      let fL : Fin 3 → {x : Fin (2 * m + 1) // x ∈ L} :=
        ![⟨i, by simp [L]⟩, ⟨j, by simp [L]⟩, ⟨k, by simp [L]⟩]
      have hfL : Function.Injective fL := by
        intro x y
        fin_cases x <;> fin_cases y <;>
          simp [fL, hijne, hji, hki, hik, hkj, hjk]
      let eL : Fin 3 ≃ {x : Fin (2 * m + 1) // x ∈ L} :=
        Equiv.ofBijective fL ((Fintype.bijective_iff_injective_and_card fL).2 ⟨hfL, by
          simp [hLcard]⟩)
      let eAll : Fin ((2 * (m - 1)) + 3) ≃ Fin (2 * m + 1) :=
        finSumFinEquiv.symm |>.trans (Equiv.sumCongr eR eL) |>.trans
          (Equiv.Finset.union R L hRL) |>.trans
            (Equiv.setCongr (by
              ext x
              simp [hcover])) |>.trans (Equiv.Set.univ _)
      let zR : Fin (2 * (m - 1)) → ℂ := fun x ↦ z (eR x)
      let zL : Fin 3 → ℂ := fun x ↦ z (eL x)
      have hzR : ∀ x, Complex.normSq (zR x) = 1 := fun x ↦ hz _
      have hzL : ∀ x, Complex.normSq (zL x) = 1 := fun x ↦ hz _
      have hzL0 : zL 0 = z i := by simp [zL, eL, fL]
      have hzL1 : zL 1 = z j := by simp [zL, eL, fL]
      have hproduct : 1 ≤ Complex.normSq (zL 0 + zL 1) *
          Complex.normSq (zL 0 - zL 1) := by
        rw [hzL0, hzL1]
        exact pair_center_product_ge_one_of_far_one_third hρsq (hz i) (hz j) hfar
      have hext := card_residual_le_three_extension zR (zL 0) (zL 1) (zL 2)
        (hzL 0) (hzL 1) (hzL 2) hproduct
      have hordered : Fin.append zR zL = fun x ↦ z (eAll x) := by
        funext x
        refine Fin.addCases ?_ ?_ x
        · intro y
          simp [zR, eAll, eR, eL, cR, fL]
          rfl
        · intro y
          simp [zL, eAll, eR, eL, cR, fL]
          rfl
      have hzLvec : ![zL 0, zL 1, zL 2] = zL := by
        funext x
        fin_cases x <;> rfl
      rw [hzLvec] at hext
      have hreindex :
          ((Finset.univ.filter fun ε : SignVec ((2 * (m - 1)) + 3) ↦
            Complex.normSq (signedSum (Fin.append zR zL) ε) ≤ 2).card) =
          ((Finset.univ.filter fun ε : SignVec (2 * m + 1) ↦
            Complex.normSq (signedSum z ε) ≤ 2).card) := by
        rw [hordered]
        exact card_signedSum_reindex_general z eAll
          (fun w ↦ Complex.normSq w ≤ 2)
      have hfactor := uniformProbability_le_eight_of_card_le_three_extension
        (fun ε : SignVec (2 * (m - 1)) ↦ Complex.normSq (signedSum zR ε) ≤ 2)
        (fun ε : SignVec ((2 * (m - 1)) + 3) ↦
          Complex.normSq (signedSum (Fin.append zR zL) ε) ≤ 2) hext
      have hfullEq : uniformProbability
          (fun ε : SignVec ((2 * (m - 1)) + 3) ↦
            Complex.normSq (signedSum (Fin.append zR zL) ε) ≤ 2) =
          uniformProbability (fun ε : SignVec (2 * m + 1) ↦
            Complex.normSq (signedSum z ε) ≤ 2) := by
        unfold uniformProbability
        rw [hreindex]
        have hden : Fintype.card (SignVec ((2 * (m - 1)) + 3)) =
            Fintype.card (SignVec (2 * m + 1)) := by
          simp only [card_signCube]
          congr 1
          omega
        rw [hden]
      rw [hfullEq] at hfactor
      by_cases hm1 : m = 1
      · subst m
        have hres : uniformProbability
            (fun ε : SignVec 0 ↦ Complex.normSq (signedSum zR ε) ≤ 2) = 1 := by
          have hevent : (fun ε : SignVec 0 ↦
              Complex.normSq (signedSum zR ε) ≤ 2) = fun _ ↦ True := by
            funext ε
            apply propext
            simp [signedSum]
          rw [hevent, uniformProbability_true]
        have hnonneg := uniformProbability_nonneg
          (fun ε : SignVec (2 * 1 + 1) ↦ Complex.normSq (signedSum z ε) ≤ 2)
        rw [hres] at hfactor
        norm_num at hfactor ⊢
        nlinarith
      · have hm2 : 0 < m - 1 := by omega
        have heven := erdos395_even_normSq (m - 1) hm2 zR hzR
        calc
          ((1 : ℝ) / 100000000000000) / (2 * m + 1) ≤
              (1 / 8 : ℝ) *
                (((1 : ℝ) / 1000000000000) /
                  ((2 : ℝ) * ((m - 1 : ℕ) : ℝ))) := by
            have hmR : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
            have hsub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ m)]
              norm_num
            rw [hsub]
            rw [show (1 / 8 : ℝ) *
                ((1 / 1000000000000 : ℝ) / (2 * ((m : ℝ) - 1))) =
                1 / (16000000000000 * ((m : ℝ) - 1)) by
              field_simp [ne_of_gt (sub_pos.mpr hmR)]
              ring]
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            norm_num
            nlinarith
          _ ≤ (1 / 8 : ℝ) * uniformProbability
              (fun ε : SignVec (2 * (m - 1)) ↦
                Complex.normSq (signedSum zR ε) ≤ 2) := by
            exact mul_le_mul_of_nonneg_left heven (by norm_num)
          _ ≤ uniformProbability (fun ε : SignVec (2 * m + 1) ↦
              Complex.normSq (signedSum z ε) ≤ 2) := by
            nlinarith

lemma normSq_le_two_iff (w : ℂ) :
    Complex.normSq w ≤ 2 ↔ ‖w‖ ≤ Real.sqrt 2 := by
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    apply (sq_le_sq₀ (norm_nonneg w) (Real.sqrt_nonneg 2)).mp
    rwa [Real.sq_sqrt (by norm_num)]
  · intro h
    have hs := (sq_le_sq₀ (norm_nonneg w) (Real.sqrt_nonneg 2)).mpr h
    rwa [Real.sq_sqrt (by norm_num)] at hs

/-- **Resolution of Erdős Problem 395.**  There is one absolute positive
constant such that every nonempty sequence of unit complex numbers has
`1/n`-scale probability of a signed sum in the closed disk of radius `√2`. -/
theorem erdos_395 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 0 < n → ∀ (z : Fin n → ℂ),
        (∀ i, ‖z i‖ = 1) →
        c / (n : ℝ) ≤
          uniformProbability (fun ε : SignVec n ↦
            ‖signedSum z ε‖ ≤ Real.sqrt 2) := by
  refine ⟨(1 : ℝ) / 100000000000000, by norm_num, ?_⟩
  intro n hn z hz
  have hzsq : ∀ i, Complex.normSq (z i) = 1 := by
    intro i
    rw [Complex.normSq_eq_norm_sq, hz i]
    norm_num
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst n
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    have hmpos : 0 < m := by omega
    have heven := erdos395_even_normSq m hmpos z hzsq
    calc
      ((1 : ℝ) / 100000000000000) / ((2 : ℝ) * m) ≤
          ((1 : ℝ) / 1000000000000) / ((2 : ℝ) * m) := by
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ uniformProbability (fun ε : SignVec (2 * m) ↦
          Complex.normSq (signedSum z ε) ≤ 2) := heven
      _ = uniformProbability (fun ε : SignVec (2 * m) ↦
          ‖signedSum z ε‖ ≤ Real.sqrt 2) := by
        congr 1
        funext ε
        exact propext (normSq_le_two_iff _)
  · subst n
    have hodd := erdos395_odd_normSq m z hzsq
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one, normSq_le_two_iff] using hodd

#print axioms erdos_395

end Erdos395

alias _root_.Erdos395.erdos395 := _root_.Erdos395.erdos_395
