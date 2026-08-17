/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Residue-density energy for Erdős Problem 438

This file contains the finite, exact part of the Khalfalah--Lodha--Szemerédi
energy increment argument.  A density profile modulo `q` is represented by a
function `Fin q → ℝ`.  Refining each residue class into `r` classes is
represented without any choice of representatives by a function
`Fin q → Fin r → ℝ`.  This nested representation makes all mean and variance
identities definitionally independent of endpoint conventions.
-/

namespace Erdos438

open scoped BigOperators

namespace Energy

noncomputable section

/-- The normalized mean of a real-valued function on `Fin q`. -/
def mean {q : ℕ} (x : Fin q → ℝ) : ℝ :=
  (∑ j, x j) / q

/-- The normalized second moment (energy) of a density profile. -/
def energy {q : ℕ} (x : Fin q → ℝ) : ℝ :=
  mean fun j => (x j) ^ 2

/-- Every entry of a density profile lies in the unit interval. -/
def IsDensity {q : ℕ} (x : Fin q → ℝ) : Prop :=
  ∀ j, 0 ≤ x j ∧ x j ≤ 1

/-- The coarse profile is obtained by averaging each block of refinements. -/
def Refines {q r : ℕ} (coarse : Fin q → ℝ) (fine : Fin q → Fin r → ℝ) : Prop :=
  ∀ j, coarse j = mean (fine j)

/-- The second moment after refining every coarse residue into `r` residues. -/
def refinedEnergy {q r : ℕ} (fine : Fin q → Fin r → ℝ) : ℝ :=
  mean fun j => mean fun k => (fine j k) ^ 2

/-- The variance contributed by the refinements of one parent residue. -/
def parentVariance {q r : ℕ} (coarse : Fin q → ℝ)
    (fine : Fin q → Fin r → ℝ) (j : Fin q) : ℝ :=
  mean fun k => (fine j k - coarse j) ^ 2

theorem mean_nonneg {q : ℕ} (_hq : 0 < q) {x : Fin q → ℝ}
    (hx : ∀ j, 0 ≤ x j) : 0 ≤ mean x := by
  unfold mean
  exact div_nonneg (Finset.sum_nonneg fun j _ => hx j) (Nat.cast_nonneg q)

theorem mean_le_mean {q : ℕ} (hq : 0 < q) {x y : Fin q → ℝ}
    (hxy : ∀ j, x j ≤ y j) : mean x ≤ mean y := by
  unfold mean
  gcongr with j
  exact hxy j

@[simp] theorem mean_const {q : ℕ} (hq : 0 < q) (c : ℝ) :
    mean (fun _ : Fin q => c) = c := by
  simp [mean, hq.ne']

theorem mean_sub {q : ℕ} (x y : Fin q → ℝ) :
    mean (fun j => x j - y j) = mean x - mean y := by
  simp only [mean, Finset.sum_sub_distrib]
  ring

theorem mean_add {q : ℕ} (x y : Fin q → ℝ) :
    mean (fun j => x j + y j) = mean x + mean y := by
  simp only [mean, Finset.sum_add_distrib]
  ring

theorem mean_smul {q : ℕ} (c : ℝ) (x : Fin q → ℝ) :
    mean (fun j => c * x j) = c * mean x := by
  simp only [mean, ← Finset.mul_sum]
  ring

/-- The elementary identity `E[X²] - E[X]² = E[(X-E[X])²]`. -/
theorem mean_sq_sub_sq_eq_variance {r : ℕ} (hr : 0 < r)
    (x : Fin r → ℝ) (c : ℝ) (hmean : mean x = c) :
    mean (fun k => (x k) ^ 2) - c ^ 2 =
      mean (fun k => (x k - c) ^ 2) := by
  rw [show (fun k => (x k - c) ^ 2) =
      (fun k => (x k) ^ 2 - (2 * c) * x k + c ^ 2) by
        funext k
        ring]
  rw [mean_add, mean_sub, mean_smul, mean_const hr, hmean]
  ring

/-- Exact refinement/variance identity, equation (4.9) in the write-up. -/
theorem refinedEnergy_sub_energy_eq_mean_variance
    {q r : ℕ} (_hq : 0 < q) (hr : 0 < r)
    {coarse : Fin q → ℝ} {fine : Fin q → Fin r → ℝ}
    (href : Refines coarse fine) :
    refinedEnergy fine - energy coarse =
      mean (fun j => parentVariance coarse fine j) := by
  have hpoint : ∀ j, mean (fun k => (fine j k) ^ 2) - (coarse j) ^ 2 =
      parentVariance coarse fine j := by
    intro j
    exact mean_sq_sub_sq_eq_variance hr (fine j) (coarse j) (href j).symm
  unfold refinedEnergy energy
  rw [← mean_sub]
  apply congrArg mean
  funext j
  exact hpoint j

theorem parentVariance_nonneg {q r : ℕ} (hr : 0 < r)
    (coarse : Fin q → ℝ) (fine : Fin q → Fin r → ℝ) (j : Fin q) :
    0 ≤ parentVariance coarse fine j := by
  apply mean_nonneg hr
  intro k
  positivity

/-- Refinement cannot decrease energy. -/
theorem energy_mono_of_refines {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    {coarse : Fin q → ℝ} {fine : Fin q → Fin r → ℝ}
    (href : Refines coarse fine) :
    energy coarse ≤ refinedEnergy fine := by
  rw [← sub_nonneg, refinedEnergy_sub_energy_eq_mean_variance hq hr href]
  exact mean_nonneg hq fun j => parentVariance_nonneg hr coarse fine j

/-- A density has second moment at most its first moment. -/
theorem energy_le_mean {q : ℕ} (hq : 0 < q) {x : Fin q → ℝ}
    (hx : IsDensity x) : energy x ≤ mean x := by
  apply mean_le_mean hq
  intro j
  nlinarith [(hx j).1, (hx j).2]

/-- A finite form of Cauchy--Schwarz: the second moment dominates the square
of the first moment. -/
theorem sq_mean_le_energy {q : ℕ} (hq : 0 < q) (x : Fin q → ℝ) :
    (mean x) ^ 2 ≤ energy x := by
  unfold energy
  rw [← sub_nonneg, mean_sq_sub_sq_eq_variance hq x (mean x) rfl]
  apply mean_nonneg hq
  intro j
  positivity

/-- Exact energy envelope used to pigeonhole a small increment. -/
theorem energy_bounds {q : ℕ} (hq : 0 < q) {x : Fin q → ℝ}
    (hx : IsDensity x) :
    (mean x) ^ 2 ≤ energy x ∧ energy x ≤ mean x :=
  ⟨sq_mean_le_energy hq x, energy_le_mean hq hx⟩

/-! ## Pigeonholing a small energy increment -/

/-- If the total increase along `L` steps is at most `1/4`, one step is at
most `1/(4L)`.  This is the exact telescoping pigeonhole used in KLS. -/
theorem exists_small_increment {L : ℕ} (hL : 0 < L) (E : ℕ → ℝ)
    (hspan : E L - E 0 ≤ 1 / 4) :
    ∃ i < L, E (i + 1) - E i ≤ 1 / (4 * L) := by
  by_contra! hlarge
  have hle : ∀ i ∈ Finset.range L,
      1 / (4 * (L : ℝ)) ≤ E (i + 1) - E i := by
    intro i hi
    exact (hlarge i (Finset.mem_range.mp hi)).le
  have hstrict : ∃ i ∈ Finset.range L,
      1 / (4 * (L : ℝ)) < E (i + 1) - E i := by
    exact ⟨0, Finset.mem_range.mpr hL, hlarge 0 hL⟩
  have hsum := Finset.sum_lt_sum hle hstrict
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_range_sub] at hsum
  have hcast : (0 : ℝ) < L := by exact_mod_cast hL
  have hleft : (L : ℝ) * (1 / (4 * (L : ℝ))) = 1 / 4 := by
    field_simp
  rw [hleft] at hsum
  linarith

/-! ## Quantitative bad-parent estimates -/

/-- If a positive proportion of children differ from their parent by at
least `δ/4`, that parent contributes variance at least `δ²/128`.  The
cardinality hypothesis is written over `ℝ`, avoiding any divisibility
assumption on `r`. -/
theorem parentVariance_ge_of_many_deviations
    {q r : ℕ} (hr : 0 < r) {coarse : Fin q → ℝ}
    {fine : Fin q → Fin r → ℝ} {j : Fin q} {δ : ℝ}
    (hδ : 0 ≤ δ) (S : Finset (Fin r))
    (hS : (r : ℝ) / 8 ≤ S.card)
    (hdev : ∀ k ∈ S, δ / 4 ≤ |fine j k - coarse j|) :
    δ ^ 2 / 128 ≤ parentVariance coarse fine j := by
  have hterm : ∀ k ∈ S, δ ^ 2 / 16 ≤ (fine j k - coarse j) ^ 2 := by
    intro k hk
    have hsquare : (δ / 4) ^ 2 ≤ |fine j k - coarse j| ^ 2 :=
      (sq_le_sq₀ (div_nonneg hδ (by norm_num)) (abs_nonneg _)).2 (hdev k hk)
    rw [sq_abs] at hsquare
    convert hsquare using 1
    ring
  have hsumS : (S.card : ℝ) * (δ ^ 2 / 16) ≤
      ∑ k ∈ S, (fine j k - coarse j) ^ 2 := by
    calc
      (S.card : ℝ) * (δ ^ 2 / 16) = ∑ _k ∈ S, δ ^ 2 / 16 := by simp
      _ ≤ ∑ k ∈ S, (fine j k - coarse j) ^ 2 :=
        Finset.sum_le_sum fun k hk => hterm k hk
  have hsumAll : (∑ k ∈ S, (fine j k - coarse j) ^ 2) ≤
      ∑ k, (fine j k - coarse j) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun k _ _ => sq_nonneg (fine j k - coarse j))
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  unfold parentVariance mean
  rw [le_div_iff₀ hrR]
  have hδsq : 0 ≤ δ ^ 2 := sq_nonneg δ
  calc
    δ ^ 2 / 128 * (r : ℝ) ≤
        (S.card : ℝ) * (δ ^ 2 / 16) := by nlinarith
    _ ≤ ∑ k ∈ S, (fine j k - coarse j) ^ 2 := hsumS
    _ ≤ ∑ k, (fine j k - coarse j) ^ 2 := hsumAll

/-- A set of parents each contributing variance at least `t` has total
cardinality bounded by the global mean variance. -/
theorem badParents_card_mul_le
    {q : ℕ} (hq : 0 < q) (v : Fin q → ℝ) (B : Finset (Fin q))
    {t σ : ℝ} (hv : ∀ j, 0 ≤ v j)
    (hbad : ∀ j ∈ B, t ≤ v j) (hglobal : mean v ≤ σ) :
    (B.card : ℝ) * t ≤ (q : ℝ) * σ := by
  have hsumB : (B.card : ℝ) * t ≤ ∑ j ∈ B, v j := by
    calc
      (B.card : ℝ) * t = ∑ _j ∈ B, t := by simp
      _ ≤ ∑ j ∈ B, v j := Finset.sum_le_sum fun j hj => hbad j hj
  have hsumAll : (∑ j ∈ B, v j) ≤ ∑ j, v j := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun j _ _ => hv j)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsumGlobal : (∑ j, v j) ≤ (q : ℝ) * σ := by
    unfold mean at hglobal
    rw [div_le_iff₀ hqR] at hglobal
    simpa [mul_comm] using hglobal
  exact hsumB.trans (hsumAll.trans hsumGlobal)

/-- The numerical specialization used in the proof: if the mean variance is
smaller than `δ³/8192`, fewer than `δ q / 2` parents can have variance at
least `δ²/128`. -/
theorem badParents_card_lt_half
    {q : ℕ} (hq : 0 < q) (v : Fin q → ℝ) (B : Finset (Fin q))
    {δ σ : ℝ} (hδ : 0 < δ) (hv : ∀ j, 0 ≤ v j)
    (hbad : ∀ j ∈ B, δ ^ 2 / 128 ≤ v j)
    (hglobal : mean v ≤ σ) (hσ : σ < δ ^ 3 / 8192) :
    (B.card : ℝ) < δ * q / 2 := by
  have hcard := badParents_card_mul_le hq v B hv hbad hglobal
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  nlinarith [mul_pos hδsq hqR]

/-! ## Padded lengths and nested moduli -/

/-- A convenient (not necessarily least) positive multiple of `Q` above
`N`.  Its excess is at most `Q`, which is all the asymptotic argument uses. -/
def paddedLength (Q N : ℕ) : ℕ :=
  Q * (N / Q + 1)

theorem dvd_paddedLength (Q N : ℕ) : Q ∣ paddedLength Q N := by
  exact dvd_mul_right Q (N / Q + 1)

theorem lt_paddedLength {Q N : ℕ} (hQ : 0 < Q) :
    N < paddedLength Q N := by
  have hmod := Nat.mod_lt N hQ
  calc
    N = N % Q + Q * (N / Q) := (Nat.mod_add_div N Q).symm
    _ < Q + Q * (N / Q) := Nat.add_lt_add_right hmod _
    _ = paddedLength Q N := by simp [paddedLength, Nat.mul_add, add_comm]

theorem paddedLength_le_add {Q N : ℕ} :
    paddedLength Q N ≤ N + Q := by
  have hdiv := Nat.div_mul_le_self N Q
  calc
    paddedLength Q N = (N / Q) * Q + Q := by
      simp [paddedLength, Nat.mul_add, mul_comm]
    _ ≤ N + Q := Nat.add_le_add_right hdiv Q

/-- A finite chain of positive moduli in which each level divides the next. -/
structure NestedModuli (L : ℕ) where
  q : Fin (L + 1) → ℕ
  pos : ∀ i, 0 < q i
  dvd_succ : ∀ i : Fin L, q i.castSucc ∣ q i.succ

/-! ## Profiles arising from an actual finite set -/

/-- The canonical residue of a natural number, as an element of `Fin q`. -/
def residueIndex (q : ℕ) (hq : 0 < q) (a : ℕ) : Fin q :=
  ⟨a % q, Nat.mod_lt a hq⟩

/-- Number of elements of `A` in one residue class modulo `q`. -/
def residueClassCard (A : Finset ℕ) (q : ℕ) (hq : 0 < q) (j : Fin q) : ℕ :=
  (A.filter fun a => residueIndex q hq a = j).card

/-- Exact normalized residue density `q |A_j| / N`. -/
def residueDensity (A : Finset ℕ) (N q : ℕ) (hq : 0 < q) (j : Fin q) : ℝ :=
  (q : ℝ) / N * residueClassCard A q hq j

theorem sum_residueClassCard (A : Finset ℕ) (q : ℕ) (hq : 0 < q) :
    ∑ j, residueClassCard A q hq j = A.card := by
  have hmap : (A : Set ℕ).MapsTo (residueIndex q hq)
      (Finset.univ : Finset (Fin q)) := by
    intro a ha
    exact Finset.mem_univ _
  symm
  simpa [residueClassCard] using Finset.card_eq_sum_card_fiberwise hmap

/-- The mean of the residue densities is exactly the global density. -/
theorem mean_residueDensity (A : Finset ℕ) {N q : ℕ}
    (hN : 0 < N) (hq : 0 < q) :
    mean (residueDensity A N q hq) = (A.card : ℝ) / N := by
  have hsumNat := sum_residueClassCard A q hq
  have hsumReal : (∑ j, (residueClassCard A q hq j : ℝ)) = (A.card : ℝ) := by
    exact_mod_cast hsumNat
  unfold mean residueDensity
  rw [← Finset.mul_sum, hsumReal]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp [hqR]

/-- A class-size bound immediately makes the normalized profile a genuine
density profile.  For padded intervals the bound follows by counting one
complete set of residue blocks. -/
theorem residueDensity_isDensity_of_bound
    (A : Finset ℕ) {N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hclass : ∀ j, (q : ℝ) * residueClassCard A q hq j ≤ N) :
    IsDensity (residueDensity A N q hq) := by
  intro j
  constructor
  · unfold residueDensity
    positivity
  · unfold residueDensity
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_mul_eq_mul_div, div_le_one hNR]
    simpa [mul_comm] using hclass j

/-! ## Dense good support -/

/-- Delete a chosen set of bad parent residues from a density profile. -/
def discard (B : Finset (Fin q)) (x : Fin q → ℝ) (j : Fin q) : ℝ :=
  if j ∈ B then 0 else x j

/-- Good parents whose coarse density is at least `δ/2`. -/
def denseGoodSupport (B : Finset (Fin q)) (δ : ℝ)
    (x : Fin q → ℝ) : Finset (Fin q) :=
  Finset.univ.filter fun j => j ∉ B ∧ δ / 2 ≤ x j

theorem mean_indicator {q : ℕ} (_hq : 0 < q) (D : Finset (Fin q)) :
    mean (fun j => if j ∈ D then (1 : ℝ) else 0) = D.card / q := by
  unfold mean
  simp

/-- Deleting `B` loses at most `|B|/q` of the normalized mass. -/
theorem mean_sub_discard_le_card
    {q : ℕ} (hq : 0 < q) {x : Fin q → ℝ} (hx : IsDensity x)
    (B : Finset (Fin q)) :
    mean x - mean (discard B x) ≤ B.card / q := by
  rw [← mean_sub]
  calc
    mean (fun j => x j - discard B x j) ≤
        mean (fun j => if j ∈ B then (1 : ℝ) else 0) := by
      apply mean_le_mean hq
      intro j
      by_cases hj : j ∈ B
      · simp [discard, hj, (hx j).2]
      · simp [discard, hj]
    _ = B.card / q := mean_indicator hq B

/-- Pointwise majorant used to turn mass on good residues into a lower bound
for the number of dense good residues. -/
theorem discard_le_denseGood_majorant
    {q : ℕ} {x : Fin q → ℝ} (hx : IsDensity x)
    (B : Finset (Fin q)) {δ : ℝ} (hδ : 0 ≤ δ) (j : Fin q) :
    discard B x j ≤
      if j ∈ denseGoodSupport B δ x then 1 else δ / 2 := by
  classical
  by_cases hjB : j ∈ B
  · have hδhalf : 0 ≤ δ / 2 := div_nonneg hδ (by norm_num)
    simpa [discard, denseGoodSupport, hjB] using hδhalf
  · by_cases hjδ : δ / 2 ≤ x j
    · simp [discard, denseGoodSupport, hjB, hjδ, (hx j).2]
    · simp [discard, denseGoodSupport, hjB, hjδ, le_of_not_ge hjδ]

theorem mean_denseGood_majorant
    {q : ℕ} (hq : 0 < q) {x : Fin q → ℝ} (hx : IsDensity x)
    (B : Finset (Fin q)) {δ : ℝ} (hδ : 0 ≤ δ) :
    mean (discard B x) ≤
      mean (fun j => if j ∈ denseGoodSupport B δ x then 1 else δ / 2) := by
  exact mean_le_mean hq fun j => discard_le_denseGood_majorant hx B hδ j

theorem mean_two_level {q : ℕ} (hq : 0 < q) (D : Finset (Fin q)) (c : ℝ) :
    mean (fun j => if j ∈ D then (1 : ℝ) else c) =
      D.card / q + (1 - D.card / q) * c := by
  have hfun : (fun j : Fin q => if j ∈ D then (1 : ℝ) else c) =
      (fun j => c + (1 - c) * (if j ∈ D then (1 : ℝ) else 0)) := by
    funext j
    by_cases hj : j ∈ D <;> simp [hj]
  rw [hfun, mean_add, mean_smul, mean_const hq, mean_indicator hq]
  ring

/-- Abstract extraction of the support to which the LOS modular theorem is
applied.  It proves strictly more than `11q/32` dense good parents, but does
not invoke LOS itself. -/
theorem eleven_thirtytwo_lt_denseGoodSupport
    {q : ℕ} (hq : 0 < q) {x : Fin q → ℝ} (hx : IsDensity x)
    (B : Finset (Fin q)) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hmass : 11 / 32 + δ ≤ mean x)
    (hbad : (B.card : ℝ) < δ * q / 2) :
    (11 : ℝ) / 32 < ((denseGoodSupport B δ x).card : ℝ) / q := by
  let D := denseGoodSupport B δ x
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlost := mean_sub_discard_le_card hq hx B
  have hbad' : (B.card : ℝ) / q < δ / 2 := by
    rw [div_lt_iff₀ hqR]
    nlinarith
  have hgoodMass : 11 / 32 + δ / 2 < mean (discard B x) := by
    nlinarith
  have hupper := mean_denseGood_majorant hq hx B hδ.le
  rw [mean_two_level hq D (δ / 2)] at hupper
  change mean (discard B x) ≤
    (D.card : ℝ) / q + (1 - (D.card : ℝ) / q) * (δ / 2) at hupper
  by_contra! hD
  change (D.card : ℝ) / q ≤ (11 : ℝ) / 32 at hD
  have hcoef : 0 ≤ 1 - δ / 2 := by linarith
  have hprod := mul_le_mul_of_nonneg_right hD hcoef
  have hmajor :
      (D.card : ℝ) / q + (1 - (D.card : ℝ) / q) * (δ / 2) ≤
        11 / 32 + 21 * δ / 64 := by
    nlinarith
  have hstrict : 11 / 32 + 21 * δ / 64 < 11 / 32 + δ / 2 := by
    nlinarith
  linarith

end

end Energy

end Erdos438
