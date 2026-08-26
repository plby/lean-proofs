import ErdosProblems.Erdos486.BiasedSkeleton

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Summability of the biased-colouring errors

The error at scale `j` decays geometrically in `biasedRadius j`.  Since a
radius-`n` block has only quadratically many possible indices, the errors form
a summable series.  We make this argument elementary by injecting every index
into an explicit finite block and summing a polynomial times a geometric
sequence.
-/

open scoped BigOperators
open Filter

namespace Erdos486

noncomputable section

/-- The error allowance supplied by the biased-colouring tail estimate. -/
def biasedEta (j : ℕ) : ℝ :=
  3 * ((63 : ℝ) / 64) ^ (2 * biasedRadius j)

theorem biasedEta_nonneg (j : ℕ) : 0 ≤ biasedEta j := by
  unfold biasedEta
  positivity

/-- A convenient upper bound for the number of indices in a radius block. -/
def biasedRadiusCapacity (n : ℕ) : ℕ :=
  400 * (n + 1) ^ 2

/-- Every index fits in the explicit block attached to its biased radius. -/
theorem lt_biasedRadiusCapacity (j : ℕ) :
    j < biasedRadiusCapacity (biasedRadius j) := by
  have hsqrt :
      Nat.sqrt j < 20 * (Nat.sqrt j / 20 + 1) :=
    Nat.lt_mul_div_succ (Nat.sqrt j) (by norm_num)
  have hsqrtSucc :
      Nat.sqrt j + 1 ≤ 20 * (biasedRadius j + 1) := by
    simp only [biasedRadius]
    omega
  have hj : j < (Nat.sqrt j + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' j
  calc
    j < (Nat.sqrt j + 1) ^ 2 := hj
    _ ≤ (20 * (biasedRadius j + 1)) ^ 2 :=
      Nat.pow_le_pow_left hsqrtSucc 2
    _ = biasedRadiusCapacity (biasedRadius j) := by
      simp [biasedRadiusCapacity]
      ring

/-- The block encoding used to compare the error series with a sigma-type
series having explicitly finite fibers. -/
def biasedRadiusCode (j : ℕ) :
    Σ n : ℕ, Fin (biasedRadiusCapacity n) :=
  ⟨biasedRadius j, ⟨j, lt_biasedRadiusCapacity j⟩⟩

theorem biasedRadiusCode_injective :
    Function.Injective biasedRadiusCode := by
  intro i j hij
  have hval := congrArg
    (fun x : Σ n : ℕ, Fin (biasedRadiusCapacity n) ↦ x.2.val) hij
  simpa [biasedRadiusCode] using hval

/-- The constant weight assigned to every slot of a radius block. -/
def biasedRadiusEnvelope
    (x : Σ n : ℕ, Fin (biasedRadiusCapacity n)) : ℝ :=
  3 * ((63 : ℝ) / 64) ^ (2 * x.1)

theorem summable_biasedRadiusEnvelope :
    Summable biasedRadiusEnvelope := by
  apply (summable_sigma_of_nonneg (fun x ↦ by
    unfold biasedRadiusEnvelope
    positivity)).2
  constructor
  · intro n
    exact Summable.of_finite
  · let ρ : ℝ := ((63 : ℝ) / 64) ^ 2
    have hρ : ‖ρ‖ < 1 := by
      norm_num [ρ, Real.norm_eq_abs]
    have hzero : Summable (fun n : ℕ ↦ ρ ^ n) := by
      simpa using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hρ)
    have hone : Summable (fun n : ℕ ↦ (n : ℝ) * ρ ^ n) := by
      simpa using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hρ)
    have htwo : Summable (fun n : ℕ ↦ (n : ℝ) ^ 2 * ρ ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hρ
    have hpoly :
        Summable (fun n : ℕ ↦
          1200 * (((n : ℝ) + 1) ^ 2 * ρ ^ n)) := by
      refine (htwo.add ((hone.mul_left 2).add hzero)).mul_left 1200 |>.congr ?_
      intro n
      ring
    have hfiber :
        (fun n : ℕ ↦
            ∑' _x : Fin (biasedRadiusCapacity n),
              biasedRadiusEnvelope ⟨n, _x⟩) =
          fun n : ℕ ↦ 1200 * (((n : ℝ) + 1) ^ 2 * ρ ^ n) := by
      funext n
      simp [biasedRadiusEnvelope, biasedRadiusCapacity, ρ, pow_mul]
      ring
    rw [hfiber]
    exact hpoly

/-- The biased-colouring error allowances are summable. -/
theorem summable_biasedEta : Summable biasedEta := by
  have h := summable_biasedRadiusEnvelope.comp_injective
    biasedRadiusCode_injective
  simpa [biasedEta, biasedRadiusEnvelope, biasedRadiusCode] using! h

/-- The sums of the shifted tails tend to zero. -/
theorem tendsto_biasedEta_tail :
    Tendsto (fun J ↦ ∑' n : ℕ, biasedEta (n + J)) atTop (nhds 0) :=
  tendsto_sum_nat_add biasedEta

/-- There is a cutoff after which every finite collection of error terms has
total mass at most `1 / 100`. -/
theorem exists_biasedEta_tail_finset_le :
    ∃ J0 : ℕ, ∀ s : Finset ℕ,
      (∀ j ∈ s, J0 ≤ j) → (∑ j ∈ s, biasedEta j) ≤ (1 : ℝ) / 100 := by
  have heventually :
      ∀ᶠ J in atTop, (∑' n : ℕ, biasedEta (n + J)) < (1 : ℝ) / 100 :=
    (tendsto_order.1 tendsto_biasedEta_tail).2 _ (by norm_num)
  obtain ⟨J0, hJ0⟩ := heventually.exists
  refine ⟨J0, fun s hs ↦ ?_⟩
  have hinjective : Set.InjOn (fun j : ℕ ↦ j - J0) (s : Set ℕ) := by
    intro i hi j hj hij
    have hiJ : J0 ≤ i := hs i hi
    have hjJ : J0 ≤ j := hs j hj
    calc
      i = (i - J0) + J0 := (Nat.sub_add_cancel hiJ).symm
      _ = (j - J0) + J0 := congrArg (· + J0) hij
      _ = j := Nat.sub_add_cancel hjJ
  have hsum :
      (∑ n ∈ s.image (fun j : ℕ ↦ j - J0), biasedEta (n + J0)) =
        ∑ j ∈ s, biasedEta j := by
    rw [Finset.sum_image hinjective]
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [Nat.sub_add_cancel (hs j hj)]
  have hsummableTail : Summable (fun n : ℕ ↦ biasedEta (n + J0)) :=
    (summable_nat_add_iff J0).2 summable_biasedEta
  have hfinite := hsummableTail.sum_le_tsum
    (s.image fun j : ℕ ↦ j - J0)
    (fun n _ ↦ biasedEta_nonneg (n + J0))
  rw [hsum] at hfinite
  exact hfinite.trans hJ0.le

end

end Erdos486
