/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim61Full
import ErdosProblems.Erdos547b.EvenReducedPadding

noncomputable section

namespace Erdos547b.ZhaoClaim61Numerics

open Erdos547b.ZhaoEvenReducedPadding

theorem ec1_numeric_of_total_error
    (α : ℚ) (q exceptional loss : ℕ)
    (hsmall : 3 * (exceptional + loss) ≤ q)
    (herror :
      (((3 * q * (exceptional + loss) : ℕ) : ℕ) : ℚ) ≤
        α * (q : ℚ) * (q : ℚ)) :
    (1 - α) * (q : ℚ) * (q : ℚ) ≤
      ((((q - exceptional) * (q - loss) -
        2 * q * (exceptional + loss) : ℕ) : ℕ) : ℚ) := by
  have heq : exceptional ≤ q := by omega
  have hlq : loss ≤ q := by omega
  have hbase : 2 * q * (exceptional + loss) ≤
      (q - exceptional) * (q - loss) := by
    have hsR : (3 : ℚ) * (exceptional + loss) ≤ q := by
      exact_mod_cast hsmall
    have heR : (exceptional : ℚ) ≤ q := by exact_mod_cast heq
    have hlR : (loss : ℚ) ≤ q := by exact_mod_cast hlq
    have hnonneg : (0 : ℚ) ≤ exceptional * loss := by positivity
    have hR : (2 : ℚ) * q * (exceptional + loss) ≤
        (q - exceptional) * (q - loss) := by
      nlinarith
    exact_mod_cast hR
  rw [Nat.cast_sub hbase, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub heq, Nat.cast_sub hlq]
  push_cast at herror ⊢
  have hnonneg : (0 : ℚ) ≤ exceptional * loss := by positivity
  nlinarith

theorem claim67_scale_of_capacity
    (ι : Type*) [Fintype ι]
    (q exceptional loss m c : ℕ)
    (hhost : exceptional + Fintype.card ι * m = 2 * q)
    (hsmall : exceptional + loss ≤ q)
    (hc : c ≤ paddedHalf ι)
    (hcapacity : m + 2 * loss + exceptional ≤ 2 * c * m) :
    (paddedHalf ι - c) * m ≤ (q - loss) - exceptional := by
  have hlq : loss ≤ q := by omega
  have heql : exceptional ≤ q - loss := by omega
  have hpad : 2 * paddedHalf ι ≤ Fintype.card ι + 1 := by
    exact paddedCard_le_card_add_one ι
  have hpadMul :
      (2 * paddedHalf ι : ℕ) * m ≤ (Fintype.card ι + 1) * m :=
    Nat.mul_le_mul_right m hpad
  have hreal :
      (2 : ℚ) * ((paddedHalf ι - c : ℕ) : ℚ) * m ≤
        (2 : ℚ) * (((q - loss) - exceptional : ℕ) : ℚ) := by
    have hcR : (c : ℚ) ≤ paddedHalf ι := by exact_mod_cast hc
    have hlqR : (loss : ℚ) ≤ q := by exact_mod_cast hlq
    have heqlR : (exceptional : ℚ) ≤ q - loss := by exact_mod_cast heql
    have hhostR : (exceptional : ℚ) + Fintype.card ι * (m : ℚ) =
        2 * q := by exact_mod_cast hhost
    have hcapR : (m : ℚ) + 2 * loss + exceptional ≤ 2 * c * m := by
      exact_mod_cast hcapacity
    have hpadR : (2 : ℚ) * paddedHalf ι * m ≤
        (Fintype.card ι + 1 : ℕ) * (m : ℚ) := by
      exact_mod_cast hpadMul
    rw [Nat.cast_sub hc, Nat.cast_sub heql, Nat.cast_sub hlq]
    push_cast at hpadR ⊢
    nlinarith
  have hn' : 2 * (paddedHalf ι - c) * m ≤
      2 * ((q - loss) - exceptional) := by
    exact_mod_cast hreal
  have hn : 2 * ((paddedHalf ι - c) * m) ≤
      2 * ((q - loss) - exceptional) := by
    simpa [Nat.mul_assoc] using hn'
  omega

/-- The cardinality scale for quantitative large clusters is the same
algebra as the degree scale, with the discarded high vertices in non-large
clusters taking the place of degree-form loss. -/
theorem claim67_card_scale_of_rich_error
    (ι : Type*) [Fintype ι]
    (q exceptional richError m c : ℕ)
    (hhost : exceptional + Fintype.card ι * m = 2 * q)
    (hsmall : exceptional + richError ≤ q)
    (hc : c ≤ paddedHalf ι)
    (hcapacity : m + 2 * richError + exceptional ≤ 2 * c * m) :
    (paddedHalf ι - c) * m ≤ q - exceptional - richError := by
  have h := claim67_scale_of_capacity ι q exceptional richError m c
    hhost hsmall hc hcapacity
  have her : exceptional ≤ q := by omega
  have hsub : (q - richError) - exceptional = q - exceptional - richError := by
    omega
  rw [hsub] at h
  exact h

/-- EC1 arithmetic with the additional quantitative-large-cluster error.
This is a direct specialization of `ec1_numeric_of_total_error`, grouping
exceptional and discarded non-large high vertices into the first deficit. -/
theorem ec1_numeric_of_rich_error
    (α : ℚ) (q exceptional loss richError : ℕ)
    (hsmall : 3 * (exceptional + loss + richError) ≤ q)
    (herror :
      (((3 * q * (exceptional + loss + richError) : ℕ) : ℕ) : ℚ) ≤
        α * (q : ℚ) * (q : ℚ)) :
    (1 - α) * (q : ℚ) * (q : ℚ) ≤
      ((((q - exceptional - richError) * (q - loss) -
        2 * q * (exceptional + loss + richError) : ℕ) : ℕ) : ℚ) := by
  have hbase := ec1_numeric_of_total_error α q
    (exceptional + richError) loss
  have hsmall' : 3 * ((exceptional + richError) + loss) ≤ q := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsmall
  have herror' :
      (((3 * q * ((exceptional + richError) + loss) : ℕ) : ℕ) : ℚ) ≤
        α * (q : ℚ) * (q : ℚ) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using herror
  have h := hbase hsmall' herror'
  have her : exceptional + richError ≤ q := by omega
  have hsub : q - (exceptional + richError) = q - exceptional - richError := by
    omega
  rw [hsub] at h
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Convert the strict real reduced-cross estimate from Claims 6.17--6.18
to the non-strict integral expression consumed by the host EC2 endpoint. -/
theorem endpoint_numeric_of_reducedCross_lt
    (cross m x error q b : ℕ) (bound : ℝ) (α : ℚ)
    (hcross : (cross : ℝ) < bound)
    (hnumeric :
      bound * (m : ℝ) ^ 2 + (x : ℝ) * error + 2 * q * b ≤
        (α : ℝ) * (q : ℝ) ^ 2) :
    ((cross * (m * m) + x * error + 2 * q * b : ℕ) : ℚ) ≤
      α * (q : ℚ) * (q : ℚ) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) ^ 2 := sq_nonneg _
  have hscaled : (cross : ℝ) * (m : ℝ) ^ 2 ≤
      bound * (m : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hcross.le hm
  have hreal :
      (cross : ℝ) * (m : ℝ) ^ 2 + (x : ℝ) * error + 2 * q * b ≤
        (α : ℝ) * (q : ℝ) ^ 2 := by
    linarith
  norm_num [pow_two] at hreal
  calc
    ((cross * (m * m) + x * error + 2 * q * b : ℕ) : ℚ) ≤
        α * ((q * q : ℕ) : ℚ) := by
      exact_mod_cast hreal
    _ = α * (q : ℚ) * (q : ℚ) := by
      push_cast
      ring

#print axioms ec1_numeric_of_total_error
#print axioms claim67_scale_of_capacity
#print axioms endpoint_numeric_of_reducedCross_lt

end Erdos547b.ZhaoClaim61Numerics
