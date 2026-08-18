import ErdosProblems.Erdos140.BourgainRegular
import ErdosProblems.Erdos140.RelativeChangSanders

/-!
# Quantitative bookkeeping for the final Erdős 140 assembly

This file contains only stable numerical/volumetric adapters. In particular,
the first lemma iterates the already proved rank-only half-dilate estimate.
It is the form needed to compare an old Bohr carrier with a much smaller
explicit scalar dilate in the terminal density-step construction.
-/

open Finset
open scoped NNReal Pointwise

namespace Erdos140

noncomputable section

namespace BohrData

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Iterating the rank-only half-dilate bound n times costs
4 ^ (n * rank). The carrier on the right is the actual dyadic dilate. -/
theorem card_unit_le_four_pow_mul_card_dyadic
    (B : BohrData G) (n : ℕ) :
    (B.dilate 1).carrier.card ≤
      4 ^ (n * B.rank) *
        (B.dilate ((1 / 2 : NNReal) ^ n)).carrier.card := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hhalf :=
        card_unit_le_four_pow_rank_mul_card_half
          (B.dilate ((1 / 2 : NNReal) ^ n))
      have hhalf' :
          (B.dilate ((1 / 2 : NNReal) ^ n)).carrier.card ≤
            4 ^ B.rank *
              (B.dilate ((1 / 2 : NNReal) *
                ((1 / 2 : NNReal) ^ n))).carrier.card := by
        simpa only [rank_dilate, dilate_dilate, one_mul] using hhalf
      calc
        (B.dilate 1).carrier.card ≤
            4 ^ (n * B.rank) *
              (B.dilate ((1 / 2 : NNReal) ^ n)).carrier.card := ih
        _ ≤ 4 ^ (n * B.rank) *
              (4 ^ B.rank *
                (B.dilate ((1 / 2 : NNReal) *
                  ((1 / 2 : NNReal) ^ n))).carrier.card) := by
              exact Nat.mul_le_mul_left _ hhalf'
        _ = 4 ^ ((n + 1) * B.rank) *
              (B.dilate ((1 / 2 : NNReal) ^ (n + 1))).carrier.card := by
              simp [Nat.add_mul, pow_succ, pow_add, mul_assoc, mul_comm]

/-- If a scale contains the n-fold dyadic scale, the same explicit
cardinality loss compares the unit carrier directly with that scale. -/
theorem card_unit_le_four_pow_mul_card_dilate_of_dyadic_le
    (B : BohrData G) (n : ℕ) {rho : NNReal}
    (hrho : (1 / 2 : NNReal) ^ n ≤ rho) :
    (B.dilate 1).carrier.card ≤
      4 ^ (n * B.rank) * (B.dilate rho).carrier.card := by
  calc
    (B.dilate 1).carrier.card ≤
        4 ^ (n * B.rank) *
          (B.dilate ((1 / 2 : NNReal) ^ n)).carrier.card :=
      card_unit_le_four_pow_mul_card_dyadic B n
    _ ≤ 4 ^ (n * B.rank) * (B.dilate rho).carrier.card := by
      exact Nat.mul_le_mul_left _
        (Finset.card_le_card (carrier_dilate_mono hrho))

/-- The same dyadic estimate with the loss displayed as a uniform
cell-count power, where the cell count is four to the n. This is the shape
consumed by the final exponential-cardinality bookkeeping. -/
theorem card_unit_le_dyadicCell_pow_rank_mul_card_dilate_of_dyadic_le
    (B : BohrData G) (n : ℕ) {rho : NNReal}
    (hrho : (1 / 2 : NNReal) ^ n ≤ rho) :
    (B.dilate 1).carrier.card ≤
      (4 ^ n) ^ B.rank * (B.dilate rho).carrier.card := by
  simpa [pow_mul] using
    card_unit_le_four_pow_mul_card_dilate_of_dyadic_le B n hrho

/-- A reciprocal natural scale contains the dyadic scale selected by the
binary ceiling logarithm. -/
theorem dyadic_clog_le_inv_nat
    (P : ℕ) (hP : 0 < P) :
    (1 / 2 : NNReal) ^ (Nat.clog 2 P) ≤ ((P : NNReal)⁻¹) := by
  have hpowNat : P ≤ 2 ^ (Nat.clog 2 P) :=
    Nat.le_pow_clog (by norm_num) P
  have hpowNN : (P : NNReal) ≤ (2 : NNReal) ^ (Nat.clog 2 P) := by
    exact_mod_cast hpowNat
  have hPpos : (0 : NNReal) < P := by exact_mod_cast hP
  have hpowPos : (0 : NNReal) < (2 : NNReal) ^ (Nat.clog 2 P) := by
    positivity
  calc
    (1 / 2 : NNReal) ^ (Nat.clog 2 P) =
        ((2 : NNReal) ^ (Nat.clog 2 P))⁻¹ := by
          rw [one_div, inv_pow]
    _ ≤ ((P : NNReal)⁻¹) :=
      (inv_le_inv₀ hpowPos hPpos).2 hpowNN

/-- Direct arbitrary-scale form for any scale at least the reciprocal of a
positive natural number. The loss is an explicit cell count to the rank. -/
theorem card_unit_le_clogCell_pow_rank_mul_card_dilate_of_inv_nat_le
    (B : BohrData G) (P : ℕ) (hP : 0 < P) {rho : NNReal}
    (hrho : ((P : NNReal)⁻¹) ≤ rho) :
    (B.dilate 1).carrier.card ≤
      (4 ^ (Nat.clog 2 P)) ^ B.rank * (B.dilate rho).carrier.card := by
  apply card_unit_le_dyadicCell_pow_rank_mul_card_dilate_of_dyadic_le
  exact (dyadic_clog_le_inv_nat P hP).trans hrho

/-- A set in a rho-dilate, added after negation to the half-dilate, stays
in the unit carrier whenever the two scales add to at most one. This is the
local sumset containment used to keep Croot--Sisask denominators local. -/
theorem neg_add_half_carrier_subset_carrier
    (B : BohrData G) (A : Finset G) {rho : NNReal}
    (hA : A ⊆ (B.dilate rho).carrier)
    (hrho : rho + 1 / 2 ≤ (1 : NNReal)) :
    (-A) + (B.dilate (1 / 2)).carrier ⊆ B.carrier := by
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_neg.mp hu
  have hsum :
      -a + v ∈ (B.dilate (rho + 1 / 2)).carrier :=
    add_mem_dilate (neg_mem_carrier.mpr (hA ha)) hv
  simpa only [dilate_one] using
    (carrier_dilate_mono hrho hsum)

/-- Real-valued half-dilate volume comparison, in the convenient
unit-carrier form used after local sumset containment. -/
theorem card_real_le_four_pow_rank_mul_card_half
    (B : BohrData G) :
    (B.carrier.card : ℝ) ≤
      (4 ^ B.rank : ℕ) * ((B.dilate (1 / 2)).carrier.card : ℝ) := by
  have h :
      B.carrier.card ≤
        4 ^ B.rank * (B.dilate (1 / 2)).carrier.card := by
    simpa using card_unit_le_four_pow_rank_mul_card_half B
  exact_mod_cast h

end BohrData

/-- Croot--Sisask's raw lower bound becomes a relative-cardinality lower
bound once both input sets are dense in the same local carrier and their
sumset stays in that carrier. No ambient-group cardinality appears. -/
theorem croot_beta_mul_card_le_of_local_sumset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B : BohrData G) (A S X : Finset G) (k : ℕ)
    {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) (hsigma : 0 ≤ sigma)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (hAdense : alpha * (B.carrier.card : ℝ) ≤ (A.card : ℝ))
    (hSdense : sigma * (B.carrier.card : ℝ) ≤ (S.card : ℝ))
    (hsum : (A + S).card ≤ B.carrier.card)
    (hX :
      (((A.card : ℝ) ^ k / 2 * S.card) /
          ((A + S).card : ℝ) ^ k ≤ (X.card : ℝ))) :
    (alpha ^ k * sigma / 2) * (B.carrier.card : ℝ) ≤
      (X.card : ℝ) := by
  have hsumPos : (0 : ℝ) < (A + S).card := by
    exact_mod_cast (hA.add hS).card_pos
  have hdenPos : (0 : ℝ) < ((A + S).card : ℝ) ^ k := by
    positivity
  apply le_trans ?_ hX
  apply (le_div_iff₀ hdenPos).2
  have hsumReal : ((A + S).card : ℝ) ≤ B.carrier.card := by
    exact_mod_cast hsum
  calc
    (alpha ^ k * sigma / 2) * (B.carrier.card : ℝ) *
        ((A + S).card : ℝ) ^ k ≤
      (alpha ^ k * sigma / 2) * (B.carrier.card : ℝ) *
        (B.carrier.card : ℝ) ^ k := by
          gcongr
    _ = (alpha * (B.carrier.card : ℝ)) ^ k / 2 *
        (sigma * (B.carrier.card : ℝ)) := by
          rw [mul_pow]
          ring
    _ ≤ (A.card : ℝ) ^ k / 2 * S.card := by
          gcongr

/-- A lower bound for the relative cardinality of X gives the exact
upper bound on the local Chang dimension used by the terminal producer.
The hypothesis is written without division so downstream finite-cardinality
arguments do not have to clear denominators twice. -/
theorem localChangDimension_le_of_mul_card_le
    {G : Type*} [AddCommGroup G] [Fintype G]
    (B : BohrData G) (X : Finset G) {beta eta : ℝ}
    (hbeta : 0 < beta) (heta : 0 < eta)
    (hX : X.Nonempty)
    (hcard : beta * (B.carrier.card : ℝ) ≤ (X.card : ℝ)) :
    RelativeChangSanders.localChangDimension B X eta ≤
      2 * (1 + Real.log (2 / beta)) / eta ^ 2 := by
  have hBpos : (0 : ℝ) < B.carrier.card := by
    exact_mod_cast B.carrier_nonempty.card_pos
  have hXpos : (0 : ℝ) < X.card := by
    exact_mod_cast hX.card_pos
  have hratio :
      2 * (B.carrier.card : ℝ) / X.card ≤ 2 / beta := by
    rw [div_le_div_iff₀ hXpos hbeta]
    nlinarith
  have hargpos : 0 < 2 * (B.carrier.card : ℝ) / X.card := by
    positivity
  have hlog :
      Real.log (2 * (B.carrier.card : ℝ) / X.card) ≤
        Real.log (2 / beta) :=
    Real.log_le_log hargpos hratio
  have hetaSq : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [RelativeChangSanders.localChangDimension]
  apply (div_le_div_iff_of_pos_right hetaSq).2
  nlinarith

/-- Half-spectrum specialization of the local Chang-dimension bound. -/
theorem localChangDimension_half_le_of_mul_card_le
    {G : Type*} [AddCommGroup G] [Fintype G]
    (B : BohrData G) (X : Finset G) {beta : ℝ}
    (hbeta : 0 < beta) (hX : X.Nonempty)
    (hcard : beta * (B.carrier.card : ℝ) ≤ (X.card : ℝ)) :
    RelativeChangSanders.localChangDimension B X (1 / 2) ≤
      8 * (1 + Real.log (2 / beta)) := by
  have h :=
    localChangDimension_le_of_mul_card_le B X hbeta
      (by norm_num : (0 : ℝ) < 1 / 2) hX hcard
  convert h using 1
  ring

/-- A real-valued cardinal bound can be turned into the natural ceiling
needed for a rank-cost field. -/
theorem card_le_natCeil_of_cast_card_le
    {α : Type*} [Fintype α] (S : Finset α) {D : ℝ}
    (hcard : (S.card : ℝ) ≤ D) :
    S.card ≤ ⌈D⌉₊ := by
  exact_mod_cast hcard.trans (Nat.le_ceil D)

end

end Erdos140

#print axioms Erdos140.BohrData.card_unit_le_four_pow_mul_card_dyadic
#print axioms Erdos140.BohrData.card_unit_le_four_pow_mul_card_dilate_of_dyadic_le
#print axioms Erdos140.BohrData.card_unit_le_dyadicCell_pow_rank_mul_card_dilate_of_dyadic_le
#print axioms Erdos140.BohrData.dyadic_clog_le_inv_nat
#print axioms Erdos140.BohrData.card_unit_le_clogCell_pow_rank_mul_card_dilate_of_inv_nat_le
#print axioms Erdos140.BohrData.neg_add_half_carrier_subset_carrier
#print axioms Erdos140.BohrData.card_real_le_four_pow_rank_mul_card_half
#print axioms Erdos140.croot_beta_mul_card_le_of_local_sumset
#print axioms Erdos140.localChangDimension_le_of_mul_card_le
#print axioms Erdos140.localChangDimension_half_le_of_mul_card_le
#print axioms Erdos140.card_le_natCeil_of_cast_card_le
