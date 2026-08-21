import ErdosProblems.Erdos239.External.Erdos67.Stochastic
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Transport between the two models of a circle character

The compactness argument represents a completely multiplicative circle-valued
function as a closed subspace of the product over positive naturals.  The
analytic argument instead uses its values at the primes as coordinates.  This
file proves that these models are canonically homeomorphic and transports
probability laws and their partial-sum moments across that homeomorphism.
-/

open scoped BigOperators
open MeasureTheory

namespace Erdos67

noncomputable section

/-- Restrict a compact completely multiplicative character to the primes. -/
def primeAssignmentOfCompactCircleCharacter
    (g : CompactCircleCharacter) : PrimeAssignment :=
  fun p ↦ g.1 (Nat.toPNat p p.2.pos)

@[simp] theorem primeAssignmentOfCompactCircleCharacter_apply
    (g : CompactCircleCharacter) (p : PrimeNat) :
    primeAssignmentOfCompactCircleCharacter g p = g.1 (Nat.toPNat p p.2.pos) := rfl

theorem continuous_primeAssignmentOfCompactCircleCharacter :
    Continuous primeAssignmentOfCompactCircleCharacter := by
  exact continuous_pi fun p ↦
    continuous_compactCircleCharacter_eval (Nat.toPNat p p.2.pos)

/-- Every compact circle character is recovered from its prime values. -/
theorem compactCircleCharacterOfPrimeAssignment_primeAssignmentOfCompactCircleCharacter
    (g : CompactCircleCharacter) :
    compactCircleCharacterOfPrimeAssignment
        (primeAssignmentOfCompactCircleCharacter g) = g := by
  apply Subtype.ext
  funext n
  change primeExtension (primeAssignmentOfCompactCircleCharacter g) n = g.1 n
  let G : ℕ → Circle := fun m ↦ g.1 m.toPNat'
  have honePNat : Nat.toPNat' 1 = (1 : ℕ+) := by
    apply PNat.eq
    exact PNat.toPNat'_coe Nat.zero_lt_one
  have hG0 : G 0 = 1 := by simp [G, g.2.1]
  have hG1 : G 1 = 1 := by rw [show G 1 = g.1 (Nat.toPNat' 1) from rfl,
    honePNat, g.2.1]
  have hGmul : ∀ x y : ℕ, Nat.Coprime x y → G (x * y) = G x * G y := by
    intro x y hxy
    by_cases hx : x = 0
    · subst x
      have hy : y = 1 := by simpa using hxy
      subst y
      simp only [Nat.zero_mul, hG0, hG1, one_mul]
    · by_cases hy : y = 0
      · subst y
        have hx1 : x = 1 := by simpa using hxy
        subst x
        simp only [Nat.mul_zero, hG0, hG1, mul_one]
      · have hxpos : 0 < x := Nat.pos_of_ne_zero hx
        have hypos : 0 < y := Nat.pos_of_ne_zero hy
        have hxyPNat : (x * y).toPNat' = x.toPNat' * y.toPNat' := by
          apply PNat.eq
          change ((x * y).toPNat' : ℕ) =
            (x.toPNat' : ℕ) * (y.toPNat' : ℕ)
          rw [PNat.toPNat'_coe (mul_pos hxpos hypos), PNat.toPNat'_coe hxpos,
            PNat.toPNat'_coe hypos]
        change g.1 (x * y).toPNat' = g.1 x.toPNat' * g.1 y.toPNat'
        rw [hxyPNat]
        exact g.2.2 x.toPNat' y.toPNat'
  have hfactor := Nat.multiplicative_factorization' G hGmul hG0 hG1 (n := (n : ℕ))
  calc
    primeExtension (primeAssignmentOfCompactCircleCharacter g) n =
        (n : ℕ).factorization.prod
          (fun p e ↦ primeValue (primeAssignmentOfCompactCircleCharacter g) p ^ e) := rfl
    _ = (n : ℕ).factorization.prod fun p e ↦ G (p ^ e) := by
      apply Finsupp.prod_congr
      intro p hpSupport
      simp only [primeValue]
      split_ifs with hp
      · have hp0 : p ≠ 0 := hp.ne_zero
        have hpow0 : p ^ (n : ℕ).factorization p ≠ 0 := pow_ne_zero _ hp0
        have hpowPNat : (p ^ (n : ℕ).factorization p).toPNat' =
            (Nat.toPNat p hp.pos) ^ (n : ℕ).factorization p := by
          apply PNat.eq
          rw [PNat.toPNat'_coe (pow_pos hp.pos _)]
          rfl
        simp only [G]
        rw [hpowPNat]
        exact ((compactCircleCharacterToCircleCharacter g).map_pow
          (Nat.toPNat p hp.pos) ((n : ℕ).factorization p)).symm
      · have hsupport : p ∈ (n : ℕ).factorization.support := by
          exact hpSupport
        exact False.elim (hp (Nat.prime_of_mem_primeFactors hsupport))
    _ = G n := hfactor.symm
    _ = g.1 n := by
      have hnPNat : (n : ℕ).toPNat' = n := PNat.eq
        (PNat.toPNat'_coe n.2)
      change g.1 (n : ℕ).toPNat' = g.1 n
      rw [hnPNat]

@[simp] theorem primeAssignmentOfCompactCircleCharacter_compactCircleCharacterOfPrimeAssignment
    (z : PrimeAssignment) :
    primeAssignmentOfCompactCircleCharacter
        (compactCircleCharacterOfPrimeAssignment z) = z := by
  funext p
  exact primeExtension_prime z p

/-- The prime-coordinate and compact-product models are canonically equivalent. -/
def compactCircleCharacterEquivPrimeAssignment :
    CompactCircleCharacter ≃ₜ PrimeAssignment where
  toFun := primeAssignmentOfCompactCircleCharacter
  invFun := compactCircleCharacterOfPrimeAssignment
  left_inv := compactCircleCharacterOfPrimeAssignment_primeAssignmentOfCompactCircleCharacter
  right_inv := primeAssignmentOfCompactCircleCharacter_compactCircleCharacterOfPrimeAssignment
  continuous_toFun := continuous_primeAssignmentOfCompactCircleCharacter
  continuous_invFun := continuous_compactCircleCharacterOfPrimeAssignment

/-- The measurable equivalence underlying the canonical homeomorphism. -/
def compactCircleCharacterMeasurableEquivPrimeAssignment :
    CompactCircleCharacter ≃ᵐ PrimeAssignment :=
  compactCircleCharacterEquivPrimeAssignment.toMeasurableEquiv

/-- Push a law on compact characters to its law of prime coordinates. -/
def primeAssignmentLaw
    (mu : ProbabilityMeasure CompactCircleCharacter) :
    ProbabilityMeasure PrimeAssignment :=
  mu.map continuous_primeAssignmentOfCompactCircleCharacter.measurable.aemeasurable

private theorem sum_Icc_one_eq_range {E : Type*} [AddCommMonoid E]
    (F : ℕ → E) (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, F k) = ∑ k ∈ Finset.range m, F (k + 1) := by
  symm
  apply Finset.sum_bij (fun k _ ↦ k + 1)
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro k₁ hk₁ k₂ hk₂ h
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro k hk
    rfl

theorem circlePartialSum_primeAssignmentOfCompactCircleCharacter
    (g : CompactCircleCharacter) (m : ℕ) :
    circlePartialSum (primeAssignmentOfCompactCircleCharacter g) m =
      compactCharacterBasePartialSum m g := by
  unfold circlePartialSum compactCharacterBasePartialSum
  rw [sum_Icc_one_eq_range]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hrecover := congrArg Subtype.val
    (compactCircleCharacterOfPrimeAssignment_primeAssignmentOfCompactCircleCharacter g)
  exact congrFun hrecover ⟨k + 1, by omega⟩

theorem circlePartialSumEnergy_primeAssignmentOfCompactCircleCharacter
    (g : CompactCircleCharacter) (m : ℕ) :
    circlePartialSumEnergy m (primeAssignmentOfCompactCircleCharacter g) =
      compactCharacterPartialSumSq 1 m g := by
  unfold circlePartialSumEnergy compactCharacterPartialSumSq
  rw [circlePartialSum_primeAssignmentOfCompactCircleCharacter]
  rw [compactCharacterPartialSum_dilation]
  rw [g.2.1]
  norm_num

/-- Transport preserves every base partial-sum mean square exactly. -/
theorem meanSquarePartialSum_primeAssignmentLaw
    (mu : ProbabilityMeasure CompactCircleCharacter) (m : ℕ) :
    meanSquarePartialSum (primeAssignmentLaw mu) m =
      compactMeanSquarePartialSum mu m := by
  unfold meanSquarePartialSum primeAssignmentLaw compactMeanSquarePartialSum
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map continuous_primeAssignmentOfCompactCircleCharacter.measurable.aemeasurable
    (continuous_circlePartialSumEnergy m).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with g
  exact circlePartialSumEnergy_primeAssignmentOfCompactCircleCharacter g m

/-! ## A zero-preserving all-natural-number model -/

/-- Extend prime coordinates to a complex-valued completely multiplicative
function on all naturals, with the conventional value zero at zero. -/
def primeAssignmentMonoidWithZeroHom (z : PrimeAssignment) : ℕ →*₀ ℂ where
  toFun n := if hn : n = 0 then 0 else (primeExtension z n : ℂ)
  map_zero' := by simp
  map_one' := by simp [primeExtension_one]
  map_mul' m n := by
    by_cases hm : m = 0
    · subst m
      simp
    · by_cases hn : n = 0
      · subst n
        simp
      · rw [dif_neg (mul_ne_zero hm hn), dif_neg hm, dif_neg hn]
        exact congrArg Subtype.val (primeExtension_mul z hm hn)

@[simp] theorem primeAssignmentMonoidWithZeroHom_zero (z : PrimeAssignment) :
    primeAssignmentMonoidWithZeroHom z 0 = 0 := by simp [primeAssignmentMonoidWithZeroHom]

@[simp] theorem primeAssignmentMonoidWithZeroHom_one (z : PrimeAssignment) :
    primeAssignmentMonoidWithZeroHom z 1 = 1 := by
  change (if h : (1 : ℕ) = 0 then 0 else (primeExtension z 1 : ℂ)) = 1
  rw [dif_neg one_ne_zero, primeExtension_one]
  rfl

theorem primeAssignmentMonoidWithZeroHom_apply_of_ne_zero
    (z : PrimeAssignment) {n : ℕ} (hn : n ≠ 0) :
    primeAssignmentMonoidWithZeroHom z n = (primeExtension z n : ℂ) := by
  simp [primeAssignmentMonoidWithZeroHom, hn]

@[simp] theorem primeAssignmentMonoidWithZeroHom_apply_prime
    (z : PrimeAssignment) (p : PrimeNat) :
    primeAssignmentMonoidWithZeroHom z p = (z p : ℂ) := by
  rw [primeAssignmentMonoidWithZeroHom_apply_of_ne_zero z p.2.ne_zero]
  simp

theorem norm_primeAssignmentMonoidWithZeroHom_apply_of_ne_zero
    (z : PrimeAssignment) {n : ℕ} (hn : n ≠ 0) :
    ‖primeAssignmentMonoidWithZeroHom z n‖ = 1 := by
  rw [primeAssignmentMonoidWithZeroHom_apply_of_ne_zero z hn]
  exact Circle.norm_coe _

end

end Erdos67
