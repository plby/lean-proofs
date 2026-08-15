import Mathlib
import ErdosProblems.Erdos285.Modular
import ErdosProblems.Erdos285.PrimePowers
import ErdosProblems.Erdos285.SubsetSum
import ErdosProblems.Erdos285.Lemma12Candidates
import UnitFractions.Definitions

/-!
# Martin's large-prime-power elimination step

This file formalizes the algebraic and finite-combinatorial content of Lemma 12
in Greg Martin's *Denser Egyptian fractions*.  Its algebraic core exposes one
bounded-surjectivity interface: every residue modulo the prime power `q` is a
sum of inverses of at most `martinBlockBound x q` members of the candidate set.
The final theorems instantiate that interface from the proved dense, scaled
dispersion, and published sufficiently-large-modulus subset-sum results.

The main theorem then selects the corresponding denominator block, proves its
interval, cardinality, and largest-prime-power properties, clears denominators,
and converts the inverse congruence into strict descent of the largest exact
prime-power part of the reduced residual denominator.
-/

namespace Erdos285.Lemma12

open Filter Finset
open scoped BigOperators
open Erdos285.PrimePowers

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A number is a product of four pairwise distinct primes.  Martin obtains the
candidate multipliers from four separated prime intervals, which in particular
implies this predicate and injectivity of the resulting products. -/
def IsFourPrimeProduct (m : ℕ) : Prop :=
  ∃ P : Finset ℕ, P.card = 4 ∧
    (∀ p ∈ P, p.Prime) ∧ m = P.prod id

lemma IsFourPrimeProduct.pos {m : ℕ} (hm : IsFourPrimeProduct m) : 0 < m := by
  obtain ⟨P, -, hP, rfl⟩ := hm
  exact Finset.prod_pos fun p hp ↦ (hP p hp).pos

lemma IsFourPrimeProduct.ne_zero {m : ℕ} (hm : IsFourPrimeProduct m) : m ≠ 0 :=
  hm.pos.ne'

/-- The denominators corresponding to a set of auxiliary multipliers. -/
def denominatorBlock (q : ℕ) (K : Finset ℕ) : Finset ℕ :=
  K.image fun m ↦ q * m

@[simp] lemma mem_denominatorBlock {q u : ℕ} {K : Finset ℕ} :
    u ∈ denominatorBlock q K ↔ ∃ m ∈ K, q * m = u := by
  simp [denominatorBlock]

lemma card_denominatorBlock {q : ℕ} (hq : q ≠ 0) (K : Finset ℕ) :
    (denominatorBlock q K).card = K.card := by
  rw [denominatorBlock, Finset.card_image_iff]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) hab

lemma rec_sum_denominatorBlock {q : ℕ} (hq : q ≠ 0) (K : Finset ℕ) :
    UnitFractions.rec_sum (denominatorBlock q K) =
      ∑ m ∈ K, (1 : ℚ) / (q * m : ℕ) := by
  rw [denominatorBlock, UnitFractions.rec_sum, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) hab

/-- The common numerator of `∑ m⁻¹` over the least common multiple of all
members of `K`. -/
def commonReciprocalNumerator (K : Finset ℕ) : ℕ :=
  ∑ m ∈ K, K.lcm id / m

lemma rec_sum_eq_commonReciprocalNumerator_div_lcm
    {K : Finset ℕ} (hK0 : ∀ m ∈ K, m ≠ 0) :
    UnitFractions.rec_sum K =
      (commonReciprocalNumerator K : ℚ) / (K.lcm id : ℕ) := by
  have hlcm0 : K.lcm id ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    exact hK0
  rw [UnitFractions.rec_sum, commonReciprocalNumerator, Nat.cast_sum,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  have hmlcm : m ∣ K.lcm id := Finset.dvd_lcm hm
  have hm0 := hK0 m hm
  field_simp [hm0, hlcm0]
  exact_mod_cast (show K.lcm id = m * (K.lcm id / m) by
    rw [mul_comm, Nat.div_mul_cancel hmlcm])

/-- Martin's numerical upper bound for the selected correction block.  `rpow`
is used for the exponent `2/3`. -/
def martinBlockBound (x q : ℕ) : ℕ :=
  ⌊200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) * (Real.log x) ^ 3⌋₊

lemma martinBlockBound_cast_le {x q : ℕ} (hx : 1 ≤ x) :
    (martinBlockBound x q : ℝ) ≤
      200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) * (Real.log x) ^ 3 := by
  apply Nat.floor_le
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx)
  positivity

lemma card_le_martin_real_bound {x q : ℕ} {U : Finset ℕ}
    (hx : 1 ≤ x) (hU : U.card ≤ martinBlockBound x q) :
    (U.card : ℝ) ≤
      200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) * (Real.log x) ^ 3 := by
  exact (by exact_mod_cast hU : (U.card : ℝ) ≤ martinBlockBound x q) |>.trans
    (martinBlockBound_cast_le hx)

/-- The large-prime-power range in Lemma 12. -/
def InEliminationRange (x q : ℕ) : Prop :=
  (x : ℝ) ^ ((1 : ℝ) / 5) ≤ q ∧
    (q : ℝ) ≤ x * (Real.log x) ^ (-22 : ℝ)

/-- The lower endpoint `x^(1/5) ≤ q` is exactly what is needed to put
the fourth-root candidate-prime scale below `q`. -/
lemma fourthRoot_div_le_of_fifthRoot_le {x q : ℕ} (hq : 0 < q)
    (h : (x : ℝ) ^ ((1 : ℝ) / 5) ≤ q) :
    Erdos285.Lemma12Candidates.fourthRoot ((x : ℝ) / q) ≤ (q : ℝ) := by
  have hrootpow : ((x : ℝ) ^ ((1 : ℝ) / 5)) ^ (5 : ℕ) = (x : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg x)]
    norm_num
  have hxq5 : (x : ℝ) ≤ (q : ℝ) ^ (5 : ℕ) := by
    rw [← hrootpow]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg x) _) h 5
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hxdiv : (x : ℝ) / q ≤ (q : ℝ) ^ (4 : ℕ) := by
    rw [div_le_iff₀ hqR]
    calc
      (x : ℝ) ≤ (q : ℝ) ^ (5 : ℕ) := hxq5
      _ = (q : ℝ) ^ (4 : ℕ) * q := by ring
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hqR.le
  rw [Erdos285.Lemma12Candidates.fourthRoot_pow_four (by positivity)]
  exact hxdiv

/-- The exact inverse-subset interface supplied by Martin's Lemmas 10 and 11.
The chosen subset is indexed by distinct auxiliary multipliers, even if their
inverse residues coincide. -/
def BoundedInverseSubsetSurjective (q C : ℕ) (M : Finset ℕ) : Prop :=
  ∀ a : ZMod q, ∃ K : Finset ℕ,
    K ⊆ M ∧ K.card ≤ C ∧
      K.sum (fun m ↦ ((m : ZMod q)⁻¹)) = a

/-- The denominator used after removing the exact `q`-part from `r.den` and
combining it with the selected auxiliary denominators.  The outer LCM is
essential: multiplying would artificially increase exponents of primes shared
by the two inputs. -/
def residualAuxiliaryLcm (r : ℚ) (q : ℕ) (K : Finset ℕ) : ℕ :=
  Nat.lcm (r.den / q) (K.lcm id)

/-- The integer numerator obtained over
`q * lcm (r.den / q) (lcm K)`. -/
def clearedNumerator (r : ℚ) (q : ℕ) (K : Finset ℕ) : ℤ :=
  r.num * (residualAuxiliaryLcm r q K / (r.den / q) : ℕ) -
    ((residualAuxiliaryLcm r q K / K.lcm id) *
      commonReciprocalNumerator K : ℕ)

/-- The LCM of a selected subfamily divides the LCM of the full candidate
family. -/
lemma lcm_dvd_lcm_of_subset {K M : Finset ℕ} (hKM : K ⊆ M) :
    K.lcm id ∣ M.lcm id :=
  Finset.lcm_mono hKM

/-- A prime power dividing an LCM already divides one of its two inputs.
This is stronger than the corresponding statement for arbitrary divisors.
The factorization-LCM decomposition avoids any multiplication of repeated
prime factors. -/
lemma isPrimePow_dvd_lcm {ℓ a b : ℕ}
    (hℓ : IsPrimePow ℓ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ℓ ∣ Nat.lcm a b) : ℓ ∣ a ∨ ℓ ∣ b := by
  have hsplit := Nat.factorizationLCMLeft_mul_factorizationLCMRight ha hb
  have hdiv' : ℓ ∣ Nat.factorizationLCMLeft a b *
      Nat.factorizationLCMRight a b := by
    rwa [hsplit]
  rw [Nat.Coprime.isPrimePow_dvd_mul
    (Nat.coprime_factorizationLCMLeft_factorizationLCMRight a b) hℓ] at hdiv'
  exact hdiv'.imp
    (fun h ↦ h.trans (Nat.factorizationLCMLeft_dvd_left a b))
    (fun h ↦ h.trans (Nat.factorizationLCMRight_dvd_right a b))

/-- A prime power dividing the LCM of a nonzero finite family divides one of
the family members. -/
lemma isPrimePow_dvd_finsetLcm {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → ℕ} {ℓ : ℕ}
    (hℓ : IsPrimePow ℓ) (hf : ∀ i ∈ s, f i ≠ 0)
    (hdiv : ℓ ∣ s.lcm f) : ∃ i ∈ s, ℓ ∣ f i := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.lcm_empty] at hdiv
      exact (hℓ.ne_one (Nat.dvd_one.mp hdiv)).elim
  | @insert a s ha ih =>
      rw [Finset.lcm_insert] at hdiv
      have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self _ _)
      have hfs : ∀ i ∈ s, f i ≠ 0 :=
        fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hlcms : s.lcm f ≠ 0 := by
        rw [Finset.lcm_ne_zero_iff]
        exact hfs
      rcases isPrimePow_dvd_lcm hℓ hfa hlcms hdiv with hleft | hright
      · exact ⟨a, Finset.mem_insert_self _ _, hleft⟩
      · obtain ⟨i, hi, hidiv⟩ := ih hfs hright
        exact ⟨i, Finset.mem_insert_of_mem hi, hidiv⟩

/-- The exact LCM bound needed by Lemma 12 follows from two transparent
inputs: all prime powers in the old cofactor are below `q`, and every
candidate is squarefree with all its prime factors below `q`. -/
lemma auxiliaryLcm_primePower_lt
    {r : ℚ} {q : ℕ} {M : Finset ℕ}
    (hqpart : q ∈ primePowerParts r.den)
    (hcofactor : ∀ ℓ : ℕ, IsPrimePow ℓ → ℓ ∣ r.den / q → ℓ < q)
    (hM0 : ∀ m ∈ M, m ≠ 0)
    (hsquarefree : ∀ m ∈ M, Squarefree m)
    (hprime_lt : ∀ m ∈ M, ∀ p : ℕ, p.Prime → p ∣ m → p < q) :
    ∀ ℓ : ℕ, IsPrimePow ℓ →
      ℓ ∣ residualAuxiliaryLcm r q M → ℓ < q := by
  intro ℓ hℓ hℓaux
  have hqspec := (mem_primePowerParts r.den_ne_zero).mp hqpart
  have hb0 : r.den / q ≠ 0 := by
    exact (Nat.div_pos (Nat.le_of_dvd r.den_pos hqspec.2.1)
      hqspec.1.pos).ne'
  have hL0 : M.lcm id ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    exact hM0
  rcases isPrimePow_dvd_lcm hℓ hb0 hL0 hℓaux with hℓb | hℓL
  · exact hcofactor ℓ hℓ hℓb
  · obtain ⟨m, hm, hℓm⟩ :=
      isPrimePow_dvd_finsetLcm hℓ hM0 hℓL
    have hℓsquarefree : Squarefree ℓ :=
      (hsquarefree m hm).squarefree_of_dvd hℓm
    have hℓprime : ℓ.Prime :=
      Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hℓsquarefree, hℓ⟩
    exact hprime_lt m hm ℓ hℓprime hℓm

/-- A common-denominator identity for the selected block. -/
lemma residual_eq_clearedFraction
    {r : ℚ} {q : ℕ} {K : Finset ℕ}
    (hqden : q ∣ r.den) (hq0 : q ≠ 0)
    (hK0 : ∀ m ∈ K, m ≠ 0) :
    r - UnitFractions.rec_sum (denominatorBlock q K) =
      (clearedNumerator r q K : ℚ) /
        (q * residualAuxiliaryLcm r q K : ℕ) := by
  have hlcm0 : K.lcm id ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    exact hK0
  have hdeneq : q * (r.den / q) = r.den := Nat.mul_div_cancel' hqden
  have hblock : UnitFractions.rec_sum (denominatorBlock q K) =
      (commonReciprocalNumerator K : ℚ) / (q * K.lcm id : ℕ) := by
    rw [rec_sum_denominatorBlock hq0]
    calc
      (∑ m ∈ K, (1 : ℚ) / (q * m : ℕ)) =
          (1 : ℚ) / q * UnitFractions.rec_sum K := by
        rw [UnitFractions.rec_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        have hm0 := hK0 m hm
        push_cast
        field_simp [hq0, hm0]
      _ = (commonReciprocalNumerator K : ℚ) / (q * K.lcm id : ℕ) := by
        rw [rec_sum_eq_commonReciprocalNumerator_div_lcm hK0]
        push_cast
        field_simp [hq0, hlcm0]
  have hdeneqQ : (r.den : ℚ) = (q : ℚ) * ((r.den / q : ℕ) : ℚ) := by
    exact_mod_cast hdeneq.symm
  have hb0 : r.den / q ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd r.den_pos hqden)
      (Nat.pos_of_ne_zero hq0))
  have hD0 : residualAuxiliaryLcm r q K ≠ 0 := by
    exact Nat.lcm_ne_zero hb0 hlcm0
  have hbD : r.den / q ∣ residualAuxiliaryLcm r q K :=
    Nat.dvd_lcm_left _ _
  have hLD : K.lcm id ∣ residualAuxiliaryLcm r q K :=
    Nat.dvd_lcm_right _ _
  rw [hblock]
  conv_lhs =>
    lhs
    rw [← r.num_div_den]
  simp only [clearedNumerator, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Nat.cast_mul]
  change
    (r.num : ℚ) / (r.den : ℚ) -
        (commonReciprocalNumerator K : ℚ) /
          ((q : ℚ) * (K.lcm id : ℕ)) =
      ((r.num : ℚ) *
            (residualAuxiliaryLcm r q K / (r.den / q) : ℕ) -
          (residualAuxiliaryLcm r q K / K.lcm id : ℕ) *
            (commonReciprocalNumerator K : ℕ)) /
        ((q : ℚ) * residualAuxiliaryLcm r q K)
  rw [hdeneqQ]
  field_simp [hq0, hb0, hlcm0, hD0]
  have hDbQ :
      ((residualAuxiliaryLcm r q K / (r.den / q) : ℕ) : ℚ) *
          (r.den / q : ℕ) = residualAuxiliaryLcm r q K := by
    exact_mod_cast Nat.div_mul_cancel hbD
  have hDLQ :
      ((residualAuxiliaryLcm r q K / K.lcm id : ℕ) : ℚ) *
          (K.lcm id : ℕ) = residualAuxiliaryLcm r q K := by
    exact_mod_cast Nat.div_mul_cancel hLD
  have hfirst :
      (r.num : ℚ) * (K.lcm id : ℕ) * residualAuxiliaryLcm r q K =
        (r.den / q : ℕ) * (K.lcm id : ℕ) *
          ((r.num : ℚ) *
            (residualAuxiliaryLcm r q K / (r.den / q) : ℕ)) := by
    rw [← hDbQ]
    ring
  have hsecond :
      (r.den / q : ℕ) * (commonReciprocalNumerator K : ℕ) *
          residualAuxiliaryLcm r q K =
        (r.den / q : ℕ) * (K.lcm id : ℕ) *
          ((commonReciprocalNumerator K : ℚ) *
            (residualAuxiliaryLcm r q K / K.lcm id : ℕ)) := by
    rw [← hDLQ]
    ring
  rw [sub_mul, hfirst, hsecond]
  ring

/-- In `ZMod q`, the common reciprocal numerator is the LCM of `K` times the
sum of the inverse residues. -/
lemma commonReciprocalNumerator_cast
    {q : ℕ} [NeZero q] {K : Finset ℕ}
    (hcop : ∀ m ∈ K, Nat.Coprime m q) :
    (commonReciprocalNumerator K : ZMod q) =
      ((K.lcm id : ℕ) : ZMod q) * K.sum (fun m ↦ ((m : ZMod q)⁻¹)) := by
  rw [commonReciprocalNumerator, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmlcm : m ∣ K.lcm id := Finset.dvd_lcm hm
  have hunit : IsUnit (m : ZMod q) :=
    (ZMod.isUnit_iff_coprime m q).mpr (hcop m hm)
  have hcastLcm : (m : ZMod q) * ((K.lcm id / m : ℕ) : ZMod q) =
      ((K.lcm id : ℕ) : ZMod q) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hmlcm]
  calc
    ((K.lcm id / m : ℕ) : ZMod q) =
        (m : ZMod q)⁻¹ * ((K.lcm id : ℕ) : ZMod q) := by
      calc
        ((K.lcm id / m : ℕ) : ZMod q) =
            ((m : ZMod q)⁻¹ * (m : ZMod q)) *
              ((K.lcm id / m : ℕ) : ZMod q) := by
                rw [ZMod.inv_mul_of_unit _ hunit, one_mul]
        _ = (m : ZMod q)⁻¹ *
              ((m : ZMod q) * ((K.lcm id / m : ℕ) : ZMod q)) := by ring
        _ = (m : ZMod q)⁻¹ * ((K.lcm id : ℕ) : ZMod q) := by rw [hcastLcm]
    _ = ((K.lcm id : ℕ) : ZMod q) * (m : ZMod q)⁻¹ := by ac_rfl

/-- Cast an exact natural quotient into `ZMod q` by multiplying with the
inverse of its (unit) divisor. -/
lemma natCast_div_eq_mul_inv {q a d : ℕ} [NeZero q]
    (hda : d ∣ a) (hdunit : IsUnit (d : ZMod q)) :
    ((a / d : ℕ) : ZMod q) = (a : ZMod q) * (d : ZMod q)⁻¹ := by
  have hcast : (d : ZMod q) * ((a / d : ℕ) : ZMod q) = (a : ZMod q) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hda]
  calc
    ((a / d : ℕ) : ZMod q) =
        (d : ZMod q)⁻¹ * ((d : ZMod q) * ((a / d : ℕ) : ZMod q)) := by
      rw [← mul_assoc, ZMod.inv_mul_of_unit _ hdunit, one_mul]
    _ = (d : ZMod q)⁻¹ * (a : ZMod q) := by rw [hcast]
    _ = (a : ZMod q) * (d : ZMod q)⁻¹ := by ac_rfl

/-- The inverse congruence selected by Lemma 11 makes the cleared residual
numerator divisible by `q`. -/
lemma clearedNumerator_dvd_of_inverseCongruence
    {r : ℚ} {q : ℕ} {K : Finset ℕ}
    (hqpart : q ∈ primePowerParts r.den)
    (hcop : ∀ m ∈ K, Nat.Coprime m q)
    (hcong : K.sum (fun m ↦ ((m : ZMod q)⁻¹)) =
      (r.num : ZMod q) * ((r.den / q : ℕ) : ZMod q)⁻¹) :
    (q : ℤ) ∣ clearedNumerator r q K := by
  have hqspec := (mem_primePowerParts r.den_ne_zero).mp hqpart
  let _ : NeZero q := ⟨hqspec.1.ne_zero⟩
  let b : ℕ := r.den / q
  let L : ℕ := K.lcm id
  let D : ℕ := residualAuxiliaryLcm r q K
  have hbunit : IsUnit (b : ZMod q) :=
    (ZMod.isUnit_iff_coprime (r.den / q) q).mpr hqspec.2.2.symm
  have hLcop : Nat.Coprime L q := by
    apply Nat.Coprime.of_dvd_left
        (show K.lcm id ∣ K.prod id by
          apply Finset.lcm_dvd
          intro m hm
          exact Finset.dvd_prod_of_mem id hm)
    rw [Nat.coprime_prod_left_iff]
    exact hcop
  have hLunit : IsUnit (L : ZMod q) :=
    (ZMod.isUnit_iff_coprime L q).mpr hLcop
  have hbD : b ∣ D := Nat.dvd_lcm_left _ _
  have hLD : L ∣ D := Nat.dvd_lcm_right _ _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [clearedNumerator, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Nat.cast_mul]
  change
    (r.num : ZMod q) * ((D / b : ℕ) : ZMod q) -
      ((D / L : ℕ) : ZMod q) * (commonReciprocalNumerator K : ZMod q) = 0
  rw [natCast_div_eq_mul_inv hbD hbunit,
    natCast_div_eq_mul_inv hLD hLunit,
    commonReciprocalNumerator_cast hcop, hcong]
  calc
    (r.num : ZMod q) * ((D : ZMod q) * (b : ZMod q)⁻¹) -
          ((D : ZMod q) * (L : ZMod q)⁻¹) *
            (((L : ZMod q) *
              ((r.num : ZMod q) * (b : ZMod q)⁻¹))) =
        (D : ZMod q) * (r.num : ZMod q) * (b : ZMod q)⁻¹ *
          (1 - (L : ZMod q)⁻¹ * (L : ZMod q)) := by ring
    _ = 0 := by
      rw [ZMod.inv_mul_of_unit _ hLunit]
      ring

/-- The reduced denominator after the congruence step divides the exact LCM of
the old denominator with its `q`-part removed and the selected auxiliaries. -/
lemma residual_den_dvd_auxiliaryLcm
    {r : ℚ} {q : ℕ} {K : Finset ℕ}
    (hqpart : q ∈ primePowerParts r.den)
    (hK0 : ∀ m ∈ K, m ≠ 0)
    (hcop : ∀ m ∈ K, Nat.Coprime m q)
    (hcong : K.sum (fun m ↦ ((m : ZMod q)⁻¹)) =
      (r.num : ZMod q) * ((r.den / q : ℕ) : ZMod q)⁻¹) :
    (r - UnitFractions.rec_sum (denominatorBlock q K)).den ∣
      residualAuxiliaryLcm r q K := by
  have hqspec := (mem_primePowerParts r.den_ne_zero).mp hqpart
  have hcleared := residual_eq_clearedFraction hqspec.2.1 hqspec.1.ne_zero hK0
  obtain ⟨z, hz⟩ := clearedNumerator_dvd_of_inverseCongruence hqpart hcop hcong
  have hq0Z : (q : ℤ) ≠ 0 := by exact_mod_cast hqspec.1.ne_zero
  have haux0 : (residualAuxiliaryLcm r q K : ℤ) ≠ 0 := by
    have hbpos : 0 < r.den / q :=
      Nat.div_pos (Nat.le_of_dvd r.den_pos hqspec.2.1) hqspec.1.pos
    have hL0 : K.lcm id ≠ 0 := by
      rw [Finset.lcm_ne_zero_iff]
      exact hK0
    exact_mod_cast Nat.lcm_ne_zero hbpos.ne' hL0
  have heq : r - UnitFractions.rec_sum (denominatorBlock q K) =
      (z : ℚ) / (residualAuxiliaryLcm r q K : ℕ) := by
    rw [hcleared, hz]
    push_cast
    field_simp [hqspec.1.ne_zero]
  have hdenZ :
      ((r - UnitFractions.rec_sum (denominatorBlock q K)).den : ℤ) ∣
        (residualAuxiliaryLcm r q K : ℤ) := by
    have := Rat.den_dvd z (residualAuxiliaryLcm r q K : ℤ)
    have hrat : Rat.divInt z (residualAuxiliaryLcm r q K : ℤ) =
        r - UnitFractions.rec_sum (denominatorBlock q K) := by
      rw [Rat.divInt_eq_div]
      exact heq.symm
    rw [hrat] at this
    exact this
  exact_mod_cast hdenZ

/-- If every prime power dividing the ambient auxiliary LCM is below `q`,
then denominator divisibility gives strict largest-prime-power descent. -/
lemma largestPrimePowerPart_residual_lt
    {r : ℚ} {q : ℕ} {K M : Finset ℕ}
    (hqpart : q ∈ primePowerParts r.den)
    (hKM : K ⊆ M)
    (hden : (r - UnitFractions.rec_sum (denominatorBlock q K)).den ∣
      residualAuxiliaryLcm r q K)
    (hbound : ∀ ℓ : ℕ, IsPrimePow ℓ →
      ℓ ∣ residualAuxiliaryLcm r q M → ℓ < q) :
    largestPrimePowerPart
        (r - UnitFractions.rec_sum (denominatorBlock q K)).den < q := by
  let s : ℚ := r - UnitFractions.rec_sum (denominatorBlock q K)
  have hqspec := (mem_primePowerParts r.den_ne_zero).mp hqpart
  have haux : residualAuxiliaryLcm r q K ∣ residualAuxiliaryLcm r q M := by
    exact lcm_dvd_lcm dvd_rfl (lcm_dvd_lcm_of_subset hKM)
  by_cases hs : 2 ≤ s.den
  · have hmem : largestPrimePowerPart s.den ∈ primePowerParts s.den :=
      largestPrimePowerPart_mem hs
    have hspec := (mem_primePowerParts s.den_ne_zero).mp hmem
    exact hbound _ hspec.1 (hspec.2.1.trans (hden.trans haux))
  · have hsmall : s.den < 2 := Nat.lt_of_not_ge hs
    have hempty : primePowerParts s.den = ∅ := primePowerParts_empty_iff.mpr hsmall
    have hzero : largestPrimePowerPart s.den = 0 := by
      rw [largestPrimePowerPart, hempty]
      simp
    change largestPrimePowerPart s.den < q
    rw [hzero]
    exact hqspec.1.pos

/-- The finite candidate data used after the analytic prime-interval and
dispersion estimates have been discharged. -/
structure CandidateData (ξ : ℝ) (x q : ℕ) (r : ℚ) (M : Finset ℕ) : Prop where
  range : InEliminationRange x q
  q_part : q ∈ primePowerParts r.den
  four_primes : ∀ m ∈ M, IsFourPrimeProduct m
  coprime : ∀ m ∈ M, Nat.Coprime m q
  interval : ∀ m ∈ M,
    ξ * x ≤ (q * m : ℕ) ∧ (q * m : ℕ) ≤ x
  largest_part : ∀ m ∈ M, largestPrimePowerPart (q * m) = q
  auxiliary_bound : ∀ ℓ : ℕ, IsPrimePow ℓ →
    ℓ ∣ residualAuxiliaryLcm r q M → ℓ < q

/-- A four-prime-product-away witness in the dispersion module supplies the
local product predicate used by the elimination algebra. -/
lemma isFourPrimeProduct_of_isKPrimeProductAway
    {q m : ℕ} (hm : Erdos285.Dispersion.IsKPrimeProductAway 4 q m) :
    IsFourPrimeProduct m := by
  obtain ⟨P, hPcard, hP, hprod⟩ := hm
  exact ⟨P, hPcard, fun p hp ↦ (hP p hp).1, hprod⟩

/-- Build all of `CandidateData` from the actual four-prime family.  In
particular, the `auxiliary_bound` field is proved for the exact double LCM,
using the old-cofactor hypothesis and the squarefree candidate-LCM theorem. -/
theorem candidateData_of_rawCandidateFamily
    {ξ : ℝ} {x p ν : ℕ} {r : ℚ} {M : Finset ℕ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hx : 0 < x)
    (hp : p.Prime) (hν : 0 < ν)
    (hrange : InEliminationRange x (p ^ ν))
    (hqpart : p ^ ν ∈ primePowerParts r.den)
    (hM : M ⊆ Erdos285.Lemma12Candidates.rawCandidates p
      (Erdos285.Lemma12Candidates.fourthRoot ξ)
      (Erdos285.Lemma12Candidates.fourthRoot
        ((x : ℝ) / (p ^ ν : ℕ))))
    (hcofactor : ∀ ℓ : ℕ, IsPrimePow ℓ →
      ℓ ∣ r.den / (p ^ ν) → ℓ < p ^ ν) :
    CandidateData ξ x (p ^ ν) r M := by
  let c : ℝ := Erdos285.Lemma12Candidates.fourthRoot ξ
  let t : ℝ := Erdos285.Lemma12Candidates.fourthRoot
    ((x : ℝ) / (p ^ ν : ℕ))
  have hc : 0 ≤ c := Erdos285.Lemma12Candidates.fourthRoot_nonneg ξ
  have ht : 0 ≤ t := Erdos285.Lemma12Candidates.fourthRoot_nonneg _
  have htq : t ≤ ((p ^ ν : ℕ) : ℝ) := by
    exact fourthRoot_div_le_of_fifthRoot_le (pow_pos hp.pos ν) hrange.1
  refine ⟨hrange, hqpart, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact isFourPrimeProduct_of_isKPrimeProductAway (q := p ^ ν)
      (Erdos285.Lemma12Candidates.rawCandidate_isKPrimeProductAway
        (ν := ν) hp (hM hm))
  · intro m hm
    exact Erdos285.Lemma12Candidates.rawCandidate_coprime_primePow hp (hM hm)
  · intro m hm
    have hprops := Erdos285.Lemma12Candidates.rawCandidate_elimination_properties
      hξ hξ1 hx hp (hM hm)
    exact ⟨hprops.2.2.1.le, by exact_mod_cast hprops.2.2.2.1⟩
  · intro m hm
    exact Erdos285.Lemma12Candidates.largestPrimePowerPart_primePow_mul_rawCandidate
      hp hν hc ht (by simpa [t] using htq) (by simpa [c, t] using hM hm)
  · intro ℓ hℓ hℓdvd
    have hqspec := (mem_primePowerParts r.den_ne_zero).mp hqpart
    have hb0 : r.den / (p ^ ν) ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd r.den_pos hqspec.2.1) hqspec.1.pos).ne'
    apply Erdos285.Lemma12Candidates.primePower_dvd_lcm_candidateFamily_lt
      hb0 hc ht (by simpa [t] using htq) (by simpa [c, t] using hM)
      hcofactor hℓ
    simpa [residualAuxiliaryLcm] using hℓdvd

/-- The algebraic/finite form of Martin's Lemma 12.

The analytic Lemmas 10 and 11 are used only through `hsurj`.  All remaining
conclusions of Lemma 12 are constructed here. -/
theorem largePrimePowerElimination
    {ξ : ℝ} {x q : ℕ} {r : ℚ} {M : Finset ℕ}
    (hdata : CandidateData ξ x q r M)
    (hsurj : BoundedInverseSubsetSurjective q (martinBlockBound x q) M) :
    ∃ U : Finset ℕ,
      U.card ≤ martinBlockBound x q ∧
      (∀ u ∈ U, ξ * x ≤ (u : ℝ) ∧ (u : ℝ) ≤ x) ∧
      (∀ u ∈ U, largestPrimePowerPart u = q) ∧
      Nat.Coprime (r - UnitFractions.rec_sum U).den q ∧
      largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q := by
  have hqspec := (mem_primePowerParts r.den_ne_zero).mp hdata.q_part
  let _ : NeZero q := ⟨hqspec.1.ne_zero⟩
  let target : ZMod q :=
    (r.num : ZMod q) * ((r.den / q : ℕ) : ZMod q)⁻¹
  obtain ⟨K, hKM, hKcard, hKsum⟩ := hsurj target
  let U := denominatorBlock q K
  have hK0 : ∀ m ∈ K, m ≠ 0 := by
    intro m hm
    exact (hdata.four_primes m (hKM hm)).ne_zero
  have hKcop : ∀ m ∈ K, Nat.Coprime m q :=
    fun m hm ↦ hdata.coprime m (hKM hm)
  have hden : (r - UnitFractions.rec_sum U).den ∣
      residualAuxiliaryLcm r q K := by
    exact residual_den_dvd_auxiliaryLcm hdata.q_part hK0 hKcop hKsum
  have hKLCoprime : Nat.Coprime (K.lcm id) q := by
    apply Nat.Coprime.of_dvd_left
        (show K.lcm id ∣ K.prod id by
          apply Finset.lcm_dvd
          intro m hm
          exact Finset.dvd_prod_of_mem id hm)
    rw [Nat.coprime_prod_left_iff]
    exact hKcop
  have hauxCoprime : Nat.Coprime (residualAuxiliaryLcm r q K) q := by
    apply Nat.Coprime.of_dvd_left
        (show residualAuxiliaryLcm r q K ∣ (r.den / q) * K.lcm id by
          exact Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
    exact Nat.Coprime.mul_left hqspec.2.2.symm hKLCoprime
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_denominatorBlock hqspec.1.ne_zero]
    exact hKcard
  · intro u hu
    obtain ⟨m, hm, rfl⟩ := mem_denominatorBlock.mp hu
    refine ⟨(hdata.interval m (hKM hm)).1, ?_⟩
    exact_mod_cast (hdata.interval m (hKM hm)).2
  · intro u hu
    obtain ⟨m, hm, rfl⟩ := mem_denominatorBlock.mp hu
    exact hdata.largest_part m (hKM hm)
  · exact Nat.Coprime.of_dvd_left hden hauxCoprime
  · exact largestPrimePowerPart_residual_lt hdata.q_part hKM hden hdata.auxiliary_bound

/-- The same result with Martin's displayed real cardinality estimate rather
than its (stronger) floored natural-number form. -/
theorem largePrimePowerElimination_realCardBound
    {ξ : ℝ} {x q : ℕ} {r : ℚ} {M : Finset ℕ}
    (hx : 1 ≤ x)
    (hdata : CandidateData ξ x q r M)
    (hsurj : BoundedInverseSubsetSurjective q (martinBlockBound x q) M) :
    ∃ U : Finset ℕ,
      (U.card : ℝ) ≤
        200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) * (Real.log x) ^ 3 ∧
      (∀ u ∈ U, ξ * x ≤ (u : ℝ) ∧ (u : ℝ) ≤ x) ∧
      (∀ u ∈ U, largestPrimePowerPart u = q) ∧
      Nat.Coprime (r - UnitFractions.rec_sum U).den q ∧
      largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q := by
  obtain ⟨U, hcard, hinterval, hpart, hcop, hdescent⟩ :=
    largePrimePowerElimination hdata hsurj
  exact ⟨U, card_le_martin_real_bound hx hcard, hinterval, hpart, hcop, hdescent⟩

/-- Martin's sparse modular-dispersion branch, connected directly to the
elimination theorem.  Thus this public entry point consumes the proved
Fourier/dispersion estimate rather than assuming subset-sum surjectivity as
an oracle. -/
theorem largePrimePowerElimination_of_scaledDispersion
    {ξ : ℝ} {x q : ℕ} {r : ℚ} {M : Finset ℕ}
    (hdata : CandidateData ξ x q r M)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hcard : M.card ≤ martinBlockBound x q)
    (hdisp : ∀ h : ZMod q, h ≠ 0 →
      M.card ≤ 2 *
        (M.filter fun m ↦ delta ≤
          (Erdos285.SubsetSum.characterDistance q h m : ℝ) / q).card)
    (hdecay : 2 * Real.log q < delta ^ 2 * M.card) :
    ∃ U : Finset ℕ,
      U.card ≤ martinBlockBound x q ∧
      (∀ u ∈ U, ξ * x ≤ (u : ℝ) ∧ (u : ℝ) ≤ x) ∧
      (∀ u ∈ U, largestPrimePowerPart u = q) ∧
      Nat.Coprime (r - UnitFractions.rec_sum U).den q ∧
      largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q := by
  have hqspec := (mem_primePowerParts r.den_ne_zero).mp hdata.q_part
  let _ : NeZero q := ⟨hqspec.1.ne_zero⟩
  apply largePrimePowerElimination hdata
  intro a
  exact Erdos285.SubsetSum.bounded_inverse_subset_sum_of_scaled_dispersion
    hqspec.1.one_lt M delta hdelta hcard hdisp hdecay a

/-- The dense Cauchy--Davenport--Chowla branch, connected to the same
elimination conclusion. -/
theorem largePrimePowerElimination_of_denseCard
    {ξ : ℝ} {x q : ℕ} {r : ℚ} {M : Finset ℕ}
    (hdata : CandidateData ξ x q r M)
    (hdense : q ≤ M.card)
    (hcard : M.card ≤ martinBlockBound x q) :
    ∃ U : Finset ℕ,
      U.card ≤ martinBlockBound x q ∧
      (∀ u ∈ U, ξ * x ≤ (u : ℝ) ∧ (u : ℝ) ≤ x) ∧
      (∀ u ∈ U, largestPrimePowerPart u = q) ∧
      Nat.Coprime (r - UnitFractions.rec_sum U).den q ∧
      largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q := by
  have hqspec := (mem_primePowerParts r.den_ne_zero).mp hdata.q_part
  let _ : NeZero q := ⟨hqspec.1.ne_zero⟩
  apply largePrimePowerElimination hdata
  intro a
  exact Erdos285.SubsetSum.bounded_inverse_subset_sum_of_card M
    hdata.coprime hdense hcard a

/-- The fully proved Martin-Lemma-11 input, specialized to four-prime
candidates and fed into the elimination algebra.  This is the unconditional
"sufficiently large modulus" form of Lemma 12: no dispersion or subset-sum
surjectivity premise remains. -/
theorem eventually_largePrimePowerElimination_of_martinHypotheses :
    ∀ᶠ q : ℕ in atTop,
      ∀ (ξ : ℝ) (x : ℕ) (r : ℚ) (M : Finset ℕ) (B : ℝ),
        CandidateData ξ x q r M →
        M.card ≤ martinBlockBound x q →
        0 < B →
        Real.log q ^ (((4 - 1 : ℕ) : ℝ) / 2) /
            Real.log (Real.log q) ^ ((4 : ℝ) / 2) < B →
        200 *
            (B ^ (2 / 3 : ℝ) *
                Real.log q ^ (((2 * 4 + 1 : ℕ) : ℝ) / 3) /
              Real.log (Real.log q) ^ (((2 * 4 : ℕ) : ℝ) / 3)) <
          M.card →
        (∀ m ∈ M, (m : ℝ) < B ∧
          Erdos285.Dispersion.IsKPrimeProductAway 4 q m) →
        ∃ U : Finset ℕ,
          U.card ≤ martinBlockBound x q ∧
          (∀ u ∈ U, ξ * x ≤ (u : ℝ) ∧ (u : ℝ) ≤ x) ∧
          (∀ u ∈ U, largestPrimePowerPart u = q) ∧
          Nat.Coprime (r - UnitFractions.rec_sum U).den q ∧
          largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q := by
  filter_upwards
      [Erdos285.SubsetSum.eventually_bounded_inverse_subset_sum_of_martin_hypotheses
        4 (by norm_num)]
      with q hsubset
  intro ξ x r M B hdata hcard hB hBsource hcardSource hM
  apply largePrimePowerElimination hdata
  exact hsubset (martinBlockBound x q) B M hcard hB hBsource hcardSource hM

/-- Fully connected form for Martin's actual four-prime candidate family.
It combines candidate construction facts, the exact-LCM denominator descent,
and the proved sufficiently-large-modulus subset-sum theorem. -/
theorem eventually_largePrimePowerElimination_of_rawCandidateFamily :
    ∀ᶠ q : ℕ in atTop,
      ∀ (ξ : ℝ) (x p ν : ℕ) (r : ℚ) (M : Finset ℕ) (B : ℝ),
        q = p ^ ν →
        0 < ξ → ξ < 1 → 0 < x → p.Prime → 0 < ν →
        InEliminationRange x q →
        q ∈ primePowerParts r.den →
        M ⊆ Erdos285.Lemma12Candidates.rawCandidates p
          (Erdos285.Lemma12Candidates.fourthRoot ξ)
          (Erdos285.Lemma12Candidates.fourthRoot ((x : ℝ) / q)) →
        (∀ ℓ : ℕ, IsPrimePow ℓ → ℓ ∣ r.den / q → ℓ < q) →
        M.card ≤ martinBlockBound x q →
        0 < B →
        Real.log q ^ (((4 - 1 : ℕ) : ℝ) / 2) /
            Real.log (Real.log q) ^ ((4 : ℝ) / 2) < B →
        200 *
            (B ^ (2 / 3 : ℝ) *
                Real.log q ^ (((2 * 4 + 1 : ℕ) : ℝ) / 3) /
              Real.log (Real.log q) ^ (((2 * 4 : ℕ) : ℝ) / 3)) <
          M.card →
        (∀ m ∈ M, (m : ℝ) < B) →
        ∃ U : Finset ℕ,
          U.card ≤ martinBlockBound x q ∧
          (∀ u ∈ U, ξ * x ≤ (u : ℝ) ∧ (u : ℝ) ≤ x) ∧
          (∀ u ∈ U, largestPrimePowerPart u = q) ∧
          Nat.Coprime (r - UnitFractions.rec_sum U).den q ∧
          largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q := by
  filter_upwards
      [Erdos285.SubsetSum.eventually_bounded_inverse_subset_sum_of_martin_hypotheses
        4 (by norm_num)]
      with q hsubset
  intro ξ x p ν r M B hq hξ hξ1 hx hp hν hrange hqpart hM hcofactor
    hcard hB hBsource hcardSource hMupper
  subst q
  have hdata : CandidateData ξ x (p ^ ν) r M :=
    candidateData_of_rawCandidateFamily hξ hξ1 hx hp hν hrange hqpart hM hcofactor
  apply largePrimePowerElimination hdata
  apply hsubset (martinBlockBound x (p ^ ν)) B M hcard hB hBsource hcardSource
  intro m hm
  exact ⟨hMupper m hm,
    Erdos285.Lemma12Candidates.rawCandidate_isKPrimeProductAway
      (ν := ν) hp (hM hm)⟩

end

end Erdos285.Lemma12

#print axioms Erdos285.Lemma12.largePrimePowerElimination
#print axioms Erdos285.Lemma12.largePrimePowerElimination_realCardBound
#print axioms Erdos285.Lemma12.largePrimePowerElimination_of_scaledDispersion
#print axioms Erdos285.Lemma12.largePrimePowerElimination_of_denseCard
#print axioms Erdos285.Lemma12.eventually_largePrimePowerElimination_of_martinHypotheses
#print axioms Erdos285.Lemma12.eventually_largePrimePowerElimination_of_rawCandidateFamily
