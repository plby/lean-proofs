import ErdosProblems.Erdos67b.BCCApplication

/-!
# The acyclic Section 4 BCC parameter hierarchy

This file makes the elementary, post-Elliott parameter choices used by the
full-divisor BCC contradiction.  The conductor cutoff `Q` and the normalized
good-residue energy bound `B` are inputs.  In this order we choose

* a number `L` of selected power layers;
* a prefix cutoff `H` containing every selected `q`-power for `q ≤ Q`;
* an exponent `k` suppressing the explicit bad-residue term; and
* a Taylor cutoff `D ≥ 32 H²`.

In particular, `D` is chosen after `H`; there is no fixed separation exponent
hidden in this package.
-/

open Finset

namespace Erdos67b

noncomputable section

/-- The divisors selected for the full-divisor BCC argument: the first `L`
powers of the eventual character level `q`. -/
def section4SelectedQPowers (q L : ℕ) : Finset ℕ :=
  (Finset.range L).image fun i ↦ q ^ i

/-- Number of power layers.  The factor `16` leaves room both for the factor
`8q` in the BCC upper bound and for the restored bad-residue term. -/
def section4BCCLayerCount (Q : ℕ) (B : ℝ) : ℕ :=
  Nat.ceil (16 * (Q : ℝ) * (B + 1)) + 1

/-- A single prefix cutoff containing `2q^i` for every `q ≤ Q` and every
selected exponent `i < L`. -/
def section4BCCPrefixCutoff (Q L : ℕ) : ℕ :=
  2 * Q ^ L

/-- A natural upper bound for the numerator of the restored bad-residue
term, uniformly over all levels `q ≤ Q`. -/
def section4BCCBadMagnitude (Q H : ℕ) : ℕ :=
  (2 * H * Q) * (2 * H) ^ 2

/-- The BCC prime-power exponent, deliberately chosen after `H`. -/
def section4BCCExponent (Q L H : ℕ) : ℕ :=
  L + section4BCCBadMagnitude Q H + 1

/-- The Taylor scale, deliberately chosen after `H`. -/
def section4BCCTaylorCutoff (H : ℕ) : ℕ :=
  32 * H ^ 2

/-- All numerical data needed at the full-divisor BCC endpoint. -/
structure Section4BCCParameters (Q : ℕ) (B : ℝ) where
  L : ℕ
  H : ℕ
  k : ℕ
  D : ℕ
  two_le_Q : 2 ≤ Q
  B_nonneg : 0 ≤ B
  L_pos : 0 < L
  H_pos : 0 < H
  k_pos : 0 < k
  D_pos : 0 < D
  layers_large : 16 * (Q : ℝ) * (B + 1) < (L : ℝ)
  L_lt_k : L < k
  selected_pow_le : ∀ q i : ℕ, 2 ≤ q → q ≤ Q → i < L → 2 * q ^ i ≤ H
  badResidueTerm_lt_one : ∀ q : ℕ, 2 ≤ q → q ≤ Q →
    (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
        ((2 ^ k : ℕ) : ℝ)) * ((2 * H : ℕ) : ℝ) ^ 2 < 1
  taylorScale_le : 32 * H ^ 2 ≤ D

theorem card_section4SelectedQPowers {q L : ℕ} (hq : 2 ≤ q) :
    (section4SelectedQPowers q L).card = L := by
  rw [section4SelectedQPowers,
    Finset.card_image_of_injective _ (Nat.pow_right_injective hq)]
  simp

theorem primeFactors_card_le_self {q : ℕ} (hq : 0 < q) :
    q.primeFactors.card ≤ q := by
  have hsubset : q.primeFactors ⊆ Finset.Icc 1 q := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_Icc.mpr
      ⟨hpPrime.one_le, Nat.le_of_dvd hq (Nat.dvd_of_mem_primeFactors hp)⟩
  calc
    q.primeFactors.card ≤ (Finset.Icc 1 q).card :=
      Finset.card_le_card hsubset
    _ = q := by simp

/-- The canonical choices realize the acyclic BCC hierarchy. -/
theorem exists_section4BCCParameters (Q : ℕ) (B : ℝ)
    (hQ : 2 ≤ Q) (hB : 0 ≤ B) : Nonempty (Section4BCCParameters Q B) := by
  let L : ℕ := section4BCCLayerCount Q B
  let H : ℕ := section4BCCPrefixCutoff Q L
  let N : ℕ := section4BCCBadMagnitude Q H
  let k : ℕ := section4BCCExponent Q L H
  let D : ℕ := section4BCCTaylorCutoff H
  have hLlarge : 16 * (Q : ℝ) * (B + 1) < (L : ℝ) := by
    have hceil :
        16 * (Q : ℝ) * (B + 1) ≤
          (Nat.ceil (16 * (Q : ℝ) * (B + 1)) : ℝ) :=
      Nat.le_ceil _
    dsimp only [L, section4BCCLayerCount]
    push_cast
    linarith
  have hLpos : 0 < L := by
    dsimp only [L, section4BCCLayerCount]
    omega
  have hHpos : 0 < H := by
    dsimp only [H, section4BCCPrefixCutoff]
    exact Nat.mul_pos (by norm_num) (pow_pos (by omega) _)
  have hNpos : 0 < N := by
    dsimp only [N, section4BCCBadMagnitude]
    positivity
  have hkdef : k = L + N + 1 := by
    simp only [k, section4BCCExponent, N]
  have hkpos : 0 < k := by
    rw [hkdef]
    omega
  have hLk : L < k := by
    rw [hkdef]
    omega
  have hDpos : 0 < D := by
    dsimp only [D, section4BCCTaylorCutoff]
    positivity
  have hpowers : ∀ q i : ℕ, 2 ≤ q → q ≤ Q → i < L → 2 * q ^ i ≤ H := by
    intro q i hq hqQ hiL
    have hbase : q ^ i ≤ Q ^ i := Nat.pow_le_pow_left hqQ i
    have hexp : Q ^ i ≤ Q ^ L :=
      Nat.pow_le_pow_right (by omega) hiL.le
    dsimp only [H, section4BCCPrefixCutoff]
    exact Nat.mul_le_mul_left 2 (hbase.trans hexp)
  have hNtwo : N < 2 ^ k := by
    calc
      N < 2 ^ N := N.lt_two_pow_self
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by rw [hkdef]; omega)
  have hbad : ∀ q : ℕ, 2 ≤ q → q ≤ Q →
      (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
          ((2 ^ k : ℕ) : ℝ)) * ((2 * H : ℕ) : ℝ) ^ 2 < 1 := by
    intro q hq hqQ
    have homega : q.primeFactors.card ≤ Q :=
      (primeFactors_card_le_self (by omega : 0 < q)).trans hqQ
    have hnumNat :
        (2 * H * q.primeFactors.card) * (2 * H) ^ 2 < 2 ^ k := by
      apply lt_of_le_of_lt _ hNtwo
      dsimp only [N, section4BCCBadMagnitude]
      exact Nat.mul_le_mul_right ((2 * H) ^ 2)
        (Nat.mul_le_mul_left (2 * H) homega)
    have hnumReal :
        ((2 * H * q.primeFactors.card : ℕ) : ℝ) *
            ((2 * H : ℕ) : ℝ) ^ 2 < ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast hnumNat
    rw [div_mul_eq_mul_div, div_lt_one (by positivity : (0 : ℝ) < (2 ^ k : ℕ))]
    exact hnumReal
  exact ⟨{
    L := L
    H := H
    k := k
    D := D
    two_le_Q := hQ
    B_nonneg := hB
    L_pos := hLpos
    H_pos := hHpos
    k_pos := hkpos
    D_pos := hDpos
    layers_large := hLlarge
    L_lt_k := hLk
    selected_pow_le := hpowers
    badResidueTerm_lt_one := hbad
    taylorScale_le := by simp [D, section4BCCTaylorCutoff]
  }⟩

/-- A canonical witness, convenient when the surrounding assembly wants data
rather than an existential. -/
def canonicalSection4BCCParameters (Q : ℕ) (B : ℝ)
    (hQ : 2 ≤ Q) (hB : 0 ≤ B) : Section4BCCParameters Q B :=
  Classical.choice (exists_section4BCCParameters Q B hQ hB)

def Section4BCCParameters.selected {Q : ℕ} {B : ℝ}
    (P : Section4BCCParameters Q B) (q : ℕ) : Finset ℕ :=
  section4SelectedQPowers q P.L

@[simp] theorem Section4BCCParameters.card_selected
    {Q : ℕ} {B : ℝ} (P : Section4BCCParameters Q B)
    {q : ℕ} (hq : 2 ≤ q) :
    (P.selected q).card = P.L :=
  card_section4SelectedQPowers hq

/-- Every selected power is an actual divisor of `q^(k-1)`, exactly the
subset hypothesis of `fullDivisor_bcc_contradiction_of_discrepancy`. -/
theorem Section4BCCParameters.selected_subset_divisors
    {Q : ℕ} {B : ℝ} (P : Section4BCCParameters Q B)
    {q : ℕ} (hq : 2 ≤ q) :
    P.selected q ⊆ (q ^ (P.k - 1)).divisors := by
  intro d hd
  rw [Section4BCCParameters.selected, section4SelectedQPowers,
    Finset.mem_image] at hd
  obtain ⟨i, hi, rfl⟩ := hd
  have hiL : i < P.L := Finset.mem_range.mp hi
  have hLk : P.L < P.k := P.L_lt_k
  have hik : i ≤ P.k - 1 := by omega
  exact Nat.mem_divisors.mpr
    ⟨Nat.pow_dvd_pow q hik, pow_ne_zero _ (by omega)⟩

/-- Every selected divisor is short enough for the BCC prefix bridge. -/
theorem Section4BCCParameters.two_mul_selected_le
    {Q : ℕ} {B : ℝ} (P : Section4BCCParameters Q B)
    {q : ℕ} (hq : 2 ≤ q) (hqQ : q ≤ Q) :
    ∀ d ∈ P.selected q, 2 * d ≤ P.H := by
  intro d hd
  rw [Section4BCCParameters.selected, section4SelectedQPowers,
    Finset.mem_image] at hd
  obtain ⟨i, hi, rfl⟩ := hd
  exact P.selected_pow_le q i hq hqQ (Finset.mem_range.mp hi)

/-- The exact strict inequality fed to the final contradiction theorem. -/
theorem Section4BCCParameters.fullDivisor_bcc_large
    {Q : ℕ} {B : ℝ} (P : Section4BCCParameters Q B)
    {q : ℕ} (hq : 2 ≤ q) (hqQ : q ≤ Q) :
    8 * (q : ℝ) *
          (B +
            (((2 * P.H * q.primeFactors.card : ℕ) : ℝ) /
                ((2 ^ P.k : ℕ) : ℝ)) * ((2 * P.H : ℕ) : ℝ) ^ 2) <
      (P.selected q).card := by
  let e : ℝ :=
    (((2 * P.H * q.primeFactors.card : ℕ) : ℝ) /
        ((2 ^ P.k : ℕ) : ℝ)) * ((2 * P.H : ℕ) : ℝ) ^ 2
  have he : e < 1 := P.badResidueTerm_lt_one q hq hqQ
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hBone : 0 < B + 1 := by linarith [P.B_nonneg]
  have hqQreal : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hsmall : 8 * (q : ℝ) * (B + e) < 16 * (Q : ℝ) * (B + 1) := by
    have hinner : B + e < B + 1 := by linarith
    have hfirst : 8 * (q : ℝ) * (B + e) < 8 * (q : ℝ) * (B + 1) := by
      nlinarith
    have hsecond : 8 * (q : ℝ) * (B + 1) ≤ 8 * (Q : ℝ) * (B + 1) := by
      nlinarith
    nlinarith
  rw [P.card_selected hq]
  change 8 * (q : ℝ) * (B + e) < (P.L : ℝ)
  exact hsmall.trans P.layers_large

/-- The parameter package directly instantiates the exact full-divisor BCC
contradiction theorem.  Thus the only remaining inputs here are the character
data and the normalized good-residue energy estimate; all elementary
parameter side conditions have been discharged. -/
theorem Section4BCCParameters.fullDivisor_bcc_contradiction
    {Q : ℕ} {B : ℝ} (P : Section4BCCParameters Q B)
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hqQ : q ≤ Q)
    (z : PrimeAssignment) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hagree : AgreesWithCharacterAway z χ)
    (hdiscrepancy :
      (1 / (((q ^ P.k : ℕ) : ℝ) * P.H)) *
          ∑ M ∈ Finset.Ioc P.H (2 * P.H),
            ∑ a ∈ cyclicGoodResidues q P.k P.H,
              Complex.normSq
                (∑ m ∈ Finset.Icc 1 M,
                  (primeExtension z
                    (a + (m : ZMod (q ^ P.k))).val : ℂ)) ≤ B) : False := by
  exact fullDivisor_bcc_contradiction_of_discrepancy
    P.k_pos P.H_pos (by omega) z χ hχ hagree (P.selected q)
      (P.selected_subset_divisors hq)
      (P.two_mul_selected_le hq hqQ) B hdiscrepancy
      (P.fullDivisor_bcc_large hq hqQ)

end

end Erdos67b
