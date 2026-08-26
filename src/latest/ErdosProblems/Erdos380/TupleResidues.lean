import ErdosProblems.Erdos380.MixingScale
import ErdosProblems.Erdos380.FiniteProbability

/-!
# Residue events on the uniform prime-tuple space

These are identities on the original Cartesian product of prime pools.
They connect the character-sum estimates to first and second moments of
the divisibility indicators, without an independence assumption on residues.
-/

open scoped BigOperators

namespace Erdos380

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tupleNaturalProduct (s : ι → Finset ℕ) (f : ∀ i, s i) : ℕ :=
  ∏ i, (f i).val

def tupleResidueIndicator (s : ι → Finset ℕ) (q : ℕ) (a : ZMod q)
    (f : ∀ i, s i) : ℝ := by
  classical
  exact if (tupleNaturalProduct s f : ZMod q) = a then 1 else 0

lemma tupleResidueIndicator_nonneg (s : ι → Finset ℕ) (q : ℕ) (a : ZMod q) (f : ∀ i, s i) :
    0 ≤ tupleResidueIndicator s q a f := by
  classical
  unfold tupleResidueIndicator
  split_ifs <;> norm_num

lemma tupleResidueIndicator_sq (s : ι → Finset ℕ) (q : ℕ) (a : ZMod q) (f : ∀ i, s i) :
    tupleResidueIndicator s q a f ^ 2 = tupleResidueIndicator s q a f := by
  classical
  unfold tupleResidueIndicator
  split_ifs <;> norm_num

lemma expect_tupleResidueIndicator (s : ι → Finset ℕ) (q : ℕ) (a : ZMod q) :
    (𝔼 f : ∀ i, s i, tupleResidueIndicator s q a f) = tupleResidueProbability s q a := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  simp only [tupleResidueIndicator, Finset.sum_boole, tupleResidueProbability, tupleResidueCount,
    tupleNaturalProduct, Fintype.card_pi, Fintype.card_coe, Nat.cast_prod]

lemma tupleResidueIndicator_mul_eq_zero (s : ι → Finset ℕ) {q : ℕ}
    {a b : ZMod q} (hab : a ≠ b) (f : ∀ i, s i) :
    tupleResidueIndicator s q a f * tupleResidueIndicator s q b f = 0 := by
  classical
  unfold tupleResidueIndicator
  split_ifs with ha hb
  · exact (hab (ha.symm.trans hb)).elim
  all_goals norm_num

lemma expect_tupleResidueIndicator_mul_same (s : ι → Finset ℕ) {q : ℕ} {a b : ZMod q}
    (hab : a ≠ b) :
    (𝔼 f : ∀ i, s i, tupleResidueIndicator s q a f * tupleResidueIndicator s q b f) = 0 := by
  simp only [tupleResidueIndicator_mul_eq_zero s hab, Finset.expect_const_zero]

theorem expect_ten_prime_residue_error_le (s : Fin 10 → Finset ℕ)
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (hs : ∀ i p, p ∈ s i → p.Prime) (hne : ∀ i, (s i).Nonempty) :
    |(𝔼 f : ∀ i, s i, tupleResidueIndicator s q a f) - 1 / (q.totient : ℝ)| ≤
      tenPrimeResidueError s q := by
  rw [expect_tupleResidueIndicator]
  have h := ten_prime_residue_bias_le s ha hs hne
  have heq : ((tupleResidueProbability s q a - 1 / (q.totient : ℝ) : ℝ) : ℂ) =
      (tupleResidueProbability s q a : ℂ) - 1 / (q.totient : ℂ) := by push_cast; rfl
  rw [← heq] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

lemma unit_mul_residue_iff {q : ℕ} (c h : (ZMod q)ˣ) (x : ZMod q) :
    (c : ZMod q) * x = h ↔ x = ((c⁻¹ * h : (ZMod q)ˣ) : ZMod q) := by
  constructor
  · intro hx
    calc
      x = (c⁻¹ : (ZMod q)ˣ) * ((c : ZMod q) * x) := by simp [← mul_assoc]
      _ = _ := by rw [hx]; rfl
  · intro hx
    rw [hx]
    simp [← mul_assoc]

def combinedResidue {p q : ℕ} (hpq : p.Coprime q) (a : ZMod p) (b : ZMod q) :
    ZMod (p * q) := (ZMod.chineseRemainder hpq).symm (a, b)

lemma combinedResidue_isUnit {p q : ℕ} (hpq : p.Coprime q)
    {a : ZMod p} {b : ZMod q} (ha : IsUnit a) (hb : IsUnit b) :
    IsUnit (combinedResidue hpq a b) := by
  have hprod : IsUnit (a, b) := by
    obtain ⟨ua, rfl⟩ := ha
    obtain ⟨ub, rfl⟩ := hb
    exact ⟨⟨(ua, ub), (↑ua⁻¹, ↑ub⁻¹), by simp, by simp⟩, rfl⟩
  exact hprod.map (ZMod.chineseRemainder hpq).symm.toMonoidHom

lemma natCast_eq_combinedResidue {p q : ℕ} (hpq : p.Coprime q)
    (a : ZMod p) (b : ZMod q) (n : ℕ) :
    ((n : ZMod p) = a ∧ (n : ZMod q) = b) ↔
      (n : ZMod (p * q)) = combinedResidue hpq a b := by
  constructor
  · rintro ⟨ha, hb⟩
    apply (ZMod.chineseRemainder hpq).injective
    rw [map_natCast, combinedResidue, RingEquiv.apply_symm_apply]
    exact Prod.ext ha hb
  · intro h
    have heq := congrArg (ZMod.chineseRemainder hpq) h
    rw [map_natCast, combinedResidue, RingEquiv.apply_symm_apply] at heq
    exact Prod.mk.inj heq

lemma tupleResidueIndicator_mul_coprime (s : ι → Finset ℕ) {p q : ℕ}
    (hpq : p.Coprime q) (a : ZMod p) (b : ZMod q) (f : ∀ i, s i) :
    tupleResidueIndicator s p a f * tupleResidueIndicator s q b f =
      tupleResidueIndicator s (p * q) (combinedResidue hpq a b) f := by
  classical
  unfold tupleResidueIndicator
  simp only [← natCast_eq_combinedResidue hpq]
  split_ifs <;> simp_all

lemma expect_tupleResidueIndicator_mul_coprime (s : ι → Finset ℕ) {p q : ℕ}
    (hpq : p.Coprime q) (a : ZMod p) (b : ZMod q) :
    (𝔼 f : ∀ i, s i, tupleResidueIndicator s p a f * tupleResidueIndicator s q b f) =
      tupleResidueProbability s (p * q) (combinedResidue hpq a b) := by
  simp only [tupleResidueIndicator_mul_coprime s hpq, expect_tupleResidueIndicator]

/-- The two-point error is controlled by the semiprime modulus, not by an
assumption that the two residue events are independent. -/
theorem expect_ten_prime_residue_pair_error_le (s : Fin 10 → Finset ℕ)
    {p q : ℕ} [NeZero p] [NeZero q] (hpq : p.Coprime q)
    {a : ZMod p} {b : ZMod q} (ha : IsUnit a) (hb : IsUnit b)
    (hs : ∀ i r, r ∈ s i → r.Prime) (hne : ∀ i, (s i).Nonempty) :
    |(𝔼 f : ∀ i, s i, tupleResidueIndicator s p a f * tupleResidueIndicator s q b f) -
      (1 / (p.totient : ℝ)) * (1 / (q.totient : ℝ))| ≤ tenPrimeResidueError s (p * q) := by
  have h := expect_ten_prime_residue_error_le s (combinedResidue_isUnit hpq ha hb) hs hne
  simp only [tupleResidueIndicator_mul_coprime s hpq]
  simpa only [Nat.totient_mul hpq, Nat.cast_mul, one_div, mul_inv_rev, mul_comm] using h

end

end Erdos380
