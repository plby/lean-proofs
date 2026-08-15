/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.DivisorSwitching

/-!
# Reciprocal sums of switched rough tuples

This file reduces the reciprocal main sum after divisor switching to the
`k`th power of a one-dimensional reciprocal sum over `z`-rough integers.
-/

namespace Erdos387

open scoped BigOperators

/-- Positive `z`-rough integers at most `T`. -/
noncomputable def roughPositiveUpTo (z T : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 T).filter (IsZRough z)

theorem mem_roughPositiveUpTo_iff {z T m : ℕ} :
    m ∈ roughPositiveUpTo z T ↔ 0 < m ∧ m ≤ T ∧ IsZRough z m := by
  classical
  rw [roughPositiveUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hm, hmT⟩, hrough⟩
    exact ⟨hm, hmT, hrough⟩
  · rintro ⟨hm, hmT, hrough⟩
    exact ⟨⟨hm, hmT⟩, hrough⟩

/-- The one-dimensional rough harmonic mass. -/
noncomputable def roughReciprocalMass (z T : ℕ) : ℝ :=
  ∑ m ∈ roughPositiveUpTo z T, (1 : ℝ) / m

namespace CoverBPZ

/-- Forget the certificate proofs and retain its ordered factor vector. -/
def switchedFactorVector {B K X : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) : Fin S.k → ℕ :=
  fun i => C.val.factor i

theorem switchedFactorVector_injective {B K X : ℕ}
    {S : BPZSection6Input B K} :
    Function.Injective
      (switchedFactorVector (X := X) (S := S)) := by
  intro C₁ C₂ h
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun h i

/-- Every switched factor vector belongs to the Cartesian power of the
one-dimensional rough set. -/
theorem switchedFactorVector_mem_piFinset
    {B K X z large : ℕ} {S : BPZSection6Input B K}
    {C : RefinedTupleCertificate S X}
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large) :
    switchedFactorVector C ∈
      Fintype.piFinset (fun _ : Fin S.k =>
        roughPositiveUpTo z (X / (large + 1))) := by
  rw [Fintype.mem_piFinset]
  intro i
  apply mem_roughPositiveUpTo_iff.mpr
  exact ⟨C.val.positive i,
    switchedCertificate_factor_le_div hC i,
    switchedCertificate_factor_rough hC i⟩

/-- The reciprocal switched-certificate sum is bounded by a Cartesian
product of one-dimensional rough reciprocal sums. -/
theorem switchedCertificate_reciprocalSum_le_mass_pow
    {B K X z large : ℕ} (S : BPZSection6Input B K) :
    (∑ C ∈ SwitchedLargeTupleCertificates S X z large,
        (1 : ℝ) / C.val.value) ≤
      (roughReciprocalMass z (X / (large + 1))) ^ S.k := by
  classical
  let T := SwitchedLargeTupleCertificates S X z large
  let R := roughPositiveUpTo z (X / (large + 1))
  let F := Fintype.piFinset (fun _ : Fin S.k => R)
  let encode := switchedFactorVector (X := X) (S := S)
  have hinj : Function.Injective encode :=
    switchedFactorVector_injective (X := X) (S := S)
  have himageSubset : T.image encode ⊆ F := by
    intro f hf
    obtain ⟨C, hCT, rfl⟩ := Finset.mem_image.mp hf
    change encode C ∈ F
    simpa [encode, F, R] using switchedFactorVector_mem_piFinset hCT
  have hsumImage :
      (∑ C ∈ T, (1 : ℝ) / C.val.value) =
        ∑ f ∈ T.image encode,
          (1 : ℝ) / ((∏ i : Fin S.k, f i : ℕ) : ℝ) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro C hCT
      rfl
    · intro C₁ h₁ C₂ h₂ h
      exact hinj h
  rw [show SwitchedLargeTupleCertificates S X z large = T from rfl,
    hsumImage]
  calc
    (∑ f ∈ T.image encode,
        (1 : ℝ) / ((∏ i : Fin S.k, f i : ℕ) : ℝ)) ≤
        ∑ f ∈ F,
          (1 : ℝ) / ((∏ i : Fin S.k, f i : ℕ) : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himageSubset
        (by intro f hfF hfImage; positivity)
    _ = ∑ f ∈ F, ∏ i : Fin S.k, ((1 : ℝ) / f i) := by
      apply Finset.sum_congr rfl
      intro f hf
      push_cast
      simp only [one_div, Finset.prod_inv_distrib]
    _ = (roughReciprocalMass z (X / (large + 1))) ^ S.k := by
      change (∑ f ∈ Fintype.piFinset (fun _ : Fin S.k => R),
          ∏ i : Fin S.k, (1 : ℝ) / f i) =
        (∑ m ∈ R, (1 : ℝ) / m) ^ S.k
      exact (Finset.sum_pow' R (fun m : ℕ => (1 : ℝ) / m) S.k).symm

/-- Product-sensitive endpoint count.  Since every switched value is at
most `T²`, counting certificates costs only `T²` times their reciprocal
mass, rather than the much larger coordinate-box bound `(T+1)^k`. -/
theorem card_switchedLargeTupleCertificates_real_le_square_mul_mass_pow
    {B K X z large : ℕ} (S : BPZSection6Input B K) :
    ((SwitchedLargeTupleCertificates S X z large).card : ℝ) ≤
      (((X / (large + 1)) ^ 2 : ℕ) : ℝ) *
        (roughReciprocalMass z (X / (large + 1))) ^ S.k := by
  classical
  let T := SwitchedLargeTupleCertificates S X z large
  let Y := (X / (large + 1)) ^ 2
  have hper : ∀ C ∈ T, (1 : ℝ) ≤ (Y : ℝ) / C.val.value := by
    intro C hC
    have hvalue := switchedCertificate_value_le_square_div hC
    have hvaluePos : (0 : ℝ) < C.val.value := by
      exact_mod_cast C.val.value_pos
    apply (le_div_iff₀ hvaluePos).2
    rw [one_mul]
    dsimp [Y]
    exact_mod_cast hvalue
  have hmass := switchedCertificate_reciprocalSum_le_mass_pow
    (X := X) (z := z) (large := large) S
  calc
    (T.card : ℝ) = ∑ C ∈ T, (1 : ℝ) := by simp
    _ ≤ ∑ C ∈ T, (Y : ℝ) / C.val.value :=
      Finset.sum_le_sum hper
    _ = (Y : ℝ) * ∑ C ∈ T, (1 : ℝ) / C.val.value := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C hC
      ring
    _ ≤ (Y : ℝ) *
        (roughReciprocalMass z (X / (large + 1))) ^ S.k :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (((X / (large + 1)) ^ 2 : ℕ) : ℝ) *
        (roughReciprocalMass z (X / (large + 1))) ^ S.k := rfl

/-- Named product-sensitive envelope for the number of switched
certificates. -/
noncomputable def switchedCertificateCountEnvelope
    {B K : ℕ} (S : BPZSection6Input B K) (X z large : ℕ) : ℝ :=
  (((X / (large + 1)) ^ 2 : ℕ) : ℝ) *
    (roughReciprocalMass z (X / (large + 1))) ^ S.k

theorem card_switchedLargeTupleCertificates_real_le_envelope
    {B K X z large : ℕ} (S : BPZSection6Input B K) :
    ((SwitchedLargeTupleCertificates S X z large).card : ℝ) ≤
      switchedCertificateCountEnvelope S X z large := by
  simpa only [switchedCertificateCountEnvelope] using
    card_switchedLargeTupleCertificates_real_le_square_mul_mass_pow
      (X := X) (z := z) (large := large) S

/-- Proposition 6.2 reduced to a one-dimensional rough harmonic estimate,
with the endpoint error still explicit. -/
theorem refinedLargeErrors_card_le_roughMassPow_add_endpoint
    {B K X z large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hz : 2 * S.k ≤ z)
    (hXwide : 6 * S.k ≤ X)
    (hscale : (X / (large + 1)) ^ 2 ≤ X / 2) :
    ((RefinedLargeErrors S X z large).card : ℝ) ≤
      (((X - X / 2 : ℕ) : ℝ) / refinementModulus S) *
          (roughReciprocalMass z (X / (large + 1))) ^ S.k +
        2 * ((X / (large + 1) + 1) ^ S.k : ℕ) := by
  have hswitch := refinedLargeErrors_card_le_switchedMain_add_endpoint
    (X := X) (z := z) (large := large) S hB hz hXwide hscale
  have hmass := switchedCertificate_reciprocalSum_le_mass_pow
    (X := X) (z := z) (large := large) S
  have hcoef : 0 ≤
      (((X - X / 2 : ℕ) : ℝ) / refinementModulus S) :=
    div_nonneg (by positivity) (by exact_mod_cast (Nat.zero_le (refinementModulus S)))
  exact hswitch.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left hmass hcoef) _)

end CoverBPZ

end Erdos387
