/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralBounds
import BoundedGaps.Maynard.ImprovedGPY.S2TrivialDiscrepancy
import BoundedGaps.Maynard.MaynardLambdaSharpBound

/-!
# Divisor-power fibers for the general pinned modulus

The arbitrary-overlap CRT modulus is an lcm.  Every coordinate of each of
the four divisor tuples therefore divides the resulting modulus.  Mapping a
quadruple to its four functions into the finite divisor set is injective, so
the fiber above `M` has size at most `tau(M)^(4 * |H|)`.  For squarefree `M`
this is `(2^(4 * |H|))^omega(M)`, precisely the fixed divisor-power weight
accepted by the weighted Bombieri--Vinogradov estimate.
-/

namespace Erdos4b

open scoped ArithmeticFunction.omega BigOperators

noncomputable section

noncomputable local instance generalTauPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Every first-family coordinate divides the complete pinned lcm period. -/
theorem pinnedGeneralFirstCoordinate_dvd_modulus
    {H : Finset ℕ} (d e d' e' : H → ℕ) (h : H) :
    d h ∣ pinnedGeneralCrtModulus H d e d' e' := by
  apply (Nat.dvd_lcm_left (d h) (d' h)).trans
  unfold pinnedGeneralCrtModulus generalCrtModulus
  exact Finset.dvd_lcm
    (show Sum.inl h ∈ (Finset.univ : Finset (PinnedGeneralCrtIndex H)) by simp)

theorem pinnedGeneralFirstCoordinateRight_dvd_modulus
    {H : Finset ℕ} (d e d' e' : H → ℕ) (h : H) :
    d' h ∣ pinnedGeneralCrtModulus H d e d' e' := by
  apply (Nat.dvd_lcm_right (d h) (d' h)).trans
  unfold pinnedGeneralCrtModulus generalCrtModulus
  exact Finset.dvd_lcm
    (show Sum.inl h ∈ (Finset.univ : Finset (PinnedGeneralCrtIndex H)) by simp)

theorem pinnedGeneralCompanionCoordinate_dvd_modulus
    {H : Finset ℕ} (d e d' e' : H → ℕ) (h : H) :
    e h ∣ pinnedGeneralCrtModulus H d e d' e' := by
  apply (Nat.dvd_lcm_left (e h) (e' h)).trans
  unfold pinnedGeneralCrtModulus generalCrtModulus
  exact Finset.dvd_lcm
    (show Sum.inr h ∈ (Finset.univ : Finset (PinnedGeneralCrtIndex H)) by simp)

theorem pinnedGeneralCompanionCoordinateRight_dvd_modulus
    {H : Finset ℕ} (d e d' e' : H → ℕ) (h : H) :
    e' h ∣ pinnedGeneralCrtModulus H d e d' e' := by
  apply (Nat.dvd_lcm_right (e h) (e' h)).trans
  unfold pinnedGeneralCrtModulus generalCrtModulus
  exact Finset.dvd_lcm
    (show Sum.inr h ∈ (Finset.univ : Finset (PinnedGeneralCrtIndex H)) by simp)

/-- Four arbitrary functions from `H` into the divisors of `M`. -/
def pinnedGeneralDivisorContainer (H : Finset ℕ) (M : ℕ) :
    Finset (PinnedGeneralQuadrupleIndex H) :=
  let T := Fintype.piFinset (fun _ : H => M.divisors)
  T.product (T.product (T.product T))

theorem pinnedGeneralModulusFiber_subset_divisorContainer
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m M : ℕ}
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e) :
    (pinnedGeneralQuadrupleIndex D E).filter
        (fun i => pinnedGeneralIndexModulus i = M) ⊆
      pinnedGeneralDivisorContainer H M := by
  classical
  intro i hi
  obtain ⟨hiIndex, hiMod⟩ := Finset.mem_filter.mp hi
  obtain ⟨hiD, hiTail⟩ := Finset.mem_product.mp hiIndex
  obtain ⟨hiE, hiTail'⟩ := Finset.mem_product.mp hiTail
  obtain ⟨hiD', hiE'⟩ := Finset.mem_product.mp hiTail'
  have hM : M ≠ 0 := by
    rw [← hiMod]
    apply (pinnedGeneralCrtModulus_pos
      (fun h => BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard
        (hD i.1 hiD) (hD i.2.2.1 hiD') h)
      (fun h => BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard
        (hE i.2.1 hiE) (hE i.2.2.2 hiE') h)).ne'
  have hd : i.1 ∈ Fintype.piFinset (fun _ : H => M.divisors) := by
    rw [Fintype.mem_piFinset]
    intro h
    apply Nat.mem_divisors.mpr
    exact ⟨by rw [← hiMod]; exact
      pinnedGeneralFirstCoordinate_dvd_modulus _ _ _ _ h, hM⟩
  have he : i.2.1 ∈ Fintype.piFinset (fun _ : H => M.divisors) := by
    rw [Fintype.mem_piFinset]
    intro h
    apply Nat.mem_divisors.mpr
    exact ⟨by rw [← hiMod]; exact
      pinnedGeneralCompanionCoordinate_dvd_modulus _ _ _ _ h, hM⟩
  have hd' : i.2.2.1 ∈ Fintype.piFinset (fun _ : H => M.divisors) := by
    rw [Fintype.mem_piFinset]
    intro h
    apply Nat.mem_divisors.mpr
    exact ⟨by rw [← hiMod]; exact
      pinnedGeneralFirstCoordinateRight_dvd_modulus _ _ _ _ h, hM⟩
  have he' : i.2.2.2 ∈ Fintype.piFinset (fun _ : H => M.divisors) := by
    rw [Fintype.mem_piFinset]
    intro h
    apply Nat.mem_divisors.mpr
    exact ⟨by rw [← hiMod]; exact
      pinnedGeneralCompanionCoordinateRight_dvd_modulus _ _ _ _ h, hM⟩
  exact Finset.mem_product.mpr ⟨hd,
    Finset.mem_product.mpr ⟨he, Finset.mem_product.mpr ⟨hd', he'⟩⟩⟩

theorem pinnedGeneralDivisorContainer_card (H : Finset ℕ) (M : ℕ) :
    (pinnedGeneralDivisorContainer H M).card =
      M.divisors.card ^ (4 * Fintype.card H) := by
  classical
  simp [pinnedGeneralDivisorContainer, Fintype.card_piFinset,
    Finset.card_product, Fintype.card_coe, ← pow_add]
  congr 1
  omega

theorem pinnedGeneralModulusFiber_card_le_divisors_pow
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m M : ℕ}
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e) :
    ((pinnedGeneralQuadrupleIndex D E).filter
        (fun i => pinnedGeneralIndexModulus i = M)).card ≤
      M.divisors.card ^ (4 * Fintype.card H) := by
  calc
    _ ≤ (pinnedGeneralDivisorContainer H M).card :=
      Finset.card_le_card
        (pinnedGeneralModulusFiber_subset_divisorContainer hD hE)
    _ = _ := pinnedGeneralDivisorContainer_card H M

def pinnedGeneralTauBase (H : Finset ℕ) : ℕ :=
  2 ^ (4 * Fintype.card H)

theorem divisors_pow_four_card_eq_pinnedGeneralTauPow
    {H : Finset ℕ} {M : ℕ} (hM : Squarefree M) :
    M.divisors.card ^ (4 * Fintype.card H) =
      pinnedGeneralTauBase H ^ ω M := by
  rw [BoundedGaps.Maynard.card_divisors_eq_two_pow_omega hM]
  unfold pinnedGeneralTauBase
  rw [← pow_mul, Nat.mul_comm (ω M), pow_mul]

theorem squarefree_finset_lcm_of_squarefree
    {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ S, Squarefree (f i)) :
    Squarefree (S.lcm f) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.lcm_insert]
      apply BoundedGaps.Maynard.squarefree_lcm
      · exact hf i (by simp)
      · apply ih
        intro j hj
        exact hf j (by simp [hj])

theorem squarefree_pinnedGeneralCrtModulus
    {H : Finset ℕ} {RD RE W m : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e') :
    Squarefree (pinnedGeneralCrtModulus H d e d' e') := by
  unfold pinnedGeneralCrtModulus generalCrtModulus
  apply squarefree_finset_lcm_of_squarefree
  intro i hi
  cases i with
  | inl h =>
      exact BoundedGaps.Maynard.squarefree_divisorTupleLcm hd hd' h
  | inr h =>
      exact BoundedGaps.Maynard.squarefree_divisorTupleLcm he he' h

theorem squarefree_of_mem_pinnedGeneralModulusSet
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m M : ℕ}
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (hM : M ∈ pinnedGeneralModulusSet D E) :
    Squarefree M := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hM
  obtain ⟨hiD, hiTail⟩ := Finset.mem_product.mp hi
  obtain ⟨hiE, hiTail'⟩ := Finset.mem_product.mp hiTail
  obtain ⟨hiD', hiE'⟩ := Finset.mem_product.mp hiTail'
  exact squarefree_pinnedGeneralCrtModulus
    (hD i.1 hiD) (hD i.2.2.1 hiD')
    (hE i.2.1 hiE) (hE i.2.2.2 hiE')

theorem pinnedGeneralModulusFiber_card_le_tauPow
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m M : ℕ}
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (hM : Squarefree M) :
    ((pinnedGeneralQuadrupleIndex D E).filter
        (fun i => pinnedGeneralIndexModulus i = M)).card ≤
      pinnedGeneralTauBase H ^ ω M := by
  exact (pinnedGeneralModulusFiber_card_le_divisors_pow hD hE).trans_eq
    (divisors_pow_four_card_eq_pinnedGeneralTauPow hM)

/-- A pointwise bound on the Selberg coefficient gives the required fixed
divisor-power envelope for every lcm fiber. -/
theorem pinnedGeneralModulusCoefficientMass_le_tauPow
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m M : ℕ}
    {L : ℝ} (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (hM : Squarefree M) (hL : 0 ≤ L)
    (hlambda : ∀ d ∈ D, ∀ e ∈ E, |lambda d e| ≤ L) :
    pinnedGeneralModulusCoefficientMass D E lambda M ≤
      L ^ 2 * ((pinnedGeneralTauBase H ^ ω M : ℕ) : ℝ) := by
  let F := (pinnedGeneralQuadrupleIndex D E).filter
    (fun i => pinnedGeneralIndexModulus i = M)
  have hterm : ∀ i ∈ F, pinnedGeneralIndexCoefficient lambda i ≤ L ^ 2 := by
    intro i hi
    have hiIndex := (Finset.mem_filter.mp hi).1
    obtain ⟨hiD, hiTail⟩ := Finset.mem_product.mp hiIndex
    obtain ⟨hiE, hiTail'⟩ := Finset.mem_product.mp hiTail
    obtain ⟨hiD', hiE'⟩ := Finset.mem_product.mp hiTail'
    unfold pinnedGeneralIndexCoefficient
    rw [pow_two]
    exact mul_le_mul (hlambda i.1 hiD i.2.1 hiE)
      (hlambda i.2.2.1 hiD' i.2.2.2 hiE') (abs_nonneg _) hL
  have hcard := pinnedGeneralModulusFiber_card_le_tauPow hD hE hM
  unfold pinnedGeneralModulusCoefficientMass
  change (∑ i ∈ F, pinnedGeneralIndexCoefficient lambda i) ≤ _
  calc
    (∑ i ∈ F, pinnedGeneralIndexCoefficient lambda i) ≤
        ∑ _i ∈ F, L ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i hi
    _ = (F.card : ℝ) * L ^ 2 := by
      simp [nsmul_eq_mul]
    _ ≤ ((pinnedGeneralTauBase H ^ ω M : ℕ) : ℝ) * L ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ = L ^ 2 * ((pinnedGeneralTauBase H ^ ω M : ℕ) : ℝ) := by ring_nf

/-- The explicit Cauchy--Schwarz/Bombieri--Vinogradov majorant used at one
prime-counting endpoint. -/
noncomputable def pinnedGeneralTauDiscrepancyBound
    (C exponent : ℝ) (x Q d : ℕ) : ℝ :=
  Real.sqrt
      ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
        (1 + Real.log Q) ^ (2 * d ^ 2)) *
    Real.sqrt
      (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) exponent)

/-- The genuine unseparated doubled Selberg coefficient.  Unlike the earlier
`fullySeparatedDoubledCoefficient`, this definition does not delete tuples
whose first and companion coordinates share a prime. -/
noncomputable def pinnedGeneralMaynardCoefficient
    (H : Finset ℕ) (RD RE W m : ℕ)
    (F G : (H → ℝ) → ℝ) (d e : H → ℕ) : ℝ :=
  BoundedGaps.Maynard.maynardCoefficient H RD W F d *
    BoundedGaps.Maynard.maynardCoefficient H RE (W * m) G e

noncomputable def pinnedGeneralMaynardCoefficientEnvelope
    (H : Finset ℕ) (RD RE : ℕ) (BD BE : ℝ) : ℝ :=
  (BD * (1 + Real.log RD) ^ (2 * (Fintype.card H) ^ 2)) *
    (BE * (1 + Real.log RE) ^ (2 * (Fintype.card H) ^ 2))

theorem pinnedGeneralMaynardCoefficientEnvelope_nonneg
    (H : Finset ℕ) (RD RE : ℕ) {BD BE : ℝ}
    (hBD : 0 ≤ BD) (hBE : 0 ≤ BE) :
    0 ≤ pinnedGeneralMaynardCoefficientEnvelope H RD RE BD BE := by
  unfold pinnedGeneralMaynardCoefficientEnvelope
  exact mul_nonneg
    (mul_nonneg hBD (by positivity)) (mul_nonneg hBE (by positivity))

theorem pinnedGeneralMaynardCoefficient_abs_le
    {H : Finset ℕ} {RD RE W m : ℕ}
    {F G : (H → ℝ) → ℝ} {BD BE : ℝ}
    (hH : H.Nonempty) (hBD : 0 ≤ BD) (hBE : 0 ≤ BE)
    (hF : ∀ x, |F x| ≤ BD) (hG : ∀ x, |G x| ≤ BE)
    {d e : H → ℕ}
    (hd : d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
    (he : e ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m)) :
    |pinnedGeneralMaynardCoefficient H RD RE W m F G d e| ≤
      pinnedGeneralMaynardCoefficientEnvelope H RD RE BD BE := by
  unfold pinnedGeneralMaynardCoefficient pinnedGeneralMaynardCoefficientEnvelope
  rw [abs_mul]
  exact mul_le_mul
    (BoundedGaps.Maynard.abs_maynardCoefficient_le_sharp_log
      H RD W F d BD hBD hF hH hd)
    (BoundedGaps.Maynard.abs_maynardCoefficient_le_sharp_log
      H RE (W * m) G e BE hBE hG hH he)
    (abs_nonneg _) (mul_nonneg hBD (by positivity))

/-- Weighted Bombieri--Vinogradov controls the grouped arbitrary-overlap
error after the elementary divisor-fiber estimate above. -/
theorem primeLevelWitness_pinnedGeneralGroupedDiscrepancySum_le_tau
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m Q : ℕ}
    {theta exponent C L : ℝ} {X₀ x₁ x₂ : ℕ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta exponent C X₀)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (hx₁ : X₀ ≤ x₁) (hx₂ : X₀ ≤ x₂)
    (hQ : pinnedGeneralModulusSet D E ⊆ Finset.Icc 1 Q)
    (hQx₁ : Q ≤ x₁ + 1) (hQx₂ : Q ≤ x₂ + 1)
    (hcut₁ : pinnedGeneralModulusSet D E ⊆
      Finset.Icc 1 (BoundedGaps.Maynard.modulusCutoff theta x₁))
    (hcut₂ : pinnedGeneralModulusSet D E ⊆
      Finset.Icc 1 (BoundedGaps.Maynard.modulusCutoff theta x₂))
    (hL : 0 ≤ L)
    (hlambda : ∀ d ∈ D, ∀ e ∈ E, |lambda d e| ≤ L) :
    pinnedGeneralGroupedDiscrepancySum H D E lambda x₁ x₂ ≤
      L ^ 2 *
        (pinnedGeneralTauDiscrepancyBound C exponent x₁ Q
            (pinnedGeneralTauBase H) +
          pinnedGeneralTauDiscrepancyBound C exponent x₂ Q
            (pinnedGeneralTauBase H)) := by
  let S := pinnedGeneralModulusSet D E
  let d := pinnedGeneralTauBase H
  let Δ₁ : ℕ → ℝ := fun M =>
    BoundedGaps.Maynard.maxProgressionDiscrepancy x₁ M
  let Δ₂ : ℕ → ℝ := fun M =>
    BoundedGaps.Maynard.maxProgressionDiscrepancy x₂ M
  have hsq : ∀ M ∈ S, Squarefree M := by
    intro M hM
    exact squarefree_of_mem_pinnedGeneralModulusSet hD hE hM
  have hBV₁ :
      (∑ M ∈ S, ((d ^ ω M : ℕ) : ℝ) * Δ₁ M) ≤
        pinnedGeneralTauDiscrepancyBound C exponent x₁ Q d := by
    simpa [pinnedGeneralTauDiscrepancyBound, S, d, Δ₁] using
      (hw.sum_tauPow_mul_maxProgressionDiscrepancy_explicit
        (d := d) hx₁ S hQ hsq hQx₁ hcut₁)
  have hBV₂ :
      (∑ M ∈ S, ((d ^ ω M : ℕ) : ℝ) * Δ₂ M) ≤
        pinnedGeneralTauDiscrepancyBound C exponent x₂ Q d := by
    simpa [pinnedGeneralTauDiscrepancyBound, S, d, Δ₂] using
      (hw.sum_tauPow_mul_maxProgressionDiscrepancy_explicit
        (d := d) hx₂ S hQ hsq hQx₂ hcut₂)
  have hmass : ∀ M ∈ S,
      pinnedGeneralModulusCoefficientMass D E lambda M ≤
        L ^ 2 * ((d ^ ω M : ℕ) : ℝ) := by
    intro M hM
    simpa [d] using pinnedGeneralModulusCoefficientMass_le_tauPow
      lambda hD hE (hsq M hM) hL hlambda
  unfold pinnedGeneralGroupedDiscrepancySum
  change (∑ M ∈ S,
      pinnedGeneralModulusCoefficientMass D E lambda M *
        (Δ₁ M + Δ₂ M)) ≤ _
  calc
    (∑ M ∈ S,
        pinnedGeneralModulusCoefficientMass D E lambda M *
          (Δ₁ M + Δ₂ M)) ≤
        ∑ M ∈ S,
          (L ^ 2 * ((d ^ ω M : ℕ) : ℝ)) *
            (Δ₁ M + Δ₂ M) := by
      apply Finset.sum_le_sum
      intro M hM
      apply mul_le_mul_of_nonneg_right (hmass M hM)
      exact add_nonneg
        (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
        (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
    _ = L ^ 2 *
        ((∑ M ∈ S, ((d ^ ω M : ℕ) : ℝ) * Δ₁ M) +
          ∑ M ∈ S, ((d ^ ω M : ℕ) : ℝ) * Δ₂ M) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      ring_nf
    _ ≤ L ^ 2 *
        (pinnedGeneralTauDiscrepancyBound C exponent x₁ Q d +
          pinnedGeneralTauDiscrepancyBound C exponent x₂ Q d) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hBV₁ hBV₂) (sq_nonneg L)
    _ = _ := by rfl

/-- The grouped discrepancy bound specialized to the actual two Maynard
coefficient systems.  All support and pointwise-coefficient assumptions are
discharged from the library's standard support and sharp lambda bound. -/
theorem primeLevelWitness_pinnedGeneralMaynardGroupedDiscrepancySum_le_tau
    {H : Finset ℕ} {RD RE W m Q : ℕ}
    {F G : (H → ℝ) → ℝ} {BD BE theta exponent C : ℝ}
    {X₀ x₁ x₂ : ℕ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta exponent C X₀)
    (hH : H.Nonempty) (hBD : 0 ≤ BD) (hBE : 0 ≤ BE)
    (hF : ∀ x, |F x| ≤ BD) (hG : ∀ x, |G x| ≤ BE)
    (hx₁ : X₀ ≤ x₁) (hx₂ : X₀ ≤ x₂)
    (hQ : pinnedGeneralModulusSet
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m)) ⊆
      Finset.Icc 1 Q)
    (hQx₁ : Q ≤ x₁ + 1) (hQx₂ : Q ≤ x₂ + 1)
    (hcut₁ : pinnedGeneralModulusSet
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m)) ⊆
      Finset.Icc 1 (BoundedGaps.Maynard.modulusCutoff theta x₁))
    (hcut₂ : pinnedGeneralModulusSet
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m)) ⊆
      Finset.Icc 1 (BoundedGaps.Maynard.modulusCutoff theta x₂)) :
    pinnedGeneralGroupedDiscrepancySum H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        (pinnedGeneralMaynardCoefficient H RD RE W m F G) x₁ x₂ ≤
      pinnedGeneralMaynardCoefficientEnvelope H RD RE BD BE ^ 2 *
        (pinnedGeneralTauDiscrepancyBound C exponent x₁ Q
            (pinnedGeneralTauBase H) +
          pinnedGeneralTauDiscrepancyBound C exponent x₂ Q
            (pinnedGeneralTauBase H)) := by
  let D := BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W
  let E := BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m)
  let lambda := pinnedGeneralMaynardCoefficient H RD RE W m F G
  let L := pinnedGeneralMaynardCoefficientEnvelope H RD RE BD BE
  have hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d := by
    intro d hd
    exact BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
  have hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e := by
    intro e he
    exact BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he
  have hL : 0 ≤ L :=
    pinnedGeneralMaynardCoefficientEnvelope_nonneg H RD RE hBD hBE
  have hlambda : ∀ d ∈ D, ∀ e ∈ E, |lambda d e| ≤ L := by
    intro d hd e he
    exact pinnedGeneralMaynardCoefficient_abs_le hH hBD hBE hF hG hd he
  simpa [D, E, lambda, L] using
    (primeLevelWitness_pinnedGeneralGroupedDiscrepancySum_le_tau
      hw lambda hD hE hx₁ hx₂ hQ hQx₁ hQx₂ hcut₁ hcut₂ hL hlambda)

/-- End-to-end arbitrary-overlap prime-count error bound with no abstract
fiber-mass hypothesis: the only coefficient input is a pointwise bound. -/
theorem primeLevelWitness_abs_pinnedGeneralErrorSum_primeInterval_le_tau
    {H : Finset ℕ} {D E : Finset (H → ℕ)}
    {RD RE W m p Y A B Q : ℕ} {theta exponent C L : ℝ} {X₀ : ℕ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta exponent C X₀)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p)
    (hmargin : ∀ h : H, ∀ q ∈ Finset.Ico A B,
      h.1 * (W * q) < p)
    (hA : 0 < A) (hAB : A ≤ B)
    (hxB : X₀ ≤ B - 1) (hxA : X₀ ≤ A - 1)
    (hQ : pinnedGeneralModulusSet D E ⊆ Finset.Icc 1 Q)
    (hQB : Q ≤ (B - 1) + 1) (hQA : Q ≤ (A - 1) + 1)
    (hcutB : pinnedGeneralModulusSet D E ⊆
      Finset.Icc 1
        (BoundedGaps.Maynard.modulusCutoff theta (B - 1)))
    (hcutA : pinnedGeneralModulusSet D E ⊆
      Finset.Icc 1
        (BoundedGaps.Maynard.modulusCutoff theta (A - 1)))
    (hL : 0 ≤ L)
    (hlambda : ∀ d ∈ D, ∀ e ∈ E, |lambda d e| ≤ L) :
    |pinnedGeneralErrorSum H D E lambda W m p
        (auxiliaryPrimeInterval A B)| ≤
      (H.card : ℝ) *
        (L ^ 2 *
          (pinnedGeneralTauDiscrepancyBound C exponent (B - 1) Q
              (pinnedGeneralTauBase H) +
            pinnedGeneralTauDiscrepancyBound C exponent (A - 1) Q
              (pinnedGeneralTauBase H))) := by
  have hpoint :=
    abs_pinnedGeneralErrorSum_primeInterval_le_weightedDiscrepancy
      lambda hD hE hm hcover hp hRDp hREY hpre hmargin hA hAB
  have hgroup := pinnedGeneralWeightedDiscrepancySum_eq_card_mul_grouped
    H D E lambda (B - 1) (A - 1)
  have hBV := primeLevelWitness_pinnedGeneralGroupedDiscrepancySum_le_tau
    hw lambda hD hE hxB hxA hQ hQB hQA hcutB hcutA hL hlambda
  calc
    _ ≤ pinnedGeneralWeightedDiscrepancySum H D E lambda
          (B - 1) (A - 1) := hpoint
    _ = (H.card : ℝ) *
          pinnedGeneralGroupedDiscrepancySum H D E lambda
            (B - 1) (A - 1) := hgroup
    _ ≤ _ := mul_le_mul_of_nonneg_left hBV (by positivity)

end

end Erdos4b
