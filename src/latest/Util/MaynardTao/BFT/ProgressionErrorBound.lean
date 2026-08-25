import Util.MaynardTao.BFT.ProgressionDistribution
import BoundedGaps.Maynard.ImprovedGPY.S2TauShiftedAggregation

/-! # Finite bounds for the progression sieve's second-moment error -/

namespace MaynardBFT

open BoundedGaps.Maynard
open scoped BigOperators ArithmeticFunction.omega

theorem compatiblePairShiftModulus_mul (H : Finset ℕ) (q W : ℕ)
    (i : (((H → ℕ) × (H → ℕ)) × H)) :
    compatiblePairShiftModulus H (q * W) i = q * compatiblePairShiftModulus H W i := by
  unfold compatiblePairShiftModulus divisorPairModulus
  ring

theorem progressionIndexedEndpointBound
    {theta A C : ℝ} {X₀ x Q q : ℕ}
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hw : PrimeLevelWitness theta A C X₀) (hx : X₀ ≤ x) (hq : 0 < q)
    (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hSQ : (compatiblePairShiftIndex H D).image (compatiblePairShiftModulus H W) ⊆
      Finset.Icc 1 Q)
    (hQx : q * Q ≤ x + 1) (hcut : q * Q ≤ modulusCutoff theta x) :
    (∑ i ∈ compatiblePairShiftIndex H D,
      maxProgressionDiscrepancy x (compatiblePairShiftModulus H (q * W) i)) ≤
      tauIndexedEndpointEnvelope H Q C A x := by
  classical
  let S := (compatiblePairShiftIndex H D).image (compatiblePairShiftModulus H W)
  have hfiber :
      (∑ i ∈ compatiblePairShiftIndex H D,
        maxProgressionDiscrepancy x (q * compatiblePairShiftModulus H W i)) ≤
      ∑ m ∈ S, (((3 * Fintype.card H) ^ ω m * Fintype.card H : ℕ) : ℝ) *
        maxProgressionDiscrepancy x (q * m) := by
    rw [sum_comp_eq_sum_modulusFiberCard (compatiblePairShiftIndex H D)
      (compatiblePairShiftModulus H W) (fun m => maxProgressionDiscrepancy x (q * m))]
    apply Finset.sum_le_sum
    intro m hm
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast modulusFiberCard_le_tauPow hH
        (Nat.pos_of_ne_zero hW.ne_zero) hD
        (squarefree_of_mem_compatiblePairShiftModulus_image hW hD hm)
        (W_dvd_of_mem_compatiblePairShiftModulus_image hm)
    · exact maxProgressionDiscrepancy_nonneg x (q * m)
  have hweighted := sum_tauPow_mul_progressionDiscrepancy
    (d := 3 * Fintype.card H) hw hx hq S hSQ
    (fun m hm => squarefree_of_mem_compatiblePairShiftModulus_image hW hD hm)
    (fun m hm => (Nat.mul_le_mul_left q (Finset.mem_Icc.mp (hSQ hm)).2).trans hQx)
    (by
      intro m hm
      have hmQ := Finset.mem_Icc.mp (hSQ hm)
      exact Finset.mem_Icc.mpr ⟨mul_pos hq hmQ.1,
        (Nat.mul_le_mul_left q hmQ.2).trans hcut⟩)
  simp_rw [compatiblePairShiftModulus_mul]
  calc
    _ ≤ ∑ m ∈ S, (((3 * Fintype.card H) ^ ω m * Fintype.card H : ℕ) : ℝ) *
        maxProgressionDiscrepancy x (q * m) := hfiber
    _ = (Fintype.card H : ℝ) *
        ∑ m ∈ S, (((3 * Fintype.card H) ^ ω m : ℕ) : ℝ) *
          maxProgressionDiscrepancy x (q * m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hweighted (Nat.cast_nonneg _)

theorem progressionShiftedEndpointBound
    {theta A C : ℝ} {X₀ : ℕ} (hw : PrimeLevelWitness theta A C X₀)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W N q : ℕ}
    (hq : 0 < q) (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hupper : ∀ h : H, X₀ ≤ 2 * N + h.1 - 1)
    (hlower : ∀ h : H, X₀ ≤ N + h.1 - 1)
    (hcutUpper : ∀ h : H, q * (W * R * R) ≤ modulusCutoff theta (2 * N + h.1 - 1))
    (hcutLower : ∀ h : H, q * (W * R * R) ≤ modulusCutoff theta (N + h.1 - 1))
    (hsizeUpper : ∀ h : H, q * (W * R * R) ≤ (2 * N + h.1 - 1) + 1)
    (hsizeLower : ∀ h : H, q * (W * R * R) ≤ (N + h.1 - 1) + 1) :
    compatiblePairShiftShiftedEndpointDiscrepancySum H D (q * W) N ≤
      (∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A (2 * N + h.1 - 1)) +
      ∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A (N + h.1 - 1) := by
  have hSQ := compatiblePairShiftModulus_image_subset_radius
    (Nat.pos_of_ne_zero hW.ne_zero) hD
  refine (compatiblePairShiftShiftedEndpointDiscrepancySum_le_shift_sum H D (q * W) N).trans ?_
  apply add_le_add
  · apply Finset.sum_le_sum
    intro h hh
    exact progressionIndexedEndpointBound hw (hupper h) hq hH hW hD hSQ
      (hsizeUpper h) (hcutUpper h)
  · apply Finset.sum_le_sum
    intro h hh
    exact progressionIndexedEndpointBound hw (hlower h) hq hH hW hD hSQ
      (hsizeLower h) (hcutLower h)

theorem progressionRestrictedErrorBound
    {theta A C : ℝ} {X₀ : ℕ} (hw : PrimeLevelWitness theta A C X₀)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v N q : ℕ}
    (hq : 0 < q) (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R (q * W) d)
    (hcoverage : CoversShiftDifferencePrimes H (q * W))
    (hv : ∀ h ∈ H, Nat.Coprime (v + h) (q * W))
    (lambda : (H → ℕ) → ℝ) (L : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L) (hbound : ∀ d ∈ D, |lambda d| ≤ L)
    (hupper : ∀ h : H, X₀ ≤ 2 * N + h.1 - 1)
    (hlower : ∀ h : H, X₀ ≤ N + h.1 - 1)
    (hcutUpper : ∀ h : H, q * (W * R * R) ≤ modulusCutoff theta (2 * N + h.1 - 1))
    (hcutLower : ∀ h : H, q * (W * R * R) ≤ modulusCutoff theta (N + h.1 - 1))
    (hsizeUpper : ∀ h : H, q * (W * R * R) ≤ (2 * N + h.1 - 1) + 1)
    (hsizeLower : ∀ h : H, q * (W * R * R) ≤ (N + h.1 - 1) + 1) :
    |compatiblePairRestrictedErrorOuter H D R (q * W) v N lambda hD| ≤
      L ^ 2 *
        ((∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A (2 * N + h.1 - 1)) +
        ∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A (N + h.1 - 1)) := by
  have hDbase : ∀ d ∈ D, IsMaynardDivisorTuple H R W d := by
    intro d hd
    have h := hD d hd
    exact ⟨h.1, h.2.1.of_dvd_right (Nat.dvd_mul_left W q), h.2.2⟩
  have hWpos : 0 < q * W := mul_pos hq (Nat.pos_of_ne_zero hW.ne_zero)
  calc
    _ ≤ compatiblePairRestrictedAbsoluteErrorOuter H D R (q * W) v N lambda hD :=
      abs_compatiblePairRestrictedErrorOuter_le_absoluteErrorOuter hD
    _ = compatiblePairShiftWeightedShiftedErrorSum H D R (q * W) v N lambda hD :=
      compatiblePairRestrictedAbsoluteErrorOuter_eq_weightedShiftedErrorSum hD
    _ ≤ L ^ 2 * compatiblePairShiftShiftedEndpointDiscrepancySum H D (q * W) N :=
      compatiblePairShiftWeightedShiftedErrorSum_le hWpos hD hcoverage hv hN hL hbound
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (progressionShiftedEndpointBound hw hq hH hW hDbase hupper hlower
        hcutUpper hcutLower hsizeUpper hsizeLower) (sq_nonneg L)

end MaynardBFT
