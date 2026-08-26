import ErdosProblems.Erdos394.PairStateClassification

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Origin-ignored pair-lattice second-moment bound
-/

open Nat Finset

namespace Erdos394

/-- Real weighted sum of positive-square lattice counts over all global label
pairs. -/
noncomputable def pairLatticeWeightedSquareSum
    (P : Finset ℕ) (K Y : ℕ) : ℝ :=
  ∑ f ∈ globalLabelPairs P K,
    (pairMultiplierGlobalWeight P f : ℝ) *
      ((latticePositiveSquare (pairStateLattice P f) Y).card : ℝ)

/-- The weighted leading area terms sum exactly to F-059's corrected square
of the first-moment density. -/
theorem normalized_pairState_area_sum_eq
    (P : Finset ℕ) (K Y : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) :
    (∑ f ∈ globalLabelPairs P K,
      (pairMultiplierGlobalWeight P f : ℝ) *
        ((Y : ℝ) ^ 2 /
          ((primeProduct P * primeProduct (pairStateZeroPrimes P f) : ℕ) : ℝ))) /
        (primeUnitCount P : ℝ) =
      (Y : ℝ) ^ 2 *
        ((((K * K) ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) ^ 2 *
          ∏ p ∈ P,
            (1 + ((K * K - 1 : ℕ) : ℝ) /
              (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)))) := by
  rw [Finset.sum_div]
  calc
    (∑ f ∈ globalLabelPairs P K,
      ((pairMultiplierGlobalWeight P f : ℝ) *
        ((Y : ℝ) ^ 2 /
          ((primeProduct P * primeProduct (pairStateZeroPrimes P f) : ℕ) : ℝ))) /
        (primeUnitCount P : ℝ)) =
      (Y : ℝ) ^ 2 *
        ((∑ f ∈ globalLabelPairs P K,
          ∏ p : ↥P, pairAreaLocalFactor p.val K (f p)) /
          (primeUnitCount P : ℝ)) := by
      rw [show (Y : ℝ) ^ 2 *
          ((∑ f ∈ globalLabelPairs P K,
            ∏ p : ↥P, pairAreaLocalFactor p.val K (f p)) /
            (primeUnitCount P : ℝ)) =
          ((Y : ℝ) ^ 2 *
            (∑ f ∈ globalLabelPairs P K,
              ∏ p : ↥P, pairAreaLocalFactor p.val K (f p))) /
            (primeUnitCount P : ℝ) by ring]
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro f hf
      rw [← pairState_area_factor P K f]
      ring
    _ = (Y : ℝ) ^ 2 *
        ((((K * K) ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) ^ 2 *
          ∏ p ∈ P,
            (1 + ((K * K - 1 : ℕ) : ℝ) /
              (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)))) := by
      rw [normalized_global_area_label_sum_eq P K hK hprime]

/-- Rational selected-vector boundaries are bounded by F-035 and the
constant Euler correction. -/
theorem normalized_rational_pairState_boundary_le
    (P : Finset ℕ) (K Y Z : ℕ) (hK : 1 < K) (hZ : 1 ≤ Z)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hZ2p : ∀ p ∈ P, Z * Z ≤ p) :
    (∑ f ∈ rationalPairStates P K Y hprime hKp,
      (pairMultiplierGlobalWeight P f : ℝ) *
        (40 * ((Y : ℝ) /
          (pairStateSelectedHeight P K Y hprime hKp f : ℝ)))) /
        (primeUnitCount P : ℝ) ≤
      40 * (K * K - 1 : ℕ) *
        ((Y : ℝ) * ((K ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) *
          ∏ p ∈ P,
            (1 + (2 * (K * K - 1 : ℕ) : ℝ) /
              ((K : ℝ) * ((p : ℝ) - 1)))) +
      40 * ∏ _p ∈ P,
        (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
          ((Z * Z : ℕ) : ℝ)) := by
  classical
  let S := rationalPairStates P K Y hprime hKp
  let height := pairStateSelectedHeight P K Y hprime hKp
  let witness := pairStateRationalWitness P K Y hprime hKp
  have hS : S ⊆ globalLabelPairs P K := by
    intro f hf
    exact (Finset.mem_filter.mp hf).1
  have hrat : ∀ f ∈ S,
      pairStateSelectedRational P K Y hprime hKp f := by
    intro f hf
    exact (Finset.mem_filter.mp hf).2
  have hheight : ∀ f ∈ S, 0 < height f := by
    intro f hf
    exact pairStateSelectedHeight_pos P K Y hprime hKp f (hS hf)
  have hwitness : ∀ f ∈ S, witness f ∈ nonzeroLabelPairs K := by
    intro f hf
    exact (pairStateRationalWitness_spec P K Y hprime hKp f (hrat f hf)).1
  have hcompat : ∀ f ∈ S, ∀ p : ↥P, ¬p.val ∣ height f →
      f p ∈ compatibleRatioLabels K (witness f).1 (witness f).2 := by
    intro f hf p hpL
    exact rational_pairState_local_compatible P K Y hprime hKp hK2p
      f (hS hf) (hrat f hf) p hpL
  have hraw := rational_real_boundary_le P K Y (by omega) hprime
    S height witness hS hheight hwitness hcompat
  have hphi : (0 : ℝ) < primeUnitCount P := by
    exact_mod_cast (show 0 < primeUnitCount P by
      unfold primeUnitCount
      exact Finset.prod_pos fun p hp ↦ by
        have hp2 := (hprime p hp).two_le
        omega)
  have hmoment := normalized_rationalBoundaryMoment_le P K (K - 1) Y
    (by omega) hprime hKp (by omega)
  have hconstBase := normalized_pairMultiplierWeight_subset_le P K
    (by omega) hprime S hS
  have hconstCorr := global_constant_label_sum_le P K Z
    (by omega) hZ hprime hZ2p
  have hconst :
      (∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ)) /
          (primeUnitCount P : ℝ) ≤
        ∏ _p ∈ P,
          (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
            ((Z * Z : ℕ) : ℝ)) := hconstBase.trans (by
      rw [← global_constant_label_sum_eq P K (by omega)]
      exact hconstCorr)
  have hdiv := (div_le_div_iff_of_pos_right hphi).mpr hraw
  change
    (∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ) *
      (40 * ((Y : ℝ) / (height f : ℝ)))) /
        (primeUnitCount P : ℝ) ≤ _
  calc
    (∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ) *
      (40 * ((Y : ℝ) / (height f : ℝ)))) /
        (primeUnitCount P : ℝ) ≤
      (40 * (K * K - 1 : ℕ) *
          (rationalBoundaryMoment P K (K - 1) Y : ℝ) +
        40 * ∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ)) /
          (primeUnitCount P : ℝ) := hdiv
    _ = 40 * (K * K - 1 : ℕ) *
          ((rationalBoundaryMoment P K (K - 1) Y : ℝ) /
            (primeUnitCount P : ℝ)) +
        40 * ((∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ)) /
          (primeUnitCount P : ℝ)) := by ring
    _ ≤ 40 * (K * K - 1 : ℕ) *
        ((Y : ℝ) * ((K ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) *
          ∏ p ∈ P,
            (1 + (2 * (K * K - 1 : ℕ) : ℝ) /
              ((K : ℝ) * ((p : ℝ) - 1)))) +
      40 * ∏ _p ∈ P,
        (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
          ((Z * Z : ℕ) : ℝ)) := by
      gcongr

/-- Non-rational selected-vector boundaries retain the decisive reciprocal
prime product after summing every label state. -/
theorem normalized_nonrational_pairState_boundary_le
    (P : Finset ℕ) (K Y Z : ℕ) (hK : 1 < K) (hZ : 1 ≤ Z)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) :
    (∑ f ∈ nonrationalPairStates P K Y hprime hKp,
      (pairMultiplierGlobalWeight P f : ℝ) *
        (40 * ((Y : ℝ) /
          (pairStateSelectedHeight P K Y hprime hKp f : ℝ)))) /
        (primeUnitCount P : ℝ) ≤
      80 * (K : ℝ) * (Y : ℝ) *
        ((1 / (primeProduct P : ℝ)) *
          ∏ _p ∈ P,
            (1 + 4 * ((K * K - 1 : ℕ) : ℝ) / (Z : ℝ))) := by
  classical
  let S := nonrationalPairStates P K Y hprime hKp
  let height := pairStateSelectedHeight P K Y hprime hKp
  have hS : S ⊆ globalLabelPairs P K := by
    intro f hf
    exact (Finset.mem_filter.mp hf).1
  have hnon : ∀ f ∈ S,
      ¬pairStateSelectedRational P K Y hprime hKp f := by
    intro f hf
    exact (Finset.mem_filter.mp hf).2
  have hphi : (0 : ℝ) < primeUnitCount P := by
    exact_mod_cast (show 0 < primeUnitCount P by
      unfold primeUnitCount
      exact Finset.prod_pos fun p hp ↦ by
        have hp2 := (hprime p hp).two_le
        omega)
  have hterm : ∀ f ∈ S,
      ((pairMultiplierGlobalWeight P f : ℝ) *
        (40 * ((Y : ℝ) / (height f : ℝ)))) /
          (primeUnitCount P : ℝ) ≤
        80 * (K : ℝ) * (Y : ℝ) *
          (∏ p : ↥P, pairNonrationalLocalFactor p.val K Z (f p)) := by
    intro f hf
    have hfG := hS hf
    let E := primeProduct (pairStateZeroPrimes P f) *
      Z ^ (P \ pairStateZeroPrimes P f).card
    have hE : E ≤ 2 * K * height f :=
      nonrational_pairState_height P K Y Z hprime hK hKp hlarge
        f hfG (hnon f hf)
    have hEpos : 0 < E := by
      dsimp [E]
      apply Nat.mul_pos
      · unfold primeProduct
        exact Finset.prod_pos fun p hp ↦
          (hprime p (Finset.mem_filter.mp hp).1).pos
      · exact pow_pos (Nat.zero_lt_of_lt hZ) _
    have hLpos : 0 < height f :=
      pairStateSelectedHeight_pos P K Y hprime hKp f hfG
    have hER : (0 : ℝ) < E := by exact_mod_cast hEpos
    have hLR : (0 : ℝ) < height f := by exact_mod_cast hLpos
    have hheightR : (E : ℝ) ≤ 2 * (K : ℝ) * (height f : ℝ) := by
      exact_mod_cast hE
    have hboundary :
        (40 : ℝ) * ((Y : ℝ) / (height f : ℝ)) ≤
          80 * (K : ℝ) * (Y : ℝ) / (E : ℝ) := by
      rw [show (40 : ℝ) * ((Y : ℝ) / (height f : ℝ)) =
          (40 * (Y : ℝ)) / (height f : ℝ) by ring,
        show (80 : ℝ) * (K : ℝ) * (Y : ℝ) / (E : ℝ) =
          (80 * (K : ℝ) * (Y : ℝ)) / (E : ℝ) by ring]
      apply (div_le_div_iff₀ hLR hER).mpr
      have hY0 : (0 : ℝ) ≤ Y := by positivity
      nlinarith
    have hwphi : 0 ≤
        (pairMultiplierGlobalWeight P f : ℝ) /
          (primeUnitCount P : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hboundary hwphi
    have hfactor := pairState_nonrational_factor P K Z f hprime
      (Nat.zero_lt_of_lt hZ)
    have hcastE : (E : ℝ) =
        (primeProduct (pairStateZeroPrimes P f) : ℝ) *
          ((Z ^ (P \ pairStateZeroPrimes P f).card : ℕ) : ℝ) := by
      dsimp [E]
      push_cast
      rfl
    rw [← hcastE] at hfactor
    change ((pairMultiplierGlobalWeight P f : ℝ) *
        (40 * ((Y : ℝ) / (height f : ℝ)))) /
          (primeUnitCount P : ℝ) ≤ _
    calc
      ((pairMultiplierGlobalWeight P f : ℝ) *
        (40 * ((Y : ℝ) / (height f : ℝ)))) /
          (primeUnitCount P : ℝ) =
        ((pairMultiplierGlobalWeight P f : ℝ) /
          (primeUnitCount P : ℝ)) *
          (40 * ((Y : ℝ) / (height f : ℝ))) := by ring
      _ ≤ ((pairMultiplierGlobalWeight P f : ℝ) /
          (primeUnitCount P : ℝ)) *
          (80 * (K : ℝ) * (Y : ℝ) / (E : ℝ)) := hmul
      _ = 80 * (K : ℝ) * (Y : ℝ) *
          (∏ p : ↥P, pairNonrationalLocalFactor p.val K Z (f p)) := by
        rw [← hfactor]
        ring
  rw [Finset.sum_div]
  calc
    (∑ f ∈ S, ((pairMultiplierGlobalWeight P f : ℝ) *
      (40 * ((Y : ℝ) / (height f : ℝ)))) /
        (primeUnitCount P : ℝ)) ≤
      ∑ f ∈ S, 80 * (K : ℝ) * (Y : ℝ) *
        (∏ p : ↥P, pairNonrationalLocalFactor p.val K Z (f p)) :=
      Finset.sum_le_sum hterm
    _ = 80 * (K : ℝ) * (Y : ℝ) *
        (∑ f ∈ S,
          ∏ p : ↥P, pairNonrationalLocalFactor p.val K Z (f p)) := by
      rw [Finset.mul_sum]
    _ ≤ 80 * (K : ℝ) * (Y : ℝ) *
        (∑ f ∈ globalLabelPairs P K,
          ∏ p : ↥P, pairNonrationalLocalFactor p.val K Z (f p)) := by
      gcongr
      intro f hf hnot
      apply Finset.prod_nonneg
      intro p hp
      unfold pairNonrationalLocalFactor
      split_ifs <;> positivity
    _ ≤ 80 * (K : ℝ) * (Y : ℝ) *
        ((1 / (primeProduct P : ℝ)) *
          ∏ _p ∈ P,
            (1 + 4 * ((K * K - 1 : ℕ) : ℝ) / (Z : ℝ))) := by
      gcongr
      exact global_nonrational_label_sum_le P K Z (by omega) hZ
        hprime hZp

/-- The additive `+4` lattice errors sum to at most four copies of the
constant Euler correction. -/
theorem normalized_pairState_constant_le
    (P : Finset ℕ) (K Z : ℕ) (hK : 0 < K) (hZ : 1 ≤ Z)
    (hprime : ∀ p ∈ P, p.Prime) (hZ2p : ∀ p ∈ P, Z * Z ≤ p) :
    (4 * ∑ f ∈ globalLabelPairs P K,
      (pairMultiplierGlobalWeight P f : ℝ)) /
        (primeUnitCount P : ℝ) ≤
      4 * ∏ _p ∈ P,
        (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
          ((Z * Z : ℕ) : ℝ)) := by
  have hbase := normalized_pairMultiplierWeight_subset_le P K hK hprime
    (globalLabelPairs P K) (by exact fun _ h ↦ h)
  have hcorr := global_constant_label_sum_le P K Z hK hZ hprime hZ2p
  have htotal :
      (∑ f ∈ globalLabelPairs P K,
        (pairMultiplierGlobalWeight P f : ℝ)) /
          (primeUnitCount P : ℝ) ≤
        ∏ _p ∈ P,
          (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
            ((Z * Z : ℕ) : ℝ)) := hbase.trans (by
      rw [← global_constant_label_sum_eq P K hK]
      exact hcorr)
  calc
    (4 * ∑ f ∈ globalLabelPairs P K,
      (pairMultiplierGlobalWeight P f : ℝ)) /
        (primeUnitCount P : ℝ) =
      4 * ((∑ f ∈ globalLabelPairs P K,
        (pairMultiplierGlobalWeight P f : ℝ)) /
          (primeUnitCount P : ℝ)) := by ring
    _ ≤ 4 * ∏ _p ∈ P,
        (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
          ((Z * Z : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left htotal (by norm_num)

/-- Complete origin-ignored pair-lattice square bound.  The only change from
an exactly cancelled second moment is the explicit area Euler correction. -/
theorem normalized_pairLatticeWeightedSquareSum_le
    (P : Finset ℕ) (K Y Z : ℕ) (hK : 1 < K) (hZ : 1 ≤ Z)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p) :
    pairLatticeWeightedSquareSum P K Y /
        (primeUnitCount P : ℝ) ≤
      (Y : ℝ) ^ 2 *
        ((((K * K) ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) ^ 2 *
          ∏ p ∈ P,
            (1 + ((K * K - 1 : ℕ) : ℝ) /
              (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)))) +
      40 * (K * K - 1 : ℕ) *
        ((Y : ℝ) * ((K ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) *
          ∏ p ∈ P,
            (1 + (2 * (K * K - 1 : ℕ) : ℝ) /
              ((K : ℝ) * ((p : ℝ) - 1)))) +
      80 * (K : ℝ) * (Y : ℝ) *
        ((1 / (primeProduct P : ℝ)) *
          ∏ _p ∈ P,
            (1 + 4 * ((K * K - 1 : ℕ) : ℝ) / (Z : ℝ))) +
      44 * ∏ _p ∈ P,
        (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
          ((Z * Z : ℕ) : ℝ)) := by
  classical
  let G := globalLabelPairs P K
  let rat := pairStateSelectedRational P K Y hprime hKp
  let height := pairStateSelectedHeight P K Y hprime hKp
  let areaRaw : ℝ := ∑ f ∈ G,
    (pairMultiplierGlobalWeight P f : ℝ) *
      ((Y : ℝ) ^ 2 /
        ((primeProduct P * primeProduct (pairStateZeroPrimes P f) : ℕ) : ℝ))
  let boundaryRaw : ℝ := ∑ f ∈ G,
    (pairMultiplierGlobalWeight P f : ℝ) *
      (40 * ((Y : ℝ) / (height f : ℝ)))
  let weightRaw : ℝ := ∑ f ∈ G, (pairMultiplierGlobalWeight P f : ℝ)
  have hphi : (0 : ℝ) < primeUnitCount P := by
    exact_mod_cast (show 0 < primeUnitCount P by
      unfold primeUnitCount
      exact Finset.prod_pos fun p hp ↦ by
        have hp2 := (hprime p hp).two_le
        omega)
  have hraw : pairLatticeWeightedSquareSum P K Y ≤
      areaRaw + boundaryRaw + 4 * weightRaw := by
    unfold pairLatticeWeightedSquareSum areaRaw boundaryRaw weightRaw G height
    calc
      (∑ f ∈ globalLabelPairs P K,
        (pairMultiplierGlobalWeight P f : ℝ) *
          ((latticePositiveSquare (pairStateLattice P f) Y).card : ℝ)) ≤
        ∑ f ∈ globalLabelPairs P K,
          (pairMultiplierGlobalWeight P f : ℝ) *
            (((Y : ℝ) ^ 2 /
              ((primeProduct P * primeProduct (pairStateZeroPrimes P f) : ℕ) : ℝ)) +
             40 * ((Y : ℝ) /
              (pairStateSelectedHeight P K Y hprime hKp f : ℝ)) + 4) := by
          apply Finset.sum_le_sum
          intro f hf
          exact mul_le_mul_of_nonneg_left
            (pairStateSelected_count_le P K Y hprime hKp f hf)
            (by positivity)
      _ = (∑ f ∈ globalLabelPairs P K,
          (pairMultiplierGlobalWeight P f : ℝ) *
            ((Y : ℝ) ^ 2 /
              ((primeProduct P * primeProduct (pairStateZeroPrimes P f) : ℕ) : ℝ))) +
          (∑ f ∈ globalLabelPairs P K,
            (pairMultiplierGlobalWeight P f : ℝ) *
              (40 * ((Y : ℝ) /
                (pairStateSelectedHeight P K Y hprime hKp f : ℝ)))) +
          4 * ∑ f ∈ globalLabelPairs P K,
            (pairMultiplierGlobalWeight P f : ℝ) := by
        rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro f hf
        ring
  have hdiv := (div_le_div_iff_of_pos_right hphi).mpr hraw
  have hboundarySplit : boundaryRaw /
      (primeUnitCount P : ℝ) =
      (∑ f ∈ rationalPairStates P K Y hprime hKp,
        (pairMultiplierGlobalWeight P f : ℝ) *
          (40 * ((Y : ℝ) / (height f : ℝ)))) /
          (primeUnitCount P : ℝ) +
      (∑ f ∈ nonrationalPairStates P K Y hprime hKp,
        (pairMultiplierGlobalWeight P f : ℝ) *
          (40 * ((Y : ℝ) / (height f : ℝ)))) /
          (primeUnitCount P : ℝ) := by
    unfold boundaryRaw G rationalPairStates nonrationalPairStates
    rw [← Finset.sum_filter_add_sum_filter_not
      (globalLabelPairs P K) rat (fun f ↦
        (pairMultiplierGlobalWeight P f : ℝ) *
          (40 * ((Y : ℝ) / (height f : ℝ))))]
    ring
  have harea := normalized_pairState_area_sum_eq P K Y (by omega) hprime
  have hrat := normalized_rational_pairState_boundary_le P K Y Z hK hZ
    hprime hKp hK2p hZ2p
  have hnon := normalized_nonrational_pairState_boundary_le P K Y Z hK hZ
    hprime hKp hlarge hZp
  have hconst := normalized_pairState_constant_le P K Z (by omega) hZ
    hprime hZ2p
  calc
    pairLatticeWeightedSquareSum P K Y /
        (primeUnitCount P : ℝ) ≤
      (areaRaw + boundaryRaw + 4 * weightRaw) /
        (primeUnitCount P : ℝ) := hdiv
    _ = areaRaw / (primeUnitCount P : ℝ) +
        boundaryRaw / (primeUnitCount P : ℝ) +
        (4 * weightRaw) / (primeUnitCount P : ℝ) := by ring
    _ = areaRaw / (primeUnitCount P : ℝ) +
        ((∑ f ∈ rationalPairStates P K Y hprime hKp,
          (pairMultiplierGlobalWeight P f : ℝ) *
            (40 * ((Y : ℝ) / (height f : ℝ)))) /
            (primeUnitCount P : ℝ) +
         (∑ f ∈ nonrationalPairStates P K Y hprime hKp,
          (pairMultiplierGlobalWeight P f : ℝ) *
            (40 * ((Y : ℝ) / (height f : ℝ)))) /
            (primeUnitCount P : ℝ)) +
        (4 * weightRaw) / (primeUnitCount P : ℝ) := by rw [hboundarySplit]
    _ ≤ (Y : ℝ) ^ 2 *
        ((((K * K) ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) ^ 2 *
          ∏ p ∈ P,
            (1 + ((K * K - 1 : ℕ) : ℝ) /
              (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)))) +
      (40 * (K * K - 1 : ℕ) *
        ((Y : ℝ) * ((K ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) *
          ∏ p ∈ P,
            (1 + (2 * (K * K - 1 : ℕ) : ℝ) /
              ((K : ℝ) * ((p : ℝ) - 1)))) +
       40 * ∏ _p ∈ P,
        (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
          ((Z * Z : ℕ) : ℝ))) +
      (80 * (K : ℝ) * (Y : ℝ) *
        ((1 / (primeProduct P : ℝ)) *
          ∏ _p ∈ P,
            (1 + 4 * ((K * K - 1 : ℕ) : ℝ) / (Z : ℝ)))) +
      4 * ∏ _p ∈ P,
        (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
          ((Z * Z : ℕ) : ℝ)) := by
      dsimp [areaRaw, weightRaw, G, height] at harea hconst ⊢
      rw [harea]
      nlinarith [hrat, hnon, hconst]
    _ = (Y : ℝ) ^ 2 *
        ((((K * K) ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) ^ 2 *
          ∏ p ∈ P,
            (1 + ((K * K - 1 : ℕ) : ℝ) /
              (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)))) +
      40 * (K * K - 1 : ℕ) *
        ((Y : ℝ) * ((K ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) *
          ∏ p ∈ P,
            (1 + (2 * (K * K - 1 : ℕ) : ℝ) /
              ((K : ℝ) * ((p : ℝ) - 1)))) +
      80 * (K : ℝ) * (Y : ℝ) *
        ((1 / (primeProduct P : ℝ)) *
          ∏ _p ∈ P,
            (1 + 4 * ((K * K - 1 : ℕ) : ℝ) / (Z : ℝ))) +
      44 * ∏ _p ∈ P,
        (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
          ((Z * Z : ℕ) : ℝ)) := by ring

end Erdos394
