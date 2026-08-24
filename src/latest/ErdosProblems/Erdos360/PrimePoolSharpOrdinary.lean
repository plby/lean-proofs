/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.InverseSourceAdaptiveData
import ErdosProblems.Erdos360.StructuredPhaseRemainder
import ErdosProblems.Erdos360.PrimeRandomAssembly
import ErdosProblems.Erdos360.StructuredPhaseDiversity

/-!
# Sharp ordinary growth for one prime-structured random pool

This is the finite form of CFP Lemma 5.6.  Its numerical record contains
only scalar inequalities; the proof below supplies the adaptive recursion,
canonical closure coordinates, structured coprimality, the complete local
inverse theorem, and the bounded-step sieve connector.
-/

namespace Erdos360

open scoped BigOperators

attribute [local instance] Classical.propDecidable

def primePoolSharpPhaseCount (z ell : ℕ) : ℕ :=
  primeRandomPoolSize z ell / 16

noncomputable def primePoolSharpGrowthThreshold (y : ℕ) : ℕ :=
  fourthRootCeil y ^ 3

def primePoolSharpLargeGain (z ell : ℕ) : ℕ :=
  primeRandomPoolSize z ell / 128

def primePoolSharpIncrement (y z : ℕ) : ℕ :=
  65536 * y / z + 1

def primePoolSharpResidueTarget (y z ell d : ℕ) : ℕ :=
  primeRandomNzero y z ell d ⌈/⌉ (primeRandomPoolSize z ell / 4)

def primePoolSharpRemainderFloor (z ell : ℕ) : ℕ :=
  primeRandomPoolSize z ell / 4 - primePoolSharpPhaseCount z ell

/-- Exact scalar hypotheses for the sharp one-pool theorem.  Quantification
over `t`, `q`, and `u` is finite arithmetic: these are respectively a pivot,
its closure modulus, and the selected fibre cardinality. -/
structure CFPPrimePoolSharpNumerics
    (A C ratio : ℝ) (n sieveLevel sieveCutoff sieveQ : ℕ)
    (y cutoff z ell d : ℕ) : Prop where
  probability :
    (2 : ℝ) * (((2 * y / d : ℕ) : ℝ) + 1) *
      Real.exp (-(primeRandomPoolDiversity y ell : ℝ) / 24) < 1
  diversity_pos : 0 < primeRandomPoolDiversity y ell
  half : 2 * primePoolSharpPhaseCount z ell ≤
    primeRandomPoolSize z ell / 4
  cutoff_room : cutoff + primePoolSharpPhaseCount z ell <
    primeRandomPoolSize z ell / 4
  source_room : 2 * cutoff < primeRandomPoolSize z ell / 4
  diversity_room : cutoff ≤ primeRandomPoolDiversity y ell / 4 + 1
  largeGain_pos : 0 < primePoolSharpLargeGain z ell
  largeGain_room :
    16 * primePoolSharpLargeGain z ell + primePoolSharpPhaseCount z ell ≤
      primeRandomPoolSize z ell / 4
  increment_gt_one : 1 < primePoolSharpIncrement y z
  increment_below_threshold :
    64 * (primePoolSharpIncrement y z - 1) ≤
      primePoolSharpGrowthThreshold y
  growth_ambient : ∀ t q : ℕ,
    y / d + 1 ≤ t → t ≤ 2 * y / d →
    0 < q → q ∣ t → d * q ≤ cutoff →
    4 * primePoolSharpGrowthThreshold y < t / q
  growth_budget : ∀ t : ℕ,
    y / d + 1 ≤ t → t ≤ 2 * y / d →
    (Nat.log 2 t + 1) *
        (2 * (Nat.log 2 t + 1) +
          (primePoolSharpGrowthThreshold y /
            primePoolSharpLargeGain z ell + 1)) ≤
      primePoolSharpPhaseCount z ell
  unsaturated_budget : ∀ t : ℕ,
    y / d + 1 ≤ t → t ≤ 2 * y / d →
    primePoolSharpResidueTarget y z ell d ≤
      primePoolSharpIncrement y z *
        (primePoolSharpPhaseCount z ell -
          (Nat.log 2 t + 1) *
            (2 * (Nat.log 2 t + 1) +
              (primePoolSharpGrowthThreshold y /
                primePoolSharpLargeGain z ell + 1)))
  fiber_ambient : ∀ t q u : ℕ,
    y / d + 1 ≤ t → t ≤ 2 * y / d →
    0 < q → q ∣ t → d * q ≤ cutoff →
    primePoolSharpGrowthThreshold y < u →
    u < sourceAdaptiveCeilSaturation
      (primePoolSharpResidueTarget y z ell d) q →
    2000000000 * u ≤ t / q
  polynomial_reverse : ∀ u : ℕ,
    primePoolSharpGrowthThreshold y < u →
    u < primePoolSharpResidueTarget y z ell d + 1 →
    2 ^ 712 * u ^ 100 <
      (u / (2 * (primePoolSharpIncrement y z - 1))) ^ 102 *
        primePoolSharpRemainderFloor z ell ^ 100
  n_pos : 0 < n
  sieveCutoff_ge : 2 ≤ sieveCutoff
  sieveLevel_ge : 101 ≤ sieveLevel
  sieveQ_pos : 0 < sieveQ
  log_bound : Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99
  ratio_nonneg : 0 ≤ ratio
  ratio_bound : ∀ step : ℕ, 0 < step → step ≤ 2 * y / d →
    ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio
  long_scale :
    (sieveQ * (sieveCutoff ^ sieveLevel) ^ 2) ^ 3 ≤
      primePoolSharpRemainderFloor z ell
  sieve_reverse : ∀ u : ℕ,
    primePoolSharpGrowthThreshold y < u →
    u < primePoolSharpResidueTarget y z ell d + 1 →
    (((192 * 48 : ℕ) : ℝ) * (primePoolSharpIncrement y z - 1)) *
        (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
            (C * ratio / Real.log (sieveCutoff : ℝ))) +
              1 / (sieveQ : ℝ)) <
      primePoolSharpRemainderFloor z ell
  sum : primeRandomPoolSize z ell * (2 * y / d) ≤
    primeRandomDiameter y z ell d

/-- The sharp finite ordinary-growth theorem in the full
prime-structured source context. -/
theorem exists_primePoolOrdinaryGrowthCertificate_of_sharp_numerics
    (A C : ℝ)
    (hsieve :
      ∀ n y sieveLevel K growth target stepBound Q : ℕ,
        ∀ X : Finset ℕ, ∀ ratio : ℝ,
        0 < n → 2 ≤ y → 101 ≤ sieveLevel → 0 < Q →
        Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ X.card →
        0 ≤ ratio →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)
        let V := C * ratio / Real.log (y : ℝ)
        ((K : ℝ) * target) * (((1 + eta) * V) + 1 / (Q : ℝ)) <
            (X.card : ℝ) →
        target < growth)
    {n y cutoff d z ell sieveLevel sieveCutoff sieveQ : ℕ}
    {W Z P : Finset ℕ} (ratio : ℝ)
    (hd : 0 < d) (hdn : d ∣ n) (hcutoff : 0 < cutoff)
    (hB : sieveCutoff ≤ y / cutoff)
    (hW : W ⊆ primeStructuredTestSet n y cutoff)
    (hscale : ∀ a ∈ Z, d * a ∈ W)
    (hPZ : P ⊆ Z)
    (hcard : P.card = primeRandomPoolSize z ell)
    (hrange : P ⊆ Finset.Icc (y / d + 1) (2 * y / d))
    (hdiverse : DiverseSampling.DiverseNat P
      (primeRandomPoolDiversity y ell))
    (hnum : CFPPrimePoolSharpNumerics A C ratio n sieveLevel sieveCutoff
      sieveQ y cutoff z ell d) :
    Nonempty (CFPOrdinaryGrowthCertificate P
      (primeRandomNzero y z ell d)
      (primeRandomDiameter y z ell d)) := by
  let m := primeRandomPoolSize z ell
  let K := primeRandomPoolDiversity y ell
  let k := primePoolSharpPhaseCount z ell
  let phaseQ := primePoolSharpGrowthThreshold y
  let L := primePoolSharpLargeGain z ell
  let D := primePoolSharpIncrement y z
  let target := primePoolSharpResidueTarget y z ell d
  let sat := sourceAdaptiveCeilSaturation target
  let lo := y / d + 1
  have hPico : P ⊆ Finset.Ico lo (2 * y / d + 1) := by
    intro a ha
    have haI := Finset.mem_Icc.mp (hrange ha)
    exact Finset.mem_Ico.mpr ⟨haI.1, by omega⟩
  have hrangePos : ∀ a ∈ P, 0 < a ∧ a ≤ 2 * y / d := by
    intro a ha
    have haI := Finset.mem_Icc.mp (hrange ha)
    exact ⟨(Nat.zero_lt_succ (y / d)).trans_le haI.1, haI.2⟩
  obtain ⟨seed, hseedP, hseedDiverse, hpivotDiverse,
      hseedCard, hpivotCard⟩ :=
    DiverseSampling.exists_balanced_diverse_bisection
      hdiverse hrangePos hnum.probability
  let pivots := P \ seed
  have hseedCardM : m / 4 ≤ seed.card := by
    simpa [m, hcard] using hseedCard
  have hpivotCardM : m / 4 ≤ pivots.card := by
    simpa [m, pivots, hcard] using hpivotCard
  have hpivotsP : pivots ⊆ P := Finset.sdiff_subset
  have hseedRange : seed ⊆ Finset.Ico lo (2 * y / d + 1) :=
    hseedP.trans hPico
  have hpivotsRange : pivots ⊆ Finset.Ico lo (2 * y / d + 1) :=
    hpivotsP.trans hPico
  have hseedZ : seed ⊆ Z := hseedP.trans hPZ
  have hpivotsZ : pivots ⊆ Z := hpivotsP.trans hPZ
  have hunion : seed ∪ pivots = P := Finset.union_sdiff_of_subset hseedP
  have hdisjoint : Disjoint seed pivots := Finset.disjoint_sdiff
  have hresidue : ∀ t ∈ pivots,
      target ≤ (occupiedResidues seed.subsetSum t).card := by
    intro t htPivot
    have htI := Finset.mem_Ico.mp (hpivotsRange htPivot)
    have htpos : 0 < t := (Nat.zero_lt_succ (y / d)).trans_le htI.1
    letI : NeZero t := ⟨htpos.ne'⟩
    let R₀ := ordinaryResidues t seed
    have hwidth : (2 * y / d + 1) - lo ≤ t := by
      have htwo := Nat.add_div_le_div_add_div_add_one y y d
      have hupper : 2 * y / d ≤ y / d + y / d + 1 := by
        simpa [two_mul] using htwo
      dsimp only [lo]
      omega
    have hphaseDiverse : PhaseDiverse htpos R₀ := by
      apply phaseDiverse_of_primeStructured_extraction
        htpos hd hdn hW hscale hseedZ (hpivotsZ htPivot)
        hseedRange hwidth hseedDiverse
      · exact hnum.source_room.trans_le hseedCardM
      · exact hnum.diversity_room
    have hR₀card : R₀.card = seed.card :=
      card_image_zmod_eq_of_subset_Ico seed hseedRange hwidth
    have hik : ∀ i < k, i ≤ R₀.card := by
      intro i hi
      rw [hR₀card]
      have hroom : cutoff + k < m / 4 := by
        simpa [k, m] using hnum.cutoff_room
      omega
    have h2ik : ∀ i < k, 2 * i ≤ R₀.card := by
      intro i hi
      rw [hR₀card]
      have hhalf : 2 * k ≤ m / 4 := by
        simpa [k, m] using hnum.half
      omega
    have hdata : Nonempty
        (CFPSourceAdaptiveSharpSelectorData htpos R₀ hphaseDiverse
          target) := by
      refine exists_CFPSourceAdaptiveSharpSelectorData_of_normalizedFiberLossConditions
        A C hsieve htpos R₀ hphaseDiverse target phaseQ D L k
          target target sat n sieveCutoff sieveLevel sieveQ 48 ratio
          ?_ ?_ ?_ ?_ ?_
          (fun i _hi _hu ↦ by
            let R := sourceAdaptiveRemainder htpos R₀ {0} (by simp)
              hphaseDiverse phaseQ i
            exact closureZModEquiv htpos R)
          (fun i _hi _hu ↦
            let R := sourceAdaptiveRemainder htpos R₀ {0} (by simp)
              hphaseDiverse phaseQ i
            let q := closureModulus htpos R
            lo ⌈/⌉ q)
          ?_ ?_ ?_ ?_ ?_
      · exact Nat.zero_lt_succ _
      · exact hnum.largeGain_pos
      · rw [hR₀card]
        exact hnum.half.trans hseedCardM
      · intro i hi
        let R := sourceAdaptiveRemainder htpos R₀ {0} (by simp)
          hphaseDiverse phaseQ i
        let Pᵢ := sourceAdaptiveIntegerRemainder htpos seed
          hphaseDiverse phaseQ i
        let q := closureModulus htpos R
        have hRsub : R ⊆ R₀ :=
          sourceAdaptiveRemainder_subset_initial
            htpos R₀ {0} (by simp) hphaseDiverse phaseQ i
        have hRcard : R.card = R₀.card - i :=
          card_sourceAdaptiveRemainder htpos R₀ {0} (by simp)
            hphaseDiverse phaseQ (hik i hi)
        have hwide : cutoff < R.card := by
          rw [hRcard, hR₀card]
          have hroom : cutoff + k < m / 4 := by
            simpa [k, m] using hnum.cutoff_room
          omega
        have hscaled : d * q ≤ cutoff := by
          apply scale_mul_closureModulus_le_cutoff_of_primeStructured_remainder
            htpos hd hdn hW hscale hseedZ (hpivotsZ htPivot)
            hseedRange hwidth hRsub hwide
        have hqpos : 0 < q := closureModulus_pos htpos R
        have hqdiv : q ∣ t := closureModulus_dvd htpos R
        rw [natCard_closure_eq_div_modulus]
        exact hnum.growth_ambient t q htI.1 (by omega) hqpos hqdiv hscaled
      · intro i hi
        rw [card_sourceAdaptiveRemainder htpos R₀ {0} (by simp)
          hphaseDiverse phaseQ (hik i hi), hR₀card]
        have hroom : 16 * L + k ≤ m / 4 := by
          simpa [L, k, m] using hnum.largeGain_room
        omega
      · intro i hi hu
        let R := sourceAdaptiveRemainder htpos R₀ {0} (by simp)
          hphaseDiverse phaseQ i
        let H := AddSubgroup.closure (R : Set (ZMod t))
        let Uᵢ := sourceAdaptiveFiber R₀ {0} R
          (sourceAdaptiveMinFiberCenter R₀ {0} R)
        let X := liftFinsetToClosure R
        let Pᵢ := sourceAdaptiveIntegerRemainder htpos seed
          hphaseDiverse phaseQ i
        let q := closureModulus htpos R
        have hbounds := sourceAdaptiveMinFiber_bounds_of_unsaturated
          htpos R₀ {0} (by simp) hphaseDiverse phaseQ sat
            (i := i) (h2ik i hi) hu
        have hRsub : R ⊆ R₀ :=
          sourceAdaptiveRemainder_subset_initial
            htpos R₀ {0} (by simp) hphaseDiverse phaseQ i
        have hRcard : R.card = R₀.card - i :=
          card_sourceAdaptiveRemainder htpos R₀ {0} (by simp)
            hphaseDiverse phaseQ (hik i hi)
        have hRfloor : primePoolSharpRemainderFloor z ell ≤ R.card := by
          rw [hRcard, hR₀card]
          dsimp only [primePoolSharpRemainderFloor]
          omega
        have hwide : cutoff < R.card := by
          rw [hRcard, hR₀card]
          have hroom : cutoff + k < m / 4 := by
            simpa [k, m] using hnum.cutoff_room
          omega
        have hscaled : d * q ≤ cutoff := by
          apply scale_mul_closureModulus_le_cutoff_of_primeStructured_remainder
            htpos hd hdn hW hscale hseedZ (hpivotsZ htPivot)
            hseedRange hwidth hRsub hwide
        have hqpos : 0 < q := closureModulus_pos htpos R
        have hqdiv : q ∣ t := closureModulus_dvd htpos R
        have hHcard : Nat.card H = t / q := by
          simpa [H, q] using natCard_closure_eq_div_modulus htpos R
        have hUcard :
            (equivCoordinates (closureZModEquiv htpos R) Uᵢ).card =
              Uᵢ.card := card_equivCoordinates _ _
        have hXcard :
            (equivCoordinates (closureZModEquiv htpos R) X).card = R.card := by
          rw [card_equivCoordinates, card_liftFinsetToClosure]
        have hUgt : phaseQ < Uᵢ.card := by
          simpa [R, Uᵢ] using hbounds.2.1
        have hUlt : Uᵢ.card < sourceAdaptiveCeilSaturation target q := by
          simpa [R, Uᵢ, q, sourceAdaptiveModulus, sat] using hbounds.2.2
        have hUltTarget : Uᵢ.card < target + 1 := by
          exact hUlt.trans_le (by
            unfold sourceAdaptiveCeilSaturation
            apply (ceilDiv_le_iff_le_mul hqpos).2
            exact (Nat.le_mul_of_pos_left target hqpos).trans
              (Nat.mul_le_mul_left q (Nat.le_succ target)))
        change NormalizedFiberLossPhaseConditions A C n sieveCutoff
          sieveLevel sieveQ 48 (D - 1) ratio (closureZModEquiv htpos R)
            (lo ⌈/⌉ q) Uᵢ X
        refine
          { base_le := ?_
            U_nonempty := ?_
            e_pos := by
              exact Nat.sub_pos_of_lt (by
                simpa [D] using hnum.increment_gt_one)
            large := ?_
            five_levels := ?_
            kappa_pos := by norm_num
            kappa_sparse := by norm_num
            ambient := ?_
            polynomial_reverse := ?_
            localDF := ?_
            n_pos := hnum.n_pos
            y_ge := hnum.sieveCutoff_ge
            sieveLevel_ge := hnum.sieveLevel_ge
            Q_pos := hnum.sieveQ_pos
            log_bound := hnum.log_bound
            coprime := ?_
            long_scale := ?_
            ratio_nonneg := hnum.ratio_nonneg
            ratio_bound := ?_
            sieve_reverse := ?_ }
        · exact ceilDiv_closureModulus_le_card htpos R htI.1
        · exact Finset.card_pos.mp (by
            rw [hUcard]
            exact Finset.card_pos.mpr hbounds.1)
        · rw [hUcard]
          have h64 := hnum.increment_below_threshold
          dsimp only [D, phaseQ] at h64 ⊢
          omega
        · rw [hUcard]
          exact hnum.increment_below_threshold.trans hUgt.le
        · rw [hUcard, hHcard]
          exact hnum.fiber_ambient t q Uᵢ.card htI.1 (by omega)
            hqpos hqdiv hscaled hUgt hUlt
        · rw [hUcard, hXcard]
          exact (hnum.polynomial_reverse Uᵢ.card hUgt hUltTarget).trans_le
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hRfloor 100))
        · intro j hj _hjlog hsparse hsmall
          apply cfpLocalDyadicInverseAlternativeWithLoss_48_at_five
            (equivCoordinates (closureZModEquiv htpos R) Uᵢ)
            (D - 1) j hj
          · simpa [hHcard] using hsparse
          · simpa [dyadicFinsetSum_succ] using hsmall
        · have hPiResidues : ordinaryResidues t Pᵢ = R := by
            simpa [Pᵢ, R] using
              ordinaryResidues_sourceAdaptiveIntegerRemainder
                htpos seed hphaseDiverse phaseQ i
          have hPiLo : ∀ p ∈ Pᵢ, lo ≤ p := by
            intro p hp
            exact (Finset.mem_Ico.mp (hseedRange
              (sourceAdaptiveIntegerRemainder_subset
                htpos seed hphaseDiverse phaseQ i hp))).1
          have hPiHi : ∀ p ∈ Pᵢ, p < lo + t := by
            intro p hp
            have hpI := Finset.mem_Ico.mp (hseedRange
              (sourceAdaptiveIntegerRemainder_subset
                htpos seed hphaseDiverse phaseQ i hp))
            omega
          have hPiCop : ∀ p ∈ Pᵢ,
              Nat.Coprime (missingPrimeProduct n sieveCutoff) p := by
            intro p hp
            exact primeStructured_extracted_set_coprime_missingPrimeProduct_le_cutoff
              hcutoff hB hdn hW hscale p
                (hseedZ (sourceAdaptiveIntegerRemainder_subset
                  htpos seed hphaseDiverse phaseQ i hp))
          have hc := interval_equivCoordinates_closure_coprime_any
            htpos Pᵢ htI.1 hPiLo hPiHi hPiCop
          rw [hPiResidues] at hc
          simpa [q] using hc
        · rw [card_intervalZmodValues, hXcard]
          exact hnum.long_scale.trans hRfloor
        · intro step hstep hstepH
          apply hnum.ratio_bound step hstep
          have hstepT : step ≤ t := hstepH.trans (by
            rw [hHcard]
            exact Nat.div_le_self _ _)
          omega
        · rw [hXcard]
          have hfloorReal :
              (primePoolSharpRemainderFloor z ell : ℝ) ≤ (R.card : ℝ) := by
            exact_mod_cast hRfloor
          have honeD : 1 ≤ D := by
            simpa [D] using hnum.increment_gt_one.le
          rw [Nat.cast_sub honeD]
          simpa [D] using
            (hnum.sieve_reverse Uᵢ.card hUgt hUltTarget).trans_le
              hfloorReal
      · intro i hi
        exact sourceAdaptiveCeilSaturation_bound
          (closureModulus_pos htpos
            (sourceAdaptiveRemainder htpos R₀ {0} (by simp)
              hphaseDiverse phaseQ i))
      · exact hnum.growth_budget t htI.1 (by omega)
      · exact hnum.unsaturated_budget t htI.1 (by omega)
      · exact le_min rfl.le rfl.le
    exact occupiedResidues_lower_of_source_adaptive_sharp_selector
      htpos seed hphaseDiverse hdata.some
  refine ⟨
    { seed := seed
      pivots := pivots
      residueGain := target
      diversity := K
      union_eq := hunion
      disjoint := hdisjoint
      pivots_pos := ?_
      residues := hresidue
      target := ?_
      diversity_pos := hnum.diversity_pos
      diverse := by simpa [K, hunion] using hdiverse
      sum_le := ?_ }⟩
  · intro t ht
    have htI := Finset.mem_Ico.mp (hpivotsRange ht)
    exact (Nat.zero_lt_succ (y / d)).trans_le htI.1
  · have hquarter : 0 < m / 4 := by
      have hhalf' : 2 * k ≤ m / 4 := by
        simpa [k, m] using hnum.half
      have hroom' : cutoff + k < m / 4 := by
        simpa [k, m] using hnum.cutoff_room
      omega
    have htarget : primeRandomNzero y z ell d ≤ (m / 4) * target := by
      exact le_smul_ceilDiv hquarter
    exact htarget.trans (by
      calc
        (m / 4) * target ≤ pivots.card * target :=
          Nat.mul_le_mul_right target hpivotCardM
        _ ≤ seed.subsetSum.card + pivots.card * target :=
          Nat.le_add_left _ _)
  · change P.sum (fun a ↦ a) ≤ primeRandomDiameter y z ell d
    have hsumUpper : P.sum (fun a ↦ a) ≤
        P.sum (fun _a ↦ 2 * y / d) :=
      Finset.sum_le_sum fun a ha ↦ (Finset.mem_Icc.mp (hrange ha)).2
    calc
      P.sum (fun a ↦ a) ≤ P.sum (fun _a ↦ 2 * y / d) := hsumUpper
      _ = P.card * (2 * y / d) := by simp
      _ = m * (2 * y / d) := by rw [hcard]
      _ ≤ primeRandomDiameter y z ell d := hnum.sum

end Erdos360

#print axioms Erdos360.exists_primePoolOrdinaryGrowthCertificate_of_sharp_numerics
