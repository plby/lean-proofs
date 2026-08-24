/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ElementarySourceAdaptiveData
import ErdosProblems.Erdos360.StructuredPhaseDiversity
import ErdosProblems.Erdos360.PrimeRandomAssembly

/-!
# Truthful adaptive ordinary growth for a prime-structured random pool

This is the finite ordinary-growth callback needed by the controlled source
assembly.  A balanced bisection supplies a diverse seed and pivot set.  At
each pivot, prime-structured phase diversity and the elementary
source-adaptive selector give the required number of occupied residues.

The numerical record below contains only inequalities true at the intended
critical scale.  In particular it does not contain the false coarse
cardinality condition `2t ≤ (K+1)|A|`.
-/

namespace Erdos360

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Number of source-adaptive phases exposed in one random pool. -/
def primePoolAdaptivePhaseCount (z ell : ℕ) : ℕ :=
  primeRandomPoolSize z ell / 8

/-- Phases reserved for guaranteed unsaturated increments after paying the
growth-step budget. -/
def primePoolAdaptiveUsablePhases (z ell : ℕ) : ℕ :=
  primePoolAdaptivePhaseCount z ell / 2

/-- Residue target at each ordinary pivot. -/
def primePoolAdaptiveResidueTarget (y z ell d : ℕ) : ℕ :=
  primeRandomNzero y z ell d ⌈/⌉ (primeRandomPoolSize z ell / 4)

/-- Increment required from each usable unsaturated phase. -/
def primePoolAdaptiveIncrement (y z ell d : ℕ) : ℕ :=
  primePoolAdaptiveResidueTarget y z ell d ⌈/⌉
    primePoolAdaptiveUsablePhases z ell

/-- Fibre threshold which pays the sharp `8(D-1)` almost-period bound. -/
def primePoolAdaptiveThreshold (y z ell d : ℕ) : ℕ :=
  8 * (primePoolAdaptiveIncrement y z ell d - 1)

/-- Exact finite inequalities used by the adaptive ordinary-pool theorem. -/
structure CFPPrimePoolAdaptiveNumerics
    (y U z ell d : ℕ) : Prop where
  probability :
    (2 : ℝ) * (((2 * y / d : ℕ) : ℝ) + 1) *
      Real.exp (-(primeRandomPoolDiversity y ell : ℝ) / 24) < 1
  diversity_pos : 0 < primeRandomPoolDiversity y ell
  usable_pos : 0 < primePoolAdaptiveUsablePhases z ell
  increment_gt_one : 1 < primePoolAdaptiveIncrement y z ell d
  phase_half : 2 * primePoolAdaptivePhaseCount z ell ≤
    primeRandomPoolSize z ell / 4
  threshold_room :
    4 * primePoolAdaptiveThreshold y z ell d +
        primePoolAdaptivePhaseCount z ell ≤
      primeRandomPoolSize z ell / 4
  source_room : 2 * U < primeRandomPoolSize z ell / 4
  diversity_room : U ≤ primeRandomPoolDiversity y ell / 4 + 1
  target_room : 4 * primePoolAdaptiveResidueTarget y z ell d ≤ y / d + 1
  growth_budget : ∀ t : ℕ, y / d + 1 ≤ t → t ≤ 2 * y / d →
    (Nat.log 2 t + 1) *
        (2 * (Nat.log 2 t + 1) +
          (primePoolAdaptiveThreshold y z ell d /
              primePoolAdaptiveThreshold y z ell d + 1)) +
      primePoolAdaptiveUsablePhases z ell ≤
        primePoolAdaptivePhaseCount z ell
  sum : primeRandomPoolSize z ell * (2 * y / d) ≤
    primeRandomDiameter y z ell d

/-- One prime-structured random pool has the exact ordinary-growth
certificate consumed by the Lev assembly. -/
theorem exists_primePoolOrdinaryGrowthCertificate_of_adaptive_numerics
    {n y U d z ell : ℕ} {W Z P : Finset ℕ}
    (hd : 0 < d) (hdn : d ∣ n)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ a ∈ Z, d * a ∈ W)
    (hPZ : P ⊆ Z)
    (hcard : P.card = primeRandomPoolSize z ell)
    (hrange : P ⊆ Finset.Icc (y / d + 1) (2 * y / d))
    (hdiverse : DiverseSampling.DiverseNat P
      (primeRandomPoolDiversity y ell))
    (hnum : CFPPrimePoolAdaptiveNumerics y U z ell d) :
    Nonempty (CFPOrdinaryGrowthCertificate P
      (primeRandomNzero y z ell d)
      (primeRandomDiameter y z ell d)) := by
  let m := primeRandomPoolSize z ell
  let K := primeRandomPoolDiversity y ell
  let phaseCount := primePoolAdaptivePhaseCount z ell
  let usable := primePoolAdaptiveUsablePhases z ell
  let residueTarget := primePoolAdaptiveResidueTarget y z ell d
  let D := primePoolAdaptiveIncrement y z ell d
  let Q := primePoolAdaptiveThreshold y z ell d
  have hPico : P ⊆ Finset.Ico (y / d + 1) (2 * y / d + 1) := by
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
  have hseedRange : seed ⊆ Finset.Ico (y / d + 1) (2 * y / d + 1) :=
    hseedP.trans hPico
  have hpivotsRange : pivots ⊆
      Finset.Ico (y / d + 1) (2 * y / d + 1) :=
    hpivotsP.trans hPico
  have hseedZ : seed ⊆ Z := hseedP.trans hPZ
  have hpivotsZ : pivots ⊆ Z := hpivotsP.trans hPZ
  have hunion : seed ∪ pivots = P := Finset.union_sdiff_of_subset hseedP
  have hdisjoint : Disjoint seed pivots := Finset.disjoint_sdiff
  have hresidue : ∀ t ∈ pivots,
      residueTarget ≤ (occupiedResidues seed.subsetSum t).card := by
    intro t htPivot
    have htI := Finset.mem_Ico.mp (hpivotsRange htPivot)
    have htpos : 0 < t :=
      (Nat.zero_lt_succ (y / d)).trans_le htI.1
    letI : NeZero t := ⟨htpos.ne'⟩
    let R₀ := seed.image fun a : ℕ ↦ (a : ZMod t)
    have hwidth : (2 * y / d + 1) - (y / d + 1) ≤ t := by
      have htwo := Nat.add_div_le_div_add_div_add_one y y d
      have hupper : 2 * y / d ≤ y / d + y / d + 1 := by
        simpa [two_mul] using htwo
      omega
    have hphaseDiverse : PhaseDiverse htpos R₀ := by
      apply phaseDiverse_of_primeStructured_extraction
        htpos hd hdn hW hscale hseedZ (hpivotsZ htPivot)
        hseedRange hwidth hseedDiverse
      · have hsource := hnum.source_room
        exact hsource.trans_le hseedCardM
      · exact hnum.diversity_room
    have hR₀card : R₀.card = seed.card :=
      card_image_zmod_eq_of_subset_Ico seed hseedRange hwidth
    have hQpos : 0 < Q := by
      dsimp only [Q, primePoolAdaptiveThreshold]
      exact Nat.mul_pos (by omega) (by
        have := hnum.increment_gt_one
        omega)
    have hroom : 4 * Q + phaseCount ≤ m / 4 := by
      simpa [Q, phaseCount, m] using hnum.threshold_room
    have hdata : Nonempty
        (CFPSourceAdaptiveSelectorData htpos R₀ hphaseDiverse
          residueTarget) := by
      apply exists_CFPSourceAdaptiveSelectorData_elementary_of_target_room
        htpos R₀ hphaseDiverse residueTarget Q D Q phaseCount
      · exact hnum.increment_gt_one
      · exact hQpos
      · rw [hR₀card]
        exact hnum.phase_half.trans hseedCardM
      · intro i hi
        rw [card_sourceAdaptiveRemainder htpos R₀ {0} (by simp)
          hphaseDiverse Q (by omega), hR₀card]
        omega
      · intro i hi
        rw [card_sourceAdaptiveRemainder htpos R₀ {0} (by simp)
          hphaseDiverse Q (by omega), hR₀card]
        omega
      · rfl
      · exact hnum.target_room.trans htI.1
      · have hgrowth := hnum.growth_budget t htI.1 (by omega)
        exact Nat.le_of_add_right_le (by
          simpa [Q, phaseCount, usable] using hgrowth)
      · have hgrowth := hnum.growth_budget t htI.1 (by omega)
        have hgrowth' :
            (Nat.log 2 t + 1) *
                (2 * (Nat.log 2 t + 1) + (Q / Q + 1)) + usable ≤
              phaseCount := by
          simpa [Q, phaseCount, usable] using hgrowth
        have husable : usable ≤ phaseCount -
            (Nat.log 2 t + 1) *
              (2 * (Nat.log 2 t + 1) + (Q / Q + 1)) := by
          omega
        have hceil : residueTarget ≤ usable * D := by
          exact le_smul_ceilDiv hnum.usable_pos
        exact hceil.trans (by
          simpa [mul_comm] using Nat.mul_le_mul_left D husable)
    exact occupiedResidues_lower_of_source_adaptive_selector
      htpos seed hphaseDiverse hdata.some
  refine ⟨
    { seed := seed
      pivots := pivots
      residueGain := residueTarget
      diversity := K
      union_eq := hunion
      disjoint := hdisjoint
      pivots_pos := ?_
      residues := ?_
      target := ?_
      diversity_pos := hnum.diversity_pos
      diverse := by simpa [K, hunion] using hdiverse
      sum_le := ?_ }⟩
  · intro t ht
    have htI := Finset.mem_Ico.mp (hpivotsRange ht)
    exact (Nat.zero_lt_succ (y / d)).trans_le htI.1
  · exact hresidue
  · have hquarter : 0 < m / 4 := by
      have husable := hnum.usable_pos
      dsimp only [usable, primePoolAdaptiveUsablePhases,
        phaseCount, primePoolAdaptivePhaseCount, m] at husable
      omega
    have htarget : primeRandomNzero y z ell d ≤
        (m / 4) * residueTarget := by
      exact le_smul_ceilDiv hquarter
    exact htarget.trans (by
      calc
        (m / 4) * residueTarget ≤ pivots.card * residueTarget :=
          Nat.mul_le_mul_right residueTarget hpivotCardM
        _ ≤ seed.subsetSum.card + pivots.card * residueTarget :=
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

#print axioms Erdos360.exists_primePoolOrdinaryGrowthCertificate_of_adaptive_numerics
