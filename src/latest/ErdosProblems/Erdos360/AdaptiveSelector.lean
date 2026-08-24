/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.CFPModularPhases

/-!
# The adaptive-selector interface for the source phase machine

The source bookkeeping in `AgentCFPModularPhases360` leaves three local
selector estimates as inputs.  This file discharges both estimates in a
growth phase from the selector already defined in `Core`, proves the ambient
modulus bound, and reduces the unsaturated estimate to one exact
almost-period exclusion.

The latter is intentionally phrased for the shift actually selected by the
recursion.  In the Conlon--Fox--Pham application its proof is the inverse
theorem followed by the progression sieve: if that shift added fewer than
`D` points, all available shifts would be `D - 1` almost periods, and the
three inverse alternatives are excluded.
-/

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

section SourceSelector

variable {b : ℕ} [NeZero b]

/-- A source growth phase is a growth phase for the selector in `Core` as
soon as the fibre threshold occupies at most one quarter of the current
remainder. -/
lemma isModularGrowthPhase_of_isCFPGrowthPhase
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) {i : ℕ}
    (hQ : 4 * Q ≤ (cfpRemainder hb R₀ E hE hdiverse i).card)
    (hg : IsCFPGrowthPhase hb R₀ E hE hdiverse Q i) :
    IsModularGrowthPhase hb R₀
      (cfpRemainder hb R₀ E hE hdiverse i) E := by
  obtain ⟨u, -, huQ⟩ := hg
  refine ⟨u, ?_⟩
  exact (Nat.mul_le_mul_left 4 huQ).trans hQ

/-- The source's multiplicative small-growth law is supplied by the
canonical selector.  The only numerical input is the source condition
`4Q ≤ |R_i|`, which identifies a `Q`-small fibre with a growth phase of
the selector in `Core`. -/
lemma cfp_adaptive_smallStep
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ)
    (hhalf : 2 * k ≤ R₀.card)
    (hQ : ∀ i < k,
      4 * Q ≤ (cfpRemainder hb R₀ E hE hdiverse i).card) :
    ∀ i < k,
      IsCFPSmallGrowthPhase hb R₀ E hE hdiverse Q i →
      cfpModulus hb R₀ E hE hdiverse i =
        cfpModulus hb R₀ E hE hdiverse (i + 1) →
      3 * cfpInternalCard hb R₀ E hE hdiverse i ≤
        2 * cfpInternalCard hb R₀ E hE hdiverse (i + 1) := by
  intro i hi hg hmod
  have hiCard : i < R₀.card := by omega
  have hwide : R₀.card ≤
      2 * (cfpRemainder hb R₀ E hE hdiverse i).card := by
    rw [card_modularRemainder hb R₀ E hE hdiverse (by omega)]
    omega
  exact modularInternalCard_growth_step hb R₀ E hE hdiverse
    hiCard hwide
    (isModularGrowthPhase_of_isCFPGrowthPhase hb R₀ E hE hdiverse Q
      (hQ i hi) hg.1)
    hmod

/-- Above the half-way point for the internal subset-sum set, the same
`3/2` selector gain is an additive gain of at least `L`, provided
`4L ≤ |R_i|`.  This is the division-free integer form of CFP (M3). -/
lemma cfp_adaptive_largeStep
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q L k : ℕ)
    (hhalf : 2 * k ≤ R₀.card)
    (hQ : ∀ i < k,
      4 * Q ≤ (cfpRemainder hb R₀ E hE hdiverse i).card)
    (hL : ∀ i < k,
      4 * L ≤ (cfpRemainder hb R₀ E hE hdiverse i).card) :
    ∀ i < k,
      IsCFPLargeGrowthPhase hb R₀ E hE hdiverse Q i →
      cfpModulus hb R₀ E hE hdiverse i =
        cfpModulus hb R₀ E hE hdiverse (i + 1) →
      L + cfpInternalCard hb R₀ E hE hdiverse i ≤
        cfpInternalCard hb R₀ E hE hdiverse (i + 1) := by
  intro i hi hg hmod
  have hiCard : i < R₀.card := by omega
  have hwide : R₀.card ≤
      2 * (cfpRemainder hb R₀ E hE hdiverse i).card := by
    rw [card_modularRemainder hb R₀ E hE hdiverse (by omega)]
    omega
  have hgrowth :
      3 * cfpInternalCard hb R₀ E hE hdiverse i ≤
        2 * cfpInternalCard hb R₀ E hE hdiverse (i + 1) :=
    modularInternalCard_growth_step hb R₀ E hE hdiverse
      hiCard hwide
      (isModularGrowthPhase_of_isCFPGrowthPhase hb R₀ E hE hdiverse Q
        (hQ i hi) hg.1)
      hmod
  have htwoL : 2 * L ≤ cfpInternalCard hb R₀ E hE hdiverse i := by
    have hrem := hL i hi
    have hlarge := hg.2
    omega
  omega

/-- Every current subgroup modulus divides, and hence is at most, the
ambient cyclic modulus. -/
lemma cfpModulus_le_ambient
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (i : ℕ) :
    cfpModulus hb R₀ E hE hdiverse i ≤ b := by
  exact Nat.le_of_dvd hb (closureModulus_dvd hb
    (cfpRemainder hb R₀ E hE hdiverse i))

/-- A convenient `dMax` form of the ambient modulus bound. -/
lemma cfpModulus_le_of_ambient_le
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) {dMax k : ℕ}
    (hbMax : b ≤ dMax) :
    ∀ i < k, cfpModulus hb R₀ E hE hdiverse i ≤ dMax := by
  intro i _
  exact (cfpModulus_le_ambient hb R₀ E hE hdiverse i).trans hbMax

/-- Exact residual inverse-theorem interface for unsaturated phases.

Membership in `almostPeriods S (D - 1)` is equivalent to adding at most
`D - 1` new points.  Thus this condition says precisely that the selected
shift has the source-required gain at every unsaturated phase. -/
def CFPPickedShiftEscapesAlmostPeriods
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q D : ℕ) (sat : ℕ → ℕ)
    (k : ℕ) : Prop :=
  ∀ i < k,
    IsCFPUnsaturatedPhase hb R₀ E hE hdiverse Q sat i →
    modularPhasePick hb R₀ E hE hdiverse
        (cfpRemainder hb R₀ E hE hdiverse i) ∉
      almostPeriods (modularPhaseSums hb R₀ E hE hdiverse i) (D - 1)

/-- The exact almost-period exclusion implies the uniform unsaturated
increment expected by `cfp_modular_phase_machine`. -/
lemma cfp_adaptive_unsaturatedStep
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q D k : ℕ) (sat : ℕ → ℕ)
    (hhalf : 2 * k ≤ R₀.card)
    (hinverse : CFPPickedShiftEscapesAlmostPeriods
      hb R₀ E hE hdiverse Q D sat k) :
    ∀ i < k,
      IsCFPUnsaturatedPhase hb R₀ E hE hdiverse Q sat i →
      D + (modularPhaseSums hb R₀ E hE hdiverse i).card ≤
        (modularPhaseSums hb R₀ E hE hdiverse (i + 1)).card := by
  intro i hi hu
  have hiCard : i < R₀.card := by omega
  have hescape := hinverse i hi hu
  have hnew : D ≤ (translationNew
      (modularPhaseSums hb R₀ E hE hdiverse i)
      (modularPhasePick hb R₀ E hE hdiverse
        (cfpRemainder hb R₀ E hE hdiverse i))).card := by
    rw [mem_almostPeriods_iff_card_translationNew_le] at hescape
    omega
  change D ≤ (translationNew
    (modularPhaseSums hb R₀ E hE hdiverse i)
    (modularPhasePick hb R₀ E hE hdiverse
      (modularRemainder hb R₀ E hE hdiverse i))).card at hnew
  rw [card_modularPhaseSums_succ hb R₀ E hE hdiverse hiCard]
  omega

/-- CFP Lemma 5.6 with the local adaptive choices discharged.

The only inverse-additive input left is
`CFPPickedShiftEscapesAlmostPeriods`; all growth-step and subgroup-modulus
obligations are derived here from the elementary parameter inequalities.
Taking `dMax = b` gives the unconditional ambient modulus bound.  A sharper
source-specific `dMax` may be supplied through `hmodMax`. -/
theorem cfp_modular_growth_of_adaptive_selector
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (Q dMax L D k satTarget unsatTarget : ℕ) (sat : ℕ → ℕ)
    (hLpos : 0 < L) (hhalf : 2 * k ≤ R₀.card)
    (hQ : ∀ i < k,
      4 * Q ≤ (cfpRemainder hb R₀ E hE hdiverse i).card)
    (hL : ∀ i < k,
      4 * L ≤ (cfpRemainder hb R₀ E hE hdiverse i).card)
    (hmodMax : ∀ i < k,
      cfpModulus hb R₀ E hE hdiverse i ≤ dMax)
    (hinverse : CFPPickedShiftEscapesAlmostPeriods
      hb R₀ E hE hdiverse Q D sat k)
    (hsatTarget : ∀ i < k,
      satTarget ≤ cfpModulus hb R₀ E hE hdiverse i *
        sat (cfpModulus hb R₀ E hE hdiverse i))
    (hgrowthBudget :
      (Nat.log 2 dMax + 1) *
          (2 * (Nat.log 2 b + 1) + (Q / L + 1)) ≤ k)
    (hunsatTarget : unsatTarget ≤ D *
      (k - (Nat.log 2 dMax + 1) *
        (2 * (Nat.log 2 b + 1) + (Q / L + 1)))) :
    min satTarget unsatTarget ≤ (E + R₀.subsetSum).card := by
  exact cfp_modular_phase_machine hb R₀ E hE hdiverse
    Q dMax L D k satTarget unsatTarget sat hLpos hhalf hmodMax
    (cfp_adaptive_smallStep hb R₀ E hE hdiverse Q k hhalf hQ)
    (cfp_adaptive_largeStep hb R₀ E hE hdiverse Q L k hhalf hQ hL)
    (cfp_adaptive_unsaturatedStep hb R₀ E hE hdiverse Q D k sat
      hhalf hinverse)
    hsatTarget hgrowthBudget hunsatTarget

/-- Ambient-modulus specialization of
`cfp_modular_growth_of_adaptive_selector`. -/
theorem cfp_modular_growth_of_adaptive_selector_ambient
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (Q L D k satTarget unsatTarget : ℕ) (sat : ℕ → ℕ)
    (hLpos : 0 < L) (hhalf : 2 * k ≤ R₀.card)
    (hQ : ∀ i < k,
      4 * Q ≤ (cfpRemainder hb R₀ E hE hdiverse i).card)
    (hL : ∀ i < k,
      4 * L ≤ (cfpRemainder hb R₀ E hE hdiverse i).card)
    (hinverse : CFPPickedShiftEscapesAlmostPeriods
      hb R₀ E hE hdiverse Q D sat k)
    (hsatTarget : ∀ i < k,
      satTarget ≤ cfpModulus hb R₀ E hE hdiverse i *
        sat (cfpModulus hb R₀ E hE hdiverse i))
    (hgrowthBudget :
      (Nat.log 2 b + 1) *
          (2 * (Nat.log 2 b + 1) + (Q / L + 1)) ≤ k)
    (hunsatTarget : unsatTarget ≤ D *
      (k - (Nat.log 2 b + 1) *
        (2 * (Nat.log 2 b + 1) + (Q / L + 1)))) :
    min satTarget unsatTarget ≤ (E + R₀.subsetSum).card := by
  exact cfp_modular_growth_of_adaptive_selector hb R₀ E hE hdiverse
    Q b L D k satTarget unsatTarget sat hLpos hhalf hQ hL
    (cfpModulus_le_of_ambient_le hb R₀ E hE hdiverse (le_refl b))
    hinverse hsatTarget hgrowthBudget hunsatTarget

end SourceSelector

end Erdos360
