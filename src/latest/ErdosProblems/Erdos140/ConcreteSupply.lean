import ErdosProblems.Erdos140.DensityStep
import ErdosProblems.Erdos140.BohrScaleVolume
import ErdosProblems.Erdos140.Bookkeeping
import ErdosProblems.Erdos140.GroupCount
import ErdosProblems.Erdos140.TwoBohrBalanced
import ErdosProblems.Erdos140.FinalAssembly
import ErdosProblems.Erdos140.HolderApproximation
import ErdosProblems.Erdos140.ConcreteNumerics
import ErdosProblems.Erdos140.RawSupplyNumerics

/-!
# Rank-regular concrete supply for the terminal step

This file deliberately avoids the plateau narrowing package: that package
remembers an exact plateau identity, whereas the quantitative Bourgain
alternative only needs a rank-regular unit carrier.  The lemmas here keep the
actual Bohr data and actual finite carriers visible.

The first part is unconditional geometry.  Starting with a rank-regular
unit-carrier restriction and a reciprocal scale, we regularize the small
dilate and obtain a genuine regular child, with the explicit
(3m)^rank * 4^rank cardinality loss.  The same child can be used twice in
the two-scale Bourgain alternative.

The second part records the exact remaining numerical hypotheses needed to
turn that geometry into a controlled increment.  They are inequalities about
the chosen reciprocal scale and the exponential budget, not a restatement of
the desired density-increment conclusion.
-/

open Finset Fintype Function
open scoped BigOperators NNReal Pointwise translate mu Indicator

namespace Erdos140.ConcreteSupply

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Transport commutes with scalar dilation. -/
theorem map_dilate_eq
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (B : BohrData G) (e : G ≃+ H) (rho : NNReal) :
    (B.map e).dilate rho = (B.dilate rho).map e := by
  rfl

/-- Rank regularity is invariant under an additive equivalence.  In
particular this supplies regularity of the doubled middle carrier in odd
cyclic groups. -/
theorem isRankRegular_map
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (B : BohrData G) (e : G ≃+ H) (hB : B.IsRankRegular) :
    (B.map e).IsRankRegular := by
  unfold BohrData.IsRankRegular at hB ⊢
  simp only [BohrData.rank_map]
  intro kappa hkappa
  have h := hB kappa hkappa
  rw [map_dilate_eq, map_dilate_eq,
    BohrData.card_map_carrier, BohrData.card_map_carrier,
    BohrData.card_map_carrier]
  exact h

/-- The doubled Bohr datum in an odd cyclic group is rank regular whenever
the original datum is. -/
theorem doubledBohrData_rankRegular
    {M : ℕ} [NeZero M] (hM : Odd M) (B : BohrData (ZMod M))
    (hB : B.IsRankRegular) :
    (GroupCount.doubledBohrData M hM B).IsRankRegular := by
  exact isRankRegular_map B (BohrData.zmodDoublingEquiv M hM) hB

/-- A regular child obtained from a reciprocal scalar dilate.  The natural
cardinality inequality is the exact combination of arbitrary-scale Bohr
volume and the rank-regular subdatum loss. -/
theorem exists_rankRegular_child_inside_inv_dilate
    (B : BohrData G) (m : ℕ) (hm : 0 < m) :
    ∃ c : DensityStep.RegularChild (G := G),
      c.bohr.IsRankRegular ∧
      c.bohr.rank = B.rank ∧
      c.outer = 1 ∧
      c.carrier = c.bohr.carrier ∧
      c.carrier ⊆ (B.dilate ((m : NNReal)⁻¹)).carrier ∧
      B.carrier.card ≤
        ((3 * m) ^ B.rank * 4 ^ B.rank) * c.carrier.card := by
  classical
  let D := B.dilate ((m : NNReal)⁻¹)
  obtain ⟨R, hRreg, hRrank, hRD, hDcard⟩ :=
    LocalizedAlmostPeriodicity.exists_rankRegular_subdatum D
  obtain ⟨c, hcbohr, _hcouter, hccarrier⟩ :=
    DensityStep.RegularChild.exists_of_rankRegular R hRreg
  refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hcbohr] using hRreg
  · simpa [hcbohr, D] using hRrank
  · exact _hcouter
  · simpa [hcbohr] using hccarrier
  · simpa [hccarrier, D] using hRD
  · have hscale :=
      BohrData.card_dilate_le_three_mul_pow_rank_mul_card_div
        B 1 hm
    have hscale' :
        B.carrier.card ≤
          (3 * m) ^ B.rank *
            (B.dilate ((m : NNReal)⁻¹)).carrier.card := by
      simpa [div_eq_mul_inv] using hscale
    calc
      B.carrier.card ≤
          (3 * m) ^ B.rank *
            (B.dilate ((m : NNReal)⁻¹)).carrier.card := hscale'
      _ ≤ (3 * m) ^ B.rank * (4 ^ B.rank * R.carrier.card) := by
        exact Nat.mul_le_mul_left _ (by simpa [D] using hDcard)
      _ = ((3 * m) ^ B.rank * 4 ^ B.rank) * c.carrier.card := by
        rw [hccarrier]
        ring

/-- The finite loss of one reciprocal-scale regularized child. -/
def reciprocalLoss (B : BohrData G) (m : ℕ) : ℕ :=
  (3 * m) ^ B.rank * 4 ^ B.rank

/-- The finite loss of first choosing K from B and then B' from K. -/
def twoReciprocalLoss (B : BohrData G) (mOne mTwo : ℕ) : ℕ :=
  reciprocalLoss B mOne * reciprocalLoss B mTwo

/-- Two actual children at two reciprocal scales.  The first child is the
baseline carrier K.  The second is constructed inside a further reciprocal
dilate of K, so its double is visibly contained in the Holder-small dilate
of K.  This is the geometry needed by the cross-term approximation; using
the same child twice would lose precisely this inclusion. -/
structure ReciprocalChildren (B : BohrData G) (mOne mTwo : ℕ) where
  childOne : DensityStep.RegularChild (G := G)
  childTwo : DensityStep.RegularChild (G := G)
  childOne_rankRegular : childOne.bohr.IsRankRegular
  childTwo_rankRegular : childTwo.bohr.IsRankRegular
  rankOne : childOne.bohr.rank = B.rank
  rankTwo : childTwo.bohr.rank = B.rank
  childOne_outer_one : childOne.outer = 1
  childTwo_outer_one : childTwo.outer = 1
  childOne_carrier : childOne.carrier = childOne.bohr.carrier
  childTwo_carrier : childTwo.carrier = childTwo.bohr.carrier
  smallOne : childOne.carrier ⊆ (B.dilate ((mOne : NNReal)⁻¹)).carrier
  smallTwo : childTwo.carrier ⊆ (B.dilate ((mOne : NNReal)⁻¹)).carrier
  middle_small :
    childTwo.carrier ⊆
      (childOne.bohr.dilate ((mTwo : NNReal)⁻¹)).carrier
  doubled_middle_small :
    GroupCount.doubledFinset childTwo.carrier ⊆
      (childOne.bohr.dilate
        ((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹)).carrier
  cardOne :
    B.carrier.card ≤
      reciprocalLoss B mOne * childOne.carrier.card
  cardTwo :
    B.carrier.card ≤
      twoReciprocalLoss B mOne mTwo * childTwo.carrier.card

/-- Unconditional construction of the two-scale geometry.  The only extra
input says that the second reciprocal scale is at most one; this is the
literal inclusion needed to regard the middle child as small for the
original Bourgain step as well as for Holder. -/
theorem exists_reciprocalChildren (B : BohrData G)
    (mOne mTwo : ℕ) (hmOne : 0 < mOne) (hmTwo : 0 < mTwo)
    (hmTwoInv : ((mTwo : NNReal)⁻¹) ≤ 1) :
    Nonempty (ReciprocalChildren B mOne mTwo) := by
  obtain ⟨cOne, hregOne, hrankOne, houterOne, hcarrierOne, hsmallOne, hcardOne⟩ :=
    exists_rankRegular_child_inside_inv_dilate B mOne hmOne
  obtain ⟨cTwo, hregTwo, hrankTwo', houterTwo, hcarrierTwo, hmiddle, hcardMiddle⟩ :=
    exists_rankRegular_child_inside_inv_dilate cOne.bohr mTwo hmTwo
  have hsmallTwo : cTwo.carrier ⊆
      (B.dilate ((mOne : NNReal)⁻¹)).carrier := by
    intro x hx
    apply hsmallOne
    rw [hcarrierOne]
    simpa using BohrData.carrier_dilate_mono hmTwoInv (hmiddle hx)
  have hdoubled :
      GroupCount.doubledFinset cTwo.carrier ⊆
        (cOne.bohr.dilate
          ((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹)).carrier := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := GroupCount.mem_doubledFinset.mp hx
    exact BohrData.add_mem_dilate (hmiddle hy) (hmiddle hy)
  have hrankTwo : cTwo.bohr.rank = B.rank := hrankTwo'.trans hrankOne
  have hcardTwo :
      B.carrier.card ≤
        twoReciprocalLoss B mOne mTwo * cTwo.carrier.card := by
    calc
      B.carrier.card ≤
          reciprocalLoss B mOne * cOne.carrier.card :=
        hcardOne
      _ ≤ reciprocalLoss B mOne *
          (reciprocalLoss cOne.bohr mTwo *
            cTwo.carrier.card) :=
        Nat.mul_le_mul_left _
          (by simpa [hcarrierOne, reciprocalLoss] using hcardMiddle)
      _ = twoReciprocalLoss B mOne mTwo * cTwo.carrier.card := by
        simp [reciprocalLoss, twoReciprocalLoss, hrankOne]
        ring
  exact ⟨{
    childOne := cOne
    childTwo := cTwo
    childOne_rankRegular := hregOne
    childTwo_rankRegular := hregTwo
    rankOne := hrankOne
    rankTwo := hrankTwo
    childOne_outer_one := houterOne
    childTwo_outer_one := houterTwo
    childOne_carrier := hcarrierOne
    childTwo_carrier := hcarrierTwo
    smallOne := hsmallOne
    smallTwo := hsmallTwo
    middle_small := hmiddle
    doubled_middle_small := hdoubled
    cardOne := hcardOne
    cardTwo := hcardTwo }⟩

/-- Exact arithmetic facts needed to use reciprocal children as one
quantitative Bourgain step.  These are the genuine outstanding numerical
inequalities: scale smallness for rank regularity, scale smallness relative
to density, and conversion of the explicit finite volume loss to the chosen
exponential budget. -/
structure ReciprocalStepBounds {original : Finset G}
    (s : DensityStep.LocatedRestriction original) (mOne mTwo : ℕ)
    (epsilon sizeCost : ℝ) where
  outer_eq_one : s.restriction.outer = 1
  rankRegular : s.restriction.bohr.IsRankRegular
  scale_rank :
    ((mOne : NNReal)⁻¹) ≤
      1 / (100 * (max s.restriction.bohr.rank 1 : ℕ) : NNReal)
  scale_density :
    400 * ((max s.restriction.bohr.rank 1 : ℕ) : ℝ) *
        (((mOne : NNReal)⁻¹ : NNReal) : ℝ) ≤ epsilon * s.density / 4
  card_budget_one :
    Real.exp (-sizeCost) * (s.card : ℝ) ≤
      ((reciprocalLoss s.restriction.bohr mOne : ℕ) : ℝ)⁻¹ *
        (s.restriction.bohr.carrier.card : ℝ)
  card_budget_two :
    Real.exp (-sizeCost) * (s.card : ℝ) ≤
      ((twoReciprocalLoss s.restriction.bohr mOne mTwo : ℕ) : ℝ)⁻¹ *
        (s.restriction.bohr.carrier.card : ℝ)

/-- The explicit finite volume loss turns the reciprocal child into the
advertised exponential-cardinality child once the three numerical bounds
above are checked. -/
theorem densePair_or_controlledIncrement_of_reciprocalChildren
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (hmOne : 0 < mOne) (hmTwo : 0 < mTwo)
    (hmTwoInv : ((mTwo : NNReal)⁻¹) ≤ 1)
    {epsilon sizeCost : ℝ} {rankCost : ℕ}
    (hepsilon : 0 < epsilon)
    (hnum : ReciprocalStepBounds s mOne mTwo epsilon sizeCost) :
    DensityStep.HasDensePair s
        (Classical.choice (exists_reciprocalChildren s.restriction.bohr
          mOne mTwo hmOne hmTwo hmTwoInv)).childOne
        (Classical.choice (exists_reciprocalChildren s.restriction.bohr
          mOne mTwo hmOne hmTwo hmTwoInv)).childTwo
        epsilon ∨
      ∃ t : DensityStep.LocatedRestriction original,
        BohrStopping.IsControlledIncrement (1 + epsilon / 2) rankCost sizeCost
          s.restriction t.restriction := by
  let P : ReciprocalChildren s.restriction.bohr mOne mTwo :=
    Classical.choice (exists_reciprocalChildren s.restriction.bohr
      mOne mTwo hmOne hmTwo hmTwoInv)
  have hfactorOnePos :
      (0 : ℝ) <
        (reciprocalLoss s.restriction.bohr mOne : ℝ) := by
    unfold reciprocalLoss
    positivity
  have hfactorTwoPos :
      (0 : ℝ) <
        (twoReciprocalLoss s.restriction.bohr mOne mTwo : ℝ) := by
    unfold twoReciprocalLoss reciprocalLoss
    positivity
  have hcardOne :
      Real.exp (-sizeCost) * (s.card : ℝ) ≤ P.childOne.carrier.card := by
    have hvol : (s.restriction.bohr.carrier.card : ℝ) ≤
        (reciprocalLoss s.restriction.bohr mOne : ℝ) *
          (P.childOne.carrier.card : ℝ) := by
      exact_mod_cast P.cardOne
    calc
      Real.exp (-sizeCost) * (s.card : ℝ) ≤
          (reciprocalLoss s.restriction.bohr mOne : ℝ)⁻¹ *
            (s.restriction.bohr.carrier.card : ℝ) := hnum.card_budget_one
      _ ≤ (reciprocalLoss s.restriction.bohr mOne : ℝ)⁻¹ *
            ((reciprocalLoss s.restriction.bohr mOne : ℝ) *
              (P.childOne.carrier.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hvol (by positivity)
      _ = P.childOne.carrier.card := by
        field_simp
  have hcardTwo :
      Real.exp (-sizeCost) * (s.card : ℝ) ≤ P.childTwo.carrier.card := by
    have hvol : (s.restriction.bohr.carrier.card : ℝ) ≤
        (twoReciprocalLoss s.restriction.bohr mOne mTwo : ℝ) *
          (P.childTwo.carrier.card : ℝ) := by
      exact_mod_cast P.cardTwo
    calc
      Real.exp (-sizeCost) * (s.card : ℝ) ≤
          (twoReciprocalLoss s.restriction.bohr mOne mTwo : ℝ)⁻¹ *
            (s.restriction.bohr.carrier.card : ℝ) := hnum.card_budget_two
      _ ≤ (twoReciprocalLoss s.restriction.bohr mOne mTwo : ℝ)⁻¹ *
            ((twoReciprocalLoss s.restriction.bohr mOne mTwo : ℝ) *
              (P.childTwo.carrier.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hvol (by positivity)
      _ = P.childTwo.carrier.card := by
        field_simp
  have hrankOne : P.childOne.bohr.rank ≤ s.rank + rankCost := by
    rw [P.rankOne]
    simp [DensityStep.LocatedRestriction.rank,
      BohrStopping.RegularRestriction.rank]
  have hrankTwo : P.childTwo.bohr.rank ≤ s.rank + rankCost := by
    rw [P.rankTwo]
    simp [DensityStep.LocatedRestriction.rank,
      BohrStopping.RegularRestriction.rank]
  simpa only [P] using
    (DensityStep.densePair_or_controlledIncrement_of_rankRegular s
      hnum.outer_eq_one hnum.rankRegular hnum.scale_rank
      P.childOne P.childTwo P.smallOne P.smallTwo hepsilon
      hnum.scale_density hrankOne hrankTwo hcardOne hcardTwo)

/-- A finite loss inequality and the corresponding reciprocal exponential
budget imply the actual child-cardinality bound.  This adapter is shared by
the raw Bourgain dichotomy above and the exact FinalAssembly interface below. -/
theorem child_card_of_loss
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {loss : ℕ} {sizeCost : ℝ} {child : Finset G}
    (hloss : (0 : ℝ) < (loss : ℝ))
    (hbudget :
      Real.exp (-sizeCost) * (s.card : ℝ) ≤
        (loss : ℝ)⁻¹ * (s.restriction.bohr.carrier.card : ℝ))
    (hvol :
      (s.restriction.bohr.carrier.card : ℝ) ≤
        (loss : ℝ) * (child.card : ℝ)) :
    Real.exp (-sizeCost) * (s.card : ℝ) ≤ child.card := by
  calc
    Real.exp (-sizeCost) * (s.card : ℝ) ≤
        (loss : ℝ)⁻¹ * (s.restriction.bohr.carrier.card : ℝ) := hbudget
    _ ≤ (loss : ℝ)⁻¹ * ((loss : ℝ) * (child.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hvol (by positivity)
    _ = child.card := by
      field_simp

/-- A logarithmic loss bound is the exact scalar condition behind a
ReciprocalStepBounds cardinality field.  This removes exponentials from the
later coarse numerical bookkeeping. -/
theorem card_budget_of_log_loss
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (houter : s.restriction.outer = 1)
    {loss : ℕ} {sizeCost : ℝ}
    (hloss : (0 : ℝ) < (loss : ℝ))
    (hlog : Real.log (loss : ℝ) ≤ sizeCost) :
    Real.exp (-sizeCost) * (s.card : ℝ) ≤
      (loss : ℝ)⁻¹ * (s.restriction.bohr.carrier.card : ℝ) := by
  have hexp :
      Real.exp (-sizeCost) ≤ (loss : ℝ)⁻¹ := by
    have hneg : -sizeCost ≤ -Real.log (loss : ℝ) := neg_le_neg hlog
    have h := Real.exp_le_exp.mpr hneg
    calc
      Real.exp (-sizeCost) ≤ Real.exp (-Real.log (loss : ℝ)) := h
      _ = (loss : ℝ)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hloss]
  have hcard :
      (s.card : ℝ) = (s.restriction.bohr.carrier.card : ℝ) := by
    unfold DensityStep.LocatedRestriction.card BohrStopping.RegularRestriction.card
      BohrStopping.RegularRestriction.ambient
    simp [houter]
  rw [hcard]
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

/-- Scalar form of the same logarithmic budget, used for a product of the
geometric and localized finite losses. -/
theorem exp_mul_loss_le_one_of_log_loss
    {loss : ℕ} {sizeCost : ℝ} (hloss : 0 < loss)
    (hlog : Real.log (loss : ℝ) ≤ sizeCost) :
    Real.exp (-sizeCost) * (loss : ℝ) ≤ 1 := by
  have hexp : Real.exp (-sizeCost) ≤ (loss : ℝ)⁻¹ := by
    have hneg : -sizeCost ≤ -Real.log (loss : ℝ) := neg_le_neg hlog
    calc
      Real.exp (-sizeCost) ≤ Real.exp (-Real.log (loss : ℝ)) :=
        Real.exp_le_exp.mpr hneg
      _ = (loss : ℝ)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hloss)]
  calc
    Real.exp (-sizeCost) * (loss : ℝ) ≤ (loss : ℝ)⁻¹ * loss := by gcongr
    _ = 1 := by
      have hlossR : (0 : ℝ) < loss := by exact_mod_cast hloss
      field_simp

/-- Croot--Sisask lower bound with a large carrier for the sampled set and
a smaller carrier for the translating set.

This is the local estimate needed by the relative-T theorem.  If A has
density alpha in a large carrier D and A+S has at most C times the size of
D, then the sampled set has density at least (alpha/C)^k / 2 inside S.
Unlike an ambient-group estimate, this bound has no current-rank factor. -/
theorem croot_beta_mul_card_le_of_two_carriers
    {A S T D : Finset G} (k : ℕ) {alpha C : ℝ}
    (halpha : 0 ≤ alpha) (hC : 0 < C)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (hAdense : alpha * (D.card : ℝ) ≤ (A.card : ℝ))
    (hsum : ((A + S).card : ℝ) ≤ C * (D.card : ℝ))
    (hT :
      (((A.card : ℝ) ^ k / 2 * S.card) /
          ((A + S).card : ℝ) ^ k ≤ (T.card : ℝ))) :
    (((alpha / C) ^ k / 2) * (S.card : ℝ)) ≤ (T.card : ℝ) := by
  have hsumPos : (0 : ℝ) < (A + S).card := by
    exact_mod_cast (hA.add hS).card_pos
  have hdenPos : (0 : ℝ) < ((A + S).card : ℝ) ^ k := by
    positivity
  apply le_trans ?_ hT
  apply (le_div_iff₀ hdenPos).2
  calc
    ((alpha / C) ^ k / 2) * (S.card : ℝ) *
        ((A + S).card : ℝ) ^ k ≤
      ((alpha / C) ^ k / 2) * (S.card : ℝ) *
        (C * (D.card : ℝ)) ^ k := by
          gcongr
    _ = (alpha * (D.card : ℝ)) ^ k / 2 * S.card := by
          have hCne : C ≠ 0 := hC.ne'
          rw [mul_pow]
          field_simp
          have hcancel : alpha / C * C = alpha := by field_simp
          rw [← mul_pow (alpha / C) C, hcancel, ← mul_pow]
    _ ≤ (A.card : ℝ) ^ k / 2 * S.card := by
          gcongr

/-- A set in the unit carrier plus a set in a small dilate stays in the
corresponding slight outer dilate.  The negated form is exactly the sumset
appearing in the relative-T Croot denominator. -/
theorem neg_add_small_subset_outer_dilate
    (B : BohrData G) (A S : Finset G) {rho : NNReal}
    (hA : A ⊆ B.carrier)
    (hS : S ⊆ (B.dilate rho).carrier) :
    (-A) + S ⊆ (B.dilate (1 + rho)).carrier := by
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_neg.mp hu
  exact BohrData.add_mem_dilate
    (by simpa using (BohrData.neg_mem_carrier.mpr (hA ha))) (hS hv)

/-- Rank regularity makes a unit carrier plus a sufficiently small carrier
cost at most a factor two.  This is the local doubling estimate used before
the relative-T Chang bound. -/
theorem card_neg_add_small_le_two_mul_card
    (B : BohrData G) (hBreg : B.IsRankRegular)
    (A S : Finset G) {rho : NNReal}
    (hA : A ⊆ B.carrier)
    (hS : S ⊆ (B.dilate rho).carrier)
    (hrho :
      rho ≤ 1 / (100 * (max B.rank 1 : ℕ) : NNReal)) :
    (-A + S).card ≤ 2 * B.carrier.card := by
  have hsub := neg_add_small_subset_outer_dilate B A S hA hS
  have hcard :
      ((B.dilate (1 + rho)).carrier.card : ℝ) ≤
        (1 + 100 * ((max B.rank 1 : ℕ) : ℝ) * (rho : ℝ)) *
          (B.carrier.card : ℝ) :=
    (hBreg rho hrho).2
  have hcoeff :
      1 + 100 * ((max B.rank 1 : ℕ) : ℝ) * (rho : ℝ) ≤ 2 := by
    have hrhoReal :
        (rho : ℝ) ≤
          1 / (100 * ((max B.rank 1 : ℕ) : ℝ)) := by
      exact_mod_cast hrho
    have hrankPos : (0 : ℝ) < (max B.rank 1 : ℕ) := by positivity
    have hmul :
        100 * ((max B.rank 1 : ℕ) : ℝ) * (rho : ℝ) ≤ 1 := by
      calc
        100 * ((max B.rank 1 : ℕ) : ℝ) * (rho : ℝ) ≤
            100 * ((max B.rank 1 : ℕ) : ℝ) *
              (1 / (100 * ((max B.rank 1 : ℕ) : ℝ))) := by
                gcongr
        _ = 1 := by field_simp
    nlinarith
  have hcard' :
      ((B.dilate (1 + rho)).carrier.card : ℝ) ≤
        2 * (B.carrier.card : ℝ) := by
    calc
      ((B.dilate (1 + rho)).carrier.card : ℝ) ≤
          (1 + 100 * ((max B.rank 1 : ℕ) : ℝ) * (rho : ℝ)) *
            (B.carrier.card : ℝ) := hcard
      _ ≤ 2 * (B.carrier.card : ℝ) := by
        gcongr
  have hsubCard :
      ((-A + S).card : ℝ) ≤
        ((B.dilate (1 + rho)).carrier.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact_mod_cast hsubCard.trans hcard'

/-- The same factor-two local-doubling estimate in the subtraction
orientation used by the supported popular set. -/
theorem card_sub_small_le_two_mul_card
    (B : BohrData G) (hBreg : B.IsRankRegular)
    (S : Finset G) {rho : NNReal}
    (hS : S ⊆ (B.dilate rho).carrier)
    (hrho :
      rho ≤ 1 / (100 * (max B.rank 1 : ℕ) : NNReal)) :
    (B.carrier - S).card ≤ 2 * B.carrier.card := by
  have h :=
    card_neg_add_small_le_two_mul_card B hBreg B.carrier S
      (fun _ hx ↦ hx) hS hrho
  have hneg :
      (B.carrier - S).card = (-B.carrier + S).card := by
    rw [← Finset.card_neg]
    simp [sub_eq_add_neg, add_comm]
  rw [hneg]
  exact h

/-- Translating the large carrier does not change the local factor-two
difference-set bound. -/
theorem card_vadd_sub_small_le_two_mul_card
    (B : BohrData G) (hBreg : B.IsRankRegular)
    (S : Finset G) {rho : NNReal}
    (hS : S ⊆ (B.dilate rho).carrier)
    (hrho :
      rho ≤ 1 / (100 * (max B.rank 1 : ℕ) : NNReal))
    (z : G) :
    ((z +ᵥ B.carrier) - S).card ≤ 2 * B.carrier.card := by
  have hbase := card_sub_small_le_two_mul_card B hBreg S hS hrho
  have heq :
      (z +ᵥ B.carrier) - S = z +ᵥ (B.carrier - S) := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_vadd_finset.mp hu
      apply Finset.mem_vadd_finset.mpr
      exact ⟨b - v, Finset.mem_sub.mpr ⟨b, hb, v, hv, rfl⟩, by
        simp only [vadd_eq_add]
        abel⟩
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_vadd_finset.mp hx
      obtain ⟨b, hb, v, hv, rfl⟩ := Finset.mem_sub.mp hu
      apply Finset.mem_sub.mpr
      exact ⟨z + b, Finset.mem_vadd_finset.mpr ⟨b, hb, rfl⟩,
        v, hv, by
          simp only [vadd_eq_add]
          abel⟩
  rw [heq, Finset.card_vadd_finset]
  exact hbase

/-- Two regular carriers for the terminal smoothing measure.  The large
carrier D is a regular dilate inside a tiny dilate of the doubled middle
carrier W.  The sampling carrier E is a further tiny regular dilate of D.
Keeping the two regularizing scalars explicit is what makes both the local
sumset estimate and the final support inclusion available. -/
structure SmoothingHierarchy (W : BohrData G) where
  eta : NNReal
  Dbohr : BohrData G
  rhoD : NNReal
  theta : NNReal
  Ebohr : BohrData G
  rhoE : NNReal
  phi : NNReal
  B₀ : BohrData G
  rho₀ : NNReal
  eta_eq : eta = 1 / (1600 * (max W.rank 1 : ℕ) : NNReal)
  eta_pos : 0 < eta
  eta_narrow :
    4 * eta ≤ 1 / (400 * (max W.rank 1 : ℕ) : NNReal)
  D_eq : Dbohr = (W.dilate eta).dilate rhoD
  rhoD_half : 1 / 2 ≤ rhoD
  rhoD_one : rhoD ≤ 1
  D_regular : Dbohr.IsRankRegular
  theta_eq : theta = 1 / (200 * (max Dbohr.rank 1 : ℕ) : NNReal)
  theta_pos : 0 < theta
  theta_small :
    theta ≤ 1 / (100 * (max Dbohr.rank 1 : ℕ) : NNReal)
  E_eq : Ebohr = (Dbohr.dilate theta).dilate rhoE
  rhoE_half : 1 / 2 ≤ rhoE
  rhoE_one : rhoE ≤ 1
  E_regular : Ebohr.IsRankRegular
  phi_eq : phi = 1 / (200 * (max Ebohr.rank 1 : ℕ) : NNReal)
  phi_pos : 0 < phi
  phi_small :
    phi ≤ 1 / (100 * (max Ebohr.rank 1 : ℕ) : NNReal)
  B₀_eq : B₀ = (Ebohr.dilate phi).dilate rho₀
  rho₀_half : 1 / 2 ≤ rho₀
  rho₀_one : rho₀ ≤ 1
  B₀_regular : B₀.IsRankRegular
  D_small : Dbohr.carrier ⊆ (W.dilate eta).carrier
  E_small : Ebohr.carrier ⊆ (W.dilate eta).carrier
  E_in_Dtheta : Ebohr.carrier ⊆ (Dbohr.dilate theta).carrier
  B₀_small : B₀.carrier ⊆ (W.dilate eta).carrier
  B₀_in_Ephi : B₀.carrier ⊆ (Ebohr.dilate phi).carrier

/-- Unconditional two-scale smoothing hierarchy inside a rank-regular
doubled middle carrier.  The chosen constants are deliberately coarse:
eta pays the fourfold support expansion, and theta pays the local
factor-two sumset comparison. -/
theorem exists_smoothingHierarchy (W : BohrData G) :
    Nonempty (SmoothingHierarchy W) := by
  let dW : ℕ := max W.rank 1
  let eta : NNReal := 1 / (1600 * (dW : NNReal))
  have hdW : 0 < dW := by simp [dW]
  have hetaPos : 0 < eta := by
    dsimp [eta]
    positivity
  have hetaNarrow :
      4 * eta ≤ 1 / (400 * (max W.rank 1 : ℕ) : NNReal) := by
    dsimp [eta, dW]
    have hd : (0 : NNReal) < (max W.rank 1 : ℕ) := by positivity
    field_simp
    norm_num
  obtain ⟨rhoD, hrhoDhalf, hrhoDone, hDreg⟩ :=
    (W.dilate eta).exists_rankRegular_dilate
  let Dbohr : BohrData G := (W.dilate eta).dilate rhoD
  let dD : ℕ := max Dbohr.rank 1
  let theta : NNReal := 1 / (200 * (dD : NNReal))
  have hdD : 0 < dD := by simp [dD]
  have hthetaPos : 0 < theta := by
    dsimp [theta]
    positivity
  have hthetaSmall :
      theta ≤ 1 / (100 * (max Dbohr.rank 1 : ℕ) : NNReal) := by
    dsimp [theta, dD]
    have hd : (0 : NNReal) < (max Dbohr.rank 1 : ℕ) := by positivity
    field_simp
    norm_num
  obtain ⟨rhoE, hrhoEhalf, hrhoEone, hEreg⟩ :=
    (Dbohr.dilate theta).exists_rankRegular_dilate
  let Ebohr : BohrData G := (Dbohr.dilate theta).dilate rhoE
  let dE : ℕ := max Ebohr.rank 1
  let phi : NNReal := 1 / (200 * (dE : NNReal))
  have hdE : 0 < dE := by simp [dE]
  have hphiPos : 0 < phi := by
    dsimp [phi]
    positivity
  have hphiSmall :
      phi ≤ 1 / (100 * (max Ebohr.rank 1 : ℕ) : NNReal) := by
    dsimp [phi, dE]
    have hd : (0 : NNReal) < (max Ebohr.rank 1 : ℕ) := by positivity
    field_simp
    norm_num
  obtain ⟨rho₀, hrho₀half, hrho₀one, hB₀reg⟩ :=
    (Ebohr.dilate phi).exists_rankRegular_dilate
  let B₀ : BohrData G := (Ebohr.dilate phi).dilate rho₀
  have hDsmall : Dbohr.carrier ⊆ (W.dilate eta).carrier := by
    dsimp [Dbohr]
    simpa using
      (BohrData.carrier_dilate_mono hrhoDone :
        ((W.dilate eta).dilate rhoD).carrier ⊆
          ((W.dilate eta).dilate 1).carrier)
  have hEtheta :
      Ebohr.carrier ⊆ (Dbohr.dilate theta).carrier := by
    dsimp [Ebohr]
    simpa using
      (BohrData.carrier_dilate_mono hrhoEone :
        ((Dbohr.dilate theta).dilate rhoE).carrier ⊆
          ((Dbohr.dilate theta).dilate 1).carrier)
  have hthetaOne : theta ≤ 1 := by
    calc
      theta ≤ 1 / (100 * (max Dbohr.rank 1 : ℕ) : NNReal) :=
        hthetaSmall
      _ ≤ 1 := by
        rw [div_le_one]
        · exact_mod_cast (show 1 ≤ 100 * max Dbohr.rank 1 by omega)
        · positivity
  have hEsmall : Ebohr.carrier ⊆ (W.dilate eta).carrier := by
    apply hEtheta.trans
    apply (BohrData.carrier_dilate_mono hthetaOne).trans
    simpa using hDsmall
  have hB₀phi :
      B₀.carrier ⊆ (Ebohr.dilate phi).carrier := by
    dsimp [B₀]
    simpa using
      (BohrData.carrier_dilate_mono hrho₀one :
        ((Ebohr.dilate phi).dilate rho₀).carrier ⊆
          ((Ebohr.dilate phi).dilate 1).carrier)
  have hphiOne : phi ≤ 1 := by
    calc
      phi ≤ 1 / (100 * (max Ebohr.rank 1 : ℕ) : NNReal) :=
        hphiSmall
      _ ≤ 1 := by
        rw [div_le_one]
        · exact_mod_cast (show 1 ≤ 100 * max Ebohr.rank 1 by omega)
        · positivity
  have hB₀small : B₀.carrier ⊆ (W.dilate eta).carrier := by
    apply hB₀phi.trans
    apply (BohrData.carrier_dilate_mono hphiOne).trans
    simpa using hEsmall
  exact ⟨{
    eta := eta
    Dbohr := Dbohr
    rhoD := rhoD
    theta := theta
    Ebohr := Ebohr
    rhoE := rhoE
    phi := phi
    B₀ := B₀
    rho₀ := rho₀
    eta_eq := rfl
    eta_pos := hetaPos
    eta_narrow := hetaNarrow
    D_eq := rfl
    rhoD_half := hrhoDhalf
    rhoD_one := hrhoDone
    D_regular := by simpa [Dbohr] using hDreg
    theta_eq := rfl
    theta_pos := hthetaPos
    theta_small := hthetaSmall
    E_eq := rfl
    rhoE_half := hrhoEhalf
    rhoE_one := hrhoEone
    E_regular := by simpa [Ebohr] using hEreg
    phi_eq := rfl
    phi_pos := hphiPos
    phi_small := hphiSmall
    B₀_eq := rfl
    rho₀_half := hrho₀half
    rho₀_one := hrho₀one
    B₀_regular := by simpa [B₀] using hB₀reg
    D_small := hDsmall
    E_small := hEsmall
    E_in_Dtheta := hEtheta
    B₀_small := hB₀small
    B₀_in_Ephi := hB₀phi }⟩

/-- Regularizing at a scale at least one half costs at most the standard
four-to-the-rank factor. -/
theorem card_le_four_pow_rank_mul_card_dilate_of_half_le
    (B : BohrData G) (rho : NNReal) (hrho : 1 / 2 ≤ rho) :
    B.carrier.card ≤ 4 ^ B.rank * (B.dilate rho).carrier.card := by
  have hhalf := B.card_unit_le_four_pow_rank_mul_card_half
  have hmono :
      (B.dilate (1 / 2)).carrier.card ≤ (B.dilate rho).carrier.card :=
    Finset.card_le_card (BohrData.carrier_dilate_mono hrho)
  calc
    B.carrier.card ≤ 4 ^ B.rank * (B.dilate (1 / 2)).carrier.card :=
      by simpa using hhalf
    _ ≤ 4 ^ B.rank * (B.dilate rho).carrier.card :=
      Nat.mul_le_mul_left _ hmono

/-- All three datums in the hierarchy retain the rank of the doubled
middle datum. -/
theorem smoothingHierarchy_ranks (W : BohrData G) (H : SmoothingHierarchy W) :
    H.Dbohr.rank = W.rank ∧ H.Ebohr.rank = W.rank ∧ H.B₀.rank = W.rank := by
  have hD : H.Dbohr.rank = W.rank := by
    rw [H.D_eq, BohrData.rank_dilate, BohrData.rank_dilate]
  have hE : H.Ebohr.rank = W.rank := by
    rw [H.E_eq, BohrData.rank_dilate, BohrData.rank_dilate]
    exact hD
  have hB : H.B₀.rank = W.rank := by
    rw [H.B₀_eq, BohrData.rank_dilate, BohrData.rank_dilate]
    exact hE
  constructor
  · exact hD
  constructor
  · exact hE
  · exact hB

/-- Explicit finite loss from the doubled middle carrier to the sampling
carrier.  The three factors are respectively the eta, theta, and phi
reciprocal dilates, each followed by a half-to-one regularization. -/
def smoothingHierarchyLoss (W : BohrData G) : ℕ :=
  ((3 * (1600 * max W.rank 1)) ^ W.rank * 4 ^ W.rank) *
    ((3 * (200 * max W.rank 1)) ^ W.rank * 4 ^ W.rank) *
    ((3 * (200 * max W.rank 1)) ^ W.rank * 4 ^ W.rank)

theorem smoothingHierarchy_card_loss
    (W : BohrData G) (H : SmoothingHierarchy W) :
    W.carrier.card ≤ smoothingHierarchyLoss W * H.B₀.carrier.card := by
  let Peta : ℕ := 1600 * max W.rank 1
  let Psmall : ℕ := 200 * max W.rank 1
  have hPeta : 0 < Peta := by dsimp [Peta]; positivity
  have hPsmall : 0 < Psmall := by dsimp [Psmall]; positivity
  have hranks := smoothingHierarchy_ranks W H
  have hWeta :
      W.carrier.card ≤ (3 * Peta) ^ W.rank *
        (W.dilate H.eta).carrier.card := by
    have hscale :=
      BohrData.card_dilate_le_three_mul_pow_rank_mul_card_div W 1 hPeta
    rw [H.eta_eq]
    simpa [Peta, div_eq_mul_inv] using hscale
  have hEtaD :
      (W.dilate H.eta).carrier.card ≤ 4 ^ W.rank * H.Dbohr.carrier.card := by
    rw [H.D_eq]
    simpa only [BohrData.rank_dilate] using
      card_le_four_pow_rank_mul_card_dilate_of_half_le
        (W.dilate H.eta) H.rhoD H.rhoD_half
  have hDEbase :
      H.Dbohr.carrier.card ≤ (3 * Psmall) ^ W.rank *
        (H.Dbohr.dilate H.theta).carrier.card := by
    have hscale :=
      BohrData.card_dilate_le_three_mul_pow_rank_mul_card_div H.Dbohr 1 hPsmall
    rw [H.theta_eq]
    simpa [Psmall, hranks.1, div_eq_mul_inv] using hscale
  have hbaseE :
      (H.Dbohr.dilate H.theta).carrier.card ≤
        4 ^ W.rank * H.Ebohr.carrier.card := by
    rw [H.E_eq]
    simpa [hranks.1] using
      card_le_four_pow_rank_mul_card_dilate_of_half_le
        (H.Dbohr.dilate H.theta) H.rhoE H.rhoE_half
  have hEBbase :
      H.Ebohr.carrier.card ≤ (3 * Psmall) ^ W.rank *
        (H.Ebohr.dilate H.phi).carrier.card := by
    have hscale :=
      BohrData.card_dilate_le_three_mul_pow_rank_mul_card_div H.Ebohr 1 hPsmall
    rw [H.phi_eq]
    simpa [Psmall, hranks.2.1, div_eq_mul_inv] using hscale
  have hbaseB :
      (H.Ebohr.dilate H.phi).carrier.card ≤
        4 ^ W.rank * H.B₀.carrier.card := by
    rw [H.B₀_eq]
    simpa [hranks.2.1] using
      card_le_four_pow_rank_mul_card_dilate_of_half_le
        (H.Ebohr.dilate H.phi) H.rho₀ H.rho₀_half
  unfold smoothingHierarchyLoss
  calc
    W.carrier.card ≤ (3 * Peta) ^ W.rank *
        (W.dilate H.eta).carrier.card := hWeta
    _ ≤ (3 * Peta) ^ W.rank * (4 ^ W.rank * H.Dbohr.carrier.card) :=
      Nat.mul_le_mul_left _ hEtaD
    _ ≤ ((3 * Peta) ^ W.rank * 4 ^ W.rank) *
        ((3 * Psmall) ^ W.rank *
          (H.Dbohr.dilate H.theta).carrier.card) := by
      have h := Nat.mul_le_mul_left
        ((3 * Peta) ^ W.rank * 4 ^ W.rank) hDEbase
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    _ ≤ ((3 * Peta) ^ W.rank * 4 ^ W.rank) *
        ((3 * Psmall) ^ W.rank * (4 ^ W.rank * H.Ebohr.carrier.card)) := by
      gcongr
    _ ≤ ((3 * Peta) ^ W.rank * 4 ^ W.rank) *
        (((3 * Psmall) ^ W.rank * 4 ^ W.rank) *
          ((3 * Psmall) ^ W.rank *
            (H.Ebohr.dilate H.phi).carrier.card)) := by
      have h := Nat.mul_le_mul_left
        (((3 * Peta) ^ W.rank * 4 ^ W.rank) *
          ((3 * Psmall) ^ W.rank * 4 ^ W.rank)) hEBbase
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    _ ≤ ((3 * Peta) ^ W.rank * 4 ^ W.rank) *
        (((3 * Psmall) ^ W.rank * 4 ^ W.rank) *
          ((3 * Psmall) ^ W.rank * (4 ^ W.rank * H.B₀.carrier.card))) := by
      gcongr
    _ = (((3 * (1600 * max W.rank 1)) ^ W.rank * 4 ^ W.rank) *
        ((3 * (200 * max W.rank 1)) ^ W.rank * 4 ^ W.rank) *
        ((3 * (200 * max W.rank 1)) ^ W.rank * 4 ^ W.rank)) *
        H.B₀.carrier.card := by
      simp [Peta, Psmall]
      ring


/-- The autocorrelation of two sets in the same eta-dilate is supported in
the fourfold eta-dilate.  This is the only support calculation needed for
the two-Bohr smoothing weight. -/
theorem smoothingWeight_support_subset_four_dilate
    (W : BohrData G) {D E : Finset G} {eta : NNReal}
    (hD : D ⊆ (W.dilate eta).carrier)
    (hE : E ⊆ (W.dilate eta).carrier) :
    ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (W.dilate (4 * eta)).carrier := by
  intro t ht
  have htSupport :
      t ∈ Function.support (LocalizedUnbalancing.smoothingWeight D E) := ht
  have hbaseNonneg :
      0 ≤ LocalizedUnbalancing.smoothingBase D E := by
    simp [LocalizedUnbalancing.smoothingBase]
  have htDiff : t ∈ (D + E) - (D + E) := by
    rw [LocalizedUnbalancing.smoothingWeight,
      support_dddconv hbaseNonneg hbaseNonneg,
      LocalizedUnbalancing.smoothingBase,
      support_ddconv mu_nonneg mu_nonneg,
      support_mu, support_mu] at htSupport
    simpa only [← coe_add, ← coe_sub, mem_coe] using htSupport
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp htDiff
  obtain ⟨d₁, hd₁, e₁, he₁, rfl⟩ := Finset.mem_add.mp hu
  obtain ⟨d₂, hd₂, e₂, he₂, rfl⟩ := Finset.mem_add.mp hv
  have hu' :
      d₁ + e₁ ∈ (W.dilate (eta + eta)).carrier :=
    BohrData.add_mem_dilate (hD hd₁) (hE he₁)
  have hv' :
      d₂ + e₂ ∈ (W.dilate (eta + eta)).carrier :=
    BohrData.add_mem_dilate (hD hd₂) (hE he₂)
  have hsub :
      (d₁ + e₁) - (d₂ + e₂) ∈
        (W.dilate ((eta + eta) + (eta + eta))).carrier :=
    BohrData.sub_mem_dilate hu' hv'
  simpa [show (eta + eta) + (eta + eta) = 4 * eta by ring] using hsub

/-- The hierarchy smoothing weight is supported inside the first child once
the doubled middle carrier is identified with its concrete doubled Bohr
datum.  This is the support field of the final raw endpoint package. -/
theorem smoothing_support_of_hierarchy_twoScale
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ}
    (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    (W : BohrData G) (H : SmoothingHierarchy W)
    (hWcarrier : W.carrier = GroupCount.doubledFinset C.childTwo.carrier) :
    ∀ t,
      LocalizedUnbalancing.smoothingWeight H.Ebohr.carrier H.Dbohr.carrier t ≠ 0 →
      t ∈ (C.childOne.bohr.dilate
        ((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹)).carrier := by
  intro t ht
  have htFour :
      t ∈ (W.dilate (4 * H.eta)).carrier :=
    smoothingWeight_support_subset_four_dilate W H.E_small H.D_small t ht
  have hfourOne : 4 * H.eta ≤ (1 : NNReal) := by
    calc
      4 * H.eta ≤
          1 / (400 * (max W.rank 1 : ℕ) : NNReal) := H.eta_narrow
      _ ≤ 1 := by
        rw [div_le_one]
        · exact_mod_cast (show 1 ≤ 400 * max W.rank 1 by omega)
        · positivity
  have htW : t ∈ W.carrier := by
    simpa only [BohrData.dilate_one] using
      (BohrData.carrier_dilate_mono hfourOne htFour)
  rw [hWcarrier] at htW
  exact C.doubled_middle_small htW

/-- The Croot sumset attached to the sampling carrier of a smoothing
hierarchy.  Naming it keeps the nested pointwise operations out of later
quantitative theorem signatures. -/
def hierarchyCrootSumset
    (W : BohrData G) (H : SmoothingHierarchy W) (A₂ : Finset G) : Finset G :=
  (-A₂) + H.B₀.carrier

def hierarchyCrootCard
    (W : BohrData G) (H : SmoothingHierarchy W) (A₂ : Finset G) : ℝ :=
  (hierarchyCrootSumset W H A₂).card

def hierarchySampleCard
    (W : BohrData G) (H : SmoothingHierarchy W) : ℝ :=
  H.B₀.carrier.card

def hierarchyNegCard (A₂ : Finset G) : ℝ :=
  (-A₂).card

section HierarchyRelativeT

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

def hierarchyBeta
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (W : BohrData G) (H : SmoothingHierarchy W)
    (_data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (k : ℕ) : ℝ :=
  ((DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p / 2) ^ k) / 2

/-- The three-level hierarchy turns the raw relative-T Croot lower bound
into a genuine density lower bound inside the sampling carrier B₀.

Here the large raw smoothing set is H.Dbohr and the small raw smoothing set
is H.Ebohr.  The sifting output A₂ lies in the small carrier, while B₀ lies
in a tiny phi-dilate of that carrier.  Rank regularity then bounds
|-A₂+B₀| by twice the small-carrier size, so the resulting beta has no
dependence on the current Bohr rank. -/
theorem hierarchy_relativeT_beta
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (W : BohrData G) (H : SmoothingHierarchy W)
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (k : ℕ) (T : Finset G)
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ))) :
    ((((DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p / 2) ^ k) /
        2) * hierarchySampleCard W H) ≤ (T.card : ℝ) := by
  have houtputs := data.output_nonempty hdelta
  have hEcardPos : (0 : ℝ) < H.Ebohr.carrier.card := by
    exact_mod_cast H.Ebohr.carrier_nonempty.card_pos
  have hAdense :
      DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p *
          (H.Ebohr.carrier.card : ℝ) ≤ (data.A₂.card : ℝ) := by
    exact (le_div_iff₀ hEcardPos).mp data.density_two
  have hnegAdense :
      DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p *
          (H.Ebohr.carrier.card : ℝ) ≤ ((-data.A₂).card : ℝ) := by
    simpa using hAdense
  have hsumNat :
      (hierarchyCrootSumset W H data.A₂).card ≤
        2 * H.Ebohr.carrier.card := by
    unfold hierarchyCrootSumset
    apply card_neg_add_small_le_two_mul_card H.Ebohr H.E_regular
      data.A₂ (H.B₀).carrier data.subset_two H.B₀_in_Ephi H.phi_small
  have hsum :
      hierarchyCrootCard W H data.A₂ ≤
        2 * (H.Ebohr.carrier.card : ℝ) := by
    unfold hierarchyCrootCard
    exact_mod_cast hsumNat
  have halpha :
      0 ≤ DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p := by
    unfold DensityStep.siftingDensityLower
    positivity
  have hnegA : (-data.A₂).Nonempty := by
    obtain ⟨a, ha⟩ := houtputs.2
    exact ⟨-a, by simpa using ha⟩
  simpa only [hierarchyNegCard, hierarchySampleCard, hierarchyCrootCard,
    hierarchyCrootSumset, show (2 : ℝ) = 2 by rfl] using
    (croot_beta_mul_card_le_of_two_carriers
      (A := -data.A₂) (S := (H.B₀).carrier) (T := T)
      (D := H.Ebohr.carrier) k halpha (by norm_num : (0 : ℝ) < 2)
      hnegA (H.B₀).carrier_nonempty hnegAdense hsum hT)

/-- The same local Croot estimate gives the uniform natural-number rank
cap used by the localized package. -/
theorem hierarchy_delta_card_le_of_croot
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (W : BohrData G) (H : SmoothingHierarchy W)
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (k : ℕ) (T : Finset G) (Delta : Finset (AddChar G Complex))
    (hbeta : 0 <
      hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
        (delta := delta) W H data k)
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ)))
    (hDelta : (Delta.card : ℝ) ≤
      RelativeChangSanders.localChangDimension H.B₀ T (1 / 2)) :
    Delta.card ≤
      ⌈8 * (1 + Real.log (2 /
        hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
          (delta := delta) W H data k))⌉₊ := by
  have hTbeta :
      hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
          (delta := delta) W H data k * (H.B₀.carrier.card : ℝ) ≤
        (T.card : ℝ) := by
    simpa [hierarchyBeta, hierarchySampleCard] using
      hierarchy_relativeT_beta W H data hdelta k T hT
  have hdim :
      RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) ≤
        8 * (1 + Real.log (2 /
          hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
            (delta := delta) W H data k)) :=
    localChangDimension_half_le_of_mul_card_le H.B₀ T hbeta
      (by
        have hpos : (0 : ℝ) <
            hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
              (delta := delta) W H data k *
            (H.B₀.carrier.card : ℝ) :=
          mul_pos hbeta (by exact_mod_cast H.B₀.carrier_nonempty.card_pos)
        have hTpos : (0 : ℝ) < T.card := hpos.trans_le hTbeta
        exact Finset.card_pos.mp (by exact_mod_cast hTpos))
      hTbeta
  exact card_le_natCeil_of_cast_card_le Delta (hDelta.trans hdim)

/-- The real-valued companion to the preceding cardinality bound.  This is
kept separate because the spectral quantizer depends on the Chang dimension
itself, not just on the cardinality of the chosen spectrum. -/
theorem hierarchy_dimension_le_of_croot
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (W : BohrData G) (H : SmoothingHierarchy W)
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (k : ℕ) (T : Finset G)
    (hbeta : 0 <
      hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
        (delta := delta) W H data k)
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ))) :
    RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) ≤
      8 * (1 + Real.log (2 /
        hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
          (delta := delta) W H data k)) := by
  have hTbeta :
      hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
          (delta := delta) W H data k * (H.B₀.carrier.card : ℝ) ≤
        (T.card : ℝ) := by
    simpa [hierarchyBeta, hierarchySampleCard] using
      hierarchy_relativeT_beta W H data hdelta k T hT
  apply localChangDimension_half_le_of_mul_card_le H.B₀ T hbeta
  · have hpos : (0 : ℝ) <
        hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
            (delta := delta) W H data k *
          (H.B₀.carrier.card : ℝ) :=
      mul_pos hbeta (by exact_mod_cast H.B₀.carrier_nonempty.card_pos)
    have hTpos : (0 : ℝ) < T.card := hpos.trans_le hTbeta
    exact Finset.card_pos.mp (by exact_mod_cast hTpos)
  · exact hTbeta

end HierarchyRelativeT

/-- The fixed Holder exponent 4(d+1) is already enough for the dense-pair
loss 1/512 on a dyadic-density state. -/
theorem densePairDensity_power_of_dyadic
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {d : ℕ}
    (hscale : (1 / (2 : ℝ) ^ d) ≤ s.density) :
    (2 / 3 : ℝ) ^ (4 * (d + 1)) ≤
      (1 - (1 / 512 : ℝ)) * s.density := by
  have hbase : (2 / 3 : ℝ) ^ 4 ≤ 1 / 2 := by norm_num
  have hpow :
      (2 / 3 : ℝ) ^ (4 * (d + 1)) ≤ (1 / 2 : ℝ) ^ (d + 1) := by
    calc
      (2 / 3 : ℝ) ^ (4 * (d + 1)) =
          ((2 / 3 : ℝ) ^ 4) ^ (d + 1) := by rw [pow_mul]
      _ ≤ (1 / 2 : ℝ) ^ (d + 1) :=
        pow_le_pow_left₀ (by positivity) hbase (d + 1)
  have hdecay :
      (1 / 2 : ℝ) ^ (d + 1) ≤
        (511 / 512 : ℝ) * (1 / (2 : ℝ) ^ d) := by
    have hpowNonneg : 0 ≤ (1 / 2 : ℝ) ^ d := by positivity
    rw [pow_succ]
    calc
      (1 / 2 : ℝ) ^ d * (1 / 2) ≤
          (1 / 2 : ℝ) ^ d * (511 / 512) :=
        mul_le_mul_of_nonneg_left (by norm_num) hpowNonneg
      _ = (511 / 512 : ℝ) * (1 / (2 : ℝ) ^ d) := by
        simp [one_div, inv_pow, mul_comm]
  calc
    (2 / 3 : ℝ) ^ (4 * (d + 1)) ≤ (1 / 2 : ℝ) ^ (d + 1) := hpow
    _ ≤ (511 / 512 : ℝ) * (1 / (2 : ℝ) ^ d) := hdecay
    _ ≤ (511 / 512 : ℝ) * s.density :=
      mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = (1 - (1 / 512 : ℝ)) * s.density := by ring

/-- Convert the concrete two-scale children into the exact rank-regular
narrowing object consumed by FinalAssembly.RawConcreteSupply.  This is the
plateau-free geometry component of that final interface. -/
noncomputable def rankRegularNarrowingPackage_of_reciprocalChildren
    {original : Finset G}
    (s : FinalAssembly.RankRegularLocatedRestriction original)
    {mOne mTwo : ℕ} (hmOne : 0 < mOne) (hmTwo : 0 < mTwo)
    (C : ReciprocalChildren s.located.restriction.bohr mOne mTwo)
    {epsilon sizeCost : ℝ} {rankCost : ℕ}
    (hnum : ReciprocalStepBounds s.located mOne mTwo epsilon sizeCost) :
    FinalAssembly.RankRegularNarrowingPackage s epsilon sizeCost rankCost := by
  have hfactorOnePos :
      (0 : ℝ) < (reciprocalLoss s.located.restriction.bohr mOne : ℝ) := by
    unfold reciprocalLoss
    positivity
  have hfactorTwoPos :
      (0 : ℝ) <
        (twoReciprocalLoss s.located.restriction.bohr mOne mTwo : ℝ) := by
    unfold twoReciprocalLoss reciprocalLoss
    positivity
  have hvolOne :
      (s.located.restriction.bohr.carrier.card : ℝ) ≤
        (reciprocalLoss s.located.restriction.bohr mOne : ℝ) *
          (C.childOne.carrier.card : ℝ) := by
    exact_mod_cast C.cardOne
  have hvolTwo :
      (s.located.restriction.bohr.carrier.card : ℝ) ≤
        (twoReciprocalLoss s.located.restriction.bohr mOne mTwo : ℝ) *
          (C.childTwo.carrier.card : ℝ) := by
    exact_mod_cast C.cardTwo
  have hcardOne :
      Real.exp (-sizeCost) * (s.card : ℝ) ≤ C.childOne.carrier.card := by
    simpa [FinalAssembly.RankRegularLocatedRestriction.card] using
      child_card_of_loss s.located hfactorOnePos hnum.card_budget_one hvolOne
  have hcardTwo :
      Real.exp (-sizeCost) * (s.card : ℝ) ≤ C.childTwo.carrier.card := by
    simpa [FinalAssembly.RankRegularLocatedRestriction.card] using
      child_card_of_loss s.located hfactorTwoPos hnum.card_budget_two hvolTwo
  have hdensityEq :
      relativeDensityOn s.located.restriction.set
          s.located.restriction.bohr.carrier = s.located.density := by
    unfold DensityStep.LocatedRestriction.density
      BohrStopping.RegularRestriction.density relativeDensityOn
      BohrStopping.RegularRestriction.ambient
    simp [s.outer_one]
  refine
    { kappa := (mOne : NNReal)⁻¹
      kappa_small := hnum.scale_rank
      childOne := C.childOne
      childTwo := C.childTwo
      childOne_outer_one := C.childOne_outer_one
      childTwo_outer_one := C.childTwo_outer_one
      childOne_rankRegular := C.childOne_rankRegular
      childTwo_rankRegular := C.childTwo_rankRegular
      smallOne := C.smallOne
      smallTwo := C.smallTwo
      narrowing_small := ?_
      rankOne := ?_
      rankTwo := ?_
      cardOne := hcardOne
      cardTwo := hcardTwo }
  · simpa only [hdensityEq] using hnum.scale_density
  · rw [C.rankOne]
    simp [FinalAssembly.RankRegularLocatedRestriction.rank,
      DensityStep.LocatedRestriction.rank, BohrStopping.RegularRestriction.rank]
  · rw [C.rankTwo]
    simp [FinalAssembly.RankRegularLocatedRestriction.rank,
      DensityStep.LocatedRestriction.rank, BohrStopping.RegularRestriction.rank]

/-! ## Plateau-free Holder fibres -/

/-- Endpoint fibre selected from a rank-regular dense pair. -/
def endpointSet {original : Finset G}
    (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon) : Finset G :=
  DensityStep.narrowingSet s.restriction.set childOne.carrier
    (GroupCount.densePairPoint hdense)

/-- Middle-term fibre selected from the same dense-pair point. -/
def middleSet {original : Finset G}
    (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon) : Finset G :=
  DensityStep.narrowingSet s.restriction.set childTwo.carrier
    (GroupCount.densePairPoint hdense)

/-- The common density retained by a rank-regular dense pair. -/
def densePairDensity {original : Finset G}
    (s : DensityStep.LocatedRestriction original) (epsilon : ℝ) : ℝ :=
  (1 - epsilon) * s.density

/-- The selected endpoint fibre is nonempty whenever the dense-pair loss is
strictly below one.  This is the exact nonemptiness field of the final raw
two-Bohr package, factored out so the analytic construction never has to
replay the local-density argument. -/
theorem endpointSet_nonempty
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    (endpointSet s childOne childTwo hdense).Nonempty := by
  let alpha := densePairDensity s epsilon
  have halpha : 0 < alpha :=
    mul_pos (sub_pos.mpr hepsilon_lt_one) s.density_pos
  have hOne : alpha ≤
      localDensity s.restriction.set childOne.carrier
        (GroupCount.densePairPoint hdense) := by
    simpa [alpha, densePairDensity] using
      GroupCount.densePairPoint_density_one hdense
  apply DensityStep.narrowingSet_nonempty_of_localDensity_pos
    childOne.carrier_nonempty
  exact halpha.trans_le hOne

/-- The selected endpoint fibre lies in the first actual child carrier. -/
theorem endpointSet_subset_childOne
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon) :
    endpointSet s childOne childTwo hdense ⊆ childOne.carrier := by
  exact DensityStep.narrowingSet_subset_carrier
    (B := childOne.bohr) (rho := childOne.outer)
    (A := s.restriction.set) (C := childOne.carrier)
    (x := GroupCount.densePairPoint hdense) (fun _ hz ↦ hz)

/-- Plateau-free version of the concrete Holder certificate constructor.
Only the actual children and their simultaneous dense translate are used. -/
noncomputable def holderCountCertificateOfDensePair
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon)
    (_hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    {p : ℕ} (hp : 0 < p) (f : G → ℝ)
    (hpDensity : (2 / 3 : ℝ) ^ p ≤ densePairDensity s epsilon)
    (happrox :
      |(GroupCount.normalizedMixedProgression
            (endpointSet s childOne childTwo hdense)
            (middleSet s childOne childTwo hdense) -
          (Fintype.card G : ℝ) / (#childOne.carrier : ℝ)) -
          HolderLifting.pairing f
            (GroupCount.doubledFinset
              (middleSet s childOne childTwo hdense))| ≤
        ((Fintype.card G : ℝ) / (#childOne.carrier : ℝ)) / 8)
    (hbalanced :
      BalancedRestriction.weightedLpNorm
          (normalizedIndicator (GroupCount.doubledFinset childTwo.carrier))
          f p ≤
        ((Fintype.card G : ℝ) / (#childOne.carrier : ℝ)) / 8) :
    GroupCount.HolderCountCertificate original := by
  let x : G := GroupCount.densePairPoint hdense
  let A' : Finset G := endpointSet s childOne childTwo hdense
  let A'' : Finset G := middleSet s childOne childTwo hdense
  let B : Finset G := childOne.carrier
  let B' : Finset G := childTwo.carrier
  let alpha : ℝ := densePairDensity s epsilon
  have hOne : alpha ≤ localDensity s.restriction.set B x := by
    simpa [alpha, x, B, densePairDensity] using
      GroupCount.densePairPoint_density_one hdense
  have hTwo : alpha ≤ localDensity s.restriction.set B' x := by
    simpa [alpha, x, B', densePairDensity] using
      GroupCount.densePairPoint_density_two hdense
  have halpha : 0 < alpha := by
    exact mul_pos (sub_pos.mpr hepsilon_lt_one) s.density_pos
  have hA' : A'.Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos
      childOne.carrier_nonempty
    exact halpha.trans_le hOne
  have hA'' : A''.Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos
      childTwo.carrier_nonempty
    exact halpha.trans_le hTwo
  have hA''B' : A'' ⊆ B' := by
    exact DensityStep.narrowingSet_subset_carrier
      (B := childTwo.bohr) (rho := childTwo.outer)
      (A := s.restriction.set) (C := childTwo.carrier)
      (x := x) (fun _ hz ↦ hz)
  have hA'trans : ∀ z ∈ A', z - (s.shift - x) ∈ original := by
    intro z hz
    have hzSource : x + z ∈ s.restriction.set :=
      (DensityStep.mem_narrowingSet.mp hz).2
    have hs := s.subset_original (x + z) hzSource
    have heq : z - (s.shift - x) = (x + z) - s.shift := by abel
    rwa [heq]
  have hA''trans : ∀ z ∈ A'', z - (s.shift - x) ∈ original := by
    intro z hz
    have hzSource : x + z ∈ s.restriction.set :=
      (DensityStep.mem_narrowingSet.mp hz).2
    have hs := s.subset_original (x + z) hzSource
    have heq : z - (s.shift - x) = (x + z) - s.shift := by abel
    rwa [heq]
  have hDensityOne : alpha * (#B : ℝ) ≤ (#A' : ℝ) := by
    have hBpos : (0 : ℝ) < #B := by
      exact_mod_cast childOne.carrier_nonempty.card_pos
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      childOne.carrier_nonempty x] at hOne
    exact (le_div_iff₀ hBpos).mp hOne
  have hDensityTwo : alpha * (#B' : ℝ) ≤ (#A'' : ℝ) := by
    have hB'pos : (0 : ℝ) < #B' := by
      exact_mod_cast childTwo.carrier_nonempty.card_pos
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      childTwo.carrier_nonempty x] at hTwo
    exact (le_div_iff₀ hB'pos).mp hTwo
  have hRelative :
      (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B' := by
    calc
      (2 / 3 : ℝ) ^ p ≤ alpha := hpDensity
      _ ≤ localDensity s.restriction.set B' x := by
        simpa [alpha, x, B', densePairDensity] using
          GroupCount.densePairPoint_density_two hdense
      _ = HolderLifting.relativeDensity A'' B' := by
        rw [DensityStep.localDensity_eq_card_narrowingSet_div
          childTwo.carrier_nonempty x]
        rfl
  have hDoubledB' : (GroupCount.doubledFinset B').Nonempty :=
    GroupCount.doubledFinset_nonempty childTwo.carrier_nonempty
  have hMoment :
      HolderLifting.localMoment (GroupCount.doubledFinset B') p f ≤
        (((Fintype.card G : ℝ) / (#B : ℝ)) / 8) ^ p := by
    apply GroupCount.localMoment_le_of_weightedLpNorm_le
      hDoubledB' hp f (by positivity)
    simpa [B, B'] using hbalanced
  exact
    { A' := A'
      A'' := A''
      B := B
      B' := B'
      translate := s.shift - x
      alpha := alpha
      p := p
      f := f
      A'_nonempty := hA'
      A''_nonempty := hA''
      B_nonempty := childOne.carrier_nonempty
      A''_subset_B' := hA''B'
      A'_sub_translate := hA'trans
      A''_sub_translate := hA''trans
      alpha_nonneg := halpha.le
      A'_density := hDensityOne
      A''_density := hDensityTwo
      p_pos := hp
      doubled_density := hRelative
      approximation := by simpa [A', A'', B] using happrox
      balanced_moment := hMoment }

/-- The actual located restriction whose set is the endpoint fibre.  This is
the state on which the high-smoothing-norm theorem must run, so subsequent
cardinality losses compose honestly. -/
noncomputable def endpointLocated
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    DensityStep.LocatedRestriction original := by
  let x := GroupCount.densePairPoint hdense
  have hfactor : 0 < densePairDensity s epsilon :=
    mul_pos (sub_pos.mpr hepsilon_lt_one) s.density_pos
  have hx : densePairDensity s epsilon ≤
      localDensity s.restriction.set childOne.carrier x := by
    simpa [x, densePairDensity] using
      GroupCount.densePairPoint_density_one hdense
  exact DensityStep.narrowLocated s childOne x (hfactor.trans_le hx)

@[simp] theorem endpointLocated_set
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    (endpointLocated s childOne childTwo hdense hepsilon_lt_one).restriction.set =
      endpointSet s childOne childTwo hdense := by
  rfl

/-- The endpoint fibre is no larger than the current located state. -/
theorem endpointLocated_card_le_state_card
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (hmOne : 0 < mOne)
    (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (houter : s.restriction.outer = 1) :
    (endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card ≤ s.card := by
  have hmOneInv : ((mOne : NNReal)⁻¹) ≤ 1 := by
    apply (inv_le_one₀ (by exact_mod_cast hmOne)).2
    exact_mod_cast (show 1 ≤ mOne by omega)
  have hchild : C.childOne.carrier.card ≤ s.restriction.bohr.carrier.card := by
    calc
      C.childOne.carrier.card ≤
          (s.restriction.bohr.dilate ((mOne : NNReal)⁻¹)).carrier.card :=
        Finset.card_le_card C.smallOne
      _ ≤ (s.restriction.bohr.dilate 1).carrier.card :=
        Finset.card_le_card (BohrData.carrier_dilate_mono hmOneInv)
      _ = s.restriction.bohr.carrier.card := by simp
  calc
    (endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card =
        C.childOne.carrier.card := by
      simp [endpointLocated, DensityStep.narrowLocated,
        DensityStep.RegularChild.asRestriction,
        DensityStep.LocatedRestriction.card, BohrStopping.RegularRestriction.card,
        BohrStopping.RegularRestriction.ambient, C.childOne_outer_one,
        C.childOne_carrier]
    _ ≤ s.restriction.bohr.carrier.card := hchild
    _ = s.card := by
      unfold DensityStep.LocatedRestriction.card BohrStopping.RegularRestriction.card
        BohrStopping.RegularRestriction.ambient
      simp [houter]

/-- The whole two-scale/hierarchy geometry compares the endpoint fibre to
the final sampling carrier by one explicit finite loss. -/
theorem endpoint_card_le_globalHierarchyLoss
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (hmOne : 0 < mOne)
    (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (houter : s.restriction.outer = 1)
    (W : BohrData G) (H : SmoothingHierarchy W)
    (hWcard : W.carrier.card = C.childTwo.carrier.card) :
    ((endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card : ℝ) ≤
      ((twoReciprocalLoss s.restriction.bohr mOne mTwo *
          smoothingHierarchyLoss W : ℕ) : ℝ) * (H.B₀.carrier.card : ℝ) := by
  have hendpoint :
      (endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card ≤
        s.card :=
    endpointLocated_card_le_state_card s hmOne C hdense hepsilon_lt_one houter
  have hstate :
      s.card ≤ twoReciprocalLoss s.restriction.bohr mOne mTwo * W.carrier.card := by
    have hC := C.cardTwo
    unfold DensityStep.LocatedRestriction.card BohrStopping.RegularRestriction.card
      BohrStopping.RegularRestriction.ambient
    rw [hWcard]
    simpa [houter] using hC
  have hhier := smoothingHierarchy_card_loss W H
  have hnat :
      (endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card ≤
        (twoReciprocalLoss s.restriction.bohr mOne mTwo *
          smoothingHierarchyLoss W) * H.B₀.carrier.card := by
    calc
      (endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card ≤
          s.card := hendpoint
      _ ≤ twoReciprocalLoss s.restriction.bohr mOne mTwo * W.carrier.card := hstate
      _ ≤ twoReciprocalLoss s.restriction.bohr mOne mTwo *
          (smoothingHierarchyLoss W * H.B₀.carrier.card) :=
        Nat.mul_le_mul_left _ hhier
      _ = (twoReciprocalLoss s.restriction.bohr mOne mTwo *
          smoothingHierarchyLoss W) * H.B₀.carrier.card := by ring
  exact_mod_cast hnat

section EndpointHighNorm

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- Rewrite the DRC sifted-density lower bound in the normalized
autocorrelation scale used by the high-norm branch.

The indicator correlation is |A|² times the probability correlation, while
the DRC denominator is |A|^(2p).  After taking the weighted p-norm, one
factor |A| remains.  This is the normalization identity that turns endpoint
density into a d-only lower bound for the later relative-T sample. -/
theorem siftingDensityLower_eq_normalizedLp
    (A B₁ B₂ : Finset G) {p : ℕ} (hp : 0 < p) :
    DensityStep.siftingDensityLower A B₁ B₂ p =
      (4 : ℝ)⁻¹ *
        ((A.card : ℝ) *
          BalancedRestriction.weightedLpNorm
            (fun x : G => ((μ_[ℝ≥0] B₁ ○ᵈ μ B₂) x : ℝ))
            (μ_[ℝ] A ○ᵈ μ A) p) ^ (2 * p) := by
  let w : G → ℝ≥0 := μ B₁ ○ᵈ μ B₂
  have hcorr :
      (𝟭_[A, Real] ○ᵈ 𝟭_[A]) =
        ((A.card : ℝ) ^ 2) • (μ_[ℝ] A ○ᵈ μ A) := by
    rw [← card_smul_mu ℝ A, smul_dddconv, dddconv_smul]
    funext x
    simp [Pi.smul_apply, smul_eq_mul, pow_two]
    ring
  have hscale :=
    LocalizedUnbalancing.weightedLpNorm_smul_of_nonneg w
      (μ_[ℝ] A ○ᵈ μ A) ((A.card : ℝ) ^ 2) (by positivity) hp
  have hnorm :
      ‖𝟭_[A, Real] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] =
        (A.card : ℝ) ^ 2 *
          BalancedRestriction.weightedLpNorm
            ((↑) ∘ w)
            (μ_[ℝ] A ○ᵈ μ A) p := by
    rw [hcorr]
    simpa only [LocalizedUnbalancing.weightedLpNorm_eq_wLpNorm w
      ((A.card : ℝ) ^ 2 • (μ_[ℝ] A ○ᵈ μ A)) hp] using hscale
  dsimp [w, Function.comp_def] at hnorm
  rw [DensityStep.siftingDensityLower, hnorm]
  by_cases hA0 : (A.card : ℝ) = 0
  · have htwo : 2 * p ≠ 0 := by omega
    simp [hA0, htwo]
  have hpow : (A.card : ℝ) ^ (2 * p) ≠ 0 := pow_ne_zero _ hA0
  field_simp [hpow]
  ring

/-- The DRC density lower bound is genuinely positive whenever the original
set and the two local base carriers meet.  This is the positivity input for
the relative-T Chang estimate; it is not obtained from the sifted output
inequalities, which are only upper bounds on the lower density. -/
theorem siftingDensityLower_pos_of_nonempty
    (A B₁ B₂ : Finset G) {p : ℕ} (hp : 0 < p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    0 < DensityStep.siftingDensityLower A B₁ B₂ p := by
  classical
  have hp0 : p ≠ 0 := hp.ne'
  have hB₁ : B₁.Nonempty := hB.mono Finset.inter_subset_left
  have hB₂ : B₂.Nonempty := hB.mono Finset.inter_subset_right
  let N : ℝ := ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂]
  have hsumEq :=
    DensityStep.sum_card_siftedSet_mul_card_siftedSet A B₁ B₂ p hp0 hB₁ hB₂
  obtain ⟨b, hb⟩ := hB
  obtain ⟨a, ha⟩ := hA
  let u₀ : Fin p → G := fun _ ↦ b - a
  have hA₁u₀ : b ∈ Sifting.siftedSet A B₁ u₀ := by
    simp only [Sifting.mem_siftedSet, u₀]
    refine ⟨Finset.inter_subset_left hb, ?_⟩
    intro i
    have : b - (b - a) = a := by abel
    rwa [this]
  have hA₂u₀ : b ∈ Sifting.siftedSet A B₂ u₀ := by
    simp only [Sifting.mem_siftedSet, u₀]
    refine ⟨Finset.inter_subset_right hb, ?_⟩
    intro i
    have : b - (b - a) = a := by abel
    rwa [this]
  have hsumPos :
      0 < ∑ u : Fin p → G,
        ((Sifting.siftedSet A B₁ u).card : ℝ) *
          (Sifting.siftedSet A B₂ u).card := by
    apply Finset.sum_pos'
    · intro u hu
      positivity
    · refine ⟨u₀, Finset.mem_univ _, ?_⟩
      exact mul_pos
        (by exact_mod_cast (Finset.card_pos.mpr ⟨b, hA₁u₀⟩))
        (by exact_mod_cast (Finset.card_pos.mpr ⟨b, hA₂u₀⟩))
  have hNp : 0 < N ^ p := by
    rw [hsumEq] at hsumPos
    have hcards : 0 < (B₁.card : ℝ) * B₂.card := by positivity
    rcases mul_pos_iff.mp hsumPos with hpos | hneg
    · simpa [N] using hpos.2
    · exact (not_lt_of_ge hcards.le hneg.1).elim
  have hNnonneg : 0 ≤ N := by
    dsimp [N]
    positivity
  have hNne : N ≠ 0 := by
    intro hN0
    rw [hN0] at hNp
    simp [hp0] at hNp
  have hNpos : 0 < N := lt_of_le_of_ne hNnonneg (Ne.symm hNne)
  unfold DensityStep.siftingDensityLower
  have hAcard : (0 : ℝ) < A.card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨a, ha⟩)
  dsimp [N] at hNpos
  positivity

/-- In the large/small hierarchy orientation, the commuted LocalAP ratio
of A₁-cardinality to supported-popular cardinality is bounded below by half
of any lower bound for the common sifted density.  This is exactly the
logarithmic ratio consumed by RawSupplyNumerics. -/
theorem supported_ratio_lower_of_hierarchy
    (H : SmoothingHierarchy W)
    {A : Finset G} {p : ℕ} {sigma delta alpha : ℝ} (z : G)
    (data : DensityStep.SiftedPopularData A
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (halpha : 0 ≤ alpha)
    (halpha_le :
      alpha ≤ DensityStep.siftingDensityLower A
        (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p) :
    alpha / 2 ≤
      (data.A₁.card : ℝ) /
        (DensityStep.SiftedPopularData.supportedPopularSet A
          (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma).card := by
  let S : Finset G :=
    DensityStep.SiftedPopularData.supportedPopularSet A
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma
  have hSnonempty : S.Nonempty := by
    simpa [S] using data.supportedPopularSet_nonempty hdelta
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hSnonempty.card_pos
  have hBcard :
      ((z +ᵥ H.Dbohr.carrier).card : ℝ) =
        (H.Dbohr.carrier.card : ℝ) := by
    simp
  have hAone :
      alpha * (H.Dbohr.carrier.card : ℝ) ≤ (data.A₁.card : ℝ) := by
    have hdense :
        alpha ≤ (data.A₁.card : ℝ) / (z +ᵥ H.Dbohr.carrier).card :=
      halpha_le.trans data.density_one
    rw [hBcard] at hdense
    have hDpos : (0 : ℝ) < H.Dbohr.carrier.card := by
      exact_mod_cast H.Dbohr.carrier_nonempty.card_pos
    exact (le_div_iff₀ hDpos).mp hdense
  have hScardNat :
      S.card ≤ 2 * H.Dbohr.carrier.card := by
    calc
      S.card ≤ ((z +ᵥ H.Dbohr.carrier) - H.Ebohr.carrier).card := by
        exact Finset.card_le_card
          (DensityStep.SiftedPopularData.supportedPopularSet_subset_sub
            A (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma)
      _ ≤ 2 * H.Dbohr.carrier.card :=
        card_vadd_sub_small_le_two_mul_card H.Dbohr H.D_regular
          H.Ebohr.carrier H.E_in_Dtheta H.theta_small z
  have hScard : (S.card : ℝ) ≤ 2 * (H.Dbohr.carrier.card : ℝ) := by
    exact_mod_cast hScardNat
  apply (le_div_iff₀ hSpos).2
  calc
    alpha / 2 * (S.card : ℝ) ≤
        alpha / 2 * (2 * (H.Dbohr.carrier.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hScard (by positivity)
    _ = alpha * (H.Dbohr.carrier.card : ℝ) := by ring
    _ ≤ (data.A₁.card : ℝ) := hAone

/-- Turn the favorable A₁/S ratio into the square-root reciprocal bound
appearing in the commuted LocalAP error term. -/
theorem sqrt_supported_ratio_le_two_div
    {A₁ S : Finset G} {alpha : ℝ}
    (halpha : 0 < alpha) (hA₁ : A₁.Nonempty) (hS : S.Nonempty)
    (hratio : alpha / 2 ≤ (A₁.card : ℝ) / S.card) :
    Real.sqrt ((S.card : ℝ) / A₁.card) ≤ Real.sqrt (2 / alpha) := by
  have hA₁pos : (0 : ℝ) < A₁.card := by exact_mod_cast hA₁.card_pos
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hmul : alpha / 2 * (S.card : ℝ) ≤ (A₁.card : ℝ) :=
    (le_div_iff₀ hSpos).mp hratio
  have hdiv : (S.card : ℝ) / A₁.card ≤ 2 / alpha := by
    apply (div_le_div_iff₀ hA₁pos halpha).2
    nlinarith
  exact Real.sqrt_le_sqrt hdiv

/-- RawSupplyNumerics pays the phase and tail terms, while a single width
input pays the regular-Bohr translation term.  Together they give the fixed
1/512 commuted LocalAP error target. -/
theorem dyadic_commuted_hsmall
    (d : ℕ) {rank : ℕ} {kappa : NNReal}
    {A₁ S : Finset G}
    (hA₁ : A₁.Nonempty) (hS : S.Nonempty)
    (hratio :
      RawSupplyNumerics.dyadicSiftedAlpha d / 2 ≤
        (A₁.card : ℝ) / S.card)
    (hwidth :
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (kappa + kappa : NNReal)) *
        Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) ≤
        1 / 2048) :
    2 * RawSupplyNumerics.approximationDelta +
        (2 / (RawSupplyNumerics.dyadicQQuant d : ℝ) +
          400 * ((max rank 1 : ℕ) : ℝ) *
            (kappa + kappa : NNReal) +
          2 * (1 / 2 : ℝ) ^ RawSupplyNumerics.dyadicTailExponent d) *
        Real.sqrt ((S.card : ℝ) / A₁.card) ≤ (1 / 512 : ℝ) := by
  have halphaPos := RawSupplyNumerics.dyadicSiftedAlpha_pos d
  have hsqrt :
      Real.sqrt ((S.card : ℝ) / A₁.card) ≤
        Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) :=
    sqrt_supported_ratio_le_two_div halphaPos hA₁ hS hratio
  have hphase :
      (2 / (RawSupplyNumerics.dyadicQQuant d : ℝ)) *
          Real.sqrt ((S.card : ℝ) / A₁.card) ≤ 1 / 2048 := by
    calc
      (2 / (RawSupplyNumerics.dyadicQQuant d : ℝ)) *
          Real.sqrt ((S.card : ℝ) / A₁.card) ≤
        (2 / (RawSupplyNumerics.dyadicQQuant d : ℝ)) *
          Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) := by
            gcongr
      _ ≤ 1 / 2048 := RawSupplyNumerics.dyadic_quantized_phase_mul_sqrt_le d
  have hwidth' :
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (kappa + kappa : NNReal)) *
        Real.sqrt ((S.card : ℝ) / A₁.card) ≤ 1 / 2048 := by
    calc
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (kappa + kappa : NNReal)) *
        Real.sqrt ((S.card : ℝ) / A₁.card) ≤
        (400 * ((max rank 1 : ℕ) : ℝ) *
          (kappa + kappa : NNReal)) *
        Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) := by
          gcongr
      _ ≤ 1 / 2048 := hwidth
  have htail :
      (2 * (1 / 2 : ℝ) ^ RawSupplyNumerics.dyadicTailExponent d) *
          Real.sqrt ((S.card : ℝ) / A₁.card) ≤ 1 / 2048 := by
    calc
      (2 * (1 / 2 : ℝ) ^ RawSupplyNumerics.dyadicTailExponent d) *
          Real.sqrt ((S.card : ℝ) / A₁.card) ≤
        (2 * (1 / 2 : ℝ) ^ RawSupplyNumerics.dyadicTailExponent d) *
          Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) := by
            gcongr
      _ ≤ 1 / 2048 := RawSupplyNumerics.dyadic_tail_error_mul_sqrt_le d
  unfold RawSupplyNumerics.approximationDelta
  nlinarith

/-- Natural denominator behind the deliberately tiny final LocalAP width. -/
def dyadicHierarchyDenominator (d rankCap : ℕ) : ℕ :=
  8388608 * max rankCap 1 *
    2 ^ (2 + 2 * d * RawSupplyNumerics.smoothingExponent d)

/-- A deliberately tiny reciprocal width for the final LocalAP child.
The factor 2^23 pays the regular-translation contribution after the crude
sqrt(2/alpha) ≤ 2/alpha bound. -/
def dyadicHierarchyKappa (d rankCap : ℕ) : NNReal :=
  ((dyadicHierarchyDenominator d rankCap : ℕ) : NNReal)⁻¹

lemma dyadicHierarchyDenominator_pos (d rankCap : ℕ) :
    0 < dyadicHierarchyDenominator d rankCap := by
  unfold dyadicHierarchyDenominator
  positivity

lemma dyadicHierarchyKappa_pos (d rankCap : ℕ) :
    0 < dyadicHierarchyKappa d rankCap := by
  unfold dyadicHierarchyKappa
  unfold dyadicHierarchyDenominator
  positivity

lemma dyadicHierarchyKappa_width
    (d rankCap rank : ℕ) (hrank : rank ≤ rankCap) :
    (400 * ((max rank 1 : ℕ) : ℝ) *
        (dyadicHierarchyKappa d rankCap +
          dyadicHierarchyKappa d rankCap : NNReal)) *
      Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) ≤
      1 / 2048 := by
  let e : ℕ := 2 + 2 * d * RawSupplyNumerics.smoothingExponent d
  let P : ℕ := dyadicHierarchyDenominator d rankCap
  have hPpos : (0 : ℝ) < P := by
    dsimp [P, dyadicHierarchyDenominator, e]
    positivity
  have hmax : max rank 1 ≤ max rankCap 1 :=
    max_le_max_right 1 hrank
  have hsqrt :
      Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) ≤
        2 / RawSupplyNumerics.dyadicSiftedAlpha d :=
    RawSupplyNumerics.sqrt_two_div_le_two_div
      (RawSupplyNumerics.dyadicSiftedAlpha_pos d)
      (RawSupplyNumerics.dyadicSiftedAlpha_le_one d)
  have hbound :
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (dyadicHierarchyKappa d rankCap +
            dyadicHierarchyKappa d rankCap : NNReal)) *
        Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) ≤
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (dyadicHierarchyKappa d rankCap +
            dyadicHierarchyKappa d rankCap : NNReal)) *
        (2 / RawSupplyNumerics.dyadicSiftedAlpha d) := by
    gcongr
  apply hbound.trans
  unfold dyadicHierarchyKappa dyadicHierarchyDenominator
    RawSupplyNumerics.dyadicSiftedAlpha
  change
    (400 * ((max rank 1 : ℕ) : ℝ) *
        (((P : ℕ) : ℝ)⁻¹ + ((P : ℕ) : ℝ)⁻¹)) *
      (2 / (1 / (2 : ℝ) ^ e)) ≤ 1 / 2048
  have hmaxReal : ((max rank 1 : ℕ) : ℝ) ≤ max rankCap 1 := by
    exact_mod_cast hmax
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hcalc :
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (((P : ℕ) : ℝ)⁻¹ + ((P : ℕ) : ℝ)⁻¹)) *
        (2 / (1 / (2 : ℝ) ^ e)) =
      1600 * ((max rank 1 : ℕ) : ℝ) * (2 : ℝ) ^ e / P := by
    field_simp
    ring
  rw [hcalc]
  have hP :
      (8388608 : ℝ) * (max rankCap 1 : ℕ) * (2 : ℝ) ^ e =
        (P : ℝ) := by
    dsimp [P, dyadicHierarchyDenominator]
    norm_cast
  rw [← hP]
  have hden : (0 : ℝ) <
      (8388608 : ℝ) * (max rankCap 1 : ℕ) * (2 : ℝ) ^ e := by
    positivity
  apply (div_le_iff₀ hden).2
  calc
    1600 * ((max rank 1 : ℕ) : ℝ) * (2 : ℝ) ^ e ≤
        1600 * ((max rankCap 1 : ℕ) : ℝ) * (2 : ℝ) ^ e := by
      gcongr
    _ ≤ (1 / 2048 : ℝ) *
        ((8388608 : ℝ) * (max rankCap 1 : ℕ) * (2 : ℝ) ^ e) := by
      have hmaxPos : (0 : ℝ) < (max rankCap 1 : ℕ) := by positivity
      nlinarith

lemma two_dyadicHierarchyKappa_le_rank_scale
    (d rankCap rank : ℕ) (hrank : rank ≤ rankCap) :
    dyadicHierarchyKappa d rankCap + dyadicHierarchyKappa d rankCap ≤
      1 / (100 * (max rank 1 : ℕ) : NNReal) := by
  let e : ℕ := 2 + 2 * d * RawSupplyNumerics.smoothingExponent d
  let P : ℕ := dyadicHierarchyDenominator d rankCap
  have hPpos : (0 : ℝ) < P := by
    dsimp [P, dyadicHierarchyDenominator, e]
    positivity
  have hrpos : (0 : ℝ) < 100 * (max rank 1 : ℕ) := by positivity
  have hmax : max rank 1 ≤ max rankCap 1 :=
    max_le_max_right 1 hrank
  have hnat : 2 * (100 * max rank 1) ≤ P := by
    dsimp [P, dyadicHierarchyDenominator]
    have hpow : 1 ≤ 2 ^ e := Nat.one_le_pow _ _ (by omega)
    calc
      2 * (100 * max rank 1) ≤ 200 * max rankCap 1 := by
        omega
      _ ≤ 8388608 * max rankCap 1 * 2 ^ e := by
        have hcoeff : 200 ≤ 8388608 := by norm_num
        calc
          200 * max rankCap 1 ≤ 8388608 * max rankCap 1 :=
            Nat.mul_le_mul_right _ hcoeff
          _ ≤ 8388608 * max rankCap 1 * 2 ^ e :=
            Nat.le_mul_of_pos_right _ (by positivity)
  have hreal :
      (2 : ℝ) * (P : ℝ)⁻¹ ≤
        1 / (100 * (max rank 1 : ℕ) : ℝ) := by
    have hnatReal : (2 : ℝ) * (100 * (max rank 1 : ℕ)) ≤ P := by
      exact_mod_cast hnat
    field_simp
    linarith
  unfold dyadicHierarchyKappa
  change
    ((P : ℕ) : NNReal)⁻¹ + ((P : ℕ) : NNReal)⁻¹ ≤
      1 / (100 * (max rank 1 : ℕ) : NNReal)
  have hnn :
      (2 : NNReal) * ((P : ℕ) : NNReal)⁻¹ ≤
        1 / (100 * (max rank 1 : ℕ) : NNReal) := by
    exact_mod_cast hreal
  simpa [two_mul] using hnn

/-- A dyadic lower bound for the common sifted density and the canonical
sample-count upper bound imply the fixed dyadic Chang-rank budget. -/
theorem hierarchy_rankBudget_of_dyadic_lower
    (W : BohrData G) (H : SmoothingHierarchy W)
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (d k : ℕ)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p)
    (hk : k ≤ RawSupplyNumerics.dyadicSampleKBound d) :
    ⌈8 * (1 + Real.log (2 /
      hierarchyBeta W H data k))⌉₊ ≤
      RawSupplyNumerics.dyadicRankCost d := by
  let alpha := RawSupplyNumerics.dyadicSiftedAlpha d
  let K := RawSupplyNumerics.dyadicSampleKBound d
  let sift := DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p
  have halphaPos : 0 < alpha := by
    simpa [alpha] using RawSupplyNumerics.dyadicSiftedAlpha_pos d
  have halphaOne : alpha ≤ 1 := by
    simpa [alpha] using RawSupplyNumerics.dyadicSiftedAlpha_le_one d
  have hsiftPos : 0 < sift := halphaPos.trans_le (by simpa [sift, alpha] using halpha_le)
  have hbaseNonneg : 0 ≤ alpha / 2 := by positivity
  have hbaseOne : alpha / 2 ≤ 1 := by linarith
  have hpowExp : (alpha / 2) ^ K ≤ (alpha / 2) ^ k := by
    have hK : k + (K - k) = K := Nat.add_sub_of_le hk
    calc
      (alpha / 2) ^ K = (alpha / 2) ^ (k + (K - k)) := by rw [hK]
      _ = (alpha / 2) ^ k * (alpha / 2) ^ (K - k) := by rw [pow_add]
      _ ≤ (alpha / 2) ^ k * 1 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_one₀ hbaseNonneg hbaseOne) (by positivity)
      _ = (alpha / 2) ^ k := by ring
  have hpowBase : (alpha / 2) ^ k ≤ (sift / 2) ^ k := by
    apply pow_le_pow_left₀
    · positivity
    · simpa [sift, alpha] using (div_le_div_of_nonneg_right halpha_le (by norm_num))
  have hbetaLower :
      RawSupplyNumerics.crootBeta alpha K ≤ hierarchyBeta W H data k := by
    unfold RawSupplyNumerics.crootBeta hierarchyBeta
    exact div_le_div_of_nonneg_right (hpowExp.trans hpowBase) (by norm_num)
  have hbetaPos : 0 < hierarchyBeta W H data k := by
    unfold hierarchyBeta
    positivity
  have hcrootPos : 0 < RawSupplyNumerics.crootBeta alpha K :=
    RawSupplyNumerics.crootBeta_pos halphaPos
  have hdiv :
      2 / hierarchyBeta W H data k ≤
        2 / RawSupplyNumerics.crootBeta alpha K := by
    exact div_le_div_of_nonneg_left (by norm_num) hcrootPos hbetaLower
  have hlog :
      Real.log (2 / hierarchyBeta W H data k) ≤
        Real.log (2 / RawSupplyNumerics.crootBeta alpha K) :=
    Real.log_le_log (by positivity) hdiv
  have hinside :
      8 * (1 + Real.log (2 / hierarchyBeta W H data k)) ≤
        8 * (1 + Real.log (2 / RawSupplyNumerics.crootBeta alpha K)) := by
    nlinarith
  apply le_trans (Nat.ceil_mono hinside)
  unfold RawSupplyNumerics.dyadicRankCost RawSupplyNumerics.changRankCost
  exact le_max_right _ _

/-- The real Chang dimension obeys the same dyadic budget.  This is the
version needed to bound the spectral quantization factor in the localized
cell count. -/
theorem hierarchy_dimension_le_dyadicRankCost
    (W : BohrData G) (H : SmoothingHierarchy W)
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (d k : ℕ)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p)
    (hk : k ≤ RawSupplyNumerics.dyadicSampleKBound d)
    (T : Finset G)
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ))) :
    RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) ≤
      RawSupplyNumerics.dyadicRankCost d := by
  have hsiftPos :
      0 < DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p :=
    (RawSupplyNumerics.dyadicSiftedAlpha_pos d).trans_le halpha_le
  have hbeta : 0 < hierarchyBeta W H data k := by
    unfold hierarchyBeta
    positivity
  have hdim := hierarchy_dimension_le_of_croot W H data hdelta k T hbeta hT
  have hceil :
      8 * (1 + Real.log (2 / hierarchyBeta W H data k)) ≤
        (⌈8 * (1 + Real.log (2 / hierarchyBeta W H data k))⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hrank := hierarchy_rankBudget_of_dyadic_lower W H data d k halpha_le hk
  have hrankReal :
      (⌈8 * (1 + Real.log (2 / hierarchyBeta W H data k))⌉₊ : ℝ) ≤
        RawSupplyNumerics.dyadicRankCost d := by
    exact_mod_cast hrank
  exact hdim.trans (hceil.trans hrankReal)

/-- A single fixed cell multiplier dominates every commuted relative-T
package at the dyadic scale once the parent rank is capped. -/
theorem hierarchy_cellMultiplier_le_dyadic
    (W : BohrData G) (H : SmoothingHierarchy W)
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (d k rankCap : ℕ)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p)
    (hk : k ≤ RawSupplyNumerics.dyadicSampleKBound d)
    (hB₀rank : H.B₀.rank ≤ rankCap)
    (T : Finset G) (Delta : Finset (AddChar G Complex))
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ)))
    (hDelta : (Delta.card : ℝ) ≤
      RelativeChangSanders.localChangDimension H.B₀ T (1 / 2)) :
    (RawSupplyNumerics.dyadicQQuant d *
        LocalizedAlmostPeriodicity.spectralQuantization
          (RelativeChangSanders.localChangDimension H.B₀ T (1 / 2))) ^
        Delta.card * 4 ^ (H.B₀.rank + Delta.card) ≤
      RawSupplyNumerics.cellMultiplier rankCap
        (RawSupplyNumerics.dyadicRankCost d)
        (RawSupplyNumerics.dyadicQQuant d *
          (⌈8 * (RawSupplyNumerics.dyadicRankCost d : ℝ)⌉₊ + 1)) := by
  let dim := RelativeChangSanders.localChangDimension H.B₀ T (1 / 2)
  have hdim : dim ≤ RawSupplyNumerics.dyadicRankCost d := by
    simpa [dim] using hierarchy_dimension_le_dyadicRankCost W H data hdelta d k
      halpha_le hk T hT
  have hspectral :
      LocalizedAlmostPeriodicity.spectralQuantization dim ≤
        ⌈8 * (RawSupplyNumerics.dyadicRankCost d : ℝ)⌉₊ + 1 := by
    unfold LocalizedAlmostPeriodicity.spectralQuantization
    apply Nat.add_le_add_right
    apply Nat.ceil_mono
    have hmax : max dim 0 ≤ (RawSupplyNumerics.dyadicRankCost d : ℝ) :=
      max_le hdim (by positivity)
    have hpi : 2 * Real.pi ≤ (8 : ℝ) := by
      nlinarith [Real.pi_lt_four]
    calc
      2 * Real.pi * max dim 0 ≤
          2 * Real.pi * RawSupplyNumerics.dyadicRankCost d := by
        gcongr
      _ ≤ 8 * (RawSupplyNumerics.dyadicRankCost d : ℝ) := by
        gcongr
  have hq : 0 < RawSupplyNumerics.dyadicQQuant d := by
    unfold RawSupplyNumerics.dyadicQQuant
    exact RawSupplyNumerics.qQuant_pos (RawSupplyNumerics.dyadicSiftedAlpha_pos d)
  have hspecPos :
      0 < LocalizedAlmostPeriodicity.spectralQuantization dim := by
    unfold LocalizedAlmostPeriodicity.spectralQuantization
    positivity
  have hn :
      0 < RawSupplyNumerics.dyadicQQuant d *
        LocalizedAlmostPeriodicity.spectralQuantization dim :=
    Nat.mul_pos hq hspecPos
  have hnN :
      RawSupplyNumerics.dyadicQQuant d *
          LocalizedAlmostPeriodicity.spectralQuantization dim ≤
        RawSupplyNumerics.dyadicQQuant d *
          (⌈8 * (RawSupplyNumerics.dyadicRankCost d : ℝ)⌉₊ + 1) :=
    Nat.mul_le_mul_left _ hspectral
  have hsiftPos :
      0 < DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p :=
    (RawSupplyNumerics.dyadicSiftedAlpha_pos d).trans_le halpha_le
  have hbeta : 0 < hierarchyBeta W H data k := by
    unfold hierarchyBeta
    positivity
  have hdeltaCard : Delta.card ≤ RawSupplyNumerics.dyadicRankCost d := by
    apply (hierarchy_delta_card_le_of_croot W H data hdelta k T Delta
      hbeta hT hDelta).trans
    exact hierarchy_rankBudget_of_dyadic_lower W H data d k halpha_le hk
  simpa [RawSupplyNumerics.cellMultiplier, dim] using
    RawSupplyNumerics.cellMultiplier_mono hn hnN hB₀rank hdeltaCard

/-- The high local norm threshold forces the exact dyadic lower bound for
the common sifted density.  The harmless factor 65/64 is intentionally
larger than one, so the endpoint density alone pays the dyadic power. -/
theorem dyadicSiftedAlpha_le_siftingDensity_of_localNorm
    (A B₁ B₂ K : Finset G) (d : ℕ)
    (hK : K.Nonempty)
    (hdensity : 1 / (2 : ℝ) ^ d ≤ (A.card : ℝ) / K.card)
    (hnorm :
      (65 / 64 : ℝ) * (K.card : ℝ)⁻¹ ≤
        BalancedRestriction.weightedLpNorm
          (fun x : G => ((μ_[ℝ≥0] B₁ ○ᵈ μ B₂) x : ℝ))
          (μ_[ℝ] A ○ᵈ μ A)
          (RawSupplyNumerics.smoothingExponent d)) :
    RawSupplyNumerics.dyadicSiftedAlpha d ≤
      DensityStep.siftingDensityLower A B₁ B₂
        (RawSupplyNumerics.smoothingExponent d) := by
  let r := RawSupplyNumerics.smoothingExponent d
  have hr : 0 < r := by
    simpa [r] using RawSupplyNumerics.smoothingExponent_pos d
  have hKpos : (0 : ℝ) < K.card := by exact_mod_cast hK.card_pos
  have hAcardNonneg : (0 : ℝ) ≤ A.card := by positivity
  have hratioNonneg : 0 ≤ (A.card : ℝ) / K.card := by positivity
  have hproduct :
      1 / (2 : ℝ) ^ d ≤
        (A.card : ℝ) *
          BalancedRestriction.weightedLpNorm
            (fun x : G => ((μ_[ℝ≥0] B₁ ○ᵈ μ B₂) x : ℝ))
            (μ_[ℝ] A ○ᵈ μ A) r := by
    calc
      1 / (2 : ℝ) ^ d ≤ (A.card : ℝ) / K.card := hdensity
      _ ≤ (65 / 64 : ℝ) * ((A.card : ℝ) / K.card) := by
        nlinarith
      _ = (A.card : ℝ) * ((65 / 64 : ℝ) * (K.card : ℝ)⁻¹) := by
        field_simp
      _ ≤ (A.card : ℝ) *
          BalancedRestriction.weightedLpNorm
            (fun x : G => ((μ_[ℝ≥0] B₁ ○ᵈ μ B₂) x : ℝ))
            (μ_[ℝ] A ○ᵈ μ A) r :=
        mul_le_mul_of_nonneg_left (by simpa [r] using hnorm) hAcardNonneg
  have hrewrite :
      RawSupplyNumerics.dyadicSiftedAlpha d =
        (4 : ℝ)⁻¹ * (1 / (2 : ℝ) ^ d) ^ (2 * r) := by
    unfold RawSupplyNumerics.dyadicSiftedAlpha
    unfold RawSupplyNumerics.dyadicAlphaExponent
    dsimp [r]
    simp only [one_div, ← inv_pow, pow_add, pow_mul]
    field_simp
    have hpow :
        (1 / 2 : ℝ) ^
            (d * RawSupplyNumerics.smoothingExponent d * 2) *
          (4 : ℝ) ^ (d * RawSupplyNumerics.smoothingExponent d) = 1 := by
      rw [show d * RawSupplyNumerics.smoothingExponent d * 2 =
          2 * (d * RawSupplyNumerics.smoothingExponent d) by omega]
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
      rw [one_div, inv_pow]
      field_simp
    norm_num [pow_mul, pow_add] at hpow ⊢
    have hcomm :
        (((1 / 2 : ℝ) ^ d) ^ RawSupplyNumerics.smoothingExponent d) ^ 2 =
          (((1 / 2 : ℝ) ^ d) ^ 2) ^
            RawSupplyNumerics.smoothingExponent d := by
      conv_lhs =>
        rw [← pow_mul, ← pow_mul]
      conv_rhs =>
        rw [← pow_mul, ← pow_mul]
      congr 1
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hcomm] at hpow
    nlinarith
  rw [hrewrite, siftingDensityLower_eq_normalizedLp A B₁ B₂ hr]
  gcongr

/-- The fixed high-norm parameters satisfy the Croot--Sisask tail
condition at every dyadic scale. -/
theorem dyadic_smoothing_tail_bound (d : ℕ) :
    ((1 / 8192 : ℝ)⁻¹) * Real.log (2 / (1 / 8192 : ℝ)) ≤
      RawSupplyNumerics.smoothingExponent d := by
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
    norm_num
  have hlog : Real.log (2 / (1 / 8192 : ℝ)) ≤ 14 := by
    rw [show (2 / (1 / 8192 : ℝ)) = (2 : ℝ) ^ 14 by norm_num,
      Real.log_pow]
    norm_num at hlog2 ⊢
    nlinarith
  have hleft :
      ((1 / 8192 : ℝ)⁻¹) * Real.log (2 / (1 / 8192 : ℝ)) ≤
        (114688 : ℝ) := by
    norm_num
    nlinarith
  apply hleft.trans
  unfold RawSupplyNumerics.smoothingExponent RawSupplyNumerics.holderExponent
  rw [BalancedRestriction.stoppingExponent_eq]
  norm_num [unbalancingMultiplier]
  have hd : 1 ≤ d + 1 := by omega
  norm_num at hd ⊢
  nlinarith

/-- The deliberately slack high threshold leaves room for the fixed
popular-set, DRC, and localized-approximation errors. -/
theorem dyadic_high_gain_numeric :
    (1 + (1 / 8 : ℝ) / 32) ≤
      (65 / 64 : ℝ) * (1 - 1 / 8192) *
        (1 - 1 / 8192 - 1 / 512) := by
  norm_num

/-- At the endpoint fibre, the fixed high threshold and the three fixed
errors give the 257/256 density gain required by the rank-regular high
branch. -/
theorem endpoint_dyadic_high_gain
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilonDense : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilonDense)
    (hepsilonDense_lt_one : epsilonDense < 1) :
    (1 + (1 / 8 : ℝ) / 32) *
        (endpointLocated s C.childOne C.childTwo hdense
          hepsilonDense_lt_one).density ≤
      ((endpointLocated s C.childOne C.childTwo hdense
          hepsilonDense_lt_one).restriction.set.card : ℝ) *
        (((1 - (1 / 8192 : ℝ)) *
            ((65 / 64 : ℝ) * (C.childOne.bohr.carrier.card : ℝ)⁻¹)) *
          (1 - (1 / 8192 : ℝ) - (1 / 512 : ℝ))) := by
  let u := endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one
  have hKpos : (0 : ℝ) < C.childOne.bohr.carrier.card := by
    exact_mod_cast C.childOne.bohr.carrier_nonempty.card_pos
  have hdensity :
      u.density = (u.restriction.set.card : ℝ) /
        C.childOne.bohr.carrier.card := by
    simp only [u, endpointLocated, DensityStep.density_narrowLocated]
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      C.childOne.carrier_nonempty]
    simp [DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction,
      C.childOne_carrier]
  rw [show (endpointLocated s C.childOne C.childTwo hdense
      hepsilonDense_lt_one).density = u.density by rfl,
    show (endpointLocated s C.childOne C.childTwo hdense
      hepsilonDense_lt_one).restriction.set = u.restriction.set by rfl,
    hdensity]
  have hnum := dyadic_high_gain_numeric
  have hA : (0 : ℝ) ≤ u.restriction.set.card := by positivity
  calc
    (1 + (1 / 8 : ℝ) / 32) *
        ((u.restriction.set.card : ℝ) / C.childOne.bohr.carrier.card) ≤
      ((65 / 64 : ℝ) * (1 - 1 / 8192) *
        (1 - 1 / 8192 - 1 / 512)) *
          ((u.restriction.set.card : ℝ) / C.childOne.bohr.carrier.card) := by
      gcongr
    _ = (u.restriction.set.card : ℝ) *
        (((1 - (1 / 8192 : ℝ)) *
            ((65 / 64 : ℝ) * (C.childOne.bohr.carrier.card : ℝ)⁻¹)) *
          (1 - (1 / 8192 : ℝ) - (1 / 512 : ℝ))) := by
      field_simp

/-- One extra dyadic bit pays for the 511/512 dense-pair loss before the
high branch is run on the endpoint fibre. -/
theorem endpointLocated_on_nextDyadicScale
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilonDense : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilonDense)
    (hepsilonDense : epsilonDense = (1 / 512 : ℝ))
    (hepsilonDense_lt_one : epsilonDense < 1)
    {d : ℕ} (hscale : 1 / (2 : ℝ) ^ d ≤ s.density) :
    1 / (2 : ℝ) ^ (d + 1) ≤
      (endpointLocated s C.childOne C.childTwo hdense
        hepsilonDense_lt_one).density := by
  let u := endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one
  have huDensity : densePairDensity s epsilonDense ≤ u.density := by
    let x := GroupCount.densePairPoint hdense
    have hx : densePairDensity s epsilonDense ≤
        localDensity s.restriction.set C.childOne.carrier x := by
      simpa [x, densePairDensity] using
        GroupCount.densePairPoint_density_one hdense
    simpa [u, endpointLocated, DensityStep.density_narrowLocated] using hx
  have hhalf :
      1 / (2 : ℝ) ^ (d + 1) ≤
        (1 - (1 / 512 : ℝ)) * (1 / (2 : ℝ) ^ d) := by
    rw [pow_succ]
    have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ d := by positivity
    field_simp
    nlinarith
  calc
    1 / (2 : ℝ) ^ (d + 1) ≤
        (1 - (1 / 512 : ℝ)) * (1 / (2 : ℝ) ^ d) := hhalf
    _ ≤ (1 - (1 / 512 : ℝ)) * s.density := by gcongr
    _ = densePairDensity s epsilonDense := by simp [densePairDensity, hepsilonDense]
    _ ≤ u.density := huDensity

/-- The larger Holder exponent at d+1 still satisfies the dense-pair power
condition required by the raw endpoint. -/
theorem densePairDensity_power_next_of_dyadic
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {d : ℕ} (hscale : 1 / (2 : ℝ) ^ d ≤ s.density) :
    (2 / 3 : ℝ) ^ RawSupplyNumerics.holderExponent (d + 1) ≤
      densePairDensity s (1 / 512 : ℝ) := by
  have hbase : 0 ≤ (2 / 3 : ℝ) := by norm_num
  have hbaseOne : (2 / 3 : ℝ) ≤ 1 := by norm_num
  have hexp : RawSupplyNumerics.holderExponent d ≤
      RawSupplyNumerics.holderExponent (d + 1) := by
    unfold RawSupplyNumerics.holderExponent
    omega
  calc
    (2 / 3 : ℝ) ^ RawSupplyNumerics.holderExponent (d + 1) ≤
        (2 / 3 : ℝ) ^ RawSupplyNumerics.holderExponent d := by
      exact pow_le_pow_of_le_one hbase hbaseOne hexp
    _ ≤ (1 - (1 / 512 : ℝ)) * s.density := by
      simpa [RawSupplyNumerics.holderExponent] using
        densePairDensity_power_of_dyadic s hscale
    _ = densePairDensity s (1 / 512 : ℝ) := by
      simp [densePairDensity]

/-- A convenient abstract boundary-width calculation: if the endpoint has
density at least alpha in the base carrier and the regularity width is at
most alpha/384, then the Holder boundary error is below 1/64 of the base
scale. -/
theorem boundary_width_of_endpoint_density
    {Acard Kcard alpha width : ℝ}
    (hAcard : 0 < Acard) (hKcard : 0 < Kcard)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hAK : alpha * Kcard ≤ Acard)
    (hwidth : width ≤ alpha / 384) (hwidthNonneg : 0 ≤ width) :
    2 * (Acard⁻¹ * width) + Kcard⁻¹ * width ≤
      (1 / 64 : ℝ) * Kcard⁻¹ := by
  have hAlphaK : 0 < alpha * Kcard := mul_pos halpha hKcard
  have hAinv : Acard⁻¹ ≤ (alpha * Kcard)⁻¹ :=
    (inv_le_inv₀ hAcard hAlphaK).2 hAK
  have hfirst : Acard⁻¹ * width ≤ Kcard⁻¹ / 384 := by
    calc
      Acard⁻¹ * width ≤ (alpha * Kcard)⁻¹ * width := by gcongr
      _ ≤ (alpha * Kcard)⁻¹ * (alpha / 384) := by gcongr
      _ = Kcard⁻¹ / 384 := by
        field_simp
  have hwidthOne : width ≤ 1 / 384 := by
    calc
      width ≤ alpha / 384 := hwidth
      _ ≤ 1 / 384 := by gcongr
  have hsecond : Kcard⁻¹ * width ≤ Kcard⁻¹ / 384 := by
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hwidthOne (by positivity : 0 ≤ Kcard⁻¹)
  calc
    2 * (Acard⁻¹ * width) + Kcard⁻¹ * width ≤
        2 * (Kcard⁻¹ / 384) + Kcard⁻¹ / 384 := by gcongr
    _ ≤ (1 / 64 : ℝ) * Kcard⁻¹ := by
      have hKinv : 0 ≤ Kcard⁻¹ := by positivity
      nlinarith

/-- The concrete second reciprocal denominator makes the Holder boundary
width small enough on a dyadic-density endpoint fibre. -/
theorem dyadic_boundary_width
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {d rankCost mOne : ℕ}
    (C : ReciprocalChildren s.restriction.bohr mOne
      (ConcreteNumerics.mTwo (d + 1) rankCost))
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo (1 / 512 : ℝ))
    (hscale : 1 / (2 : ℝ) ^ d ≤ s.density)
    (hrank : s.rank ≤ ConcreteNumerics.rankCap (d + 1) rankCost)
    (hrankCost : 0 < rankCost) :
    2 * (((endpointSet s C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
        (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
          (((ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ +
            (ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ : NNReal) : ℝ))) +
      (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
        (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
          (((ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ +
            (ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ : NNReal) : ℝ)) ≤
      (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹ := by
  let alpha : ℝ := (1 - (1 / 512 : ℝ)) * (1 / (2 : ℝ) ^ d)
  let width : ℝ :=
    200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
      (((ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ +
        (ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ : NNReal) : ℝ)
  have hAne : (endpointSet s C.childOne C.childTwo hdense).Nonempty :=
    endpointSet_nonempty s C.childOne C.childTwo hdense (by norm_num)
  have hApos : (0 : ℝ) < (endpointSet s C.childOne C.childTwo hdense).card := by
    exact_mod_cast hAne.card_pos
  have hKpos : (0 : ℝ) < C.childOne.bohr.carrier.card := by
    exact_mod_cast C.childOne.bohr.carrier_nonempty.card_pos
  have halphaPos : 0 < alpha := by unfold alpha; positivity
  have halphaOne : alpha ≤ 1 := by
    unfold alpha
    have hdensity : 1 / (2 : ℝ) ^ d ≤ 1 := by
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
      exact (div_le_iff₀ (by positivity)).2 (by simpa using hpow)
    nlinarith
  have hOne : alpha ≤
      localDensity s.restriction.set C.childOne.carrier
        (GroupCount.densePairPoint hdense) := by
    calc
      alpha ≤ (1 - (1 / 512 : ℝ)) * s.density := by
        unfold alpha
        gcongr
      _ = densePairDensity s (1 / 512 : ℝ) := by simp [densePairDensity]
      _ ≤ localDensity s.restriction.set C.childOne.carrier
          (GroupCount.densePairPoint hdense) := by
        simpa [densePairDensity] using GroupCount.densePairPoint_density_one hdense
  have hAK : alpha * (C.childOne.bohr.carrier.card : ℝ) ≤
      (endpointSet s C.childOne C.childTwo hdense).card := by
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      C.childOne.carrier_nonempty] at hOne
    have hCpos : (0 : ℝ) < C.childOne.carrier.card := by
      exact_mod_cast C.childOne.carrier_nonempty.card_pos
    simpa [endpointSet, C.childOne_carrier] using
      (le_div_iff₀ hCpos).mp hOne
  have hwidthNonneg : 0 ≤ width := by unfold width; positivity
  have hwidth : width ≤ alpha / 384 := by
    have hmax : max C.childOne.bohr.rank 1 ≤
        ConcreteNumerics.rankCap (d + 1) rankCost := by
      rw [C.rankOne]
      exact ConcreteNumerics.max_rank_le_rankCap hrankCost hrank
    have hmPos : (0 : ℝ) < ConcreteNumerics.mTwo (d + 1) rankCost := by
      exact_mod_cast ConcreteNumerics.mTwo_pos hrankCost
    have hRpos : (0 : ℝ) < ConcreteNumerics.rankCap (d + 1) rankCost := by
      exact_mod_cast ConcreteNumerics.rankCap_pos hrankCost
    have hmaxR : ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) ≤
        ConcreteNumerics.rankCap (d + 1) rankCost := by exact_mod_cast hmax
    have hmaxR' : max (C.childOne.bohr.rank : ℝ) 1 ≤
        ConcreteNumerics.rankCap (d + 1) rankCost := by
      simpa [Nat.cast_max] using hmaxR
    unfold width alpha ConcreteNumerics.mTwo
    simp only [NNReal.coe_add, NNReal.coe_inv, NNReal.coe_natCast]
    push_cast
    change 200 * max (C.childOne.bohr.rank : ℝ) 1 *
        ((76800 * ConcreteNumerics.rankCap (d + 1) rankCost *
          2 ^ (d + 1 + 1) : ℝ)⁻¹ +
          (76800 * ConcreteNumerics.rankCap (d + 1) rankCost *
          2 ^ (d + 1 + 1) : ℝ)⁻¹) ≤
      ((1 - 1 / 512) * (1 / (2 : ℝ) ^ d)) / 384
    field_simp
    have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
    have hpow2 : (2 : ℝ) ^ (d + 1 + 1) = 4 * (2 : ℝ) ^ d := by
      rw [show d + 1 + 1 = d + 2 by omega, pow_add]
      norm_num
      ring
    rw [hpow2]
    nlinarith
  convert boundary_width_of_endpoint_density hApos hKpos halphaPos halphaOne
      hAK hwidth hwidthNonneg using 1 <;> simp [width] <;> norm_num

/-- Consume the commuted, support-restricted relative-T constructor inside
the three-level smoothing hierarchy.

The hypotheses after hsmall are deliberately scalar bookkeeping obligations:
a uniform Chang-rank cap, a uniform multiplier cap, and the lower bound on
the regularized source carrier which pays that multiplier.  No
density-increment conclusion is assumed here. -/
theorem supportedLocalizedPackage_of_hierarchy
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (W : BohrData G) (H : SmoothingHierarchy W)
    {B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData s.restriction.set B₁
      H.Ebohr.carrier p sigma delta)
    (hp : 0 < p)
    (hB : (B₁ ∩ H.Ebohr.carrier).Nonempty)
    (hdelta : delta < 1)
    (approxDelta : ℝ) (happroxDelta : 0 < approxDelta)
    (m : ℕ) (hm : m ≠ 0)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max H.B₀.rank 1 : ℕ) : NNReal))
    (qQuant : ℕ) (hqQuant : 0 < qQuant)
    (approximationError sizeCost : ℝ)
    (hsmall : ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      (Delta.card : ℝ) ≤
        RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) →
      2 * approxDelta +
          (2 / (qQuant : ℝ) +
            400 * ((max H.B₀.rank 1 : ℕ) : ℝ) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : ℝ) ^ m) *
          Real.sqrt
            (((DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set B₁ H.Ebohr.carrier p sigma).card : ℝ) /
              data.A₁.card) ≤ approximationError)
    {rankCost cardMultiplier : ℕ}
    (hB₀rank : H.B₀.rank ≤ s.rank)
    (hrankBudget :
      ⌈8 * (1 + Real.log (2 /
        hierarchyBeta W H data
          (DensityStep.localizedAPSampleK
            (-(DensityStep.SiftedPopularData.supportedPopularSet
              s.restriction.set B₁ H.Ebohr.carrier p sigma))
            data.A₁ approxDelta m)))⌉₊ ≤ rankCost)
    (hmult : ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      ((hierarchyNegCard data.A₂ ^
          (DensityStep.localizedAPSampleK
            (-(DensityStep.SiftedPopularData.supportedPopularSet
              s.restriction.set B₁ H.Ebohr.carrier p sigma))
            data.A₁ approxDelta m) / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^
            (DensityStep.localizedAPSampleK
              (-(DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set B₁ H.Ebohr.carrier p sigma))
              data.A₁ approxDelta m) ≤ (T.card : ℝ)) →
      (Delta.card : ℝ) ≤
        RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) →
      (qQuant * LocalizedAlmostPeriodicity.spectralQuantization
          (RelativeChangSanders.localChangDimension H.B₀ T (1 / 2))) ^
          Delta.card *
        4 ^ (H.B₀.rank + Delta.card) ≤ cardMultiplier)
    (hcardMultiplier : 0 < cardMultiplier)
    (hsource : ∀ (T : Finset G) (rho : NNReal) (C₀ : BohrData G)
        (Delta : Finset (AddChar G Complex)),
      ((hierarchyNegCard data.A₂ ^
          (DensityStep.localizedAPSampleK
            (-(DensityStep.SiftedPopularData.supportedPopularSet
              s.restriction.set B₁ H.Ebohr.carrier p sigma))
            data.A₁ approxDelta m) / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^
            (DensityStep.localizedAPSampleK
              (-(DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set B₁ H.Ebohr.carrier p sigma))
              data.A₁ approxDelta m) ≤ (T.card : ℝ)) →
      1 / 2 ≤ rho →
      C₀ = H.B₀.dilate (rho *
        RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2)) →
      Real.exp (-sizeCost) * (s.card : ℝ) * (cardMultiplier : ℝ) ≤
        ((C₀.dilate kappa).carrier.card : ℝ)) :
    ∃ (parent : BohrData G) (parentWidth : NNReal)
      (source : Finset G) (multiplier : ℕ),
      ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
        parentWidth source rankCost multiplier approximationError,
        P.child.rank ≤ s.rank + rankCost ∧
        Real.exp (-sizeCost) * (s.card : ℝ) ≤ P.child.carrier.card := by
  obtain ⟨T, X, rho, C₀, Delta, hTcard, hTB₀, hXne, hDelta,
      hrhoHalf, hrhoOne, hC₀, Praw⟩ :=
    DensityStep.exists_supportedLocalizedSiftingPackage_of_relativeT_scaled_le_with_witnesses_commuted
      data hdelta approxDelta happroxDelta m hm H.B₀ H.B₀_regular
      kappa hkappa qQuant hqQuant approximationError hsmall
  obtain ⟨Praw⟩ := Praw
  let rawMultiplier : ℕ :=
    (qQuant * LocalizedAlmostPeriodicity.spectralQuantization
        (RelativeChangSanders.localChangDimension H.B₀ T (1 / 2))) ^
        Delta.card *
      4 ^ (H.B₀.rank + Delta.card)
  let k : ℕ :=
    DensityStep.localizedAPSampleK
      (-(DensityStep.SiftedPopularData.supportedPopularSet
        s.restriction.set B₁ H.Ebohr.carrier p sigma))
      data.A₁ approxDelta m
  have hTcard' :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ)) := by
    simpa [k, hierarchyNegCard, hierarchySampleCard,
      hierarchyCrootCard, hierarchyCrootSumset] using hTcard
  have hsiftPos :
      0 < DensityStep.siftingDensityLower s.restriction.set B₁
        H.Ebohr.carrier p :=
    siftingDensityLower_pos_of_nonempty s.restriction.set B₁
      H.Ebohr.carrier hp hB s.restriction.nonempty
  have hbeta :
      0 < hierarchyBeta W H data k := by
    unfold hierarchyBeta
    positivity
  have hrank' : Delta.card ≤ rankCost := by
    apply (hierarchy_delta_card_le_of_croot W H data hdelta k T Delta
      hbeta hTcard' hDelta).trans
    simpa [k] using hrankBudget
  have hmult' : rawMultiplier ≤ cardMultiplier := by
    simpa [rawMultiplier] using hmult T Delta hTcard' hDelta
  let P := Praw.mono hrank' hmult' (le_refl approximationError)
  have hPrank : P.child.rank ≤ s.rank + rankCost := by
    have hraw := P.rank_bound
    calc
      P.child.rank ≤ H.B₀.rank + rankCost := by
        simpa [P, hC₀, BohrData.rank_dilate] using hraw
      _ ≤ s.rank + rankCost := Nat.add_le_add_right hB₀rank rankCost
  have hsource' :
      Real.exp (-sizeCost) * (s.card : ℝ) * (cardMultiplier : ℝ) ≤
        ((C₀.dilate kappa).carrier.card : ℝ) :=
    hsource T rho C₀ Delta hTcard' hrhoHalf hC₀
  have hrelative :
      ((C₀.dilate kappa).carrier.card : ℝ) ≤
        (cardMultiplier : ℝ) * (P.child.carrier.card : ℝ) := by
    have hnat :
        (C₀.dilate kappa).carrier.card ≤
          cardMultiplier * P.child.carrier.card := by
      exact P.relative_card
    exact_mod_cast hnat
  have hmultCard :
      (cardMultiplier : ℝ) *
          (Real.exp (-sizeCost) * (s.card : ℝ)) ≤
        (cardMultiplier : ℝ) * (P.child.carrier.card : ℝ) := by
    calc
      (cardMultiplier : ℝ) *
          (Real.exp (-sizeCost) * (s.card : ℝ)) =
          Real.exp (-sizeCost) * (s.card : ℝ) * cardMultiplier := by ring
      _ ≤ ((C₀.dilate kappa).carrier.card : ℝ) := hsource'
      _ ≤ (cardMultiplier : ℝ) * (P.child.carrier.card : ℝ) := hrelative
  have hmultPos : (0 : ℝ) < cardMultiplier := by exact_mod_cast hcardMultiplier
  have hPcard :
      Real.exp (-sizeCost) * (s.card : ℝ) ≤ P.child.carrier.card :=
    le_of_mul_le_mul_left hmultCard hmultPos
  exact ⟨C₀, kappa + kappa, (C₀.dilate kappa).carrier,
    cardMultiplier, P, hPrank, hPcard⟩

/-- Dyadic specialization of the local hierarchy adapter.  RawSupplyNumerics
now supplies both the sample-count and Chang-rank bounds; only the phase
error and pure volume/card-multiplier estimates remain as explicit scalar
inputs. -/
theorem supportedLocalizedPackage_of_dyadic_hierarchy
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (W : BohrData G) (H : SmoothingHierarchy W)
    {d : ℕ} (z : G)
    {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData s.restriction.set
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma delta)
    (hp : 0 < p)
    (hB : ((z +ᵥ H.Dbohr.carrier) ∩ H.Ebohr.carrier).Nonempty)
    (hdelta : delta < 1)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower s.restriction.set
          (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max H.B₀.rank 1 : ℕ) : NNReal))
    (approximationError sizeCost : ℝ)
    (happroximationError : (1 / 512 : ℝ) ≤ approximationError)
    (hwidth :
      (400 * ((max H.B₀.rank 1 : ℕ) : ℝ) *
          (kappa + kappa : NNReal)) *
        Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) ≤
          1 / 2048)
    {cardMultiplier : ℕ}
    (hB₀rank : H.B₀.rank ≤ s.rank)
    (hmult : ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      ((hierarchyNegCard data.A₂ ^
          (DensityStep.localizedAPSampleK
            (-(DensityStep.SiftedPopularData.supportedPopularSet
              s.restriction.set (z +ᵥ H.Dbohr.carrier)
                H.Ebohr.carrier p sigma))
            data.A₁ RawSupplyNumerics.approximationDelta
              (RawSupplyNumerics.dyadicTailExponent d)) / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^
            (DensityStep.localizedAPSampleK
              (-(DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set (z +ᵥ H.Dbohr.carrier)
                  H.Ebohr.carrier p sigma))
              data.A₁ RawSupplyNumerics.approximationDelta
                (RawSupplyNumerics.dyadicTailExponent d)) ≤ (T.card : ℝ)) →
      (Delta.card : ℝ) ≤
        RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) →
      (RawSupplyNumerics.dyadicQQuant d *
          LocalizedAlmostPeriodicity.spectralQuantization
            (RelativeChangSanders.localChangDimension H.B₀ T (1 / 2))) ^
          Delta.card *
        4 ^ (H.B₀.rank + Delta.card) ≤ cardMultiplier)
    (hcardMultiplier : 0 < cardMultiplier)
    (hsource : ∀ (T : Finset G) (rho : NNReal) (C₀ : BohrData G)
        (Delta : Finset (AddChar G Complex)),
      ((hierarchyNegCard data.A₂ ^
          (DensityStep.localizedAPSampleK
            (-(DensityStep.SiftedPopularData.supportedPopularSet
              s.restriction.set (z +ᵥ H.Dbohr.carrier)
                H.Ebohr.carrier p sigma))
            data.A₁ RawSupplyNumerics.approximationDelta
              (RawSupplyNumerics.dyadicTailExponent d)) / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^
            (DensityStep.localizedAPSampleK
              (-(DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set (z +ᵥ H.Dbohr.carrier)
                  H.Ebohr.carrier p sigma))
              data.A₁ RawSupplyNumerics.approximationDelta
                (RawSupplyNumerics.dyadicTailExponent d)) ≤ (T.card : ℝ)) →
      1 / 2 ≤ rho →
      C₀ = H.B₀.dilate (rho *
        RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2)) →
      Real.exp (-sizeCost) * (s.card : ℝ) * (cardMultiplier : ℝ) ≤
        ((C₀.dilate kappa).carrier.card : ℝ)) :
    ∃ (parent : BohrData G) (parentWidth : NNReal)
      (source : Finset G) (multiplier : ℕ),
      ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
        parentWidth source (RawSupplyNumerics.dyadicRankCost d)
          multiplier approximationError,
        P.child.rank ≤ s.rank + RawSupplyNumerics.dyadicRankCost d ∧
        Real.exp (-sizeCost) * (s.card : ℝ) ≤ P.child.carrier.card := by
  let S : Finset G :=
    DensityStep.SiftedPopularData.supportedPopularSet s.restriction.set
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma
  let k : ℕ :=
    DensityStep.localizedAPSampleK (-S) data.A₁
      RawSupplyNumerics.approximationDelta
      (RawSupplyNumerics.dyadicTailExponent d)
  have halphaPos := RawSupplyNumerics.dyadicSiftedAlpha_pos d
  have hratio :
      RawSupplyNumerics.dyadicSiftedAlpha d / 2 ≤
        (data.A₁.card : ℝ) / (-S).card := by
    simpa [S] using
      supported_ratio_lower_of_hierarchy H z data hdelta
        (RawSupplyNumerics.dyadicSiftedAlpha_pos d).le halpha_le
  have htailPos :
      0 < RawSupplyNumerics.dyadicTailExponent d := by
    unfold RawSupplyNumerics.dyadicTailExponent
    exact RawSupplyNumerics.tailExponent_pos
      (RawSupplyNumerics.dyadicSiftedAlpha_pos d)
      (RawSupplyNumerics.dyadicSiftedAlpha_le_one d)
  have hk :
      k ≤ RawSupplyNumerics.dyadicSampleKBound d := by
    dsimp [k]
    unfold RawSupplyNumerics.dyadicSampleKBound
    exact RawSupplyNumerics.localizedAPSampleK_le_sampleKBound
      (-S) data.A₁ halphaPos
      (RawSupplyNumerics.dyadicSiftedAlpha_le_two d) hratio htailPos
  have hsmall :
      ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      (Delta.card : ℝ) ≤
        RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) →
      2 * RawSupplyNumerics.approximationDelta +
          (2 / (RawSupplyNumerics.dyadicQQuant d : ℝ) +
            400 * ((max H.B₀.rank 1 : ℕ) : ℝ) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : ℝ) ^ RawSupplyNumerics.dyadicTailExponent d) *
          Real.sqrt
            (((DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set (z +ᵥ H.Dbohr.carrier)
                H.Ebohr.carrier p sigma).card : ℝ) /
              data.A₁.card) ≤ approximationError := by
    intro T Delta hDelta
    have houtputs := data.output_nonempty hdelta
    have hSnonempty : S.Nonempty := by
      simpa [S] using data.supportedPopularSet_nonempty hdelta
    apply (dyadic_commuted_hsmall d houtputs.1 hSnonempty
      (by simpa [S] using hratio) hwidth).trans
    exact happroximationError
  apply supportedLocalizedPackage_of_hierarchy s W H data hp hB hdelta
    RawSupplyNumerics.approximationDelta
    RawSupplyNumerics.approximationDelta_pos
    (RawSupplyNumerics.dyadicTailExponent d) htailPos.ne'
    kappa hkappa (RawSupplyNumerics.dyadicQQuant d)
    (by
      unfold RawSupplyNumerics.dyadicQQuant
      exact RawSupplyNumerics.qQuant_pos halphaPos)
    approximationError sizeCost hsmall hB₀rank
  · simpa [k, S] using
      hierarchy_rankBudget_of_dyadic_lower W H data d k halpha_le hk
  · exact hmult
  · exact hcardMultiplier
  · exact hsource

/-- A reusable source-cardinality adapter.  Once an earlier geometric loss
compares the ambient state to B and the single displayed exponential
inequality pays the remaining reciprocal source scale and cell multiplier,
the actual regularized source carrier is large enough for the localized
package. -/
theorem source_card_of_inv_scale_and_budget
    (B : BohrData G) (source : Finset G) {rho : NNReal}
    (P : ℕ) (hP : 0 < P)
    (hrho : ((P : NNReal)⁻¹) ≤ rho)
    {baseCard globalLoss sizeCost : ℝ} {cardMultiplier : ℕ}
    (hglobalLoss : 0 ≤ globalLoss)
    (hbase : baseCard ≤ globalLoss * (B.carrier.card : ℝ))
    (hsource : source = (B.dilate rho).carrier)
    (hbudget :
      Real.exp (-sizeCost) * globalLoss *
          (((3 * P) ^ B.rank : ℕ) : ℝ) * (cardMultiplier : ℝ) ≤ 1) :
    Real.exp (-sizeCost) * baseCard * (cardMultiplier : ℝ) ≤
      (source.card : ℝ) := by
  have hBsourceNat :
      B.carrier.card ≤ (3 * P) ^ B.rank * source.card := by
    rw [hsource]
    exact RawSupplyNumerics.card_unit_le_three_mul_pow_rank_mul_card_dilate_of_inv_nat_le
      B P hP hrho
  have hBsource :
      (B.carrier.card : ℝ) ≤
        (((3 * P) ^ B.rank : ℕ) : ℝ) * (source.card : ℝ) := by
    exact_mod_cast hBsourceNat
  have hbaseSource :
      baseCard ≤ globalLoss *
          (((3 * P) ^ B.rank : ℕ) : ℝ) * (source.card : ℝ) := by
    calc
      baseCard ≤ globalLoss * (B.carrier.card : ℝ) := hbase
      _ ≤ globalLoss *
          ((((3 * P) ^ B.rank : ℕ) : ℝ) * (source.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hBsource hglobalLoss
      _ = globalLoss * (((3 * P) ^ B.rank : ℕ) : ℝ) *
          (source.card : ℝ) := by ring
  calc
    Real.exp (-sizeCost) * baseCard * (cardMultiplier : ℝ) ≤
        Real.exp (-sizeCost) *
          (globalLoss * (((3 * P) ^ B.rank : ℕ) : ℝ) *
            (source.card : ℝ)) * (cardMultiplier : ℝ) := by
              gcongr
    _ = (Real.exp (-sizeCost) * globalLoss *
          (((3 * P) ^ B.rank : ℕ) : ℝ) * (cardMultiplier : ℝ)) *
          (source.card : ℝ) := by ring
    _ ≤ 1 * (source.card : ℝ) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = (source.card : ℝ) := by ring

/-- Apply the preceding source adapter to the actual nested local-Chang
regular datum and the fixed dyadic hierarchy width. -/
theorem source_card_of_localChang_hierarchy
    (H : SmoothingHierarchy W) (d rankCap : ℕ)
    (T : Finset G) (rho : NNReal) (C₀ : BohrData G)
    (hrho : 1 / 2 ≤ rho)
    (hC₀ : C₀ = H.B₀.dilate (rho *
      RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2)))
    {baseCard globalLoss sizeCost : ℝ} {cardMultiplier : ℕ}
    (hglobalLoss : 0 ≤ globalLoss)
    (hbase : baseCard ≤ globalLoss * (H.B₀.carrier.card : ℝ))
    (hbudget :
      Real.exp (-sizeCost) * globalLoss *
          (((3 * RawSupplyNumerics.sourceDenominator H.B₀.rank
              (RelativeChangSanders.localChangCap H.B₀ T (1 / 2))
              (dyadicHierarchyDenominator d rankCap)) ^ H.B₀.rank : ℕ) : ℝ) *
            (cardMultiplier : ℝ) ≤ 1) :
    Real.exp (-sizeCost) * baseCard * (cardMultiplier : ℝ) ≤
      ((C₀.dilate (dyadicHierarchyKappa d rankCap)).carrier.card : ℝ) := by
  let m := dyadicHierarchyDenominator d rankCap
  let P := RawSupplyNumerics.sourceDenominator H.B₀.rank
    (RelativeChangSanders.localChangCap H.B₀ T (1 / 2)) m
  have hm : 0 < m := by
    simpa [m] using dyadicHierarchyDenominator_pos d rankCap
  have hP : 0 < P := by
    exact RawSupplyNumerics.sourceDenominator_pos hm
  have hscale :
      ((P : NNReal)⁻¹) ≤
        rho * RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2) *
          (m : NNReal)⁻¹ := by
    simpa [P] using
      RawSupplyNumerics.inv_sourceDenominator_le_localChang_source_scale
        H.B₀ T (1 / 2) m hm rho hrho
  have hcarrier :
      (C₀.dilate (dyadicHierarchyKappa d rankCap)).carrier =
        (H.B₀.dilate
          (rho * RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2) *
            (m : NNReal)⁻¹)).carrier := by
    rw [hC₀]
    simp [dyadicHierarchyKappa, m, BohrData.dilate_dilate,
      mul_assoc, mul_comm, mul_left_comm]
  apply source_card_of_inv_scale_and_budget
    (rho := rho * RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2) *
    (m : NNReal)⁻¹)
    H.B₀ (C₀.dilate (dyadicHierarchyKappa d rankCap)).carrier P hP
  · exact hscale
  · exact hglobalLoss
  · exact hbase
  · exact hcarrier
  · simpa [P, m] using hbudget

/-- Fixed spectral-cell count used by every dyadic localized package at a
given rank cap. -/
def dyadicCellCount (d : ℕ) : ℕ :=
  RawSupplyNumerics.dyadicQQuant d *
    (⌈8 * (RawSupplyNumerics.dyadicRankCost d : ℝ)⌉₊ + 1)

def dyadicCardMultiplier (d rankCap : ℕ) : ℕ :=
  RawSupplyNumerics.cellMultiplier rankCap
    (RawSupplyNumerics.dyadicRankCost d) (dyadicCellCount d)

def dyadicSourceDenominator (d rankCap : ℕ) : ℕ :=
  RawSupplyNumerics.sourceDenominator rankCap
    (RawSupplyNumerics.dyadicRankCost d + 1)
    (dyadicHierarchyDenominator d rankCap)

lemma dyadicCellCount_pos (d : ℕ) : 0 < dyadicCellCount d := by
  unfold dyadicCellCount
  have hq : 0 < RawSupplyNumerics.dyadicQQuant d := by
    unfold RawSupplyNumerics.dyadicQQuant
    exact RawSupplyNumerics.qQuant_pos (RawSupplyNumerics.dyadicSiftedAlpha_pos d)
  positivity

lemma dyadicCardMultiplier_pos (d rankCap : ℕ) :
    0 < dyadicCardMultiplier d rankCap := by
  unfold dyadicCardMultiplier RawSupplyNumerics.cellMultiplier
  have hn := dyadicCellCount_pos d
  positivity

/-- The local Chang cap itself is at most one more than the dyadic rank
budget whenever the hierarchy Croot lower bound is available. -/
theorem hierarchy_localChangCap_le_dyadic
    (W : BohrData G) (H : SmoothingHierarchy W)
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (d k : ℕ)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p)
    (hk : k ≤ RawSupplyNumerics.dyadicSampleKBound d)
    (T : Finset G)
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ))) :
    RelativeChangSanders.localChangCap H.B₀ T (1 / 2) ≤
      RawSupplyNumerics.dyadicRankCost d + 1 := by
  unfold RelativeChangSanders.localChangCap
  apply Nat.add_le_add_right
  apply Nat.ceil_le.mpr
  exact hierarchy_dimension_le_dyadicRankCost W H data hdelta d k
    halpha_le hk T hT

/-- Fully fixed dyadic localized package from the geometric hierarchy.  The
only remaining input is one scalar exponential budget for the already fixed
global/source/cell loss; all rank, phase, width, and multiplier estimates
are discharged here. -/
theorem supportedLocalizedPackage_of_dyadic_hierarchy_fixed
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (W : BohrData G) (H : SmoothingHierarchy W)
    {d : ℕ} (z : G)
    {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData s.restriction.set
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma delta)
    (hp : 0 < p)
    (hB : ((z +ᵥ H.Dbohr.carrier) ∩ H.Ebohr.carrier).Nonempty)
    (hdelta : delta < 1)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower s.restriction.set
          (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p)
    (rankCap : ℕ)
    (hB₀rank_s : H.B₀.rank ≤ s.rank)
    (hB₀rank : H.B₀.rank ≤ rankCap)
    {globalLoss localSizeCost : ℝ}
    (hglobalLoss : 0 ≤ globalLoss)
    (hbase : (s.card : ℝ) ≤ globalLoss * (H.B₀.carrier.card : ℝ))
    (hbudget :
      Real.exp (-localSizeCost) * globalLoss *
          (((3 * dyadicSourceDenominator d rankCap) ^ rankCap : ℕ) : ℝ) *
            (dyadicCardMultiplier d rankCap : ℝ) ≤ 1) :
    ∃ (parent : BohrData G) (parentWidth : NNReal)
      (source : Finset G) (multiplier : ℕ),
      ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
        parentWidth source (RawSupplyNumerics.dyadicRankCost d)
          multiplier (1 / 512 : ℝ),
        P.child.rank ≤ s.rank + RawSupplyNumerics.dyadicRankCost d ∧
        Real.exp (-localSizeCost) * (s.card : ℝ) ≤ P.child.carrier.card := by
  let S : Finset G :=
    DensityStep.SiftedPopularData.supportedPopularSet s.restriction.set
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma
  let k : ℕ := DensityStep.localizedAPSampleK (-S) data.A₁
    RawSupplyNumerics.approximationDelta (RawSupplyNumerics.dyadicTailExponent d)
  have halphaPos := RawSupplyNumerics.dyadicSiftedAlpha_pos d
  have hratio :
      RawSupplyNumerics.dyadicSiftedAlpha d / 2 ≤
        (data.A₁.card : ℝ) / (-S).card := by
    simpa [S] using supported_ratio_lower_of_hierarchy H z data hdelta
      halphaPos.le halpha_le
  have htailPos : 0 < RawSupplyNumerics.dyadicTailExponent d := by
    unfold RawSupplyNumerics.dyadicTailExponent
    exact RawSupplyNumerics.tailExponent_pos halphaPos
      (RawSupplyNumerics.dyadicSiftedAlpha_le_one d)
  have hk : k ≤ RawSupplyNumerics.dyadicSampleKBound d := by
    dsimp [k]
    unfold RawSupplyNumerics.dyadicSampleKBound
    exact RawSupplyNumerics.localizedAPSampleK_le_sampleKBound
      (-S) data.A₁ halphaPos (RawSupplyNumerics.dyadicSiftedAlpha_le_two d)
      hratio htailPos
  apply supportedLocalizedPackage_of_dyadic_hierarchy s W H z data hp hB hdelta
    halpha_le (dyadicHierarchyKappa d rankCap)
    (two_dyadicHierarchyKappa_le_rank_scale d rankCap H.B₀.rank hB₀rank)
    (1 / 512 : ℝ) localSizeCost (le_rfl)
    (dyadicHierarchyKappa_width d rankCap H.B₀.rank hB₀rank)
    hB₀rank_s
  · intro T Delta hT hDelta
    simpa [dyadicCardMultiplier, dyadicCellCount, k, S] using
      hierarchy_cellMultiplier_le_dyadic W H data hdelta d k rankCap
        halpha_le hk hB₀rank T Delta (by simpa [k, S] using hT) hDelta
  · exact dyadicCardMultiplier_pos d rankCap
  · intro T rho C₀ Delta hT hrhoHalf hC₀
    have hcap :
        RelativeChangSanders.localChangCap H.B₀ T (1 / 2) ≤
          RawSupplyNumerics.dyadicRankCost d + 1 :=
      hierarchy_localChangCap_le_dyadic W H data hdelta d k halpha_le hk T
        (by simpa [k, S] using hT)
    have hP :
        RawSupplyNumerics.sourceDenominator H.B₀.rank
            (RelativeChangSanders.localChangCap H.B₀ T (1 / 2))
            (dyadicHierarchyDenominator d rankCap) ≤
          dyadicSourceDenominator d rankCap := by
      unfold dyadicSourceDenominator RawSupplyNumerics.sourceDenominator
      have hmax : max H.B₀.rank 1 ≤ max rankCap 1 :=
        max_le_max_right 1 hB₀rank
      gcongr
    have hpow :
        (3 * RawSupplyNumerics.sourceDenominator H.B₀.rank
            (RelativeChangSanders.localChangCap H.B₀ T (1 / 2))
            (dyadicHierarchyDenominator d rankCap)) ^ H.B₀.rank ≤
          (3 * dyadicSourceDenominator d rankCap) ^ rankCap := by
      calc
        (3 * RawSupplyNumerics.sourceDenominator H.B₀.rank
            (RelativeChangSanders.localChangCap H.B₀ T (1 / 2))
            (dyadicHierarchyDenominator d rankCap)) ^ H.B₀.rank ≤
          (3 * dyadicSourceDenominator d rankCap) ^ H.B₀.rank := by
            apply Nat.pow_le_pow_left
            gcongr
        _ ≤ (3 * dyadicSourceDenominator d rankCap) ^ rankCap := by
          apply Nat.pow_le_pow_right
          · have hPfixed : 0 < dyadicSourceDenominator d rankCap := by
              unfold dyadicSourceDenominator
              exact RawSupplyNumerics.sourceDenominator_pos
                (dyadicHierarchyDenominator_pos d rankCap)
            exact Nat.mul_pos (by norm_num) hPfixed
          · exact hB₀rank
    have hbudget' :
        Real.exp (-localSizeCost) * globalLoss *
          (((3 * RawSupplyNumerics.sourceDenominator H.B₀.rank
              (RelativeChangSanders.localChangCap H.B₀ T (1 / 2))
              (dyadicHierarchyDenominator d rankCap)) ^ H.B₀.rank : ℕ) : ℝ) *
            (dyadicCardMultiplier d rankCap : ℝ) ≤ 1 := by
      apply le_trans ?_ hbudget
      gcongr
    exact source_card_of_localChang_hierarchy H d rankCap T rho C₀
      hrhoHalf hC₀ hglobalLoss hbase hbudget'

/-- High smoothing norm on the endpoint fibre gives a genuine increment
after composing the first K-child loss with the later LocalAP-child loss.
The displayed localized premise is exactly the package produced from the
scaled unconditional localized almost-periodicity theorem. -/
theorem highNorm_endpoint_increment_of_localizedPackage
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilonDense : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilonDense)
    (hepsilonDense_lt_one : epsilonDense < 1)
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    {epsilon sigma delta approximationError lowerNorm firstSizeCost
      localSizeCost : ℝ} {rankCost r : ℕ}
    (hepsilon : 0 < epsilon)
    (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hr : 0 < r) (hrEven : Even r) (hrTwo : 2 ≤ r)
    (hrTail : sigma⁻¹ * Real.log (2 / delta) ≤ r)
    (hlowerNorm : 0 ≤ lowerNorm)
    (hfirst :
      Real.exp (-firstSizeCost) * (s.card : ℝ) ≤ C.childOne.carrier.card)
    (hhigh : lowerNorm ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (μ_[Real]
          (endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one).restriction.set
          ○ᵈ
          μ (endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one).restriction.set)
        r)
    (hgain :
      (1 + epsilon / 32) *
          (endpointLocated s C.childOne C.childTwo hdense
            hepsilonDense_lt_one).density ≤
        ((endpointLocated s C.childOne C.childTwo hdense
            hepsilonDense_lt_one).restriction.set.card : ℝ) *
          (((1 - sigma) * lowerNorm) *
            (1 - delta - approximationError)))
    (hlocalized :
      ∀ (z : G), z ∈ D - E → ((z +ᵥ E) ∩ D).Nonempty →
        ∀ data : DensityStep.SiftedPopularData
            (endpointLocated s C.childOne C.childTwo hdense
              hepsilonDense_lt_one).restriction.set
            (z +ᵥ E) D r sigma delta,
          ∃ (parent : BohrData G) (parentWidth : NNReal)
            (source : Finset G) (cardMultiplier : Nat),
            ∃ P : DensityStep.LocalizedSiftingPackage data parent parentWidth source
              rankCost cardMultiplier approximationError,
              P.child.rank ≤
                (endpointLocated s C.childOne C.childTwo hdense
                  hepsilonDense_lt_one).rank + rankCost ∧
              Real.exp (-localSizeCost) *
                  ((endpointLocated s C.childOne C.childTwo hdense
                    hepsilonDense_lt_one).card : ℝ) ≤ P.child.carrier.card) :
    ∃ t : DensityStep.LocatedRestriction original,
      (1 + epsilon / 32) * densePairDensity s epsilonDense ≤ t.density ∧
      t.rank ≤ s.rank + rankCost ∧
      Real.exp (-(firstSizeCost + localSizeCost)) * (s.card : ℝ) ≤
        (t.card : ℝ) := by
  let u := endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one
  obtain ⟨t, ht⟩ :=
    DensityStep.highSmoothingNorm_locatedIncrement u hD hE hepsilon
      hsigma hsigmaOne hdelta hdeltaOne hr hrEven hrTwo hrTail hlowerNorm
      (by simpa [u] using hhigh) (by simpa [u] using hgain)
      (by simpa [u] using hlocalized)
  have huDensity : densePairDensity s epsilonDense ≤ u.density := by
    let x := GroupCount.densePairPoint hdense
    have hx : densePairDensity s epsilonDense ≤
        localDensity s.restriction.set C.childOne.carrier x := by
      simpa [x, densePairDensity] using
        GroupCount.densePairPoint_density_one hdense
    simpa [u, endpointLocated, DensityStep.density_narrowLocated] using hx
  have hfirst' :
      Real.exp (-firstSizeCost) * (s.card : ℝ) ≤ (u.card : ℝ) := by
    change Real.exp (-firstSizeCost) * (s.card : ℝ) ≤
      (C.childOne.carrier.card : ℝ)
    exact hfirst
  refine ⟨t, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left huDensity (by nlinarith)).trans ht.1
  · have huRank : u.rank = s.rank := by
      simpa [u, endpointLocated, DensityStep.LocatedRestriction.rank,
        BohrStopping.RegularRestriction.rank,
        DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
        using C.rankOne
    rw [← huRank]
    exact ht.2.1
  · calc
      Real.exp (-(firstSizeCost + localSizeCost)) * (s.card : ℝ) =
          Real.exp (-localSizeCost) *
            (Real.exp (-firstSizeCost) * (s.card : ℝ)) := by
        rw [show -(firstSizeCost + localSizeCost) =
            -localSizeCost + -firstSizeCost by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (-localSizeCost) * (u.card : ℝ) :=
        mul_le_mul_of_nonneg_left hfirst' (Real.exp_pos _).le
      _ ≤ (t.card : ℝ) := ht.2.2

/-- Rank-regular strengthening of the high-smoothing-norm density step.

The generic density step deliberately forgets regularity of the selected
local-almost-period Bohr datum.  The final rank-regular recursion cannot
forget it, so we repeat only its final averaging paragraph and choose the
unit regular child of the already rank-regular datum. -/
theorem highSmoothingNorm_rankRegularLocatedIncrement
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {D E : Finset G}
    (hD : D.Nonempty) (hE : E.Nonempty)
    {epsilon sigma delta approximationError lowerNorm sizeCost : ℝ}
    {rankCost r : ℕ}
    (hepsilon : 0 < epsilon)
    (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hr : 0 < r) (hrEven : Even r) (hrTwo : 2 ≤ r)
    (hrTail : sigma⁻¹ * Real.log (2 / delta) ≤ r)
    (hlowerNorm : 0 ≤ lowerNorm)
    (hhigh : lowerNorm ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) r)
    (hgain :
      (1 + epsilon / 32) * s.density ≤
        (s.restriction.set.card : ℝ) *
          (((1 - sigma) * lowerNorm) *
            (1 - delta - approximationError)))
    (hlocalized :
      ∀ (z : G), z ∈ D - E → ((z +ᵥ E) ∩ D).Nonempty →
        lowerNorm ≤
          ‖μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set‖_[
            r, μ (z +ᵥ E) ○ᵈ μ D] →
        ∀ data : DensityStep.SiftedPopularData s.restriction.set
            (z +ᵥ E) D r sigma delta,
          ∃ (parent : BohrData G) (parentWidth : NNReal)
            (source : Finset G) (cardMultiplier : ℕ),
            ∃ P : DensityStep.LocalizedSiftingPackage data parent parentWidth
              source rankCost cardMultiplier approximationError,
              P.child.rank ≤ s.rank + rankCost ∧
              Real.exp (-sizeCost) * (s.card : ℝ) ≤ P.child.carrier.card) :
    ∃ t : FinalAssembly.RankRegularLocatedRestriction original,
      BohrStopping.IsControlledIncrement (1 + epsilon / 32) rankCost sizeCost
        s.restriction t.located.restriction := by
  obtain ⟨z, hz, hinter, hlocalNorm⟩ :=
    DensityStep.exists_translated_difference_lpNorm_ge hD hE
      s.restriction.nonempty hr hlowerNorm hhigh
  let B₁ : Finset G := z +ᵥ E
  let B₂ : Finset G := D
  have hB : (B₁ ∩ B₂).Nonempty := by
    simpa [B₁, B₂] using hinter
  obtain ⟨data⟩ :=
    DensityStep.exists_sifted_popular_data_unconditional
      (A := s.restriction.set) (p := r) (epsilon := sigma) (delta := delta)
      B₁ B₂ hsigma hsigmaOne hdelta hrEven hrTwo hrTail hB
      s.restriction.nonempty
  obtain ⟨parent, parentWidth, source, cardMultiplier, P, hPrank, hPcard⟩ :=
    hlocalized z hz (by simpa [B₁, B₂] using hinter)
      (by simpa [B₁, B₂] using hlocalNorm)
      (by simpa [B₁, B₂] using data)
  have houtputs := data.output_nonempty hdeltaOne
  have hmass :
      1 - delta - approximationError ≤
        LocalizedAlmostPeriodicity.countingInner
          (LocalizedAlmostPeriodicity.sumConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator P.child.carrier)
            (LocalizedAlmostPeriodicity.differenceConvolution
              (LocalizedAlmostPeriodicity.probabilityIndicator data.A₁)
              (LocalizedAlmostPeriodicity.probabilityIndicator data.A₂)))
          (LocalizedAlmostPeriodicity.setIndicator
            (_root_.s r sigma B₁ B₂ s.restriction.set)) := by
    exact DensityStep.smoothed_popular_mass_lower_bound houtputs.1 houtputs.2
      (by
        simpa only [DensityStep.countingInner_difference_setIndicator_eq_sum]
          using data.popular_mass)
      P.triple_error
  have hthreshold : 0 ≤ (1 - sigma) * lowerNorm :=
    mul_nonneg (sub_nonneg.mpr hsigmaOne) hlowerNorm
  have hpopular : ∀ x ∈ _root_.s r sigma B₁ B₂ s.restriction.set,
      (1 - sigma) * lowerNorm ≤
        (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) x := by
    intro x hx
    have hxPopular :
        (1 - sigma) *
            ‖μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set‖_[
              r, μ B₁ ○ᵈ μ B₂] <
          (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) x :=
      (mem_s'.mp hx)
    exact (mul_le_mul_of_nonneg_left hlocalNorm
      (sub_nonneg.mpr hsigmaOne)).trans hxPopular.le
  have hcorr : ∀ x, 0 ≤
      (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) x := by
    intro x
    exact dddconv_apply_nonneg mu_nonneg mu_nonneg x
  obtain ⟨x, hx⟩ :=
    DensityStep.exists_localDensity_ge_of_smoothed_superlevel
      P.child.carrier_nonempty houtputs.1 houtputs.2 s.restriction.nonempty
      hthreshold hcorr hpopular hmass
      (show ((1 - sigma) * lowerNorm) * (1 - delta - approximationError) ≤
          ((1 - sigma) * lowerNorm) * (1 - delta - approximationError) from le_rfl)
  obtain ⟨child, hchildBohr, hchildOuter, hchildCarrier⟩ :=
    DensityStep.RegularChild.exists_of_rankRegular P.child P.child_regular
  have hx' :
      (1 + epsilon / 32) * s.density ≤
        localDensity s.restriction.set child.carrier x := by
    rw [hchildCarrier]
    exact hgain.trans hx
  have hpos : 0 <
      localDensity s.restriction.set child.carrier x :=
    (mul_pos (by nlinarith [hepsilon]) s.density_pos).trans_le hx'
  let t := DensityStep.narrowLocated s child x hpos
  refine ⟨{ located := t, outer_one := ?_, rankRegular := ?_ }, ?_⟩
  · simpa [t, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
      using hchildOuter
  · simpa [t, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction,
      hchildBohr] using P.child_regular
  · apply DensityStep.narrowLocated_isControlledIncrement s child x hpos hx'
    · simpa [hchildBohr] using hPrank
    · simpa [hchildCarrier] using hPcard

/-- Support-restricted rank-regular high-norm step.  This is the version
used with the relative-T package, where the popular set is intersected with
the actual base-pair difference support before Croot--Sisask is invoked. -/
theorem highSmoothingNorm_rankRegularLocatedIncrement_supported
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {D E : Finset G}
    (hD : D.Nonempty) (hE : E.Nonempty)
    {epsilon sigma delta approximationError lowerNorm sizeCost : ℝ}
    {rankCost r : ℕ}
    (hepsilon : 0 < epsilon)
    (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hr : 0 < r) (hrEven : Even r) (hrTwo : 2 ≤ r)
    (hrTail : sigma⁻¹ * Real.log (2 / delta) ≤ r)
    (hlowerNorm : 0 ≤ lowerNorm)
    (hhigh : lowerNorm ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) r)
    (hgain :
      (1 + epsilon / 32) * s.density ≤
        (s.restriction.set.card : ℝ) *
          (((1 - sigma) * lowerNorm) *
            (1 - delta - approximationError)))
    (hlocalized :
      ∀ (z : G), z ∈ D - E → ((z +ᵥ E) ∩ D).Nonempty →
        lowerNorm ≤
          ‖μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set‖_[
            r, μ (z +ᵥ E) ○ᵈ μ D] →
        ∀ data : DensityStep.SiftedPopularData s.restriction.set
            (z +ᵥ E) D r sigma delta,
          ∃ (parent : BohrData G) (parentWidth : NNReal)
            (source : Finset G) (cardMultiplier : ℕ),
            ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
              parentWidth source rankCost cardMultiplier approximationError,
              P.child.rank ≤ s.rank + rankCost ∧
              Real.exp (-sizeCost) * (s.card : ℝ) ≤ P.child.carrier.card) :
    ∃ t : FinalAssembly.RankRegularLocatedRestriction original,
      BohrStopping.IsControlledIncrement (1 + epsilon / 32) rankCost sizeCost
        s.restriction t.located.restriction := by
  obtain ⟨z, hz, hinter, hlocalNorm⟩ :=
    DensityStep.exists_translated_difference_lpNorm_ge hD hE
      s.restriction.nonempty hr hlowerNorm hhigh
  let B₁ : Finset G := z +ᵥ E
  let B₂ : Finset G := D
  have hB : (B₁ ∩ B₂).Nonempty := by
    simpa [B₁, B₂] using hinter
  obtain ⟨data⟩ :=
    DensityStep.exists_sifted_popular_data_unconditional
      (A := s.restriction.set) (p := r) (epsilon := sigma) (delta := delta)
      B₁ B₂ hsigma hsigmaOne hdelta hrEven hrTwo hrTail hB
      s.restriction.nonempty
  obtain ⟨parent, parentWidth, source, cardMultiplier, P, hPrank, hPcard⟩ :=
    hlocalized z hz (by simpa [B₁, B₂] using hinter)
      (by simpa [B₁, B₂] using hlocalNorm)
      (by simpa [B₁, B₂] using data)
  have houtputs := data.output_nonempty hdeltaOne
  let S : Finset G :=
    DensityStep.SiftedPopularData.supportedPopularSet
      s.restriction.set B₁ B₂ r sigma
  have hmass :
      1 - delta - approximationError ≤
        LocalizedAlmostPeriodicity.countingInner
          (LocalizedAlmostPeriodicity.sumConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator P.child.carrier)
            (LocalizedAlmostPeriodicity.differenceConvolution
              (LocalizedAlmostPeriodicity.probabilityIndicator data.A₁)
              (LocalizedAlmostPeriodicity.probabilityIndicator data.A₂)))
          (LocalizedAlmostPeriodicity.setIndicator S) := by
    exact DensityStep.smoothed_popular_mass_lower_bound houtputs.1 houtputs.2
      (by
        simpa only [DensityStep.countingInner_difference_setIndicator_eq_sum]
          using data.supported_popular_mass)
      (by simpa [S] using P.triple_error)
  have hthreshold : 0 ≤ (1 - sigma) * lowerNorm :=
    mul_nonneg (sub_nonneg.mpr hsigmaOne) hlowerNorm
  have hpopular : ∀ x ∈ S,
      (1 - sigma) * lowerNorm ≤
        (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) x := by
    intro x hx
    have hxGlobal : x ∈ _root_.s r sigma B₁ B₂ s.restriction.set := by
      have hx' := hx
      change x ∈ _root_.s r sigma B₁ B₂ s.restriction.set ∩ (B₁ - B₂) at hx'
      exact (Finset.mem_inter.mp hx').1
    have hxPopular :
        (1 - sigma) *
            ‖μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set‖_[
              r, μ B₁ ○ᵈ μ B₂] <
          (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) x :=
      (mem_s'.mp hxGlobal)
    exact (mul_le_mul_of_nonneg_left hlocalNorm
      (sub_nonneg.mpr hsigmaOne)).trans hxPopular.le
  have hcorr : ∀ x, 0 ≤
      (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) x := by
    intro x
    exact dddconv_apply_nonneg mu_nonneg mu_nonneg x
  obtain ⟨x, hx⟩ :=
    DensityStep.exists_localDensity_ge_of_smoothed_superlevel
      P.child.carrier_nonempty houtputs.1 houtputs.2 s.restriction.nonempty
      hthreshold hcorr hpopular hmass
      (show ((1 - sigma) * lowerNorm) * (1 - delta - approximationError) ≤
          ((1 - sigma) * lowerNorm) * (1 - delta - approximationError) from le_rfl)
  obtain ⟨child, hchildBohr, hchildOuter, hchildCarrier⟩ :=
    DensityStep.RegularChild.exists_of_rankRegular P.child P.child_regular
  have hx' :
      (1 + epsilon / 32) * s.density ≤
        localDensity s.restriction.set child.carrier x := by
    rw [hchildCarrier]
    exact hgain.trans hx
  have hpos : 0 < localDensity s.restriction.set child.carrier x :=
    (mul_pos (by nlinarith [hepsilon]) s.density_pos).trans_le hx'
  let t := DensityStep.narrowLocated s child x hpos
  refine ⟨{ located := t, outer_one := ?_, rankRegular := ?_ }, ?_⟩
  · simpa [t, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
      using hchildOuter
  · simpa [t, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction,
      hchildBohr] using P.child_regular
  · apply DensityStep.narrowLocated_isControlledIncrement s child x hpos hx'
    · simpa [hchildBohr] using hPrank
    · simpa [hchildCarrier] using hPcard

/-- Compose the rank-regular supported high-norm step on the endpoint fibre
with the first reciprocal-child loss.  This is the exact shape required by
the raw two-Bohr endpoint interface. -/
theorem highNorm_endpoint_rankRegular_increment_of_supportedPackage
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilonDense : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilonDense)
    (hepsilonDense_lt_one : epsilonDense < 1)
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    {epsilon sigma delta approximationError lowerNorm firstSizeCost
      localSizeCost : ℝ} {rankCost r : ℕ}
    (hepsilon : 0 < epsilon)
    (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hr : 0 < r) (hrEven : Even r) (hrTwo : 2 ≤ r)
    (hrTail : sigma⁻¹ * Real.log (2 / delta) ≤ r)
    (hlowerNorm : 0 ≤ lowerNorm)
    (hfirst :
      Real.exp (-firstSizeCost) * (s.card : ℝ) ≤ C.childOne.carrier.card)
    (hhigh : lowerNorm ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (μ_[Real]
          (endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one).restriction.set
          ○ᵈ
          μ (endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one).restriction.set)
        r)
    (hgain :
      (1 + epsilon / 32) *
          (endpointLocated s C.childOne C.childTwo hdense
            hepsilonDense_lt_one).density ≤
        ((endpointLocated s C.childOne C.childTwo hdense
            hepsilonDense_lt_one).restriction.set.card : ℝ) *
          (((1 - sigma) * lowerNorm) *
            (1 - delta - approximationError)))
    (hlocalized :
      ∀ (z : G), z ∈ D - E → ((z +ᵥ E) ∩ D).Nonempty →
        lowerNorm ≤
          ‖μ_[ℝ]
              (endpointLocated s C.childOne C.childTwo hdense
                hepsilonDense_lt_one).restriction.set ○ᵈ
              μ (endpointLocated s C.childOne C.childTwo hdense
                hepsilonDense_lt_one).restriction.set‖_[
            r, μ (z +ᵥ E) ○ᵈ μ D] →
        ∀ data : DensityStep.SiftedPopularData
            (endpointLocated s C.childOne C.childTwo hdense
              hepsilonDense_lt_one).restriction.set
            (z +ᵥ E) D r sigma delta,
          ∃ (parent : BohrData G) (parentWidth : NNReal)
            (source : Finset G) (cardMultiplier : Nat),
            ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
              parentWidth source rankCost cardMultiplier approximationError,
              P.child.rank ≤
                (endpointLocated s C.childOne C.childTwo hdense
                  hepsilonDense_lt_one).rank + rankCost ∧
              Real.exp (-localSizeCost) *
                  ((endpointLocated s C.childOne C.childTwo hdense
                    hepsilonDense_lt_one).card : ℝ) ≤ P.child.carrier.card) :
    ∃ t : FinalAssembly.RankRegularLocatedRestriction original,
      (1 + epsilon / 32) * densePairDensity s epsilonDense ≤ t.density ∧
      t.rank ≤ s.rank + rankCost ∧
      Real.exp (-(firstSizeCost + localSizeCost)) * (s.card : ℝ) ≤
        (t.card : ℝ) := by
  let u := endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one
  obtain ⟨t, ht⟩ :=
    highSmoothingNorm_rankRegularLocatedIncrement_supported u hD hE hepsilon
      hsigma hsigmaOne hdelta hdeltaOne hr hrEven hrTwo hrTail hlowerNorm
      (by simpa [u] using hhigh) (by simpa [u] using hgain)
      (by simpa [u] using hlocalized)
  have huDensity : densePairDensity s epsilonDense ≤ u.density := by
    let x := GroupCount.densePairPoint hdense
    have hx : densePairDensity s epsilonDense ≤
        localDensity s.restriction.set C.childOne.carrier x := by
      simpa [x, densePairDensity] using
        GroupCount.densePairPoint_density_one hdense
    simpa [u, endpointLocated, DensityStep.density_narrowLocated] using hx
  have hfirst' :
      Real.exp (-firstSizeCost) * (s.card : ℝ) ≤ (u.card : ℝ) := by
    change Real.exp (-firstSizeCost) * (s.card : ℝ) ≤
      (C.childOne.carrier.card : ℝ)
    exact hfirst
  refine ⟨t, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left huDensity (by nlinarith)).trans ht.1
  · have huRank : u.rank = s.rank := by
      simpa [u, endpointLocated, DensityStep.LocatedRestriction.rank,
        BohrStopping.RegularRestriction.rank,
        DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
        using C.rankOne
    rw [← huRank]
    exact ht.2.1
  · calc
      Real.exp (-(firstSizeCost + localSizeCost)) * (s.card : ℝ) =
          Real.exp (-localSizeCost) *
            (Real.exp (-firstSizeCost) * (s.card : ℝ)) := by
        rw [show -(firstSizeCost + localSizeCost) =
            -localSizeCost + -firstSizeCost by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (-localSizeCost) * (u.card : ℝ) :=
        mul_le_mul_of_nonneg_left hfirst' (Real.exp_pos _).le
      _ ≤ (t.card : ℝ) := ht.2.2

end EndpointHighNorm

/-! ## Raw two-Bohr endpoint data -/

section TwoBohr

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The scaled balanced convolution used by the Holder endpoint. -/
def scaledBalanced (K : BohrData G) (A : Finset G) : G → ℝ :=
  (Fintype.card G : ℝ) •
    normalizedConvolution (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier)

/-- The two-scale doubled-middle inclusion discharges the Holder
approximation field for the actual endpoint and middle fibres. -/
theorem approximation_of_twoScaleDensePair
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hkappa :
      (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ ≤
        1 / (100 * (max C.childOne.bohr.rank 1 : ℕ) : NNReal))
    (hwidth :
      2 * (((endpointSet s C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ))) +
        (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ)) ≤
        (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹) :
    |(GroupCount.normalizedMixedProgression
          (endpointSet s C.childOne C.childTwo hdense)
          (middleSet s C.childOne C.childTwo hdense) -
        (Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) -
        HolderLifting.pairing
          (scaledBalanced C.childOne.bohr
            (endpointSet s C.childOne C.childTwo hdense))
          (GroupCount.doubledFinset
            (middleSet s C.childOne C.childTwo hdense))| ≤
      ((Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) / 8 := by
  let alpha := densePairDensity s epsilon
  have halpha : 0 < alpha :=
    mul_pos (sub_pos.mpr hepsilon_lt_one) s.density_pos
  have hOne : alpha ≤
      localDensity s.restriction.set C.childOne.carrier
        (GroupCount.densePairPoint hdense) := by
    simpa [alpha, densePairDensity] using
      GroupCount.densePairPoint_density_one hdense
  have hTwo : alpha ≤
      localDensity s.restriction.set C.childTwo.carrier
        (GroupCount.densePairPoint hdense) := by
    simpa [alpha, densePairDensity] using
      GroupCount.densePairPoint_density_two hdense
  have hA :
      (endpointSet s C.childOne C.childTwo hdense).Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos
      C.childOne.carrier_nonempty
    exact halpha.trans_le hOne
  have hA'' :
      (middleSet s C.childOne C.childTwo hdense).Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos
      C.childTwo.carrier_nonempty
    exact halpha.trans_le hTwo
  have hAK :
      endpointSet s C.childOne C.childTwo hdense ⊆
        C.childOne.bohr.carrier := by
    rw [← C.childOne_carrier]
    exact DensityStep.narrowingSet_subset_carrier
      (B := C.childOne.bohr) (rho := C.childOne.outer)
      (A := s.restriction.set) (C := C.childOne.carrier)
      (x := GroupCount.densePairPoint hdense) (fun _ hz ↦ hz)
  have hmiddle :
      middleSet s C.childOne C.childTwo hdense ⊆ C.childTwo.carrier := by
    exact DensityStep.narrowingSet_subset_carrier
      (B := C.childTwo.bohr) (rho := C.childTwo.outer)
      (A := s.restriction.set) (C := C.childTwo.carrier)
      (x := GroupCount.densePairPoint hdense) (fun _ hz ↦ hz)
  have hsmall :
      GroupCount.doubledFinset
          (middleSet s C.childOne C.childTwo hdense) ⊆
        (C.childOne.bohr.dilate
          ((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹)).carrier :=
    (GroupCount.doubledFinset_mono hmiddle).trans C.doubled_middle_small
  have h :=
    HolderApproximation.normalizedMixedProgression_scaledBalanced_approximation_of_boundaryWidth
      C.childOne_rankRegular hkappa hA hAK hA'' hsmall hwidth
  simpa [scaledBalanced, C.childOne_carrier] using h

/-- Bridge the concrete two-scale geometry to the exact raw endpoint
interface exported by FinalAssembly.

The inputs after the doubled-weight datum are precisely the local analytic
objects still produced by the terminal construction: two smoothing sets,
their support and boundary estimates, and the genuine rank-regular
high-norm exit.  The theorem itself only aligns the two copies of the raw
finite-set definitions and fills the deterministic endpoint fields. -/
theorem finalRawTwoBohrEndpointPackage_of_twoScale
    {original : Finset G}
    (s : FinalAssembly.RankRegularLocatedRestriction original)
    {mOne mTwo : ℕ} (hmOne : 0 < mOne) (hmTwo : 0 < mTwo)
    (C : ReciprocalChildren s.located.restriction.bohr mOne mTwo)
    {epsilon sizeCost : ℝ} {rankCost p : ℕ}
    (hnum : ReciprocalStepBounds s.located mOne mTwo epsilon sizeCost)
    (hdense : DensityStep.HasDensePair s.located
      (rankRegularNarrowingPackage_of_reciprocalChildren
        (rankCost := rankCost) s hmOne hmTwo C hnum).childOne
      (rankRegularNarrowingPackage_of_reciprocalChildren
        (rankCost := rankCost) s hmOne hmTwo C hnum).childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (W : BohrData G) (hWreg : W.IsRankRegular)
    (hWcarrier :
      W.carrier = GroupCount.doubledFinset C.childTwo.carrier)
    {eta : ℝ≥0} (heta : 0 < eta)
    (hetaNarrow :
      4 * eta ≤ 1 / (400 * (max W.rank 1 : ℕ) : ℝ≥0))
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    (hDsmall : D ⊆ (W.dilate eta).carrier)
    (hEsmall : E ⊆ (W.dilate eta).carrier)
    {kappa : ℝ≥0}
    (hkappaEq :
      kappa = (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹)
    (hkappa :
      kappa ≤
        1 / (100 * (max C.childOne.bohr.rank 1 : ℕ) : ℝ≥0))
    (hsupport :
      ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
        t ∈ (C.childOne.bohr.dilate kappa).carrier)
    (hwidth :
      2 * (((endpointSet s.located C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (kappa : ℝ))) +
        (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (kappa : ℝ)) ≤
        (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹)
    (hpDensity :
      (2 / 3 : ℝ) ^ p ≤
        GroupCount.densePairDensity s.located epsilon)
    (hhigh :
      (1 + (1 / 8 : ℝ) / 8) *
          (C.childOne.bohr.carrier.card : ℝ)⁻¹ ≤
          BalancedRestriction.weightedLpNorm
            ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
            (μ_[ℝ] (FinalAssembly.rawDensePairEndpointSet hdense) ○ᵈ
              μ (FinalAssembly.rawDensePairEndpointSet hdense))
            (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p) →
        ∃ t : FinalAssembly.RankRegularLocatedRestriction original,
          (257 / 256 : ℝ) *
              GroupCount.densePairDensity s.located epsilon ≤ t.density ∧
          t.rank ≤ s.rank + rankCost ∧
          Real.exp (-sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ)) :
    Nonempty
      (FinalAssembly.RawTwoBohrEndpointPackage (p := p) s
        (rankRegularNarrowingPackage_of_reciprocalChildren
          (rankCost := rankCost) s hmOne hmTwo C hnum) hdense) := by
  let P := rankRegularNarrowingPackage_of_reciprocalChildren
    (rankCost := rankCost) s hmOne hmTwo C hnum
  change DensityStep.HasDensePair s.located C.childOne C.childTwo epsilon at hdense
  have hendpoint :
      (FinalAssembly.rawDensePairEndpointSet hdense).Nonempty := by
    simpa [FinalAssembly.rawDensePairEndpointSet, endpointSet] using
      endpointSet_nonempty s.located C.childOne C.childTwo hdense hepsilon_lt_one
  have hsubset :
      FinalAssembly.rawDensePairEndpointSet hdense ⊆ C.childOne.bohr.carrier := by
    rw [← C.childOne_carrier]
    simpa [FinalAssembly.rawDensePairEndpointSet, endpointSet] using
      endpointSet_subset_childOne s.located C.childOne C.childTwo hdense
  have happrox :
      |(GroupCount.normalizedMixedProgression
            (FinalAssembly.rawDensePairEndpointSet hdense)
            (FinalAssembly.rawDensePairMiddleSet hdense) -
          (Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) -
          HolderLifting.pairing
            (FinalAssembly.scaledBalanced C.childOne.bohr
              (FinalAssembly.rawDensePairEndpointSet hdense))
            (GroupCount.doubledFinset
              (FinalAssembly.rawDensePairMiddleSet hdense))| ≤
        ((Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) / 8 := by
    have hholder :
        (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ ≤
          1 / (100 * (max C.childOne.bohr.rank 1 : ℕ) : NNReal) := by
      simpa [hkappaEq] using hkappa
    have hwidthHolder :
        2 * (((endpointSet s.located C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
            (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
              (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ))) +
          (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
            (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
              (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ)) ≤
          (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹ := by
      simpa [hkappaEq] using hwidth
    simpa [FinalAssembly.rawDensePairEndpointSet,
      FinalAssembly.rawDensePairMiddleSet, endpointSet, middleSet,
      FinalAssembly.scaledBalanced, scaledBalanced] using
      approximation_of_twoScaleDensePair s.located C hdense hepsilon_lt_one
        hholder hwidthHolder
  exact ⟨{
    base := C.childOne.bohr
    weight := W
    base_regular := C.childOne_rankRegular
    weight_regular := hWreg
    base_carrier := by
      change C.childOne.bohr.carrier = C.childOne.carrier
      exact C.childOne_carrier.symm
    weight_carrier := hWcarrier
    endpoint_nonempty := hendpoint
    endpoint_subset := hsubset
    eta := eta
    eta_pos := heta
    eta_narrow := hetaNarrow
    D := D
    E := E
    D_nonempty := hD
    E_nonempty := hE
    D_small := hDsmall
    E_small := hEsmall
    kappa := kappa
    rank_width := hkappa
    smoothing_support := hsupport
    boundary_width := hwidth
    density_power := hpDensity
    approximation := happrox
    highNorm_increment := hhigh }⟩

/-- The actual dyadic hierarchy fills the raw endpoint interface once the
two outer volume budgets and the single fixed local budget are supplied.
All analytic choices are now literal constants. -/
theorem finalRawTwoBohrEndpointPackage_of_dyadic_hierarchy
    {original : Finset G}
    (s : FinalAssembly.RankRegularLocatedRestriction original)
    {d rankCap mOne mTwo : ℕ}
    (hmOne : 0 < mOne) (hmTwo : 0 < mTwo)
    (C : ReciprocalChildren s.located.restriction.bohr mOne mTwo)
    {firstSizeCost localSizeCost : ℝ}
    (hnum : ReciprocalStepBounds s.located mOne mTwo (1 / 512 : ℝ)
      (firstSizeCost + localSizeCost))
    (hfirst :
      Real.exp (-firstSizeCost) * (s.card : ℝ) ≤ C.childOne.carrier.card)
    (hdense : DensityStep.HasDensePair s.located
      (rankRegularNarrowingPackage_of_reciprocalChildren
        (rankCost := RawSupplyNumerics.dyadicRankCost (d + 1))
        s hmOne hmTwo C hnum).childOne
      (rankRegularNarrowingPackage_of_reciprocalChildren
        (rankCost := RawSupplyNumerics.dyadicRankCost (d + 1))
        s hmOne hmTwo C hnum).childTwo (1 / 512 : ℝ))
    (hscale : 1 / (2 : ℝ) ^ d ≤ s.density)
    (W : BohrData G) (hWreg : W.IsRankRegular)
    (hWcarrier : W.carrier = GroupCount.doubledFinset C.childTwo.carrier)
    (hWcard : W.carrier.card = C.childTwo.carrier.card)
    (hWrank : W.rank = s.rank)
    (H : SmoothingHierarchy W)
    (hsrank : s.rank ≤ rankCap)
    (hkappa :
      (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ ≤
        1 / (100 * (max C.childOne.bohr.rank 1 : ℕ) : NNReal))
    (hwidth :
      2 * (((endpointSet s.located C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ))) +
        (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ)) ≤
        (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹)
    (hlocalBudget :
      Real.exp (-localSizeCost) *
          ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
            smoothingHierarchyLoss W : ℕ) : ℝ) *
          (((3 * dyadicSourceDenominator (d + 1) rankCap) ^ rankCap : ℕ) : ℝ) *
            (dyadicCardMultiplier (d + 1) rankCap : ℝ) ≤ 1) :
    Nonempty (FinalAssembly.RawTwoBohrEndpointPackage
      (p := RawSupplyNumerics.holderExponent (d + 1)) s
      (rankRegularNarrowingPackage_of_reciprocalChildren
        (rankCost := RawSupplyNumerics.dyadicRankCost (d + 1))
        s hmOne hmTwo C hnum) hdense) := by
  change DensityStep.HasDensePair s.located C.childOne C.childTwo
    (1 / 512 : ℝ) at hdense
  let u := endpointLocated s.located C.childOne C.childTwo hdense (by norm_num)
  have hranks := smoothingHierarchy_ranks W H
  have hB₀rankEq : H.B₀.rank = s.rank := hranks.2.2.trans hWrank
  have hB₀rankCap : H.B₀.rank ≤ rankCap := by rw [hB₀rankEq]; exact hsrank
  have huRank : u.rank = s.rank := by
    simpa [u, endpointLocated, DensityStep.LocatedRestriction.rank,
      FinalAssembly.RankRegularLocatedRestriction.rank,
      BohrStopping.RegularRestriction.rank,
      DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
      using C.rankOne
  have hB₀rankU : H.B₀.rank ≤ u.rank := by
    rw [hB₀rankEq, huRank]
  have huScale : 1 / (2 : ℝ) ^ (d + 1) ≤ u.density := by
    simpa [u] using endpointLocated_on_nextDyadicScale s.located C hdense rfl
      (by norm_num) hscale
  have hbase : (u.card : ℝ) ≤
      ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
          smoothingHierarchyLoss W : ℕ) : ℝ) * (H.B₀.carrier.card : ℝ) := by
    simpa [u] using endpoint_card_le_globalHierarchyLoss s.located hmOne C hdense
      (by norm_num) s.outer_one W H hWcard
  have hlocalized :
      ∀ (z : G), z ∈ H.Ebohr.carrier - H.Dbohr.carrier →
        ((z +ᵥ H.Dbohr.carrier) ∩ H.Ebohr.carrier).Nonempty →
        (65 / 64 : ℝ) * (C.childOne.bohr.carrier.card : ℝ)⁻¹ ≤
          ‖μ_[ℝ] u.restriction.set ○ᵈ μ u.restriction.set‖_[
            RawSupplyNumerics.smoothingExponent (d + 1),
              μ (z +ᵥ H.Dbohr.carrier) ○ᵈ μ H.Ebohr.carrier] →
        ∀ data : DensityStep.SiftedPopularData u.restriction.set
            (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier
            (RawSupplyNumerics.smoothingExponent (d + 1))
            (1 / 8192 : ℝ) (1 / 8192 : ℝ),
          ∃ (parent : BohrData G) (parentWidth : NNReal)
            (source : Finset G) (cardMultiplier : Nat),
            ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
              parentWidth source (RawSupplyNumerics.dyadicRankCost (d + 1))
              cardMultiplier (1 / 512 : ℝ),
              P.child.rank ≤ u.rank + RawSupplyNumerics.dyadicRankCost (d + 1) ∧
              Real.exp (-localSizeCost) * (u.card : ℝ) ≤ P.child.carrier.card := by
    intro z hz hinter hlocalNorm data
    have hlocalNorm' :
        (65 / 64 : ℝ) * (C.childOne.bohr.carrier.card : ℝ)⁻¹ ≤
          BalancedRestriction.weightedLpNorm
            ((NNReal.toReal ∘ (μ (z +ᵥ H.Dbohr.carrier) ○ᵈ
              μ H.Ebohr.carrier)) : G → ℝ)
            (μ_[ℝ] u.restriction.set ○ᵈ μ u.restriction.set)
            (RawSupplyNumerics.smoothingExponent (d + 1)) := by
      rw [LocalizedUnbalancing.weightedLpNorm_eq_wLpNorm
        (μ (z +ᵥ H.Dbohr.carrier) ○ᵈ μ H.Ebohr.carrier)
        (μ_[ℝ] u.restriction.set ○ᵈ μ u.restriction.set)
        (RawSupplyNumerics.smoothingExponent_pos (d + 1))]
      exact hlocalNorm
    have halpha :
        RawSupplyNumerics.dyadicSiftedAlpha (d + 1) ≤
          DensityStep.siftingDensityLower u.restriction.set
            (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier
            (RawSupplyNumerics.smoothingExponent (d + 1)) :=
      dyadicSiftedAlpha_le_siftingDensity_of_localNorm
        u.restriction.set (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier
        C.childOne.bohr.carrier (d + 1)
        C.childOne.bohr.carrier_nonempty
        (by
          have hdensity :
              u.density = (u.restriction.set.card : ℝ) /
                C.childOne.bohr.carrier.card := by
            simp only [u, endpointLocated, DensityStep.density_narrowLocated]
            rw [DensityStep.localDensity_eq_card_narrowingSet_div
              C.childOne.carrier_nonempty]
            simp [DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction,
              C.childOne_carrier]
          rwa [← hdensity]) hlocalNorm'
    exact supportedLocalizedPackage_of_dyadic_hierarchy_fixed u W H z data
      (RawSupplyNumerics.smoothingExponent_pos (d + 1)) hinter (by norm_num)
      halpha rankCap hB₀rankU hB₀rankCap (by positivity) hbase hlocalBudget
  apply finalRawTwoBohrEndpointPackage_of_twoScale s hmOne hmTwo C hnum hdense
    (by norm_num) W hWreg hWcarrier H.eta_pos H.eta_narrow
    H.Ebohr.carrier_nonempty H.Dbohr.carrier_nonempty H.E_small H.D_small
    (show (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ =
      (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ from rfl)
    hkappa
    (smoothing_support_of_hierarchy_twoScale s.located C W H hWcarrier)
    hwidth (densePairDensity_power_next_of_dyadic s.located hscale)
  intro hhigh
  obtain ⟨t, htDensity, htRank, htCard⟩ :=
    highNorm_endpoint_rankRegular_increment_of_supportedPackage
      s.located C hdense (by norm_num) H.Ebohr.carrier_nonempty
      H.Dbohr.carrier_nonempty (epsilon := (1 / 8 : ℝ))
      (sigma := (1 / 8192 : ℝ)) (delta := (1 / 8192 : ℝ))
      (approximationError := (1 / 512 : ℝ))
      (lowerNorm := (65 / 64 : ℝ) *
        (C.childOne.bohr.carrier.card : ℝ)⁻¹)
      (firstSizeCost := firstSizeCost) (localSizeCost := localSizeCost)
      (rankCost := RawSupplyNumerics.dyadicRankCost (d + 1))
      (r := RawSupplyNumerics.smoothingExponent (d + 1))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (RawSupplyNumerics.smoothingExponent_pos (d + 1))
      (RawSupplyNumerics.smoothingExponent_even (d + 1))
      (by
        have hpos := RawSupplyNumerics.smoothingExponent_pos (d + 1)
        have heven := RawSupplyNumerics.smoothingExponent_even (d + 1)
        rcases heven with ⟨k, hk⟩
        omega)
      (dyadic_smoothing_tail_bound (d + 1)) (by positivity) hfirst
      (by
        norm_num at hhigh ⊢
        simpa [u, RawSupplyNumerics.smoothingExponent,
          FinalAssembly.rawDensePairEndpointSet, endpointSet,
          rankRegularNarrowingPackage_of_reciprocalChildren] using hhigh)
      (endpoint_dyadic_high_gain s.located C hdense (by norm_num))
      (by simpa [u] using hlocalized)
  exact ⟨t, by norm_num at htDensity ⊢; exact htDensity, htRank, by
    simpa [FinalAssembly.RankRegularLocatedRestriction.card,
      add_comm, add_left_comm, add_assoc] using htCard⟩

/-- Uniform coefficient used by the unconditional raw supply.  The factor
4096 splits evenly into one first-child budget and one localized budget,
and each half pays the shift from d to d+1. -/
def rawSupplyConstant : ℝ :=
  4096 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ)

lemma nextScale_total_log_le_halfSupply
    (d rank cap : ℕ)
    (hrank : rank ≤ ConcreteNumerics.rankCap (d + 1)
      (RawSupplyNumerics.dyadicRankCost (d + 1)))
    (hcap : cap ≤ 8 * RawSupplyNumerics.dyadicRankCost (d + 1)) :
    Real.log (RawSupplyNumerics.dyadicTotalLossFormula (d + 1) rank cap : ℝ) ≤
      2048 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  have hlog := RawSupplyNumerics.log_dyadicTotalLossFormula_le_degree_eleven
    (d + 1) rank cap hrank hcap
  have hbase : ((d + 1 + 1 : ℕ) : ℝ) ≤ 2 * ((d + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hpow : ((d + 1 + 1 : ℕ) : ℝ) ^ 11 ≤
      (2 : ℝ) ^ 11 * ((d + 1 : ℕ) : ℝ) ^ 11 := by
    calc
      ((d + 1 + 1 : ℕ) : ℝ) ^ 11 ≤
          (2 * ((d + 1 : ℕ) : ℝ)) ^ 11 :=
        pow_le_pow_left₀ (by positivity) hbase 11
      _ = (2 : ℝ) ^ 11 * ((d + 1 : ℕ) : ℝ) ^ 11 := by rw [mul_pow]
  calc
    Real.log (RawSupplyNumerics.dyadicTotalLossFormula (d + 1) rank cap : ℝ) ≤
        (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
          ((d + 1 + 1 : ℕ) : ℝ) ^ 11 := by simpa using hlog
    _ ≤ (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
        ((2 : ℝ) ^ 11 * ((d + 1 : ℕ) : ℝ) ^ 11) := by gcongr
    _ = 2048 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by norm_num; ring

lemma nextScale_twoReciprocal_log_le_halfSupply
    (d rank : ℕ)
    (hrank : rank ≤ ConcreteNumerics.rankCap (d + 1)
      (RawSupplyNumerics.dyadicRankCost (d + 1))) :
    Real.log (RawSupplyNumerics.twoReciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
      (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) : ℝ) ≤
      2048 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  let cap := RawSupplyNumerics.dyadicRankCost (d + 1) + 1
  have hcap : cap ≤ 8 * RawSupplyNumerics.dyadicRankCost (d + 1) := by
    dsimp [cap]
    have hpos := RawSupplyNumerics.dyadicRankCost_pos (d + 1)
    omega
  have htotal := nextScale_total_log_le_halfSupply d rank cap hrank hcap
  have htwoPos : (0 : ℝ) < RawSupplyNumerics.twoReciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
      (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) := by
    exact_mod_cast Nat.mul_pos
      (RawSupplyNumerics.reciprocalLossFormula_pos
        (ConcreteNumerics.mOne_pos (RawSupplyNumerics.dyadicRankCost_pos (d + 1))))
      (RawSupplyNumerics.reciprocalLossFormula_pos
        (ConcreteNumerics.mTwo_pos (RawSupplyNumerics.dyadicRankCost_pos (d + 1))))
  have hle : RawSupplyNumerics.twoReciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
      (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) ≤
      RawSupplyNumerics.dyadicTotalLossFormula (d + 1) rank cap := by
    unfold RawSupplyNumerics.dyadicTotalLossFormula
    rw [show
      RawSupplyNumerics.twoReciprocalLossFormula rank
          (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
          (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) *
          RawSupplyNumerics.smoothingHierarchyLossFormula rank *
          (3 * RawSupplyNumerics.sourceDenominator rank cap
            (RawSupplyNumerics.dyadicHierarchyFormula (d + 1)
              (ConcreteNumerics.rankCap (d + 1)
                (RawSupplyNumerics.dyadicRankCost (d + 1))))) ^ rank *
          RawSupplyNumerics.dyadicCellMultiplier (d + 1) =
        RawSupplyNumerics.twoReciprocalLossFormula rank
          (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
          (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) *
          (RawSupplyNumerics.smoothingHierarchyLossFormula rank *
          (3 * RawSupplyNumerics.sourceDenominator rank cap
            (RawSupplyNumerics.dyadicHierarchyFormula (d + 1)
              (ConcreteNumerics.rankCap (d + 1)
                (RawSupplyNumerics.dyadicRankCost (d + 1))))) ^ rank *
          RawSupplyNumerics.dyadicCellMultiplier (d + 1)) by ring]
    apply Nat.le_mul_of_pos_right
    have hsmooth : 0 < RawSupplyNumerics.smoothingHierarchyLossFormula rank := by
      unfold RawSupplyNumerics.smoothingHierarchyLossFormula
        RawSupplyNumerics.reciprocalLossFormula
      positivity
    have hsource : 0 <
        (3 * RawSupplyNumerics.sourceDenominator rank cap
          (RawSupplyNumerics.dyadicHierarchyFormula (d + 1)
            (ConcreteNumerics.rankCap (d + 1)
              (RawSupplyNumerics.dyadicRankCost (d + 1))))) ^ rank := by
      unfold RawSupplyNumerics.sourceDenominator RawSupplyNumerics.dyadicHierarchyFormula
      positivity
    have hcell : 0 < RawSupplyNumerics.dyadicCellMultiplier (d + 1) := by
      unfold RawSupplyNumerics.dyadicCellMultiplier RawSupplyNumerics.cellMultiplier
      have hq : 0 < RawSupplyNumerics.dyadicQQuant (d + 1) := by
        unfold RawSupplyNumerics.dyadicQQuant
        exact RawSupplyNumerics.qQuant_pos
          (RawSupplyNumerics.dyadicSiftedAlpha_pos (d + 1))
      positivity
    exact Nat.mul_pos (Nat.mul_pos hsmooth hsource) hcell
  exact (Real.log_le_log htwoPos (by exact_mod_cast hle)).trans htotal

lemma nextScale_reciprocal_log_le_halfSupply
    (d rank : ℕ)
    (hrank : rank ≤ ConcreteNumerics.rankCap (d + 1)
      (RawSupplyNumerics.dyadicRankCost (d + 1))) :
    Real.log (RawSupplyNumerics.reciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) : ℝ) ≤
      2048 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  have htwo := nextScale_twoReciprocal_log_le_halfSupply d rank hrank
  have honePos : (0 : ℝ) < RawSupplyNumerics.reciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) := by
    exact_mod_cast RawSupplyNumerics.reciprocalLossFormula_pos
      (ConcreteNumerics.mOne_pos (RawSupplyNumerics.dyadicRankCost_pos (d + 1)))
  have hle : RawSupplyNumerics.reciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) ≤
      RawSupplyNumerics.twoReciprocalLossFormula rank
        (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
        (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) := by
    unfold RawSupplyNumerics.twoReciprocalLossFormula
    apply Nat.le_mul_of_pos_right
    exact RawSupplyNumerics.reciprocalLossFormula_pos
      (ConcreteNumerics.mTwo_pos (RawSupplyNumerics.dyadicRankCost_pos (d + 1)))
  exact (Real.log_le_log honePos (by exact_mod_cast hle)).trans htwo

/-- The preceding geometry and dyadic bookkeeping give the unconditional
rank-regular raw supply consumed by the final recursion. -/
theorem exists_rawConcreteSupply :
    ∃ K : ℝ, 0 < K ∧ FinalAssembly.RawConcreteSupply K := by
  refine ⟨rawSupplyConstant, ?_, ?_⟩
  · unfold rawSupplyConstant
    unfold RawSupplyNumerics.dyadicTotalLogConstant
      RawSupplyNumerics.dyadicRankDegreeEightConstant
      RawSupplyNumerics.dyadicCellLogConstant
    positivity
  · intro N A hA d hd
    let e : ℕ := d + 1
    let rankCost : ℕ := RawSupplyNumerics.dyadicRankCost e
    let p : ℕ := RawSupplyNumerics.holderExponent e
    refine ⟨rankCost, p, ?_, ?_⟩
    · dsimp [p]
      exact RawSupplyNumerics.holderExponent_pos e
    · intro n hn s hscale hrank
      let rankCap : ℕ := ConcreteNumerics.rankCap e rankCost
      let mOne : ℕ := ConcreteNumerics.mOne e rankCost
      let mTwo : ℕ := ConcreteNumerics.mTwo e rankCost
      let halfCost : ℝ :=
        2048 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
          ((d + 1 : ℕ) : ℝ) ^ 11
      have hrankCost : 0 < rankCost := by
        dsimp [rankCost]
        exact RawSupplyNumerics.dyadicRankCost_pos e
      have hsrank : s.rank ≤ rankCap := by
        dsimp [rankCap, e, rankCost]
        unfold ConcreteNumerics.rankCap
        have hn' : n ≤ 1024 * (d + 1 + 1) := by omega
        exact le_trans hrank (Nat.mul_le_mul_right _ hn')
      have hmOne : 0 < mOne := by
        dsimp [mOne]
        exact ConcreteNumerics.mOne_pos hrankCost
      have hmTwo : 0 < mTwo := by
        dsimp [mTwo]
        exact ConcreteNumerics.mTwo_pos hrankCost
      have hscaleE : 1 / (2 : ℝ) ^ e ≤ s.density := by
        calc
          1 / (2 : ℝ) ^ e ≤ 1 / (2 : ℝ) ^ d := by
            dsimp [e]
            rw [pow_succ]
            have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
            field_simp
            nlinarith
          _ ≤ s.density := hscale
      have hnum : ReciprocalStepBounds s.located mOne mTwo (1 / 512 : ℝ)
          (rawSupplyConstant * ((d + 1 : ℕ) : ℝ) ^ 11) := by
        refine
          { outer_eq_one := s.outer_one
            rankRegular := s.rankRegular
            scale_rank := ?_
            scale_density := ?_
            card_budget_one := ?_
            card_budget_two := ?_ }
        · dsimp [mOne]
          exact ConcreteNumerics.inv_mOne_le_rank_scale hrankCost hsrank
        · dsimp [mOne]
          exact ConcreteNumerics.mOne_scale_density hrankCost hsrank hscaleE
        ·
          have hloss :
              (0 : ℝ) <
                (reciprocalLoss s.located.restriction.bohr mOne : ℕ) := by
            unfold reciprocalLoss
            positivity
          apply card_budget_of_log_loss s.located s.outer_one hloss
          have hlog := nextScale_reciprocal_log_le_halfSupply d s.rank hsrank
          apply hlog.trans
          unfold rawSupplyConstant
          gcongr
          norm_num
        ·
          have hloss :
              (0 : ℝ) <
                (twoReciprocalLoss s.located.restriction.bohr mOne mTwo : ℕ) := by
            unfold twoReciprocalLoss reciprocalLoss
            positivity
          apply card_budget_of_log_loss s.located s.outer_one hloss
          have hlog := nextScale_twoReciprocal_log_le_halfSupply d s.rank hsrank
          apply hlog.trans
          unfold rawSupplyConstant
          gcongr
          norm_num
      have hmTwoInv : ((mTwo : NNReal)⁻¹) ≤ 1 := by
        apply (inv_le_one₀ (by exact_mod_cast hmTwo)).2
        exact_mod_cast (show 1 ≤ mTwo by omega)
      let C : ReciprocalChildren s.located.restriction.bohr mOne mTwo :=
        Classical.choice (exists_reciprocalChildren s.located.restriction.bohr
          mOne mTwo hmOne hmTwo hmTwoInv)
      have hcost :
          halfCost + halfCost =
            rawSupplyConstant * ((d + 1 : ℕ) : ℝ) ^ 11 := by
        dsimp [halfCost, rawSupplyConstant]
        ring
      have hnumHalf :
          ReciprocalStepBounds s.located mOne mTwo (1 / 512 : ℝ)
            (halfCost + halfCost) := by
        rw [hcost]
        exact hnum
      rw [← hcost]
      let P : FinalAssembly.RankRegularNarrowingPackage s (1 / 512 : ℝ)
          (halfCost + halfCost) rankCost :=
        rankRegularNarrowingPackage_of_reciprocalChildren
          (rankCost := rankCost) s hmOne hmTwo C hnumHalf
      refine ⟨P, ?_⟩
      intro hdense
      have hfirstBudget :
          Real.exp (-halfCost) * (s.located.card : ℝ) ≤
            ((reciprocalLoss s.located.restriction.bohr mOne : ℕ) : ℝ)⁻¹ *
              (s.located.restriction.bohr.carrier.card : ℝ) := by
        have hloss :
            (0 : ℝ) <
              (reciprocalLoss s.located.restriction.bohr mOne : ℕ) := by
          unfold reciprocalLoss
          positivity
        apply card_budget_of_log_loss s.located s.outer_one hloss
        simpa [halfCost, reciprocalLoss,
          RawSupplyNumerics.reciprocalLossFormula, mOne, e, rankCost,
          FinalAssembly.RankRegularLocatedRestriction.rank,
          DensityStep.LocatedRestriction.rank,
          BohrStopping.RegularRestriction.rank] using
          (nextScale_reciprocal_log_le_halfSupply d s.rank hsrank)
      have hfirst :
          Real.exp (-halfCost) * (s.card : ℝ) ≤ C.childOne.carrier.card := by
        have hloss :
            (0 : ℝ) <
              (reciprocalLoss s.located.restriction.bohr mOne : ℕ) := by
          unfold reciprocalLoss
          positivity
        have hvol :
            (s.located.restriction.bohr.carrier.card : ℝ) ≤
              (reciprocalLoss s.located.restriction.bohr mOne : ℝ) *
                (C.childOne.carrier.card : ℝ) := by
          exact_mod_cast C.cardOne
        simpa [FinalAssembly.RankRegularLocatedRestriction.card] using
          child_card_of_loss s.located hloss hfirstBudget hvol
      letI : NeZero (intervalModulus N) := ⟨by simp [intervalModulus]⟩
      have hodd : Odd (intervalModulus N) := by
        exact ⟨N, by simp [intervalModulus, two_mul]⟩
      let W : BohrData (ZMod (intervalModulus N)) :=
        GroupCount.doubledBohrData (intervalModulus N) hodd C.childTwo.bohr
      have hWreg : W.IsRankRegular := by
        dsimp [W]
        exact doubledBohrData_rankRegular hodd C.childTwo.bohr
          C.childTwo_rankRegular
      have hWcarrier :
          W.carrier = GroupCount.doubledFinset C.childTwo.carrier := by
        rw [C.childTwo_carrier]
        dsimp [W]
        exact
          (GroupCount.doubledFinset_bohrCarrier_eq_doubledBohrData
            hodd C.childTwo.bohr).symm
      have hWcard : W.carrier.card = C.childTwo.carrier.card := by
        dsimp [W]
        rw [GroupCount.card_doubledBohrData_carrier]
        exact congrArg Finset.card C.childTwo_carrier.symm
      have hWrank : W.rank = s.rank := by
        dsimp [W]
        rw [GroupCount.rank_doubledBohrData, C.rankTwo]
        rfl
      let H : SmoothingHierarchy W :=
        Classical.choice (exists_smoothingHierarchy W)
      have hkappa :
          (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ ≤
            1 / (100 * (max C.childOne.bohr.rank 1 : ℕ) : NNReal) := by
        rw [C.rankOne]
        simpa [mTwo, e, rankCost,
          FinalAssembly.RankRegularLocatedRestriction.rank,
          DensityStep.LocatedRestriction.rank,
          BohrStopping.RegularRestriction.rank] using
          (ConcreteNumerics.two_inv_mTwo_le_rank_scale hrankCost hsrank)
      have hwidth :
          2 * (((endpointSet s.located C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
              (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
                (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ))) +
            (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
              (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
                (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ)) ≤
            (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹ := by
        simpa [mTwo, e, rankCost] using
          (dyadic_boundary_width s.located C hdense hscale hsrank hrankCost)
      let cap : ℕ := rankCost + 1
      have hcap : cap ≤ 8 * RawSupplyNumerics.dyadicRankCost e := by
        dsimp [cap, rankCost]
        have hpos := RawSupplyNumerics.dyadicRankCost_pos e
        omega
      have htotalPos :
          0 < RawSupplyNumerics.dyadicTotalLossFormula e rankCap cap := by
        have hmOne' : 0 < ConcreteNumerics.mOne e
            (RawSupplyNumerics.dyadicRankCost e) :=
          ConcreteNumerics.mOne_pos (RawSupplyNumerics.dyadicRankCost_pos e)
        have hmTwo' : 0 < ConcreteNumerics.mTwo e
            (RawSupplyNumerics.dyadicRankCost e) :=
          ConcreteNumerics.mTwo_pos (RawSupplyNumerics.dyadicRankCost_pos e)
        have hq : 0 < RawSupplyNumerics.dyadicQQuant e := by
          unfold RawSupplyNumerics.dyadicQQuant
          exact RawSupplyNumerics.qQuant_pos
            (RawSupplyNumerics.dyadicSiftedAlpha_pos e)
        have htwo : 0 < RawSupplyNumerics.twoReciprocalLossFormula rankCap
            (ConcreteNumerics.mOne e (RawSupplyNumerics.dyadicRankCost e))
            (ConcreteNumerics.mTwo e (RawSupplyNumerics.dyadicRankCost e)) := by
          unfold RawSupplyNumerics.twoReciprocalLossFormula
          exact Nat.mul_pos
            (RawSupplyNumerics.reciprocalLossFormula_pos hmOne')
            (RawSupplyNumerics.reciprocalLossFormula_pos hmTwo')
        have hsmooth :
            0 < RawSupplyNumerics.smoothingHierarchyLossFormula rankCap := by
          unfold RawSupplyNumerics.smoothingHierarchyLossFormula
            RawSupplyNumerics.reciprocalLossFormula
          positivity
        have hsource :
            0 < (3 * RawSupplyNumerics.sourceDenominator rankCap cap
              (RawSupplyNumerics.dyadicHierarchyFormula e
                (ConcreteNumerics.rankCap e
                  (RawSupplyNumerics.dyadicRankCost e)))) ^ rankCap := by
          unfold RawSupplyNumerics.sourceDenominator
            RawSupplyNumerics.dyadicHierarchyFormula
          positivity
        have hcell : 0 < RawSupplyNumerics.dyadicCellMultiplier e := by
          unfold RawSupplyNumerics.dyadicCellMultiplier
            RawSupplyNumerics.cellMultiplier
          positivity
        unfold RawSupplyNumerics.dyadicTotalLossFormula
        exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos htwo hsmooth) hsource) hcell
      have htotalBudget :
          Real.exp (-halfCost) *
              (RawSupplyNumerics.dyadicTotalLossFormula e rankCap cap : ℝ) ≤
            1 := by
        apply exp_mul_loss_le_one_of_log_loss htotalPos
        simpa [halfCost, e] using
          (nextScale_total_log_le_halfSupply d rankCap cap (le_rfl) hcap)
      have hfiniteLe :
          (twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
              smoothingHierarchyLoss W) *
              (3 * dyadicSourceDenominator e rankCap) ^ rankCap *
              dyadicCardMultiplier e rankCap ≤
            RawSupplyNumerics.dyadicTotalLossFormula e rankCap cap := by
        have hbohrRank :
            s.located.restriction.bohr.rank ≤ rankCap := by
          simpa [FinalAssembly.RankRegularLocatedRestriction.rank,
            DensityStep.LocatedRestriction.rank,
            BohrStopping.RegularRestriction.rank] using hsrank
        have hreciprocal {m : ℕ} (hm : 0 < m) :
            reciprocalLoss s.located.restriction.bohr m ≤
              RawSupplyNumerics.reciprocalLossFormula rankCap m := by
          unfold reciprocalLoss RawSupplyNumerics.reciprocalLossFormula
          exact Nat.mul_le_mul
            (Nat.pow_le_pow_right (by omega) hbohrRank)
            (Nat.pow_le_pow_right (by norm_num) hbohrRank)
        have htwo :
            twoReciprocalLoss s.located.restriction.bohr mOne mTwo ≤
              RawSupplyNumerics.twoReciprocalLossFormula rankCap mOne mTwo := by
          unfold twoReciprocalLoss RawSupplyNumerics.twoReciprocalLossFormula
          exact Nat.mul_le_mul (hreciprocal hmOne) (hreciprocal hmTwo)
        have hmax : max s.rank 1 ≤ max rankCap 1 :=
          max_le_max_right 1 hsrank
        have hsmoothFactor (c : ℕ) (hc : 0 < c) :
            (3 * (c * max s.rank 1)) ^ s.rank * 4 ^ s.rank ≤
              RawSupplyNumerics.reciprocalLossFormula rankCap
                (c * max rankCap 1) := by
          unfold RawSupplyNumerics.reciprocalLossFormula
          have hbase :
              3 * (c * max s.rank 1) ≤ 3 * (c * max rankCap 1) := by
            gcongr
          have hbasePos : 0 < 3 * (c * max rankCap 1) := by positivity
          have hfirst :
              (3 * (c * max s.rank 1)) ^ s.rank ≤
                (3 * (c * max rankCap 1)) ^ rankCap := by
            calc
              (3 * (c * max s.rank 1)) ^ s.rank ≤
                  (3 * (c * max rankCap 1)) ^ s.rank :=
                Nat.pow_le_pow_left hbase _
              _ ≤ (3 * (c * max rankCap 1)) ^ rankCap :=
                Nat.pow_le_pow_right hbasePos hsrank
          exact Nat.mul_le_mul hfirst
            (Nat.pow_le_pow_right (by norm_num) hsrank)
        have hsmooth :
            smoothingHierarchyLoss W ≤
              RawSupplyNumerics.smoothingHierarchyLossFormula rankCap := by
          unfold smoothingHierarchyLoss
            RawSupplyNumerics.smoothingHierarchyLossFormula
          rw [hWrank]
          exact Nat.mul_le_mul
            (Nat.mul_le_mul (hsmoothFactor 1600 (by norm_num))
              (hsmoothFactor 200 (by norm_num)))
            (hsmoothFactor 200 (by norm_num))
        have hsource :
            (3 * dyadicSourceDenominator e rankCap) ^ rankCap =
              (3 * RawSupplyNumerics.sourceDenominator rankCap cap
                (RawSupplyNumerics.dyadicHierarchyFormula e
                  (ConcreteNumerics.rankCap e
                    (RawSupplyNumerics.dyadicRankCost e)))) ^ rankCap := by
          unfold dyadicSourceDenominator dyadicHierarchyDenominator
            RawSupplyNumerics.sourceDenominator
            RawSupplyNumerics.dyadicHierarchyFormula
            RawSupplyNumerics.dyadicAlphaExponent
          dsimp [rankCap, rankCost, cap]
        have hcell :
            dyadicCardMultiplier e rankCap =
              RawSupplyNumerics.dyadicCellMultiplier e := by
          unfold dyadicCardMultiplier dyadicCellCount
            RawSupplyNumerics.dyadicCellMultiplier
          rw [RawSupplyNumerics.ceil_eight_mul_rank_add_one_eq]
        unfold RawSupplyNumerics.dyadicTotalLossFormula
        rw [← hsource, ← hcell]
        dsimp [mOne, mTwo, rankCost]
        exact Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul htwo hsmooth) (le_rfl))
          (le_rfl)
      have hlocalBudget :
          Real.exp (-halfCost) *
              ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
                smoothingHierarchyLoss W : ℕ) : ℝ) *
              (((3 * dyadicSourceDenominator e rankCap) ^ rankCap : ℕ) : ℝ) *
                (dyadicCardMultiplier e rankCap : ℝ) ≤ 1 := by
        calc
          Real.exp (-halfCost) *
              ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
                smoothingHierarchyLoss W : ℕ) : ℝ) *
              (((3 * dyadicSourceDenominator e rankCap) ^ rankCap : ℕ) : ℝ) *
                (dyadicCardMultiplier e rankCap : ℝ) ≤
              Real.exp (-halfCost) *
                (RawSupplyNumerics.dyadicTotalLossFormula e rankCap cap : ℝ) := by
                  have hfiniteLeR :
                      ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
                        smoothingHierarchyLoss W) *
                        (3 * dyadicSourceDenominator e rankCap) ^ rankCap *
                        dyadicCardMultiplier e rankCap : ℝ) ≤
                        (RawSupplyNumerics.dyadicTotalLossFormula
                          e rankCap cap : ℝ) := by
                    exact_mod_cast hfiniteLe
                  push_cast at hfiniteLeR ⊢
                  calc
                    Real.exp (-halfCost) *
                        ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo : ℝ) *
                          smoothingHierarchyLoss W) *
                        (3 * dyadicSourceDenominator e rankCap : ℝ) ^ rankCap *
                          dyadicCardMultiplier e rankCap =
                        Real.exp (-halfCost) *
                          (((twoReciprocalLoss s.located.restriction.bohr mOne mTwo : ℝ) *
                            smoothingHierarchyLoss W) *
                            (3 * dyadicSourceDenominator e rankCap : ℝ) ^ rankCap *
                              dyadicCardMultiplier e rankCap) := by ring
                    _ ≤ Real.exp (-halfCost) *
                        (RawSupplyNumerics.dyadicTotalLossFormula e rankCap cap : ℝ) :=
                      mul_le_mul_of_nonneg_left hfiniteLeR (Real.exp_pos _).le
          _ ≤ 1 := htotalBudget
      simpa [p, e] using
        (finalRawTwoBohrEndpointPackage_of_dyadic_hierarchy
          (d := d) (rankCap := rankCap) (mOne := mOne) (mTwo := mTwo)
          s hmOne hmTwo C hnumHalf hfirst hdense hscale W hWreg
          hWcarrier hWcard hWrank H hsrank hkappa hwidth hlocalBudget)

/-- Scaling a raw two-Bohr bound into the ambient-normalized Holder bound. -/
theorem scaledBalanced_bound_of_raw
    {K W : BohrData G} {A : Finset G} {p : ℕ} (hp : 0 < p)
    {epsilon : ℝ}
    (hraw :
      BalancedRestriction.weightedLpNorm (normalizedIndicator W.carrier)
          (normalizedConvolution
            (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier)) p ≤
        epsilon * (K.carrier.card : ℝ)⁻¹) :
    BalancedRestriction.weightedLpNorm (normalizedIndicator W.carrier)
        (scaledBalanced K A) p ≤
      (Fintype.card G : ℝ) * (epsilon * (K.carrier.card : ℝ)⁻¹) := by
  let w : G → ℝ≥0 := μ W.carrier
  have hscale :=
    LocalizedUnbalancing.weightedLpNorm_smul_of_nonneg w
      (normalizedConvolution
        (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier))
      (Fintype.card G : ℝ) (by positivity) hp
  have hscale' :
      BalancedRestriction.weightedLpNorm (normalizedIndicator W.carrier)
          (scaledBalanced K A) p =
        (Fintype.card G : ℝ) *
          BalancedRestriction.weightedLpNorm (normalizedIndicator W.carrier)
            (normalizedConvolution
              (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier)) p := by
    simpa only [w, NNReal.coe_comp_mu,
      LocalizedUnbalancing.mu_eq_normalizedIndicator,
      scaledBalanced] using hscale
  rw [hscale']
  exact mul_le_mul_of_nonneg_left hraw (by positivity)

/-- The smallest honest two-Bohr endpoint API.

All fields are geometric or analytic estimates on actual objects.  In
particular, it does not contain a Holder certificate or an increment.  The
middle child and its doubled carrier are already present in
ReciprocalChildren; the weight equality below identifies that actual doubled
carrier with the regular Bohr datum used by TwoBohrBalanced. -/
structure RawTwoBohrEndpointPackage
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilon)
    (p : ℕ) where
  base : BohrData G
  weight : BohrData G
  base_regular : base.IsRankRegular
  weight_regular : weight.IsRankRegular
  base_carrier : base.carrier = C.childOne.carrier
  weight_carrier :
    weight.carrier = GroupCount.doubledFinset C.childTwo.carrier
  eta : ℝ≥0
  eta_pos : 0 < eta
  eta_narrow :
    4 * eta ≤ 1 / (400 * (max weight.rank 1 : ℕ) : ℝ≥0)
  D : Finset G
  E : Finset G
  D_nonempty : D.Nonempty
  E_nonempty : E.Nonempty
  D_small : D ⊆ (weight.dilate eta).carrier
  E_small : E ⊆ (weight.dilate eta).carrier
  kappa : ℝ≥0
  rank_width :
    kappa ≤ 1 / (100 * (max base.rank 1 : ℕ) : ℝ≥0)
  smoothing_support :
    ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (base.dilate kappa).carrier
  boundary_width :
    2 * (((endpointSet s C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
        (200 * ((max base.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
      (base.carrier.card : ℝ)⁻¹ *
        (200 * ((max base.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
      (1 / 8 : ℝ) / 8 * (base.carrier.card : ℝ)⁻¹
  density_power :
    (2 / 3 : ℝ) ^ p ≤ densePairDensity s epsilon
  approximation :
    |(GroupCount.normalizedMixedProgression
          (endpointSet s C.childOne C.childTwo hdense)
          (middleSet s C.childOne C.childTwo hdense) -
        (Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) -
        HolderLifting.pairing
          (scaledBalanced base (endpointSet s C.childOne C.childTwo hdense))
          (GroupCount.doubledFinset
            (middleSet s C.childOne C.childTwo hdense))| ≤
      ((Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) / 8

/-- If the high-norm branch is absent, TwoBohrBalanced supplies the raw
balanced estimate, which the plateau-free fibre constructor turns into an
actual Holder certificate.  This theorem makes the remaining high-norm
LocalAP bridge completely explicit. -/
noncomputable def holderCertificate_of_rawTwoBohr_stopping
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilon)
    {p : ℕ} (hp : 0 < p)
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    (Q : RawTwoBohrEndpointPackage s C hdense p)
    (hnohigh : ¬
      (1 + (1 / 8 : ℝ) / 8) * (Q.base.carrier.card : ℝ)⁻¹ ≤
        BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight Q.D Q.E)
          (μ_[ℝ] (endpointSet s C.childOne C.childTwo hdense) ○ᵈ
            μ (endpointSet s C.childOne C.childTwo hdense))
          (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p)) :
    GroupCount.HolderCountCertificate original := by
  have hendpoint_nonempty :
      (endpointSet s C.childOne C.childTwo hdense).Nonempty := by
    let alpha := densePairDensity s epsilon
    have halpha : 0 < alpha :=
      mul_pos (sub_pos.mpr hepsilon_lt_one) s.density_pos
    have hOne : alpha ≤
        localDensity s.restriction.set C.childOne.carrier
          (GroupCount.densePairPoint hdense) := by
      simpa [alpha, densePairDensity] using
        GroupCount.densePairPoint_density_one hdense
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos
      C.childOne.carrier_nonempty
    exact halpha.trans_le hOne
  have hendpoint_subset :
      endpointSet s C.childOne C.childTwo hdense ⊆ Q.base.carrier := by
    rw [Q.base_carrier]
    exact DensityStep.narrowingSet_subset_carrier
      (B := C.childOne.bohr) (rho := C.childOne.outer)
      (A := s.restriction.set) (C := C.childOne.carrier)
      (x := GroupCount.densePairPoint hdense) (fun _ hz ↦ hz)
  have hraw :=
    TwoBohrBalanced.balanced_of_two_bohr_concrete_stopping
      Q.base_regular Q.weight_regular hendpoint_nonempty hendpoint_subset
      Q.eta_pos Q.eta_narrow Q.D_nonempty Q.E_nonempty Q.D_small Q.E_small
      Q.rank_width Q.smoothing_support (by norm_num) (by norm_num)
      Q.boundary_width hp hnohigh
  have hscaled := scaledBalanced_bound_of_raw hp hraw
  have hbalanced :
      BalancedRestriction.weightedLpNorm
          (normalizedIndicator (GroupCount.doubledFinset C.childTwo.carrier))
          (scaledBalanced Q.base (endpointSet s C.childOne C.childTwo hdense)) p ≤
        ((Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) / 8 := by
    rw [Q.weight_carrier] at hscaled
    rw [Q.base_carrier] at hscaled
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  exact holderCountCertificateOfDensePair s C.childOne C.childTwo hdense
    hepsilon_nonneg hepsilon_lt_one hp
    (scaledBalanced Q.base (endpointSet s C.childOne C.childTwo hdense))
    Q.density_power Q.approximation hbalanced

end TwoBohr

#print axioms exists_rankRegular_child_inside_inv_dilate
#print axioms exists_reciprocalChildren
#print axioms densePair_or_controlledIncrement_of_reciprocalChildren
#print axioms card_budget_of_log_loss
#print axioms densePairDensity_power_of_dyadic
#print axioms rankRegularNarrowingPackage_of_reciprocalChildren
#print axioms highNorm_endpoint_increment_of_localizedPackage
#print axioms approximation_of_twoScaleDensePair
#print axioms exists_rawConcreteSupply

end

end Erdos140.ConcreteSupply
