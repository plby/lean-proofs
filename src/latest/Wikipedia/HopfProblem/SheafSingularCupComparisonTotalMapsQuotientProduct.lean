import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsQuotientBasic

/-!
# Actual cup preservation on the first and last quotient maps

The cochain product identities give literal identities on cocycles.
The actual quotient projections are surjective, so these identities
prove cup preservation for all original quotient classes.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

private theorem map_cup_of_representative_formulas
    {Z1 Z2 H1 H2 W1 W2 K1 K2 : Type*}
    (q1 : Z1 → H1) (q2 : Z2 → H2) (r1 : W1 → K1) (r2 : W2 → K2)
    (zcup : Z1 → Z1 → Z2) (wcup : W1 → W1 → W2)
    (hcup : H1 → H1 → H2) (kcup : K1 → K1 → K2)
    (zmap1 : Z1 → W1) (zmap2 : Z2 → W2)
    (hmap1 : H1 → K1) (hmap2 : H2 → K2)
    (hq : Function.Surjective q1)
    (hhcup : ∀ a b, hcup (q1 a) (q1 b) = q2 (zcup a b))
    (hkcup : ∀ a b, kcup (r1 a) (r1 b) = r2 (wcup a b))
    (hmap1_rep : ∀ a, hmap1 (q1 a) = r1 (zmap1 a))
    (hmap2_rep : ∀ a, hmap2 (q2 a) = r2 (zmap2 a))
    (hzmap : ∀ a b, zmap2 (zcup a b) = wcup (zmap1 a) (zmap1 b))
    (a b : H1) : hmap2 (hcup a b) = kcup (hmap1 a) (hmap1 b) := by
  obtain ⟨a, rfl⟩ := hq a
  obtain ⟨b, rfl⟩ := hq b
  rw [hhcup, hmap2_rep, hmap1_rep, hmap1_rep, hkcup, hzmap]

variable (X : TopCat.{0})

theorem firstCocycle_cup (a b : (constantData X).CocycleOne) :
    firstCocycleTwo X ((constantData X).cupCocycle a b) =
      (TotalSheaf.globalData X).cupCocycle (firstCocycleOne X a) (firstCocycleOne X b) := by
  apply Subtype.ext
  exact (firstCocycleTwo_val X ((constantData X).cupCocycle a b)).trans
    ((first_cupOne X a.val b.val).symm.trans
      (congrArg₂ (TotalSheaf.globalData X).cupOne
        (firstCocycleOne_val X a).symm (firstCocycleOne_val X b).symm))

theorem lastCocycle_cup (a b : (RingCochains.globalData X).CocycleOne) :
    lastCocycleTwo X ((RingCochains.globalData X).cupCocycle a b) =
      (TotalSheaf.globalData X).cupCocycle (lastCocycleOne X a) (lastCocycleOne X b) := by
  apply Subtype.ext
  exact (lastCocycleTwo_val X ((RingCochains.globalData X).cupCocycle a b)).trans
    ((last_cupOne X a.val b.val).symm.trans
      (congrArg₂ (TotalSheaf.globalData X).cupOne
        (lastCocycleOne_val X a).symm (lastCocycleOne_val X b).symm))

/-- The actual first-column quotient maps preserve the original cup products. -/
theorem firstH_cup (a b : (constantData X).CohomologyOne) :
    firstH2 X ((constantData X).cup a b) =
      (TotalSheaf.globalData X).cup (firstH1 X a) (firstH1 X b) :=
  map_cup_of_representative_formulas
    (constantData X).classOne (constantData X).classTwo
    (TotalSheaf.globalData X).classOne (TotalSheaf.globalData X).classTwo
    (constantData X).cupCocycle (TotalSheaf.globalData X).cupCocycle
    (fun a b => (constantData X).cup a b) (fun a b => (TotalSheaf.globalData X).cup a b)
    (firstCocycleOne X) (firstCocycleTwo X) (firstH1 X) (firstH2 X)
    (constantData X).classOne_surjective
    (constantData X).cup_classOne (TotalSheaf.globalData X).cup_classOne
    (firstH1_classOne X) (firstH2_classTwo X) (firstCocycle_cup X) a b

/-- The actual last-row quotient maps preserve the original cup products. -/
theorem lastH_cup (a b : (RingCochains.globalData X).CohomologyOne) :
    lastH2 X ((RingCochains.globalData X).cup a b) =
      (TotalSheaf.globalData X).cup (lastH1 X a) (lastH1 X b) :=
  map_cup_of_representative_formulas
    (RingCochains.globalData X).classOne (RingCochains.globalData X).classTwo
    (TotalSheaf.globalData X).classOne (TotalSheaf.globalData X).classTwo
    (RingCochains.globalData X).cupCocycle (TotalSheaf.globalData X).cupCocycle
    (fun a b => (RingCochains.globalData X).cup a b)
    (fun a b => (TotalSheaf.globalData X).cup a b)
    (lastCocycleOne X) (lastCocycleTwo X) (lastH1 X) (lastH2 X)
    (RingCochains.globalData X).classOne_surjective
    (RingCochains.globalData X).cup_classOne (TotalSheaf.globalData X).cup_classOne
    (lastH1_classOne X) (lastH2_classTwo X) (lastCocycle_cup X) a b

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
