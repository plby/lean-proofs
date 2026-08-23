import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412Connector
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMapLawReduced
import ErdosProblems.Erdos1166.Erdos1166HLOZPrimedOddRightWinner
import ErdosProblems.Erdos1166.Erdos1166HLOZTerminalParityWinner
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410Prop48Connector
import ErdosProblems.Erdos1166.Erdos1166HLOZConditionalCategoryProduct
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixAExactExit

/-!
Literal stopped-source constructors for the profile atoms used in the
Lemmas 4.11--4.12 connector.

The important point is negative: callers of these constructors do not supply
the stopped product map law.  That law is derived from the mixed stopped
reconstruction, block grouping, and the left/right winner shape identities.
The remaining record contains only the event identifications and the
conditional categorical estimates belonging to (4.47).
-/

namespace Erdos1166.HLOZProp47Lemma411412SourceAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open HLOZDecomposition HLOZActualStopped HLOZPrimedStopped
  HLOZIncompleteStoppedBlocks HLOZStoppedSourcePartition
  HLOZStoppedMixedReconstruction HLOZStoppedMapLaw
  HLOZStoppedMapLawReduced HLOZPrimedOddMixedReconstruction
  HLOZPrimedOddRightWinner HLOZProp48SourceBands HLOZProp48Truncated
  HLOZTerminalParityWinner
  HLOZEquation447
  HLOZProp47Lemma411412Connector
  HLOZLemma410Prop48Connector
  HLOZLemma411 HLOZLemma411Recursion HLOZLemma412Windows HLOZBandRatios
  HLOZProp47Parameters HLOZLemma410SourceBands
  HLOZProp45SourceInterval HLOZProp45SourceMirrors HLOZProp45SourceEndpoints
  HLOZConditionalCategoryProduct HLOZAppendixAExactExit

/-! ### Literal stopped-prefix cylinders for the full-walk path switch -/

/-- A finite union of genuine full-walk stopped prefixes, transported to walk
path space.  This is the literal type of the bad and artificial-`I₀`
witness families in (4.51)--(4.54).  The deleted nearest-neighbor path is
fixed inside each source fibre; the holding-coordinate switch changes the
full-walk prefix represented here. -/
noncomputable def stoppedPrefixPathEvent (E : Finset StoppedPrefix) :
    Set (ℕ → Site) :=
  simpleRandomWalk '' finiteStoppedPrefixEvent E

/-- A stopped-past path event with one prescribed first fresh direction.
This is the literal strong-Markov event used before (4.49). -/
noncomputable def sourceForcedDirectionPathEvent
    (tau : (ℕ → Direction) → ℕ) (base : Set (ℕ → Site))
    (d : Direction) : Set (ℕ → Site) :=
  simpleRandomWalk ''
    (simpleRandomWalk ⁻¹' base ∩
      incrementShiftAfter tau ⁻¹' {eta | eta 0 = d})

/-- The four possible first fresh directions cover the base event on the
support of the random-walk law.  The right side is written as an image of a
preimage because an arbitrary path outside that support need not be a simple
random-walk trajectory. -/
theorem iUnion_sourceForcedDirectionPathEvent
    (tau : (ℕ → Direction) → ℕ) (base : Set (ℕ → Site)) :
    (⋃ d : Direction, sourceForcedDirectionPathEvent tau base d) =
      simpleRandomWalk '' (simpleRandomWalk ⁻¹' base) := by
  ext s
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨d, omega, homega, rfl⟩
    exact ⟨omega, homega.1, rfl⟩
  · rintro ⟨omega, homega, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨(incrementShiftAfter tau omega) 0, omega, ⟨homega, ?_⟩, rfl⟩
    rfl

/-- The preceding cover is an equality of real probabilities.  No
measurability hypothesis on `base` is required: `MeasurableEmbedding.map_apply`
computes the pushforward measure on arbitrary sets. -/
theorem sourceForcedDirectionPathEvent_iUnion_measureReal
    (tau : (ℕ → Direction) → ℕ) (base : Set (ℕ → Site)) :
    simpleRandomWalkLaw.real base =
      simpleRandomWalkLaw.real
        (⋃ d : Direction, sourceForcedDirectionPathEvent tau base d) := by
  rw [iUnion_sourceForcedDirectionPathEvent]
  change (Measure.map simpleRandomWalk incrementLaw).real base =
    (Measure.map simpleRandomWalk incrementLaw).real
      (simpleRandomWalk '' (simpleRandomWalk ⁻¹' base))
  simp only [Measure.real,
    HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk.map_apply,
    HLOZSourceInstantiation.simpleRandomWalk_injective.preimage_image]

/-- A canonical first fresh direction whose forced event has maximal real
probability.  This replaces a source-level choice of direction. -/
noncomputable def sourceDominantForcedDirection
    (tau : (ℕ → Direction) → ℕ) (base : Set (ℕ → Site)) : Direction :=
  (Finset.univ.exists_max_image
    (fun d : Direction ↦ simpleRandomWalkLaw.real
      (sourceForcedDirectionPathEvent tau base d))
    Finset.univ_nonempty).choose

theorem sourceForcedDirectionPathEvent_measureReal_le_dominant
    (tau : (ℕ → Direction) → ℕ) (base : Set (ℕ → Site))
    (d : Direction) :
    simpleRandomWalkLaw.real (sourceForcedDirectionPathEvent tau base d) ≤
      simpleRandomWalkLaw.real (sourceForcedDirectionPathEvent tau base
        (sourceDominantForcedDirection tau base)) := by
  exact ((Finset.univ.exists_max_image
    (fun e : Direction ↦ simpleRandomWalkLaw.real
      (sourceForcedDirectionPathEvent tau base e))
    Finset.univ_nonempty).choose_spec).2 d (Finset.mem_univ d)

/-- Finite direction averaging gives the factor four used before (4.49).
The theorem applies directly to the post-`Theta` base event, so neither the
chosen direction nor its probability inequality is source data. -/
theorem sourceDominantForcedDirection_reduction
    (tau : (ℕ → Direction) → ℕ) (base : Set (ℕ → Site)) :
    simpleRandomWalkLaw.real base ≤
      4 * simpleRandomWalkLaw.real
        (sourceForcedDirectionPathEvent tau base
          (sourceDominantForcedDirection tau base)) := by
  rw [sourceForcedDirectionPathEvent_iUnion_measureReal]
  calc
    simpleRandomWalkLaw.real
        (⋃ d : Direction, sourceForcedDirectionPathEvent tau base d) ≤
        ∑ d : Direction, simpleRandomWalkLaw.real
          (sourceForcedDirectionPathEvent tau base d) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _d : Direction, simpleRandomWalkLaw.real
        (sourceForcedDirectionPathEvent tau base
          (sourceDominantForcedDirection tau base)) := by
      exact Finset.sum_le_sum fun d _hd ↦
        sourceForcedDirectionPathEvent_measureReal_le_dominant tau base d
    _ = 4 * simpleRandomWalkLaw.real
        (sourceForcedDirectionPathEvent tau base
          (sourceDominantForcedDirection tau base)) := by
      simp only [Fin.sum_univ_four]
      ring

theorem measurableSet_sourceForcedDirectionPathEvent
    (tau : (ℕ → Direction) → ℕ) (base : Set (ℕ → Site))
    (d : Direction) (htau : Measurable tau)
    (hbase : ∀ n, MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹' base ∩ {omega | tau omega = n})) :
    MeasurableSet (sourceForcedDirectionPathEvent tau base d) := by
  apply HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
    |>.measurableSet_image.2
  apply (measurableSet_pastEvent tau (simpleRandomWalk ⁻¹' base) hbase).inter
  exact (measurableSet_singleton d).preimage
    ((measurable_pi_apply 0).comp (measurable_incrementShiftAfter htau))

/-- Exact quarter factor for the prescribed first fresh direction.  The
source supplies only stopped-past measurability; the IID restart theorem
proves the numerical probability identity. -/
theorem sourceForcedDirectionPathEvent_measureReal
    (tau : (ℕ → Direction) → ℕ) (base : Set (ℕ → Site))
    (d : Direction) (htau : Measurable tau)
    (hbaseMeas : MeasurableSet base)
    (hbase : ∀ n, MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹' base ∩ {omega | tau omega = n})) :
    simpleRandomWalkLaw.real (sourceForcedDirectionPathEvent tau base d) =
      (1 / 4 : ℝ) * simpleRandomWalkLaw.real base := by
  let A : Set (ℕ → Direction) := simpleRandomWalk ⁻¹' base
  let B : Set (ℕ → Direction) := {eta | eta 0 = d}
  have hA : MeasurableSet A := measurableSet_pastEvent tau A hbase
  have hB : MeasurableSet B :=
    (measurableSet_singleton d).preimage (measurable_pi_apply 0)
  have hforce : simpleRandomWalkLaw
        (sourceForcedDirectionPathEvent tau base d) =
      incrementLaw (A ∩ incrementShiftAfter tau ⁻¹' B) := by
    rw [simpleRandomWalkLaw, Measure.map_apply measurable_simpleRandomWalk
      (measurableSet_sourceForcedDirectionPathEvent tau base d htau hbase)]
    congr 1
    exact HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk.injective
      |>.preimage_image _
  have hbaseMeasure : simpleRandomWalkLaw base = incrementLaw A := by
    rw [simpleRandomWalkLaw,
      Measure.map_apply measurable_simpleRandomWalk hbaseMeas]
  have hfactor := measure_inter_incrementShiftAfter_eq_mul
    tau A B htau hbase hB
  change (simpleRandomWalkLaw
      (sourceForcedDirectionPathEvent tau base d)).toReal =
    (1 / 4 : ℝ) * (simpleRandomWalkLaw base).toReal
  rw [hforce, hfactor, hbaseMeasure]
  rw [show incrementLaw B = (4 : ENNReal)⁻¹ by
    simpa only [B] using increment_direction_prob 0 d]
  simp [mul_comm]

theorem measurableSet_stoppedPrefixPathEvent (E : Finset StoppedPrefix) :
    MeasurableSet (stoppedPrefixPathEvent E) := by
  apply HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
    |>.measurableSet_image.2
  unfold finiteStoppedPrefixEvent
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro _hp
  exact measurableSet_stoppedPrefixAtom p

/-- Exact path-space mass of a finite stopped-prefix family. -/
theorem simpleRandomWalkLaw_stoppedPrefixPathEvent
    (m k : ℕ) (E : Finset StoppedPrefix)
    (hE : ∀ p ∈ E, IsFirstKStoppedPrefix m k p) :
    simpleRandomWalkLaw (stoppedPrefixPathEvent E) =
      ∑ p ∈ E, (4 : ℝ≥0∞)⁻¹ ^ p.1 := by
  rw [simpleRandomWalkLaw,
    Measure.map_apply measurable_simpleRandomWalk
      (measurableSet_stoppedPrefixPathEvent E)]
  have hpre : simpleRandomWalk ⁻¹' stoppedPrefixPathEvent E =
      finiteStoppedPrefixEvent E := by
    unfold stoppedPrefixPathEvent
    exact HLOZSourceInstantiation.simpleRandomWalk_injective.preimage_image _
  rw [hpre]
  exact finiteStoppedPrefixEvent_prob m k E hE

/-- Two disjoint finite families of first-`k` stopped prefixes give disjoint
walk-path cylinders.  The proof uses the genuine stopped-time prefix-code
property, not an assumed path-event disjointness statement. -/
theorem stoppedPrefixPathEvent_disjoint
    (m k : ℕ) (E F : Finset StoppedPrefix)
    (hE : ∀ p ∈ E, IsFirstKStoppedPrefix m k p)
    (hF : ∀ p ∈ F, IsFirstKStoppedPrefix m k p)
    (hEF : Disjoint (↑E : Set StoppedPrefix) (↑F : Set StoppedPrefix)) :
    Disjoint (stoppedPrefixPathEvent E) (stoppedPrefixPathEvent F) := by
  rw [Set.disjoint_left]
  intro path hpathE hpathF
  rcases hpathE with ⟨omega, homegaE, rfl⟩
  rcases hpathF with ⟨eta, hetaF, hwalk⟩
  have heta : eta = omega :=
    HLOZSourceInstantiation.simpleRandomWalk_injective hwalk
  subst eta
  unfold finiteStoppedPrefixEvent at homegaE hetaF
  rcases Set.mem_iUnion.mp homegaE with ⟨p, hpE⟩
  rcases Set.mem_iUnion.mp hpE with ⟨hp, homegaP⟩
  rcases Set.mem_iUnion.mp hetaF with ⟨q, hqF⟩
  rcases Set.mem_iUnion.mp hqF with ⟨hq, homegaQ⟩
  by_cases hpq : p = q
  · subst q
    exact Set.disjoint_left.mp hEF hp hq
  · exact Set.disjoint_left.mp
      (stoppedPrefixAtom_pairwiseDisjoint_on_firstK m k
        (hE p hp) (hF q hq) hpq) homegaP homegaQ

/-- Literal finite-cylinder data for one global full-walk path branch.

The only numerical source field is the comparison of the two explicit sums
of prefix weights `4^{-length}`.  All set-level path probabilities,
measurability, and full-path disjointness are derived by Lean.

The bad cylinders stop when the original `k`-th level-`m` site is created.
The artificial-`I₀` witness in (4.53) generally has additional sites at
level `m`, so for each exact count `q` it is a
first-`witnessStoppingCount q` prefix rather than a first-`k` prefix.
Keeping these two stopping counts separate is essential to the source's
disjointness argument (4.54). -/
structure Equation447StoppedPrefixChangedPathBranchData
    (m k : ℕ) (c : ℝ)
    (failure thetaPathEvent : Set (ℕ → Site)) (rho : ℝ) where
  Code : Type
  [codeCountable : Countable Code]
  forcedGoodEvent : Set (ℕ → Site)
  badByCount : ℕ → Set (ℕ → Site)
  badPrefixes : ℕ → Code → Finset StoppedPrefix
  witnessPrefixes : ℕ → Code → Finset StoppedPrefix
  forced_reduction :
    simpleRandomWalkLaw.real (failure \ thetaPathEvent) ≤
      4 * simpleRandomWalkLaw.real forcedGoodEvent
  forced_count_cover :
    forcedGoodEvent ⊆ ⋃ t : ℕ, badByCount (Nat.ceil rho + t)
  count_path_cover : ∀ q,
    badByCount q ⊆ ⋃ eta, stoppedPrefixPathEvent (badPrefixes q eta)
  witnessStoppingCount : ℕ → ℕ
  bad_firstK : ∀ q eta p, p ∈ badPrefixes q eta →
    IsFirstKStoppedPrefix m k p
  witness_firstK : ∀ q eta p, p ∈ witnessPrefixes q eta →
    IsFirstKStoppedPrefix m (witnessStoppingCount q) p
  witness_prefix_disjoint : ∀ q eta zeta, eta ≠ zeta →
    Disjoint (↑(witnessPrefixes q eta) : Set StoppedPrefix)
      (↑(witnessPrefixes q zeta) : Set StoppedPrefix)
  prefix_weight_switch : ∀ q eta, Nat.ceil rho ≤ q →
    (∑ p ∈ badPrefixes q eta, (4 : ℝ≥0∞)⁻¹ ^ p.1) ≤
      ENNReal.ofReal (Real.exp (-c * (q : ℝ))) *
        ∑ p ∈ witnessPrefixes q eta, (4 : ℝ≥0∞)⁻¹ ^ p.1

namespace Equation447StoppedPrefixChangedPathBranchData

/-- Convert literal stopped-prefix cylinders into the global path-switch
package consumed by the source-faithful Equation-(4.47) connector. -/
noncomputable def toChangedPathBranch
    {m k : ℕ} {c rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixChangedPathBranchData
      m k c failure thetaPathEvent rho) :
    StoppedEquation447ChangedPathBranch c failure thetaPathEvent rho where
  Code := R.Code
  codeCountable := R.codeCountable
  forcedGoodEvent := R.forcedGoodEvent
  badByCount := R.badByCount
  badPathAtom := fun q eta ↦ stoppedPrefixPathEvent (R.badPrefixes q eta)
  witnessPathAtom := fun q eta ↦
    stoppedPrefixPathEvent (R.witnessPrefixes q eta)
  forced_reduction := R.forced_reduction
  forced_count_cover := R.forced_count_cover
  count_path_cover := R.count_path_cover
  path_switch := by
    intro q eta hq
    rw [simpleRandomWalkLaw_stoppedPrefixPathEvent m k
        (R.badPrefixes q eta) (R.bad_firstK q eta),
      simpleRandomWalkLaw_stoppedPrefixPathEvent m (R.witnessStoppingCount q)
        (R.witnessPrefixes q eta) (R.witness_firstK q eta)]
    exact R.prefix_weight_switch q eta hq
  witness_disjoint := by
    intro q eta zeta hne
    exact stoppedPrefixPathEvent_disjoint m (R.witnessStoppingCount q)
      (R.witnessPrefixes q eta) (R.witnessPrefixes q zeta)
      (R.witness_firstK q eta) (R.witness_firstK q zeta)
      (R.witness_prefix_disjoint q eta zeta hne)
  witness_measurable := by
    intro q eta
    exact measurableSet_stoppedPrefixPathEvent (R.witnessPrefixes q eta)

end Equation447StoppedPrefixChangedPathBranchData

/-! ### Categorical factorization of the literal stopped-prefix weights -/

/-- Source data for the literal stopped-prefix switch before the elementary
binomial-layer estimate is applied.

For fixed exact count `q` and deleted-path code `eta`, the source identifies
the total weight of the all-upper stopped prefixes and of the artificial
`I₀` witness prefixes with two cells of the same finite categorical product,
multiplied by one common history normalizer.  The only comparison retained at
the coordinate level is the one-coordinate upper/lower mass ratio.  Lean then
chooses the optimal witness layer and proves its exponential advantage; no
aggregate inequality between the two prefix sums is assumed. -/
structure Equation447StoppedPrefixOptimalCategoricalBranchData
    (m k : ℕ) (ratioC : ℝ)
    (failure thetaPathEvent : Set (ℕ → Site)) (rho : ℝ) where
  Code : Type
  [codeCountable : Countable Code]
  forcedGoodEvent : Set (ℕ → Site)
  badByCount : ℕ → Set (ℕ → Site)
  badPrefixes : ℕ → Code → Finset StoppedPrefix
  witnessPrefixes : ℕ → Code → Finset StoppedPrefix
  forced_reduction :
    simpleRandomWalkLaw.real (failure \ thetaPathEvent) ≤
      4 * simpleRandomWalkLaw.real forcedGoodEvent
  forced_count_cover :
    forcedGoodEvent ⊆ ⋃ t : ℕ, badByCount (Nat.ceil rho + t)
  count_path_cover : ∀ q,
    badByCount q ⊆ ⋃ eta, stoppedPrefixPathEvent (badPrefixes q eta)
  witnessStoppingCount : ℕ → ℕ
  bad_firstK : ∀ q eta p, p ∈ badPrefixes q eta →
    IsFirstKStoppedPrefix m k p
  witness_firstK : ∀ q eta p, p ∈ witnessPrefixes q eta →
    IsFirstKStoppedPrefix m (witnessStoppingCount q) p
  witness_prefix_disjoint : ∀ q eta zeta, eta ≠ zeta →
    Disjoint (↑(witnessPrefixes q eta) : Set StoppedPrefix)
      (↑(witnessPrefixes q zeta) : Set StoppedPrefix)
  normalizer : ℕ → Code → ENNReal
  categoryLaw : ∀ q, Code → Fin q → ProbabilityMeasure (Fin 3)
  bad_weight_eq : ∀ q eta,
    (∑ p ∈ badPrefixes q eta, (4 : ℝ≥0∞)⁻¹ ^ p.1) =
      normalizer q eta *
        Measure.pi (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
          {allUpperConfig}
  witness_weight_eq : ∀ q eta,
    (∑ p ∈ witnessPrefixes q eta, (4 : ℝ≥0∞)⁻¹ ^ p.1) =
      normalizer q eta *
        Measure.pi (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
          (↑(categoricalWitnessLayer (ι := Fin q)
            (categoricalOptimalWitnessCount ratioC q)) :
            Set (Fin q → Fin 3))
  category_mass_ratio : ∀ q eta x,
    ((categoryLaw q eta x : Measure (Fin 3))).real {0} ≤
      ratioC * ((categoryLaw q eta x : Measure (Fin 3))).real {1}

namespace Equation447StoppedPrefixOptimalCategoricalBranchData

/-- Convert the source's common-normalizer categorical identities into the
literal stopped-prefix comparison.  The sole numerical argument is the
optimal-layer inequality, which is supplied uniformly and eventually below. -/
noncomputable def toStoppedPrefixChangedPathBranchData
    {m k : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixOptimalCategoricalBranchData
      m k ratioC failure thetaPathEvent rho)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q, Nat.ceil rho ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    Equation447StoppedPrefixChangedPathBranchData m k
      (categoricalOptimalRate ratioC) failure thetaPathEvent rho where
  Code := R.Code
  codeCountable := R.codeCountable
  forcedGoodEvent := R.forcedGoodEvent
  badByCount := R.badByCount
  badPrefixes := R.badPrefixes
  witnessPrefixes := R.witnessPrefixes
  forced_reduction := R.forced_reduction
  forced_count_cover := R.forced_count_cover
  count_path_cover := R.count_path_cover
  witnessStoppingCount := R.witnessStoppingCount
  bad_firstK := R.bad_firstK
  witness_firstK := R.witness_firstK
  witness_prefix_disjoint := R.witness_prefix_disjoint
  prefix_weight_switch := by
    intro q eta hq
    let nu : Fin q → Measure (Fin 3) :=
      fun x ↦ (R.categoryLaw q eta x : Measure (Fin 3))
    letI (x : Fin q) : IsProbabilityMeasure (nu x) :=
      (R.categoryLaw q eta x).prop
    let factor : ℝ :=
      Real.exp (-categoricalOptimalRate ratioC * (q : ℝ))
    have hcat : Measure.pi nu {allUpperConfig} ≤
        ENNReal.ofReal factor * Measure.pi nu
          (↑(categoricalWitnessLayer (ι := Fin q)
            (categoricalOptimalWitnessCount ratioC q)) :
            Set (Fin q → Fin 3)) := by
      exact categorical_allUpper_ennreal_le_factor_mul_concreteWitnessLayer
        nu ratioC factor hC.le (Real.exp_nonneg _)
        (R.category_mass_ratio q eta)
        (categoricalOptimalWitnessCount ratioC q)
        (by simpa only [Fintype.card_fin] using
          categoricalOptimalWitnessCount_le ratioC q)
        (by simpa only [Fintype.card_fin] using hbinomial q hq)
    calc
      (∑ p ∈ R.badPrefixes q eta, (4 : ℝ≥0∞)⁻¹ ^ p.1) =
          R.normalizer q eta * Measure.pi nu {allUpperConfig} := by
            simpa only [nu] using R.bad_weight_eq q eta
      _ ≤ R.normalizer q eta *
          (ENNReal.ofReal factor * Measure.pi nu
            (↑(categoricalWitnessLayer (ι := Fin q)
              (categoricalOptimalWitnessCount ratioC q)) :
              Set (Fin q → Fin 3))) := by
            gcongr
      _ = ENNReal.ofReal factor *
          (R.normalizer q eta * Measure.pi nu
            (↑(categoricalWitnessLayer (ι := Fin q)
              (categoricalOptimalWitnessCount ratioC q)) :
              Set (Fin q → Fin 3))) := by
            ac_rfl
      _ = ENNReal.ofReal factor *
          ∑ p ∈ R.witnessPrefixes q eta, (4 : ℝ≥0∞)⁻¹ ^ p.1 := by
            rw [R.witness_weight_eq q eta]
      _ = ENNReal.ofReal
          (Real.exp (-categoricalOptimalRate ratioC * (q : ℝ))) *
          ∑ p ∈ R.witnessPrefixes q eta, (4 : ℝ≥0∞)⁻¹ ^ p.1 := by
            rfl

end Equation447StoppedPrefixOptimalCategoricalBranchData

/-! ### Finite encoding of the categorical prefix fibres -/

/-- Summing a pointwise stopped-prefix factorization through a finite
equivalence gives the common-background factorization of the whole prefix
family. -/
theorem stoppedPrefixWeight_sum_eq_background_sum_mul_of_equiv
    {B : Type} [Fintype B]
    (prefixes : Finset StoppedPrefix)
    (E : {p // p ∈ prefixes} ≃ B)
    (backgroundWeight : B → ENNReal)
    (cell : ENNReal)
    (hweight : ∀ p : {p // p ∈ prefixes},
      (4 : ENNReal)⁻¹ ^ Sigma.fst p.val =
        backgroundWeight (E p) * cell) :
    (∑ p ∈ prefixes, (4 : ENNReal)⁻¹ ^ p.1) =
      (∑ b, backgroundWeight b) * cell := by
  rw [← Finset.sum_attach]
  calc
    (∑ p : {p // p ∈ prefixes},
        (4 : ENNReal)⁻¹ ^ Sigma.fst p.val) =
        ∑ p : {p // p ∈ prefixes},
          backgroundWeight (E p) * cell := by
            apply Fintype.sum_congr
            exact hweight
    _ = ∑ b : B, backgroundWeight b * cell :=
      Equiv.sum_comp E (fun b ↦ backgroundWeight b * cell)
    _ = (∑ b, backgroundWeight b) * cell := by
      rw [Finset.sum_mul]

/-- If witness prefixes are in bijection with a common background and a
finite categorical layer, their total prefix weight is the background sum
times the product-law mass of that layer. -/
theorem stoppedPrefixWeight_sum_eq_background_sum_mul_pi_finset_of_equiv
    {B ι : Type} [Fintype B] [Fintype ι]
    (prefixes : Finset StoppedPrefix)
    (W : Finset (ι → Fin 3))
    (E : {p // p ∈ prefixes} ≃ B × {z // z ∈ W})
    (backgroundWeight : B → ENNReal)
    (nu : ι → Measure (Fin 3)) [∀ x, IsProbabilityMeasure (nu x)]
    (hweight : ∀ p : {p // p ∈ prefixes},
      (4 : ENNReal)⁻¹ ^ Sigma.fst p.val =
        backgroundWeight (E p).1 * Measure.pi nu {((E p).2.1)}) :
    (∑ p ∈ prefixes, (4 : ENNReal)⁻¹ ^ p.1) =
      (∑ b, backgroundWeight b) * Measure.pi nu (↑W : Set (ι → Fin 3)) := by
  rw [← Finset.sum_attach]
  calc
    (∑ p : {p // p ∈ prefixes},
        (4 : ENNReal)⁻¹ ^ Sigma.fst p.val) =
        ∑ p : {p // p ∈ prefixes},
          backgroundWeight (E p).1 * Measure.pi nu {((E p).2.1)} := by
            apply Fintype.sum_congr
            exact hweight
    _ = ∑ x : B × {z // z ∈ W},
          backgroundWeight x.1 * Measure.pi nu {x.2.1} :=
      Equiv.sum_comp E
        (fun x ↦ backgroundWeight x.1 * Measure.pi nu {x.2.1})
    _ = (∑ b, backgroundWeight b) *
        ∑ z : {z // z ∈ W}, Measure.pi nu {z.1} := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = (∑ b, backgroundWeight b) *
        ∑ z ∈ W, Measure.pi nu {z} := by
      congr 1
      exact Finset.sum_attach W (fun z ↦ Measure.pi nu {z})
    _ = (∑ b, backgroundWeight b) *
        Measure.pi nu (↑W : Set (ι → Fin 3)) := by
      rw [sum_measure_singleton]

/-! The literal source need not choose a common background weight.  It is
recovered from the bad-prefix weight by dividing by the all-upper cell.  The
two elementary cancellation lemmas below isolate the only `ENNReal`
bookkeeping needed for that normalization. -/

theorem ennreal_background_factorization
    (wbad p0 : ENNReal) (hp0 : p0 ≠ 0) (hp0top : p0 ≠ ∞) :
    wbad = (wbad / p0) * p0 := by
  exact (ENNReal.div_mul_cancel hp0 hp0top).symm

theorem ennreal_witness_factorization_of_relative_weight
    (wbad wwit p0 pz : ENNReal)
    (hp0 : p0 ≠ 0) (hp0top : p0 ≠ ∞)
    (hrelative : wwit * p0 = wbad * pz) :
    wwit = (wbad / p0) * pz := by
  calc
    wwit = (wbad * pz) / p0 :=
      (ENNReal.eq_div_iff hp0 hp0top).2
        (by simpa [mul_comm] using hrelative)
    _ = (wbad / p0) * pz := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Coordinatewise positivity of the upper category makes the finite
all-upper product cell nonzero.  Thus the source-facing record need not
postulate nonvanishing of an already-assembled categorical product. -/
theorem probabilityMeasure_pi_allUpper_ne_zero
    {ι : Type*} [Fintype ι]
    (nu : ι → ProbabilityMeasure (Fin 3))
    (hupper : ∀ x, (nu x : Measure (Fin 3)) {0} ≠ 0) :
    Measure.pi (fun x ↦ (nu x : Measure (Fin 3))) {allUpperConfig} ≠ 0 := by
  letI (x : ι) : IsProbabilityMeasure (nu x : Measure (Fin 3)) :=
    (nu x).prop
  rw [Measure.pi_singleton]
  apply Finset.prod_ne_zero_iff.mpr
  intro x _hx
  simpa only [allUpperConfig] using hupper x

/-- A literal finite encoding of the source's categorical stopped-prefix
switch.

For fixed count and deleted-path code, each bad prefix is itself the retained
background history, while a witness prefix is equivalent to a bad prefix
together with one configuration in the canonical witness layer.  The fields
`bad_prefix_weight` and `witness_prefix_weight` are pointwise
factorizations.  Consequently neither aggregate categorical weight identity
is a source premise. -/
structure Equation447StoppedPrefixCategoricalEncodingBranchData
    (m k : ℕ) (ratioC : ℝ)
    (failure thetaPathEvent : Set (ℕ → Site)) (rho : ℝ) where
  Code : Type
  [codeCountable : Countable Code]
  forcedGoodEvent : Set (ℕ → Site)
  badByCount : ℕ → Set (ℕ → Site)
  badPrefixes : ℕ → Code → Finset StoppedPrefix
  witnessPrefixes : ℕ → Code → Finset StoppedPrefix
  forced_reduction :
    simpleRandomWalkLaw.real (failure \ thetaPathEvent) ≤
      4 * simpleRandomWalkLaw.real forcedGoodEvent
  forced_count_cover :
    forcedGoodEvent ⊆ ⋃ t : ℕ, badByCount (Nat.ceil rho + t)
  count_path_cover : ∀ q,
    badByCount q ⊆ ⋃ eta, stoppedPrefixPathEvent (badPrefixes q eta)
  witnessStoppingCount : ℕ → ℕ
  bad_firstK : ∀ q eta p, p ∈ badPrefixes q eta →
    IsFirstKStoppedPrefix m k p
  witness_firstK : ∀ q eta p, p ∈ witnessPrefixes q eta →
    IsFirstKStoppedPrefix m (witnessStoppingCount q) p
  witness_prefix_disjoint : ∀ q eta zeta, eta ≠ zeta →
    Disjoint (↑(witnessPrefixes q eta) : Set StoppedPrefix)
      (↑(witnessPrefixes q zeta) : Set StoppedPrefix)
  backgroundWeight : ∀ q eta,
    {p // p ∈ badPrefixes q eta} → ENNReal
  categoryLaw : ∀ q, Code → Fin q → ProbabilityMeasure (Fin 3)
  witnessEquiv : ∀ q eta,
    {p // p ∈ witnessPrefixes q eta} ≃
      {p // p ∈ badPrefixes q eta} ×
        {z // z ∈ categoricalWitnessLayer (ι := Fin q)
          (categoricalOptimalWitnessCount ratioC q)}
  bad_prefix_weight : ∀ q eta p,
    (4 : ENNReal)⁻¹ ^ Sigma.fst p.val =
      backgroundWeight q eta p *
        Measure.pi
          (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
          {allUpperConfig}
  witness_prefix_weight : ∀ q eta p,
    (4 : ENNReal)⁻¹ ^ Sigma.fst p.val =
      backgroundWeight q eta (witnessEquiv q eta p).1 *
        Measure.pi
          (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
          {((witnessEquiv q eta p).2.1)}
  category_mass_ratio : ∀ q eta x,
    ((categoryLaw q eta x : Measure (Fin 3))).real {0} ≤
      ratioC * ((categoryLaw q eta x : Measure (Fin 3))).real {1}

/-- The stopped-prefix categorical encoding for the canonically dominant
prescribed direction.  The auxiliary `Theta` event may depend on the first
fresh step, so the exact stopped-past IID quarter identity need not apply to
the theta-free branch.  Instead, the finite direction cover and maximality
theorem above prove the required factor-four reduction for that arbitrary
post-`Theta` event.  The source therefore supplies neither a direction nor a
probability inequality.  The deleted-path fibre label is fixed to `ℕ`, so the
source also supplies neither an auxiliary code type nor its countability
instance.  Witness separation is required only as pairwise disjointness of the
finite prefix families at each fixed count; there is no global witness-label
function and hence no unnecessary coherence across different counts.  The
source otherwise only covers the resulting canonical directional event by
literal stopped-prefix cylinders and gives the natural-indexed fibre data.
The witness stopping count is not additional source data: a categorical
configuration with `t` artificial-lower coordinates creates exactly `k + t`
level-`m` sites, so the canonical witness layer stops at
`k + categoricalOptimalWitnessCount ratioC q`.
It does not choose a background weight or give two absolute pointwise
factorizations.  On a nonempty bad fibre it only proves that every
one-coordinate upper cell is nonzero and gives the cross-multiplied relative
weight identity for each matched witness prefix.  Lean proves nonvanishing of
the all-upper product, divides by that mass to construct the common background
normalization, and recovers both factorizations.  Witness families, their
bad-times-layer equivalences, categorical laws, and likelihood comparisons
are supplied only on nonempty bad fibres.  Lean fills an empty fibre with the
empty witness family, its unique empty equivalence, and the inactive Dirac
category. -/
structure Equation447StoppedPrefixCategoricalForcedDirectionBranchData
    (m k : ℕ) (ratioC : ℝ)
    (failure thetaPathEvent : Set (ℕ → Site)) (rho : ℝ) where
  badPrefixes : ℕ → ℕ → Finset StoppedPrefix
  witnessPrefixes : ∀ q eta,
    (badPrefixes q eta).Nonempty → Finset StoppedPrefix
  forced_prefix_cover :
    sourceForcedDirectionPathEvent (stoppedCreationTime m k)
        (failure \ thetaPathEvent)
        (sourceDominantForcedDirection (stoppedCreationTime m k)
          (failure \ thetaPathEvent)) ⊆
      ⋃ t : ℕ, ⋃ eta,
        stoppedPrefixPathEvent (badPrefixes (Nat.ceil rho + t) eta)
  bad_firstK : ∀ q eta p, p ∈ badPrefixes q eta →
    IsFirstKStoppedPrefix m k p
  witness_firstK : ∀ q eta
      (hbad : (badPrefixes q eta).Nonempty) p,
    p ∈ witnessPrefixes q eta hbad →
    IsFirstKStoppedPrefix m
      (k + categoricalOptimalWitnessCount ratioC q) p
  witness_prefix_disjoint : ∀ q eta zeta
      (hEta : (badPrefixes q eta).Nonempty)
      (hZeta : (badPrefixes q zeta).Nonempty), eta ≠ zeta →
    Disjoint (↑(witnessPrefixes q eta hEta) : Set StoppedPrefix)
      (↑(witnessPrefixes q zeta hZeta) : Set StoppedPrefix)
  categoryLaw : ∀ q eta,
    (badPrefixes q eta).Nonempty → Fin q → ProbabilityMeasure (Fin 3)
  witnessEquiv : ∀ q eta (hbad : (badPrefixes q eta).Nonempty),
    {p // p ∈ witnessPrefixes q eta hbad} ≃
      {p // p ∈ badPrefixes q eta} ×
        {z // z ∈ categoricalWitnessLayer (ι := Fin q)
          (categoricalOptimalWitnessCount ratioC q)}
  category_upper_ne_zero : ∀ q eta
      (hbad : (badPrefixes q eta).Nonempty) x,
    (categoryLaw q eta hbad x : Measure (Fin 3)) {0} ≠ 0
  witness_bad_relative_weight : ∀ q eta
      (hbad : (badPrefixes q eta).Nonempty)
      (p : {p // p ∈ witnessPrefixes q eta hbad}),
    let pbad := (witnessEquiv q eta hbad p).1
    (4 : ENNReal)⁻¹ ^ Sigma.fst p.val *
          Measure.pi
            (fun x ↦ (categoryLaw q eta hbad x : Measure (Fin 3)))
            {allUpperConfig} =
      (4 : ENNReal)⁻¹ ^ Sigma.fst pbad.val *
          Measure.pi
            (fun x ↦ (categoryLaw q eta hbad x : Measure (Fin 3)))
            {((witnessEquiv q eta hbad p).2.1)}
  category_mass_ratio : ∀ q eta
      (hbad : (badPrefixes q eta).Nonempty) x,
    ((categoryLaw q eta hbad x : Measure (Fin 3))).real {0} ≤
      ratioC * ((categoryLaw q eta hbad x : Measure (Fin 3))).real {1}

namespace Equation447StoppedPrefixCategoricalForcedDirectionBranchData

/-- Total witness-prefix family used by the generic connector.  An empty bad
fibre has no contribution and is assigned the empty witness family. -/
noncomputable def totalWitnessPrefixes
    {m k : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixCategoricalForcedDirectionBranchData
      m k ratioC failure thetaPathEvent rho)
    (q eta : ℕ) : Finset StoppedPrefix :=
  if hbad : (R.badPrefixes q eta).Nonempty then
    R.witnessPrefixes q eta hbad
  else ∅

@[simp] theorem totalWitnessPrefixes_of_nonempty
    {m k : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixCategoricalForcedDirectionBranchData
      m k ratioC failure thetaPathEvent rho)
    (q eta : ℕ) (hbad : (R.badPrefixes q eta).Nonempty) :
    R.totalWitnessPrefixes q eta = R.witnessPrefixes q eta hbad := by
  simp [totalWitnessPrefixes, hbad]

/-- Canonical transport from the total witness subtype to the active source
subtype on a nonempty bad fibre. -/
noncomputable def totalWitnessPrefixesEquivOfNonempty
    {m k : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixCategoricalForcedDirectionBranchData
      m k ratioC failure thetaPathEvent rho)
    (q eta : ℕ) (hbad : (R.badPrefixes q eta).Nonempty) :
    {p // p ∈ R.totalWitnessPrefixes q eta} ≃
      {p // p ∈ R.witnessPrefixes q eta hbad} where
  toFun p := ⟨p.1, by
    simpa only [totalWitnessPrefixes_of_nonempty R q eta hbad] using p.2⟩
  invFun p := ⟨p.1, by
    simpa only [totalWitnessPrefixes_of_nonempty R q eta hbad] using p.2⟩
  left_inv p := Subtype.ext rfl
  right_inv p := Subtype.ext rfl

/-- The active source equivalence, extended canonically across empty bad
fibres. -/
noncomputable def totalWitnessEquiv
    {m k : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixCategoricalForcedDirectionBranchData
      m k ratioC failure thetaPathEvent rho)
    (q eta : ℕ) :
    {p // p ∈ R.totalWitnessPrefixes q eta} ≃
      {p // p ∈ R.badPrefixes q eta} ×
        {z // z ∈ categoricalWitnessLayer (ι := Fin q)
          (categoricalOptimalWitnessCount ratioC q)} := by
  by_cases hbad : (R.badPrefixes q eta).Nonempty
  · exact (R.totalWitnessPrefixesEquivOfNonempty q eta hbad).trans
      (R.witnessEquiv q eta hbad)
  · letI : IsEmpty {p // p ∈ R.totalWitnessPrefixes q eta} :=
      ⟨fun p ↦ by simpa [totalWitnessPrefixes, hbad] using p.2⟩
    letI : IsEmpty {p // p ∈ R.badPrefixes q eta} :=
      ⟨fun p ↦ hbad ⟨p.1, p.2⟩⟩
    exact Equiv.equivOfIsEmpty _ _

/-- On a nonempty bad fibre, the total equivalence evaluates through the
source equivalence after the canonical subtype transport. -/
@[simp] theorem totalWitnessEquiv_apply_of_nonempty
    {m k : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixCategoricalForcedDirectionBranchData
      m k ratioC failure thetaPathEvent rho)
    (q eta : ℕ) (hbad : (R.badPrefixes q eta).Nonempty)
    (p : {p // p ∈ R.totalWitnessPrefixes q eta}) :
    R.totalWitnessEquiv q eta p =
      R.witnessEquiv q eta hbad
        ⟨p.1, by
          simpa only [totalWitnessPrefixes_of_nonempty R q eta hbad] using
            p.2⟩ := by
  simp [totalWitnessEquiv, hbad, totalWitnessPrefixesEquivOfNonempty]

/-- Total categorical law used by the generic connector.  Empty bad fibres
are mathematically inactive and receive the fallback category `2`. -/
noncomputable def totalCategoryLaw
    {m k : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixCategoricalForcedDirectionBranchData
      m k ratioC failure thetaPathEvent rho)
    (q eta : ℕ) (x : Fin q) : ProbabilityMeasure (Fin 3) :=
  if hbad : (R.badPrefixes q eta).Nonempty then
    R.categoryLaw q eta hbad x
  else
    ⟨Measure.dirac 2, Measure.dirac.isProbabilityMeasure⟩

@[simp] theorem totalCategoryLaw_of_nonempty
    {m k : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixCategoricalForcedDirectionBranchData
      m k ratioC failure thetaPathEvent rho)
    (q eta : ℕ) (hbad : (R.badPrefixes q eta).Nonempty) (x : Fin q) :
    R.totalCategoryLaw q eta x = R.categoryLaw q eta hbad x := by
  simp [totalCategoryLaw, hbad]

/-- Forget the canonical prescribed-direction event.  Finite direction
averaging constructs the post-`Theta` factor-four reduction, while the raw
quarter identity remains available separately from
`sourceForcedDirectionPathEvent_measureReal`. -/
noncomputable def toCategoricalEncodingBranchData
    {m k : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixCategoricalForcedDirectionBranchData
      m k ratioC failure thetaPathEvent rho) :
    Equation447StoppedPrefixCategoricalEncodingBranchData
      m k ratioC failure thetaPathEvent rho where
  Code := ℕ
  codeCountable := inferInstance
  forcedGoodEvent := sourceForcedDirectionPathEvent (stoppedCreationTime m k)
    (failure \ thetaPathEvent)
      (sourceDominantForcedDirection (stoppedCreationTime m k)
        (failure \ thetaPathEvent))
  badByCount := fun q ↦
    ⋃ eta, stoppedPrefixPathEvent (R.badPrefixes q eta)
  badPrefixes := R.badPrefixes
  witnessPrefixes := R.totalWitnessPrefixes
  forced_reduction := sourceDominantForcedDirection_reduction
    (stoppedCreationTime m k) (failure \ thetaPathEvent)
  forced_count_cover := R.forced_prefix_cover
  count_path_cover := fun _ ↦ Set.Subset.rfl
  witnessStoppingCount := fun q ↦
    k + categoricalOptimalWitnessCount ratioC q
  bad_firstK := R.bad_firstK
  witness_firstK := by
    intro q eta p hp
    by_cases hbad : (R.badPrefixes q eta).Nonempty
    · exact R.witness_firstK q eta hbad p (by
        simpa only [totalWitnessPrefixes_of_nonempty R q eta hbad] using hp)
    · simp [totalWitnessPrefixes, hbad] at hp
  witness_prefix_disjoint := by
    intro q eta zeta hne
    by_cases hEta : (R.badPrefixes q eta).Nonempty
    · by_cases hZeta : (R.badPrefixes q zeta).Nonempty
      · simpa only [totalWitnessPrefixes_of_nonempty R q eta hEta,
          totalWitnessPrefixes_of_nonempty R q zeta hZeta] using
          R.witness_prefix_disjoint q eta zeta hEta hZeta hne
      · simp [totalWitnessPrefixes, hZeta]
    · simp [totalWitnessPrefixes, hEta]
  backgroundWeight := fun q eta p ↦
    (4 : ENNReal)⁻¹ ^ Sigma.fst p.val /
      Measure.pi
        (fun x ↦ (R.totalCategoryLaw q eta x : Measure (Fin 3)))
        {allUpperConfig}
  categoryLaw := R.totalCategoryLaw
  witnessEquiv := R.totalWitnessEquiv
  bad_prefix_weight := by
    intro q eta p
    apply ennreal_background_factorization
    · exact probabilityMeasure_pi_allUpper_ne_zero
        (R.totalCategoryLaw q eta)
        (by
          intro x
          let hbad : (R.badPrefixes q eta).Nonempty := ⟨p.1, p.2⟩
          simpa only [totalCategoryLaw_of_nonempty R q eta hbad x] using
            R.category_upper_ne_zero q eta ⟨p.1, p.2⟩ x)
    · exact measure_ne_top _ _
  witness_prefix_weight := by
    intro q eta p
    let pbad := (R.totalWitnessEquiv q eta p).1
    let hbad : (R.badPrefixes q eta).Nonempty := ⟨pbad.1, pbad.2⟩
    let pSource :
        {p // p ∈ R.witnessPrefixes q eta hbad} :=
      ⟨p.1, by
        simpa only [totalWitnessPrefixes_of_nonempty R q eta hbad] using
          p.2⟩
    have hequiv :
        R.totalWitnessEquiv q eta p =
          R.witnessEquiv q eta hbad pSource :=
      totalWitnessEquiv_apply_of_nonempty R q eta hbad p
    apply ennreal_witness_factorization_of_relative_weight
    · exact probabilityMeasure_pi_allUpper_ne_zero
        (R.totalCategoryLaw q eta)
        (by
          intro x
          simpa only [totalCategoryLaw_of_nonempty R q eta hbad x] using
            R.category_upper_ne_zero q eta hbad x)
    · exact measure_ne_top _ _
    · simpa only [totalCategoryLaw_of_nonempty R q eta hbad, hequiv] using
        R.witness_bad_relative_weight q eta hbad pSource
  category_mass_ratio := by
    intro q eta x
    by_cases hbad : (R.badPrefixes q eta).Nonempty
    · simpa only [totalCategoryLaw_of_nonempty R q eta hbad x] using
        R.category_mass_ratio q eta hbad x
    · simp [totalCategoryLaw, hbad, measureReal_def,
        Measure.dirac_apply]

end Equation447StoppedPrefixCategoricalForcedDirectionBranchData

namespace Equation447StoppedPrefixCategoricalEncodingBranchData

/-- Total weight of the common background fibre. -/
noncomputable def backgroundNormalizer
    {m k : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixCategoricalEncodingBranchData
      m k ratioC failure thetaPathEvent rho)
    (q : ℕ) (eta : R.Code) : ENNReal :=
  ∑ b, R.backgroundWeight q eta b

/-- Sum the explicit finite encodings to obtain the common-normalizer
categorical package. -/
noncomputable def toOptimalCategoricalBranchData
    {m k : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent : Set (ℕ → Site)}
    (R : Equation447StoppedPrefixCategoricalEncodingBranchData
      m k ratioC failure thetaPathEvent rho) :
    Equation447StoppedPrefixOptimalCategoricalBranchData
      m k ratioC failure thetaPathEvent rho where
  Code := R.Code
  codeCountable := R.codeCountable
  forcedGoodEvent := R.forcedGoodEvent
  badByCount := R.badByCount
  badPrefixes := R.badPrefixes
  witnessPrefixes := R.witnessPrefixes
  forced_reduction := R.forced_reduction
  forced_count_cover := R.forced_count_cover
  count_path_cover := R.count_path_cover
  witnessStoppingCount := R.witnessStoppingCount
  bad_firstK := R.bad_firstK
  witness_firstK := R.witness_firstK
  witness_prefix_disjoint := R.witness_prefix_disjoint
  normalizer := R.backgroundNormalizer
  categoryLaw := R.categoryLaw
  bad_weight_eq := by
    intro q eta
    exact stoppedPrefixWeight_sum_eq_background_sum_mul_of_equiv
      (R.badPrefixes q eta) (Equiv.refl _)
      (R.backgroundWeight q eta)
      (Measure.pi
        (fun x ↦ (R.categoryLaw q eta x : Measure (Fin 3)))
        {allUpperConfig})
      (R.bad_prefix_weight q eta)
  witness_weight_eq := by
    intro q eta
    let nu : Fin q → Measure (Fin 3) :=
      fun x ↦ (R.categoryLaw q eta x : Measure (Fin 3))
    letI (x : Fin q) : IsProbabilityMeasure (nu x) :=
      (R.categoryLaw q eta x).prop
    exact stoppedPrefixWeight_sum_eq_background_sum_mul_pi_finset_of_equiv
      (R.witnessPrefixes q eta)
      (categoricalWitnessLayer (ι := Fin q)
        (categoricalOptimalWitnessCount ratioC q))
      (R.witnessEquiv q eta) (R.backgroundWeight q eta) nu
      (by simpa only [nu] using R.witness_prefix_weight q eta)
  category_mass_ratio := R.category_mass_ratio

end Equation447StoppedPrefixCategoricalEncodingBranchData

/-- All-six, finite-branch input whose changed-path atoms are literal finite
families of stopped prefixes.  Thus the only probability comparison left in
the source package is an inequality between two displayed finite sums of
`4^{-length}`. -/
def Prop47Lemma411412FiniteBranchStoppedPrefixChangedPathAuxThetaInputs
    (thetaTarget : ℕ → Fin 6 →
      HLOZProp47SourceAssembly.StageIndex → Set (ℕ → Site))
    (branchCount : ℕ) (c rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in Filter.atTop, ∀ i : Fin 6,
    ∀ r : HLOZProp47SourceAssembly.StageIndex,
    ∃ branchFailure : Fin branchCount → Set (ℕ → Site),
      ∃ rho : Fin branchCount → ℝ,
      ∃ branches : (j : Fin branchCount) →
          Equation447StoppedPrefixChangedPathBranchData
            m (HLOZProp47SourceAssembly.stageNumber r) c (branchFailure j)
              (thetaTarget m i r) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        ∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j

/-- Forget the explicit finite prefix families after deriving all of their
path-space measure and disjointness properties. -/
theorem finiteBranchChangedPathAuxThetaInputs_of_stoppedPrefixes
    (thetaTarget : ℕ → Fin 6 →
      HLOZProp47SourceAssembly.StageIndex → Set (ℕ → Site))
    (branchCount : ℕ) (c rhoCoeff : ℝ)
    (h : Prop47Lemma411412FiniteBranchStoppedPrefixChangedPathAuxThetaInputs
      thetaTarget branchCount c rhoCoeff) :
    Prop47Lemma411412FiniteBranchChangedPathAuxThetaInputs
      thetaTarget branchCount c rhoCoeff := by
  filter_upwards [h] with m hm
  intro i r
  rcases hm i r with
    ⟨branchFailure, rho, branches, hcover, hthreshold⟩
  refine ⟨branchFailure, rho,
    fun j ↦ (branches j).toChangedPathBranch, hcover, hthreshold⟩

/-- All-six literal stopped-prefix input in the source's categorical form.

The rate and the finite-sum comparison are absent: each fixed deleted-path
fibre supplies the two exact categorical product identities and the
one-coordinate likelihood ratio.  The branch threshold is the canonical
quarter-log-square threshold resulting from the four-way winner/parity
pigeonhole step. -/
def Prop47Lemma411412FiniteBranchStoppedPrefixOptimalCategoricalAuxThetaInputs
    (thetaTarget : ℕ → Fin 6 →
      HLOZProp47SourceAssembly.StageIndex → Set (ℕ → Site))
    (branchCount : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in Filter.atTop, ∀ i : Fin 6,
    ∀ r : HLOZProp47SourceAssembly.StageIndex,
    ∃ branchFailure : Fin branchCount → Set (ℕ → Site),
      ∃ rho : Fin branchCount → ℝ,
      ∃ branches : (j : Fin branchCount) →
          Equation447StoppedPrefixOptimalCategoricalBranchData
            m (HLOZProp47SourceAssembly.stageNumber r) ratioC
              (branchFailure j) (thetaTarget m i r) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        ∀ j, (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 ≤ rho j

/-- The strongest literal stopped-prefix source interface currently consumed
by the all-six connector.  The two categorical product identities are
replaced by finite background/witness equivalences and pointwise prefix
weight factorizations. -/
def Prop47Lemma411412FiniteBranchStoppedPrefixCategoricalEncodingAuxThetaInputs
    (thetaTarget : ℕ → Fin 6 →
      HLOZProp47SourceAssembly.StageIndex → Set (ℕ → Site))
    (branchCount : ℕ) (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in Filter.atTop, ∀ i : Fin 6,
    ∀ r : HLOZProp47SourceAssembly.StageIndex,
    ∃ branchFailure : Fin branchCount → Set (ℕ → Site),
      ∃ rho : Fin branchCount → ℝ,
      ∃ branches : (j : Fin branchCount) →
          Equation447StoppedPrefixCategoricalEncodingBranchData
            m (HLOZProp47SourceAssembly.stageNumber r) ratioC
              (branchFailure j) (thetaTarget m i r) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        ∀ j, (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 ≤ rho j

/-- Sum each explicit finite encoding to obtain the categorical-product
source package. -/
theorem finiteBranchStoppedPrefixOptimalCategoricalAuxThetaInputs_of_encoding
    (thetaTarget : ℕ → Fin 6 →
      HLOZProp47SourceAssembly.StageIndex → Set (ℕ → Site))
    (branchCount : ℕ) (ratioC : ℝ)
    (h :
      Prop47Lemma411412FiniteBranchStoppedPrefixCategoricalEncodingAuxThetaInputs
        thetaTarget branchCount ratioC) :
    Prop47Lemma411412FiniteBranchStoppedPrefixOptimalCategoricalAuxThetaInputs
      thetaTarget branchCount ratioC := by
  filter_upwards [h] with m hm
  intro i r
  rcases hm i r with
    ⟨branchFailure, rho, branches, hcover, hthreshold⟩
  exact ⟨branchFailure, rho,
    fun j ↦ (branches j).toOptimalCategoricalBranchData,
    hcover, hthreshold⟩

/-- The optimal-binomial theorem turns the literal categorical stopped-prefix
package into the former finite-prefix sum-comparison package. -/
theorem finiteBranchStoppedPrefixChangedPathAuxThetaInputs_of_optimalCategorical
    (thetaTarget : ℕ → Fin 6 →
      HLOZProp47SourceAssembly.StageIndex → Set (ℕ → Site))
    (branchCount : ℕ) (ratioC : ℝ) (hC : 0 < ratioC)
    (h :
      Prop47Lemma411412FiniteBranchStoppedPrefixOptimalCategoricalAuxThetaInputs
        thetaTarget branchCount ratioC) :
    Prop47Lemma411412FiniteBranchStoppedPrefixChangedPathAuxThetaInputs
      thetaTarget branchCount (categoricalOptimalRate ratioC) (1 / 4) := by
  have hbinomial :=
    eventually_optimal_binomial_layer_above_quarter_log_sq ratioC hC
  filter_upwards [h, hbinomial] with m hm hbin
  intro i r
  rcases hm i r with
    ⟨branchFailure, rho, branches, hcover, hthreshold⟩
  refine ⟨branchFailure, rho, ?_, hcover, hthreshold⟩
  intro j
  apply (branches j).toStoppedPrefixChangedPathBranchData hC
  intro q hq
  apply hbin q
  exact (Nat.ceil_le_ceil (hthreshold j)).trans hq

/-- The genuinely analytic/event-identification fields of an equation-(4.47)
atom, after its stopped product law and measurability have been separated. -/
structure Equation447RemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC cTheta thetaPower : ℝ)
    (failure pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  badAtom : ℕ → (Coord → ℕ) → Set ((Coord → ℕ) × Direction)
  historyAtom : ℕ → (Coord → ℕ) → Set ((Coord → ℕ) × Direction)
  category : ∀ q, (Coord → ℕ) →
    ((Coord → ℕ) × Direction) → Fin q → Fin 3
  categoryLaw : ∀ q, (Coord → ℕ) → Fin q → Measure (Fin 3)
  categoryLaw_probability : ∀ q eta x,
    IsProbabilityMeasure (categoryLaw q eta x)
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2) ∩ D) ×ˢ
        (Set.univ : Set Direction))
  theta_bound :
    ((sourceTruncatedProfileMeasure m profile).prod directionLaw).real
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ≤
      Real.exp (-cTheta * (m : ℝ) ^ thetaPower)
  equation447_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta, badAtom q eta
  bad_subset_history_allUpper : ∀ q eta,
    badAtom q eta ⊆ historyAtom q eta ∩
      category q eta ⁻¹' {allUpperConfig}
  conditional_category_product : ∀ q eta,
    (sourceTruncatedProfileMeasure m profile).prod directionLaw
        (historyAtom q eta ∩ category q eta ⁻¹' {allUpperConfig}) =
      (sourceTruncatedProfileMeasure m profile).prod directionLaw
          (historyAtom q eta) *
        Measure.pi (categoryLaw q eta) {allUpperConfig}
  category_mass_ratio : ∀ q eta x,
    (categoryLaw q eta x).real {0} ≤
      ratioC * (categoryLaw q eta x).real {1}
  history_disjoint : ∀ q, Pairwise fun eta zeta ↦
    Disjoint (historyAtom q eta) (historyAtom q zeta)
  history_measurable : ∀ q eta, MeasurableSet (historyAtom q eta)

/-- The event/category fields of a branch atom at an explicit profile
threshold.  This is the source-faithful form used after the full favorite-set
overflow has been split into parity/winner branches. -/
structure Equation447BranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (failure pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  badAtom : ℕ → (Coord → ℕ) → Set ((Coord → ℕ) × Direction)
  historyAtom : ℕ → (Coord → ℕ) → Set ((Coord → ℕ) × Direction)
  category : ∀ q, (Coord → ℕ) →
    ((Coord → ℕ) × Direction) → Fin q → Fin 3
  categoryLaw : ∀ q, (Coord → ℕ) → Fin q → Measure (Fin 3)
  categoryLaw_probability : ∀ q eta x,
    IsProbabilityMeasure (categoryLaw q eta x)
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ D) ×ˢ
        (Set.univ : Set Direction))
  thetaPathEvent : Set (ℕ → Site)
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent
  equation447_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta, badAtom q eta
  bad_subset_history_allUpper : ∀ q eta,
    badAtom q eta ⊆ historyAtom q eta ∩
      category q eta ⁻¹' {allUpperConfig}
  conditional_category_product : ∀ q eta,
    (sourceTruncatedProfileMeasure m profile).prod directionLaw
        (historyAtom q eta ∩ category q eta ⁻¹' {allUpperConfig}) =
      (sourceTruncatedProfileMeasure m profile).prod directionLaw
          (historyAtom q eta) *
        Measure.pi (categoryLaw q eta) {allUpperConfig}
  category_mass_ratio : ∀ q eta x,
    (categoryLaw q eta x).real {0} ≤
      ratioC * (categoryLaw q eta x).real {1}
  history_disjoint : ∀ q, Pairwise fun eta zeta ↦
    Disjoint (historyAtom q eta) (historyAtom q zeta)
  history_measurable : ∀ q eta, MeasurableSet (historyAtom q eta)

/-- Literal deleted-path witness data for the special base step (4.47).
Unlike `Equation447BranchRemainingData`, this record does not pretend that
the artificial lower-band witness remains in the same stopped history atom.
It exposes the paper's changed-path atom, its fixed-cardinality switch bound,
and the stopping-time disjointness (4.54). -/
structure Equation447PathWitnessBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (c rho : ℝ)
    (failure pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  Path : Type
  [pathCountable : Countable Path]
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  badAtom : ℕ → Path → Set ((Coord → ℕ) × Direction)
  witnessAtom : ℕ → Path → Set ((Coord → ℕ) × Direction)
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ D) ×ˢ
        (Set.univ : Set Direction))
  thetaPathEvent : Set (ℕ → Site)
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent
  equation447_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta, badAtom q eta
  path_switch : ∀ q eta, Nat.ceil rho ≤ q →
    ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
        (badAtom q eta) ≤
      ENNReal.ofReal (Real.exp (-c * (q : ℝ))) *
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
          (witnessAtom q eta)
  witness_disjoint : ∀ q, Pairwise fun eta zeta ↦
    Disjoint (witnessAtom q eta) (witnessAtom q zeta)
  witness_measurable : ∀ q eta, MeasurableSet (witnessAtom q eta)

/-- The source-level categorical form of the deleted-path witness argument
in (4.51)--(4.54).

For each external-path history and exact bad cardinality `q`, the source
identifies the all-upper categorical cell and an artificial-lower witness
layer.  The two conditional cell identities share the same history
normalizer, while the coordinate ratio and the explicit binomial-layer
inequality are precisely the Stirling comparison.  Consequently the
measure-level `path_switch` field of
`Equation447PathWitnessBranchRemainingData` is derived below; it is not an
assumption of this record. -/
structure Equation447CategoricalPathWitnessBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (c rho : ℝ)
    (failure pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  Path : Type
  [pathCountable : Countable Path]
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  ratioC : ℝ
  ratioC_nonneg : 0 ≤ ratioC
  witnessCount : ℕ → Path → ℕ
  badAtom : ℕ → Path → Set ((Coord → ℕ) × Direction)
  witnessAtom : ℕ → Path → Set ((Coord → ℕ) × Direction)
  badHistory : ℕ → Path → Set ((Coord → ℕ) × Direction)
  witnessHistory : ℕ → Path → Set ((Coord → ℕ) × Direction)
  normalizer : ℕ → Path → ENNReal
  badCategory : ∀ q, Path →
    ((Coord → ℕ) × Direction) → Fin q → Fin 3
  witnessCategory : ∀ q, Path →
    ((Coord → ℕ) × Direction) → Fin q → Fin 3
  categoryLaw : ∀ q, Path → Fin q → ProbabilityMeasure (Fin 3)
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ D) ×ˢ
        (Set.univ : Set Direction))
  thetaPathEvent : Set (ℕ → Site)
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent
  equation447_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta, badAtom q eta
  bad_subset : ∀ q eta,
    badAtom q eta ⊆ badHistory q eta ∩
      badCategory q eta ⁻¹' {allUpperConfig}
  witness_subset : ∀ q eta,
    witnessHistory q eta ∩ witnessCategory q eta ⁻¹'
        (↑(categoricalWitnessLayer (ι := Fin q) (witnessCount q eta)) :
          Set (Fin q → Fin 3)) ⊆ witnessAtom q eta
  bad_conditional_product : ∀ q eta,
    (sourceTruncatedProfileMeasure m profile).prod directionLaw
        (badHistory q eta ∩
          badCategory q eta ⁻¹' {allUpperConfig}) =
      normalizer q eta *
        Measure.pi (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
          {allUpperConfig}
  witness_conditional_product : ∀ q eta,
    (sourceTruncatedProfileMeasure m profile).prod directionLaw
        (witnessHistory q eta ∩ witnessCategory q eta ⁻¹'
          (↑(categoricalWitnessLayer (ι := Fin q) (witnessCount q eta)) :
            Set (Fin q → Fin 3))) =
      normalizer q eta *
        Measure.pi (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
          (↑(categoricalWitnessLayer (ι := Fin q) (witnessCount q eta)) :
            Set (Fin q → Fin 3))
  category_mass_ratio : ∀ q eta x,
    ((categoryLaw q eta x : Measure (Fin 3))).real {0} ≤
      ratioC * ((categoryLaw q eta x : Measure (Fin 3))).real {1}
  witnessCount_le : ∀ q eta, witnessCount q eta ≤ q
  binomial_layer : ∀ q eta, Nat.ceil rho ≤ q →
    ratioC ^ witnessCount q eta ≤
      Real.exp (-c * (q : ℝ)) * Nat.choose q (witnessCount q eta)
  witness_disjoint : ∀ q, Pairwise fun eta zeta ↦
    Disjoint (witnessAtom q eta) (witnessAtom q zeta)

namespace Equation447CategoricalPathWitnessBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {c rho : ℝ}
  {failure pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Derive the set-level fixed-cardinality path switch from the conditional
categorical product and binomial-layer comparison. -/
noncomputable def toRemainingData
    (R : Equation447CategoricalPathWitnessBranchRemainingData cWindow m c rho
      failure pathAtom profile lazyVector nextDirection) :
    Equation447PathWitnessBranchRemainingData cWindow m c rho
      failure pathAtom profile lazyVector nextDirection where
  Path := R.Path
  pathCountable := R.pathCountable
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  witnessAtom := R.witnessAtom
  failure_subset := R.failure_subset
  thetaPathEvent := R.thetaPathEvent
  theta_preimage_subset := R.theta_preimage_subset
  equation447_cover := R.equation447_cover
  path_switch := by
    intro q eta hq
    letI (x : Fin q) : IsProbabilityMeasure
        (R.categoryLaw q eta x : Measure (Fin 3)) :=
      (R.categoryLaw q eta x).prop
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      (measure_bad_le_exp_mul_witness_of_conditional_categorical_layer
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
        (R.badAtom q eta) (R.witnessAtom q eta)
        (R.badHistory q eta) (R.witnessHistory q eta)
        (R.normalizer q eta)
        (R.badCategory q eta) (R.witnessCategory q eta)
        (fun x ↦ (R.categoryLaw q eta x : Measure (Fin 3)))
        R.ratioC c R.ratioC_nonneg (R.witnessCount q eta)
        (by simpa using R.witnessCount_le q eta)
        (R.bad_subset q eta) (R.witness_subset q eta)
        (R.bad_conditional_product q eta)
        (R.witness_conditional_product q eta)
        (R.category_mass_ratio q eta) (by simpa using R.binomial_layer q eta hq))
  witness_disjoint := R.witness_disjoint
  witness_measurable := by
    intro q eta
    exact (Set.to_countable (R.witnessAtom q eta)).measurableSet

end Equation447CategoricalPathWitnessBranchRemainingData

/-! ### Categorical source data with the binomial layer internalized -/

/-- The source-level categorical history/witness package after removing the
Stirling/binomial inequality from the assumptions.

The witness cardinality is Lean's canonical maximum weighted binomial layer
`categoricalOptimalWitnessCount ratioC q`.  The elementary binomial theorem
in `HLOZEquation447` proves that this layer has an exponential advantage for
all sufficiently large `q`; the quarter-log-square threshold makes every
cardinality used by the planar connector sufficiently large. -/
structure Equation447OptimalCategoricalPathWitnessBranchCoreData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (failure pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  Path : Type
  [pathCountable : Countable Path]
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  badAtom : ℕ → Path → Set ((Coord → ℕ) × Direction)
  witnessAtom : ℕ → Path → Set ((Coord → ℕ) × Direction)
  badHistory : ℕ → Path → Set ((Coord → ℕ) × Direction)
  witnessHistory : ℕ → Path → Set ((Coord → ℕ) × Direction)
  normalizer : ℕ → Path → ENNReal
  badCategory : ∀ q, Path →
    ((Coord → ℕ) × Direction) → Fin q → Fin 3
  witnessCategory : ∀ q, Path →
    ((Coord → ℕ) × Direction) → Fin q → Fin 3
  categoryLaw : ∀ q, Path → Fin q → ProbabilityMeasure (Fin 3)
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ D) ×ˢ
        (Set.univ : Set Direction))
  thetaPathEvent : Set (ℕ → Site)
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent
  equation447_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta, badAtom q eta
  bad_subset : ∀ q eta,
    badAtom q eta ⊆ badHistory q eta ∩
      badCategory q eta ⁻¹' {allUpperConfig}
  witness_subset : ∀ q eta,
    witnessHistory q eta ∩ witnessCategory q eta ⁻¹'
        (↑(categoricalWitnessLayer (ι := Fin q)
          (categoricalOptimalWitnessCount ratioC q)) :
          Set (Fin q → Fin 3)) ⊆ witnessAtom q eta
  bad_conditional_product : ∀ q eta,
    (sourceTruncatedProfileMeasure m profile).prod directionLaw
        (badHistory q eta ∩
          badCategory q eta ⁻¹' {allUpperConfig}) =
      normalizer q eta *
        Measure.pi (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
          {allUpperConfig}
  witness_conditional_product : ∀ q eta,
    (sourceTruncatedProfileMeasure m profile).prod directionLaw
        (witnessHistory q eta ∩ witnessCategory q eta ⁻¹'
          (↑(categoricalWitnessLayer (ι := Fin q)
            (categoricalOptimalWitnessCount ratioC q)) :
            Set (Fin q → Fin 3))) =
      normalizer q eta *
        Measure.pi (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
          (↑(categoricalWitnessLayer (ι := Fin q)
            (categoricalOptimalWitnessCount ratioC q)) :
            Set (Fin q → Fin 3))
  category_mass_ratio : ∀ q eta x,
    ((categoryLaw q eta x : Measure (Fin 3))).real {0} ≤
      ratioC * ((categoryLaw q eta x : Measure (Fin 3))).real {1}

/-- The optimal categorical package in the form consumed by the existing
fixed-cardinality connector.  The categorical data and the cross-path
disjointness are separated so that the latter can be derived from the
stopping-length argument (4.54). -/
structure Equation447OptimalCategoricalPathWitnessBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (failure pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction)
    extends Equation447OptimalCategoricalPathWitnessBranchCoreData
      cWindow m ratioC rho failure pathAtom profile lazyVector nextDirection where
  witness_disjoint : ∀ q, Pairwise fun eta zeta ↦
    Disjoint (witnessAtom q eta) (witnessAtom q zeta)

/-! ### Stopping-length derivation of (4.54) -/

/-- Abstract form of the monotone stopped-path-length argument in HLOZ
(4.54).  A witness at path length `horizon eta` has exactly `target q`
level-`m` sites, while immediately before that horizon it has one fewer.
If two different path codes have the same length, their fixed prefixes are
incompatible.  These facts imply pairwise disjointness; it is not a separate
probability assumption. -/
structure Equation447PathLengthSeparationData
    {Path Ω : Type}
    (witnessAtom : ℕ → Path → Set Ω) where
  horizon : Path → ℕ
  levelCount : Ω → ℕ → ℕ
  target : ℕ → ℕ
  levelCount_mono : ∀ w, Monotone (levelCount w)
  horizon_pos : ∀ q eta w, w ∈ witnessAtom q eta → 0 < horizon eta
  count_at_horizon : ∀ q eta w, w ∈ witnessAtom q eta →
    levelCount w (horizon eta) = target q
  count_before_horizon : ∀ q eta w, w ∈ witnessAtom q eta →
    levelCount w (horizon eta - 1) + 1 = target q
  same_horizon_unique : ∀ q eta zeta w,
    horizon eta = horizon zeta →
    w ∈ witnessAtom q eta → w ∈ witnessAtom q zeta → eta = zeta

namespace Equation447PathLengthSeparationData

variable {Path Ω : Type} {witnessAtom : ℕ → Path → Set Ω}

/-- Monotonicity of the level-count process and the one-site jump at the
chosen stopped length prove the disjointness statement (4.54). -/
theorem pairwise_disjoint
    (S : Equation447PathLengthSeparationData witnessAtom) (q : ℕ) :
    Pairwise fun eta zeta ↦
      Disjoint (witnessAtom q eta) (witnessAtom q zeta) := by
  intro eta zeta hne
  rw [Set.disjoint_left]
  intro w hwEta hwZeta
  have hEtaPos := S.horizon_pos q eta w hwEta
  have hZetaPos := S.horizon_pos q zeta w hwZeta
  rcases lt_trichotomy (S.horizon eta) (S.horizon zeta) with
      hlt | heq | hgt
  · have htime : S.horizon eta ≤ S.horizon zeta - 1 := by omega
    have hmono := S.levelCount_mono w htime
    have hEta := S.count_at_horizon q eta w hwEta
    have hZeta := S.count_before_horizon q zeta w hwZeta
    omega
  · exact hne (S.same_horizon_unique q eta zeta w heq hwEta hwZeta)
  · have htime : S.horizon zeta ≤ S.horizon eta - 1 := by omega
    have hmono := S.levelCount_mono w htime
    have hEta := S.count_before_horizon q eta w hwEta
    have hZeta := S.count_at_horizon q zeta w hwZeta
    omega

end Equation447PathLengthSeparationData

/-- Source-facing optimal categorical package with (4.54) expressed by the
literal stopped-length/count mechanism rather than assumed as a set-level
disjointness conclusion. -/
structure Equation447LengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (failure pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction)
    extends Equation447OptimalCategoricalPathWitnessBranchCoreData
      cWindow m ratioC rho failure pathAtom profile lazyVector nextDirection where
  separation : Equation447PathLengthSeparationData witnessAtom

namespace Equation447LengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC rho : ℝ}
  {failure pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Forget the path-length certificate after deriving its set-level
disjointness consequence. -/
noncomputable def toOptimalCategoricalPathWitnessBranchRemainingData
    (R : Equation447LengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho failure pathAtom profile lazyVector nextDirection) :
    Equation447OptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho failure pathAtom profile lazyVector nextDirection where
  toEquation447OptimalCategoricalPathWitnessBranchCoreData :=
    R.toEquation447OptimalCategoricalPathWitnessBranchCoreData
  witness_disjoint := R.separation.pairwise_disjoint

end Equation447LengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData

/-! ### Rectangular derivation of the two conditional products in (4.47) -/

/-- The canonical one-coordinate conditional category law used below.

The profile inequality makes the truncated negative-binomial law a
probability measure.  A null history fibre is assigned the inactive category
`2`; this makes the finite-product factorization valid without a positivity
premise on every coordinate fibre. -/
noncomputable def equation447ConditionalCategoryLawOrDirac
    (m k : ℕ) (hk : k < m) (history : Set ℕ)
    (category : ℕ → Fin 3) : ProbabilityMeasure (Fin 3) :=
  conditionalCategoryLawOrDirac
    (sourceTruncatedNegBinMeasure m k)
    (cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m k hk))
    history MeasurableSet.of_discrete category (measurable_of_countable _) 2

/-- Source-facing rectangular data for the bad path and its artificial
changed-path witness in (4.47)--(4.53).

Unlike `Equation447OptimalCategoricalPathWitnessBranchCoreData`, this record
does not assume either full conditional-product identity.  For every feasible
count it identifies the two histories with coordinate rectangles, supplies
injective selected coordinates and coordinate category maps, and records only
the two facts genuinely shared across the path switch: equality of the two
history masses and equality of the selected one-coordinate conditional laws.
Lean derives both finite product identities.  Infeasible counts are filled by
the inactive Dirac category and hence contribute zero automatically.  The
fresh direction is fixed definitionally to the first direction: the stopped
product law is uniform in that coordinate, and the downstream connector has
already proved the factor-four restoration.  Thus choosing a direction is
bookkeeping, not source data.  The bad and changed-path rectangles both use
that same singleton direction, so the source supplies only the equality of
their truncated-profile masses; Lean restores the common direction factor.
The likelihood comparison is not stored as an inequality between two whole
conditional cells either.  The source identifies two finite cells and gives
the actual injective cell switch together with a comparison of the raw
negative-binomial masses of each paired singleton.  Lean proves that atoms
outside the truncation support have zero mass, proves that the switch
preserves the support, cancels the common conditional normalizer on supported
atoms, and then sums the injective switch to obtain the required cell-mass
ratio.  Thus the source assumes neither normalized singleton comparisons nor
the stronger comparison of every upper singleton with every lower singleton.
The changed-path alternatives are indexed canonically by natural numbers,
so this strongest source record also has no auxiliary path type or
countability instance. -/
structure Equation447RectangularOptimalCategoricalPathWitnessBranchCoreData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (failure thetaPathEvent pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  profile_lt : ∀ x, profile x < m
  D : Set (Coord → ℕ)
  badHistoryFiber : ∀ q, q ≤ Fintype.card Coord → ℕ → Coord → Set ℕ
  badSelectedCoordinate : ∀ q, q ≤ Fintype.card Coord → ℕ → Fin q → Coord
  badSelectedCoordinate_injective : ∀ q hq eta,
    Function.Injective (badSelectedCoordinate q hq eta)
  badCategoryCoordinate :
    ∀ q, q ≤ Fintype.card Coord → ℕ → Fin q → ℕ → Fin 3
  witnessHistoryFiber : ∀ q, q ≤ Fintype.card Coord → ℕ → Coord → Set ℕ
  witnessSelectedCoordinate :
    ∀ q, q ≤ Fintype.card Coord → ℕ → Fin q → Coord
  witnessSelectedCoordinate_injective : ∀ q hq eta,
    Function.Injective (witnessSelectedCoordinate q hq eta)
  witnessCategoryCoordinate :
    ∀ q, q ≤ Fintype.card Coord → ℕ → Fin q → ℕ → Fin 3
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ D) ×ˢ
        (Set.univ : Set Direction))
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent
  equation447_cover : ∀ q hq,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {(0 : Direction)}) ⊆ ⋃ eta,
        (((Set.pi Set.univ (badHistoryFiber q hq eta)) ×ˢ
            {(0 : Direction)}) ∩
          (fun w x ↦ badCategoryCoordinate q hq eta x
            (w.1 (badSelectedCoordinate q hq eta x))) ⁻¹'
            {@allUpperConfig (Fin q)})
  history_mass_eq : ∀ q hq eta,
    sourceTruncatedProfileMeasure m profile
        (Set.pi Set.univ (badHistoryFiber q hq eta)) =
      sourceTruncatedProfileMeasure m profile
        (Set.pi Set.univ (witnessHistoryFiber q hq eta))
  conditionalLaw_eq : ∀ q hq eta x,
    equation447ConditionalCategoryLawOrDirac m
        (profile (badSelectedCoordinate q hq eta x))
        (profile_lt (badSelectedCoordinate q hq eta x))
        (badHistoryFiber q hq eta (badSelectedCoordinate q hq eta x))
        (badCategoryCoordinate q hq eta x) =
      equation447ConditionalCategoryLawOrDirac m
        (profile (witnessSelectedCoordinate q hq eta x))
        (profile_lt (witnessSelectedCoordinate q hq eta x))
        (witnessHistoryFiber q hq eta
          (witnessSelectedCoordinate q hq eta x))
        (witnessCategoryCoordinate q hq eta x)
  upperCell : ∀ q, q ≤ Fintype.card Coord → ℕ → Fin q → Finset ℕ
  lowerCell : ∀ q, q ≤ Fintype.card Coord → ℕ → Fin q → Finset ℕ
  upperCell_identification : ∀ q hq eta x,
    badHistoryFiber q hq eta (badSelectedCoordinate q hq eta x) ∩
        badCategoryCoordinate q hq eta x ⁻¹' ({0} : Set (Fin 3)) =
      (↑(upperCell q hq eta x) : Set ℕ)
  lowerCell_identification : ∀ q hq eta x,
    badHistoryFiber q hq eta (badSelectedCoordinate q hq eta x) ∩
        badCategoryCoordinate q hq eta x ⁻¹' ({1} : Set (Fin 3)) =
      (↑(lowerCell q hq eta x) : Set ℕ)
  ratioC_nonneg : 0 ≤ ratioC
  cellSwitch : ∀ q, q ≤ Fintype.card Coord → ℕ → Fin q → ℕ → ℕ
  cellSwitch_mem_lower : ∀ q hq eta x a,
    a ∈ upperCell q hq eta x →
      cellSwitch q hq eta x a ∈ lowerCell q hq eta x
  cellSwitch_injective : ∀ q hq eta x,
    Set.InjOn (cellSwitch q hq eta x) (↑(upperCell q hq eta x) : Set ℕ)
  cellSwitch_below : ∀ q hq eta x,
    ∀ a ∈ upperCell q hq eta x,
      a ∈ sourceBelowSet m
          (profile (badSelectedCoordinate q hq eta x)) →
        cellSwitch q hq eta x a ∈ sourceBelowSet m
          (profile (badSelectedCoordinate q hq eta x))
  pointwise_raw_mass_ratio : ∀ q hq eta x,
    ∀ a ∈ upperCell q hq eta x,
      Erdos1166.HLOZUrn.negBinMass
          (profile (badSelectedCoordinate q hq eta x)) a ≤
      ratioC *
        Erdos1166.HLOZUrn.negBinMass
          (profile (badSelectedCoordinate q hq eta x))
            (cellSwitch q hq eta x a)

namespace Equation447RectangularOptimalCategoricalPathWitnessBranchCoreData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC rho : ℝ}
  {failure thetaPathEvent pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

variable (R : Equation447RectangularOptimalCategoricalPathWitnessBranchCoreData
    cWindow m ratioC rho failure thetaPathEvent pathAtom
      profile lazyVector nextDirection)

/-- Sum the literal injective singleton switch over the two finite history
cells.

This is the whole-cell likelihood inequality formerly stored directly in the
strict rectangular source record. -/
theorem raw_category_mass_ratio (q : ℕ)
    (hq : q ≤ Fintype.card Coord) (eta : ℕ) (x : Fin q) :
    (sourceTruncatedNegBinMeasure m
      (profile (R.badSelectedCoordinate q hq eta x))).real
        (R.badHistoryFiber q hq eta
            (R.badSelectedCoordinate q hq eta x) ∩
          R.badCategoryCoordinate q hq eta x ⁻¹' ({0} : Set (Fin 3))) ≤
      ratioC *
        (sourceTruncatedNegBinMeasure m
          (profile (R.badSelectedCoordinate q hq eta x))).real
          (R.badHistoryFiber q hq eta
              (R.badSelectedCoordinate q hq eta x) ∩
            R.badCategoryCoordinate q hq eta x ⁻¹' ({1} : Set (Fin 3))) := by
  let μ := sourceTruncatedNegBinMeasure m
    (profile (R.badSelectedCoordinate q hq eta x))
  letI : IsProbabilityMeasure μ :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m
        (profile (R.badSelectedCoordinate q hq eta x))
        (R.profile_lt (R.badSelectedCoordinate q hq eta x)))
  rw [R.upperCell_identification q hq eta x,
    R.lowerCell_identification q hq eta x]
  have hmeasure :
      μ (↑(R.upperCell q hq eta x) : Set ℕ) ≤
        ENNReal.ofReal ratioC *
          μ (↑(R.lowerCell q hq eta x) : Set ℕ) := by
    apply measure_le_mul_measure_of_injective_point_switch μ
      (↑(R.upperCell q hq eta x) : Set ℕ)
      (↑(R.lowerCell q hq eta x) : Set ℕ)
      (ENNReal.ofReal ratioC) (R.cellSwitch q hq eta x)
    · intro a ha
      exact R.cellSwitch_mem_lower q hq eta x a ha
    · exact R.cellSwitch_injective q hq eta x
    · intro a ha
      have hreal : μ.real {a} ≤
          ratioC * μ.real {R.cellSwitch q hq eta x a} := by
        by_cases haBelow : a ∈ sourceBelowSet m
            (profile (R.badSelectedCoordinate q hq eta x))
        · have hbBelow := R.cellSwitch_below q hq eta x a ha haBelow
          rw [sourceTruncatedNegBinMeasure_real_singleton m
              (profile (R.badSelectedCoordinate q hq eta x)) a
              (R.profile_lt (R.badSelectedCoordinate q hq eta x)) haBelow,
            sourceTruncatedNegBinMeasure_real_singleton m
              (profile (R.badSelectedCoordinate q hq eta x))
              (R.cellSwitch q hq eta x a)
              (R.profile_lt (R.badSelectedCoordinate q hq eta x)) hbBelow]
          have hnorm : 0 ≤
              (Erdos1166.HLOZUrn.negBinMeasure
                (profile (R.badSelectedCoordinate q hq eta x))
                  (sourceBelowSet m
                    (profile (R.badSelectedCoordinate q hq eta x)))).toReal⁻¹ := by
            positivity
          calc
            _ ≤
                (Erdos1166.HLOZUrn.negBinMeasure
                  (profile (R.badSelectedCoordinate q hq eta x))
                    (sourceBelowSet m
                      (profile (R.badSelectedCoordinate q hq eta x)))).toReal⁻¹ *
                  (ratioC * Erdos1166.HLOZUrn.negBinMass
                    (profile (R.badSelectedCoordinate q hq eta x))
                      (R.cellSwitch q hq eta x a)) :=
              mul_le_mul_of_nonneg_left
                (R.pointwise_raw_mass_ratio q hq eta x a ha) hnorm
            _ = _ := by ring
        · rw [sourceTruncatedNegBinMeasure_real_singleton_eq_zero_of_not_mem
            m (profile (R.badSelectedCoordinate q hq eta x)) a haBelow]
          exact mul_nonneg R.ratioC_nonneg measureReal_nonneg
      rw [← ofReal_measureReal (measure_ne_top μ {a}),
        ← ofReal_measureReal
          (measure_ne_top μ {R.cellSwitch q hq eta x a}),
        ← ENNReal.ofReal_mul R.ratioC_nonneg]
      exact ENNReal.ofReal_le_ofReal
        hreal
  have hfinite : ENNReal.ofReal ratioC *
      μ (↑(R.lowerCell q hq eta x) : Set ℕ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  simpa only [measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal R.ratioC_nonneg] using hreal

/-- Total bad history; infeasible exact counts use the whole product space,
while their inactive category makes the relevant category cell empty. -/
noncomputable def badHistory (q eta : ℕ) :
    Set ((Coord → ℕ) × Direction) :=
  if hq : q ≤ Fintype.card Coord then
    (Set.pi Set.univ (R.badHistoryFiber q hq eta)) ×ˢ
      {(0 : Direction)}
  else Set.univ

/-- Total artificial-witness history. -/
noncomputable def witnessHistory (q eta : ℕ) :
    Set ((Coord → ℕ) × Direction) :=
  if hq : q ≤ Fintype.card Coord then
    (Set.pi Set.univ (R.witnessHistoryFiber q hq eta)) ×ˢ
      {(0 : Direction)}
  else Set.univ

/-- Total bad category vector. -/
noncomputable def badCategory (q eta : ℕ) :
    ((Coord → ℕ) × Direction) → Fin q → Fin 3 :=
  if hq : q ≤ Fintype.card Coord then
    fun w x ↦ R.badCategoryCoordinate q hq eta x
      (w.1 (R.badSelectedCoordinate q hq eta x))
  else fun _ _ ↦ 2

/-- Total artificial-witness category vector. -/
noncomputable def witnessCategory (q eta : ℕ) :
    ((Coord → ℕ) × Direction) → Fin q → Fin 3 :=
  if hq : q ≤ Fintype.card Coord then
    fun w x ↦ R.witnessCategoryCoordinate q hq eta x
      (w.1 (R.witnessSelectedCoordinate q hq eta x))
  else fun _ _ ↦ 2

/-- The common selected-coordinate law, represented using the bad history;
`conditionalLaw_eq` identifies the artificial path's law with this one. -/
noncomputable def categoryLaw (q eta : ℕ) (x : Fin q) :
    ProbabilityMeasure (Fin 3) :=
  if hq : q ≤ Fintype.card Coord then
    equation447ConditionalCategoryLawOrDirac m
      (profile (R.badSelectedCoordinate q hq eta x))
      (R.profile_lt (R.badSelectedCoordinate q hq eta x))
      (R.badHistoryFiber q hq eta (R.badSelectedCoordinate q hq eta x))
      (R.badCategoryCoordinate q hq eta x)
  else ⟨Measure.dirac 2, Measure.dirac.isProbabilityMeasure⟩

/-- The bad all-upper cell. -/
noncomputable def badAtom (q eta : ℕ) :
    Set ((Coord → ℕ) × Direction) :=
  R.badHistory q eta ∩ R.badCategory q eta ⁻¹' {allUpperConfig}

/-- The optimal artificial lower-category layer. -/
noncomputable def witnessAtom (q eta : ℕ) :
    Set ((Coord → ℕ) × Direction) :=
  R.witnessHistory q eta ∩ R.witnessCategory q eta ⁻¹'
    (↑(categoricalWitnessLayer (ι := Fin q)
      (categoricalOptimalWitnessCount ratioC q)) : Set (Fin q → Fin 3))

/-- The common history normalizer. -/
noncomputable def normalizer (q eta : ℕ) : ENNReal :=
  (sourceTruncatedProfileMeasure m profile).prod directionLaw
    (R.badHistory q eta)

/-- Rectangular finite-product factorization supplies the old core record,
including both exact conditional products. -/
noncomputable def toOptimalCategoricalPathWitnessBranchCoreData :
    Equation447OptimalCategoricalPathWitnessBranchCoreData
      cWindow m ratioC rho failure pathAtom profile lazyVector
        nextDirection := by
  letI (x : Coord) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (R.profile_lt x))
  exact
    { Path := ℕ
      pathCountable := inferInstance
      forcedDirection := 0
      D := R.D
      badAtom := R.badAtom
      witnessAtom := R.witnessAtom
      badHistory := R.badHistory
      witnessHistory := R.witnessHistory
      normalizer := R.normalizer
      badCategory := R.badCategory
      witnessCategory := R.witnessCategory
      categoryLaw := R.categoryLaw
      failure_subset := R.failure_subset
      thetaPathEvent := thetaPathEvent
      theta_preimage_subset := R.theta_preimage_subset
      equation447_cover := by
        intro q
        by_cases hq : q ≤ Fintype.card Coord
        · simpa [badAtom, badHistory, badCategory, hq] using
            R.equation447_cover q hq
        · rw [sourceEquation447ByCount_eq_empty_of_card_lt cWindow m profile
              R.D Set.univ q (Nat.lt_of_not_ge hq)]
          simp
      bad_subset := by
        intro q eta
        exact le_rfl
      witness_subset := by
        intro q eta
        exact le_rfl
      bad_conditional_product := by
        intro q eta
        by_cases hq : q ≤ Fintype.card Coord
        · simpa [badAtom, badHistory, badCategory, categoryLaw, normalizer,
            hq, sourceTruncatedProfileMeasure,
            equation447ConditionalCategoryLawOrDirac] using
            (pi_prod_history_selected_category_finset_factorization_or_dirac
              (fun x ↦ sourceTruncatedNegBinMeasure m (profile x))
              directionLaw (R.badHistoryFiber q hq eta)
              (fun _ ↦ MeasurableSet.of_discrete)
              ({(0 : Direction)} : Set Direction)
              (R.badSelectedCoordinate q hq eta)
              (R.badSelectedCoordinate_injective q hq eta)
              (R.badCategoryCoordinate q hq eta)
              (fun _ ↦ measurable_of_countable _)
              (fun _ ↦ (2 : Fin 3))
              ({@allUpperConfig (Fin q)} : Finset (Fin q → Fin 3)))
        · have hqpos : 0 < q := by omega
          have hcat : (fun _ : ((Coord → ℕ) × Direction) ↦
                fun _ : Fin q ↦ (2 : Fin 3)) ⁻¹'
                ({@allUpperConfig (Fin q)} : Set (Fin q → Fin 3)) = ∅ := by
            ext w
            simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
            intro hw
            have heq : (fun _ : Fin q ↦ (2 : Fin 3)) =
                @allUpperConfig (Fin q) := by simpa using hw
            have hbad := congrFun heq ⟨0, hqpos⟩
            norm_num [allUpperConfig] at hbad
            omega
          have hpi : Measure.pi (fun _ : Fin q ↦ Measure.dirac (2 : Fin 3))
                ({@allUpperConfig (Fin q)} : Set (Fin q → Fin 3)) = 0 := by
            rw [Measure.pi_singleton]
            apply Finset.prod_eq_zero (i := ⟨0, hqpos⟩)
            · simp
            · simp [allUpperConfig]
          simp [badAtom, badHistory, badCategory, categoryLaw, normalizer,
            hq, hcat, hpi]
      witness_conditional_product := by
        intro q eta
        by_cases hq : q ≤ Fintype.card Coord
        · have hfact :=
            pi_prod_history_selected_category_finset_factorization_or_dirac
              (fun x ↦ sourceTruncatedNegBinMeasure m (profile x))
              directionLaw (R.witnessHistoryFiber q hq eta)
              (fun _ ↦ MeasurableSet.of_discrete)
              ({(0 : Direction)} : Set Direction)
              (R.witnessSelectedCoordinate q hq eta)
              (R.witnessSelectedCoordinate_injective q hq eta)
              (R.witnessCategoryCoordinate q hq eta)
              (fun _ ↦ measurable_of_countable _)
              (fun _ ↦ (2 : Fin 3))
              (categoricalWitnessLayer (ι := Fin q)
                (categoricalOptimalWitnessCount ratioC q))
          have hlaw : (fun x ↦
                ((equation447ConditionalCategoryLawOrDirac m
                  (profile (R.witnessSelectedCoordinate q hq eta x))
                  (R.profile_lt (R.witnessSelectedCoordinate q hq eta x))
                  (R.witnessHistoryFiber q hq eta
                    (R.witnessSelectedCoordinate q hq eta x))
                  (R.witnessCategoryCoordinate q hq eta x) :
                    ProbabilityMeasure (Fin 3)) : Measure (Fin 3))) =
              fun x ↦
                ((equation447ConditionalCategoryLawOrDirac m
                  (profile (R.badSelectedCoordinate q hq eta x))
                  (R.profile_lt (R.badSelectedCoordinate q hq eta x))
                  (R.badHistoryFiber q hq eta
                    (R.badSelectedCoordinate q hq eta x))
                  (R.badCategoryCoordinate q hq eta x) :
                    ProbabilityMeasure (Fin 3)) : Measure (Fin 3)) := by
            funext x
            exact congrArg ProbabilityMeasure.toMeasure
              (R.conditionalLaw_eq q hq eta x).symm
          have hmass :
              ((Measure.pi fun x ↦
                sourceTruncatedNegBinMeasure m (profile x)).prod directionLaw)
                  ((Set.pi Set.univ (R.badHistoryFiber q hq eta)) ×ˢ
                    {(0 : Direction)}) =
                ((Measure.pi fun x ↦
                  sourceTruncatedNegBinMeasure m (profile x)).prod directionLaw)
                  ((Set.pi Set.univ (R.witnessHistoryFiber q hq eta)) ×ˢ
                    {(0 : Direction)}) := by
            rw [Measure.prod_prod, Measure.prod_prod]
            simpa [sourceTruncatedProfileMeasure] using
              congrArg (fun z : ENNReal ↦ z * directionLaw {(0 : Direction)})
                (R.history_mass_eq q hq eta)
          simp only [equation447ConditionalCategoryLawOrDirac] at hlaw
          rw [← hmass, hlaw] at hfact
          simpa [witnessAtom, witnessHistory, witnessCategory, categoryLaw,
            normalizer, badHistory, hq, sourceTruncatedProfileMeasure,
            equation447ConditionalCategoryLawOrDirac] using hfact
        · have hqpos : 0 < q := by omega
          let W := categoricalWitnessLayer (ι := Fin q)
            (categoricalOptimalWitnessCount ratioC q)
          have hcat : (fun _ : ((Coord → ℕ) × Direction) ↦
                fun _ : Fin q ↦ (2 : Fin 3)) ⁻¹'
                (↑W : Set (Fin q → Fin 3)) = ∅ := by
            ext w
            simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
            intro hw
            have hbinary := categoricalWitnessLayer_binary
              (categoricalOptimalWitnessCount ratioC q) hw ⟨0, hqpos⟩
            omega
          have hpi : Measure.pi (fun _ : Fin q ↦ Measure.dirac (2 : Fin 3))
                (↑W : Set (Fin q → Fin 3)) = 0 := by
            rw [← sum_measure_singleton]
            apply Finset.sum_eq_zero
            intro z hz
            rw [Measure.pi_singleton]
            apply Finset.prod_eq_zero (i := ⟨0, hqpos⟩)
            · simp
            · have hbinary := categoricalWitnessLayer_binary
                  (categoricalOptimalWitnessCount ratioC q) hz ⟨0, hqpos⟩
              rcases hbinary with hzero | hone
              · simp [hzero]
              · simp [hone]
          simp [witnessAtom, witnessHistory, witnessCategory, categoryLaw,
            normalizer, hq, W, hcat, hpi]
      category_mass_ratio := by
        intro q eta x
        by_cases hq : q ≤ Fintype.card Coord
        · simpa [categoryLaw, hq,
            equation447ConditionalCategoryLawOrDirac] using
            (conditionalCategoryLawOrDirac_two_mass_ratio_of_inter
              (sourceTruncatedNegBinMeasure m
                (profile (R.badSelectedCoordinate q hq eta x)))
              (cond_isProbabilityMeasure
                (negBinMeasure_sourceBelowSet_ne_zero m
                  (profile (R.badSelectedCoordinate q hq eta x))
                  (R.profile_lt (R.badSelectedCoordinate q hq eta x))))
              (R.badHistoryFiber q hq eta
                (R.badSelectedCoordinate q hq eta x))
              MeasurableSet.of_discrete
              (R.badCategoryCoordinate q hq eta x)
              (measurable_of_countable _)
              ratioC (R.raw_category_mass_ratio q hq eta x))
        · simp [categoryLaw, hq, measureReal_def, Measure.dirac_apply] }

end Equation447RectangularOptimalCategoricalPathWitnessBranchCoreData

/-- Rectangular optimal categorical data together with the literal stopped
length/count certificate for (4.54). -/
structure Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (failure thetaPathEvent pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  core : Equation447RectangularOptimalCategoricalPathWitnessBranchCoreData
    cWindow m ratioC rho failure thetaPathEvent pathAtom
      profile lazyVector nextDirection
  separation : Equation447PathLengthSeparationData core.witnessAtom

namespace Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC rho : ℝ}
  {failure thetaPathEvent pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Derive the legacy length-separated package, including both finite-product
identities, from the two rectangular histories. -/
noncomputable def toLengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
    (R : Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho failure thetaPathEvent pathAtom
        profile lazyVector nextDirection) :
    Equation447LengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho failure pathAtom profile lazyVector nextDirection where
  toEquation447OptimalCategoricalPathWitnessBranchCoreData :=
    R.core.toOptimalCategoricalPathWitnessBranchCoreData
  separation := R.separation

end Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData

namespace Equation447OptimalCategoricalPathWitnessBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC rho : ℝ}
  {failure pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Derive the path-switch package once the numerical optimal-layer theorem
is available above this branch's threshold. -/
noncomputable def toRemainingData
    (R : Equation447OptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho failure pathAtom profile lazyVector nextDirection)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q, Nat.ceil rho ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    Equation447PathWitnessBranchRemainingData cWindow m
      (categoricalOptimalRate ratioC) rho
      failure pathAtom profile lazyVector nextDirection where
  Path := R.Path
  pathCountable := R.pathCountable
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  witnessAtom := R.witnessAtom
  failure_subset := R.failure_subset
  thetaPathEvent := R.thetaPathEvent
  theta_preimage_subset := R.theta_preimage_subset
  equation447_cover := R.equation447_cover
  path_switch := by
    intro q eta hq
    letI (x : Fin q) : IsProbabilityMeasure
        (R.categoryLaw q eta x : Measure (Fin 3)) :=
      (R.categoryLaw q eta x).prop
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      (measure_bad_le_exp_mul_witness_of_conditional_categorical_layer
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
        (R.badAtom q eta) (R.witnessAtom q eta)
        (R.badHistory q eta) (R.witnessHistory q eta)
        (R.normalizer q eta)
        (R.badCategory q eta) (R.witnessCategory q eta)
        (fun x ↦ (R.categoryLaw q eta x : Measure (Fin 3)))
        ratioC (categoricalOptimalRate ratioC) hC.le
        (categoricalOptimalWitnessCount ratioC q)
        (by simpa using categoricalOptimalWitnessCount_le ratioC q)
        (R.bad_subset q eta) (R.witness_subset q eta)
        (R.bad_conditional_product q eta)
        (R.witness_conditional_product q eta)
        (R.category_mass_ratio q eta) (by simpa using hbinomial q hq))
  witness_disjoint := R.witness_disjoint
  witness_measurable := by
    intro q eta
    exact (Set.to_countable (R.witnessAtom q eta)).measurableSet

end Equation447OptimalCategoricalPathWitnessBranchRemainingData

/-- A strictly more primitive source interface for the deleted-path switch.
The source supplies an actual injective transformation from each bad atom to
its witness atom and compares the two singleton probabilities.  The
set-level `path_switch` inequality and measurability of the witness atoms are
then theorems of countable discrete measure theory, not assumptions.

This is the appropriate interface for formalizing the path modification in
HLOZ (4.51)--(4.54): the remaining mathematical work is exactly the
combinatorial injectivity and the likelihood ratio of one modified path. -/
structure Equation447InjectivePathWitnessBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (c rho : ℝ)
    (failure pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  Path : Type
  [pathCountable : Countable Path]
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  badAtom : ℕ → Path → Set ((Coord → ℕ) × Direction)
  witnessAtom : ℕ → Path → Set ((Coord → ℕ) × Direction)
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ D) ×ˢ
        (Set.univ : Set Direction))
  thetaPathEvent : Set (ℕ → Site)
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent
  equation447_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta, badAtom q eta
  switch : ∀ q, Path → ((Coord → ℕ) × Direction) →
    ((Coord → ℕ) × Direction)
  switch_mapsTo : ∀ q eta,
    Set.MapsTo (switch q eta) (badAtom q eta) (witnessAtom q eta)
  switch_injective : ∀ q eta,
    Set.InjOn (switch q eta) (badAtom q eta)
  switch_point_mass : ∀ q eta z, z ∈ badAtom q eta →
    ((sourceTruncatedProfileMeasure m profile).prod directionLaw) {z} ≤
      ENNReal.ofReal (Real.exp (-c * (q : ℝ))) *
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
          {switch q eta z}
  witness_disjoint : ∀ q, Pairwise fun eta zeta ↦
    Disjoint (witnessAtom q eta) (witnessAtom q zeta)

namespace Equation447InjectivePathWitnessBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {c rho : ℝ}
  {failure pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Sum the pointwise injective source switch to obtain the existing
path-witness record consumed by the equation-(4.47) connector. -/
noncomputable def toRemainingData
    (R : Equation447InjectivePathWitnessBranchRemainingData cWindow m c rho
      failure pathAtom profile lazyVector nextDirection) :
    Equation447PathWitnessBranchRemainingData cWindow m c rho
      failure pathAtom profile lazyVector nextDirection where
  Path := R.Path
  pathCountable := R.pathCountable
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  witnessAtom := R.witnessAtom
  failure_subset := R.failure_subset
  thetaPathEvent := R.thetaPathEvent
  theta_preimage_subset := R.theta_preimage_subset
  equation447_cover := R.equation447_cover
  path_switch := by
    intro q eta _hq
    exact measure_le_mul_measure_of_injective_point_switch
      ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
      (R.badAtom q eta) (R.witnessAtom q eta)
      (ENNReal.ofReal (Real.exp (-c * (q : ℝ))))
      (R.switch q eta) (R.switch_mapsTo q eta)
      (R.switch_injective q eta) (R.switch_point_mass q eta)
  witness_disjoint := R.witness_disjoint
  witness_measurable := by
    intro q eta
    exact (Set.to_countable (R.witnessAtom q eta)).measurableSet

end Equation447InjectivePathWitnessBranchRemainingData

namespace Equation447PathWitnessBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {c rho : ℝ}
  {failure pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Assemble the literal path-switch atom once a stopped source has supplied
its already-proved product map law.  The four parity/winner source records
below instantiate this definition, so callers never assume that map law. -/
noncomputable def toStoppedEquation447PathWitnessBranchAtom
    (R : Equation447PathWitnessBranchRemainingData cWindow m c rho
      failure pathAtom profile lazyVector nextDirection)
    (hmeasPath : MeasurableSet pathAtom)
    (hprofile : ∀ x, profile x < m)
    (hmeasLazy : Measurable lazyVector)
    (hmeasNext : Measurable nextDirection)
    (hmap :
      (simpleRandomWalkLaw.restrict pathAtom).map
          (fun s ↦ (lazyVector s, nextDirection s)) =
        simpleRandomWalkLaw pathAtom •
          ((sourceTruncatedProfileMeasure m profile).prod directionLaw)) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c failure rho where
  Coord := Coord
  coordFintype := inferInstance
  Path := R.Path
  pathCountable := R.pathCountable
  pathAtom := pathAtom
  measurableSet_pathAtom := hmeasPath
  profile := profile
  profile_lt := hprofile
  lazyVector := lazyVector
  measurable_lazyVector := hmeasLazy
  nextDirection := nextDirection
  measurable_nextDirection := hmeasNext
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  witnessAtom := R.witnessAtom
  map_law := hmap
  failure_subset := R.failure_subset
  thetaPathEvent := R.thetaPathEvent
  theta_preimage_subset := R.theta_preimage_subset
  equation447_cover := R.equation447_cover
  path_switch := R.path_switch
  witness_disjoint := R.witness_disjoint
  witness_measurable := R.witness_measurable

end Equation447PathWitnessBranchRemainingData

/-- Source-facing form of the remaining equation-(4.47) data in which the
history atoms are literal fibers of one measurable history code.  Their
pairwise disjointness and measurability are therefore consequences, not
independent source assumptions. -/
structure Equation447CodedBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (failure thetaPathEvent pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  historyCode : ∀ _q, ((Coord → ℕ) × Direction) → (Coord → ℕ)
  category : ∀ q, (Coord → ℕ) →
    ((Coord → ℕ) × Direction) → Fin q → Fin 3
  categoryLaw : ∀ q, (Coord → ℕ) → Fin q → ProbabilityMeasure (Fin 3)
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ D) ×ˢ
        (Set.univ : Set Direction))
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent
  equation447_history_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta,
        (historyCode q ⁻¹' {eta}) ∩
          category q eta ⁻¹' {allUpperConfig}
  conditional_category_product : ∀ q eta,
    (sourceTruncatedProfileMeasure m profile).prod directionLaw
        ((historyCode q ⁻¹' {eta}) ∩
          category q eta ⁻¹' {allUpperConfig}) =
      (sourceTruncatedProfileMeasure m profile).prod directionLaw
          (historyCode q ⁻¹' {eta}) *
        Measure.pi (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
          {allUpperConfig}
  category_mass_ratio : ∀ q eta x,
    ((categoryLaw q eta x : Measure (Fin 3))).real {0} ≤
      ratioC * ((categoryLaw q eta x : Measure (Fin 3))).real {1}

namespace Equation447CodedBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC rho : ℝ}
  {failure thetaPathEvent pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- A coded history package supplies the older core record with its two
set-theoretic fields proved canonically from fibers. -/
noncomputable def toRemainingData
    (R : Equation447CodedBranchRemainingData cWindow m ratioC rho
      failure thetaPathEvent pathAtom profile lazyVector nextDirection) :
    Equation447BranchRemainingData cWindow m ratioC rho
      failure pathAtom profile lazyVector nextDirection where
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := fun q eta ↦
    (R.historyCode q ⁻¹' {eta}) ∩
      R.category q eta ⁻¹' {allUpperConfig}
  historyAtom := fun q eta ↦ R.historyCode q ⁻¹' {eta}
  category := R.category
  categoryLaw := fun q eta x ↦ (R.categoryLaw q eta x : Measure (Fin 3))
  categoryLaw_probability := by
    intro q eta x
    exact (R.categoryLaw q eta x).prop
  failure_subset := R.failure_subset
  thetaPathEvent := thetaPathEvent
  theta_preimage_subset := R.theta_preimage_subset
  equation447_cover := R.equation447_history_cover
  bad_subset_history_allUpper := by
    intro q eta
    exact le_rfl
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := by
    intro q eta zeta hne
    rw [Set.disjoint_left]
    intro w hwEta hwZeta
    have heta : R.historyCode q w = eta := by simpa using hwEta
    have hzeta : R.historyCode q w = zeta := by simpa using hwZeta
    exact hne (heta.symm.trans hzeta)
  history_measurable := by
    intro q eta
    exact (MeasurableSet.singleton eta).preimage
      (measurable_of_countable (R.historyCode q))

end Equation447CodedBranchRemainingData

/-- The fixed-profile part of equation (4.47), with no auxiliary path-space
failure or profile-exception event.  Proposition 4.8 uses exactly this data:
its base estimate is proved under the truncated profile law before any event
is transported back to paths. -/
structure Equation447CodedProfileData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC : ℝ)
    (profile : Coord → ℕ) where
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  historyCode : ∀ _q, ((Coord → ℕ) × Direction) → (Coord → ℕ)
  category : ∀ q, (Coord → ℕ) →
    ((Coord → ℕ) × Direction) → Fin q → Fin 3
  categoryLaw : ∀ q, (Coord → ℕ) → Fin q → ProbabilityMeasure (Fin 3)
  equation447_history_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta,
        (historyCode q ⁻¹' {eta}) ∩
          category q eta ⁻¹' {allUpperConfig}
  conditional_category_product : ∀ q eta,
    (sourceTruncatedProfileMeasure m profile).prod directionLaw
        ((historyCode q ⁻¹' {eta}) ∩
          category q eta ⁻¹' {allUpperConfig}) =
      (sourceTruncatedProfileMeasure m profile).prod directionLaw
          (historyCode q ⁻¹' {eta}) *
        Measure.pi (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
          {allUpperConfig}
  category_mass_ratio : ∀ q eta x,
    ((categoryLaw q eta x : Measure (Fin 3))).real {0} ≤
      ratioC * ((categoryLaw q eta x : Measure (Fin 3))).real {1}

namespace Equation447CodedProfileData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC rho : ℝ}
  {profile : Coord → ℕ}

/-- Supply the legacy branch-shaped consumer with empty failure and universal
path exception.  Neither dummy field is inspected by the fixed-profile
Proposition-4.8 theorem. -/
noncomputable def toRemainingData
    (R : Equation447CodedProfileData cWindow m ratioC profile)
    (pathAtom : Set (ℕ → Site))
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) :
    Equation447BranchRemainingData cWindow m ratioC rho
      ∅ pathAtom profile lazyVector nextDirection where
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := fun q eta ↦
    (R.historyCode q ⁻¹' {eta}) ∩
      R.category q eta ⁻¹' {allUpperConfig}
  historyAtom := fun q eta ↦ R.historyCode q ⁻¹' {eta}
  category := R.category
  categoryLaw := fun q eta x ↦ (R.categoryLaw q eta x : Measure (Fin 3))
  categoryLaw_probability := by
    intro q eta x
    exact (R.categoryLaw q eta x).prop
  failure_subset := by simp
  thetaPathEvent := Set.univ
  theta_preimage_subset := by simp
  equation447_cover := R.equation447_history_cover
  bad_subset_history_allUpper := by
    intro q eta
    exact le_rfl
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := by
    intro q eta zeta hne
    rw [Set.disjoint_left]
    intro w hwEta hwZeta
    have heta : R.historyCode q w = eta := by simpa using hwEta
    have hzeta : R.historyCode q w = zeta := by simpa using hwZeta
    exact hne (heta.symm.trans hzeta)
  history_measurable := by
    intro q eta
    exact (MeasurableSet.singleton eta).preimage
      (measurable_of_countable (R.historyCode q))

end Equation447CodedProfileData

/-- Coordinatewise source form of the equation-(4.47) history/category
decomposition.

Instead of assuming a conditional-product equality, the source identifies
each history-code fiber with a rectangle of coordinate events together with
an independent direction event.  The finite product identity is then a
theorem.  No history-fiber positivity is required: if any coordinate fiber
is null, the entire history rectangle is null and the factorization is
automatic; a null selected coordinate uses a harmless Dirac law in the
unused third category.  The deterministic cover and one-coordinate
adjacent-band ratio remain. -/
structure Equation447CoordinatewiseProfileData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC : ℝ)
    (profile : Coord → ℕ) where
  profile_lt : ∀ x, profile x < m
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  historyCode : ∀ _q, ((Coord → ℕ) × Direction) → (Coord → ℕ)
  historyFiber : ∀ q, (Coord → ℕ) → Coord → Set ℕ
  directionHistory : ∀ q, (Coord → ℕ) → Set Direction
  selectedCoordinate : ∀ q, (Coord → ℕ) → Fin q → Coord
  selectedCoordinate_injective : ∀ q eta,
    Function.Injective (selectedCoordinate q eta)
  categoryCoordinate : ∀ q, (Coord → ℕ) → Fin q → ℕ → Fin 3
  historyCode_fiber : ∀ q eta,
    historyCode q ⁻¹' {eta} =
      (Set.pi Set.univ (historyFiber q eta)) ×ˢ
        directionHistory q eta
  equation447_history_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta,
        ((Set.pi Set.univ (historyFiber q eta)) ×ˢ
          directionHistory q eta) ∩
            (fun w x ↦ categoryCoordinate q eta x
              (w.1 (selectedCoordinate q eta x))) ⁻¹'
              {allUpperConfig}
  category_mass_ratio : ∀ q eta x,
    ((conditionalCategoryLawOrDirac
      (sourceTruncatedNegBinMeasure m
        (profile (selectedCoordinate q eta x)))
      (cond_isProbabilityMeasure
        (negBinMeasure_sourceBelowSet_ne_zero m
          (profile (selectedCoordinate q eta x))
          (profile_lt (selectedCoordinate q eta x))))
      (historyFiber q eta (selectedCoordinate q eta x))
      MeasurableSet.of_discrete
      (categoryCoordinate q eta x) (measurable_of_countable _) 2 :
        ProbabilityMeasure (Fin 3)) : Measure (Fin 3)).real {0} ≤
      ratioC *
        ((conditionalCategoryLawOrDirac
          (sourceTruncatedNegBinMeasure m
            (profile (selectedCoordinate q eta x)))
          (cond_isProbabilityMeasure
            (negBinMeasure_sourceBelowSet_ne_zero m
              (profile (selectedCoordinate q eta x))
              (profile_lt (selectedCoordinate q eta x))))
          (historyFiber q eta (selectedCoordinate q eta x))
          MeasurableSet.of_discrete
          (categoryCoordinate q eta x) (measurable_of_countable _) 2 :
            ProbabilityMeasure (Fin 3)) : Measure (Fin 3)).real {1}

namespace Equation447CoordinatewiseProfileData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC : ℝ} {profile : Coord → ℕ}

/-- Coordinate rectangles automatically supply the coded fixed-profile
record, including the exact conditional categorical product. -/
noncomputable def toCodedProfileData
    (R : Equation447CoordinatewiseProfileData
      cWindow m ratioC profile) :
    Equation447CodedProfileData cWindow m ratioC profile := by
  letI (x : Coord) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (R.profile_lt x))
  let categoryLaw : ∀ q, (Coord → ℕ) → Fin q → ProbabilityMeasure (Fin 3) :=
    fun q eta x ↦ conditionalCategoryLawOrDirac
      (sourceTruncatedNegBinMeasure m
        (profile (R.selectedCoordinate q eta x)))
      inferInstance
      (R.historyFiber q eta (R.selectedCoordinate q eta x))
      MeasurableSet.of_discrete
      (R.categoryCoordinate q eta x) (measurable_of_countable _) 2
  exact
    { forcedDirection := R.forcedDirection
      D := R.D
      historyCode := R.historyCode
      category := fun q eta w x ↦ R.categoryCoordinate q eta x
        (w.1 (R.selectedCoordinate q eta x))
      categoryLaw := categoryLaw
      equation447_history_cover := by
        intro q
        simpa only [R.historyCode_fiber] using R.equation447_history_cover q
      conditional_category_product := by
        intro q eta
        rw [R.historyCode_fiber]
        simpa only [sourceTruncatedProfileMeasure, categoryLaw] using
          (pi_prod_history_selected_category_factorization_or_dirac
            (fun x ↦ sourceTruncatedNegBinMeasure m (profile x))
            directionLaw (R.historyFiber q eta)
            (fun _ ↦ MeasurableSet.of_discrete)
            (R.directionHistory q eta) (R.selectedCoordinate q eta)
            (R.selectedCoordinate_injective q eta)
            (R.categoryCoordinate q eta)
            (fun _ ↦ measurable_of_countable _)
            (fun _ ↦ (2 : Fin 3))
            allUpperConfig)
      category_mass_ratio := by
        intro q eta x
        simpa only [categoryLaw] using R.category_mass_ratio q eta x }

end Equation447CoordinatewiseProfileData

/-! ### Feasible-count coordinate data

`sourceEquation447ByCount ... q` is empty once `q` is larger than the finite
coordinate type.  A literal source package should therefore provide an
injective enumeration only for feasible `q`; asking for one at every natural
number would make the record inconsistent.  The bounded record below is the
constructible source interface.  Its converter fills infeasible counts with
an inactive Dirac category, for which both the count atom and the all-upper
category event are empty. -/

/-- Coordinatewise equation-(4.47) data only at feasible finite counts. -/
structure Equation447BoundedCoordinatewiseProfileData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC : ℝ)
    (profile : Coord → ℕ) where
  profile_lt : ∀ x, profile x < m
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  historyCode : ∀ _q, ((Coord → ℕ) × Direction) → (Coord → ℕ)
  historyFiber : ∀ q, q ≤ Fintype.card Coord →
    (Coord → ℕ) → Coord → Set ℕ
  directionHistory : ∀ q, q ≤ Fintype.card Coord →
    (Coord → ℕ) → Set Direction
  selectedCoordinate : ∀ q, q ≤ Fintype.card Coord →
    (Coord → ℕ) → Fin q → Coord
  selectedCoordinate_injective : ∀ q hq eta,
    Function.Injective (selectedCoordinate q hq eta)
  categoryCoordinate : ∀ q, q ≤ Fintype.card Coord →
    (Coord → ℕ) → Fin q → ℕ → Fin 3
  historyCode_fiber : ∀ q hq eta,
    historyCode q ⁻¹' {eta} =
      (Set.pi Set.univ (historyFiber q hq eta)) ×ˢ
        directionHistory q hq eta
  equation447_history_cover : ∀ q hq,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta,
        ((Set.pi Set.univ (historyFiber q hq eta)) ×ˢ
          directionHistory q hq eta) ∩
            (fun w x ↦ categoryCoordinate q hq eta x
              (w.1 (selectedCoordinate q hq eta x))) ⁻¹'
              {@allUpperConfig (Fin q)}
  category_mass_ratio : ∀ q hq eta x,
    ((conditionalCategoryLawOrDirac
      (sourceTruncatedNegBinMeasure m
        (profile (selectedCoordinate q hq eta x)))
      (cond_isProbabilityMeasure
        (negBinMeasure_sourceBelowSet_ne_zero m
          (profile (selectedCoordinate q hq eta x))
          (profile_lt (selectedCoordinate q hq eta x))))
      (historyFiber q hq eta (selectedCoordinate q hq eta x))
      MeasurableSet.of_discrete
      (categoryCoordinate q hq eta x) (measurable_of_countable _) 2 :
        ProbabilityMeasure (Fin 3)) : Measure (Fin 3)).real {0} ≤
      ratioC *
        ((conditionalCategoryLawOrDirac
          (sourceTruncatedNegBinMeasure m
            (profile (selectedCoordinate q hq eta x)))
          (cond_isProbabilityMeasure
            (negBinMeasure_sourceBelowSet_ne_zero m
              (profile (selectedCoordinate q hq eta x))
              (profile_lt (selectedCoordinate q hq eta x))))
          (historyFiber q hq eta (selectedCoordinate q hq eta x))
          MeasurableSet.of_discrete
          (categoryCoordinate q hq eta x) (measurable_of_countable _) 2 :
            ProbabilityMeasure (Fin 3)) : Measure (Fin 3)).real {1}

namespace Equation447BoundedCoordinatewiseProfileData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC : ℝ} {profile : Coord → ℕ}

/-- Totalize feasible-count coordinate data to the fixed-profile record.
For an infeasible count the exact count atom is empty, and the inactive
Dirac category makes the conditional product identity `0 = 0`. -/
noncomputable def toCodedProfileData
    (R : Equation447BoundedCoordinatewiseProfileData
      cWindow m ratioC profile) :
    Equation447CodedProfileData cWindow m ratioC profile := by
  letI (x : Coord) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (R.profile_lt x))
  let category : ∀ q, (Coord → ℕ) →
      ((Coord → ℕ) × Direction) → Fin q → Fin 3 :=
    fun q eta w ↦ if hq : q ≤ Fintype.card Coord then
      fun x ↦ R.categoryCoordinate q hq eta x
        (w.1 (R.selectedCoordinate q hq eta x))
    else fun _ ↦ 2
  let categoryLaw : ∀ q, (Coord → ℕ) → Fin q →
      ProbabilityMeasure (Fin 3) :=
    fun q eta x ↦ if hq : q ≤ Fintype.card Coord then
      conditionalCategoryLawOrDirac
        (sourceTruncatedNegBinMeasure m
          (profile (R.selectedCoordinate q hq eta x)))
        inferInstance
        (R.historyFiber q hq eta (R.selectedCoordinate q hq eta x))
        MeasurableSet.of_discrete
        (R.categoryCoordinate q hq eta x) (measurable_of_countable _) 2
    else ⟨Measure.dirac 2, Measure.dirac.isProbabilityMeasure⟩
  exact
    { forcedDirection := R.forcedDirection
      D := R.D
      historyCode := R.historyCode
      category := category
      categoryLaw := categoryLaw
      equation447_history_cover := by
        intro q
        by_cases hq : q ≤ Fintype.card Coord
        · simpa only [category, dif_pos hq, R.historyCode_fiber q hq] using
            R.equation447_history_cover q hq
        · rw [sourceEquation447ByCount_eq_empty_of_card_lt cWindow m profile
              R.D Set.univ q (Nat.lt_of_not_ge hq)]
          simp
      conditional_category_product := by
        intro q eta
        by_cases hq : q ≤ Fintype.card Coord
        · rw [R.historyCode_fiber q hq eta]
          simpa [sourceTruncatedProfileMeasure, category, categoryLaw, hq] using
            (pi_prod_history_selected_category_factorization_or_dirac
              (fun x ↦ sourceTruncatedNegBinMeasure m (profile x))
              directionLaw (R.historyFiber q hq eta)
              (fun _ ↦ MeasurableSet.of_discrete)
              (R.directionHistory q hq eta) (R.selectedCoordinate q hq eta)
              (R.selectedCoordinate_injective q hq eta)
              (R.categoryCoordinate q hq eta)
              (fun _ ↦ measurable_of_countable _)
              (fun _ ↦ (2 : Fin 3))
              (@allUpperConfig (Fin q)))
        · have hqpos : 0 < q := by omega
          have hcat : (fun _ : ((Coord → ℕ) × Direction) ↦
                fun _ : Fin q ↦ (2 : Fin 3)) ⁻¹'
                ({@allUpperConfig (Fin q)} : Set (Fin q → Fin 3)) = ∅ := by
              ext w
              constructor
              · intro hw
                have heq : (fun _ : Fin q ↦ (2 : Fin 3)) =
                    @allUpperConfig (Fin q) := by simpa using hw
                have hbad := congrFun heq ⟨0, hqpos⟩
                norm_num [allUpperConfig] at hbad
                omega
              · simp
          have hpi : Measure.pi (fun _ : Fin q ↦ Measure.dirac (2 : Fin 3))
                ({@allUpperConfig (Fin q)} : Set (Fin q → Fin 3)) = 0 := by
              rw [Measure.pi_singleton]
              apply Finset.prod_eq_zero (i := ⟨0, hqpos⟩)
              · simp
              · simp [allUpperConfig]
          have hpi' : Measure.pi
                (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
                ({@allUpperConfig (Fin q)} : Set (Fin q → Fin 3)) = 0 := by
            simpa [categoryLaw, hq] using hpi
          simp only [category, dif_neg hq]
          rw [hcat, Set.inter_empty, measure_empty, hpi', mul_zero]
      category_mass_ratio := by
        intro q eta x
        by_cases hq : q ≤ Fintype.card Coord
        · simpa [categoryLaw, hq] using R.category_mass_ratio q hq eta x
        · simp [categoryLaw, hq, measureReal_def, Measure.dirac_apply] }

/-- Feasible-count rectangular data also supplies the complete canonical
finite witness layer used by the deleted-path switch.

The path index is the history-code value itself.  Consequently distinct
witness atoms are disjoint without any additional source premise.  For
feasible counts the two conditional products follow from the finite-layer
factorization theorem; for infeasible counts the inactive category `2`
belongs to neither the all-upper cell nor the binary witness layer. -/
noncomputable def toOptimalCategoricalPathWitnessBranchRemainingData
    (R : Equation447BoundedCoordinatewiseProfileData
      cWindow m ratioC profile)
    (rho : ℝ) (failure thetaPathEvent pathAtom : Set (ℕ → Site))
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction)
    (failure_subset :
      failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        ((sourceProfileQEvent m 1 profile rho ∩ R.D) ×ˢ
          (Set.univ : Set Direction)))
    (theta_preimage_subset :
      pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
          (sourceProfileThetaBad cWindow m 1 profile ×ˢ
            (Set.univ : Set Direction)) ⊆ thetaPathEvent) :
    Equation447OptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC rho failure pathAtom profile lazyVector
        nextDirection := by
  letI (x : Coord) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (R.profile_lt x))
  let category : ∀ q, (Coord → ℕ) →
      ((Coord → ℕ) × Direction) → Fin q → Fin 3 :=
    fun q eta w ↦ if hq : q ≤ Fintype.card Coord then
      fun x ↦ R.categoryCoordinate q hq eta x
        (w.1 (R.selectedCoordinate q hq eta x))
    else fun _ ↦ 2
  let categoryLaw : ∀ q, (Coord → ℕ) → Fin q →
      ProbabilityMeasure (Fin 3) :=
    fun q eta x ↦ if hq : q ≤ Fintype.card Coord then
      conditionalCategoryLawOrDirac
        (sourceTruncatedNegBinMeasure m
          (profile (R.selectedCoordinate q hq eta x)))
        inferInstance
        (R.historyFiber q hq eta (R.selectedCoordinate q hq eta x))
        MeasurableSet.of_discrete
        (R.categoryCoordinate q hq eta x) (measurable_of_countable _) 2
    else ⟨Measure.dirac 2, Measure.dirac.isProbabilityMeasure⟩
  let historyAtom : ∀ q, (Coord → ℕ) →
      Set ((Coord → ℕ) × Direction) :=
    fun q eta ↦ R.historyCode q ⁻¹' {eta}
  let badAtom : ∀ q, (Coord → ℕ) →
      Set ((Coord → ℕ) × Direction) :=
    fun q eta ↦ historyAtom q eta ∩
      category q eta ⁻¹' {@allUpperConfig (Fin q)}
  let witnessAtom : ∀ q, (Coord → ℕ) →
      Set ((Coord → ℕ) × Direction) :=
    fun q eta ↦ historyAtom q eta ∩ category q eta ⁻¹'
      (↑(categoricalWitnessLayer (ι := Fin q)
        (categoricalOptimalWitnessCount ratioC q)) : Set (Fin q → Fin 3))
  exact
    { Path := Coord → ℕ
      pathCountable := inferInstance
      forcedDirection := R.forcedDirection
      D := R.D
      badAtom := badAtom
      witnessAtom := witnessAtom
      badHistory := historyAtom
      witnessHistory := historyAtom
      normalizer := fun q eta ↦
        (sourceTruncatedProfileMeasure m profile).prod directionLaw
          (historyAtom q eta)
      badCategory := category
      witnessCategory := category
      categoryLaw := categoryLaw
      failure_subset := failure_subset
      thetaPathEvent := thetaPathEvent
      theta_preimage_subset := theta_preimage_subset
      equation447_cover := by
        intro q
        by_cases hq : q ≤ Fintype.card Coord
        · simpa only [badAtom, historyAtom, category, dif_pos hq,
            R.historyCode_fiber q hq] using
            R.equation447_history_cover q hq
        · rw [sourceEquation447ByCount_eq_empty_of_card_lt cWindow m profile
              R.D Set.univ q (Nat.lt_of_not_ge hq)]
          simp
      bad_subset := by
        intro q eta
        exact le_rfl
      witness_subset := by
        intro q eta
        exact le_rfl
      bad_conditional_product := by
        intro q eta
        by_cases hq : q ≤ Fintype.card Coord
        · simp only [historyAtom]
          rw [R.historyCode_fiber q hq eta]
          simpa [sourceTruncatedProfileMeasure, historyAtom, category,
            categoryLaw, hq] using
            (pi_prod_history_selected_category_finset_factorization_or_dirac
              (fun x ↦ sourceTruncatedNegBinMeasure m (profile x))
              directionLaw (R.historyFiber q hq eta)
              (fun _ ↦ MeasurableSet.of_discrete)
              (R.directionHistory q hq eta) (R.selectedCoordinate q hq eta)
              (R.selectedCoordinate_injective q hq eta)
              (R.categoryCoordinate q hq eta)
              (fun _ ↦ measurable_of_countable _)
              (fun _ ↦ (2 : Fin 3))
              ({@allUpperConfig (Fin q)} : Finset (Fin q → Fin 3)))
        · have hqpos : 0 < q := by omega
          have hcat : (fun _ : ((Coord → ℕ) × Direction) ↦
                fun _ : Fin q ↦ (2 : Fin 3)) ⁻¹'
                ({@allUpperConfig (Fin q)} : Set (Fin q → Fin 3)) = ∅ := by
              ext w
              constructor
              · intro hw
                have heq : (fun _ : Fin q ↦ (2 : Fin 3)) =
                    @allUpperConfig (Fin q) := by simpa using hw
                have hbad := congrFun heq ⟨0, hqpos⟩
                norm_num [allUpperConfig] at hbad
                omega
              · simp
          have hpi : Measure.pi (fun _ : Fin q ↦ Measure.dirac (2 : Fin 3))
                ({@allUpperConfig (Fin q)} : Set (Fin q → Fin 3)) = 0 := by
              rw [Measure.pi_singleton]
              apply Finset.prod_eq_zero (i := ⟨0, hqpos⟩)
              · simp
              · simp [allUpperConfig]
          have hpi' : Measure.pi
                (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
                ({@allUpperConfig (Fin q)} : Set (Fin q → Fin 3)) = 0 := by
            simpa [categoryLaw, hq] using hpi
          simp only [historyAtom, category, dif_neg hq]
          rw [hcat, Set.inter_empty, measure_empty, hpi', mul_zero]
      witness_conditional_product := by
        intro q eta
        by_cases hq : q ≤ Fintype.card Coord
        · simp only [historyAtom]
          rw [R.historyCode_fiber q hq eta]
          simpa [sourceTruncatedProfileMeasure, historyAtom, category,
            categoryLaw, hq] using
            (pi_prod_history_selected_category_finset_factorization_or_dirac
              (fun x ↦ sourceTruncatedNegBinMeasure m (profile x))
              directionLaw (R.historyFiber q hq eta)
              (fun _ ↦ MeasurableSet.of_discrete)
              (R.directionHistory q hq eta) (R.selectedCoordinate q hq eta)
              (R.selectedCoordinate_injective q hq eta)
              (R.categoryCoordinate q hq eta)
              (fun _ ↦ measurable_of_countable _)
              (fun _ ↦ (2 : Fin 3))
              (categoricalWitnessLayer (ι := Fin q)
                (categoricalOptimalWitnessCount ratioC q)))
        · have hqpos : 0 < q := by omega
          let W := categoricalWitnessLayer (ι := Fin q)
            (categoricalOptimalWitnessCount ratioC q)
          have hcat : (fun _ : ((Coord → ℕ) × Direction) ↦
                fun _ : Fin q ↦ (2 : Fin 3)) ⁻¹'
                (↑W : Set (Fin q → Fin 3)) = ∅ := by
              ext w
              simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
              intro hw
              have hbinary := categoricalWitnessLayer_binary
                (categoricalOptimalWitnessCount ratioC q) hw ⟨0, hqpos⟩
              omega
          have hpi : Measure.pi (fun _ : Fin q ↦ Measure.dirac (2 : Fin 3))
                (↑W : Set (Fin q → Fin 3)) = 0 := by
              rw [← sum_measure_singleton]
              apply Finset.sum_eq_zero
              intro z hz
              rw [Measure.pi_singleton]
              apply Finset.prod_eq_zero (i := ⟨0, hqpos⟩)
              · simp
              · have hbinary := categoricalWitnessLayer_binary
                    (categoricalOptimalWitnessCount ratioC q) hz ⟨0, hqpos⟩
                rcases hbinary with hzero | hone
                · simp [hzero]
                · simp [hone]
          have hpi' : Measure.pi
                (fun x ↦ (categoryLaw q eta x : Measure (Fin 3)))
                (↑W : Set (Fin q → Fin 3)) = 0 := by
            simpa [categoryLaw, hq] using hpi
          simp only [historyAtom, category, dif_neg hq]
          rw [show (↑(categoricalWitnessLayer (ι := Fin q)
                (categoricalOptimalWitnessCount ratioC q)) :
                Set (Fin q → Fin 3)) = (↑W : Set (Fin q → Fin 3)) by rfl]
          rw [hcat, Set.inter_empty, measure_empty, hpi', mul_zero]
      category_mass_ratio := by
        intro q eta x
        by_cases hq : q ≤ Fintype.card Coord
        · simpa [categoryLaw, hq] using R.category_mass_ratio q hq eta x
        · simp [categoryLaw, hq, measureReal_def, Measure.dirac_apply]
      witness_disjoint := by
        intro q eta zeta hne
        rw [Set.disjoint_left]
        intro w hwEta hwZeta
        have heta : R.historyCode q w = eta := by
          simpa only [witnessAtom, historyAtom, Set.mem_inter_iff,
            Set.mem_preimage, Set.mem_singleton_iff] using hwEta.1
        have hzeta : R.historyCode q w = zeta := by
          simpa only [witnessAtom, historyAtom, Set.mem_inter_iff,
            Set.mem_preimage, Set.mem_singleton_iff] using hwZeta.1
        exact hne (heta.symm.trans hzeta) }

end Equation447BoundedCoordinatewiseProfileData

/-- Still more literal coordinatewise data for equation (4.47).

The source need not formulate a ratio between two already-conditioned
probabilities.  It supplies the ratio for the two raw category intersections
inside the same one-coordinate history fiber.  For a nonnull fiber the common
conditional normalizer cancels; for a null fiber the fallback third-category
Dirac law makes both displayed masses zero. -/
structure Equation447RawRectangularProfileData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC : ℝ)
    (profile : Coord → ℕ) where
  profile_lt : ∀ x, profile x < m
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  historyCode : ∀ _q, ((Coord → ℕ) × Direction) → (Coord → ℕ)
  historyFiber : ∀ q, (Coord → ℕ) → Coord → Set ℕ
  directionHistory : ∀ q, (Coord → ℕ) → Set Direction
  selectedCoordinate : ∀ q, (Coord → ℕ) → Fin q → Coord
  selectedCoordinate_injective : ∀ q eta,
    Function.Injective (selectedCoordinate q eta)
  categoryCoordinate : ∀ q, (Coord → ℕ) → Fin q → ℕ → Fin 3
  historyCode_fiber : ∀ q eta,
    historyCode q ⁻¹' {eta} =
      (Set.pi Set.univ (historyFiber q eta)) ×ˢ
        directionHistory q eta
  equation447_history_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta,
        ((Set.pi Set.univ (historyFiber q eta)) ×ˢ
          directionHistory q eta) ∩
            (fun w x ↦ categoryCoordinate q eta x
              (w.1 (selectedCoordinate q eta x))) ⁻¹'
              {allUpperConfig}
  raw_category_mass_ratio : ∀ q eta x,
    (sourceTruncatedNegBinMeasure m
      (profile (selectedCoordinate q eta x))).real
        (historyFiber q eta (selectedCoordinate q eta x) ∩
          categoryCoordinate q eta x ⁻¹' ({0} : Set (Fin 3))) ≤
      ratioC *
        (sourceTruncatedNegBinMeasure m
          (profile (selectedCoordinate q eta x))).real
          (historyFiber q eta (selectedCoordinate q eta x) ∩
            categoryCoordinate q eta x ⁻¹' ({1} : Set (Fin 3)))

namespace Equation447RawRectangularProfileData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC : ℝ} {profile : Coord → ℕ}

/-- Raw history-intersection ratios supply the conditional coordinate ratios
required by the finite product connector. -/
noncomputable def toCoordinatewiseProfileData
    (R : Equation447RawRectangularProfileData
      cWindow m ratioC profile) :
    Equation447CoordinatewiseProfileData
      cWindow m ratioC profile where
  profile_lt := R.profile_lt
  forcedDirection := R.forcedDirection
  D := R.D
  historyCode := R.historyCode
  historyFiber := R.historyFiber
  directionHistory := R.directionHistory
  selectedCoordinate := R.selectedCoordinate
  selectedCoordinate_injective := R.selectedCoordinate_injective
  categoryCoordinate := R.categoryCoordinate
  historyCode_fiber := R.historyCode_fiber
  equation447_history_cover := R.equation447_history_cover
  category_mass_ratio := by
    intro q eta x
    exact conditionalCategoryLawOrDirac_two_mass_ratio_of_inter
      (sourceTruncatedNegBinMeasure m
        (profile (R.selectedCoordinate q eta x)))
      (cond_isProbabilityMeasure
        (negBinMeasure_sourceBelowSet_ne_zero m
          (profile (R.selectedCoordinate q eta x))
          (R.profile_lt (R.selectedCoordinate q eta x))))
      (R.historyFiber q eta (R.selectedCoordinate q eta x))
      MeasurableSet.of_discrete
      (R.categoryCoordinate q eta x) (measurable_of_countable _)
      ratioC (R.raw_category_mass_ratio q eta x)

end Equation447RawRectangularProfileData

/-- Finite-cell presentation of the raw coordinate ratio.

For every selected coordinate the two relevant pieces of the history fiber
are identified with equal-cardinality finite cells.  A pointwise comparison
of their negative-binomial singleton masses is then summed internally; when
the cells are empty both sides vanish.  Thus neither nonemptiness nor the raw
set-mass ratio remains a source premise. -/
structure Equation447FiniteCellProfileData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC : ℝ)
    (profile : Coord → ℕ) where
  profile_lt : ∀ x, profile x < m
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  historyCode : ∀ _q, ((Coord → ℕ) × Direction) → (Coord → ℕ)
  historyFiber : ∀ q, (Coord → ℕ) → Coord → Set ℕ
  directionHistory : ∀ q, (Coord → ℕ) → Set Direction
  selectedCoordinate : ∀ q, (Coord → ℕ) → Fin q → Coord
  selectedCoordinate_injective : ∀ q eta,
    Function.Injective (selectedCoordinate q eta)
  categoryCoordinate : ∀ q, (Coord → ℕ) → Fin q → ℕ → Fin 3
  historyCode_fiber : ∀ q eta,
    historyCode q ⁻¹' {eta} =
      (Set.pi Set.univ (historyFiber q eta)) ×ˢ
        directionHistory q eta
  equation447_history_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta,
        ((Set.pi Set.univ (historyFiber q eta)) ×ˢ
          directionHistory q eta) ∩
            (fun w x ↦ categoryCoordinate q eta x
              (w.1 (selectedCoordinate q eta x))) ⁻¹'
              {allUpperConfig}
  upperCell : ∀ q, (Coord → ℕ) → Fin q → Finset ℕ
  lowerCell : ∀ q, (Coord → ℕ) → Fin q → Finset ℕ
  upperCell_identification : ∀ q eta x,
    historyFiber q eta (selectedCoordinate q eta x) ∩
        categoryCoordinate q eta x ⁻¹' ({0} : Set (Fin 3)) =
      (↑(upperCell q eta x) : Set ℕ)
  lowerCell_identification : ∀ q eta x,
    historyFiber q eta (selectedCoordinate q eta x) ∩
        categoryCoordinate q eta x ⁻¹' ({1} : Set (Fin 3)) =
      (↑(lowerCell q eta x) : Set ℕ)
  cell_card_eq : ∀ q eta x,
    (upperCell q eta x).card = (lowerCell q eta x).card
  pointwise_mass_ratio : ∀ q eta x,
    ∀ a ∈ upperCell q eta x, ∀ b ∈ lowerCell q eta x,
      (sourceTruncatedNegBinMeasure m
        (profile (selectedCoordinate q eta x))).real {a} ≤
      ratioC *
        (sourceTruncatedNegBinMeasure m
          (profile (selectedCoordinate q eta x))).real {b}

namespace Equation447FiniteCellProfileData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC : ℝ} {profile : Coord → ℕ}

/-- Sum the pointwise cell comparison and expose the resulting raw
rectangular profile data. -/
noncomputable def toRawRectangularProfileData
    (R : Equation447FiniteCellProfileData
      cWindow m ratioC profile) :
    Equation447RawRectangularProfileData
      cWindow m ratioC profile where
  profile_lt := R.profile_lt
  forcedDirection := R.forcedDirection
  D := R.D
  historyCode := R.historyCode
  historyFiber := R.historyFiber
  directionHistory := R.directionHistory
  selectedCoordinate := R.selectedCoordinate
  selectedCoordinate_injective := R.selectedCoordinate_injective
  categoryCoordinate := R.categoryCoordinate
  historyCode_fiber := R.historyCode_fiber
  equation447_history_cover := R.equation447_history_cover
  raw_category_mass_ratio := by
    intro q eta x
    let μ := sourceTruncatedNegBinMeasure m
      (profile (R.selectedCoordinate q eta x))
    letI : IsProbabilityMeasure μ :=
      cond_isProbabilityMeasure
        (negBinMeasure_sourceBelowSet_ne_zero m
          (profile (R.selectedCoordinate q eta x))
          (R.profile_lt (R.selectedCoordinate q eta x)))
    rw [R.upperCell_identification q eta x,
      R.lowerCell_identification q eta x]
    by_cases hupper : (R.upperCell q eta x).Nonempty
    · exact measureReal_finset_le_mul_of_pointwise μ
        (R.upperCell q eta x) (R.lowerCell q eta x) ratioC
        (R.cell_card_eq q eta x) hupper.card_pos
        (R.pointwise_mass_ratio q eta x)
    · have hupperEmpty : R.upperCell q eta x = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hupper
      have hlowerEmpty : R.lowerCell q eta x = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [← R.cell_card_eq q eta x, hupperEmpty]
        rfl
      simp [hupperEmpty, hlowerEmpty]

end Equation447FiniteCellProfileData

/-- The part of a finite source band lying in one coordinate history fibre. -/
noncomputable def sourceHistoryCell (band : Finset ℕ) (fiber : Set ℕ) :
    Finset ℕ := by
  classical
  exact band.filter fun k ↦ k ∈ fiber

/-- A canonical enumeration of a finite selected-coordinate set.

The source naturally supplies the set of selected candidate coordinates and
its cardinality.  Choosing an ordering is bookkeeping, so it is performed
noncomputably inside Lean rather than retained as source data. -/
noncomputable def sourceSelectedCoordinate {Coord : Type}
    (q : ℕ) (selected : Finset Coord) (hcard : selected.card = q) :
    Fin q → Coord := by
  classical
  let e : Fin q ≃ selected := Fintype.equivOfCardEq (by simpa [hcard])
  exact fun x ↦ e x

lemma sourceSelectedCoordinate_injective {Coord : Type}
    (q : ℕ) (selected : Finset Coord) (hcard : selected.card = q) :
    Function.Injective (sourceSelectedCoordinate q selected hcard) := by
  classical
  let e : Fin q ≃ selected := Fintype.equivOfCardEq (by simpa [hcard])
  intro x y hxy
  apply e.injective
  apply Subtype.ext
  exact hxy

lemma sourceSelectedCoordinate_mem {Coord : Type}
    (q : ℕ) (selected : Finset Coord) (hcard : selected.card = q)
    (x : Fin q) : sourceSelectedCoordinate q selected hcard x ∈ selected := by
  classical
  let e : Fin q ≃ selected := Fintype.equivOfCardEq (by simpa [hcard])
  exact (e x).property

/-- The canonical source-band category, guarded by precisely the interval
and external-window hypotheses under which Lemma 4.12 compares adjacent
negative-binomial cells.  Invalid coordinates are assigned the inactive
category. -/
noncomputable def sourceWindowedBandCategory
    (cWindow m ℓ i k : ℕ) : Fin 3 := by
  classical
  exact if 2 ≤ ℓ ∧ SourceIntervalIndex m ℓ ∧
        InSourceExternalWindow cWindow m ℓ i then
      sourceBandCategory m ℓ i k
    else 2

lemma sourceWindowedBandCategory_eq_zero_window
    {cWindow m ℓ i k : ℕ}
    (hzero : sourceWindowedBandCategory cWindow m ℓ i k = 0) :
    2 ≤ ℓ ∧ SourceIntervalIndex m ℓ ∧
      InSourceExternalWindow cWindow m ℓ i := by
  classical
  by_contra hwindow
  simp [sourceWindowedBandCategory, hwindow] at hzero

/-- A coordinatewise history label is relevant only when its canonical
rectangle and all-upper band cell actually contain a vector from the bad
exact-count event.  Irrelevant labels can be assigned the inactive category
internally, so source window arithmetic is never requested for them. -/
def sourceBandHistoryRelevant {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (profile : Coord → ℕ) (D : Set (Coord → ℕ))
    (coordinateHistoryCode : ∀ _q : ℕ, Coord → ℕ → ℕ)
    (selectedCoordinates : ∀ q, q ≤ Fintype.card Coord →
      (Coord → ℕ) → Finset Coord)
    (selectedCoordinates_card : ∀ q hq eta,
      (selectedCoordinates q hq eta).card = q)
    (level : ∀ q, q ≤ Fintype.card Coord →
      (Coord → ℕ) → Fin q → ℕ)
    (q : ℕ) (hq : q ≤ Fintype.card Coord) (eta : Coord → ℕ) : Prop :=
  ∃ w ∈ sourceEquation447ByCount cWindow m profile D Set.univ q,
    w ∈ Set.pi Set.univ (fun x ↦ {k | coordinateHistoryCode q x k = eta x}) ∧
      (fun x ↦ sourceWindowedBandCategory cWindow m (level q hq eta x)
        (profile (sourceSelectedCoordinate q (selectedCoordinates q hq eta)
          (selectedCoordinates_card q hq eta) x))
        (w (sourceSelectedCoordinate q (selectedCoordinates q hq eta)
          (selectedCoordinates_card q hq eta) x))) = allUpperConfig

/-- If translation by one source-cell width sends the current part of a
history fibre into its preceding-band part, then the current cell has no more
points than the preceding cell.  Injectivity of translation is automatic; no
surjectivity or reverse history implication is needed. -/
lemma sourceHistoryCell_card_le_of_shift
    (c m ℓ i : ℕ) (fiber : Set ℕ)
    (hindex : SourceIntervalIndex m ℓ)
    (growth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i)
    (hshift : ∀ k, k ∈ sourceCurrentLazyBand m ℓ i →
      k ∈ fiber → k + sourceCellWidth m ∈ fiber) :
    (sourceHistoryCell (sourceCurrentLazyBand m ℓ i) fiber).card ≤
      (sourceHistoryCell (sourcePreviousLazyBand m ℓ i) fiber).card := by
  classical
  rcases hindex with ⟨hℓ, hindexBound⟩
  have hfit : ℓ * sourceCellWidth m ≤ m := by
    have hle : ℓ ≤ 2 * ℓ := by omega
    exact (Nat.mul_le_mul_right (sourceCellWidth m) hle).trans hindexBound
  obtain ⟨hupper, hprev⟩ :=
    sourceInterval_endpoint_relations m ℓ hℓ hfit
  rcases growth with ⟨hm, hdev, hgap, hlarge, hscale⟩
  have hindex' : 2 * (ℓ * sourceCellWidth m) ≤ m := by
    calc
      2 * (ℓ * sourceCellWidth m) = 2 * ℓ * sourceCellWidth m := by ring
      _ ≤ m := hindexBound
  have hhalf : m ≤ 2 * sourceIntervalLower m ℓ := by
    unfold sourceIntervalLower
    omega
  have hclose : 30 * sourceCellWidth m + 16 * sourceDeviationWidth c m ≤
      sourceIntervalLower m ℓ := by omega
  have hiLower : i ≤ sourceIntervalLower m ℓ := by
    unfold InSourceExternalWindow at hiwin
    omega
  apply Finset.card_le_card_of_injOn (fun k ↦ k + sourceCellWidth m)
  · intro k hk
    change k ∈ sourceHistoryCell (sourceCurrentLazyBand m ℓ i) fiber at hk
    change k + sourceCellWidth m ∈
      sourceHistoryCell (sourcePreviousLazyBand m ℓ i) fiber
    simp only [sourceHistoryCell, Finset.mem_filter] at hk ⊢
    refine ⟨?_, hshift k hk.1 hk.2⟩
    have hkIco := Finset.mem_Ico.mp hk.1
    apply Finset.mem_Ico.mpr
    omega
  · intro k₁ hk₁ k₂ hk₂ heq
    exact Nat.add_right_cancel heq

/-- Canonical HLOZ adjacent-band presentation of the finite category cells.

Unlike `Equation447AdjacentCellProfileData`, this record does not let the
source choose a category map or two finite cells and then separately identify
them with the current and previous HLOZ bands.  The category is
`sourceBandCategory`, and the cells are definitionally the history fibre
filtered by the two canonical bands.  A history code is supplied separately
for each coordinate; Lean assembles the global code componentwise and proves
that its fibres are the corresponding product rectangles.  The source cover
is stated purely on the lazy-vector space.  Lean inserts a fixed fresh
direction only when entering the legacy product-space connector.  In
particular the source no longer supplies a chosen fresh direction, an
arbitrary direction-history set, or a global product-fibre identity.  The
source supplies the literal finite set of
  selected coordinates and its cardinality; Lean chooses an enumeration and
  proves it injective.  The only history-cell datum retained from the source is
  one-way preservation, on labels occurring in the bad-event cover, of
  membership in the corresponding coordinate fibre under forward translation
  by one source-cell width.  This is required only for current-band values
  already in that fibre.  Lean turns it into an injection of the current cell into the preceding cell, which is
  exactly the cardinality domination needed in
  (4.47).  Lean assigns the inactive category to history labels that never
  occur in the bad-event cover and to coordinates outside the valid source
  window.  Consequently the all-upper source cover itself proves every
  interval-index and external-window fact that is actually used; there is no
  separate window-arithmetic field.  Empty cells contribute zero and are
  discharged internally. -/
structure Equation447SourceBandProfileData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ)
    (profile : Coord → ℕ) where
  D : Set (Coord → ℕ)
  coordinateHistoryCode : ∀ _q, Coord → ℕ → ℕ
  selectedCoordinates : ∀ q, q ≤ Fintype.card Coord →
    (Coord → ℕ) → Finset Coord
  selectedCoordinates_card : ∀ q hq eta,
    (selectedCoordinates q hq eta).card = q
  level : ∀ q, q ≤ Fintype.card Coord → (Coord → ℕ) →
    Fin q → ℕ
  equation447_history_cover : ∀ q hq,
    sourceEquation447ByCount cWindow m profile D Set.univ q ⊆ ⋃ eta,
        (Set.pi Set.univ (fun x ↦
            {k | coordinateHistoryCode q x k = eta x})) ∩
            (fun w x ↦ sourceWindowedBandCategory cWindow m
              (level q hq eta x)
              (profile (sourceSelectedCoordinate q
                (selectedCoordinates q hq eta)
                (selectedCoordinates_card q hq eta) x))
                (w (sourceSelectedCoordinate q
                  (selectedCoordinates q hq eta)
                  (selectedCoordinates_card q hq eta) x))) ⁻¹'
              {allUpperConfig}
  coordinateHistoryCode_shift : ∀ q hq eta,
    sourceBandHistoryRelevant cWindow m profile D coordinateHistoryCode
      selectedCoordinates selectedCoordinates_card level q hq eta →
    ∀ x k,
      k ∈ sourceCurrentLazyBand m (level q hq eta x)
          (profile (sourceSelectedCoordinate q
            (selectedCoordinates q hq eta)
            (selectedCoordinates_card q hq eta) x)) →
      coordinateHistoryCode q
          (sourceSelectedCoordinate q (selectedCoordinates q hq eta)
            (selectedCoordinates_card q hq eta) x) k =
        eta (sourceSelectedCoordinate q (selectedCoordinates q hq eta)
          (selectedCoordinates_card q hq eta) x) →
      coordinateHistoryCode q
          (sourceSelectedCoordinate q (selectedCoordinates q hq eta)
            (selectedCoordinates_card q hq eta) x)
          (k + sourceCellWidth m) =
        eta (sourceSelectedCoordinate q (selectedCoordinates q hq eta)
          (selectedCoordinates_card q hq eta) x)

namespace Equation447SourceBandProfileData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {profile : Coord → ℕ}

/-- The bad-event relevance predicate specialized to a source-band record. -/
def historyRelevant
    (R : Equation447SourceBandProfileData cWindow m profile)
    (q : ℕ) (hq : q ≤ Fintype.card Coord) (eta : Coord → ℕ) : Prop :=
  sourceBandHistoryRelevant cWindow m profile R.D R.coordinateHistoryCode
    R.selectedCoordinates R.selectedCoordinates_card R.level q hq eta

/-- The coordinatewise history fibre determined by the source label. -/
def historyFiber
    (R : Equation447SourceBandProfileData cWindow m profile)
    (q : ℕ) (eta : Coord → ℕ) (x : Coord) : Set ℕ :=
  {k | R.coordinateHistoryCode q x k = eta x}

/-- The canonical global history code is the componentwise coordinate code;
the fresh direction is deliberately not included in the stopped history. -/
def fullHistoryCode
    (R : Equation447SourceBandProfileData cWindow m profile)
    (q : ℕ) : ((Coord → ℕ) × Direction) → (Coord → ℕ) :=
  fun w x ↦ R.coordinateHistoryCode q x (w.1 x)

/-- Fibres of the canonical global code are product rectangles, with the
fresh direction unrestricted.  This replaces the former source premise. -/
lemma fullHistoryCode_fiber
    (R : Equation447SourceBandProfileData cWindow m profile)
    (q : ℕ) (eta : Coord → ℕ) :
    R.fullHistoryCode q ⁻¹' {eta} =
      (Set.pi Set.univ (R.historyFiber q eta)) ×ˢ
        (Set.univ : Set Direction) := by
  ext w
  simp only [historyFiber, Set.mem_preimage,
    Set.mem_singleton_iff, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    and_true]
  constructor
  · intro h x _hx
    exact congrFun h x
  · intro h
    funext x
    exact h x (Set.mem_univ x)

/-- Lean's canonical enumeration of the literal finite selected-coordinate
set stored by the source record. -/
noncomputable def selectedCoordinate
    (R : Equation447SourceBandProfileData cWindow m profile)
    (q : ℕ) (hq : q ≤ Fintype.card Coord)
    (eta : Coord → ℕ) : Fin q → Coord :=
  sourceSelectedCoordinate q (R.selectedCoordinates q hq eta)
    (R.selectedCoordinates_card q hq eta)

lemma selectedCoordinate_injective
    (R : Equation447SourceBandProfileData cWindow m profile)
    (q : ℕ) (hq : q ≤ Fintype.card Coord) (eta : Coord → ℕ) :
    Function.Injective (R.selectedCoordinate q hq eta) :=
  sourceSelectedCoordinate_injective q (R.selectedCoordinates q hq eta)
    (R.selectedCoordinates_card q hq eta)

lemma selectedCoordinate_mem
    (R : Equation447SourceBandProfileData cWindow m profile)
    (q : ℕ) (hq : q ≤ Fintype.card Coord)
    (eta : Coord → ℕ) (x : Fin q) :
    R.selectedCoordinate q hq eta x ∈ R.selectedCoordinates q hq eta :=
  sourceSelectedCoordinate_mem q (R.selectedCoordinates q hq eta)
    (R.selectedCoordinates_card q hq eta) x

/-- Every coordinate of a history label that occurs in the all-upper source
cover automatically lies in the valid Lemma-4.12 window. -/
lemma window_of_historyRelevant
    (R : Equation447SourceBandProfileData cWindow m profile)
    (q : ℕ) (hq : q ≤ Fintype.card Coord) (eta : Coord → ℕ)
    (hrel : R.historyRelevant q hq eta) (x : Fin q) :
    2 ≤ R.level q hq eta x ∧
      SourceIntervalIndex m (R.level q hq eta x) ∧
      InSourceExternalWindow cWindow m (R.level q hq eta x)
        (profile (R.selectedCoordinate q hq eta x)) := by
  rcases hrel with ⟨w, _hwCount, _hwHistory, hwCategory⟩
  apply sourceWindowedBandCategory_eq_zero_window
    (k := w (R.selectedCoordinate q hq eta x))
  have hx := congrFun hwCategory x
  simpa only [allUpperConfig, selectedCoordinate] using hx

/-- The part of a coordinate history fibre in the canonical current band. -/
noncomputable def upperCell
    (R : Equation447SourceBandProfileData cWindow m profile)
    (q : ℕ) (hq : q ≤ Fintype.card Coord)
    (eta : Coord → ℕ) (x : Fin q) : Finset ℕ :=
  sourceHistoryCell
    (sourceCurrentLazyBand m (R.level q hq eta x)
      (profile (R.selectedCoordinate q hq eta x)))
    (R.historyFiber q eta (R.selectedCoordinate q hq eta x))

/-- The part of a coordinate history fibre in the canonical preceding band. -/
noncomputable def lowerCell
    (R : Equation447SourceBandProfileData cWindow m profile)
    (q : ℕ) (hq : q ≤ Fintype.card Coord)
    (eta : Coord → ℕ) (x : Fin q) : Finset ℕ :=
  sourceHistoryCell
    (sourcePreviousLazyBand m (R.level q hq eta x)
      (profile (R.selectedCoordinate q hq eta x)))
    (R.historyFiber q eta (R.selectedCoordinate q hq eta x))

/-- Cardinality domination of the two canonical history cells, derived from
the literal one-way shift implication stored by the source record. -/
lemma cell_card_le
    (R : Equation447SourceBandProfileData cWindow m profile)
    (growth : SourceWindowGrowth cWindow m)
    (q : ℕ) (hq : q ≤ Fintype.card Coord)
    (eta : Coord → ℕ) (hrel : R.historyRelevant q hq eta) (x : Fin q) :
    (R.upperCell q hq eta x).card ≤ (R.lowerCell q hq eta x).card := by
  classical
  have hwindow := R.window_of_historyRelevant q hq eta hrel x
  apply sourceHistoryCell_card_le_of_shift
    cWindow m (R.level q hq eta x)
      (profile (R.selectedCoordinate q hq eta x))
      (R.historyFiber q eta (R.selectedCoordinate q hq eta x))
    hwindow.2.1 growth hwindow.2.2
  intro k hk hkcode
  change R.coordinateHistoryCode q (R.selectedCoordinate q hq eta x)
      (k + sourceCellWidth m) = eta (R.selectedCoordinate q hq eta x)
  change R.coordinateHistoryCode q (R.selectedCoordinate q hq eta x) k =
      eta (R.selectedCoordinate q hq eta x) at hkcode
  simpa only [selectedCoordinate] using
    R.coordinateHistoryCode_shift q hq eta hrel x k hk hkcode

end Equation447SourceBandProfileData

/-- Literal adjacent-band presentation of the two finite category cells.

The source-facing fields identify the cells and place them inside the two
adjacent HLOZ bands.  Lemma 4.12 then proves every singleton comparison; no
probability inequality remains in this record.  Null history fibers need no
positivity or nonemptiness premise: their rectangular contribution vanishes,
and the checked connector installs a harmless Dirac law in category `2`.
The coordinatewise profile
bound is derived separately from each literal stopped winner source and
passed to the converter, rather than stored in this category-cell record. -/
structure Equation447AdjacentCellProfileData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ)
    (profile : Coord → ℕ) where
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  historyCode : ∀ _q, ((Coord → ℕ) × Direction) → (Coord → ℕ)
  historyFiber : ∀ q, (Coord → ℕ) → Coord → Set ℕ
  directionHistory : ∀ q, (Coord → ℕ) → Set Direction
  selectedCoordinate : ∀ q, (Coord → ℕ) → Fin q → Coord
  selectedCoordinate_injective : ∀ q eta,
    Function.Injective (selectedCoordinate q eta)
  categoryCoordinate : ∀ q, (Coord → ℕ) → Fin q → ℕ → Fin 3
  historyCode_fiber : ∀ q eta,
    historyCode q ⁻¹' {eta} =
      (Set.pi Set.univ (historyFiber q eta)) ×ˢ
        directionHistory q eta
  equation447_history_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆ ⋃ eta,
        ((Set.pi Set.univ (historyFiber q eta)) ×ˢ
          directionHistory q eta) ∩
            (fun w x ↦ categoryCoordinate q eta x
              (w.1 (selectedCoordinate q eta x))) ⁻¹'
              {allUpperConfig}
  upperCell : ∀ q, (Coord → ℕ) → Fin q → Finset ℕ
  lowerCell : ∀ q, (Coord → ℕ) → Fin q → Finset ℕ
  upperCell_identification : ∀ q eta x,
    historyFiber q eta (selectedCoordinate q eta x) ∩
        categoryCoordinate q eta x ⁻¹' ({0} : Set (Fin 3)) =
      (↑(upperCell q eta x) : Set ℕ)
  lowerCell_identification : ∀ q eta x,
    historyFiber q eta (selectedCoordinate q eta x) ∩
        categoryCoordinate q eta x ⁻¹' ({1} : Set (Fin 3)) =
      (↑(lowerCell q eta x) : Set ℕ)
  cell_card_eq : ∀ q eta x,
    (upperCell q eta x).card = (lowerCell q eta x).card
  level : ∀ q, (Coord → ℕ) → Fin q → ℕ
  level_two : ∀ q eta x, 2 ≤ level q eta x
  level_index : ∀ q eta x, SourceIntervalIndex m (level q eta x)
  external_window : ∀ q eta x,
    InSourceExternalWindow cWindow m (level q eta x)
      (profile (selectedCoordinate q eta x))
  upperCell_subset_current : ∀ q eta x,
    ↑(upperCell q eta x) ⊆ sourceCurrentLazyBand m (level q eta x)
      (profile (selectedCoordinate q eta x))
  lowerCell_subset_previous : ∀ q eta x,
    ↑(lowerCell q eta x) ⊆ sourcePreviousLazyBand m (level q eta x)
      (profile (selectedCoordinate q eta x))

namespace Equation447AdjacentCellProfileData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {profile : Coord → ℕ}

/-- Lemma 4.12 fills the pointwise cell comparison required by the finite
cell connector.  Its deterministic large-scale window-growth hypothesis is
passed by the eventual X/Y assembly connectors, rather than stored in the
source-facing adjacent-cell record. -/
noncomputable def toFiniteCellProfileData
    (R : Equation447AdjacentCellProfileData cWindow m profile)
    (profile_lt : ∀ x, profile x < m)
    (growth : SourceWindowGrowth cWindow m) :
    Equation447FiniteCellProfileData cWindow m
      (Real.exp (sourceAdjacentComparisonExponent cWindow)) profile where
  profile_lt := profile_lt
  forcedDirection := R.forcedDirection
  D := R.D
  historyCode := R.historyCode
  historyFiber := R.historyFiber
  directionHistory := R.directionHistory
  selectedCoordinate := R.selectedCoordinate
  selectedCoordinate_injective := R.selectedCoordinate_injective
  categoryCoordinate := R.categoryCoordinate
  historyCode_fiber := R.historyCode_fiber
  equation447_history_cover := R.equation447_history_cover
  upperCell := R.upperCell
  lowerCell := R.lowerCell
  upperCell_identification := R.upperCell_identification
  lowerCell_identification := R.lowerCell_identification
  cell_card_eq := R.cell_card_eq
  pointwise_mass_ratio := by
    intro q eta x a ha b hb
    exact sourceTruncatedNegBinMeasure_adjacent_singleton_le
      cWindow m (R.level q eta x)
        (profile (R.selectedCoordinate q eta x)) a b
      (profile_lt (R.selectedCoordinate q eta x))
      (R.level_two q eta x) (R.level_index q eta x) growth
      (R.external_window q eta x)
      (R.upperCell_subset_current q eta x ha)
      (R.lowerCell_subset_previous q eta x hb)

end Equation447AdjacentCellProfileData

namespace Equation447SourceBandProfileData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {profile : Coord → ℕ}

/-- Canonical adjacent bands supply the bounded coordinatewise profile data.

Only feasible exact counts need an enumeration of selected coordinates.  The
bounded converter subsequently fills every infeasible count by the inactive
Dirac category, using the fact that its exact-count event is empty. -/
noncomputable def toBoundedCoordinatewiseProfileData
    (R : Equation447SourceBandProfileData cWindow m profile)
    (profile_lt : ∀ x, profile x < m)
    (growth : SourceWindowGrowth cWindow m) :
    Equation447BoundedCoordinatewiseProfileData cWindow m
      (Real.exp (sourceAdjacentComparisonExponent cWindow)) profile where
  profile_lt := profile_lt
  forcedDirection := 0
  D := R.D
  historyCode := R.fullHistoryCode
  historyFiber := fun q _hq eta ↦ R.historyFiber q eta
  directionHistory := fun _q _hq _eta ↦ Set.univ
  selectedCoordinate := R.selectedCoordinate
  selectedCoordinate_injective := R.selectedCoordinate_injective
  categoryCoordinate := by
    classical
    exact fun q hq eta x k ↦
      if R.historyRelevant q hq eta then
        sourceWindowedBandCategory cWindow m (R.level q hq eta x)
          (profile (R.selectedCoordinate q hq eta x)) k
      else 2
  historyCode_fiber := fun q _hq eta ↦ R.fullHistoryCode_fiber q eta
  equation447_history_cover := by
    intro q hq w hw
    rcases hw with ⟨hwCount, _hwDirection⟩
    rcases Set.mem_iUnion.mp (R.equation447_history_cover q hq hwCount) with
      ⟨eta, hwHistory, hwCategory⟩
    have hrel : R.historyRelevant q hq eta := by
      exact ⟨w.1, hwCount, hwHistory, by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hwCategory⟩
    refine Set.mem_iUnion.mpr ⟨eta, ?_⟩
    exact ⟨⟨hwHistory, Set.mem_univ _⟩, by
      simpa only [hrel, if_true, selectedCoordinate, Set.mem_preimage,
        Set.mem_singleton_iff] using hwCategory⟩
  category_mass_ratio := by
    classical
    intro q hq eta x
    let selected := R.selectedCoordinate q hq eta x
    let level := R.level q hq eta x
    let μ := sourceTruncatedNegBinMeasure m (profile selected)
    letI : IsProbabilityMeasure μ :=
      cond_isProbabilityMeasure
        (negBinMeasure_sourceBelowSet_ne_zero m (profile selected)
          (profile_lt selected))
    by_cases hrel : R.historyRelevant q hq eta
    · simp only [hrel, if_true]
      have hwindow := R.window_of_historyRelevant q hq eta hrel x
      have hwindow' : 2 ≤ level ∧ SourceIntervalIndex m level ∧
          InSourceExternalWindow cWindow m level (profile selected) := by
        simpa only [level, selected] using hwindow
      have hcategory :
          sourceWindowedBandCategory cWindow m level (profile selected) =
            sourceBandCategory m level (profile selected) := by
        funext k
        simp [sourceWindowedBandCategory, hwindow']
      apply conditionalCategoryLawOrDirac_two_mass_ratio_of_inter
        μ inferInstance
        (R.historyFiber q eta selected) MeasurableSet.of_discrete
        (sourceWindowedBandCategory cWindow m level (profile selected))
        (measurable_of_countable _)
        (Real.exp (sourceAdjacentComparisonExponent cWindow))
      have hupper :
          R.historyFiber q eta selected ∩
              sourceWindowedBandCategory cWindow m level
                (profile selected) ⁻¹'
                ({0} : Set (Fin 3)) =
            (↑(R.upperCell q hq eta x) : Set ℕ) := by
        rw [hcategory, sourceBandCategory_zero_preimage]
        ext k
        simp [selected, level, upperCell, sourceHistoryCell, and_comm]
      have hlower :
          R.historyFiber q eta selected ∩
              sourceWindowedBandCategory cWindow m level
                (profile selected) ⁻¹'
                ({1} : Set (Fin 3)) =
            (↑(R.lowerCell q hq eta x) : Set ℕ) := by
        rw [hcategory, sourceBandCategory_one_preimage]
        ext k
        simp [selected, level, lowerCell, sourceHistoryCell, and_comm]
      rw [hupper, hlower]
      by_cases hnonempty : (R.upperCell q hq eta x).Nonempty
      · rcases hnonempty with ⟨a, ha⟩
        apply measureReal_finset_le_mul_of_pointwise_of_card_le μ
          (R.upperCell q hq eta x) (R.lowerCell q hq eta x)
          (Real.exp (sourceAdjacentComparisonExponent cWindow))
          (R.cell_card_le growth q hq eta hrel x)
          (Finset.card_pos.mpr ⟨a, ha⟩)
        intro a ha b hb
        apply sourceTruncatedNegBinMeasure_adjacent_singleton_le
          cWindow m (R.level q hq eta x)
          (profile (R.selectedCoordinate q hq eta x)) a b
          (profile_lt (R.selectedCoordinate q hq eta x))
          hwindow.1 hwindow.2.1 growth hwindow.2.2
        · exact (Finset.mem_filter.mp ha).1
        · exact (Finset.mem_filter.mp hb).1
      · have hupperEmpty : R.upperCell q hq eta x = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnonempty
        rw [hupperEmpty]
        simp only [Finset.coe_empty, measure_empty, measureReal_def,
          ENNReal.toReal_zero]
        exact mul_nonneg (Real.exp_nonneg _) measureReal_nonneg
    · simp only [hrel, if_false]
      apply conditionalCategoryLawOrDirac_two_mass_ratio_of_inter
        μ inferInstance
        (R.historyFiber q eta selected) MeasurableSet.of_discrete
        (fun _ ↦ (2 : Fin 3)) (measurable_of_countable _)
        (Real.exp (sourceAdjacentComparisonExponent cWindow))
      simp

/-- Total source-band profile data, including the vacuous infeasible-count
cases, in the coded form consumed by equation (4.47). -/
noncomputable def toCodedProfileData
    (R : Equation447SourceBandProfileData cWindow m profile)
    (profile_lt : ∀ x, profile x < m)
    (growth : SourceWindowGrowth cWindow m) :
    Equation447CodedProfileData cWindow m
      (Real.exp (sourceAdjacentComparisonExponent cWindow)) profile :=
  (R.toBoundedCoordinatewiseProfileData profile_lt growth).toCodedProfileData

end Equation447SourceBandProfileData

/-- Branch event data whose equation-(4.47) probability identity is reduced
to coordinatewise history fibers.  The only additional fields are the two
path-space inclusions needed by the branch consumer. -/
structure Equation447CoordinatewiseBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (failure thetaPathEvent pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  profileData : Equation447CoordinatewiseProfileData
    cWindow m ratioC profile
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ profileData.D) ×ˢ
        (Set.univ : Set Direction))
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent

namespace Equation447CoordinatewiseBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC rho : ℝ}
  {failure thetaPathEvent pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Coordinatewise branch fibers supply the coded branch record; in
particular the conditional categorical product is no longer a premise. -/
noncomputable def toCodedBranchRemainingData
    (R : Equation447CoordinatewiseBranchRemainingData
      cWindow m ratioC rho failure thetaPathEvent pathAtom
      profile lazyVector nextDirection) :
    Equation447CodedBranchRemainingData cWindow m ratioC rho
      failure thetaPathEvent pathAtom profile lazyVector nextDirection := by
  let P := R.profileData.toCodedProfileData
  exact
    { forcedDirection := P.forcedDirection
      D := P.D
      historyCode := P.historyCode
      category := P.category
      categoryLaw := P.categoryLaw
      failure_subset := R.failure_subset
      theta_preimage_subset := R.theta_preimage_subset
      equation447_history_cover := P.equation447_history_cover
      conditional_category_product := P.conditional_category_product
      category_mass_ratio := P.category_mass_ratio }

end Equation447CoordinatewiseBranchRemainingData

/-- Branch-shaped wrapper around raw rectangular history data.  Both the
finite conditional product and the cancellation of the one-coordinate
conditioning normalizers are derived internally. -/
structure Equation447RawRectangularBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (failure thetaPathEvent pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  profileData : Equation447RawRectangularProfileData
    cWindow m ratioC profile
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ profileData.D) ×ˢ
        (Set.univ : Set Direction))
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent

namespace Equation447RawRectangularBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC rho : ℝ}
  {failure thetaPathEvent pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Forget only the raw-ratio presentation; the resulting coordinatewise
record can then use the checked rectangle-product theorem. -/
noncomputable def toCoordinatewiseBranchRemainingData
    (R : Equation447RawRectangularBranchRemainingData
      cWindow m ratioC rho failure thetaPathEvent pathAtom
      profile lazyVector nextDirection) :
    Equation447CoordinatewiseBranchRemainingData
      cWindow m ratioC rho failure thetaPathEvent pathAtom
      profile lazyVector nextDirection where
  profileData := R.profileData.toCoordinatewiseProfileData
  failure_subset := R.failure_subset
  theta_preimage_subset := R.theta_preimage_subset

end Equation447RawRectangularBranchRemainingData

/-- Branch wrapper whose one-coordinate input consists only of two explicit
finite cells and their pointwise singleton-mass comparison. -/
structure Equation447FiniteCellBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (ratioC rho : ℝ)
    (failure thetaPathEvent pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  profileData : Equation447FiniteCellProfileData
    cWindow m ratioC profile
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ profileData.D) ×ˢ
        (Set.univ : Set Direction))
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent

namespace Equation447FiniteCellBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC rho : ℝ}
  {failure thetaPathEvent pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Finite cells first sum to raw ratios, after which the existing
rectangular-history connector performs both conditioning steps. -/
noncomputable def toRawRectangularBranchRemainingData
    (R : Equation447FiniteCellBranchRemainingData
      cWindow m ratioC rho failure thetaPathEvent pathAtom
      profile lazyVector nextDirection) :
    Equation447RawRectangularBranchRemainingData
      cWindow m ratioC rho failure thetaPathEvent pathAtom
      profile lazyVector nextDirection where
  profileData := R.profileData.toRawRectangularProfileData
  failure_subset := R.failure_subset
  theta_preimage_subset := R.theta_preimage_subset

end Equation447FiniteCellBranchRemainingData

/-- Branch wrapper for literal adjacent-band cells.  Its probability
comparison is filled entirely by the checked Lemma-4.12 window estimate. -/
structure Equation447AdjacentCellBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (rho : ℝ)
    (failure thetaPathEvent pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  profileData : Equation447AdjacentCellProfileData
    cWindow m profile
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ profileData.D) ×ˢ
        (Set.univ : Set Direction))
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent

namespace Equation447AdjacentCellBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {rho : ℝ}
  {failure thetaPathEvent pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Expose the finite-cell wrapper with its canonical adjacent-band ratio. -/
noncomputable def toFiniteCellBranchRemainingData
    (R : Equation447AdjacentCellBranchRemainingData
      cWindow m rho failure thetaPathEvent pathAtom
      profile lazyVector nextDirection)
    (profile_lt : ∀ x, profile x < m)
    (growth : SourceWindowGrowth cWindow m) :
    Equation447FiniteCellBranchRemainingData cWindow m
      (Real.exp (sourceAdjacentComparisonExponent cWindow)) rho
      failure thetaPathEvent pathAtom profile lazyVector nextDirection where
  profileData := R.profileData.toFiniteCellProfileData profile_lt growth
  failure_subset := R.failure_subset
  theta_preimage_subset := R.theta_preimage_subset

end Equation447AdjacentCellBranchRemainingData

/-- Branch wrapper whose coordinate categories and cells are the canonical
HLOZ adjacent bands.  Only the branch-event inclusions remain in addition to
the source-band profile data. -/
structure Equation447SourceBandBranchRemainingData
    {Coord : Type} [Fintype Coord]
    (cWindow m : ℕ) (rho : ℝ)
    (failure thetaPathEvent pathAtom : Set (ℕ → Site))
    (profile : Coord → ℕ)
    (lazyVector : (ℕ → Site) → Coord → ℕ)
    (nextDirection : (ℕ → Site) → Direction) where
  profileData : Equation447SourceBandProfileData
    cWindow m profile
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ profileData.D) ×ˢ
        (Set.univ : Set Direction))
  theta_preimage_subset :
    pathAtom ∩ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPathEvent

namespace Equation447SourceBandBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {rho : ℝ}
  {failure thetaPathEvent pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Direct bounded source-band bridge used by the literal X/Y
equation-(4.47) consumers.  Counts larger than the finite coordinate type are
handled internally as empty exact-count events. -/
noncomputable def toCodedBranchRemainingData
    (R : Equation447SourceBandBranchRemainingData
      cWindow m rho failure thetaPathEvent pathAtom
      profile lazyVector nextDirection)
    (profile_lt : ∀ x, profile x < m)
    (growth : SourceWindowGrowth cWindow m) :
    Equation447CodedBranchRemainingData cWindow m
      (Real.exp (sourceAdjacentComparisonExponent cWindow)) rho
      failure thetaPathEvent pathAtom profile lazyVector nextDirection := by
  let P := R.profileData.toCodedProfileData profile_lt growth
  exact
    { forcedDirection := P.forcedDirection
      D := P.D
      historyCode := P.historyCode
      category := P.category
      categoryLaw := P.categoryLaw
      failure_subset := R.failure_subset
      theta_preimage_subset := R.theta_preimage_subset
      equation447_history_cover := P.equation447_history_cover
      conditional_category_product := P.conditional_category_product
      category_mass_ratio := P.category_mass_ratio }

/-- The same literal adjacent-band source data also supplies the optimal
deleted-path witness package.

All categorical product identities, the optimal layer, and disjointness of
distinct history-code witnesses are derived internally.  Beyond the source
band rectangles, only the two branch-event inclusions remain. -/
noncomputable def toOptimalCategoricalPathWitnessBranchRemainingData
    (R : Equation447SourceBandBranchRemainingData
      cWindow m rho failure thetaPathEvent pathAtom
      profile lazyVector nextDirection)
    (profile_lt : ∀ x, profile x < m)
    (growth : SourceWindowGrowth cWindow m) :
    Equation447OptimalCategoricalPathWitnessBranchRemainingData
      cWindow m (Real.exp (sourceAdjacentComparisonExponent cWindow)) rho
      failure pathAtom profile lazyVector nextDirection :=
  (R.profileData.toBoundedCoordinatewiseProfileData profile_lt growth)
    |>.toOptimalCategoricalPathWitnessBranchRemainingData
      rho failure thetaPathEvent pathAtom lazyVector nextDirection
      R.failure_subset R.theta_preimage_subset

end Equation447SourceBandBranchRemainingData

namespace Equation447CodedBranchRemainingData

variable {Coord : Type} [Fintype Coord]
  {cWindow m : ℕ} {ratioC rho : ℝ}
  {failure thetaPathEvent pathAtom : Set (ℕ → Site)}
  {profile : Coord → ℕ}
  {lazyVector : (ℕ → Site) → Coord → ℕ}
  {nextDirection : (ℕ → Site) → Direction}

/-- Forget the path-space branch fields of an equation-(4.47) record.

The categorical history decomposition depends on the fixed profile, but not
on the numerical threshold used by the surrounding branch event.  Hence the
fixed-profile result type has no threshold parameter, and this projection
does not ask the caller to manufacture one.  The same checked
conditional-product law can therefore be reused at any threshold by the
fixed-profile Proposition-4.8 recursion.  This is the formal sharing point
between the Lemma-4.10 and Lemmas-4.11--4.12 source packages. -/
def toProfileData
    (R : Equation447CodedBranchRemainingData cWindow m ratioC rho
      failure thetaPathEvent pathAtom profile lazyVector nextDirection) :
    Equation447CodedProfileData cWindow m ratioC profile where
  forcedDirection := R.forcedDirection
  D := R.D
  historyCode := R.historyCode
  category := R.category
  categoryLaw := R.categoryLaw
  equation447_history_cover := R.equation447_history_cover
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio

end Equation447CodedBranchRemainingData

/-- Literal unprimed/even left-winner source data. -/
structure UnprimedEvenLeftWinnerSource (m : ℕ) where
  q : ℕ
  k : ℕ
  creationSet : Finset Site
  labels : Fin q → IncrementPair
  labels_nondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair
  m_pos : 0 < m
  k_pos : 0 < k
  creation_card : creationSet.card = k
  creation_pairFree : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) creationSet
  offBase : UnprimedEvenOffBaseMixedCondition labels m creationSet
  terminal_mem : stoppedTerminalBase labels ∈ creationSet
  admissible_nonempty :
    (actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k creationSet labels)).Nonempty
  candidateBases : Finset (StoppedExternalBase (0, 0) labels)

namespace UnprimedEvenLeftWinnerSource

variable {m : ℕ} (S : UnprimedEvenLeftWinnerSource m)

noncomputable def activeBases :
    Finset (StoppedExternalBase (0, 0) S.labels) :=
  unprimedEvenLeftWinnerBases S.labels S.candidateBases

abbrev Coord :=
  ActiveFreeStoppedBase (0, 0) S.labels S.creationSet S.activeBases

def incrementEvent : Set (ℕ → Direction) :=
  actualStoppedVectorEvent m S.k S.labels (stoppedRunVectorBox S.q m) ∩
    stoppedSourceCondition m S.k S.creationSet

def pathAtom : Set (ℕ → Site) := simpleRandomWalk '' S.incrementEvent

noncomputable def profile : S.Coord → ℕ :=
  activeFreeStoppedShape (0, 0) S.labels S.creationSet S.activeBases

/-- The literal admissible stopped-vector witness forces every active
left-winner shape below the stopping level. -/
theorem profile_lt : ∀ x, S.profile x < m :=
  unprimedEven_leftWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.labels S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases

noncomputable def lazyVector : (ℕ → Site) → S.Coord → ℕ :=
  unprimedEvenActiveFreePathLazy m S.k S.creationSet S.labels S.activeBases

noncomputable def nextDirection : (ℕ → Site) → Direction :=
  unprimedEvenActiveFreePathNext m S.k S.creationSet S.labels S.activeBases

theorem measurableSet_pathAtom : MeasurableSet S.pathAtom := by
  have hIncrement : MeasurableSet S.incrementEvent := by
    rw [incrementEvent, unprimedEven_source_partition m S.k S.creationSet
      S.labels S.m_pos S.k_pos S.creation_pairFree]
    exact measurableSet_actualStoppedVectorEvent _ _ _ _
  exact HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
    |>.measurableSet_image.2 hIncrement

theorem measurable_lazyVector : Measurable S.lazyVector :=
  measurable_unprimedEvenActiveFreePathLazy m S.k S.creationSet S.labels
    S.labels_nondistinguished S.activeBases

theorem measurable_nextDirection : Measurable S.nextDirection :=
  measurable_unprimedEvenActiveFreePathNext m S.k S.creationSet S.labels
    S.labels_nondistinguished S.activeBases

theorem map_law :
    (simpleRandomWalkLaw.restrict S.pathAtom).map
        (fun s ↦ (S.lazyVector s, S.nextDirection s)) =
      simpleRandomWalkLaw S.pathAtom •
        ((sourceTruncatedProfileMeasure m S.profile).prod directionLaw) :=
  unprimedEven_leftWinner_StoppedEquation447Atom_map_law
    m S.k S.creationSet S.labels S.labels_nondistinguished S.m_pos S.k_pos
      S.creation_card S.creation_pairFree S.offBase S.terminal_mem
      S.admissible_nonempty S.candidateBases

/-- Construct an equation-(4.47) atom with the stopped product law filled in
by the checked unprimed-left source theorem. -/
noncomputable def toStoppedEquation447Atom
    (cWindow : ℕ) (ratioC cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site))
    (R : Equation447RemainingData cWindow m ratioC cTheta thetaPower
      failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447Atom cWindow m ratioC cTheta thetaPower failure where
  Coord := S.Coord
  coordFintype := inferInstance
  pathAtom := S.pathAtom
  measurableSet_pathAtom := S.measurableSet_pathAtom
  profile := S.profile
  profile_lt := unprimedEven_leftWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.labels S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases
  lazyVector := S.lazyVector
  measurable_lazyVector := S.measurable_lazyVector
  nextDirection := S.nextDirection
  measurable_nextDirection := S.measurable_nextDirection
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  historyAtom := R.historyAtom
  category := R.category
  categoryLaw := R.categoryLaw
  categoryLaw_probability := R.categoryLaw_probability
  map_law := S.map_law
  failure_subset := R.failure_subset
  theta_bound := R.theta_bound
  equation447_cover := R.equation447_cover
  bad_subset_history_allUpper := R.bad_subset_history_allUpper
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := R.history_disjoint
  history_measurable := R.history_measurable

/-- Branch-specific version with an explicit profile threshold. -/
noncomputable def toStoppedEquation447BranchAtom
    (cWindow : ℕ) (ratioC rho : ℝ)
    (failure : Set (ℕ → Site))
    (R : Equation447BranchRemainingData cWindow m ratioC
      rho failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447BranchAtom cWindow m ratioC
      failure rho where
  Coord := S.Coord
  coordFintype := inferInstance
  pathAtom := S.pathAtom
  measurableSet_pathAtom := S.measurableSet_pathAtom
  profile := S.profile
  profile_lt := unprimedEven_leftWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.labels S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases
  lazyVector := S.lazyVector
  measurable_lazyVector := S.measurable_lazyVector
  nextDirection := S.nextDirection
  measurable_nextDirection := S.measurable_nextDirection
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  historyAtom := R.historyAtom
  category := R.category
  categoryLaw := R.categoryLaw
  categoryLaw_probability := R.categoryLaw_probability
  map_law := S.map_law
  failure_subset := R.failure_subset
  thetaPathEvent := R.thetaPathEvent
  theta_preimage_subset := R.theta_preimage_subset
  equation447_cover := R.equation447_cover
  bad_subset_history_allUpper := R.bad_subset_history_allUpper
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := R.history_disjoint
  history_measurable := R.history_measurable

/-- Literal deleted-path-switch version of the unprimed/even source atom. -/
noncomputable def toStoppedEquation447PathWitnessBranchAtom
    (cWindow : ℕ) (c rho : ℝ) (failure : Set (ℕ → Site))
    (R : Equation447PathWitnessBranchRemainingData cWindow m c rho
      failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c failure rho :=
  R.toStoppedEquation447PathWitnessBranchAtom
    S.measurableSet_pathAtom
    (unprimedEven_leftWinner_profile_lt_of_nonempty
      m S.k S.creationSet S.labels S.m_pos S.creation_card
        S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
        S.candidateBases)
    S.measurable_lazyVector S.measurable_nextDirection S.map_law

/-- The literal unprimed/even source atom, equation (4.47), and the
theta-free Proposition 4.8 recursion give the complete high-band path bound
outside the single global profile-exception event.  No fixed-profile
probability estimate is supplied by the caller. -/
theorem prop48_good_band_local_bound
    (cWindow : ℕ) {C cBase alpha : ℝ}
    {failure thetaPath : Set (ℕ → Site)}
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hfailure : failure ∩ S.pathAtom ⊆
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ S.pathAtom) ∩
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw ((failure \ thetaPath) ∩ S.pathAtom) ≤
      tail * simpleRandomWalkLaw S.pathAtom := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood :=
    stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
      A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  have hgoodS :
      sourceTruncatedProfileMeasure m S.profile
        ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
          sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
    change sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
    exact hgood
  apply stoppedProfileGoodEvent_local_bound S.profile S.pathAtom failure
    thetaPath (fun s ↦ (S.lazyVector s, S.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D)
    (sourceProfileThetaUpTo cWindow m
      (sourceAlphaIntervalCount m alpha) S.profile)
    (S.measurable_lazyVector.prodMk S.measurable_nextDirection)
    S.map_law hfailure htheta tail hgoodS

end UnprimedEvenLeftWinnerSource

/-- Literal primed/odd strict-right-winner source data. -/
structure PrimedOddStrictRightWinnerSource (m : ℕ) where
  q : ℕ
  k : ℕ
  creationSet : Finset Site
  first : Direction
  labels : Fin q → IncrementPair
  labels_nondistinguished : ∀ i, labels i ≠ primedDistinguishedIncrementPair
  m_pos : 0 < m
  k_pos : 0 < k
  creation_card : creationSet.card = k
  creation_pairFree : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) creationSet
  offBase : PrimedOddOffBaseMixedCondition first labels m creationSet
  terminal_mem : primedStoppedTerminalSite first labels ∈ creationSet
  admissible_nonempty :
    (actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k creationSet first labels)).Nonempty
  candidateBases : Finset
    (StoppedExternalBase (primedInitialBase first) labels)

namespace PrimedOddStrictRightWinnerSource

variable {m : ℕ} (S : PrimedOddStrictRightWinnerSource m)

noncomputable def activeBases : Finset
    (StoppedExternalBase (primedInitialBase S.first) S.labels) :=
  primedOddStrictRightWinnerBases S.first S.labels S.candidateBases

abbrev Coord := ActiveFreeStoppedBase (primedInitialBase S.first) S.labels
  S.creationSet S.activeBases

def incrementEvent : Set (ℕ → Direction) :=
  actualPrimedStoppedVectorEvent m S.k S.first S.labels
      (stoppedRunVectorBox S.q m) ∩
    stoppedSourceCondition m S.k S.creationSet

def pathAtom : Set (ℕ → Site) := simpleRandomWalk '' S.incrementEvent

noncomputable def profile : S.Coord → ℕ :=
  activeFreeStoppedShape (primedInitialBase S.first) S.labels S.creationSet
    S.activeBases

/-- The literal admissible stopped-vector witness forces every active
strict-right winner shape below the stopping level. -/
theorem profile_lt : ∀ x, S.profile x < m :=
  primedOdd_strictRightWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.first S.labels S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases

noncomputable def lazyVector : (ℕ → Site) → S.Coord → ℕ :=
  primedOddActiveFreePathLazy m S.k S.creationSet S.first S.labels
    S.activeBases

noncomputable def nextDirection : (ℕ → Site) → Direction :=
  primedOddActiveFreePathNext m S.k S.creationSet S.first S.labels
    S.activeBases

theorem measurableSet_pathAtom : MeasurableSet S.pathAtom := by
  have hIncrement : MeasurableSet S.incrementEvent := by
    rw [incrementEvent, primedOdd_source_partition m S.k S.creationSet
      S.first S.labels S.m_pos S.k_pos S.creation_pairFree]
    unfold actualPrimedStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedStoppedPrefix S.first S.labels v)
  exact HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
    |>.measurableSet_image.2 hIncrement

theorem measurable_lazyVector : Measurable S.lazyVector :=
  measurable_primedOddActiveFreePathLazy m S.k S.creationSet S.first
    S.labels S.labels_nondistinguished S.activeBases

theorem measurable_nextDirection : Measurable S.nextDirection :=
  measurable_primedOddActiveFreePathNext m S.k S.creationSet S.first
    S.labels S.labels_nondistinguished S.activeBases

theorem map_law :
    (simpleRandomWalkLaw.restrict S.pathAtom).map
        (fun s ↦ (S.lazyVector s, S.nextDirection s)) =
      simpleRandomWalkLaw S.pathAtom •
        ((sourceTruncatedProfileMeasure m S.profile).prod directionLaw) :=
  primedOdd_strictRightWinner_StoppedEquation447Atom_map_law
    m S.k S.creationSet S.first S.labels S.labels_nondistinguished
      S.m_pos S.k_pos S.creation_card S.creation_pairFree S.offBase
      S.terminal_mem S.admissible_nonempty S.candidateBases

/-- Construct an equation-(4.47) atom with the stopped product law filled in
by the checked primed-right source theorem. -/
noncomputable def toStoppedEquation447Atom
    (cWindow : ℕ) (ratioC cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site))
    (R : Equation447RemainingData cWindow m ratioC cTheta thetaPower
      failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447Atom cWindow m ratioC cTheta thetaPower failure where
  Coord := S.Coord
  coordFintype := inferInstance
  pathAtom := S.pathAtom
  measurableSet_pathAtom := S.measurableSet_pathAtom
  profile := S.profile
  profile_lt := primedOdd_strictRightWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.first S.labels S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases
  lazyVector := S.lazyVector
  measurable_lazyVector := S.measurable_lazyVector
  nextDirection := S.nextDirection
  measurable_nextDirection := S.measurable_nextDirection
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  historyAtom := R.historyAtom
  category := R.category
  categoryLaw := R.categoryLaw
  categoryLaw_probability := R.categoryLaw_probability
  map_law := S.map_law
  failure_subset := R.failure_subset
  theta_bound := R.theta_bound
  equation447_cover := R.equation447_cover
  bad_subset_history_allUpper := R.bad_subset_history_allUpper
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := R.history_disjoint
  history_measurable := R.history_measurable

/-- Branch-specific version with an explicit profile threshold. -/
noncomputable def toStoppedEquation447BranchAtom
    (cWindow : ℕ) (ratioC rho : ℝ)
    (failure : Set (ℕ → Site))
    (R : Equation447BranchRemainingData cWindow m ratioC
      rho failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447BranchAtom cWindow m ratioC
      failure rho where
  Coord := S.Coord
  coordFintype := inferInstance
  pathAtom := S.pathAtom
  measurableSet_pathAtom := S.measurableSet_pathAtom
  profile := S.profile
  profile_lt := primedOdd_strictRightWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.first S.labels S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases
  lazyVector := S.lazyVector
  measurable_lazyVector := S.measurable_lazyVector
  nextDirection := S.nextDirection
  measurable_nextDirection := S.measurable_nextDirection
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  historyAtom := R.historyAtom
  category := R.category
  categoryLaw := R.categoryLaw
  categoryLaw_probability := R.categoryLaw_probability
  map_law := S.map_law
  failure_subset := R.failure_subset
  thetaPathEvent := R.thetaPathEvent
  theta_preimage_subset := R.theta_preimage_subset
  equation447_cover := R.equation447_cover
  bad_subset_history_allUpper := R.bad_subset_history_allUpper
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := R.history_disjoint
  history_measurable := R.history_measurable

/-- Literal deleted-path-switch version of the primed/odd source atom. -/
noncomputable def toStoppedEquation447PathWitnessBranchAtom
    (cWindow : ℕ) (c rho : ℝ) (failure : Set (ℕ → Site))
    (R : Equation447PathWitnessBranchRemainingData cWindow m c rho
      failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c failure rho :=
  R.toStoppedEquation447PathWitnessBranchAtom
    S.measurableSet_pathAtom
    (primedOdd_strictRightWinner_profile_lt_of_nonempty
      m S.k S.creationSet S.first S.labels S.m_pos S.creation_card
        S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
        S.candidateBases)
    S.measurable_lazyVector S.measurable_nextDirection S.map_law

/-- The literal primed/odd source atom and equation (4.47) feed the same
theta-free Proposition 4.8 recursion as the unprimed branch. -/
theorem prop48_good_band_local_bound
    (cWindow : ℕ) {C cBase alpha : ℝ}
    {failure thetaPath : Set (ℕ → Site)}
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hfailure : failure ∩ S.pathAtom ⊆
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ S.pathAtom) ∩
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw ((failure \ thetaPath) ∩ S.pathAtom) ≤
      tail * simpleRandomWalkLaw S.pathAtom := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood :=
    stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
      A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  have hgoodS :
      sourceTruncatedProfileMeasure m S.profile
        ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
          sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
    change sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
    exact hgood
  apply stoppedProfileGoodEvent_local_bound S.profile S.pathAtom failure
    thetaPath (fun s ↦ (S.lazyVector s, S.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D)
    (sourceProfileThetaUpTo cWindow m
      (sourceAlphaIntervalCount m alpha) S.profile)
    (S.measurable_lazyVector.prodMk S.measurable_nextDirection)
    S.map_law hfailure htheta tail hgoodS

end PrimedOddStrictRightWinnerSource

/-! ### Full-terminal parity source atoms

These are the two terminal companions to the nonterminal sources above. The
path statistic's direction is taken at the completion clock `T + 1`, as
provided by `HLOZTerminalParityWinner`. -/

/-- Literal unprimed-odd terminal tie-left source data. -/
structure UnprimedOddTerminalTieLeftSource (m : ℕ) where
  q : ℕ
  k : ℕ
  creationSet : Finset Site
  labels : Fin q → IncrementPair
  labels_nondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair
  terminal : IncrementPair
  m_pos : 0 < m
  k_pos : 0 < k
  creation_card : creationSet.card = k
  creation_pairFree : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) creationSet
  offBase : UnprimedOddOffBaseMixedCondition
    labels terminal m creationSet
  terminal_mem : stoppedTerminalBase labels +
    directionStep (terminal 0) ∈ creationSet
  admissible_nonempty :
    (actualAdmissibleOddStoppedVectors m k labels terminal
      (unprimedOddSourceConstraint m k creationSet labels terminal)).Nonempty
  candidateBases : Finset (StoppedExternalBase (0, 0) labels)

namespace UnprimedOddTerminalTieLeftSource

variable {m : ℕ} (S : UnprimedOddTerminalTieLeftSource m)

noncomputable def activeBases :
    Finset (StoppedExternalBase (0, 0) S.labels) :=
  unprimedOddTieLeftWinnerBases S.labels
    (unprimedOddTerminalExternalRight S.labels S.terminal) S.candidateBases

abbrev Coord :=
  ActiveFreeStoppedBase (0, 0) S.labels S.creationSet S.activeBases

def incrementEvent : Set (ℕ → Direction) :=
  actualOddStoppedVectorEvent m S.k S.labels S.terminal
      (stoppedRunVectorBox S.q m) ∩
    stoppedSourceCondition m S.k S.creationSet

def pathAtom : Set (ℕ → Site) := simpleRandomWalk '' S.incrementEvent

noncomputable def profile : S.Coord → ℕ :=
  activeFreeStoppedShape (0, 0) S.labels S.creationSet S.activeBases

/-- The literal terminal admissible-vector witness forces every active
tie-left winner shape below the stopping level. -/
theorem profile_lt : ∀ x, S.profile x < m :=
  unprimedOdd_tieLeftWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.labels S.terminal S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases

noncomputable def lazyVector : (ℕ → Site) → S.Coord → ℕ :=
  unprimedOddActiveFreePathLazy m S.k S.creationSet S.labels S.terminal
    S.activeBases

noncomputable def nextDirection : (ℕ → Site) → Direction :=
  unprimedOddActiveFreePathNext m S.k S.creationSet S.labels S.terminal
    S.activeBases

theorem measurableSet_pathAtom : MeasurableSet S.pathAtom := by
  have hIncrement : MeasurableSet S.incrementEvent := by
    rw [incrementEvent, unprimedOdd_source_partition m S.k S.creationSet
      S.labels S.terminal S.m_pos S.k_pos S.creation_pairFree]
    unfold actualOddStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedOddStoppedPrefix S.labels v S.terminal)
  exact HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
    |>.measurableSet_image.2 hIncrement

theorem measurable_lazyVector : Measurable S.lazyVector :=
  measurable_unprimedOddActiveFreePathLazy m S.k S.creationSet S.labels
    S.labels_nondistinguished S.terminal S.activeBases

theorem measurable_nextDirection : Measurable S.nextDirection :=
  measurable_unprimedOddActiveFreePathNext m S.k S.creationSet S.labels
    S.labels_nondistinguished S.terminal S.activeBases

theorem map_law :
    (simpleRandomWalkLaw.restrict S.pathAtom).map
        (fun s ↦ (S.lazyVector s, S.nextDirection s)) =
      simpleRandomWalkLaw S.pathAtom •
        ((sourceTruncatedProfileMeasure m S.profile).prod directionLaw) :=
  unprimedOdd_sourceTieLeftWinner_StoppedEquation447Atom_map_law
    m S.k S.creationSet S.labels S.labels_nondistinguished S.terminal
      S.m_pos S.k_pos S.creation_card S.creation_pairFree S.offBase
      S.terminal_mem S.candidateBases S.admissible_nonempty

/-- Construct a literal equation-(4.47) terminal atom without a supplied
map law. -/
noncomputable def toStoppedEquation447Atom
    (cWindow : ℕ) (ratioC cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site))
    (R : Equation447RemainingData cWindow m ratioC cTheta thetaPower
      failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447Atom cWindow m ratioC cTheta thetaPower failure where
  Coord := S.Coord
  coordFintype := inferInstance
  pathAtom := S.pathAtom
  measurableSet_pathAtom := S.measurableSet_pathAtom
  profile := S.profile
  profile_lt := unprimedOdd_tieLeftWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.labels S.terminal S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases
  lazyVector := S.lazyVector
  measurable_lazyVector := S.measurable_lazyVector
  nextDirection := S.nextDirection
  measurable_nextDirection := S.measurable_nextDirection
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  historyAtom := R.historyAtom
  category := R.category
  categoryLaw := R.categoryLaw
  categoryLaw_probability := R.categoryLaw_probability
  map_law := S.map_law
  failure_subset := R.failure_subset
  theta_bound := R.theta_bound
  equation447_cover := R.equation447_cover
  bad_subset_history_allUpper := R.bad_subset_history_allUpper
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := R.history_disjoint
  history_measurable := R.history_measurable

/-- Branch-specific terminal version with an explicit profile threshold. -/
noncomputable def toStoppedEquation447BranchAtom
    (cWindow : ℕ) (ratioC rho : ℝ)
    (failure : Set (ℕ → Site))
    (R : Equation447BranchRemainingData cWindow m ratioC
      rho failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447BranchAtom cWindow m ratioC
      failure rho where
  Coord := S.Coord
  coordFintype := inferInstance
  pathAtom := S.pathAtom
  measurableSet_pathAtom := S.measurableSet_pathAtom
  profile := S.profile
  profile_lt := unprimedOdd_tieLeftWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.labels S.terminal S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases
  lazyVector := S.lazyVector
  measurable_lazyVector := S.measurable_lazyVector
  nextDirection := S.nextDirection
  measurable_nextDirection := S.measurable_nextDirection
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  historyAtom := R.historyAtom
  category := R.category
  categoryLaw := R.categoryLaw
  categoryLaw_probability := R.categoryLaw_probability
  map_law := S.map_law
  failure_subset := R.failure_subset
  thetaPathEvent := R.thetaPathEvent
  theta_preimage_subset := R.theta_preimage_subset
  equation447_cover := R.equation447_cover
  bad_subset_history_allUpper := R.bad_subset_history_allUpper
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := R.history_disjoint
  history_measurable := R.history_measurable

/-- Literal deleted-path-switch version of the unprimed odd-terminal atom. -/
noncomputable def toStoppedEquation447PathWitnessBranchAtom
    (cWindow : ℕ) (c rho : ℝ) (failure : Set (ℕ → Site))
    (R : Equation447PathWitnessBranchRemainingData cWindow m c rho
      failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c failure rho :=
  R.toStoppedEquation447PathWitnessBranchAtom
    S.measurableSet_pathAtom
    (unprimedOdd_tieLeftWinner_profile_lt_of_nonempty
      m S.k S.creationSet S.labels S.terminal S.m_pos S.creation_card
        S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
        S.candidateBases)
    S.measurable_lazyVector S.measurable_nextDirection S.map_law

/-- The unprimed odd-terminal source atom and equation (4.47) give the
theta-free Proposition 4.8 high-band bound on this parity branch. -/
theorem prop48_good_band_local_bound
    (cWindow : ℕ) {C cBase alpha : ℝ}
    {failure thetaPath : Set (ℕ → Site)}
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hfailure : failure ∩ S.pathAtom ⊆
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ S.pathAtom) ∩
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw ((failure \ thetaPath) ∩ S.pathAtom) ≤
      tail * simpleRandomWalkLaw S.pathAtom := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood :=
    stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
      A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  have hgoodS :
      sourceTruncatedProfileMeasure m S.profile
        ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
          sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
    change sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
    exact hgood
  apply stoppedProfileGoodEvent_local_bound S.profile S.pathAtom failure
    thetaPath (fun s ↦ (S.lazyVector s, S.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D)
    (sourceProfileThetaUpTo cWindow m
      (sourceAlphaIntervalCount m alpha) S.profile)
    (S.measurable_lazyVector.prodMk S.measurable_nextDirection)
    S.map_law hfailure htheta tail hgoodS

end UnprimedOddTerminalTieLeftSource

/-- Literal primed-even terminal strict-right source data. -/
structure PrimedEvenTerminalStrictRightSource (m : ℕ) where
  q : ℕ
  k : ℕ
  creationSet : Finset Site
  first : Direction
  labels : Fin q → IncrementPair
  labels_nondistinguished : ∀ i,
    labels i ≠ primedDistinguishedIncrementPair
  terminal : IncrementPair
  m_pos : 0 < m
  k_pos : 0 < k
  creation_card : creationSet.card = k
  creation_pairFree : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) creationSet
  offBase : PrimedEvenOffBaseMixedCondition
    first labels terminal m creationSet
  terminal_mem : primedStoppedTerminalSite first labels +
    directionStep (terminal 0) ∈ creationSet
  admissible_nonempty :
    (actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (primedEvenSourceConstraint m k creationSet first labels terminal)).Nonempty
  candidateBases : Finset
    (StoppedExternalBase (primedInitialBase first) labels)

namespace PrimedEvenTerminalStrictRightSource

variable {m : ℕ} (S : PrimedEvenTerminalStrictRightSource m)

noncomputable def activeBases : Finset
    (StoppedExternalBase (primedInitialBase S.first) S.labels) :=
  primedEvenStrictRightWinnerBases S.first S.labels
    (primedEvenTerminalExternalLeft S.first S.labels S.terminal)
      S.candidateBases

abbrev Coord := ActiveFreeStoppedBase (primedInitialBase S.first) S.labels
  S.creationSet S.activeBases

def incrementEvent : Set (ℕ → Direction) :=
  actualPrimedTerminalVectorEvent m S.k S.first S.labels S.terminal
      (stoppedRunVectorBox S.q m) ∩
    stoppedSourceCondition m S.k S.creationSet

def pathAtom : Set (ℕ → Site) := simpleRandomWalk '' S.incrementEvent

noncomputable def profile : S.Coord → ℕ :=
  activeFreeStoppedShape (primedInitialBase S.first) S.labels S.creationSet
    S.activeBases

/-- The literal terminal admissible-vector witness forces every active
strict-right winner shape below the stopping level. -/
theorem profile_lt : ∀ x, S.profile x < m :=
  primedEven_strictRightWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.first S.labels S.terminal S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases

noncomputable def lazyVector : (ℕ → Site) → S.Coord → ℕ :=
  primedEvenActiveFreePathLazy m S.k S.creationSet S.first S.labels S.terminal
    S.activeBases

noncomputable def nextDirection : (ℕ → Site) → Direction :=
  primedEvenActiveFreePathNext m S.k S.creationSet S.first S.labels S.terminal
    S.activeBases

theorem measurableSet_pathAtom : MeasurableSet S.pathAtom := by
  have hIncrement : MeasurableSet S.incrementEvent := by
    rw [incrementEvent, primedEven_source_partition m S.k S.creationSet
      S.first S.labels S.terminal S.m_pos S.k_pos S.creation_pairFree]
    unfold actualPrimedTerminalVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedTerminalStoppedPrefix
          S.first S.labels v S.terminal)
  exact HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
    |>.measurableSet_image.2 hIncrement

theorem measurable_lazyVector : Measurable S.lazyVector :=
  measurable_primedEvenActiveFreePathLazy m S.k S.creationSet S.first
    S.labels S.labels_nondistinguished S.terminal S.activeBases

theorem measurable_nextDirection : Measurable S.nextDirection :=
  measurable_primedEvenActiveFreePathNext m S.k S.creationSet S.first
    S.labels S.labels_nondistinguished S.terminal S.activeBases

theorem map_law :
    (simpleRandomWalkLaw.restrict S.pathAtom).map
        (fun s ↦ (S.lazyVector s, S.nextDirection s)) =
      simpleRandomWalkLaw S.pathAtom •
        ((sourceTruncatedProfileMeasure m S.profile).prod directionLaw) :=
  primedEven_sourceStrictRightWinner_StoppedEquation447Atom_map_law
    m S.k S.creationSet S.first S.labels S.labels_nondistinguished
      S.terminal S.m_pos S.k_pos S.creation_card S.creation_pairFree
      S.offBase S.terminal_mem S.candidateBases S.admissible_nonempty

/-- Construct a literal equation-(4.47) terminal atom without a supplied
map law. -/
noncomputable def toStoppedEquation447Atom
    (cWindow : ℕ) (ratioC cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site))
    (R : Equation447RemainingData cWindow m ratioC cTheta thetaPower
      failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447Atom cWindow m ratioC cTheta thetaPower failure where
  Coord := S.Coord
  coordFintype := inferInstance
  pathAtom := S.pathAtom
  measurableSet_pathAtom := S.measurableSet_pathAtom
  profile := S.profile
  profile_lt := primedEven_strictRightWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.first S.labels S.terminal S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases
  lazyVector := S.lazyVector
  measurable_lazyVector := S.measurable_lazyVector
  nextDirection := S.nextDirection
  measurable_nextDirection := S.measurable_nextDirection
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  historyAtom := R.historyAtom
  category := R.category
  categoryLaw := R.categoryLaw
  categoryLaw_probability := R.categoryLaw_probability
  map_law := S.map_law
  failure_subset := R.failure_subset
  theta_bound := R.theta_bound
  equation447_cover := R.equation447_cover
  bad_subset_history_allUpper := R.bad_subset_history_allUpper
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := R.history_disjoint
  history_measurable := R.history_measurable

/-- Branch-specific terminal version with an explicit profile threshold. -/
noncomputable def toStoppedEquation447BranchAtom
    (cWindow : ℕ) (ratioC rho : ℝ)
    (failure : Set (ℕ → Site))
    (R : Equation447BranchRemainingData cWindow m ratioC
      rho failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447BranchAtom cWindow m ratioC
      failure rho where
  Coord := S.Coord
  coordFintype := inferInstance
  pathAtom := S.pathAtom
  measurableSet_pathAtom := S.measurableSet_pathAtom
  profile := S.profile
  profile_lt := primedEven_strictRightWinner_profile_lt_of_nonempty
    m S.k S.creationSet S.first S.labels S.terminal S.m_pos S.creation_card
      S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
      S.candidateBases
  lazyVector := S.lazyVector
  measurable_lazyVector := S.measurable_lazyVector
  nextDirection := S.nextDirection
  measurable_nextDirection := S.measurable_nextDirection
  forcedDirection := R.forcedDirection
  D := R.D
  badAtom := R.badAtom
  historyAtom := R.historyAtom
  category := R.category
  categoryLaw := R.categoryLaw
  categoryLaw_probability := R.categoryLaw_probability
  map_law := S.map_law
  failure_subset := R.failure_subset
  thetaPathEvent := R.thetaPathEvent
  theta_preimage_subset := R.theta_preimage_subset
  equation447_cover := R.equation447_cover
  bad_subset_history_allUpper := R.bad_subset_history_allUpper
  conditional_category_product := R.conditional_category_product
  category_mass_ratio := R.category_mass_ratio
  history_disjoint := R.history_disjoint
  history_measurable := R.history_measurable

/-- Literal deleted-path-switch version of the primed even-terminal atom. -/
noncomputable def toStoppedEquation447PathWitnessBranchAtom
    (cWindow : ℕ) (c rho : ℝ) (failure : Set (ℕ → Site))
    (R : Equation447PathWitnessBranchRemainingData cWindow m c rho
      failure S.pathAtom S.profile S.lazyVector S.nextDirection) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c failure rho :=
  R.toStoppedEquation447PathWitnessBranchAtom
    S.measurableSet_pathAtom
    (primedEven_strictRightWinner_profile_lt_of_nonempty
      m S.k S.creationSet S.first S.labels S.terminal S.m_pos S.creation_card
        S.creation_pairFree S.offBase S.terminal_mem S.admissible_nonempty
        S.candidateBases)
    S.measurable_lazyVector S.measurable_nextDirection S.map_law

/-- The primed even-terminal source atom and equation (4.47) give the
theta-free Proposition 4.8 high-band bound on this parity branch. -/
theorem prop48_good_band_local_bound
    (cWindow : ℕ) {C cBase alpha : ℝ}
    {failure thetaPath : Set (ℕ → Site)}
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hfailure : failure ∩ S.pathAtom ⊆
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ S.pathAtom) ∩
      (fun s ↦ (S.lazyVector s, S.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw ((failure \ thetaPath) ∩ S.pathAtom) ≤
      tail * simpleRandomWalkLaw S.pathAtom := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood :=
    stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
      A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  have hgoodS :
      sourceTruncatedProfileMeasure m S.profile
        ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
          sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
    change sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
    exact hgood
  apply stoppedProfileGoodEvent_local_bound S.profile S.pathAtom failure
    thetaPath (fun s ↦ (S.lazyVector s, S.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D)
    (sourceProfileThetaUpTo cWindow m
      (sourceAlphaIntervalCount m alpha) S.profile)
    (S.measurable_lazyVector.prodMk S.measurable_nextDirection)
    S.map_law hfailure htheta tail hgoodS

end PrimedEvenTerminalStrictRightSource

/-! ### Theta-free stopped decompositions for Proposition 4.8

The preceding four local theorems are now assembled without reintroducing
the former fixed-profile `base_bound` and per-level `theta_bound` fields.
Every atom carries literal stopped source data, the coded equation-(4.47)
identification, and only the two deterministic event inclusions.  A single
path-space `thetaPath` is removed before aggregation and can subsequently be
paid for by Proposition 4.5. -/

theorem measure_diff_le_of_disjoint_stopped_atoms
    {failure thetaPath : Set (ℕ → Site)}
    (atom : ℕ → Set (ℕ → Site)) (tail : ℝ≥0∞)
    (cover : failure ⊆ ⋃ n, atom n)
    (pairwise_disjoint : Pairwise fun n l ↦ Disjoint (atom n) (atom l))
    (measurable_atom : ∀ n, MeasurableSet (atom n))
    (local_bound : ∀ n,
      simpleRandomWalkLaw ((failure \ thetaPath) ∩ atom n) ≤
        tail * simpleRandomWalkLaw (atom n)) :
    simpleRandomWalkLaw (failure \ thetaPath) ≤ tail := by
  apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw
    (failure \ thetaPath) (fun n ↦ (failure \ thetaPath) ∩ atom n)
      atom tail
  · intro omega homega
    rcases Set.mem_iUnion.mp (cover homega.1) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, homega, hn⟩
  · exact local_bound
  · exact pairwise_disjoint
  · exact measurable_atom

/-- One literal unprimed/even stopped atom for the theta-free Proposition
4.8 reduction.  The record contains no probability bound. -/
structure UnprimedEvenGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set (ℕ → Site)) where
  source : UnprimedEvenLeftWinnerSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  theta_subset : (failure ∩ source.pathAtom) ∩
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
        (Set.univ : Set Direction)) ⊆ thetaPath

/-- Reuse a branch equation-(4.47) law in the unprimed/even
Proposition-4.8 atom.  Only the two band-specific path identifications remain
to be supplied. -/
noncomputable def UnprimedEvenGoodBandAtomData.ofBranchRemaining
    {cWindow m : ℕ} {C alpha rho : ℝ}
    {failure thetaPath branchFailure branchTheta : Set (ℕ → Site)}
    (source : UnprimedEvenLeftWinnerSource m)
    (R : Equation447CodedBranchRemainingData cWindow m C rho
      branchFailure branchTheta source.pathAtom source.profile
      source.lazyVector source.nextDirection)
    (hfailure : failure ∩ source.pathAtom ⊆
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
            source.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ source.pathAtom) ∩
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath) :
    UnprimedEvenGoodBandAtomData cWindow m C alpha failure thetaPath where
  source := source
  remaining := R.toProfileData
  failure_subset := hfailure
  theta_subset := htheta

/-- A countable, disjoint literal unprimed/even decomposition. -/
structure UnprimedEvenGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set (ℕ → Site)) where
  atoms : ℕ → UnprimedEvenGoodBandAtomData cWindow m C alpha failure thetaPath
  cover : failure ⊆ ⋃ n, (atoms n).source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).source.pathAtom (atoms l).source.pathAtom

theorem measure_diff_le_of_unprimedEvenGoodBandDecomposition
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    {failure thetaPath : Set (ℕ → Site)}
    (D : UnprimedEvenGoodBandDecomposition cWindow m C alpha failure thetaPath)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure \ thetaPath) ≤ tail := by
  apply measure_diff_le_of_disjoint_stopped_atoms
    (fun n ↦ (D.atoms n).source.pathAtom) tail D.cover D.pairwise_disjoint
  · intro n
    exact (D.atoms n).source.measurableSet_pathAtom
  · intro n
    exact (D.atoms n).source.prop48_good_band_local_bound cWindow
      (D.atoms n).remaining G hC halpha hAlpha
      (D.atoms n).failure_subset (D.atoms n).theta_subset hbaseAbsorb
      tail hshift

/-- One literal primed/odd strict-right atom for the theta-free reduction. -/
structure PrimedOddGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set (ℕ → Site)) where
  source : PrimedOddStrictRightWinnerSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  theta_subset : (failure ∩ source.pathAtom) ∩
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
        (Set.univ : Set Direction)) ⊆ thetaPath

/-- Reuse a branch equation-(4.47) law in the primed/odd
Proposition-4.8 atom. -/
noncomputable def PrimedOddGoodBandAtomData.ofBranchRemaining
    {cWindow m : ℕ} {C alpha rho : ℝ}
    {failure thetaPath branchFailure branchTheta : Set (ℕ → Site)}
    (source : PrimedOddStrictRightWinnerSource m)
    (R : Equation447CodedBranchRemainingData cWindow m C rho
      branchFailure branchTheta source.pathAtom source.profile
      source.lazyVector source.nextDirection)
    (hfailure : failure ∩ source.pathAtom ⊆
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
            source.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ source.pathAtom) ∩
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath) :
    PrimedOddGoodBandAtomData cWindow m C alpha failure thetaPath where
  source := source
  remaining := R.toProfileData
  failure_subset := hfailure
  theta_subset := htheta

structure PrimedOddGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set (ℕ → Site)) where
  atoms : ℕ → PrimedOddGoodBandAtomData cWindow m C alpha failure thetaPath
  cover : failure ⊆ ⋃ n, (atoms n).source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).source.pathAtom (atoms l).source.pathAtom

theorem measure_diff_le_of_primedOddGoodBandDecomposition
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    {failure thetaPath : Set (ℕ → Site)}
    (D : PrimedOddGoodBandDecomposition cWindow m C alpha failure thetaPath)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure \ thetaPath) ≤ tail := by
  apply measure_diff_le_of_disjoint_stopped_atoms
    (fun n ↦ (D.atoms n).source.pathAtom) tail D.cover D.pairwise_disjoint
  · intro n
    exact (D.atoms n).source.measurableSet_pathAtom
  · intro n
    exact (D.atoms n).source.prop48_good_band_local_bound cWindow
      (D.atoms n).remaining G hC halpha hAlpha
      (D.atoms n).failure_subset (D.atoms n).theta_subset hbaseAbsorb
      tail hshift

/-- One literal unprimed odd-terminal tie-left atom for the theta-free
reduction. -/
structure UnprimedOddTerminalGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set (ℕ → Site)) where
  source : UnprimedOddTerminalTieLeftSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  theta_subset : (failure ∩ source.pathAtom) ∩
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
        (Set.univ : Set Direction)) ⊆ thetaPath

/-- Reuse a branch equation-(4.47) law in the unprimed odd-terminal
Proposition-4.8 atom. -/
noncomputable def UnprimedOddTerminalGoodBandAtomData.ofBranchRemaining
    {cWindow m : ℕ} {C alpha rho : ℝ}
    {failure thetaPath branchFailure branchTheta : Set (ℕ → Site)}
    (source : UnprimedOddTerminalTieLeftSource m)
    (R : Equation447CodedBranchRemainingData cWindow m C rho
      branchFailure branchTheta source.pathAtom source.profile
      source.lazyVector source.nextDirection)
    (hfailure : failure ∩ source.pathAtom ⊆
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
            source.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ source.pathAtom) ∩
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath) :
    UnprimedOddTerminalGoodBandAtomData cWindow m C alpha
      failure thetaPath where
  source := source
  remaining := R.toProfileData
  failure_subset := hfailure
  theta_subset := htheta

structure UnprimedOddTerminalGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set (ℕ → Site)) where
  atoms : ℕ → UnprimedOddTerminalGoodBandAtomData cWindow m C alpha
    failure thetaPath
  cover : failure ⊆ ⋃ n, (atoms n).source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).source.pathAtom (atoms l).source.pathAtom

theorem measure_diff_le_of_unprimedOddTerminalGoodBandDecomposition
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    {failure thetaPath : Set (ℕ → Site)}
    (D : UnprimedOddTerminalGoodBandDecomposition cWindow m C alpha
      failure thetaPath)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure \ thetaPath) ≤ tail := by
  apply measure_diff_le_of_disjoint_stopped_atoms
    (fun n ↦ (D.atoms n).source.pathAtom) tail D.cover D.pairwise_disjoint
  · intro n
    exact (D.atoms n).source.measurableSet_pathAtom
  · intro n
    exact (D.atoms n).source.prop48_good_band_local_bound cWindow
      (D.atoms n).remaining G hC halpha hAlpha
      (D.atoms n).failure_subset (D.atoms n).theta_subset hbaseAbsorb
      tail hshift

/-- One literal primed even-terminal strict-right atom for the theta-free
reduction. -/
structure PrimedEvenTerminalGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set (ℕ → Site)) where
  source : PrimedEvenTerminalStrictRightSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  theta_subset : (failure ∩ source.pathAtom) ∩
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
        (Set.univ : Set Direction)) ⊆ thetaPath

/-- Reuse a branch equation-(4.47) law in the primed even-terminal
Proposition-4.8 atom. -/
noncomputable def PrimedEvenTerminalGoodBandAtomData.ofBranchRemaining
    {cWindow m : ℕ} {C alpha rho : ℝ}
    {failure thetaPath branchFailure branchTheta : Set (ℕ → Site)}
    (source : PrimedEvenTerminalStrictRightSource m)
    (R : Equation447CodedBranchRemainingData cWindow m C rho
      branchFailure branchTheta source.pathAtom source.profile
      source.lazyVector source.nextDirection)
    (hfailure : failure ∩ source.pathAtom ⊆
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
            source.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ R.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ source.pathAtom) ∩
      (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
        (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m alpha) source.profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath) :
    PrimedEvenTerminalGoodBandAtomData cWindow m C alpha
      failure thetaPath where
  source := source
  remaining := R.toProfileData
  failure_subset := hfailure
  theta_subset := htheta

structure PrimedEvenTerminalGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ)
    (failure thetaPath : Set (ℕ → Site)) where
  atoms : ℕ → PrimedEvenTerminalGoodBandAtomData cWindow m C alpha
    failure thetaPath
  cover : failure ⊆ ⋃ n, (atoms n).source.pathAtom
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).source.pathAtom (atoms l).source.pathAtom

theorem measure_diff_le_of_primedEvenTerminalGoodBandDecomposition
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    {failure thetaPath : Set (ℕ → Site)}
    (D : PrimedEvenTerminalGoodBandDecomposition cWindow m C alpha
      failure thetaPath)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure \ thetaPath) ≤ tail := by
  apply measure_diff_le_of_disjoint_stopped_atoms
    (fun n ↦ (D.atoms n).source.pathAtom) tail D.cover D.pairwise_disjoint
  · intro n
    exact (D.atoms n).source.measurableSet_pathAtom
  · intro n
    exact (D.atoms n).source.prop48_good_band_local_bound cWindow
      (D.atoms n).remaining G hC halpha hAlpha
      (D.atoms n).failure_subset (D.atoms n).theta_subset hbaseAbsorb
      tail hshift

/-- The two stopping-time parities of the left-winner branch.  The target
already includes whatever stopped history is needed by the eventual
Lemma-4.10 application; only the displayed union cover is required. -/
structure LeftWinnerParityGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ)
    (target thetaPath : Set (ℕ → Site)) where
  evenFailure : Set (ℕ → Site)
  oddTerminalFailure : Set (ℕ → Site)
  cover : target ⊆ evenFailure ∪ oddTerminalFailure
  even : UnprimedEvenGoodBandDecomposition cWindow m C alpha
    evenFailure thetaPath
  oddTerminal : UnprimedOddTerminalGoodBandDecomposition cWindow m C alpha
    oddTerminalFailure thetaPath

theorem measure_diff_le_of_leftWinnerParityGoodBandDecomposition
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    {target thetaPath : Set (ℕ → Site)}
    (D : LeftWinnerParityGoodBandDecomposition cWindow m C alpha
      target thetaPath)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (branchTail tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ branchTail)
    (habsorb : 2 * branchTail ≤ tail) :
    simpleRandomWalkLaw (target \ thetaPath) ≤ tail := by
  have heven := measure_diff_le_of_unprimedEvenGoodBandDecomposition
    D.even G hC halpha hAlpha hbaseAbsorb branchTail hshift
  have hodd := measure_diff_le_of_unprimedOddTerminalGoodBandDecomposition
    D.oddTerminal G hC halpha hAlpha hbaseAbsorb branchTail hshift
  calc
    simpleRandomWalkLaw (target \ thetaPath) ≤
        simpleRandomWalkLaw
          ((D.evenFailure \ thetaPath) ∪
            (D.oddTerminalFailure \ thetaPath)) := by
      apply measure_mono
      intro omega homega
      rcases D.cover homega.1 with heven' | hodd'
      · exact Or.inl ⟨heven', homega.2⟩
      · exact Or.inr ⟨hodd', homega.2⟩
    _ ≤ simpleRandomWalkLaw (D.evenFailure \ thetaPath) +
        simpleRandomWalkLaw (D.oddTerminalFailure \ thetaPath) :=
      measure_union_le _ _
    _ ≤ branchTail + branchTail := add_le_add heven hodd
    _ = 2 * branchTail := by ring
    _ ≤ tail := habsorb

/-- The two stopping-time parities of the strict-right branch. -/
structure RightWinnerParityGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ)
    (target thetaPath : Set (ℕ → Site)) where
  oddFailure : Set (ℕ → Site)
  evenTerminalFailure : Set (ℕ → Site)
  cover : target ⊆ oddFailure ∪ evenTerminalFailure
  odd : PrimedOddGoodBandDecomposition cWindow m C alpha
    oddFailure thetaPath
  evenTerminal : PrimedEvenTerminalGoodBandDecomposition cWindow m C alpha
    evenTerminalFailure thetaPath

theorem measure_diff_le_of_rightWinnerParityGoodBandDecomposition
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    {target thetaPath : Set (ℕ → Site)}
    (D : RightWinnerParityGoodBandDecomposition cWindow m C alpha
      target thetaPath)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (branchTail tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ branchTail)
    (habsorb : 2 * branchTail ≤ tail) :
    simpleRandomWalkLaw (target \ thetaPath) ≤ tail := by
  have hodd := measure_diff_le_of_primedOddGoodBandDecomposition
    D.odd G hC halpha hAlpha hbaseAbsorb branchTail hshift
  have heven := measure_diff_le_of_primedEvenTerminalGoodBandDecomposition
    D.evenTerminal G hC halpha hAlpha hbaseAbsorb branchTail hshift
  calc
    simpleRandomWalkLaw (target \ thetaPath) ≤
        simpleRandomWalkLaw
          ((D.oddFailure \ thetaPath) ∪
            (D.evenTerminalFailure \ thetaPath)) := by
      apply measure_mono
      intro omega homega
      rcases D.cover homega.1 with hodd' | heven'
      · exact Or.inl ⟨hodd', homega.2⟩
      · exact Or.inr ⟨heven', homega.2⟩
    _ ≤ simpleRandomWalkLaw (D.oddFailure \ thetaPath) +
        simpleRandomWalkLaw (D.evenTerminalFailure \ thetaPath) :=
      measure_union_le _ _
    _ ≤ branchTail + branchTail := add_le_add hodd heven
    _ = 2 * branchTail := by ring
    _ ≤ tail := habsorb

/-! ### Strong atom-conditioned banded decompositions

The older theta-free structures above remove one path event from every
profile atom.  The four structures below attach an arbitrary-interval
Proposition-4.5 input separately at every level.  Their implications are
formally valid, but the input is stronger than the literal source law because
its negative-binomial fields are conditioned on a complete stopped atom.
They are retained as an auxiliary API and are not consumed by the final
source closure. -/

private theorem unprimedEven_good_profile_bound
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    (S : UnprimedEvenLeftWinnerSource m)
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood := stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
    A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  change sourceTruncatedProfileMeasure m S.profile
    ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
      sourceProfileThetaUpTo cWindow m
        (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
  exact hgood

private theorem primedOdd_good_profile_bound
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    (S : PrimedOddStrictRightWinnerSource m)
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood := stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
    A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  change sourceTruncatedProfileMeasure m S.profile
    ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
      sourceProfileThetaUpTo cWindow m
        (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
  exact hgood

private theorem unprimedOddTerminal_good_profile_bound
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    (S : UnprimedOddTerminalTieLeftSource m)
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood := stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
    A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  change sourceTruncatedProfileMeasure m S.profile
    ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
      sourceProfileThetaUpTo cWindow m
        (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
  exact hgood

private theorem primedEvenTerminal_good_profile_bound
    {cWindow m : ℕ} {C cBase alpha : ℝ}
    (S : PrimedEvenTerminalStrictRightSource m)
    (R : Equation447CodedProfileData cWindow m C S.profile)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    sourceTruncatedProfileMeasure m S.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail := by
  let sourceInst : Fintype S.Coord := inferInstance
  letI : Fintype S.Coord := sourceInst
  let A := S.toStoppedEquation447BranchAtom cWindow C
    (Real.log (m : ℝ) ^ 2) ∅
      (R.toRemainingData S.pathAtom S.lazyVector S.nextDirection)
  have hgood := stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
    A G hC halpha hAlpha hbaseAbsorb tail hshift
  have hcoordFintype : A.coordFintype = sourceInst := Subsingleton.elim _ _
  rw [hcoordFintype] at hgood
  change sourceTruncatedProfileMeasure m S.profile
    ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) S.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ R.D) \
      sourceProfileThetaUpTo cWindow m
        (sourceAlphaIntervalCount m alpha) S.profile) ≤ tail at hgood
  exact hgood

/-- Auxiliary unprimed/even atom with one strong atom-conditioned
Proposition-4.5 input for each recursive interval level.  The final literal
source closure does not consume this stronger package. -/
structure UnprimedEvenSourceBandedGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ) (failure : Set (ℕ → Site)) where
  source : UnprimedEvenLeftWinnerSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  bands : StoppedProfileBandedThetaInputs cWindow m source.k alpha
    source.profile source.pathAtom failure
      (fun s ↦ (source.lazyVector s, source.nextDirection s))

structure PrimedOddSourceBandedGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ) (failure : Set (ℕ → Site)) where
  source : PrimedOddStrictRightWinnerSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  bands : StoppedProfileBandedThetaInputs cWindow m source.k alpha
    source.profile source.pathAtom failure
      (fun s ↦ (source.lazyVector s, source.nextDirection s))

structure UnprimedOddTerminalSourceBandedGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ) (failure : Set (ℕ → Site)) where
  source : UnprimedOddTerminalTieLeftSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  bands : StoppedProfileBandedThetaInputs cWindow m source.k alpha
    source.profile source.pathAtom failure
      (fun s ↦ (source.lazyVector s, source.nextDirection s))

structure PrimedEvenTerminalSourceBandedGoodBandAtomData
    (cWindow m : ℕ) (C alpha : ℝ) (failure : Set (ℕ → Site)) where
  source : PrimedEvenTerminalStrictRightSource m
  remaining : Equation447CodedProfileData cWindow m C source.profile
  failure_subset : failure ∩ source.pathAtom ⊆
    (fun s ↦ (source.lazyVector s, source.nextDirection s)) ⁻¹'
      (((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          source.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ remaining.D)) ×ˢ
        (Set.univ : Set Direction))
  bands : StoppedProfileBandedThetaInputs cWindow m source.k alpha
    source.profile source.pathAtom failure
      (fun s ↦ (source.lazyVector s, source.nextDirection s))

theorem UnprimedEvenSourceBandedGoodBandAtomData.local_bound
    {cWindow m : ℕ} {C cBase alpha : ℝ} {failure : Set (ℕ → Site)}
    (D : UnprimedEvenSourceBandedGoodBandAtomData cWindow m C alpha failure)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hscales : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
      SourceIntervalScale m (sourceIntervalLower m (l.1 + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l.1 + 1)))
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ D.source.pathAtom) ≤
      (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m) *
          simpleRandomWalkLaw D.source.pathAtom := by
  apply stoppedProfileEvent_local_bound_of_source_banded_theta
    D.source.profile D.source.pathAtom failure
    (fun s ↦ (D.source.lazyVector s, D.source.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) D.source.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha)) ∩ D.remaining.D)
    D.bands hscales
    (D.source.measurable_lazyVector.prodMk D.source.measurable_nextDirection)
    D.source.map_law D.failure_subset tail
  exact unprimedEven_good_profile_bound D.source D.remaining G hC halpha hAlpha
    hbaseAbsorb tail hshift

theorem PrimedOddSourceBandedGoodBandAtomData.local_bound
    {cWindow m : ℕ} {C cBase alpha : ℝ} {failure : Set (ℕ → Site)}
    (D : PrimedOddSourceBandedGoodBandAtomData cWindow m C alpha failure)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hscales : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
      SourceIntervalScale m (sourceIntervalLower m (l.1 + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l.1 + 1)))
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ D.source.pathAtom) ≤
      (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m) *
          simpleRandomWalkLaw D.source.pathAtom := by
  apply stoppedProfileEvent_local_bound_of_source_banded_theta
    D.source.profile D.source.pathAtom failure
    (fun s ↦ (D.source.lazyVector s, D.source.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) D.source.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha)) ∩ D.remaining.D)
    D.bands hscales
    (D.source.measurable_lazyVector.prodMk D.source.measurable_nextDirection)
    D.source.map_law D.failure_subset tail
  exact primedOdd_good_profile_bound D.source D.remaining G hC halpha hAlpha
    hbaseAbsorb tail hshift

theorem UnprimedOddTerminalSourceBandedGoodBandAtomData.local_bound
    {cWindow m : ℕ} {C cBase alpha : ℝ} {failure : Set (ℕ → Site)}
    (D : UnprimedOddTerminalSourceBandedGoodBandAtomData cWindow m C alpha failure)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hscales : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
      SourceIntervalScale m (sourceIntervalLower m (l.1 + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l.1 + 1)))
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ D.source.pathAtom) ≤
      (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m) *
          simpleRandomWalkLaw D.source.pathAtom := by
  apply stoppedProfileEvent_local_bound_of_source_banded_theta
    D.source.profile D.source.pathAtom failure
    (fun s ↦ (D.source.lazyVector s, D.source.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) D.source.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha)) ∩ D.remaining.D)
    D.bands hscales
    (D.source.measurable_lazyVector.prodMk D.source.measurable_nextDirection)
    D.source.map_law D.failure_subset tail
  exact unprimedOddTerminal_good_profile_bound D.source D.remaining G hC
    halpha hAlpha hbaseAbsorb tail hshift

theorem PrimedEvenTerminalSourceBandedGoodBandAtomData.local_bound
    {cWindow m : ℕ} {C cBase alpha : ℝ} {failure : Set (ℕ → Site)}
    (D : PrimedEvenTerminalSourceBandedGoodBandAtomData cWindow m C alpha failure)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hscales : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
      SourceIntervalScale m (sourceIntervalLower m (l.1 + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l.1 + 1)))
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ D.source.pathAtom) ≤
      (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m) *
          simpleRandomWalkLaw D.source.pathAtom := by
  apply stoppedProfileEvent_local_bound_of_source_banded_theta
    D.source.profile D.source.pathAtom failure
    (fun s ↦ (D.source.lazyVector s, D.source.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) D.source.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha)) ∩ D.remaining.D)
    D.bands hscales
    (D.source.measurable_lazyVector.prodMk D.source.measurable_nextDirection)
    D.source.map_law D.failure_subset tail
  exact primedEvenTerminal_good_profile_bound D.source D.remaining G hC
    halpha hAlpha hbaseAbsorb tail hshift

structure LeftWinnerSourceBandedGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ) (target : Set (ℕ → Site)) where
  evenFailure : Set (ℕ → Site)
  oddTerminalFailure : Set (ℕ → Site)
  cover : target ⊆ evenFailure ∪ oddTerminalFailure
  evenAtoms : ℕ → UnprimedEvenSourceBandedGoodBandAtomData
    cWindow m C alpha evenFailure
  even_cover : evenFailure ⊆ ⋃ n, (evenAtoms n).source.pathAtom
  even_disjoint : Pairwise fun n l ↦
    Disjoint (evenAtoms n).source.pathAtom (evenAtoms l).source.pathAtom
  oddAtoms : ℕ → UnprimedOddTerminalSourceBandedGoodBandAtomData
    cWindow m C alpha oddTerminalFailure
  odd_cover : oddTerminalFailure ⊆ ⋃ n, (oddAtoms n).source.pathAtom
  odd_disjoint : Pairwise fun n l ↦
    Disjoint (oddAtoms n).source.pathAtom (oddAtoms l).source.pathAtom

structure RightWinnerSourceBandedGoodBandDecomposition
    (cWindow m : ℕ) (C alpha : ℝ) (target : Set (ℕ → Site)) where
  oddFailure : Set (ℕ → Site)
  evenTerminalFailure : Set (ℕ → Site)
  cover : target ⊆ oddFailure ∪ evenTerminalFailure
  oddAtoms : ℕ → PrimedOddSourceBandedGoodBandAtomData
    cWindow m C alpha oddFailure
  odd_cover : oddFailure ⊆ ⋃ n, (oddAtoms n).source.pathAtom
  odd_disjoint : Pairwise fun n l ↦
    Disjoint (oddAtoms n).source.pathAtom (oddAtoms l).source.pathAtom
  evenAtoms : ℕ → PrimedEvenTerminalSourceBandedGoodBandAtomData
    cWindow m C alpha evenTerminalFailure
  even_cover : evenTerminalFailure ⊆ ⋃ n, (evenAtoms n).source.pathAtom
  even_disjoint : Pairwise fun n l ↦
    Disjoint (evenAtoms n).source.pathAtom (evenAtoms l).source.pathAtom

private theorem measure_le_of_disjoint_source_banded_atoms
    {failure : Set (ℕ → Site)}
    (atom : ℕ → Set (ℕ → Site)) (tail : ℝ≥0∞)
    (cover : failure ⊆ ⋃ n, atom n)
    (pairwise_disjoint : Pairwise fun n l ↦ Disjoint (atom n) (atom l))
    (measurable_atom : ∀ n, MeasurableSet (atom n))
    (local_bound : ∀ n, simpleRandomWalkLaw (failure ∩ atom n) ≤
      tail * simpleRandomWalkLaw (atom n)) :
    simpleRandomWalkLaw failure ≤ tail := by
  apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw
    failure (fun n ↦ failure ∩ atom n) atom tail
  · intro omega homega
    rcases Set.mem_iUnion.mp (cover homega) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, homega, hn⟩
  · exact local_bound
  · exact pairwise_disjoint
  · exact measurable_atom

theorem LeftWinnerSourceBandedGoodBandDecomposition.measure_le
    {cWindow m : ℕ} {C cBase alpha : ℝ} {target : Set (ℕ → Site)}
    (D : LeftWinnerSourceBandedGoodBandDecomposition
      cWindow m C alpha target)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hscales : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
      SourceIntervalScale m (sourceIntervalLower m (l.1 + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l.1 + 1)))
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw target ≤
      2 * (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m) := by
  let atomTail := tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
    sourceProp45FourBranchError m
  have heven : simpleRandomWalkLaw D.evenFailure ≤ atomTail := by
    apply measure_le_of_disjoint_source_banded_atoms
      (fun n ↦ (D.evenAtoms n).source.pathAtom) atomTail
      D.even_cover D.even_disjoint
    · intro n
      exact (D.evenAtoms n).source.measurableSet_pathAtom
    · intro n
      exact (D.evenAtoms n).local_bound G hC halpha hAlpha hscales
        hbaseAbsorb tail hshift
  have hodd : simpleRandomWalkLaw D.oddTerminalFailure ≤ atomTail := by
    apply measure_le_of_disjoint_source_banded_atoms
      (fun n ↦ (D.oddAtoms n).source.pathAtom) atomTail
      D.odd_cover D.odd_disjoint
    · intro n
      exact (D.oddAtoms n).source.measurableSet_pathAtom
    · intro n
      exact (D.oddAtoms n).local_bound G hC halpha hAlpha hscales
        hbaseAbsorb tail hshift
  calc
    simpleRandomWalkLaw target ≤
        simpleRandomWalkLaw (D.evenFailure ∪ D.oddTerminalFailure) :=
      measure_mono D.cover
    _ ≤ simpleRandomWalkLaw D.evenFailure +
        simpleRandomWalkLaw D.oddTerminalFailure := measure_union_le _ _
    _ ≤ atomTail + atomTail := add_le_add heven hodd
    _ = 2 * (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m) := by
      dsimp [atomTail]
      ring

theorem RightWinnerSourceBandedGoodBandDecomposition.measure_le
    {cWindow m : ℕ} {C cBase alpha : ℝ} {target : Set (ℕ → Site)}
    (D : RightWinnerSourceBandedGoodBandDecomposition
      cWindow m C alpha target)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hC : 0 < C) (halpha : kappaOne ≤ alpha)
    (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hscales : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
      SourceIntervalScale m (sourceIntervalLower m (l.1 + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l.1 + 1)))
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw target ≤
      2 * (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m) := by
  let atomTail := tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
    sourceProp45FourBranchError m
  have hodd : simpleRandomWalkLaw D.oddFailure ≤ atomTail := by
    apply measure_le_of_disjoint_source_banded_atoms
      (fun n ↦ (D.oddAtoms n).source.pathAtom) atomTail
      D.odd_cover D.odd_disjoint
    · intro n
      exact (D.oddAtoms n).source.measurableSet_pathAtom
    · intro n
      exact (D.oddAtoms n).local_bound G hC halpha hAlpha hscales
        hbaseAbsorb tail hshift
  have heven : simpleRandomWalkLaw D.evenTerminalFailure ≤ atomTail := by
    apply measure_le_of_disjoint_source_banded_atoms
      (fun n ↦ (D.evenAtoms n).source.pathAtom) atomTail
      D.even_cover D.even_disjoint
    · intro n
      exact (D.evenAtoms n).source.measurableSet_pathAtom
    · intro n
      exact (D.evenAtoms n).local_bound G hC halpha hAlpha hscales
        hbaseAbsorb tail hshift
  calc
    simpleRandomWalkLaw target ≤
        simpleRandomWalkLaw (D.oddFailure ∪ D.evenTerminalFailure) :=
      measure_mono D.cover
    _ ≤ simpleRandomWalkLaw D.oddFailure +
        simpleRandomWalkLaw D.evenTerminalFailure := measure_union_le _ _
    _ ≤ atomTail + atomTail := add_le_add hodd heven
    _ = 2 * (tail + (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m) := by
      dsimp [atomTail]
      ring

end Erdos1166.HLOZProp47Lemma411412SourceAtoms
