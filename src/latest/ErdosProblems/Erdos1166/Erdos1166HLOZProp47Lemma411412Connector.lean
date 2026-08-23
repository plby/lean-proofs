import ErdosProblems.Erdos1166.Erdos1166HLOZEquation447
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Canonical
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47SourceAssembly
import ErdosProblems.Erdos1166.Erdos1166HLOZSourceInstantiation

/-!
The source-facing closure of the Lemmas 4.11--4.12 exceptional estimate
used by Proposition 4.7.

The checked analytic lemmas already prove the fixed-profile estimate.  The
genuinely planar input is the disintegration at the stopped time: on every
external-path atom, the vector of lazy local times must have the truncated
negative-binomial product law, and the planar cardinality event must map to
the first source band.  The prescribed next direction in (4.47) is retained
as an independent `Direction` coordinate, rather than encoded as an event of
the lazy vector.  `StoppedEquation447Atom` records this joint law and the
conditional categorical product statement; it does not assume a probability
bound for the planar event.
-/

namespace Erdos1166.HLOZProp47Lemma411412Connector

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

open HLOZPairing.ScreeningBridge
open HLOZProp47Parameters HLOZProp47SourceObjects
open HLOZProp47SourceAssembly HLOZProp48SourceBands HLOZProp48Truncated
open HLOZProp47Canonical
open HLOZEquation447
open HLOZLemma412Windows

/-- The source event to which the stopped-profile argument is applied.  The
avoidance and distance-bin factors in `lemma411412FailureEvent` only make that
event smaller, so they do not belong in the profile-law input. -/
def lemma411412CardinalityFailureEvent
    (m : ℕ) (i : Fin 6) (r : StageIndex) : Set (ℕ → Site) :=
  prefixPairingEvent m i (stageNumber r + 1) ∩
    {s | Real.log m ^ 2 <
      ((nearFavoriteSites i s m (stageNumber r) kappaOne).card : ℝ)}

theorem lemma411412FailureEvent_subset_cardinalityFailureEvent
    (m : ℕ) (i : Fin 6) (r : StageIndex) (alpha : ℝ) :
    lemma411412FailureEvent m i r alpha ⊆
      lemma411412CardinalityFailureEvent m i r := by
  rintro s ⟨⟨⟨hprefix, _havoid⟩, _hbin⟩, hcard⟩
  exact ⟨hprefix, hcard⟩

/-- The profile-Theta part of a Lemmas 4.11--4.12 failure is exactly one of
the Proposition 4.5 exceptions.  Off that event only the stopped-profile
cardinality estimate remains. -/
theorem lemma411412FailureEvent_subset_prop45_union_cardinalityDiff
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (r : StageIndex) (alpha : ℝ) :
    lemma411412FailureEvent m i r alpha ⊆
      prop45FailureEvent profiles cStar m i r alpha ∪
        (lemma411412CardinalityFailureEvent m i r \
          stoppedThetaEvent (profiles i) (cStar i) m (stageNumber r)) := by
  rintro s ⟨⟨⟨hprefix, havoid⟩, hbin⟩, hcard⟩
  by_cases htheta :
      s ∈ stoppedThetaEvent (profiles i) (cStar i) m (stageNumber r)
  · exact Or.inl ⟨⟨⟨hprefix, havoid⟩, hbin⟩, htheta⟩
  · exact Or.inr ⟨⟨hprefix, hcard⟩, htheta⟩

/-- The history-level profile exception used by a stopped atom need not be
the canonical `Theta` event used in the final Proposition-4.5 split.  This
event retains the three deterministic factors of a Lemmas 4.11--4.12
failure and replaces only its profile exception. -/
def lemma411412AuxThetaEvent
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set (ℕ → Site))
    (m : ℕ) (i : Fin 6) (r : StageIndex) (alpha : ℝ) :
    Set (ℕ → Site) :=
  prefixPairingEvent m i (stageNumber r + 1) ∩
    hlozDirectAvoidanceEvent m (stageNumber r + 1) ∩
    distanceBinEvent m (stageNumber r) alpha ∩ thetaTarget m i r

/-- If the canonical and stopped-atom profile exceptions differ, a failure
is covered by the canonical Proposition-4.5 event, the auxiliary profile
event, or the cardinality event with the auxiliary exception removed. -/
theorem lemma411412FailureEvent_subset_prop45_union_auxTheta_union_cardinalityDiff
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set (ℕ → Site))
    (m : ℕ) (i : Fin 6) (r : StageIndex) (alpha : ℝ) :
    lemma411412FailureEvent m i r alpha ⊆
      prop45FailureEvent profiles cStar m i r alpha ∪
        (lemma411412AuxThetaEvent thetaTarget m i r alpha ∪
          (lemma411412CardinalityFailureEvent m i r \
            thetaTarget m i r)) := by
  rintro s ⟨⟨⟨hprefix, havoid⟩, hbin⟩, hcard⟩
  by_cases htheta :
      s ∈ stoppedThetaEvent (profiles i) (cStar i) m (stageNumber r)
  · exact Or.inl ⟨⟨⟨hprefix, havoid⟩, hbin⟩, htheta⟩
  · by_cases haux : s ∈ thetaTarget m i r
    · exact Or.inr (Or.inl ⟨⟨⟨hprefix, havoid⟩, hbin⟩, haux⟩)
    · exact Or.inr (Or.inr ⟨⟨hprefix, hcard⟩, haux⟩)

/-- The real open window in `nearFavoriteSites` is contained in the first
integer source band.  This is the ceiling arithmetic needed before the
stopped local-time vector can be identified with `sourceProfileQEvent`. -/
theorem nearFavoriteWindow_subset_sourceFirstInterval
    (m j : ℕ)
    (hlower : (m : ℝ) - (m : ℝ) ^ kappaOne < j)
    (hupper : (j : ℝ) < m) : InSourceInterval m 1 j := by
  constructor
  · unfold sourceIntervalLower
    simp only [one_mul]
    by_cases hw : sourceCellWidth m ≤ m
    · have hreal : ((m - sourceCellWidth m : ℕ) : ℝ) ≤ j := by
        rw [Nat.cast_sub hw]
        have hceil : (m : ℝ) ^ kappaOne ≤ sourceCellWidth m := by
          exact Nat.le_ceil ((m : ℝ) ^ kappaOne)
        linarith
      exact_mod_cast hreal
    · simp [Nat.sub_eq_zero_of_le (le_of_not_ge hw)]
  · have hupperNat : j < m := by exact_mod_cast hupper
    simpa [sourceIntervalUpper] using hupperNat

theorem nearFavoriteSites_localTime_mem_sourceFirstInterval
    {i : Fin 6} {s : ℕ → Site} {m k : ℕ} {x : Site}
    (hx : x ∈ nearFavoriteSites i s m k kappaOne) :
    InSourceInterval m 1 (localTime s (directCreationTime m k s) x) := by
  unfold nearFavoriteSites at hx
  rw [Finset.mem_filter] at hx
  exact nearFavoriteWindow_subset_sourceFirstInterval m
    (localTime s (directCreationTime m k s) x) hx.2.2.2.1 hx.2.2.2.2

/-- One external-path atom in the stopped-time disintegration needed for
(4.47).  Its finite coordinate type is carried by the atom and may depend on
it; this lets concrete stopped-law constructors use the native active-base
subtype without an artificial reindexing through `Fin`.

`map_law` is a law on `lazy-vector × next-direction`, so the factor `1/4`
follows from the literal uniform direction law.  The source constructors in
`Erdos1166HLOZProp47Lemma411412SourceAtoms` derive this field for the
unprimed-left and primed-strict-right branches.  Their remaining inputs are
the exact event identification and source-visible categorical hypotheses. -/
structure StoppedEquation447Atom
    (cWindow m : ℕ) (C cTheta a : ℝ)
    (failure : Set (ℕ → Site)) where
  Coord : Type
  [coordFintype : Fintype Coord]
  pathAtom : Set (ℕ → Site)
  measurableSet_pathAtom : MeasurableSet pathAtom
  profile : Coord → ℕ
  profile_lt : ∀ x, profile x < m
  lazyVector : (ℕ → Site) → (Coord → ℕ)
  measurable_lazyVector : Measurable lazyVector
  nextDirection : (ℕ → Site) → Direction
  measurable_nextDirection : Measurable nextDirection
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  badAtom : ℕ → (Coord → ℕ) →
    Set ((Coord → ℕ) × Direction)
  historyAtom : ℕ → (Coord → ℕ) →
    Set ((Coord → ℕ) × Direction)
  category : ∀ q, (Coord → ℕ) →
    ((Coord → ℕ) × Direction) → Fin q → Fin 3
  categoryLaw : ∀ q, (Coord → ℕ) → Fin q → Measure (Fin 3)
  categoryLaw_probability : ∀ q eta x,
    IsProbabilityMeasure (categoryLaw q eta x)
  map_law :
    (simpleRandomWalkLaw.restrict pathAtom).map
        (fun s ↦ (lazyVector s, nextDirection s)) =
      simpleRandomWalkLaw pathAtom •
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2) ∩ D) ×ˢ
        (Set.univ : Set Direction))
  theta_bound :
    ((sourceTruncatedProfileMeasure m profile).prod directionLaw).real
        (sourceProfileThetaBad cWindow m 1 profile ×ˢ
          (Set.univ : Set Direction)) ≤
      Real.exp (-cTheta * (m : ℝ) ^ a)
  equation447_cover : ∀ q,
    (sourceEquation447ByCount cWindow m profile D Set.univ q ×ˢ
      {forcedDirection}) ⊆
      ⋃ eta, badAtom q eta
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
      C * (categoryLaw q eta x).real {1}
  history_disjoint : ∀ q, Pairwise fun eta zeta ↦
    Disjoint (historyAtom q eta) (historyAtom q zeta)
  history_measurable : ∀ q eta, MeasurableSet (historyAtom q eta)

/-- A source-faithful branch atom.  Unlike `StoppedEquation447Atom`, its
profile-cardinality threshold is explicit and its `failure` is the failure
event of one parity/winner branch, not the full planar cardinality event. -/
structure StoppedEquation447BranchAtom
    (cWindow m : ℕ) (C : ℝ)
    (failure : Set (ℕ → Site)) (rho : ℝ) where
  Coord : Type
  [coordFintype : Fintype Coord]
  pathAtom : Set (ℕ → Site)
  measurableSet_pathAtom : MeasurableSet pathAtom
  profile : Coord → ℕ
  profile_lt : ∀ x, profile x < m
  lazyVector : (ℕ → Site) → (Coord → ℕ)
  measurable_lazyVector : Measurable lazyVector
  nextDirection : (ℕ → Site) → Direction
  measurable_nextDirection : Measurable nextDirection
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  badAtom : ℕ → (Coord → ℕ) →
    Set ((Coord → ℕ) × Direction)
  historyAtom : ℕ → (Coord → ℕ) →
    Set ((Coord → ℕ) × Direction)
  category : ∀ q, (Coord → ℕ) →
    ((Coord → ℕ) × Direction) → Fin q → Fin 3
  categoryLaw : ∀ q, (Coord → ℕ) → Fin q → Measure (Fin 3)
  categoryLaw_probability : ∀ q eta x,
    IsProbabilityMeasure (categoryLaw q eta x)
  map_law :
    (simpleRandomWalkLaw.restrict pathAtom).map
        (fun s ↦ (lazyVector s, nextDirection s)) =
      simpleRandomWalkLaw pathAtom •
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
  failure_subset :
    failure ∩ pathAtom ⊆ (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
      ((sourceProfileQEvent m 1 profile rho ∩ D) ×ˢ
        (Set.univ : Set Direction))
  /-- The path-space external-profile exception corresponding to
  `sourceProfileThetaBad`.  It is kept outside the conditional product
  estimate and is paid globally by Proposition 4.5. -/
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
      C * (categoryLaw q eta x).real {1}
  history_disjoint : ∀ q, Pairwise fun eta zeta ↦
    Disjoint (historyAtom q eta) (historyAtom q zeta)
  history_measurable : ∀ q eta, MeasurableSet (historyAtom q eta)

/-- The path-space switch form of the exceptional base step (4.47).

The ordinary `StoppedEquation447BranchAtom` above is useful for the later
adjacent-band recursion, where the two configurations live in one stopped
product atom.  At the base step the paper keeps the deleted nearest-neighbor
path fixed but changes lazy holding coordinates from `I₁` to the artificial
band `I₀`.  This can change the underlying full-walk prefix and its stopping
horizon, so the bad and witness events are compared in global walk path
space; (4.54) proves that the witness events are disjoint.  This record
exposes exactly that mechanism.  In particular it contains neither a
same-below-`m`-profile categorical product identity nor the final branch
probability bound. -/
structure StoppedEquation447PathWitnessBranchAtom
    (cWindow m : ℕ) (c : ℝ)
    (failure : Set (ℕ → Site)) (rho : ℝ) where
  Coord : Type
  [coordFintype : Fintype Coord]
  Path : Type
  [pathCountable : Countable Path]
  pathAtom : Set (ℕ → Site)
  measurableSet_pathAtom : MeasurableSet pathAtom
  profile : Coord → ℕ
  profile_lt : ∀ x, profile x < m
  lazyVector : (ℕ → Site) → (Coord → ℕ)
  measurable_lazyVector : Measurable lazyVector
  nextDirection : (ℕ → Site) → Direction
  measurable_nextDirection : Measurable nextDirection
  forcedDirection : Direction
  D : Set (Coord → ℕ)
  badAtom : ℕ → Path → Set ((Coord → ℕ) × Direction)
  witnessAtom : ℕ → Path → Set ((Coord → ℕ) × Direction)
  map_law :
    (simpleRandomWalkLaw.restrict pathAtom).map
        (fun s ↦ (lazyVector s, nextDirection s)) =
      simpleRandomWalkLaw pathAtom •
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
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
  /-- The checked local path switch (4.51)--(4.53).  Its exponential factor
  is per fixed cardinality; the geometric sum over cardinalities is proved
  by `sourceEquation447_good_real_le`. -/
  path_switch : ∀ q eta, Nat.ceil rho ≤ q →
    ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
        (badAtom q eta) ≤
      ENNReal.ofReal (Real.exp (-c * (q : ℝ))) *
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
          (witnessAtom q eta)
  witness_disjoint : ∀ q, Pairwise fun eta zeta ↦
    Disjoint (witnessAtom q eta) (witnessAtom q zeta)
  witness_measurable : ∀ q eta, MeasurableSet (witnessAtom q eta)

/-- The literal full-walk-path form of the exceptional base step (4.47).

Unlike `StoppedEquation447PathWitnessBranchAtom`, the bad and witness atoms
here live in the original random-walk path space.  The source's artificial
`I₀` construction keeps the deleted nearest-neighbor path fixed, while
changing an `I₁` holding block changes the full walk prefix and, in general,
its stopping horizon.  Thus the witness need not remain in the same
below-`m` stopped-profile atom.  The factor `1/4` is the prescribed first
step in the source proof; the remaining fields are exactly the count
decomposition, the fixed-deleted-path holding-coordinate switch, and the
global full-path disjointness from (4.51)--(4.54). -/
structure StoppedEquation447ChangedPathBranch
    (c : ℝ) (failure thetaPathEvent : Set (ℕ → Site)) (rho : ℝ) where
  Code : Type
  [codeCountable : Countable Code]
  forcedGoodEvent : Set (ℕ → Site)
  badByCount : ℕ → Set (ℕ → Site)
  badPathAtom : ℕ → Code → Set (ℕ → Site)
  witnessPathAtom : ℕ → Code → Set (ℕ → Site)
  forced_reduction :
    simpleRandomWalkLaw.real (failure \ thetaPathEvent) ≤
      4 * simpleRandomWalkLaw.real forcedGoodEvent
  forced_count_cover :
    forcedGoodEvent ⊆ ⋃ k : ℕ, badByCount (Nat.ceil rho + k)
  count_path_cover : ∀ q, badByCount q ⊆ ⋃ eta, badPathAtom q eta
  path_switch : ∀ q eta, Nat.ceil rho ≤ q →
    simpleRandomWalkLaw (badPathAtom q eta) ≤
      ENNReal.ofReal (Real.exp (-c * (q : ℝ))) *
        simpleRandomWalkLaw (witnessPathAtom q eta)
  witness_disjoint : ∀ q, Pairwise fun eta zeta ↦
    Disjoint (witnessPathAtom q eta) (witnessPathAtom q zeta)
  witness_measurable : ∀ q eta, MeasurableSet (witnessPathAtom q eta)

/-- The remaining stopped planar input, uniformly in the six pairings and
three creation stages.  The atoms form a measurable disjoint partition of
the concrete planar cardinality-failure event. -/
def Prop47Lemma411412StoppedProfileInputs
    (cWindow : ℕ) (C cTheta a : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    ∃ atoms : ℕ → StoppedEquation447Atom cWindow m C cTheta a
        (lemma411412CardinalityFailureEvent m i r),
      lemma411412CardinalityFailureEvent m i r ⊆
          ⋃ eta, (atoms eta).pathAtom ∧
        Pairwise fun eta zeta ↦
          Disjoint (atoms eta).pathAtom (atoms zeta).pathAtom

private theorem eventually_conditionalEquation447_error_absorb
    {C cTheta a : ℝ} (hC : 0 < C) (hcTheta : 0 < cTheta) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop,
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d * (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K +
          Real.exp (-cTheta * (m : ℝ) ^ a)) ≤
        Real.exp (-(d / 2) * Real.log (m : ℝ) ^ 2) := by
  let d := Real.log ((C + 1) / C)
  let K := (1 - Real.exp (-d))⁻¹
  have hratio : 1 < (C + 1) / C := by
    rw [one_lt_div hC]
    linarith
  have hd : 0 < d := Real.log_pos hratio
  have hstretch := HLOZLemma411.eventually_const_mul_log_sq_le_rpow
    hd hcTheta ha
  have habsorb := HLOZLemma411.eventually_three_rpow_mul_exp_neg_log_sq_le
    hd (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (4 * (K + 1) / 3)
  filter_upwards [hstretch, habsorb, eventually_ge_atTop N] with
      m hstretchM habsorbM hm
  have hK0 : 0 ≤ K := by
    dsimp [K]
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hcoeff : 4 * (K + 1) ≤ 3 * (m : ℝ) := by
    have hNm : (N : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hrho0 : 0 ≤ Real.log (m : ℝ) ^ 2 := sq_nonneg _
  have hceil : Real.log (m : ℝ) ^ 2 ≤
      (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ) :=
    Nat.le_ceil _
  have hfirst :
      Real.exp (-d * (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) ≤
        Real.exp (-d * Real.log (m : ℝ) ^ 2) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have htheta : Real.exp (-cTheta * (m : ℝ) ^ a) ≤
      Real.exp (-d * Real.log (m : ℝ) ^ 2) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp0 : 0 ≤ Real.exp (-d * Real.log (m : ℝ) ^ 2) :=
    (Real.exp_pos _).le
  dsimp only [d, K]
  calc
    4 * (Real.exp
          (-Real.log ((C + 1) / C) *
            (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) *
          (1 - Real.exp (-Real.log ((C + 1) / C)))⁻¹ +
        Real.exp (-cTheta * (m : ℝ) ^ a)) ≤
        4 * (K + 1) * Real.exp (-d * Real.log (m : ℝ) ^ 2) := by
      dsimp [d, K] at hfirst htheta hK0 ⊢
      nlinarith
    _ ≤ 3 * (m : ℝ) * Real.exp (-d * Real.log (m : ℝ) ^ 2) := by
      gcongr
    _ = 3 * (m : ℝ) ^ (1 : ℝ) *
        Real.exp (-d * Real.log (m : ℝ) ^ 2) := by rw [Real.rpow_one]
    _ ≤ Real.exp (-(d / 2) * Real.log (m : ℝ) ^ 2) := habsorbM

private theorem stoppedEquation447Atom_local_bound
    {cWindow m : ℕ} {C cTheta a : ℝ}
    {failure : Set (ℕ → Site)}
    (A : StoppedEquation447Atom cWindow m C cTheta a failure)
    (hC : 0 < C)
    (habsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d * (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K +
          Real.exp (-cTheta * (m : ℝ) ^ a)) ≤
        Real.exp (-(d / 2) * Real.log (m : ℝ) ^ 2)) :
    simpleRandomWalkLaw (failure ∩ A.pathAtom) ≤
      ENNReal.ofReal (Real.exp (-(Real.log ((C + 1) / C) / 2) *
        Real.log (m : ℝ) ^ 2)) *
        simpleRandomWalkLaw A.pathAtom := by
  letI : Fintype A.Coord := A.coordFintype
  let lazyNu : Measure (A.Coord → ℕ) :=
    sourceTruncatedProfileMeasure m A.profile
  letI (x : A.Coord) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (A.profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (A.profile x) (A.profile_lt x))
  letI : IsProbabilityMeasure lazyNu := by
    dsimp [lazyNu]
    unfold sourceTruncatedProfileMeasure
    infer_instance
  let nu : Measure ((A.Coord → ℕ) × Direction) :=
    lazyNu.prod directionLaw
  letI : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  letI (q : ℕ) (eta : A.Coord → ℕ) (x : Fin q) :
      IsProbabilityMeasure (A.categoryLaw q eta x) :=
    A.categoryLaw_probability q eta x
  let d := Real.log ((C + 1) / C)
  let K := (1 - Real.exp (-d))⁻¹
  let rho := Real.log (m : ℝ) ^ 2
  let lazyQ : Set (A.Coord → ℕ) :=
    sourceProfileQEvent m 1 A.profile rho ∩ A.D
  let fullEvent : Set ((A.Coord → ℕ) × Direction) :=
    lazyQ ×ˢ (Set.univ : Set Direction)
  let forcedEvent : Set ((A.Coord → ℕ) × Direction) :=
    (Set.univ : Set (A.Coord → ℕ)) ×ˢ {A.forcedDirection}
  let thetaEvent : Set ((A.Coord → ℕ) × Direction) :=
    sourceProfileThetaBad cWindow m 1 A.profile ×ˢ
      (Set.univ : Set Direction)
  let goodEvent : Set ((A.Coord → ℕ) × Direction) :=
    sourceEquation447Event cWindow m A.profile rho A.D Set.univ ×ˢ
      {A.forcedDirection}
  let byCount (q : ℕ) : Set ((A.Coord → ℕ) × Direction) :=
    sourceEquation447ByCount cWindow m A.profile A.D Set.univ q ×ˢ
      {A.forcedDirection}
  have hcoverCount : goodEvent ⊆
      ⋃ k : ℕ, byCount (Nat.ceil rho + k) := by
    rintro ⟨lazy, direction⟩ ⟨hlazy, hdirection⟩
    rcases Set.mem_iUnion.mp
        (sourceEquation447Event_subset_iUnion_byCount cWindow m A.profile
          rho A.D Set.univ hlazy) with ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk, hdirection⟩
  have hgood :
      nu.real goodEvent ≤
        Real.exp (-d * (Nat.ceil rho : ℝ)) * K := by
    exact equation447_real_of_conditional_categorical_product nu
      goodEvent byCount
      A.badAtom A.historyAtom A.category A.categoryLaw
      rho C hC hcoverCount
      A.equation447_cover A.bad_subset_history_allUpper
      A.conditional_category_product A.category_mass_ratio
      A.history_disjoint A.history_measurable
  have hgoodEvent : fullEvent ∩ forcedEvent ∩ thetaEventᶜ = goodEvent := by
    ext z
    simp only [fullEvent, forcedEvent, thetaEvent, goodEvent, lazyQ,
      sourceEquation447Event, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_univ, and_true, Set.mem_compl_iff]
    tauto
  have hforced :
      nu.real (fullEvent ∩ forcedEvent) =
        (1 / 4 : ℝ) * nu.real fullEvent := by
    have hinter : fullEvent ∩ forcedEvent =
        lazyQ ×ˢ {A.forcedDirection} := by
      ext z
      simp [fullEvent, forcedEvent]
    have hdir : directionLaw.real {A.forcedDirection} = (1 / 4 : ℝ) := by
      rw [measureReal_def]
      simp [directionLaw]
    rw [hinter]
    dsimp [nu, fullEvent]
    rw [measureReal_prod_prod, measureReal_prod_prod, hdir]
    simp
    ring
  have hgood' :
      nu.real (fullEvent ∩ forcedEvent ∩ thetaEventᶜ) ≤
        Real.exp (-d * (Nat.ceil rho : ℝ)) * K := by
    rw [hgoodEvent]
    exact hgood
  have hprofileReal :
      nu.real fullEvent ≤
        Real.exp (-(d / 2) * Real.log (m : ℝ) ^ 2) := by
    apply (equation447_of_forced_step_and_theta nu
      fullEvent forcedEvent thetaEvent hforced hgood' A.theta_bound).trans
    exact habsorb
  have hprofile :
      nu fullEvent ≤
        ENNReal.ofReal
          (Real.exp (-(d / 2) * Real.log (m : ℝ) ^ 2)) := by
    rw [← ofReal_measureReal (measure_ne_top nu _)]
    exact ENNReal.ofReal_le_ofReal hprofileReal
  have hsubset : failure ∩ A.pathAtom ⊆
      A.pathAtom ∩ (fun s ↦ (A.lazyVector s, A.nextDirection s)) ⁻¹'
        fullEvent := by
    intro s hs
    exact ⟨hs.2, A.failure_subset hs⟩
  calc
    simpleRandomWalkLaw (failure ∩ A.pathAtom) ≤
        simpleRandomWalkLaw
          (A.pathAtom ∩ (fun s ↦ (A.lazyVector s, A.nextDirection s)) ⁻¹'
            fullEvent) :=
      measure_mono hsubset
    _ = (simpleRandomWalkLaw.restrict A.pathAtom)
        ((fun s ↦ (A.lazyVector s, A.nextDirection s)) ⁻¹' fullEvent) := by
      rw [Measure.restrict_apply' A.measurableSet_pathAtom, inter_comm]
    _ = ((simpleRandomWalkLaw.restrict A.pathAtom).map
          (fun s ↦ (A.lazyVector s, A.nextDirection s))) fullEvent := by
      rw [Measure.map_apply
        (A.measurable_lazyVector.prodMk A.measurable_nextDirection)
        MeasurableSet.of_discrete]
    _ = simpleRandomWalkLaw A.pathAtom * nu fullEvent := by
      rw [A.map_law, Measure.smul_apply]
      rfl
    _ ≤ simpleRandomWalkLaw A.pathAtom *
        ENNReal.ofReal (Real.exp (-(d / 2) * Real.log (m : ℝ) ^ 2)) := by
      gcongr
    _ = ENNReal.ofReal (Real.exp (-(Real.log ((C + 1) / C) / 2) *
          Real.log (m : ℝ) ^ 2)) *
        simpleRandomWalkLaw A.pathAtom := mul_comm _ _

/-- The fixed-profile content of equation (4.47) after the external-profile
exception has been removed.  This formulation is shared by the Lemma 4.10
Proposition-4.8 recursion: it bounds the first band directly under the
truncated product law, before transporting anything back to path space. -/
theorem stoppedEquation447BranchAtom_profile_good_base_bound_of_absorb
    {cWindow m : ℕ} {C rho target : ℝ}
    {failure : Set (ℕ → Site)}
    (A : StoppedEquation447BranchAtom cWindow m C failure rho)
    (hC : 0 < C)
    (habsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d * (Nat.ceil rho : ℝ)) * K) ≤
        Real.exp (-target)) :
    let _ : Fintype A.Coord := A.coordFintype
    (sourceTruncatedProfileMeasure m A.profile).real
        ((sourceProfileQEvent m 1 A.profile rho ∩ A.D) \
          sourceProfileThetaBad cWindow m 1 A.profile) ≤
      Real.exp (-target) := by
  letI : Fintype A.Coord := A.coordFintype
  let lazyNu : Measure (A.Coord → ℕ) :=
    sourceTruncatedProfileMeasure m A.profile
  letI (x : A.Coord) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (A.profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (A.profile x) (A.profile_lt x))
  letI : IsProbabilityMeasure lazyNu := by
    dsimp [lazyNu]
    unfold sourceTruncatedProfileMeasure
    infer_instance
  let nu : Measure ((A.Coord → ℕ) × Direction) :=
    lazyNu.prod directionLaw
  letI : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  letI (q : ℕ) (eta : A.Coord → ℕ) (x : Fin q) :
      IsProbabilityMeasure (A.categoryLaw q eta x) :=
    A.categoryLaw_probability q eta x
  let d := Real.log ((C + 1) / C)
  let K := (1 - Real.exp (-d))⁻¹
  let lazyQ : Set (A.Coord → ℕ) :=
    sourceProfileQEvent m 1 A.profile rho ∩ A.D
  let fullEvent : Set ((A.Coord → ℕ) × Direction) :=
    lazyQ ×ˢ (Set.univ : Set Direction)
  let forcedEvent : Set ((A.Coord → ℕ) × Direction) :=
    (Set.univ : Set (A.Coord → ℕ)) ×ˢ {A.forcedDirection}
  let thetaEvent : Set ((A.Coord → ℕ) × Direction) :=
    sourceProfileThetaBad cWindow m 1 A.profile ×ˢ
      (Set.univ : Set Direction)
  let goodEvent : Set ((A.Coord → ℕ) × Direction) :=
    sourceEquation447Event cWindow m A.profile rho A.D Set.univ ×ˢ
      {A.forcedDirection}
  let byCount (q : ℕ) : Set ((A.Coord → ℕ) × Direction) :=
    sourceEquation447ByCount cWindow m A.profile A.D Set.univ q ×ˢ
      {A.forcedDirection}
  have hcoverCount : goodEvent ⊆
      ⋃ k : ℕ, byCount (Nat.ceil rho + k) := by
    rintro ⟨lazy, direction⟩ ⟨hlazy, hdirection⟩
    rcases Set.mem_iUnion.mp
        (sourceEquation447Event_subset_iUnion_byCount cWindow m A.profile
          rho A.D Set.univ hlazy) with ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk, hdirection⟩
  have hgood :
      nu.real goodEvent ≤
        Real.exp (-d * (Nat.ceil rho : ℝ)) * K := by
    exact equation447_real_of_conditional_categorical_product nu
      goodEvent byCount A.badAtom A.historyAtom A.category A.categoryLaw
      rho C hC hcoverCount A.equation447_cover
      A.bad_subset_history_allUpper A.conditional_category_product
      A.category_mass_ratio A.history_disjoint A.history_measurable
  have hgoodEvent : fullEvent ∩ thetaEventᶜ ∩ forcedEvent = goodEvent := by
    ext z
    simp only [fullEvent, forcedEvent, thetaEvent, goodEvent, lazyQ,
      sourceEquation447Event, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_univ, and_true, Set.mem_compl_iff]
    tauto
  have hforced :
      nu.real (fullEvent ∩ thetaEventᶜ ∩ forcedEvent) =
        (1 / 4 : ℝ) * nu.real (fullEvent ∩ thetaEventᶜ) := by
    have hfull : fullEvent ∩ thetaEventᶜ =
        (lazyQ ∩ (sourceProfileThetaBad cWindow m 1 A.profile)ᶜ) ×ˢ
          (Set.univ : Set Direction) := by
      ext z
      simp [fullEvent, thetaEvent]
    have hinter : fullEvent ∩ thetaEventᶜ ∩ forcedEvent =
        (lazyQ ∩ (sourceProfileThetaBad cWindow m 1 A.profile)ᶜ) ×ˢ
          {A.forcedDirection} := by
      ext z
      simp [fullEvent, forcedEvent, thetaEvent]
    have hdir : directionLaw.real {A.forcedDirection} = (1 / 4 : ℝ) := by
      rw [measureReal_def]
      simp [directionLaw]
    rw [hinter, hfull]
    dsimp [nu]
    rw [measureReal_prod_prod, measureReal_prod_prod, hdir]
    simp
    ring
  have hprofileProduct :
      nu.real (fullEvent ∩ thetaEventᶜ) ≤ Real.exp (-target) := by
    have hscale :
        nu.real (fullEvent ∩ thetaEventᶜ) =
          4 * nu.real (fullEvent ∩ thetaEventᶜ ∩ forcedEvent) := by
      linarith
    calc
      nu.real (fullEvent ∩ thetaEventᶜ) =
          4 * nu.real (fullEvent ∩ thetaEventᶜ ∩ forcedEvent) := hscale
      _ ≤ 4 * (Real.exp (-d * (Nat.ceil rho : ℝ)) * K) := by
        gcongr
        rw [hgoodEvent]
        exact hgood
      _ ≤ Real.exp (-target) := habsorb
  have hfull : fullEvent ∩ thetaEventᶜ =
      (lazyQ \ sourceProfileThetaBad cWindow m 1 A.profile) ×ˢ
        (Set.univ : Set Direction) := by
    ext z
    simp [fullEvent, thetaEvent]
  have heq :
      lazyNu.real
          (lazyQ \ sourceProfileThetaBad cWindow m 1 A.profile) =
        nu.real (fullEvent ∩ thetaEventᶜ) := by
    rw [hfull]
    dsimp [nu]
    rw [measureReal_prod_prod, probReal_univ]
    simp
  change lazyNu.real
      (lazyQ \ sourceProfileThetaBad cWindow m 1 A.profile) ≤ _
  rw [heq]
  exact hprofileProduct

/-- Equation (4.47) on one branch, with an arbitrary common exponential
target.  This form is what finite branch aggregation needs: different winner
branches may have different source thresholds, while the eventual absorption
argument supplies one rate valid for all of them. -/
theorem stoppedEquation447BranchAtom_local_bound_of_absorb
    {cWindow m : ℕ} {C rho target : ℝ}
    {failure : Set (ℕ → Site)}
    (A : StoppedEquation447BranchAtom
      cWindow m C failure rho)
    (hC : 0 < C)
    (habsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d * (Nat.ceil rho : ℝ)) * K) ≤
        Real.exp (-target)) :
    simpleRandomWalkLaw ((failure \ A.thetaPathEvent) ∩ A.pathAtom) ≤
      ENNReal.ofReal (Real.exp (-target)) *
        simpleRandomWalkLaw A.pathAtom := by
  letI : Fintype A.Coord := A.coordFintype
  let lazyNu : Measure (A.Coord → ℕ) :=
    sourceTruncatedProfileMeasure m A.profile
  letI (x : A.Coord) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (A.profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (A.profile x) (A.profile_lt x))
  letI : IsProbabilityMeasure lazyNu := by
    dsimp [lazyNu]
    unfold sourceTruncatedProfileMeasure
    infer_instance
  let nu : Measure ((A.Coord → ℕ) × Direction) :=
    lazyNu.prod directionLaw
  letI : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  letI (q : ℕ) (eta : A.Coord → ℕ) (x : Fin q) :
      IsProbabilityMeasure (A.categoryLaw q eta x) :=
    A.categoryLaw_probability q eta x
  let d := Real.log ((C + 1) / C)
  let K := (1 - Real.exp (-d))⁻¹
  let lazyQ : Set (A.Coord → ℕ) :=
    sourceProfileQEvent m 1 A.profile rho ∩ A.D
  let fullEvent : Set ((A.Coord → ℕ) × Direction) :=
    lazyQ ×ˢ (Set.univ : Set Direction)
  let forcedEvent : Set ((A.Coord → ℕ) × Direction) :=
    (Set.univ : Set (A.Coord → ℕ)) ×ˢ {A.forcedDirection}
  let thetaEvent : Set ((A.Coord → ℕ) × Direction) :=
    sourceProfileThetaBad cWindow m 1 A.profile ×ˢ
      (Set.univ : Set Direction)
  let goodEvent : Set ((A.Coord → ℕ) × Direction) :=
    sourceEquation447Event cWindow m A.profile rho A.D Set.univ ×ˢ
      {A.forcedDirection}
  let byCount (q : ℕ) : Set ((A.Coord → ℕ) × Direction) :=
    sourceEquation447ByCount cWindow m A.profile A.D Set.univ q ×ˢ
      {A.forcedDirection}
  have hcoverCount : goodEvent ⊆
      ⋃ k : ℕ, byCount (Nat.ceil rho + k) := by
    rintro ⟨lazy, direction⟩ ⟨hlazy, hdirection⟩
    rcases Set.mem_iUnion.mp
        (sourceEquation447Event_subset_iUnion_byCount cWindow m A.profile
          rho A.D Set.univ hlazy) with ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk, hdirection⟩
  have hgood :
      nu.real goodEvent ≤
        Real.exp (-d * (Nat.ceil rho : ℝ)) * K := by
    exact equation447_real_of_conditional_categorical_product nu
      goodEvent byCount A.badAtom A.historyAtom A.category A.categoryLaw
      rho C hC hcoverCount A.equation447_cover
      A.bad_subset_history_allUpper A.conditional_category_product
      A.category_mass_ratio A.history_disjoint A.history_measurable
  have hgoodEvent : fullEvent ∩ thetaEventᶜ ∩ forcedEvent = goodEvent := by
    ext z
    simp only [fullEvent, forcedEvent, thetaEvent, goodEvent, lazyQ,
      sourceEquation447Event, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_univ, and_true, Set.mem_compl_iff]
    tauto
  have hforced :
      nu.real (fullEvent ∩ thetaEventᶜ ∩ forcedEvent) =
        (1 / 4 : ℝ) * nu.real (fullEvent ∩ thetaEventᶜ) := by
    have hfull : fullEvent ∩ thetaEventᶜ =
        (lazyQ ∩ (sourceProfileThetaBad cWindow m 1 A.profile)ᶜ) ×ˢ
          (Set.univ : Set Direction) := by
      ext z
      simp [fullEvent, thetaEvent]
    have hinter : fullEvent ∩ thetaEventᶜ ∩ forcedEvent =
        (lazyQ ∩ (sourceProfileThetaBad cWindow m 1 A.profile)ᶜ) ×ˢ
          {A.forcedDirection} := by
      ext z
      simp [fullEvent, forcedEvent, thetaEvent]
    have hdir : directionLaw.real {A.forcedDirection} = (1 / 4 : ℝ) := by
      rw [measureReal_def]
      simp [directionLaw]
    rw [hinter, hfull]
    dsimp [nu]
    rw [measureReal_prod_prod, measureReal_prod_prod, hdir]
    simp
    ring
  have hgood' :
      nu.real (fullEvent ∩ thetaEventᶜ ∩ forcedEvent) ≤
        Real.exp (-d * (Nat.ceil rho : ℝ)) * K := by
    rw [hgoodEvent]
    exact hgood
  have hprofileReal :
      nu.real (fullEvent ∩ thetaEventᶜ) ≤ Real.exp (-target) := by
    have hscale :
        nu.real (fullEvent ∩ thetaEventᶜ) =
          4 * nu.real (fullEvent ∩ thetaEventᶜ ∩ forcedEvent) := by
      linarith
    calc
      nu.real (fullEvent ∩ thetaEventᶜ) =
          4 * nu.real (fullEvent ∩ thetaEventᶜ ∩ forcedEvent) := hscale
      _ ≤ 4 * (Real.exp (-d * (Nat.ceil rho : ℝ)) * K) := by
        gcongr
      _ ≤ Real.exp (-target) := habsorb
  have hprofile :
      nu (fullEvent ∩ thetaEventᶜ) ≤
        ENNReal.ofReal (Real.exp (-target)) := by
    rw [← ofReal_measureReal (measure_ne_top nu _)]
    exact ENNReal.ofReal_le_ofReal hprofileReal
  have hsubset : (failure \ A.thetaPathEvent) ∩ A.pathAtom ⊆
      A.pathAtom ∩ (fun s ↦ (A.lazyVector s, A.nextDirection s)) ⁻¹'
        (fullEvent ∩ thetaEventᶜ) := by
    intro s hs
    refine ⟨hs.2, A.failure_subset ⟨hs.1.1, hs.2⟩, ?_⟩
    intro htheta
    exact hs.1.2 (A.theta_preimage_subset ⟨hs.2, htheta⟩)
  calc
    simpleRandomWalkLaw ((failure \ A.thetaPathEvent) ∩ A.pathAtom) ≤
        simpleRandomWalkLaw
          (A.pathAtom ∩ (fun s ↦ (A.lazyVector s, A.nextDirection s)) ⁻¹'
            (fullEvent ∩ thetaEventᶜ)) := measure_mono hsubset
    _ = (simpleRandomWalkLaw.restrict A.pathAtom)
        ((fun s ↦ (A.lazyVector s, A.nextDirection s)) ⁻¹'
          (fullEvent ∩ thetaEventᶜ)) := by
      rw [Measure.restrict_apply' A.measurableSet_pathAtom, inter_comm]
    _ = ((simpleRandomWalkLaw.restrict A.pathAtom).map
          (fun s ↦ (A.lazyVector s, A.nextDirection s)))
            (fullEvent ∩ thetaEventᶜ) := by
      rw [Measure.map_apply
        (A.measurable_lazyVector.prodMk A.measurable_nextDirection)
        MeasurableSet.of_discrete]
    _ = simpleRandomWalkLaw A.pathAtom *
        nu (fullEvent ∩ thetaEventᶜ) := by
      rw [A.map_law, Measure.smul_apply]
      rfl
    _ ≤ simpleRandomWalkLaw A.pathAtom *
        ENNReal.ofReal (Real.exp (-target)) := by
      gcongr
    _ = ENNReal.ofReal (Real.exp (-target)) *
        simpleRandomWalkLaw A.pathAtom := mul_comm _ _

/-- Equation (4.47) on one branch, stated at that branch's own profile
threshold. -/
theorem stoppedEquation447BranchAtom_local_bound
    {cWindow m : ℕ} {C rho : ℝ}
    {failure : Set (ℕ → Site)}
    (A : StoppedEquation447BranchAtom
      cWindow m C failure rho)
    (hC : 0 < C)
    (habsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d * (Nat.ceil rho : ℝ)) * K) ≤
        Real.exp (-(d / 2) * rho)) :
    simpleRandomWalkLaw ((failure \ A.thetaPathEvent) ∩ A.pathAtom) ≤
      ENNReal.ofReal (Real.exp
        (-(Real.log ((C + 1) / C) / 2) * rho)) *
        simpleRandomWalkLaw A.pathAtom := by
  have habsorb' :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d * (Nat.ceil rho : ℝ)) * K) ≤
        Real.exp (-(d / 2 * rho)) := by
    simpa only [neg_mul] using habsorb
  convert stoppedEquation447BranchAtom_local_bound_of_absorb
    (target := Real.log ((C + 1) / C) / 2 * rho) A hC habsorb' using 1 <;>
      ring

/-- The source path-switch proof of (4.47), transported back through one
stopped path atom.  The explicit inverse factor is the geometric sum over
the exact cardinality, and the factor `4` restores the prescribed fresh
direction.  No artificial lower bound on the source's positive exponential
rate is imposed. -/
theorem stoppedEquation447PathWitnessBranchAtom_local_bound
    {cWindow m : ℕ} {c rho : ℝ}
    {failure : Set (ℕ → Site)}
    (A : StoppedEquation447PathWitnessBranchAtom
      cWindow m c failure rho)
    (hc : 0 < c) :
    simpleRandomWalkLaw ((failure \ A.thetaPathEvent) ∩ A.pathAtom) ≤
      ENNReal.ofReal (4 * (Real.exp (-c * rho) *
        (1 - Real.exp (-c))⁻¹)) *
        simpleRandomWalkLaw A.pathAtom := by
  letI : Fintype A.Coord := A.coordFintype
  letI : Countable A.Path := A.pathCountable
  let lazyNu : Measure (A.Coord → ℕ) :=
    sourceTruncatedProfileMeasure m A.profile
  letI (x : A.Coord) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (A.profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (A.profile x) (A.profile_lt x))
  letI : IsProbabilityMeasure lazyNu := by
    dsimp [lazyNu]
    unfold sourceTruncatedProfileMeasure
    infer_instance
  let nu : Measure ((A.Coord → ℕ) × Direction) :=
    lazyNu.prod directionLaw
  letI : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  let lazyQ : Set (A.Coord → ℕ) :=
    sourceProfileQEvent m 1 A.profile rho ∩ A.D
  let fullEvent : Set ((A.Coord → ℕ) × Direction) :=
    lazyQ ×ˢ (Set.univ : Set Direction)
  let forcedEvent : Set ((A.Coord → ℕ) × Direction) :=
    (Set.univ : Set (A.Coord → ℕ)) ×ˢ {A.forcedDirection}
  let thetaEvent : Set ((A.Coord → ℕ) × Direction) :=
    sourceProfileThetaBad cWindow m 1 A.profile ×ˢ
      (Set.univ : Set Direction)
  let goodEvent : Set ((A.Coord → ℕ) × Direction) :=
    sourceEquation447Event cWindow m A.profile rho A.D Set.univ ×ˢ
      {A.forcedDirection}
  let byCount (q : ℕ) : Set ((A.Coord → ℕ) × Direction) :=
    sourceEquation447ByCount cWindow m A.profile A.D Set.univ q ×ˢ
      {A.forcedDirection}
  have hcoverCount : goodEvent ⊆
      ⋃ k : ℕ, byCount (Nat.ceil rho + k) := by
    rintro ⟨lazy, direction⟩ ⟨hlazy, hdirection⟩
    rcases Set.mem_iUnion.mp
        (sourceEquation447Event_subset_iUnion_byCount cWindow m A.profile
          rho A.D Set.univ hlazy) with ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk, hdirection⟩
  have hgood : nu.real goodEvent ≤
      Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹ := by
    exact equation447_real_of_fixed_cardinality_pos nu goodEvent byCount
      A.badAtom A.witnessAtom rho c hc hcoverCount A.equation447_cover
      A.path_switch A.witness_disjoint A.witness_measurable
  have hgoodEvent : fullEvent ∩ thetaEventᶜ ∩ forcedEvent = goodEvent := by
    ext z
    simp only [fullEvent, forcedEvent, thetaEvent, goodEvent, lazyQ,
      sourceEquation447Event, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_univ, and_true, Set.mem_compl_iff]
    tauto
  have hforced :
      nu.real (fullEvent ∩ thetaEventᶜ ∩ forcedEvent) =
        (1 / 4 : ℝ) * nu.real (fullEvent ∩ thetaEventᶜ) := by
    have hfull : fullEvent ∩ thetaEventᶜ =
        (lazyQ ∩ (sourceProfileThetaBad cWindow m 1 A.profile)ᶜ) ×ˢ
          (Set.univ : Set Direction) := by
      ext z
      simp [fullEvent, thetaEvent]
    have hinter : fullEvent ∩ thetaEventᶜ ∩ forcedEvent =
        (lazyQ ∩ (sourceProfileThetaBad cWindow m 1 A.profile)ᶜ) ×ˢ
          {A.forcedDirection} := by
      ext z
      simp [fullEvent, forcedEvent, thetaEvent]
    have hdir : directionLaw.real {A.forcedDirection} = (1 / 4 : ℝ) := by
      rw [measureReal_def]
      simp [directionLaw]
    rw [hinter, hfull]
    dsimp [nu]
    rw [measureReal_prod_prod, measureReal_prod_prod, hdir]
    simp
    ring
  have hprofileReal :
      nu.real (fullEvent ∩ thetaEventᶜ) ≤
        4 * (Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹) := by
    rw [hgoodEvent] at hforced
    nlinarith [hgood]
  have hprofile :
      nu (fullEvent ∩ thetaEventᶜ) ≤
        ENNReal.ofReal (4 * (Real.exp (-c * rho) *
          (1 - Real.exp (-c))⁻¹)) := by
    rw [← ofReal_measureReal (measure_ne_top nu _)]
    exact ENNReal.ofReal_le_ofReal hprofileReal
  have hsubset : (failure \ A.thetaPathEvent) ∩ A.pathAtom ⊆
      A.pathAtom ∩ (fun s ↦ (A.lazyVector s, A.nextDirection s)) ⁻¹'
        (fullEvent ∩ thetaEventᶜ) := by
    intro s hs
    refine ⟨hs.2, A.failure_subset ⟨hs.1.1, hs.2⟩, ?_⟩
    intro htheta
    exact hs.1.2 (A.theta_preimage_subset ⟨hs.2, htheta⟩)
  calc
    simpleRandomWalkLaw ((failure \ A.thetaPathEvent) ∩ A.pathAtom) ≤
        simpleRandomWalkLaw
          (A.pathAtom ∩ (fun s ↦ (A.lazyVector s, A.nextDirection s)) ⁻¹'
            (fullEvent ∩ thetaEventᶜ)) := measure_mono hsubset
    _ = (simpleRandomWalkLaw.restrict A.pathAtom)
        ((fun s ↦ (A.lazyVector s, A.nextDirection s)) ⁻¹'
          (fullEvent ∩ thetaEventᶜ)) := by
      rw [Measure.restrict_apply' A.measurableSet_pathAtom, inter_comm]
    _ = ((simpleRandomWalkLaw.restrict A.pathAtom).map
          (fun s ↦ (A.lazyVector s, A.nextDirection s)))
            (fullEvent ∩ thetaEventᶜ) := by
      rw [Measure.map_apply
        (A.measurable_lazyVector.prodMk A.measurable_nextDirection)
        MeasurableSet.of_discrete]
    _ = simpleRandomWalkLaw A.pathAtom *
        nu (fullEvent ∩ thetaEventᶜ) := by
      rw [A.map_law, Measure.smul_apply]
      rfl
    _ ≤ simpleRandomWalkLaw A.pathAtom *
        ENNReal.ofReal (4 * (Real.exp (-c * rho) *
          (1 - Real.exp (-c))⁻¹)) := by gcongr
    _ = ENNReal.ofReal (4 * (Real.exp (-c * rho) *
          (1 - Real.exp (-c))⁻¹)) *
        simpleRandomWalkLaw A.pathAtom := mul_comm _ _

/-- Equation (4.47) with the source switch performed in random-walk path
space.  In particular, the artificial-`I₀` witnesses are not required to
belong to the same truncated stopped-profile law as the bad paths. -/
theorem stoppedEquation447ChangedPathBranch_bound
    {c rho : ℝ} {failure thetaPathEvent : Set (ℕ → Site)}
    (A : StoppedEquation447ChangedPathBranch
      c failure thetaPathEvent rho)
    (hc : 0 < c) :
    simpleRandomWalkLaw (failure \ thetaPathEvent) ≤
      ENNReal.ofReal (4 * (Real.exp (-c * rho) *
        (1 - Real.exp (-c))⁻¹)) := by
  letI : Countable A.Code := A.codeCountable
  have hforced : simpleRandomWalkLaw.real A.forcedGoodEvent ≤
      Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹ := by
    exact equation447_real_of_fixed_cardinality_pos simpleRandomWalkLaw
      A.forcedGoodEvent A.badByCount A.badPathAtom A.witnessPathAtom
      rho c hc A.forced_count_cover A.count_path_cover A.path_switch
      A.witness_disjoint A.witness_measurable
  have hreal : simpleRandomWalkLaw.real (failure \ thetaPathEvent) ≤
      4 * (Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹) :=
    A.forced_reduction.trans (mul_le_mul_of_nonneg_left hforced (by norm_num))
  rw [← ofReal_measureReal (measure_ne_top simpleRandomWalkLaw _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The fixed-profile consequence of the literal deleted-path switch.

This is the sharing point with Proposition 4.8.  The path modification in
(4.51)--(4.54) bounds the first source band under the truncated product law
before that law is transported back to a stopped path atom.  Consequently
the same changed-path witness used by Lemmas 4.11--4.12 supplies the base
estimate for the later adjacent-band recursion; no second same-history
categorical factorization is needed. -/
theorem stoppedEquation447PathWitnessBranchAtom_profile_good_base_bound
    {cWindow m : ℕ} {c rho : ℝ}
    {failure : Set (ℕ → Site)}
    (A : StoppedEquation447PathWitnessBranchAtom
      cWindow m c failure rho)
    (hc : 0 < c) :
    let _ : Fintype A.Coord := A.coordFintype
    (sourceTruncatedProfileMeasure m A.profile).real
        ((sourceProfileQEvent m 1 A.profile rho ∩ A.D) \
          sourceProfileThetaBad cWindow m 1 A.profile) ≤
      4 * (Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹) := by
  letI : Fintype A.Coord := A.coordFintype
  letI : Countable A.Path := A.pathCountable
  let lazyNu : Measure (A.Coord → ℕ) :=
    sourceTruncatedProfileMeasure m A.profile
  letI (x : A.Coord) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (A.profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (A.profile x) (A.profile_lt x))
  letI : IsProbabilityMeasure lazyNu := by
    dsimp [lazyNu]
    unfold sourceTruncatedProfileMeasure
    infer_instance
  let nu : Measure ((A.Coord → ℕ) × Direction) :=
    lazyNu.prod directionLaw
  letI : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  let lazyQ : Set (A.Coord → ℕ) :=
    sourceProfileQEvent m 1 A.profile rho ∩ A.D
  let fullEvent : Set ((A.Coord → ℕ) × Direction) :=
    lazyQ ×ˢ (Set.univ : Set Direction)
  let forcedEvent : Set ((A.Coord → ℕ) × Direction) :=
    (Set.univ : Set (A.Coord → ℕ)) ×ˢ {A.forcedDirection}
  let thetaEvent : Set ((A.Coord → ℕ) × Direction) :=
    sourceProfileThetaBad cWindow m 1 A.profile ×ˢ
      (Set.univ : Set Direction)
  let goodEvent : Set ((A.Coord → ℕ) × Direction) :=
    sourceEquation447Event cWindow m A.profile rho A.D Set.univ ×ˢ
      {A.forcedDirection}
  let byCount (q : ℕ) : Set ((A.Coord → ℕ) × Direction) :=
    sourceEquation447ByCount cWindow m A.profile A.D Set.univ q ×ˢ
      {A.forcedDirection}
  have hcoverCount : goodEvent ⊆
      ⋃ k : ℕ, byCount (Nat.ceil rho + k) := by
    rintro ⟨lazy, direction⟩ ⟨hlazy, hdirection⟩
    rcases Set.mem_iUnion.mp
        (sourceEquation447Event_subset_iUnion_byCount cWindow m A.profile
          rho A.D Set.univ hlazy) with ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk, hdirection⟩
  have hgood : nu.real goodEvent ≤
      Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹ := by
    exact equation447_real_of_fixed_cardinality_pos nu goodEvent byCount
      A.badAtom A.witnessAtom rho c hc hcoverCount A.equation447_cover
      A.path_switch A.witness_disjoint A.witness_measurable
  have hgoodEvent : fullEvent ∩ thetaEventᶜ ∩ forcedEvent = goodEvent := by
    ext z
    simp only [fullEvent, forcedEvent, thetaEvent, goodEvent, lazyQ,
      sourceEquation447Event, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_univ, and_true, Set.mem_compl_iff]
    tauto
  have hforced :
      nu.real (fullEvent ∩ thetaEventᶜ ∩ forcedEvent) =
        (1 / 4 : ℝ) * nu.real (fullEvent ∩ thetaEventᶜ) := by
    have hfull : fullEvent ∩ thetaEventᶜ =
        (lazyQ ∩ (sourceProfileThetaBad cWindow m 1 A.profile)ᶜ) ×ˢ
          (Set.univ : Set Direction) := by
      ext z
      simp [fullEvent, thetaEvent]
    have hinter : fullEvent ∩ thetaEventᶜ ∩ forcedEvent =
        (lazyQ ∩ (sourceProfileThetaBad cWindow m 1 A.profile)ᶜ) ×ˢ
          {A.forcedDirection} := by
      ext z
      simp [fullEvent, forcedEvent, thetaEvent]
    have hdir : directionLaw.real {A.forcedDirection} = (1 / 4 : ℝ) := by
      rw [measureReal_def]
      simp [directionLaw]
    rw [hinter, hfull]
    dsimp [nu]
    rw [measureReal_prod_prod, measureReal_prod_prod, hdir]
    simp
    ring
  have hprofileReal :
      nu.real (fullEvent ∩ thetaEventᶜ) ≤
        4 * (Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹) := by
    rw [hgoodEvent] at hforced
    nlinarith [hgood]
  have hfull : fullEvent ∩ thetaEventᶜ =
      ((lazyQ \
        sourceProfileThetaBad cWindow m 1 A.profile) ×ˢ
          (Set.univ : Set Direction)) := by
    ext z
    simp [fullEvent, thetaEvent]
  rw [hfull] at hprofileReal
  dsimp [nu, lazyNu, lazyQ] at hprofileReal ⊢
  have hdirUniv : directionLaw.real (Set.univ : Set Direction) = 1 := by
    rw [measureReal_def, measure_univ]
    simp
  simpa only [measureReal_prod_prod, hdirUniv, mul_one] using hprofileReal

private theorem cardinalityFailure_measure_le_of_stoppedProfileAtoms
    {cWindow m : ℕ} {C cTheta a : ℝ} {i : Fin 6} {r : StageIndex}
    (atoms : ℕ → StoppedEquation447Atom cWindow m C cTheta a
      (lemma411412CardinalityFailureEvent m i r))
    (hcover : lemma411412CardinalityFailureEvent m i r ⊆
      ⋃ eta, (atoms eta).pathAtom)
    (hdisjoint : Pairwise fun eta zeta ↦
      Disjoint (atoms eta).pathAtom (atoms zeta).pathAtom)
    (hC : 0 < C)
    (habsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d * (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K +
          Real.exp (-cTheta * (m : ℝ) ^ a)) ≤
        Real.exp (-(d / 2) * Real.log (m : ℝ) ^ 2)) :
    simpleRandomWalkLaw (lemma411412CardinalityFailureEvent m i r) ≤
      ENNReal.ofReal (Real.exp (-(Real.log ((C + 1) / C) / 2) *
        Real.log (m : ℝ) ^ 2)) := by
  apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw
    (lemma411412CardinalityFailureEvent m i r)
    (fun eta ↦ lemma411412CardinalityFailureEvent m i r ∩ (atoms eta).pathAtom)
    (fun eta ↦ (atoms eta).pathAtom)
    (ENNReal.ofReal (Real.exp (-(Real.log ((C + 1) / C) / 2) *
      Real.log (m : ℝ) ^ 2)))
  · intro s hs
    rcases Set.mem_iUnion.mp (hcover hs) with ⟨eta, heta⟩
    exact Set.mem_iUnion.mpr ⟨eta, hs, heta⟩
  · intro eta
    exact stoppedEquation447Atom_local_bound (atoms eta) hC habsorb
  · exact hdisjoint
  · intro eta
    exact (atoms eta).measurableSet_pathAtom

/-! ### Finite source-branch aggregation

The four parity/winner families in the stopped construction are not mutually
disjoint.  They therefore must first be summed by a finite union bound.  Only
the countable atoms *inside each branch* need to be pairwise disjoint. -/

private theorem eventually_branchConditionalEquation447_error_absorb
    {C rhoCoeff : ℝ}
    (hC : 0 < C)
    (hrhoCoeff : 0 < rhoCoeff) :
    ∀ᶠ m : ℕ in atTop, ∀ rho : ℝ,
      rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho →
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d * (Nat.ceil rho : ℝ)) * K) ≤
        Real.exp (-(d * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2) := by
  let d := Real.log ((C + 1) / C)
  let c := d * rhoCoeff
  let K := (1 - Real.exp (-d))⁻¹
  have hratio : 1 < (C + 1) / C := by
    rw [one_lt_div hC]
    linarith
  have hd : 0 < d := Real.log_pos hratio
  have hc : 0 < c := mul_pos hd hrhoCoeff
  have habsorb := HLOZLemma411.eventually_three_rpow_mul_exp_neg_log_sq_le
    hc (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (4 * (K + 1) / 3)
  filter_upwards [habsorb, eventually_ge_atTop N] with
      m habsorbM hm
  intro rho hrho
  have hK0 : 0 ≤ K := by
    dsimp [K]
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hcoeff : 4 * (K + 1) ≤ 3 * (m : ℝ) := by
    have hNm : (N : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hceil : rho ≤ (Nat.ceil rho : ℝ) := Nat.le_ceil rho
  have hthresholdCeil :
      rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ (Nat.ceil rho : ℝ) :=
    hrho.trans hceil
  have hfirst :
      Real.exp (-d * (Nat.ceil rho : ℝ)) ≤
        Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hthresholdCeil hd.le
    dsimp [c]
    nlinarith
  have hexp0 : 0 ≤ Real.exp (-c * Real.log (m : ℝ) ^ 2) :=
    (Real.exp_pos _).le
  dsimp only [d, K]
  calc
    4 * (Real.exp
          (-Real.log ((C + 1) / C) * (Nat.ceil rho : ℝ)) *
          (1 - Real.exp (-Real.log ((C + 1) / C)))⁻¹) ≤
        4 * (K + 1) * Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
      dsimp [d, K] at hfirst hK0 ⊢
      nlinarith
    _ ≤ 3 * (m : ℝ) * Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
      gcongr
    _ = 3 * (m : ℝ) ^ (1 : ℝ) *
        Real.exp (-c * Real.log (m : ℝ) ^ 2) := by rw [Real.rpow_one]
    _ ≤ Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2) := habsorbM
    _ = Real.exp
        (-(Real.log ((C + 1) / C) * rhoCoeff / 2) *
          Real.log (m : ℝ) ^ 2) := by rfl

/-- Public logarithmic-square specialization of the branch absorption.
This is the base rate used when equation (4.47) starts the theta-free
Proposition 4.8 recursion. -/
theorem eventually_equation447_logSq_profile_base_absorb
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(d / 2 * Real.log (m : ℝ) ^ 2)) := by
  have h := eventually_branchConditionalEquation447_error_absorb
    hC (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h] with m hm
  have hle : 1 * Real.log (m : ℝ) ^ 2 ≤ Real.log (m : ℝ) ^ 2 := by
    rw [one_mul]
  have hm' := hm (Real.log (m : ℝ) ^ 2) hle
  dsimp only at hm' ⊢
  convert hm' using 1 <;> ring

private theorem branch_measure_le_of_stoppedProfileAtoms
    {cWindow m : ℕ} {C rho rhoCoeff : ℝ}
    (branch : Set (ℕ → Site))
    (atoms : ℕ → StoppedEquation447BranchAtom
      cWindow m C branch rho)
    (thetaTarget : Set (ℕ → Site))
    (hcover : branch ⊆ ⋃ eta, (atoms eta).pathAtom)
    (htheta : ∀ eta, (atoms eta).thetaPathEvent ⊆ thetaTarget)
    (hdisjoint : Pairwise fun eta zeta ↦
      Disjoint (atoms eta).pathAtom (atoms zeta).pathAtom)
    (hC : 0 < C)
    (habsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d * (Nat.ceil rho : ℝ)) * K) ≤
        Real.exp (-(d * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) :
    simpleRandomWalkLaw (branch \ thetaTarget) ≤
      ENNReal.ofReal (Real.exp
        (-(Real.log ((C + 1) / C) * rhoCoeff / 2) *
          Real.log (m : ℝ) ^ 2)) := by
  apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw
    (branch \ thetaTarget)
    (fun eta ↦ (branch \ thetaTarget) ∩ (atoms eta).pathAtom)
    (fun eta ↦ (atoms eta).pathAtom)
    (ENNReal.ofReal (Real.exp
      (-(Real.log ((C + 1) / C) * rhoCoeff / 2) *
        Real.log (m : ℝ) ^ 2)))
  · intro s hs
    rcases Set.mem_iUnion.mp (hcover hs.1) with ⟨eta, heta⟩
    exact Set.mem_iUnion.mpr ⟨eta, hs, heta⟩
  · intro eta
    have habsorb' :
        let d := Real.log ((C + 1) / C)
        let K := (1 - Real.exp (-d))⁻¹
        4 * (Real.exp (-d * (Nat.ceil rho : ℝ)) * K) ≤
          Real.exp (-(d * rhoCoeff / 2 * Real.log (m : ℝ) ^ 2)) := by
      simpa only [neg_mul] using habsorb
    calc
      simpleRandomWalkLaw
          ((branch \ thetaTarget) ∩ (atoms eta).pathAtom) ≤
        simpleRandomWalkLaw
          ((branch \ (atoms eta).thetaPathEvent) ∩
            (atoms eta).pathAtom) := by
          apply measure_mono
          rintro s ⟨⟨hsBranch, hsTheta⟩, hsAtom⟩
          exact ⟨⟨hsBranch, fun h ↦ hsTheta (htheta eta h)⟩, hsAtom⟩
      _ ≤ ENNReal.ofReal
            (Real.exp (-(Real.log ((C + 1) / C) * rhoCoeff / 2) *
              Real.log (m : ℝ) ^ 2)) *
          simpleRandomWalkLaw (atoms eta).pathAtom := by
        simpa only [neg_mul] using
          (stoppedEquation447BranchAtom_local_bound_of_absorb
          (target := Real.log ((C + 1) / C) * rhoCoeff / 2 *
            Real.log (m : ℝ) ^ 2) (atoms eta) hC habsorb')
  · exact hdisjoint
  · intro eta
    exact (atoms eta).measurableSet_pathAtom

/-- A finite collection of source branches.  No disjointness is imposed
between branches; each branch carries its own countable disjoint atomization.
Each branch also carries its own failure event and threshold; `rhoCoeff` is
the uniform positive fraction of `log(m)^2` retained after the deterministic
winner split.  For the paper's decomposition one instantiates
`branchCount = 4`. -/
def Prop47Lemma411412FiniteBranchStoppedProfileInputs
    (branchCount cWindow : ℕ) (C rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    ∃ branchFailure : Fin branchCount → Set (ℕ → Site),
      ∃ rho : Fin branchCount → ℝ,
      ∃ atoms : (j : Fin branchCount) → ℕ →
          StoppedEquation447BranchAtom cWindow m C
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        (∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ⊆ ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆
          stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
            m (stageNumber r)) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom

/-- Finite-branch input for the literal deleted-path switch proof of (4.47).
The branch and stopped-atom covers are the same as in
`Prop47Lemma411412FiniteBranchStoppedProfileInputs`, but the local atom is the
path-witness atom above.  Thus the only fixed-cardinality inputs are the
checked path switch and the witness disjointness (4.54). -/
def Prop47Lemma411412FiniteBranchPathWitnessInputs
    (branchCount cWindow : ℕ) (c rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    ∃ branchFailure : Fin branchCount → Set (ℕ → Site),
      ∃ rho : Fin branchCount → ℝ,
      ∃ atoms : (j : Fin branchCount) → ℕ →
          StoppedEquation447PathWitnessBranchAtom cWindow m c
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        (∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ∩
            HLOZSourceInstantiation.simpleRandomWalkSupport ⊆
          ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆
          stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
            m (stageNumber r)) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom

/-- Finite-branch form of the actual changed-deleted-path proof.

There is one path-space switch package per winner/parity branch, rather than
one switch inside every stopped-profile atom.  This is the quantifier order
of HLOZ (4.51)--(4.54): changed paths from different original external
profiles are allowed to meet, and the global stopped-horizon argument proves
disjointness only after all of them have been collected. -/
def Prop47Lemma411412FiniteBranchChangedPathInputs
    (branchCount : ℕ) (c rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    ∃ branchFailure : Fin branchCount → Set (ℕ → Site),
      ∃ rho : Fin branchCount → ℝ,
      ∃ branches : (j : Fin branchCount) →
          StoppedEquation447ChangedPathBranch c (branchFailure j)
            (stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r)) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        ∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j

/-- Changed-path input with the source's natural profile exception retained
explicitly.  This is the form needed for the reflected column pairing, whose
exception is paid separately rather than identified with the canonical
temporal `Theta` event. -/
def Prop47Lemma411412FiniteBranchChangedPathAuxThetaInputs
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set (ℕ → Site))
    (branchCount : ℕ) (c rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    ∃ branchFailure : Fin branchCount → Set (ℕ → Site),
      ∃ rho : Fin branchCount → ℝ,
      ∃ branches : (j : Fin branchCount) →
          StoppedEquation447ChangedPathBranch c (branchFailure j)
            (thetaTarget m i r) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        ∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j

/-- Flexible-theta form of the literal deleted-path-switch input.  This is
needed for the reflected column pairing: its natural stopped exception is
the reflection of the `Y` temporal event, and is paid by a separate
auxiliary-theta estimate rather than identified with an unrelated event. -/
def Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputs
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set (ℕ → Site))
    (branchCount cWindow : ℕ) (c rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    ∃ branchFailure : Fin branchCount → Set (ℕ → Site),
      ∃ rho : Fin branchCount → ℝ,
      ∃ atoms : (j : Fin branchCount) → ℕ →
          StoppedEquation447PathWitnessBranchAtom cWindow m c
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        (∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ∩
            HLOZSourceInstantiation.simpleRandomWalkSupport ⊆
          ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆ thetaTarget m i r) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom

/-- Flexible-theta finite-branch input.  The stopped categorical law may
have a natural profile exception different from the canonical temporal
`Theta` event.  Its probability is supplied separately through
`Prop47Lemma411412AuxThetaEstimate`; no set-theoretic comparison between the
two exceptions is required. -/
def Prop47Lemma411412FiniteBranchAuxThetaInputs
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set (ℕ → Site))
    (branchCount cWindow : ℕ) (C rhoCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    ∃ branchFailure : Fin branchCount → Set (ℕ → Site),
      ∃ rho : Fin branchCount → ℝ,
      ∃ atoms : (j : Fin branchCount) → ℕ →
          StoppedEquation447BranchAtom cWindow m C
            (branchFailure j) (rho j),
        lemma411412CardinalityFailureEvent m i r ⊆ ⋃ j, branchFailure j ∧
        (∀ j, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j) ∧
        (∀ j, branchFailure j ⊆ ⋃ eta, (atoms j eta).pathAtom) ∧
        (∀ j eta, (atoms j eta).thetaPathEvent ⊆ thetaTarget m i r) ∧
        ∀ j, Pairwise fun eta zeta ↦
          Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom

/-- Eventual bound for the auxiliary stopped-atom profile exception, with
the same deterministic prefix/avoidance/distance factors as the target
Lemmas 4.11--4.12 failure. -/
def Prop47Lemma411412AuxThetaEstimate
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set (ℕ → Site))
    (thetaCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    ∀ a : AlphaIndex, alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma411412AuxThetaEvent thetaTarget m i r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m thetaCoeff kappa

private theorem cardinalityFailure_measure_le_of_finiteBranches
    {branchCount cWindow m : ℕ} {C rhoCoeff : ℝ}
    {i : Fin 6} {r : StageIndex}
    (branchFailure : Fin branchCount → Set (ℕ → Site))
    (rho : Fin branchCount → ℝ)
    (atoms : (j : Fin branchCount) → ℕ →
      StoppedEquation447BranchAtom cWindow m C
        (branchFailure j) (rho j))
    (thetaTarget : Set (ℕ → Site))
    (hcover : lemma411412CardinalityFailureEvent m i r ⊆
      ⋃ j, branchFailure j)
    (hthreshold : ∀ j,
      rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j)
    (hatomCover : ∀ j,
      branchFailure j ⊆ ⋃ eta, (atoms j eta).pathAtom)
    (htheta : ∀ j eta, (atoms j eta).thetaPathEvent ⊆ thetaTarget)
    (hdisjoint : ∀ j, Pairwise fun eta zeta ↦
      Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom)
    (hC : 0 < C)
    (habsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      ∀ rho : ℝ, rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho →
        4 * (Real.exp (-d * (Nat.ceil rho : ℝ)) * K) ≤
          Real.exp (-(d * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) :
    simpleRandomWalkLaw
        (lemma411412CardinalityFailureEvent m i r \ thetaTarget) ≤
      (branchCount : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-(Real.log ((C + 1) / C) * rhoCoeff / 2) *
            Real.log (m : ℝ) ^ 2)) := by
  calc
    simpleRandomWalkLaw
        (lemma411412CardinalityFailureEvent m i r \ thetaTarget) ≤
        simpleRandomWalkLaw (⋃ j, branchFailure j \ thetaTarget) := by
      apply measure_mono
      rintro s ⟨hsCard, hsTheta⟩
      rcases Set.mem_iUnion.mp (hcover hsCard) with ⟨j, hj⟩
      exact Set.mem_iUnion.mpr ⟨j, hj, hsTheta⟩
    _ ≤ ∑ j, simpleRandomWalkLaw
        (branchFailure j \ thetaTarget) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin branchCount,
        ENNReal.ofReal (Real.exp
          (-(Real.log ((C + 1) / C) * rhoCoeff / 2) *
            Real.log (m : ℝ) ^ 2)) := by
      exact Finset.sum_le_sum fun j _ ↦
        branch_measure_le_of_stoppedProfileAtoms (branchFailure j) (atoms j)
          thetaTarget
          (hatomCover j) (htheta j) (hdisjoint j) hC
            (habsorb (rho j) (hthreshold j))
    _ = (branchCount : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-(Real.log ((C + 1) / C) * rhoCoeff / 2) *
            Real.log (m : ℝ) ^ 2)) := by simp

/-- A fixed finite number of branches is absorbed by sacrificing another
factor two in the logarithmic-square exponent. -/
private theorem eventually_finiteBranch_profileRate_absorb
    (branchCount : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ m : ℕ in atTop,
      (branchCount : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-(d / 2) * Real.log (m : ℝ) ^ 2)) ≤
        ENNReal.ofReal (Real.exp (-(d / 4) * Real.log (m : ℝ) ^ 2)) := by
  have hpoly := HLOZLemma411.eventually_three_rpow_mul_exp_neg_log_sq_le
    (c := d / 2) (b := (1 : ℝ)) (by positivity) (by norm_num)
  filter_upwards [hpoly, eventually_ge_atTop branchCount,
    eventually_ge_atTop 1] with m hpolyM hm h1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hcoeff : (branchCount : ℝ) ≤ 3 * (m : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    exact_mod_cast (show branchCount ≤ 3 * m by omega)
  have hreal :
      (branchCount : ℝ) *
          Real.exp (-(d / 2) * Real.log (m : ℝ) ^ 2) ≤
        Real.exp (-(d / 4) * Real.log (m : ℝ) ^ 2) := by
    calc
      (branchCount : ℝ) *
          Real.exp (-(d / 2) * Real.log (m : ℝ) ^ 2) ≤
        (3 * (m : ℝ) ^ (1 : ℝ)) *
          Real.exp (-(d / 2) * Real.log (m : ℝ) ^ 2) := by gcongr
      _ ≤ Real.exp (-((d / 2) / 2) * Real.log (m : ℝ) ^ 2) := hpolyM
      _ = Real.exp (-(d / 4) * Real.log (m : ℝ) ^ 2) := by ring_nf
  rw [← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (show 0 ≤ (branchCount : ℝ) by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- A fixed changed-path prefactor is absorbed by half of the available
logarithmic-square exponent.  This is public because the identical
fixed-profile estimate is also the base band in Proposition 4.8. -/
theorem eventually_pathWitnessEquation447_error_absorb
    {c rhoCoeff : ℝ} (hc : 0 < c) (hrhoCoeff : 0 < rhoCoeff) :
    ∀ᶠ m : ℕ in atTop, ∀ rho : ℝ,
      rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho →
        4 * (Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹) ≤
          Real.exp (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2) := by
  let prefactor : ℝ := 4 * (1 - Real.exp (-c))⁻¹
  have hden : 0 < 1 - Real.exp (-c) :=
    sub_pos.mpr ((Real.exp_lt_one_iff).mpr (by linarith))
  have hprefactor : 0 < prefactor := by
    dsimp [prefactor]
    positivity
  have hcrho : 0 < c * rhoCoeff := mul_pos hc hrhoCoeff
  have hpoly := HLOZLemma411.eventually_three_rpow_mul_exp_neg_log_sq_le
    hcrho (show (0 : ℝ) ≤ 1 by norm_num)
  filter_upwards [hpoly, eventually_ge_atTop (Nat.ceil prefactor),
    eventually_ge_atTop 1] with m hpolyM hm h1
  intro rho hrho
  have hexp : Real.exp (-c * rho) ≤
      Real.exp (-(c * rhoCoeff) * Real.log (m : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hrho hc.le
    nlinarith
  have hprefactorM : prefactor ≤ (m : ℝ) := by
    exact (Nat.le_ceil prefactor).trans (by exact_mod_cast hm)
  have hcoeff : prefactor ≤ 3 * (m : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    nlinarith [show (0 : ℝ) < m by exact_mod_cast h1]
  calc
    4 * (Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹) =
        prefactor * Real.exp (-c * rho) := by
      dsimp [prefactor]
      ring
    _ ≤ prefactor *
        Real.exp (-(c * rhoCoeff) * Real.log (m : ℝ) ^ 2) := by gcongr
    _ ≤ (3 * (m : ℝ) ^ (1 : ℝ)) *
        Real.exp (-(c * rhoCoeff) * Real.log (m : ℝ) ^ 2) := by
      gcongr
    _ ≤ Real.exp (-((c * rhoCoeff) / 2) *
        Real.log (m : ℝ) ^ 2) := hpolyM

private theorem branch_measure_le_of_pathWitnessAtoms
    {cWindow m : ℕ} {c rho rhoCoeff : ℝ}
    (branch : Set (ℕ → Site))
    (atoms : ℕ → StoppedEquation447PathWitnessBranchAtom
      cWindow m c branch rho)
    (thetaTarget : Set (ℕ → Site))
    (hcover : branch ∩ HLOZSourceInstantiation.simpleRandomWalkSupport ⊆
      ⋃ eta, (atoms eta).pathAtom)
    (htheta : ∀ eta, (atoms eta).thetaPathEvent ⊆ thetaTarget)
    (hdisjoint : Pairwise fun eta zeta ↦
      Disjoint (atoms eta).pathAtom (atoms zeta).pathAtom)
    (hc : 0 < c)
    (habsorb : 4 * (Real.exp (-c * rho) *
      (1 - Real.exp (-c))⁻¹) ≤
      Real.exp (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) :
    simpleRandomWalkLaw (branch \ thetaTarget) ≤
      ENNReal.ofReal (Real.exp
        (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) := by
  have hsupported : simpleRandomWalkLaw
      ((branch ∩ HLOZSourceInstantiation.simpleRandomWalkSupport) \
        thetaTarget) ≤
      ENNReal.ofReal (Real.exp
        (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) := by
    apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw
      ((branch ∩ HLOZSourceInstantiation.simpleRandomWalkSupport) \
        thetaTarget)
      (fun eta ↦
        (((branch ∩ HLOZSourceInstantiation.simpleRandomWalkSupport) \
          thetaTarget) ∩ (atoms eta).pathAtom))
      (fun eta ↦ (atoms eta).pathAtom)
      (ENNReal.ofReal (Real.exp
        (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)))
    · intro s hs
      rcases hs with ⟨⟨hsBranch, hsSupport⟩, hsTheta⟩
      rcases Set.mem_iUnion.mp (hcover ⟨hsBranch, hsSupport⟩) with
        ⟨eta, heta⟩
      exact Set.mem_iUnion.mpr
        ⟨eta, ⟨⟨⟨hsBranch, hsSupport⟩, hsTheta⟩, heta⟩⟩
    · intro eta
      calc
        simpleRandomWalkLaw
            ((((branch ∩
                HLOZSourceInstantiation.simpleRandomWalkSupport) \
              thetaTarget) ∩ (atoms eta).pathAtom)) ≤
          simpleRandomWalkLaw
            ((branch \ (atoms eta).thetaPathEvent) ∩
              (atoms eta).pathAtom) := by
            apply measure_mono
            rintro s ⟨⟨⟨hsBranch, _hsSupport⟩, hsTheta⟩, hsAtom⟩
            exact ⟨⟨hsBranch, fun h ↦ hsTheta (htheta eta h)⟩, hsAtom⟩
        _ ≤ ENNReal.ofReal (4 * (Real.exp (-c * rho) *
              (1 - Real.exp (-c))⁻¹)) *
            simpleRandomWalkLaw (atoms eta).pathAtom :=
          stoppedEquation447PathWitnessBranchAtom_local_bound (atoms eta) hc
        _ ≤ ENNReal.ofReal (Real.exp
              (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) *
            simpleRandomWalkLaw (atoms eta).pathAtom := by
          gcongr
    · exact hdisjoint
    · intro eta
      exact (atoms eta).measurableSet_pathAtom
  have hevent :
      (branch ∩ HLOZSourceInstantiation.simpleRandomWalkSupport) \
          thetaTarget =
        HLOZSourceInstantiation.simpleRandomWalkSupport ∩
          (branch \ thetaTarget) := by
    ext s
    simp only [Set.mem_diff, Set.mem_inter_iff]
    tauto
  rw [hevent,
    HLOZSourceInstantiation.simpleRandomWalkLaw_inter_support] at hsupported
  exact hsupported

private theorem cardinalityFailure_measure_le_of_pathWitnessBranches
    {branchCount cWindow m : ℕ} {c rhoCoeff : ℝ}
    {i : Fin 6} {r : StageIndex}
    (branchFailure : Fin branchCount → Set (ℕ → Site))
    (rho : Fin branchCount → ℝ)
    (atoms : (j : Fin branchCount) → ℕ →
      StoppedEquation447PathWitnessBranchAtom cWindow m c
        (branchFailure j) (rho j))
    (thetaTarget : Set (ℕ → Site))
    (hcover : lemma411412CardinalityFailureEvent m i r ⊆
      ⋃ j, branchFailure j)
    (hthreshold : ∀ j,
      rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j)
    (hatomCover : ∀ j,
      branchFailure j ∩ HLOZSourceInstantiation.simpleRandomWalkSupport ⊆
        ⋃ eta, (atoms j eta).pathAtom)
    (htheta : ∀ j eta, (atoms j eta).thetaPathEvent ⊆ thetaTarget)
    (hdisjoint : ∀ j, Pairwise fun eta zeta ↦
      Disjoint (atoms j eta).pathAtom (atoms j zeta).pathAtom)
    (hc : 0 < c)
    (habsorb : ∀ rho : ℝ,
      rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho →
        4 * (Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹) ≤
          Real.exp (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) :
    simpleRandomWalkLaw
        (lemma411412CardinalityFailureEvent m i r \ thetaTarget) ≤
      (branchCount : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) := by
  calc
    simpleRandomWalkLaw
        (lemma411412CardinalityFailureEvent m i r \ thetaTarget) ≤
        simpleRandomWalkLaw (⋃ j, branchFailure j \ thetaTarget) := by
      apply measure_mono
      rintro s ⟨hsCard, hsTheta⟩
      rcases Set.mem_iUnion.mp (hcover hsCard) with ⟨j, hj⟩
      exact Set.mem_iUnion.mpr ⟨j, hj, hsTheta⟩
    _ ≤ ∑ j, simpleRandomWalkLaw (branchFailure j \ thetaTarget) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin branchCount,
        ENNReal.ofReal (Real.exp
          (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) := by
      exact Finset.sum_le_sum fun j _ ↦
        branch_measure_le_of_pathWitnessAtoms (branchFailure j) (atoms j)
          thetaTarget (hatomCover j) (htheta j) (hdisjoint j) hc
            (habsorb (rho j) (hthreshold j))
    _ = (branchCount : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) := by simp

/-- Union the source's globally switched path families over the finitely many
winner/parity branches.  There is deliberately no outer stopped-profile
atomization here: its disjointness would be destroyed by the changed-path
map in (4.51). -/
private theorem cardinalityFailure_measure_le_of_changedPathBranches
    {branchCount m : ℕ} {c rhoCoeff : ℝ}
    {i : Fin 6} {r : StageIndex}
    (thetaTarget : Set (ℕ → Site))
    (branchFailure : Fin branchCount → Set (ℕ → Site))
    (rho : Fin branchCount → ℝ)
    (branches : (j : Fin branchCount) →
      StoppedEquation447ChangedPathBranch c (branchFailure j)
        thetaTarget (rho j))
    (hcover : lemma411412CardinalityFailureEvent m i r ⊆
      ⋃ j, branchFailure j)
    (hthreshold : ∀ j,
      rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho j)
    (hc : 0 < c)
    (habsorb : ∀ rho : ℝ,
      rhoCoeff * Real.log (m : ℝ) ^ 2 ≤ rho →
        4 * (Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹) ≤
          Real.exp (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) :
    simpleRandomWalkLaw
        (lemma411412CardinalityFailureEvent m i r \
          thetaTarget) ≤
      (branchCount : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) := by
  calc
    simpleRandomWalkLaw
        (lemma411412CardinalityFailureEvent m i r \ thetaTarget) ≤
        simpleRandomWalkLaw (⋃ j, branchFailure j \ thetaTarget) := by
      apply measure_mono
      rintro s ⟨hsCard, hsTheta⟩
      rcases Set.mem_iUnion.mp (hcover hsCard) with ⟨j, hj⟩
      exact Set.mem_iUnion.mpr ⟨j, hj, hsTheta⟩
    _ ≤ ∑ j, simpleRandomWalkLaw (branchFailure j \ thetaTarget) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin branchCount,
        ENNReal.ofReal (Real.exp
          (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) := by
      apply Finset.sum_le_sum
      intro j _hj
      calc
        simpleRandomWalkLaw (branchFailure j \ thetaTarget) ≤
            ENNReal.ofReal (4 * (Real.exp (-c * rho j) *
              (1 - Real.exp (-c))⁻¹)) :=
          stoppedEquation447ChangedPathBranch_bound (branches j) hc
        _ ≤ ENNReal.ofReal (Real.exp
              (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) :=
          ENNReal.ofReal_le_ofReal (habsorb (rho j) (hthreshold j))
    _ = (branchCount : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) := by simp

/-- A shifted version of the standard logarithmic-square absorption, in the
exact `(m+1)^{-3 kappa}` normalization used by the Proposition 4.7
assembly. -/
theorem eventually_shifted_logSquare_le_sourceExceptional
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-d * Real.log ((m : ℝ) + 1) ^ 2)) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  have hreal := (tendsto_add_atTop_nat 1).eventually
    (eventually_exponential_error_absorbed (c := d) hd)
  filter_upwards [hreal] with m hm
  have hm' :
      Real.exp (-d * Real.log ((m : ℝ) + 1) ^ 2) ≤
        ((m : ℝ) + 1) ^ (-(3 * kappa)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hm
  rw [sourceExceptionalRateWithPrefactor]
  simp only [Nat.cast_one, one_mul]
  rw [sourceExceptionalRate]
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  rw [← hbase, ENNReal.ofReal_rpow_of_pos (by positivity)]
  exact ENNReal.ofReal_le_ofReal hm'

private theorem eventually_unshifted_half_logSquare_le_sourceExceptional
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2)) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  have hshift := eventually_shifted_logSquare_le_sourceExceptional
    (d := c / 8) (by positivity)
  filter_upwards [hshift, eventually_ge_atTop 2] with m hshift hm
  have hmpos : (0 : ℝ) < m := by positivity
  have hm1pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm1le : (m : ℝ) + 1 ≤ (m : ℝ) ^ 2 := by
    exact_mod_cast (show m + 1 ≤ m ^ 2 by nlinarith)
  have hlog : Real.log ((m : ℝ) + 1) ≤ 2 * Real.log (m : ℝ) := by
    calc
      Real.log ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) ^ 2) :=
        Real.log_le_log hm1pos hm1le
      _ = 2 * Real.log (m : ℝ) := by rw [Real.log_pow]; norm_num
  have hlog0 : 0 ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hmLog0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hsquare : Real.log ((m : ℝ) + 1) ^ 2 ≤
      4 * Real.log (m : ℝ) ^ 2 := by nlinarith
  have hexp :
      Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2) ≤
        Real.exp (-(c / 8) * Real.log ((m : ℝ) + 1) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (ENNReal.ofReal_le_ofReal hexp).trans hshift

/-- The stopped-profile inputs imply the exact named estimate consumed by
the Proposition 4.7 assembly.  In particular, neither the target event
estimate nor a renamed equivalent of it is assumed. -/
theorem prop47Lemma411412Estimate_of_stoppedProfileInputs
    (cWindow : ℕ) {C cTheta a : ℝ}
    (hC : 0 < C) (hcTheta : 0 < cTheta) (ha : 0 < a)
    (h : Prop47Lemma411412StoppedProfileInputs cWindow C cTheta a) :
    Prop47Lemma411412Estimate 1 := by
  have hratio : 1 < (C + 1) / C := by
    rw [one_lt_div hC]
    linarith
  have hd : 0 < Real.log ((C + 1) / C) := Real.log_pos hratio
  have habsorb := eventually_conditionalEquation447_error_absorb hC hcTheta ha
  have hrate := eventually_unshifted_half_logSquare_le_sourceExceptional hd
  filter_upwards [h, habsorb, hrate] with m hm habsorbM hrateM
  intro i r alphaIndex _halpha
  rcases hm i r with ⟨atoms, hcover, hdisjoint⟩
  calc
    simpleRandomWalkLaw
        (lemma411412FailureEvent m i r (alphaValue alphaIndex)) ≤
      simpleRandomWalkLaw (lemma411412CardinalityFailureEvent m i r) :=
        measure_mono
          (lemma411412FailureEvent_subset_cardinalityFailureEvent
            m i r (alphaValue alphaIndex))
    _ ≤ ENNReal.ofReal
        (Real.exp (-(Real.log ((C + 1) / C) / 2) *
          Real.log (m : ℝ) ^ 2)) :=
      cardinalityFailure_measure_le_of_stoppedProfileAtoms atoms hcover
        hdisjoint hC habsorbM
    _ ≤ sourceExceptionalRateWithPrefactor m 1 kappa := hrateM

/-- Source-faithful finite-branch version.  Each branch is estimated using
Equation (4.47), branches are combined by a union bound, and the fixed branch
count is absorbed into the logarithmic-square exponential before conversion
to the polynomial exceptional rate. -/
theorem prop47Lemma411412Estimate_of_finiteBranchStoppedProfileInputs
    (branchCount cWindow prop45Coeff : ℕ) {C rhoCoeff : ℝ}
    (hC : 0 < C)
    (hrhoCoeff : 0 < rhoCoeff)
    (h : Prop47Lemma411412FiniteBranchStoppedProfileInputs
      branchCount cWindow C rhoCoeff)
    (hProp45 : Prop47Prop45Estimate
      sourceCanonicalProfiles canonicalCStar prop45Coeff) :
    Prop47Lemma411412Estimate (prop45Coeff + 1) := by
  have hratio : 1 < (C + 1) / C := by
    rw [one_lt_div hC]
    linarith
  have hd : 0 < Real.log ((C + 1) / C) := Real.log_pos hratio
  have hdRho : 0 < Real.log ((C + 1) / C) * rhoCoeff :=
    mul_pos hd hrhoCoeff
  have habsorb := eventually_branchConditionalEquation447_error_absorb
    hC hrhoCoeff
  have hbranches := eventually_finiteBranch_profileRate_absorb
    branchCount hdRho
  have hrate := eventually_unshifted_half_logSquare_le_sourceExceptional
    (c := Real.log ((C + 1) / C) * rhoCoeff / 2) (by positivity)
  filter_upwards [h, hProp45, habsorb, hbranches, hrate] with
      m hm hProp45M habsorbM hbranchesM hrateM
  intro i r alphaIndex halpha
  rcases hm i r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  have hcardDiff :
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r)) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
    calc
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r)) ≤
        (branchCount : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(Real.log ((C + 1) / C) * rhoCoeff / 2) *
            Real.log (m : ℝ) ^ 2)) :=
        cardinalityFailure_measure_le_of_finiteBranches branchFailure rho atoms
          (stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
            m (stageNumber r))
          hcover hthreshold hatomCover htheta hdisjoint hC habsorbM
      _ ≤ ENNReal.ofReal
        (Real.exp
          (-(Real.log ((C + 1) / C) * rhoCoeff / 4) *
          Real.log (m : ℝ) ^ 2)) := hbranchesM
      _ ≤ sourceExceptionalRateWithPrefactor m 1 kappa := by
        convert hrateM using 1 <;> ring
  calc
    simpleRandomWalkLaw
        (lemma411412FailureEvent m i r (alphaValue alphaIndex)) ≤
      simpleRandomWalkLaw
        (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex) ∪
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r))) :=
        measure_mono
          (lemma411412FailureEvent_subset_prop45_union_cardinalityDiff
            sourceCanonicalProfiles canonicalCStar m i r
              (alphaValue alphaIndex))
    _ ≤ simpleRandomWalkLaw
          (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex)) +
        simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r)) := measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
        sourceExceptionalRateWithPrefactor m 1 kappa :=
      add_le_add (hProp45M i r alphaIndex halpha) hcardDiff
    _ = sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Source-faithful Equation-(4.47) closure through the paper's deleted-path
switch.  The fixed-cardinality path switch and witness disjointness are
consumed inside each atom, the finitely many parity/winner branches are
union-bounded, and both fixed losses are absorbed in the logarithmic-square
rate before Proposition 4.5 is restored. -/
theorem prop47Lemma411412Estimate_of_finiteBranchPathWitnessInputs
    (branchCount cWindow prop45Coeff : ℕ) {c rhoCoeff : ℝ}
    (hc : 0 < c)
    (hrhoCoeff : 0 < rhoCoeff)
    (h : Prop47Lemma411412FiniteBranchPathWitnessInputs
      branchCount cWindow c rhoCoeff)
    (hProp45 : Prop47Prop45Estimate
      sourceCanonicalProfiles canonicalCStar prop45Coeff) :
    Prop47Lemma411412Estimate (prop45Coeff + 1) := by
  have hcrho : 0 < c * rhoCoeff := mul_pos hc hrhoCoeff
  have habsorb := eventually_pathWitnessEquation447_error_absorb
    hc hrhoCoeff
  have hbranches := eventually_finiteBranch_profileRate_absorb
    branchCount hcrho
  have hrate := eventually_unshifted_half_logSquare_le_sourceExceptional
    (c := c * rhoCoeff / 2) (by positivity)
  filter_upwards [h, hProp45, habsorb, hbranches, hrate] with
      m hm hProp45M habsorbM hbranchesM hrateM
  intro i r alphaIndex halpha
  rcases hm i r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  have hcardDiff :
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r)) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
    calc
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r)) ≤
        (branchCount : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) :=
        cardinalityFailure_measure_le_of_pathWitnessBranches
          branchFailure rho atoms
          (stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
            m (stageNumber r))
          hcover hthreshold hatomCover htheta hdisjoint hc habsorbM
      _ ≤ ENNReal.ofReal
          (Real.exp (-(c * rhoCoeff / 4) *
            Real.log (m : ℝ) ^ 2)) := hbranchesM
      _ ≤ sourceExceptionalRateWithPrefactor m 1 kappa := by
        convert hrateM using 1 <;> ring
  calc
    simpleRandomWalkLaw
        (lemma411412FailureEvent m i r (alphaValue alphaIndex)) ≤
      simpleRandomWalkLaw
        (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex) ∪
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r))) :=
        measure_mono
          (lemma411412FailureEvent_subset_prop45_union_cardinalityDiff
            sourceCanonicalProfiles canonicalCStar m i r
              (alphaValue alphaIndex))
    _ ≤ simpleRandomWalkLaw
          (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex)) +
        simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r)) := measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
        sourceExceptionalRateWithPrefactor m 1 kappa :=
      add_le_add (hProp45M i r alphaIndex halpha) hcardDiff
    _ = sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Source-faithful Equation-(4.47) closure with the changed-path switch at
the correct, global quantifier level.  The artificial-`I₀` witnesses are
ordinary random-walk path events, not cells of the truncated profile law and
not children of the original stopped-profile atom. -/
theorem prop47Lemma411412Estimate_of_finiteBranchChangedPathInputs
    (branchCount prop45Coeff : ℕ) {c rhoCoeff : ℝ}
    (hc : 0 < c)
    (hrhoCoeff : 0 < rhoCoeff)
    (h : Prop47Lemma411412FiniteBranchChangedPathInputs
      branchCount c rhoCoeff)
    (hProp45 : Prop47Prop45Estimate
      sourceCanonicalProfiles canonicalCStar prop45Coeff) :
    Prop47Lemma411412Estimate (prop45Coeff + 1) := by
  have hcrho : 0 < c * rhoCoeff := mul_pos hc hrhoCoeff
  have habsorb := eventually_pathWitnessEquation447_error_absorb
    hc hrhoCoeff
  have hbranches := eventually_finiteBranch_profileRate_absorb
    branchCount hcrho
  have hrate := eventually_unshifted_half_logSquare_le_sourceExceptional
    (c := c * rhoCoeff / 2) (by positivity)
  filter_upwards [h, hProp45, habsorb, hbranches, hrate] with
      m hm hProp45M habsorbM hbranchesM hrateM
  intro i r alphaIndex halpha
  rcases hm i r with
    ⟨branchFailure, rho, branches, hcover, hthreshold⟩
  have hcardDiff :
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r)) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
    calc
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r)) ≤
        (branchCount : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) :=
        cardinalityFailure_measure_le_of_changedPathBranches
          (stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
            m (stageNumber r))
          branchFailure rho branches hcover hthreshold hc habsorbM
      _ ≤ ENNReal.ofReal
          (Real.exp (-(c * rhoCoeff / 4) *
            Real.log (m : ℝ) ^ 2)) := hbranchesM
      _ ≤ sourceExceptionalRateWithPrefactor m 1 kappa := by
        convert hrateM using 1 <;> ring
  calc
    simpleRandomWalkLaw
        (lemma411412FailureEvent m i r (alphaValue alphaIndex)) ≤
      simpleRandomWalkLaw
        (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex) ∪
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r))) :=
        measure_mono
          (lemma411412FailureEvent_subset_prop45_union_cardinalityDiff
            sourceCanonicalProfiles canonicalCStar m i r
              (alphaValue alphaIndex))
    _ ≤ simpleRandomWalkLaw
          (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex)) +
        simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \
            stoppedThetaEvent (sourceCanonicalProfiles i) (canonicalCStar i)
              m (stageNumber r)) := measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
        sourceExceptionalRateWithPrefactor m 1 kappa :=
      add_le_add (hProp45M i r alphaIndex halpha) hcardDiff
    _ = sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Global changed-path closure with the source's natural auxiliary profile
exception.  This is the direct all-six endpoint matching the quarter-turn and
reflection assembly. -/
theorem prop47Lemma411412Estimate_of_finiteBranchChangedPathAuxThetaInputs
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set (ℕ → Site))
    (branchCount prop45Coeff thetaCoeff : ℕ)
    {c rhoCoeff : ℝ}
    (hc : 0 < c)
    (hrhoCoeff : 0 < rhoCoeff)
    (h : Prop47Lemma411412FiniteBranchChangedPathAuxThetaInputs
      thetaTarget branchCount c rhoCoeff)
    (hProp45 : Prop47Prop45Estimate
      sourceCanonicalProfiles canonicalCStar prop45Coeff)
    (hAuxTheta : Prop47Lemma411412AuxThetaEstimate
      thetaTarget thetaCoeff) :
    Prop47Lemma411412Estimate (prop45Coeff + thetaCoeff + 1) := by
  have hcrho : 0 < c * rhoCoeff := mul_pos hc hrhoCoeff
  have habsorb := eventually_pathWitnessEquation447_error_absorb
    hc hrhoCoeff
  have hbranches := eventually_finiteBranch_profileRate_absorb
    branchCount hcrho
  have hrate := eventually_unshifted_half_logSquare_le_sourceExceptional
    (c := c * rhoCoeff / 2) (by positivity)
  filter_upwards [h, hProp45, hAuxTheta, habsorb, hbranches, hrate] with
      m hm hProp45M hAuxThetaM habsorbM hbranchesM hrateM
  intro i r alphaIndex halpha
  rcases hm i r with
    ⟨branchFailure, rho, branches, hcover, hthreshold⟩
  have hcardDiff :
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \ thetaTarget m i r) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
    calc
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \ thetaTarget m i r) ≤
        (branchCount : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) :=
        cardinalityFailure_measure_le_of_changedPathBranches
          (thetaTarget m i r) branchFailure rho branches
          hcover hthreshold hc habsorbM
      _ ≤ ENNReal.ofReal
          (Real.exp (-(c * rhoCoeff / 4) *
            Real.log (m : ℝ) ^ 2)) := hbranchesM
      _ ≤ sourceExceptionalRateWithPrefactor m 1 kappa := by
        convert hrateM using 1 <;> ring
  calc
    simpleRandomWalkLaw
        (lemma411412FailureEvent m i r (alphaValue alphaIndex)) ≤
      simpleRandomWalkLaw
        (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex) ∪
          (lemma411412AuxThetaEvent thetaTarget m i r
              (alphaValue alphaIndex) ∪
            (lemma411412CardinalityFailureEvent m i r \
              thetaTarget m i r))) :=
        measure_mono
          (lemma411412FailureEvent_subset_prop45_union_auxTheta_union_cardinalityDiff
            sourceCanonicalProfiles canonicalCStar thetaTarget m i r
              (alphaValue alphaIndex))
    _ ≤ simpleRandomWalkLaw
          (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex)) +
        simpleRandomWalkLaw
          (lemma411412AuxThetaEvent thetaTarget m i r
              (alphaValue alphaIndex) ∪
            (lemma411412CardinalityFailureEvent m i r \
              thetaTarget m i r)) := measure_union_le _ _
    _ ≤ simpleRandomWalkLaw
          (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex)) +
        (simpleRandomWalkLaw
            (lemma411412AuxThetaEvent thetaTarget m i r
              (alphaValue alphaIndex)) +
          simpleRandomWalkLaw
            (lemma411412CardinalityFailureEvent m i r \
              thetaTarget m i r)) := by
        gcongr
        exact measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
        (sourceExceptionalRateWithPrefactor m thetaCoeff kappa +
          sourceExceptionalRateWithPrefactor m 1 kappa) :=
      add_le_add (hProp45M i r alphaIndex halpha)
        (add_le_add (hAuxThetaM i r alphaIndex halpha) hcardDiff)
    _ = sourceExceptionalRateWithPrefactor m
        (prop45Coeff + thetaCoeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Deleted-path-switch closure with a separately paid auxiliary stopped
exception.  This is the source-faithful endpoint used after reflecting the
two reunited column phases to `Y'`. -/
theorem prop47Lemma411412Estimate_of_finiteBranchPathWitnessAuxThetaInputs
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set (ℕ → Site))
    (branchCount cWindow prop45Coeff thetaCoeff : ℕ)
    {c rhoCoeff : ℝ}
    (hc : 0 < c)
    (hrhoCoeff : 0 < rhoCoeff)
    (h : Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputs
      thetaTarget branchCount cWindow c rhoCoeff)
    (hProp45 : Prop47Prop45Estimate
      sourceCanonicalProfiles canonicalCStar prop45Coeff)
    (hAuxTheta : Prop47Lemma411412AuxThetaEstimate
      thetaTarget thetaCoeff) :
    Prop47Lemma411412Estimate (prop45Coeff + thetaCoeff + 1) := by
  have hcrho : 0 < c * rhoCoeff := mul_pos hc hrhoCoeff
  have habsorb := eventually_pathWitnessEquation447_error_absorb
    hc hrhoCoeff
  have hbranches := eventually_finiteBranch_profileRate_absorb
    branchCount hcrho
  have hrate := eventually_unshifted_half_logSquare_le_sourceExceptional
    (c := c * rhoCoeff / 2) (by positivity)
  filter_upwards [h, hProp45, hAuxTheta, habsorb, hbranches, hrate] with
      m hm hProp45M hAuxThetaM habsorbM hbranchesM hrateM
  intro i r alphaIndex halpha
  rcases hm i r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  have hcardDiff :
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \ thetaTarget m i r) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
    calc
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \ thetaTarget m i r) ≤
        (branchCount : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (-(c * rhoCoeff / 2) * Real.log (m : ℝ) ^ 2)) :=
        cardinalityFailure_measure_le_of_pathWitnessBranches
          branchFailure rho atoms (thetaTarget m i r)
          hcover hthreshold hatomCover htheta hdisjoint hc habsorbM
      _ ≤ ENNReal.ofReal
          (Real.exp (-(c * rhoCoeff / 4) * Real.log (m : ℝ) ^ 2)) :=
        hbranchesM
      _ ≤ sourceExceptionalRateWithPrefactor m 1 kappa := by
        convert hrateM using 1 <;> ring
  calc
    simpleRandomWalkLaw
        (lemma411412FailureEvent m i r (alphaValue alphaIndex)) ≤
      simpleRandomWalkLaw
        (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex) ∪
          (lemma411412AuxThetaEvent thetaTarget m i r
              (alphaValue alphaIndex) ∪
            (lemma411412CardinalityFailureEvent m i r \
              thetaTarget m i r))) :=
        measure_mono
          (lemma411412FailureEvent_subset_prop45_union_auxTheta_union_cardinalityDiff
            sourceCanonicalProfiles canonicalCStar thetaTarget m i r
              (alphaValue alphaIndex))
    _ ≤ simpleRandomWalkLaw
          (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex)) +
        simpleRandomWalkLaw
          (lemma411412AuxThetaEvent thetaTarget m i r
              (alphaValue alphaIndex) ∪
            (lemma411412CardinalityFailureEvent m i r \
              thetaTarget m i r)) := measure_union_le _ _
    _ ≤ simpleRandomWalkLaw
          (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex)) +
        (simpleRandomWalkLaw
            (lemma411412AuxThetaEvent thetaTarget m i r
              (alphaValue alphaIndex)) +
          simpleRandomWalkLaw
            (lemma411412CardinalityFailureEvent m i r \
              thetaTarget m i r)) := by
        gcongr
        exact measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
        (sourceExceptionalRateWithPrefactor m thetaCoeff kappa +
          sourceExceptionalRateWithPrefactor m 1 kappa) :=
      add_le_add (hProp45M i r alphaIndex halpha)
        (add_le_add (hAuxThetaM i r alphaIndex halpha) hcardDiff)
    _ = sourceExceptionalRateWithPrefactor m
        (prop45Coeff + thetaCoeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Source-faithful finite-branch estimate with an auxiliary stopped-atom
profile exception.  The canonical Proposition-4.5 event and the auxiliary
exception are each paid once; the categorical cardinality remainder costs
the final unit coefficient. -/
theorem prop47Lemma411412Estimate_of_finiteBranchAuxThetaInputs
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set (ℕ → Site))
    (branchCount cWindow prop45Coeff thetaCoeff : ℕ) {C rhoCoeff : ℝ}
    (hC : 0 < C)
    (hrhoCoeff : 0 < rhoCoeff)
    (h : Prop47Lemma411412FiniteBranchAuxThetaInputs
      thetaTarget branchCount cWindow C rhoCoeff)
    (hProp45 : Prop47Prop45Estimate
      sourceCanonicalProfiles canonicalCStar prop45Coeff)
    (hAuxTheta : Prop47Lemma411412AuxThetaEstimate
      thetaTarget thetaCoeff) :
    Prop47Lemma411412Estimate (prop45Coeff + thetaCoeff + 1) := by
  have hratio : 1 < (C + 1) / C := by
    rw [one_lt_div hC]
    linarith
  have hd : 0 < Real.log ((C + 1) / C) := Real.log_pos hratio
  have hdRho : 0 < Real.log ((C + 1) / C) * rhoCoeff :=
    mul_pos hd hrhoCoeff
  have habsorb := eventually_branchConditionalEquation447_error_absorb
    hC hrhoCoeff
  have hbranches := eventually_finiteBranch_profileRate_absorb
    branchCount hdRho
  have hrate := eventually_unshifted_half_logSquare_le_sourceExceptional
    (c := Real.log ((C + 1) / C) * rhoCoeff / 2) (by positivity)
  filter_upwards [h, hProp45, hAuxTheta, habsorb, hbranches, hrate] with
      m hm hProp45M hAuxThetaM habsorbM hbranchesM hrateM
  intro i r alphaIndex halpha
  rcases hm i r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  have hcardDiff :
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \ thetaTarget m i r) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
    calc
      simpleRandomWalkLaw
          (lemma411412CardinalityFailureEvent m i r \
            thetaTarget m i r) ≤
        (branchCount : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(Real.log ((C + 1) / C) * rhoCoeff / 2) *
            Real.log (m : ℝ) ^ 2)) :=
        cardinalityFailure_measure_le_of_finiteBranches branchFailure rho atoms
          (thetaTarget m i r) hcover hthreshold hatomCover htheta hdisjoint
          hC habsorbM
      _ ≤ ENNReal.ofReal
        (Real.exp
          (-(Real.log ((C + 1) / C) * rhoCoeff / 4) *
          Real.log (m : ℝ) ^ 2)) := hbranchesM
      _ ≤ sourceExceptionalRateWithPrefactor m 1 kappa := by
        convert hrateM using 1 <;> ring
  calc
    simpleRandomWalkLaw
        (lemma411412FailureEvent m i r (alphaValue alphaIndex)) ≤
      simpleRandomWalkLaw
        (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex) ∪
          (lemma411412AuxThetaEvent thetaTarget m i r
              (alphaValue alphaIndex) ∪
            (lemma411412CardinalityFailureEvent m i r \
              thetaTarget m i r))) :=
        measure_mono
          (lemma411412FailureEvent_subset_prop45_union_auxTheta_union_cardinalityDiff
            sourceCanonicalProfiles canonicalCStar thetaTarget m i r
              (alphaValue alphaIndex))
    _ ≤ simpleRandomWalkLaw
          (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex)) +
        simpleRandomWalkLaw
          (lemma411412AuxThetaEvent thetaTarget m i r
              (alphaValue alphaIndex) ∪
            (lemma411412CardinalityFailureEvent m i r \
              thetaTarget m i r)) := measure_union_le _ _
    _ ≤ simpleRandomWalkLaw
          (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m i r (alphaValue alphaIndex)) +
        (simpleRandomWalkLaw
            (lemma411412AuxThetaEvent thetaTarget m i r
              (alphaValue alphaIndex)) +
          simpleRandomWalkLaw
            (lemma411412CardinalityFailureEvent m i r \
              thetaTarget m i r)) := by
        gcongr
        exact measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
        (sourceExceptionalRateWithPrefactor m thetaCoeff kappa +
          sourceExceptionalRateWithPrefactor m 1 kappa) :=
      add_le_add (hProp45M i r alphaIndex halpha)
        (add_le_add (hAuxThetaM i r alphaIndex halpha) hcardDiff)
    _ = sourceExceptionalRateWithPrefactor m
        (prop45Coeff + thetaCoeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Four-branch specialization matching the two terminal parities crossed
with the tie-left/strict-right winner split. -/
theorem prop47Lemma411412Estimate_of_fourBranchStoppedProfileInputs
    (cWindow prop45Coeff : ℕ) {C rhoCoeff : ℝ}
    (hC : 0 < C)
    (hrhoCoeff : 0 < rhoCoeff)
    (h : Prop47Lemma411412FiniteBranchStoppedProfileInputs
      4 cWindow C rhoCoeff)
    (hProp45 : Prop47Prop45Estimate
      sourceCanonicalProfiles canonicalCStar prop45Coeff) :
    Prop47Lemma411412Estimate (prop45Coeff + 1) :=
  prop47Lemma411412Estimate_of_finiteBranchStoppedProfileInputs
    4 cWindow prop45Coeff hC hrhoCoeff h hProp45

#print axioms prop47Lemma411412Estimate_of_stoppedProfileInputs
#print axioms prop47Lemma411412Estimate_of_finiteBranchStoppedProfileInputs
#print axioms stoppedEquation447PathWitnessBranchAtom_local_bound
#print axioms stoppedEquation447ChangedPathBranch_bound
#print axioms prop47Lemma411412Estimate_of_finiteBranchPathWitnessInputs
#print axioms prop47Lemma411412Estimate_of_finiteBranchChangedPathInputs
#print axioms prop47Lemma411412Estimate_of_finiteBranchChangedPathAuxThetaInputs
#print axioms prop47Lemma411412Estimate_of_finiteBranchPathWitnessAuxThetaInputs
#print axioms prop47Lemma411412Estimate_of_fourBranchStoppedProfileInputs

end Erdos1166.HLOZProp47Lemma411412Connector
