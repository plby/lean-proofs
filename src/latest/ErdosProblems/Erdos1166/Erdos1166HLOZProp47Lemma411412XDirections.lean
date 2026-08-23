import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412XEastBridge
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Prop45XRotations

/-!
# Quarter-turn transport for the Lemmas 4.11--4.12 source atoms

The four stopping-parity/winner families are constructed literally for the
east checkerboard pairing.  This file transports the already constructed
branch-specific atoms through the origin-fixing quarter turns.  In
particular, a rotated atom retains its own failure event and source threshold;
no rotated branch is asked to imply the unsplit cardinality overflow.
-/

namespace Erdos1166.HLOZProp47Lemma411412XDirections

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

open HLOZPairing HLOZPairingProfiles HLOZProp47SourceObjects
open HLOZProp47SourceAssembly
open HLOZProp47Canonical
open HLOZProp47Prop45XRotations
open HLOZProp47Lemma411412Connector
open HLOZProp47Lemma411412XEastBridge
open HLOZBandRatios

abbrev Path := ℕ → Site

/-- The inverse quarter turn. -/
def rotationInverseDir (d : Dir) : Dir :=
  match d.1 with
  | 0 => east
  | 1 => south
  | 2 => west
  | _ => north

@[simp] theorem orientSite_rotationInverseDir_left (d : Dir) (x : Site) :
    orientSite (rotationInverseDir d) (orientSite d x) = x := by
  rcases x with ⟨x₁, x₂⟩
  fin_cases d <;> simp [rotationInverseDir, orientSite, east, north, west, south]

@[simp] theorem orientSite_rotationInverseDir_right (d : Dir) (x : Site) :
    orientSite d (orientSite (rotationInverseDir d) x) = x := by
  rcases x with ⟨x₁, x₂⟩
  fin_cases d <;> simp [rotationInverseDir, orientSite, east, north, west, south]

@[simp] theorem orientPath_rotationInverseDir_left (d : Dir) (s : Path) :
    orientPath (rotationInverseDir d) (orientPath d s) = s := by
  funext n
  exact orientSite_rotationInverseDir_left d (s n)

@[simp] theorem orientPath_rotationInverseDir_right (d : Dir) (s : Path) :
    orientPath d (orientPath (rotationInverseDir d) s) = s := by
  funext n
  exact orientSite_rotationInverseDir_right d (s n)

/-- Quarter turns preserve the range of the increment-to-path map. -/
theorem orientPath_mem_simpleRandomWalkSupport
    (d : Dir) {s : Path}
    (hs : s ∈ HLOZSourceInstantiation.simpleRandomWalkSupport) :
    orientPath d s ∈ HLOZSourceInstantiation.simpleRandomWalkSupport := by
  rcases hs with ⟨omega, rfl⟩
  refine ⟨orientIncrements d omega, ?_⟩
  funext n
  exact simpleRandomWalk_orientIncrements d omega n

/-- The vertical reflection also preserves genuine simple-walk paths. -/
theorem reflectPath_mem_simpleRandomWalkSupport
    {s : Path}
    (hs : s ∈ HLOZSourceInstantiation.simpleRandomWalkSupport) :
    reflectPath s ∈ HLOZSourceInstantiation.simpleRandomWalkSupport := by
  rcases hs with ⟨omega, rfl⟩
  refine ⟨reflectIncrements omega, ?_⟩
  funext n
  exact simpleRandomWalk_reflectIncrements omega n

theorem distinguishedEndpoint_xIndex (d : Dir) (x : Site) :
    distinguishedEndpoint (xIndex d) x =
      if chessEven x then x else shift x (vec (oppositeDir d)) := by
  classical
  fin_cases d <;>
    simp [distinguishedEndpoint, xIndex, oppositeDir, east, north, west, south]

theorem orientSite_shift_west (d : Dir) (x : Site) :
    orientSite d (shift x (vec west)) =
      shift (orientSite d x) (vec (oppositeDir d)) := by
  rcases x with ⟨x₁, x₂⟩
  fin_cases d <;>
    simp [orientSite, shift, vec, oppositeDir, east, north, west, south,
      add_comm]

theorem distinguishedEndpoint_x_orient (d : Dir) (x : Site) :
    distinguishedEndpoint (xIndex d) (orientSite d x) =
      orientSite d (distinguishedEndpoint (xIndex east) x) := by
  rw [distinguishedEndpoint_xIndex, distinguishedEndpoint_xIndex]
  rw [chessEven_orientSite]
  by_cases hx : chessEven x
  · simp [hx]
  · simp only [hx, if_false]
    simpa only [oppositeDir, east, west] using
      (orientSite_shift_west d x).symm

theorem creationDominoEndpoints_x_orient
    (d : Dir) (s : Path) (m k : ℕ) :
    creationDominoEndpoints (xIndex d) (orientPath d s) m k =
      (creationDominoEndpoints (xIndex east) s m k).image (orientSite d) := by
  unfold creationDominoEndpoints
  rw [Finset.image_image]
  apply Finset.image_congr
  intro j hj
  change distinguishedEndpoint (xIndex d)
      (levelCreationSite (orientPath d s) m j) =
    orientSite d (distinguishedEndpoint (xIndex east)
      (levelCreationSite s m j))
  rw [levelCreationSite_orientPath, distinguishedEndpoint_x_orient]

theorem nearFavoriteSites_x_orient
    (d : Dir) (s : Path) (m k : ℕ) (alpha : ℝ) :
    nearFavoriteSites (xIndex d) (orientPath d s) m k alpha =
      (nearFavoriteSites (xIndex east) s m k alpha).image (orientSite d) := by
  classical
  unfold nearFavoriteSites
  rw [visitedSites_orientPath, directCreationTime_orientPath,
    firstKSitesReachLevel_orientPath, creationDominoEndpoints_x_orient]
  ext y
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hxVisited, rfl⟩, hfinite, houtside, hlower, hupper⟩
    refine ⟨x, ⟨hxVisited, hfinite, ?_, ?_, ?_⟩, rfl⟩
    · intro hcreated
      apply houtside
      rw [distinguishedEndpoint_x_orient]
      exact ⟨distinguishedEndpoint (xIndex east) x, hcreated, rfl⟩
    · simpa only [localTime_orientPath] using hlower
    · simpa only [localTime_orientPath] using hupper
  · rintro ⟨x, ⟨hxVisited, hfinite, houtside, hlower, hupper⟩, rfl⟩
    refine ⟨⟨x, hxVisited, rfl⟩, hfinite, ?_, ?_, ?_⟩
    · intro hcreated
      rcases hcreated with ⟨z, hz, hEq⟩
      apply houtside
      have hEq' : distinguishedEndpoint (xIndex east) x = z := by
        apply orientSite_injective d
        rw [distinguishedEndpoint_x_orient] at hEq
        exact hEq.symm
      exact hEq' ▸ hz
    · simpa only [localTime_orientPath] using hlower
    · simpa only [localTime_orientPath] using hupper

theorem nearFavoriteSites_x_orient_card
    (d : Dir) (s : Path) (m k : ℕ) (alpha : ℝ) :
    (nearFavoriteSites (xIndex d) (orientPath d s) m k alpha).card =
      (nearFavoriteSites (xIndex east) s m k alpha).card := by
  rw [nearFavoriteSites_x_orient]
  exact Finset.card_image_of_injective _ (orientSite_injective d)

theorem lemma411412CardinalityFailureEvent_x_orient_iff
    (d : Dir) (s : Path) (m : ℕ) (r : StageIndex) :
    s ∈ lemma411412CardinalityFailureEvent m (xIndex east) r ↔
      orientPath d s ∈ lemma411412CardinalityFailureEvent m (xIndex d) r := by
  constructor
  · rintro ⟨hprefix, hcard⟩
    refine ⟨(prefixPairingEvent_x_orient_iff d s m _).mp hprefix, ?_⟩
    change Real.log (m : ℝ) ^ 2 <
      (nearFavoriteSites (xIndex east) s m (stageNumber r)
        HLOZProp47Parameters.kappaOne).card at hcard
    change Real.log (m : ℝ) ^ 2 <
      (nearFavoriteSites (xIndex d) (orientPath d s) m (stageNumber r)
        HLOZProp47Parameters.kappaOne).card
    rwa [nearFavoriteSites_x_orient_card]
  · rintro ⟨hprefix, hcard⟩
    refine ⟨(prefixPairingEvent_x_orient_iff d s m _).mpr hprefix, ?_⟩
    change Real.log (m : ℝ) ^ 2 <
      (nearFavoriteSites (xIndex d) (orientPath d s) m (stageNumber r)
        HLOZProp47Parameters.kappaOne).card at hcard
    change Real.log (m : ℝ) ^ 2 <
      (nearFavoriteSites (xIndex east) s m (stageNumber r)
        HLOZProp47Parameters.kappaOne).card
    rwa [nearFavoriteSites_x_orient_card] at hcard

theorem lemma411412CardinalityFailureEvent_x_preimage_inverse
    (d : Dir) (m : ℕ) (r : StageIndex) :
    orientPath (rotationInverseDir d) ⁻¹'
        lemma411412CardinalityFailureEvent m (xIndex east) r =
      lemma411412CardinalityFailureEvent m (xIndex d) r := by
  ext s
  change orientPath (rotationInverseDir d) s ∈
      lemma411412CardinalityFailureEvent m (xIndex east) r ↔ _
  rw [lemma411412CardinalityFailureEvent_x_orient_iff d]
  simp only [orientPath_rotationInverseDir_right]

private theorem map_restrict_preimage_comp_of_map_eq
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (mu : Measure Ω) (f : Ω → Ω) (g : Ω → Z)
    (hf : Measurable f) (hg : Measurable g)
    (hmap : mu.map f = mu) {S : Set Ω} (hS : MeasurableSet S) :
    (mu.restrict (f ⁻¹' S)).map (g ∘ f) =
      (mu.restrict S).map g := by
  ext E hE
  rw [Measure.map_apply (hg.comp hf) hE,
    Measure.restrict_apply' (hS.preimage hf),
    Measure.map_apply hg hE, Measure.restrict_apply' hS]
  have hset :
      (g ∘ f) ⁻¹' E ∩ f ⁻¹' S =
        f ⁻¹' (g ⁻¹' E ∩ S) := by
    ext omega
    rfl
  rw [hset, ← Measure.map_apply hf ((hE.preimage hg).inter hS), hmap]

private theorem measure_preimage_eq_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (f : Ω → Ω) (hf : Measurable f)
    (hmap : mu.map f = mu) {S : Set Ω} (hS : MeasurableSet S) :
    mu (f ⁻¹' S) = mu S := by
  calc
    mu (f ⁻¹' S) = (mu.map f) S := (Measure.map_apply hf hS).symm
    _ = mu S := by rw [hmap]

/-- Transport one complete branch atom.  The finite coordinate law and every
equation-(4.47) categorical object are unchanged; only the path-space atom,
failure event, and path statistics are pulled back by the inverse quarter
turn. -/
noncomputable def rotateBranchAtom
    (d : Dir) {cWindow m : ℕ} {C rho : ℝ}
    {failure : Set Path}
    (A : StoppedEquation447BranchAtom
      cWindow m C failure rho) :
    StoppedEquation447BranchAtom cWindow m C
      (orientPath (rotationInverseDir d) ⁻¹' failure) rho where
  Coord := A.Coord
  coordFintype := A.coordFintype
  pathAtom := orientPath (rotationInverseDir d) ⁻¹' A.pathAtom
  measurableSet_pathAtom :=
    A.measurableSet_pathAtom.preimage
      (measurable_orientPath (rotationInverseDir d))
  profile := A.profile
  profile_lt := A.profile_lt
  lazyVector := fun s ↦ A.lazyVector (orientPath (rotationInverseDir d) s)
  measurable_lazyVector := A.measurable_lazyVector.comp
    (measurable_orientPath (rotationInverseDir d))
  nextDirection := fun s ↦
    A.nextDirection (orientPath (rotationInverseDir d) s)
  measurable_nextDirection := A.measurable_nextDirection.comp
    (measurable_orientPath (rotationInverseDir d))
  forcedDirection := A.forcedDirection
  D := A.D
  badAtom := A.badAtom
  historyAtom := A.historyAtom
  category := A.category
  categoryLaw := A.categoryLaw
  categoryLaw_probability := A.categoryLaw_probability
  map_law := by
    let g := orientPath (rotationInverseDir d)
    have hg : Measurable g := measurable_orientPath (rotationInverseDir d)
    have hmap : simpleRandomWalkLaw.map g = simpleRandomWalkLaw :=
      simpleRandomWalkLaw_map_orientPath (rotationInverseDir d)
    have htransport := map_restrict_preimage_comp_of_map_eq
      simpleRandomWalkLaw g
      (fun s ↦ (A.lazyVector s, A.nextDirection s)) hg
      (A.measurable_lazyVector.prodMk A.measurable_nextDirection)
      hmap A.measurableSet_pathAtom
    have hmass := measure_preimage_eq_of_map_eq
      simpleRandomWalkLaw g hg hmap A.measurableSet_pathAtom
    change (simpleRandomWalkLaw.restrict (g ⁻¹' A.pathAtom)).map
        ((fun s ↦ (A.lazyVector s, A.nextDirection s)) ∘ g) = _
    rw [htransport, A.map_law, hmass]
  failure_subset := by
    intro s hs
    exact A.failure_subset hs
  thetaPathEvent := orientPath (rotationInverseDir d) ⁻¹' A.thetaPathEvent
  theta_preimage_subset := by
    intro s hs
    exact A.theta_preimage_subset hs
  equation447_cover := A.equation447_cover
  bad_subset_history_allUpper := A.bad_subset_history_allUpper
  conditional_category_product := A.conditional_category_product
  category_mass_ratio := A.category_mass_ratio
  history_disjoint := A.history_disjoint
  history_measurable := A.history_measurable

/-- Quarter-turn transport for the literal deleted-path switch.  The
fixed-cardinality bad and witness cells live in profile space and are left
unchanged; only path-space events and observations are pulled back. -/
noncomputable def rotatePathWitnessBranchAtom
    (d : Dir) {cWindow m : ℕ} {c rho : ℝ}
    {failure : Set Path}
    (A : StoppedEquation447PathWitnessBranchAtom
      cWindow m c failure rho) :
    StoppedEquation447PathWitnessBranchAtom cWindow m c
      (orientPath (rotationInverseDir d) ⁻¹' failure) rho where
  Coord := A.Coord
  coordFintype := A.coordFintype
  Path := A.Path
  pathCountable := A.pathCountable
  pathAtom := orientPath (rotationInverseDir d) ⁻¹' A.pathAtom
  measurableSet_pathAtom :=
    A.measurableSet_pathAtom.preimage
      (measurable_orientPath (rotationInverseDir d))
  profile := A.profile
  profile_lt := A.profile_lt
  lazyVector := fun s ↦ A.lazyVector (orientPath (rotationInverseDir d) s)
  measurable_lazyVector := A.measurable_lazyVector.comp
    (measurable_orientPath (rotationInverseDir d))
  nextDirection := fun s ↦
    A.nextDirection (orientPath (rotationInverseDir d) s)
  measurable_nextDirection := A.measurable_nextDirection.comp
    (measurable_orientPath (rotationInverseDir d))
  forcedDirection := A.forcedDirection
  D := A.D
  badAtom := A.badAtom
  witnessAtom := A.witnessAtom
  map_law := by
    let g := orientPath (rotationInverseDir d)
    have hg : Measurable g := measurable_orientPath (rotationInverseDir d)
    have hmap : simpleRandomWalkLaw.map g = simpleRandomWalkLaw :=
      simpleRandomWalkLaw_map_orientPath (rotationInverseDir d)
    have htransport := map_restrict_preimage_comp_of_map_eq
      simpleRandomWalkLaw g
      (fun s ↦ (A.lazyVector s, A.nextDirection s)) hg
      (A.measurable_lazyVector.prodMk A.measurable_nextDirection)
      hmap A.measurableSet_pathAtom
    have hmass := measure_preimage_eq_of_map_eq
      simpleRandomWalkLaw g hg hmap A.measurableSet_pathAtom
    change (simpleRandomWalkLaw.restrict (g ⁻¹' A.pathAtom)).map
        ((fun s ↦ (A.lazyVector s, A.nextDirection s)) ∘ g) = _
    rw [htransport, A.map_law, hmass]
  failure_subset := by
    intro s hs
    exact A.failure_subset hs
  thetaPathEvent := orientPath (rotationInverseDir d) ⁻¹' A.thetaPathEvent
  theta_preimage_subset := by
    intro s hs
    exact A.theta_preimage_subset hs
  equation447_cover := A.equation447_cover
  path_switch := A.path_switch
  witness_disjoint := A.witness_disjoint
  witness_measurable := A.witness_measurable

/-- A complete branch-specific X-east atomization rotates to any one of the
four checkerboard pairings. -/
theorem finiteBranchStoppedProfileInputsAt_x_of_east
    (d : Dir) (branchCount cWindow : ℕ)
    (C rhoCoeff : ℝ)
    (h : Prop47Lemma411412FiniteBranchStoppedProfileInputsAt
      (xIndex east) branchCount cWindow C rhoCoeff) :
    Prop47Lemma411412FiniteBranchStoppedProfileInputsAt
      (xIndex d) branchCount cWindow C rhoCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  let g := orientPath (rotationInverseDir d)
  let rotatedFailure : Fin branchCount → Set Path :=
    fun j ↦ g ⁻¹' branchFailure j
  let rotatedAtoms : (j : Fin branchCount) → ℕ →
      StoppedEquation447BranchAtom cWindow m C
        (rotatedFailure j) (rho j) :=
    fun j eta ↦ rotateBranchAtom d (atoms j eta)
  refine ⟨rotatedFailure, rho, rotatedAtoms, ?_, hthreshold, ?_, ?_, ?_⟩
  · intro s hs
    have hsource : g s ∈
        lemma411412CardinalityFailureEvent m (xIndex east) r := by
      apply (lemma411412CardinalityFailureEvent_x_orient_iff d (g s) m r).mpr
      simpa only [g, orientPath_rotationInverseDir_right] using hs
    rcases Set.mem_iUnion.mp (hcover hsource) with ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  · intro j s hs
    rcases Set.mem_iUnion.mp (hatomCover j hs) with ⟨eta, heta⟩
    exact Set.mem_iUnion.mpr ⟨eta, heta⟩
  · intro j eta s hs
    have hold := htheta j eta hs
    have hrot := (stoppedThetaEvent_x_orient_iff d
      (canonicalCStar (xIndex east)) (g s) m (stageNumber r)).mp hold
    have hrot' : s ∈ stoppedThetaEvent (deletionProfilePair (xDeletion d))
        (canonicalCStar (xIndex east)) m (stageNumber r) := by
      simpa only [g, orientPath_rotationInverseDir_right] using hrot
    have hprofile : sourceCanonicalProfiles (xIndex d) =
        deletionProfilePair (xDeletion d) := by
      simpa only [xIndex, canonicalProfiles, pairingProfiles,
        pairingDeletion_x] using sourceCanonicalProfiles_x d
    rw [hprofile]
    simpa only [canonicalCStar] using hrot'
  · intro j eta zeta hne
    rw [Set.disjoint_left]
    intro s hsEta hsZeta
    exact Set.disjoint_left.1 (hdisjoint j hne) hsEta hsZeta

/-- A complete path-witness atomization at X-east rotates to every
checkerboard pairing without changing its exponential switch constant. -/
theorem finiteBranchPathWitnessInputsAt_x_of_east
    (d : Dir) (branchCount cWindow : ℕ)
    (c rhoCoeff : ℝ)
    (h : Prop47Lemma411412FiniteBranchPathWitnessInputsAt
      (xIndex east) branchCount cWindow c rhoCoeff) :
    Prop47Lemma411412FiniteBranchPathWitnessInputsAt
      (xIndex d) branchCount cWindow c rhoCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  let g := orientPath (rotationInverseDir d)
  let rotatedFailure : Fin branchCount → Set Path :=
    fun j ↦ g ⁻¹' branchFailure j
  let rotatedAtoms : (j : Fin branchCount) → ℕ →
      StoppedEquation447PathWitnessBranchAtom cWindow m c
        (rotatedFailure j) (rho j) :=
    fun j eta ↦ rotatePathWitnessBranchAtom d (atoms j eta)
  refine ⟨rotatedFailure, rho, rotatedAtoms, ?_, hthreshold, ?_, ?_, ?_⟩
  · intro s hs
    have hsource : g s ∈
        lemma411412CardinalityFailureEvent m (xIndex east) r := by
      apply (lemma411412CardinalityFailureEvent_x_orient_iff d (g s) m r).mpr
      simpa only [g, orientPath_rotationInverseDir_right] using hs
    rcases Set.mem_iUnion.mp (hcover hsource) with ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  · intro j s hs
    have hsourceSupport : g s ∈
        HLOZSourceInstantiation.simpleRandomWalkSupport := by
      change orientPath (rotationInverseDir d) s ∈
        HLOZSourceInstantiation.simpleRandomWalkSupport
      exact orientPath_mem_simpleRandomWalkSupport
        (rotationInverseDir d) hs.2
    rcases Set.mem_iUnion.mp
      (hatomCover j ⟨hs.1, hsourceSupport⟩) with ⟨eta, heta⟩
    exact Set.mem_iUnion.mpr ⟨eta, heta⟩
  · intro j eta s hs
    have hold := htheta j eta hs
    have hrot := (stoppedThetaEvent_x_orient_iff d
      (canonicalCStar (xIndex east)) (g s) m (stageNumber r)).mp hold
    have hrot' : s ∈ stoppedThetaEvent (deletionProfilePair (xDeletion d))
        (canonicalCStar (xIndex east)) m (stageNumber r) := by
      simpa only [g, orientPath_rotationInverseDir_right] using hrot
    have hprofile : sourceCanonicalProfiles (xIndex d) =
        deletionProfilePair (xDeletion d) := by
      simpa only [xIndex, canonicalProfiles, pairingProfiles,
        pairingDeletion_x] using sourceCanonicalProfiles_x d
    rw [hprofile]
    simpa only [canonicalCStar] using hrot'
  · intro j eta zeta hne
    rw [Set.disjoint_left]
    intro s hsEta hsZeta
    exact Set.disjoint_left.1 (hdisjoint j hne) hsEta hsZeta

/-- The literal four-family X-east source data supplies all four rotated
checkerboard pairing inputs. -/
theorem finiteBranchStoppedProfileInputsAt_x_of_source
    (d : Dir) (cWindow : ℕ)
    (rhoCoeff : ℝ)
    (h : Prop47Lemma411412XEastFourBranchSourceInputs
      cWindow rhoCoeff) :
    Prop47Lemma411412FiniteBranchStoppedProfileInputsAt
      (xIndex d) 4 cWindow
        (Real.exp (sourceAdjacentComparisonExponent cWindow)) rhoCoeff :=
  finiteBranchStoppedProfileInputsAt_x_of_east d 4 cWindow
    (Real.exp (sourceAdjacentComparisonExponent cWindow)) rhoCoeff
    (finiteBranchStoppedProfileInputsAt_xEast_of_source
      cWindow rhoCoeff h)

/-- The canonical four-family X-east deleted-path-switch package supplies
all four checkerboard pairings. -/
theorem finiteBranchPathWitnessInputsAt_x_of_source
    (d : Dir) (cWindow : ℕ) (c : ℝ)
    (h : Prop47Lemma411412XEastCanonicalFourBranchPathWitnessSourceInputs
      cWindow c) :
    Prop47Lemma411412FiniteBranchPathWitnessInputsAt
      (xIndex d) 4 cWindow c (1 / 4 : ℝ) :=
  finiteBranchPathWitnessInputsAt_x_of_east d 4 cWindow c (1 / 4 : ℝ)
    (finiteBranchPathWitnessInputsAt_xEast_of_source cWindow c h)

/-! ### A common four-branch arity for the X and Y source families -/

private def duplicateTwoBranchIndex : Fin 4 → Fin 2 := ![0, 1, 0, 1]

private def includeTwoBranchIndex (j : Fin 2) : Fin 4 :=
  ⟨j.1, lt_trans j.2 (by omega)⟩

@[simp] private theorem duplicateTwoBranchIndex_include (j : Fin 2) :
    duplicateTwoBranchIndex (includeTwoBranchIndex j) = j := by
  fin_cases j <;> rfl

/-- Duplicating the two families does not assert any cross-branch
disjointness.  It merely gives the two column phases the same `Fin 4` arity as
the four X stopping-parity families, at the harmless cost already covered by
the finite union bound. -/
theorem finiteBranchStoppedProfileInputsAt_four_of_two
    (i : Fin 6) (cWindow : ℕ) (C rhoCoeff : ℝ)
    (h : Prop47Lemma411412FiniteBranchStoppedProfileInputsAt
      i 2 cWindow C rhoCoeff) :
    Prop47Lemma411412FiniteBranchStoppedProfileInputsAt
      i 4 cWindow C rhoCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  let branchFailure4 : Fin 4 → Set Path :=
    fun j ↦ branchFailure (duplicateTwoBranchIndex j)
  let rho4 : Fin 4 → ℝ := fun j ↦ rho (duplicateTwoBranchIndex j)
  let atoms4 : (j : Fin 4) → ℕ →
      StoppedEquation447BranchAtom cWindow m C
        (branchFailure4 j) (rho4 j) :=
    fun j eta ↦ atoms (duplicateTwoBranchIndex j) eta
  refine ⟨branchFailure4, rho4, atoms4, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases Set.mem_iUnion.mp (hcover hs) with ⟨j, hj⟩
    refine Set.mem_iUnion.mpr ⟨includeTwoBranchIndex j, ?_⟩
    change s ∈ branchFailure (duplicateTwoBranchIndex (includeTwoBranchIndex j))
    simpa only [duplicateTwoBranchIndex_include]
  · intro j
    exact hthreshold (duplicateTwoBranchIndex j)
  · intro j
    exact hatomCover (duplicateTwoBranchIndex j)
  · intro j eta
    exact htheta (duplicateTwoBranchIndex j) eta
  · intro j
    exact hdisjoint (duplicateTwoBranchIndex j)

/-- The same harmless arity padding for deleted-path-switch atoms. -/
theorem finiteBranchPathWitnessInputsAt_four_of_two
    (i : Fin 6) (cWindow : ℕ) (c rhoCoeff : ℝ)
    (h : Prop47Lemma411412FiniteBranchPathWitnessInputsAt
      i 2 cWindow c rhoCoeff) :
    Prop47Lemma411412FiniteBranchPathWitnessInputsAt
      i 4 cWindow c rhoCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  let branchFailure4 : Fin 4 → Set Path :=
    fun j ↦ branchFailure (duplicateTwoBranchIndex j)
  let rho4 : Fin 4 → ℝ := fun j ↦ rho (duplicateTwoBranchIndex j)
  let atoms4 : (j : Fin 4) → ℕ →
      StoppedEquation447PathWitnessBranchAtom cWindow m c
        (branchFailure4 j) (rho4 j) :=
    fun j eta ↦ atoms (duplicateTwoBranchIndex j) eta
  refine ⟨branchFailure4, rho4, atoms4, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases Set.mem_iUnion.mp (hcover hs) with ⟨j, hj⟩
    refine Set.mem_iUnion.mpr ⟨includeTwoBranchIndex j, ?_⟩
    change s ∈ branchFailure (duplicateTwoBranchIndex (includeTwoBranchIndex j))
    simpa only [duplicateTwoBranchIndex_include]
  · intro j
    exact hthreshold (duplicateTwoBranchIndex j)
  · intro j
    exact hatomCover (duplicateTwoBranchIndex j)
  · intro j eta
    exact htheta (duplicateTwoBranchIndex j) eta
  · intro j
    exact hdisjoint (duplicateTwoBranchIndex j)

/-- Arity padding for the flexible-theta deleted-path-switch interface. -/
theorem finiteBranchPathWitnessAuxThetaInputsAt_four_of_two
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set Path)
    (i : Fin 6) (cWindow : ℕ) (c rhoCoeff : ℝ)
    (h : Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputsAt
      thetaTarget i 2 cWindow c rhoCoeff) :
    Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputsAt
      thetaTarget i 4 cWindow c rhoCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  let branchFailure4 : Fin 4 → Set Path :=
    fun j ↦ branchFailure (duplicateTwoBranchIndex j)
  let rho4 : Fin 4 → ℝ := fun j ↦ rho (duplicateTwoBranchIndex j)
  let atoms4 : (j : Fin 4) → ℕ →
      StoppedEquation447PathWitnessBranchAtom cWindow m c
        (branchFailure4 j) (rho4 j) :=
    fun j eta ↦ atoms (duplicateTwoBranchIndex j) eta
  refine ⟨branchFailure4, rho4, atoms4, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases Set.mem_iUnion.mp (hcover hs) with ⟨j, hj⟩
    refine Set.mem_iUnion.mpr ⟨includeTwoBranchIndex j, ?_⟩
    change s ∈ branchFailure (duplicateTwoBranchIndex (includeTwoBranchIndex j))
    simpa only [duplicateTwoBranchIndex_include]
  · intro j
    exact hthreshold (duplicateTwoBranchIndex j)
  · intro j
    exact hatomCover (duplicateTwoBranchIndex j)
  · intro j eta
    exact htheta (duplicateTwoBranchIndex j) eta
  · intro j
    exact hdisjoint (duplicateTwoBranchIndex j)

/-- The same harmless branch duplication for the flexible auxiliary-theta
interface. -/
theorem finiteBranchAuxThetaInputsAt_four_of_two
    (thetaTarget : ℕ → Fin 6 → StageIndex → Set Path)
    (i : Fin 6) (cWindow : ℕ) (C rhoCoeff : ℝ)
    (h : Prop47Lemma411412FiniteBranchAuxThetaInputsAt
      thetaTarget i 2 cWindow C rhoCoeff) :
    Prop47Lemma411412FiniteBranchAuxThetaInputsAt
      thetaTarget i 4 cWindow C rhoCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with
    ⟨branchFailure, rho, atoms, hcover, hthreshold, hatomCover, htheta,
      hdisjoint⟩
  let branchFailure4 : Fin 4 → Set Path :=
    fun j ↦ branchFailure (duplicateTwoBranchIndex j)
  let rho4 : Fin 4 → ℝ := fun j ↦ rho (duplicateTwoBranchIndex j)
  let atoms4 : (j : Fin 4) → ℕ →
      StoppedEquation447BranchAtom cWindow m C
        (branchFailure4 j) (rho4 j) :=
    fun j eta ↦ atoms (duplicateTwoBranchIndex j) eta
  refine ⟨branchFailure4, rho4, atoms4, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases Set.mem_iUnion.mp (hcover hs) with ⟨j, hj⟩
    refine Set.mem_iUnion.mpr ⟨includeTwoBranchIndex j, ?_⟩
    change s ∈ branchFailure (duplicateTwoBranchIndex (includeTwoBranchIndex j))
    simpa only [duplicateTwoBranchIndex_include]
  · intro j
    exact hthreshold (duplicateTwoBranchIndex j)
  · intro j
    exact hatomCover (duplicateTwoBranchIndex j)
  · intro j eta
    exact htheta (duplicateTwoBranchIndex j) eta
  · intro j
    exact hdisjoint (duplicateTwoBranchIndex j)

end Erdos1166.HLOZProp47Lemma411412XDirections
