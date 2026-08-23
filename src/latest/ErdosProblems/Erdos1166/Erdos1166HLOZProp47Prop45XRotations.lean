/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Prop45XEastPrimed

/-!
# Rotation transport for the four `X_j` cases of HLOZ Proposition 4.5

The unprimed and primed `X₁` estimates are assembled on their own finite
external-path atomizations in `HLOZProp47Prop45XEastPrimed`.  This file does
not rotate those atoms.  Instead it rotates the already assembled full
stopped event, containing both deletion phases, under a measure-preserving
quarter turn of the original walk.
-/

namespace Erdos1166.HLOZProp47Prop45XRotations

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open HLOZProp47SourceObjects HLOZProp47SourceAssembly
open HLOZProp47Canonical HLOZPairingProfiles HLOZPairing
open HLOZPairing.ScreeningBridge
open HLOZProp47Parameters
open HLOZProp45SourceAbsorption
open HLOZProp47Prop45XEastPrimed

abbrev Path := ℕ → Site

theorem localTime_orientPath (d : Dir) (s : Path) (n : ℕ) (x : Site) :
    localTime (orientPath d s) n (orientSite d x) = localTime s n x := by
  unfold localTime orientPath
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ ↦ (orientSite_injective d).eq_iff

theorem visitedSites_orientPath (d : Dir) (s : Path) (n : ℕ) :
    visitedSites (orientPath d s) n =
      (visitedSites s n).image (orientSite d) := by
  unfold visitedSites orientPath
  rw [Finset.image_image]
  rfl

theorem sitesAtLeastLevel_orientPath (d : Dir) (s : Path) (n m : ℕ) :
    sitesAtLeastLevel (orientPath d s) n m =
      (sitesAtLeastLevel s n m).image (orientSite d) := by
  ext y
  rw [sitesAtLeastLevel, sitesAtLeastLevel, visitedSites_orientPath]
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hm⟩
    exact ⟨x, ⟨hx, by simpa only [localTime_orientPath] using hm⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hm⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by simpa only [localTime_orientPath] using hm⟩

theorem card_sitesAtLeastLevel_orientPath
    (d : Dir) (s : Path) (n m : ℕ) :
    (sitesAtLeastLevel (orientPath d s) n m).card =
      (sitesAtLeastLevel s n m).card := by
  rw [sitesAtLeastLevel_orientPath]
  exact Finset.card_image_of_injective _ (orientSite_injective d)

theorem firstKSitesReachLevel_orientPath
    (d : Dir) (s : Path) (m k : ℕ) :
    firstKSitesReachLevel m k (orientPath d s) =
      firstKSitesReachLevel m k s := by
  have heq (j : ℕ) :
      (sitesAtLeastLevel (orientPath d s) j m).card =
        (sitesAtLeastLevel s j m).card :=
    card_sitesAtLeastLevel_orientPath d s j m
  unfold firstKSitesReachLevel hittingAfter
  by_cases h : ∃ j, 0 ≤ j ∧ (sitesAtLeastLevel s j m).card ∈ Set.Ici k
  · have hd : ∃ j, 0 ≤ j ∧
        (sitesAtLeastLevel (orientPath d s) j m).card ∈ Set.Ici k := by
      simpa only [heq] using h
    simp only [hd, h, if_true, heq]
  · have hd : ¬ ∃ j, 0 ≤ j ∧
        (sitesAtLeastLevel (orientPath d s) j m).card ∈ Set.Ici k := by
      simpa only [heq] using h
    simp only [hd, h, if_false]

theorem directCreationTime_orientPath
    (d : Dir) (s : Path) (m k : ℕ) :
    directCreationTime m k (orientPath d s) = directCreationTime m k s := by
  unfold directCreationTime
  rw [firstKSitesReachLevel_orientPath]

theorem levelCreationSite_orientPath
    (d : Dir) (s : Path) (m k : ℕ) :
    levelCreationSite (orientPath d s) m k =
      orientSite d (levelCreationSite s m k) := by
  unfold levelCreationSite orientPath
  congr 2
  exact congrArg WithTop.untopA
    (firstKSitesReachLevel_orientPath d s m k)

theorem levelCreationSitesUpTo_orientPath
    (d : Dir) (s : Path) (m k : ℕ) :
    levelCreationSitesUpTo (orientPath d s) m k =
      (levelCreationSitesUpTo s m k).image (orientSite d) := by
  rw [levelCreationSitesUpTo, levelCreationSitesUpTo, Finset.image_image]
  apply Finset.image_congr
  intro j hj
  exact levelCreationSite_orientPath d s m j

theorem orientSite_shift_east (d : Dir) (x : Site) :
    orientSite d (shift x (vec east)) =
      shift (orientSite d x) (vec d) := by
  change orientSite d (x + vec east) = orientSite d x + vec d
  rw [orientSite_add, orientSite_east]

theorem XPair_orientSite_iff (d : Dir) (x y : Site) :
    XPair d (orientSite d x) (orientSite d y) ↔ XPair east x y := by
  constructor
  · rintro (⟨hx, hxy⟩ | ⟨hy, hyx⟩)
    · refine Or.inl ⟨(chessEven_orientSite d x).mp hx, ?_⟩
      apply orientSite_injective d
      rw [orientSite_shift_east]
      exact hxy
    · refine Or.inr ⟨(chessEven_orientSite d y).mp hy, ?_⟩
      apply orientSite_injective d
      rw [orientSite_shift_east]
      exact hyx
  · rintro (⟨hx, rfl⟩ | ⟨hy, rfl⟩)
    · exact Or.inl ⟨(chessEven_orientSite d x).mpr hx,
        orientSite_shift_east d x⟩
    · exact Or.inr ⟨(chessEven_orientSite d y).mpr hy,
        orientSite_shift_east d y⟩

theorem pairFree_X_orientSite_iff
    (d : Dir) (A : Finset Site) :
    PairFree (XPair d) (A.image (orientSite d)) ↔
      PairFree (XPair east) A := by
  constructor
  · intro h x hx y hy hxy hpair
    exact h (orientSite d x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (orientSite d y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      (fun hEq ↦ hxy (orientSite_injective d hEq))
      ((XPair_orientSite_iff d x y).mpr hpair)
  · intro h x hx y hy hxy hpair
    rcases Finset.mem_image.mp hx with ⟨x₀, hx₀, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y₀, hy₀, rfl⟩
    exact h x₀ hx₀ y₀ hy₀
      (fun hEq ↦ hxy (congrArg (orientSite d) hEq))
      ((XPair_orientSite_iff d x₀ y₀).mp hpair)

/-- The source pairing history is rotated together with the stopped
Theta event.  This is essential: Proposition 4.5 controls `Theta ∩ M`,
not the bare stopped Theta event. -/
theorem prefixPairingEvent_x_orient_iff
    (d : Dir) (s : Path) (m k : ℕ) :
    s ∈ prefixPairingEvent m (xIndex east) k ↔
      orientPath d s ∈ prefixPairingEvent m (xIndex d) k := by
  simp only [prefixPairingEvent, Set.mem_inter_iff, Set.mem_setOf_eq,
    pairingRelation_xIndex, hlozThresholdTimeEventK,
    firstKSitesReachLevel_orientPath,
    levelCreationSitesUpTo_orientPath, pairFree_X_orientSite_iff]

/-- Membership in either stopped half is equivariant under the quarter turn
carrying the east domino to direction `d`. -/
theorem mem_stoppedThetaHalfSites_orient
    (d : Dir) (forward upper : Bool) (cStar : ℝ)
    (s : Path) (m k : ℕ) (x : Site) :
    orientSite d x ∈
        stoppedThetaHalfSites
          (deletionExternalLocalTime (xDeletion d) forward)
          (if forward then chessEven else fun y ↦ ¬ chessEven y)
          upper cStar (orientPath d s) m k ↔
      x ∈ stoppedThetaHalfSites
        (deletionExternalLocalTime (xDeletion east) forward)
        (if forward then chessEven else fun y ↦ ¬ chessEven y)
        upper cStar s m k := by
  simp only [stoppedThetaHalfSites, Finset.mem_filter,
    directCreationTime_orientPath, firstKSitesReachLevel_orientPath]
  have hvisited : orientSite d x ∈
      (visitedSites s (directCreationTime m k s)).image (orientSite d) ↔
      x ∈ visitedSites s (directCreationTime m k s) := by
    constructor
    · intro hmem
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hmem
      exact (orientSite_injective d hxy).symm ▸ hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [visitedSites_orientPath, hvisited, localTime_orientPath,
    deletionExternalLocalTime_orient]
  cases forward <;>
    simp_all only [Bool.false_eq_true, Bool.true_eq, if_false, if_true,
      chessEven_orientSite]

theorem orientSite_surjective (d : Dir) : Function.Surjective (orientSite d) := by
  intro y
  rcases y with ⟨y₁, y₂⟩
  fin_cases d
  · exact ⟨(y₁, y₂), rfl⟩
  · exact ⟨(y₂, -y₁), by simp [orientSite]⟩
  · exact ⟨(-y₁, -y₂), by simp [orientSite]⟩
  · exact ⟨(-y₂, y₁), by simp [orientSite]⟩

theorem nonempty_stoppedThetaHalfSites_orient
    (d : Dir) (forward upper : Bool) (cStar : ℝ)
    (s : Path) (m k : ℕ) :
    (stoppedThetaHalfSites
      (deletionExternalLocalTime (xDeletion east) forward)
      (if forward then (xDeletion east).distinguished
        else fun y ↦ ¬ (xDeletion east).distinguished y)
      upper cStar s m k).Nonempty ↔
    (stoppedThetaHalfSites
      (deletionExternalLocalTime (xDeletion d) forward)
      (if forward then (xDeletion d).distinguished
        else fun y ↦ ¬ (xDeletion d).distinguished y)
      upper cStar (orientPath d s) m k).Nonempty := by
  simp only [xDeletion]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨orientSite d x,
      (mem_stoppedThetaHalfSites_orient d forward upper cStar s m k x).2 hx⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := orientSite_surjective d y
    exact ⟨x,
      (mem_stoppedThetaHalfSites_orient d forward upper cStar s m k x).1 hy⟩

/-- The full stopped event, after the unprimed and primed sides have been
united, is carried from `X₁` to `X_d` by path rotation. -/
theorem stoppedThetaEvent_x_orient_iff
    (d : Dir) (cStar : ℝ) (s : Path) (m k : ℕ) :
    s ∈ stoppedThetaEvent (deletionProfilePair (xDeletion east))
        cStar m k ↔
      orientPath d s ∈ stoppedThetaEvent
        (deletionProfilePair (xDeletion d)) cStar m k := by
  have h₀ := nonempty_stoppedThetaHalfSites_orient
    d true false cStar s m k
  have h₁ := nonempty_stoppedThetaHalfSites_orient
    d true true cStar s m k
  have h₂ := nonempty_stoppedThetaHalfSites_orient
    d false false cStar s m k
  have h₃ := nonempty_stoppedThetaHalfSites_orient
    d false true cStar s m k
  simp only [Bool.true_eq, if_true] at h₀ h₁
  simp only [Bool.false_eq_true, if_false] at h₂ h₃
  simp only [stoppedThetaEvent, Set.mem_setOf_eq, stoppedThetaSites,
    deletionProfilePair, Finset.union_nonempty]
  rw [h₀, h₁, h₂, h₃]

theorem prefixStoppedThetaEvent_x_orient_iff
    (d : Dir) (cStar : ℝ) (s : Path) (m k : ℕ) :
    s ∈ prefixPairingEvent m (xIndex east) (k + 1) ∩
        stoppedThetaEvent (deletionProfilePair (xDeletion east))
          cStar m k ↔
      orientPath d s ∈ prefixPairingEvent m (xIndex d) (k + 1) ∩
        stoppedThetaEvent (deletionProfilePair (xDeletion d))
          cStar m k := by
  exact and_congr (prefixPairingEvent_x_orient_iff d s m (k + 1))
    (stoppedThetaEvent_x_orient_iff d cStar s m k)

theorem measurable_orientPath (d : Dir) : Measurable (orientPath d) := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_of_countable (orientSite d)).comp (measurable_pi_apply n)

/-- Rotation preserves the canonical path law. -/
theorem simpleRandomWalkLaw_map_orientPath (d : Dir) :
    simpleRandomWalkLaw.map (orientPath d) = simpleRandomWalkLaw := by
  unfold simpleRandomWalkLaw
  calc
    Measure.map (orientPath d) (Measure.map simpleRandomWalk incrementLaw) =
        Measure.map (orientPath d ∘ simpleRandomWalk) incrementLaw :=
      Measure.map_map (measurable_orientPath d) measurable_simpleRandomWalk
    _ = Measure.map (simpleRandomWalk ∘ orientIncrements d)
        incrementLaw := by
      apply Measure.map_congr
      filter_upwards [] with ω
      funext n
      exact (simpleRandomWalk_orientIncrements d ω n).symm
    _ = Measure.map simpleRandomWalk
        (Measure.map (orientIncrements d) incrementLaw) :=
      (Measure.map_map measurable_simpleRandomWalk
        (measurable_orientIncrements d)).symm
    _ = Measure.map simpleRandomWalk incrementLaw := by
      rw [incrementLaw_map_orientIncrements]

theorem simpleRandomWalkLaw_stoppedThetaEvent_x_eq
    (d : Dir) (cStar : ℝ) (m k : ℕ) :
    simpleRandomWalkLaw
        (stoppedThetaEvent (deletionProfilePair (xDeletion d)) cStar m k) =
      simpleRandomWalkLaw
        (stoppedThetaEvent (deletionProfilePair (xDeletion east))
          cStar m k) := by
  let E := stoppedThetaEvent (deletionProfilePair (xDeletion d)) cStar m k
  have hE : MeasurableSet E := measurableSet_stoppedThetaEvent _ _ _ _
  calc
    simpleRandomWalkLaw E =
        (simpleRandomWalkLaw.map (orientPath d)) E := by
      rw [simpleRandomWalkLaw_map_orientPath]
    _ = simpleRandomWalkLaw ((orientPath d) ⁻¹' E) :=
      Measure.map_apply (measurable_orientPath d) hE
    _ = simpleRandomWalkLaw
        (stoppedThetaEvent (deletionProfilePair (xDeletion east))
          cStar m k) := by
      congr 1
      ext s
      exact (stoppedThetaEvent_x_orient_iff d cStar s m k).symm

theorem simpleRandomWalkLaw_prefixStoppedThetaEvent_x_eq
    (d : Dir) (cStar : ℝ) (m k : ℕ) :
    simpleRandomWalkLaw
        (prefixPairingEvent m (xIndex d) (k + 1) ∩
          stoppedThetaEvent (deletionProfilePair (xDeletion d))
            cStar m k) =
      simpleRandomWalkLaw
        (prefixPairingEvent m (xIndex east) (k + 1) ∩
          stoppedThetaEvent (deletionProfilePair (xDeletion east))
            cStar m k) := by
  let E := prefixPairingEvent m (xIndex d) (k + 1) ∩
    stoppedThetaEvent (deletionProfilePair (xDeletion d)) cStar m k
  have hE : MeasurableSet E :=
    (measurableSet_prefixPairingEvent m (xIndex d) (k + 1)).inter
      (measurableSet_stoppedThetaEvent _ _ _ _)
  calc
    simpleRandomWalkLaw E =
        (simpleRandomWalkLaw.map (orientPath d)) E := by
      rw [simpleRandomWalkLaw_map_orientPath]
    _ = simpleRandomWalkLaw ((orientPath d) ⁻¹' E) :=
      Measure.map_apply (measurable_orientPath d) hE
    _ = simpleRandomWalkLaw
        (prefixPairingEvent m (xIndex east) (k + 1) ∩
          stoppedThetaEvent (deletionProfilePair (xDeletion east))
            cStar m k) := by
      congr 1
      ext s
      exact (prefixStoppedThetaEvent_x_orient_iff d cStar s m k).symm

/-- A full `X₁` stopped-event estimate transfers to every one of the four
rotated chessboard tilings. -/
theorem stoppedThetaEvent_x_le_of_east
    (d : Dir) (m k : ℕ) (R : ℝ≥0∞)
    (hEast : simpleRandomWalkLaw
      (stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
        (canonicalCStar ⟨0, by omega⟩) m k) ≤ R) :
    simpleRandomWalkLaw
      (stoppedThetaEvent (canonicalProfiles ⟨d.1, by omega⟩)
        (canonicalCStar ⟨d.1, by omega⟩) m k) ≤ R := by
  rw [show canonicalProfiles ⟨d.1, by omega⟩ =
      deletionProfilePair (xDeletion d) by
        simp [canonicalProfiles, pairingProfiles],
    show canonicalCStar ⟨d.1, by omega⟩ = 10 by rfl,
    simpleRandomWalkLaw_stoppedThetaEvent_x_eq]
  simpa only [canonicalProfiles, pairingProfiles, pairingDeletion,
    canonicalCStar] using hEast

/-- Source-correct rotation transport for the event actually controlled in
Proposition 4.5: the stopped Theta event intersected with its pairing
history. -/
theorem prefixStoppedThetaEvent_x_le_of_east
    (d : Dir) (m k : ℕ) (R : ℝ≥0∞)
    (hEast : simpleRandomWalkLaw
      (prefixPairingEvent m ⟨0, by omega⟩ (k + 1) ∩
        stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
          (canonicalCStar ⟨0, by omega⟩) m k) ≤ R) :
    simpleRandomWalkLaw
      (prefixPairingEvent m ⟨d.1, by omega⟩ (k + 1) ∩
        stoppedThetaEvent (canonicalProfiles ⟨d.1, by omega⟩)
          (canonicalCStar ⟨d.1, by omega⟩) m k) ≤ R := by
  have heast : (⟨0, by omega⟩ : Fin 6) = xIndex east := by
    apply Fin.ext
    rfl
  rw [heast] at hEast
  have hEast' : simpleRandomWalkLaw
      (prefixPairingEvent m (xIndex east) (k + 1) ∩
        stoppedThetaEvent (deletionProfilePair (xDeletion east))
          10 m k) ≤ R := by
    simpa only [canonicalProfiles, pairingProfiles, xIndex,
      pairingDeletion_x, canonicalCStar] using hEast
  rw [show (⟨d.1, by omega⟩ : Fin 6) = xIndex d by rfl,
    show canonicalProfiles (xIndex d) =
      deletionProfilePair (xDeletion d) by
        simp [canonicalProfiles, pairingProfiles, xIndex],
    show canonicalCStar (xIndex d) = 10 by rfl,
    simpleRandomWalkLaw_prefixStoppedThetaEvent_x_eq]
  exact hEast'

/-- The separate `X₁` atomizations therefore supply the low-distance
Proposition-4.5 estimate for all four `X_j` indices. -/
theorem xDirections_prop45Estimate_of_separateAtomizations
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (hatoms : HasXEastSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    ∀ᶠ m : ℕ in atTop, ∀ d : Dir, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (prop45FailureEvent canonicalProfiles canonicalCStar m
            ⟨d.1, by omega⟩ r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m
          (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  filter_upwards [xEast_stoppedThetaEstimate_of_separateAtomizations hatoms]
    with m hm
  intro d r a _ha
  apply (measure_mono (show
    prop45FailureEvent canonicalProfiles canonicalCStar m
        ⟨d.1, by omega⟩ r (alphaValue a) ⊆
      prefixPairingEvent m ⟨d.1, by omega⟩ (stageNumber r + 1) ∩
        stoppedThetaEvent (canonicalProfiles ⟨d.1, by omega⟩)
          (canonicalCStar ⟨d.1, by omega⟩) m (stageNumber r) by
    intro s hs
    exact ⟨hs.1.1.1, hs.2⟩)).trans
  exact prefixStoppedThetaEvent_x_le_of_east d m (stageNumber r) _
    (hm r)

end Erdos1166.HLOZProp47Prop45XRotations
