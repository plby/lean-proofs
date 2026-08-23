/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47SourceObjects
import ErdosProblems.Erdos1166.Erdos1166HLOZPrimedStopped

/-!
# Pairing-adapted deletion profiles for HLOZ Proposition 4.7

HLOZ (2.12)--(2.14) uses original-time parity to delete two-step horizontal
excursions.  The four `X_j` profiles below are the checked rotations of that
construction.  The `Y` and `Y'` values in this file are an endpoint-adapted
formal generalization, selecting respectively even and odd first coordinates.
They are useful auxiliary profiles, but they are **not** by themselves an
identification with the temporal-parity deletion of (2.12).  Any source-level
use of the column profiles must therefore supply a separate event
identification/coverage theorem (or work directly with the required column
probability estimate).
-/

namespace Erdos1166.HLOZPairingProfiles

open MeasureTheory ProbabilityTheory
open HLOZFoundation HLOZDecomposition HLOZPairing HLOZProp47SourceObjects
open HLOZPrimedStopped

/-- The data defining one oriented domino tiling. -/
structure DeletionData where
  distinguished : Site → Prop
  step : Site
  /-- If true, use literal original-time parity as in HLOZ (2.12).  If false,
  use the endpoint selector.  The latter is an auxiliary formal extension,
  not a source identification. -/
  timeParity : Bool

/-- A completed excursion along an oriented domino.  The forward deletion
uses `x,x+v,x` at distinguished endpoints.  The primed deletion uses
`x,x-v,x` at the opposite endpoints, exactly as in HLOZ (2.12). -/
def IsDeletionEnd (D : DeletionData) (forward : Bool)
    (s : ℕ → Site) (k : ℕ) : Prop :=
  2 ≤ k ∧
    (if D.timeParity then (if forward then Even k else Odd k)
      else if forward then D.distinguished (s (k - 2))
        else ¬ D.distinguished (s (k - 2))) ∧
    s (k - 1) = s (k - 2) + (if forward then D.step else -D.step) ∧
    s k = s (k - 2)

noncomputable local instance deletionEndDecidable
    (D : DeletionData) (forward : Bool) (s : ℕ → Site) (k : ℕ) :
    Decidable (IsDeletionEnd D forward s k) := Classical.propDecidable _

noncomputable def deletionEndsThrough (D : DeletionData) (forward : Bool)
    (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter (IsDeletionEnd D forward s)

noncomputable def deletionCompletedRemovedTimes
    (D : DeletionData) (forward : Bool) (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  (deletionEndsThrough D forward s n).biUnion fun k ↦ {k - 1, k}

noncomputable def deletionPartialRemovedTimes
    (D : DeletionData) (forward : Bool) (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  if IsDeletionEnd D forward s (n + 1) then {n} else ∅

noncomputable def deletionRemovedTimes
    (D : DeletionData) (forward : Bool) (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  deletionCompletedRemovedTimes D forward s n ∪
    deletionPartialRemovedTimes D forward s n

noncomputable def deletionRetainedTimes
    (D : DeletionData) (forward : Bool) (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  Finset.range (n + 1) \ deletionRemovedTimes D forward s n

/-- The external profile after deleting excursions on one endpoint class. -/
noncomputable def deletionExternalLocalTime
    (D : DeletionData) (forward : Bool)
    (s : ℕ → Site) (n : ℕ) (x : Site) : ℕ :=
  ((deletionRetainedTimes D forward s n).filter fun j ↦ s j = x).card

theorem deletionRemovedTimes_subset_range
    (D : DeletionData) (forward : Bool) (s : ℕ → Site) (n : ℕ) :
    deletionRemovedTimes D forward s n ⊆ Finset.range (n + 1) := by
  intro j hj
  rw [deletionRemovedTimes, Finset.mem_union] at hj
  rcases hj with hj | hj
  · rcases Finset.mem_biUnion.mp hj with ⟨k, hk, hjk⟩
    have hkn : k ≤ n :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjk
    simp only [Finset.mem_range]
    rcases hjk with rfl | rfl <;> omega
  · simp only [deletionPartialRemovedTimes] at hj
    split at hj
    · simp only [Finset.mem_singleton] at hj
      subst j
      simp
    · simp at hj

theorem isDeletionEnd_congr {D : DeletionData} {forward : Bool}
    {s t : ℕ → Site} {q k : ℕ}
    (hst : ∀ j, j ≤ q → s j = t j) (hkq : k ≤ q) :
    IsDeletionEnd D forward s k ↔ IsDeletionEnd D forward t k := by
  by_cases hk2 : 2 ≤ k
  · simp only [IsDeletionEnd, hk2, true_and]
    rw [hst (k - 2) (by omega), hst (k - 1) (by omega), hst k hkq]
  · simp [IsDeletionEnd, hk2]

theorem deletionEndsThrough_congr {D : DeletionData} {forward : Bool}
    {s t : ℕ → Site} {q n : ℕ}
    (hst : ∀ j, j ≤ q → s j = t j) (hnq : n ≤ q) :
    deletionEndsThrough D forward s n = deletionEndsThrough D forward t n := by
  ext k
  simp only [deletionEndsThrough, Finset.mem_filter, Finset.mem_Icc,
    and_congr_right_iff]
  intro hk
  exact isDeletionEnd_congr hst (hk.2.trans hnq)

theorem deletionRemovedTimes_congr {D : DeletionData} {forward : Bool}
    {s t : ℕ → Site} {q n : ℕ}
    (hst : ∀ j, j ≤ q → s j = t j) (hnq : n + 1 ≤ q) :
    deletionRemovedTimes D forward s n = deletionRemovedTimes D forward t n := by
  unfold deletionRemovedTimes deletionCompletedRemovedTimes
    deletionPartialRemovedTimes
  rw [deletionEndsThrough_congr hst (by omega)]
  have hi := isDeletionEnd_congr (D := D) (forward := forward) hst hnq
  by_cases hs : IsDeletionEnd D forward s (n + 1)
  · have ht := hi.mp hs
    simp [hs, ht]
  · have ht : ¬ IsDeletionEnd D forward t (n + 1) := fun h ↦ hs (hi.mpr h)
    simp [hs, ht]

theorem measurable_deletionExternalLocalTime
    (D : DeletionData) (forward : Bool) (n : ℕ) (x : Site) :
    Measurable fun s ↦ deletionExternalLocalTime D forward s n x := by
  have hfiltration : Measurable[canonicalFiltration (n + 1)]
      (fun s ↦ deletionExternalLocalTime D forward s n x) := by
    apply measurable_of_prefix
    unfold PrefixDependent deletionExternalLocalTime deletionRetainedTimes
    intro s t hst
    change ((Finset.range (n + 1) \ deletionRemovedTimes D forward s n).filter
        fun j ↦ s j = x).card =
      ((Finset.range (n + 1) \ deletionRemovedTimes D forward t n).filter
        fun j ↦ t j = x).card
    rw [deletionRemovedTimes_congr hst le_rfl]
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hj
    rw [hst j (by
      have := Finset.mem_sdiff.mp hj
      exact Nat.le_of_lt (Finset.mem_range.mp this.1))]
  exact hfiltration.mono (canonicalFiltration.le (n + 1)) le_rfl

/-- Chessboard tiling `X_j`. -/
def xDeletion (d : Dir) : DeletionData where
  distinguished := chessEven
  step := vec d
  timeParity := true

/-- Endpoint-adapted auxiliary profile associated with the column tiling `Y`
from (4.29).  This is not the temporal-parity deletion of (2.12). -/
def yDeletion : DeletionData where
  distinguished := fun x ↦ Even x.1
  step := vec east
  timeParity := false

/-- Endpoint-adapted auxiliary profile associated with the translated column
tiling `Y'` from (4.30).  This is not the temporal-parity deletion of (2.12). -/
def yDeletion' : DeletionData where
  distinguished := fun x ↦ Odd x.1
  step := vec east
  timeParity := false

/-- The four literal rotated deletion profiles followed by the two auxiliary
endpoint-adapted column profiles, in the order used by `pairingRelation`. -/
def pairingDeletion (i : Fin 6) : DeletionData :=
  match i.1 with
  | 0 => xDeletion east
  | 1 => xDeletion north
  | 2 => xDeletion west
  | 3 => xDeletion south
  | 4 => yDeletion
  | _ => yDeletion'

/-- The two source deletion profiles attached to an oriented tiling. -/
noncomputable def deletionProfilePair (D : DeletionData) : ExternalProfilePair where
  unprimed := deletionExternalLocalTime D true
  primed := deletionExternalLocalTime D false
  unprimedSites := D.distinguished
  primedSites := fun x ↦ ¬ D.distinguished x
  measurable_unprimed := measurable_deletionExternalLocalTime D true
  measurable_primed := measurable_deletionExternalLocalTime D false

/-- The six formal pairing-adapted profiles used by the current Proposition
4.7 assembly.  The final two entries require the separate column connector
described above before they can be called literal HLOZ source profiles. -/
noncomputable def pairingProfiles : Fin 6 → ExternalProfilePair :=
  fun i ↦ deletionProfilePair (pairingDeletion i)

@[simp] theorem pairingProfiles_unprimedSites (i : Fin 6) :
    (pairingProfiles i).unprimedSites = (pairingDeletion i).distinguished := rfl

@[simp] theorem pairingProfiles_primedSites (i : Fin 6) :
    (pairingProfiles i).primedSites =
      (fun x ↦ ¬ (pairingDeletion i).distinguished x) := rfl

@[simp] theorem pairingDeletion_x (d : Dir) :
    pairingDeletion ⟨d.1, by omega⟩ = xDeletion d := by
  fin_cases d <;> rfl

@[simp] theorem pairingDeletion_y : pairingDeletion ⟨4, by omega⟩ = yDeletion := rfl

@[simp] theorem pairingDeletion_y' : pairingDeletion ⟨5, by omega⟩ = yDeletion' := rfl

/-- Literal paper form of the primed `X₁` deletion:
`S_{k-2}=S_{k-1}+e₁=S_k`. -/
theorem isDeletionEnd_xEast_primed_paperFormula (s : ℕ → Site) (k : ℕ) :
    IsDeletionEnd (xDeletion east) false s k ↔
      2 ≤ k ∧ Odd k ∧
        s (k - 2) = s (k - 1) + HLOZDecomposition.paperE1 ∧
        s k = s (k - 2) := by
  simp only [IsDeletionEnd, Bool.false_eq_true, if_false, xDeletion,
    Bool.true_eq, vec, east, HLOZDecomposition.paperE1]
  constructor
  · rintro ⟨hk, hp, hstep, hreturn⟩
    refine ⟨hk, hp, ?_, hreturn⟩
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add,
      Prod.fst_neg, Prod.snd_neg]
    · have h := congrArg Prod.fst hstep
      norm_num at h ⊢
      omega
    · have h := congrArg Prod.snd hstep
      norm_num at h ⊢
      omega
  · rintro ⟨hk, hp, hstep, hreturn⟩
    refine ⟨hk, hp, ?_, hreturn⟩
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add,
      Prod.fst_neg, Prod.snd_neg]
    · have h := congrArg Prod.fst hstep
      norm_num at h ⊢
      omega
    · have h := congrArg Prod.snd hstep
      norm_num at h ⊢
      omega

/-! ### Dihedral transport for the four `X_j` profiles -/

/-- The quarter-turn taking `e₁` to the distinguished direction `e_j`. -/
def orientSite (d : Dir) (x : Site) : Site :=
  match d.1 with
  | 0 => x
  | 1 => (-x.2, x.1)
  | 2 => (-x.1, -x.2)
  | _ => (x.2, -x.1)

def orientPath (d : Dir) (s : ℕ → Site) : ℕ → Site := fun n ↦ orientSite d (s n)

theorem orientSite_injective (d : Dir) : Function.Injective (orientSite d) := by
  intro x y h
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  fin_cases d <;> simp [orientSite] at h ⊢
  all_goals rcases h with ⟨h₁, h₂⟩ <;> constructor <;> omega

@[simp] theorem orientSite_add (d : Dir) (x y : Site) :
    orientSite d (x + y) = orientSite d x + orientSite d y := by
  fin_cases d <;> ext <;> simp [orientSite] <;> ring

@[simp] theorem orientSite_neg (d : Dir) (x : Site) :
    orientSite d (-x) = -orientSite d x := by
  fin_cases d <;> ext <;> simp [orientSite]

@[simp] theorem orientSite_east (d : Dir) : orientSite d (vec east) = vec d := by
  fin_cases d <;> norm_num [orientSite, vec, east]

@[simp] theorem chessEven_orientSite (d : Dir) (x : Site) :
    chessEven (orientSite d x) ↔ chessEven x := by
  fin_cases d
  · rfl
  · change Even (-x.2 + x.1) ↔ Even (x.1 + x.2)
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k + x.2, by omega⟩
    · rintro ⟨k, hk⟩
      exact ⟨k - x.2, by omega⟩
  · change Even (-x.1 + -x.2) ↔ Even (x.1 + x.2)
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨-k, by omega⟩
  · change Even (x.2 + -x.1) ↔ Even (x.1 + x.2)
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k + x.1, by omega⟩
    · rintro ⟨k, hk⟩
      exact ⟨k - x.1, by omega⟩

theorem isDeletionEnd_orient (d : Dir) (forward : Bool)
    (s : ℕ → Site) (k : ℕ) :
    IsDeletionEnd (xDeletion d) forward (orientPath d s) k ↔
      IsDeletionEnd (xDeletion east) forward s k := by
  cases forward
  · simp only [IsDeletionEnd, Bool.false_eq_true, if_false, xDeletion,
      orientPath, chessEven_orientSite, orientSite_neg, orientSite_east,
      orientSite_add]
    constructor <;> rintro ⟨hk, hp, hs, hr⟩
    · refine ⟨hk, hp, ?_, orientSite_injective d hr⟩
      apply orientSite_injective d
      simpa only [orientSite_add, orientSite_neg, orientSite_east] using hs
    · refine ⟨hk, hp, ?_, congrArg (orientSite d) hr⟩
      simpa only [orientSite_add, orientSite_neg, orientSite_east] using
        congrArg (orientSite d) hs
  · simp only [IsDeletionEnd, if_true, xDeletion, orientPath,
      chessEven_orientSite, orientSite_east, orientSite_add]
    constructor <;> rintro ⟨hk, hp, hs, hr⟩
    · refine ⟨hk, hp, ?_, orientSite_injective d hr⟩
      apply orientSite_injective d
      simpa only [orientSite_add, orientSite_east] using hs
    · refine ⟨hk, hp, ?_, congrArg (orientSite d) hr⟩
      simpa only [orientSite_add, orientSite_east] using congrArg (orientSite d) hs

theorem deletionEndsThrough_orient (d : Dir) (forward : Bool)
    (s : ℕ → Site) (n : ℕ) :
    deletionEndsThrough (xDeletion d) forward (orientPath d s) n =
      deletionEndsThrough (xDeletion east) forward s n := by
  ext k
  simp only [deletionEndsThrough, Finset.mem_filter]
  rw [isDeletionEnd_orient]

theorem deletionRemovedTimes_orient (d : Dir) (forward : Bool)
    (s : ℕ → Site) (n : ℕ) :
    deletionRemovedTimes (xDeletion d) forward (orientPath d s) n =
      deletionRemovedTimes (xDeletion east) forward s n := by
  unfold deletionRemovedTimes deletionCompletedRemovedTimes
    deletionPartialRemovedTimes
  rw [deletionEndsThrough_orient]
  by_cases h : IsDeletionEnd (xDeletion east) forward s (n + 1)
  · have h' := (isDeletionEnd_orient d forward s (n + 1)).mpr h
    simp [h, h']
  · have h' : ¬ IsDeletionEnd (xDeletion d) forward
        (orientPath d s) (n + 1) := fun h' ↦
      h ((isDeletionEnd_orient d forward s (n + 1)).mp h')
    simp [h, h']

/-- Equivariance of the deletion profile under the quarter-turn carrying
`e₁` to the direction of `X_j`. -/
theorem deletionExternalLocalTime_orient (d : Dir) (forward : Bool)
    (s : ℕ → Site) (n : ℕ) (x : Site) :
    deletionExternalLocalTime (xDeletion d) forward
        (orientPath d s) n (orientSite d x) =
      deletionExternalLocalTime (xDeletion east) forward s n x := by
  unfold deletionExternalLocalTime deletionRetainedTimes
  rw [deletionRemovedTimes_orient]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _
  exact (orientSite_injective d).eq_iff

/-! ### Increment-law transport for the four `X_j` profiles -/

/-- The permutation of the four canonical increments induced by
`orientSite d`.  Notice that the ordering of `Direction` in `Core` differs
from the ordering of `Dir` used for the pairing relations. -/
def orientDirection (d : Dir) (e : Direction) : Direction :=
  match d.1 with
  | 0 => e
  | 1 => match e.1 with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0
  | 2 => match e.1 with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2
  | _ => match e.1 with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1

theorem orientDirection_injective (d : Dir) :
    Function.Injective (orientDirection d) := by
  intro x y h
  fin_cases d <;> fin_cases x <;> fin_cases y <;>
    simp [orientDirection] at h ⊢

theorem orientDirection_surjective (d : Dir) :
    Function.Surjective (orientDirection d) := by
  intro y
  fin_cases d <;> fin_cases y
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ |
    exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

noncomputable def orientDirectionEquiv (d : Dir) : Direction ≃ Direction :=
  Equiv.ofBijective (orientDirection d)
    ⟨orientDirection_injective d, orientDirection_surjective d⟩

@[simp] theorem directionStep_orientDirection (d : Dir) (e : Direction) :
    directionStep (orientDirection d e) = orientSite d (directionStep e) := by
  fin_cases d <;> fin_cases e <;>
    norm_num [orientDirection, directionStep, orientSite]

def orientIncrements (d : Dir) (ω : ℕ → Direction) : ℕ → Direction :=
  fun n ↦ orientDirection d (ω n)

theorem measurable_orientIncrements (d : Dir) :
    Measurable (orientIncrements d) := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_from_top : Measurable (orientDirection d)).comp
    (measurable_pi_apply n)

/-- Pathwise intertwining of the increment permutation and lattice
orientation. -/
theorem simpleRandomWalk_orientIncrements (d : Dir)
    (ω : ℕ → Direction) (n : ℕ) :
    simpleRandomWalk (orientIncrements d ω) n =
      orientSite d (simpleRandomWalk ω n) := by
  induction n with
  | zero =>
      change (0 : Site) = orientSite d (0 : Site)
      fin_cases d <;> rfl
  | succ n ih =>
      rw [simpleRandomWalk_succ', simpleRandomWalk_succ', ih]
      simp [orientIncrements]

theorem directionLaw_map_orientDirection (d : Dir) :
    directionLaw.map (orientDirection d) = directionLaw := by
  let p := PMF.uniformOfFintype Direction
  have hp : p.map (orientDirection d) = p := by
    apply PMF.ext
    intro b
    rw [PMF.map_apply]
    simp only [p, PMF.uniformOfFintype_apply]
    change (∑' a, if b = (orientDirectionEquiv d) a then
        (Fintype.card Direction : ENNReal)⁻¹ else 0) = _
    rw [Equiv.tsum_eq (orientDirectionEquiv d)
      (fun c ↦ if b = c then (Fintype.card Direction : ENNReal)⁻¹ else 0)]
    simp
  unfold directionLaw
  calc
    (PMF.uniformOfFintype Direction).toMeasure.map (orientDirection d) =
        ((PMF.uniformOfFintype Direction).map
          (orientDirection d)).toMeasure :=
      PMF.toMeasure_map (orientDirection d)
        (PMF.uniformOfFintype Direction)
        (measurable_from_top : Measurable (orientDirection d))
    _ = (PMF.uniformOfFintype Direction).toMeasure :=
      congrArg PMF.toMeasure hp

/-- The coordinatewise quarter-turn preserves the iid increment law. -/
theorem incrementLaw_map_orientIncrements (d : Dir) :
    incrementLaw.map (orientIncrements d) = incrementLaw := by
  unfold incrementLaw orientIncrements
  rw [Measure.infinitePi_map_pi]
  · congr 2
    funext n
    exact directionLaw_map_orientDirection d
  · intro n
    exact measurable_from_top

/-! ### Translation transport for the two column tilings -/

/- The translation identities below are deterministic profile identities.
They are not law-preserving transformations of an origin-started walk; the
origin-fixing reflection interface follows them. -/

def translateSite (a x : Site) : Site := x + a

def translatePath (a : Site) (s : ℕ → Site) : ℕ → Site :=
  fun n ↦ translateSite a (s n)

theorem translateSite_injective (a : Site) :
    Function.Injective (translateSite a) := by
  intro x y h
  exact add_right_cancel h

@[simp] theorem yDeletion'_distinguished_translateEast (x : Site) :
    (yDeletion').distinguished (translateSite (vec east) x) ↔
      yDeletion.distinguished x := by
  change Odd ((x + (1, 0)).1) ↔ Even x.1
  simpa using Int.odd_add_one (a := x.1)

/-- Translating by `e₁` carries the even-column deletion `Y` to the
odd-column deletion `Y'`, for both deletion orientations. -/
theorem isDeletionEnd_y_translate (forward : Bool) (s : ℕ → Site) (k : ℕ) :
    IsDeletionEnd yDeletion' forward (translatePath (vec east) s) k ↔
      IsDeletionEnd yDeletion forward s k := by
  cases forward
  · change (2 ≤ k ∧ ¬ Odd (translateSite (vec east) (s (k - 2))).1 ∧
        translateSite (vec east) (s (k - 1)) =
          translateSite (vec east) (s (k - 2)) + -vec east ∧
        translateSite (vec east) (s k) =
          translateSite (vec east) (s (k - 2))) ↔
      (2 ≤ k ∧ ¬ Even (s (k - 2)).1 ∧
        s (k - 1) = s (k - 2) + -vec east ∧ s k = s (k - 2))
    constructor <;> rintro ⟨hk, hp, hs, hr⟩
    · refine ⟨hk, (yDeletion'_distinguished_translateEast
          (s (k - 2))).not.mp hp, ?_, translateSite_injective (vec east) hr⟩
      apply add_right_cancel (G := Site)
      calc
        s (k - 1) + vec east =
            (s (k - 2) + vec east) + -vec east := hs
        _ = (s (k - 2) + -vec east) + vec east := by abel
    · refine ⟨hk, (yDeletion'_distinguished_translateEast
          (s (k - 2))).not.mpr hp, ?_,
        congrArg (translateSite (vec east)) hr⟩
      change s (k - 1) + vec east =
        (s (k - 2) + vec east) + -vec east
      calc
        s (k - 1) + vec east =
            (s (k - 2) + -vec east) + vec east :=
          congrArg (fun z ↦ z + vec east) hs
        _ = (s (k - 2) + vec east) + -vec east := by abel
  · change (2 ≤ k ∧ Odd (translateSite (vec east) (s (k - 2))).1 ∧
        translateSite (vec east) (s (k - 1)) =
          translateSite (vec east) (s (k - 2)) + vec east ∧
        translateSite (vec east) (s k) =
          translateSite (vec east) (s (k - 2))) ↔
      (2 ≤ k ∧ Even (s (k - 2)).1 ∧
        s (k - 1) = s (k - 2) + vec east ∧ s k = s (k - 2))
    constructor <;> rintro ⟨hk, hp, hs, hr⟩
    · refine ⟨hk, (yDeletion'_distinguished_translateEast
          (s (k - 2))).mp hp, ?_, translateSite_injective (vec east) hr⟩
      apply add_right_cancel (G := Site)
      exact hs
    · refine ⟨hk, (yDeletion'_distinguished_translateEast
          (s (k - 2))).mpr hp, ?_,
        congrArg (translateSite (vec east)) hr⟩
      change s (k - 1) + vec east =
        (s (k - 2) + vec east) + vec east
      exact congrArg (fun z ↦ z + vec east) hs

theorem deletionEndsThrough_y_translate (forward : Bool)
    (s : ℕ → Site) (n : ℕ) :
    deletionEndsThrough yDeletion' forward (translatePath (vec east) s) n =
      deletionEndsThrough yDeletion forward s n := by
  ext k
  simp only [deletionEndsThrough, Finset.mem_filter]
  rw [isDeletionEnd_y_translate]

theorem deletionRemovedTimes_y_translate (forward : Bool)
    (s : ℕ → Site) (n : ℕ) :
    deletionRemovedTimes yDeletion' forward (translatePath (vec east) s) n =
      deletionRemovedTimes yDeletion forward s n := by
  unfold deletionRemovedTimes deletionCompletedRemovedTimes
    deletionPartialRemovedTimes
  rw [deletionEndsThrough_y_translate]
  by_cases h : IsDeletionEnd yDeletion forward s (n + 1)
  · have h' := (isDeletionEnd_y_translate forward s (n + 1)).mpr h
    simp [h, h']
  · have h' : ¬ IsDeletionEnd yDeletion' forward
        (translatePath (vec east) s) (n + 1) := fun h' ↦
      h ((isDeletionEnd_y_translate forward s (n + 1)).mp h')
    simp [h, h']

/-- Profile equivariance between the distinct `Y` and `Y'` encodings.  This
does not identify either encoding with the time-parity `X₁` encoding. -/
theorem deletionExternalLocalTime_y_translate (forward : Bool)
    (s : ℕ → Site) (n : ℕ) (x : Site) :
    deletionExternalLocalTime yDeletion' forward
        (translatePath (vec east) s) n (translateSite (vec east) x) =
      deletionExternalLocalTime yDeletion forward s n x := by
  unfold deletionExternalLocalTime deletionRetainedTimes
  rw [deletionRemovedTimes_y_translate]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _
  exact (translateSite_injective (vec east)).eq_iff

/-! ### Origin-fixing reflection transport for `Y` and `Y'` -/

/-- Reflection in the vertical axis. -/
def reflectSite (x : Site) : Site := (-x.1, x.2)

def reflectPath (s : ℕ → Site) : ℕ → Site := fun n ↦ reflectSite (s n)

theorem reflectSite_injective : Function.Injective reflectSite := by
  intro x y h
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp [reflectSite] at h ⊢
  omega

@[simp] theorem reflectSite_add (x y : Site) :
    reflectSite (x + y) = reflectSite x + reflectSite y := by
  ext <;> simp [reflectSite] <;> ring

@[simp] theorem reflectSite_neg (x : Site) :
    reflectSite (-x) = -reflectSite x := by
  ext <;> simp [reflectSite]

@[simp] theorem reflectSite_east : reflectSite (vec east) = -vec east := by
  norm_num [reflectSite, vec, east]

@[simp] theorem odd_reflectSite (x : Site) :
    Odd (reflectSite x).1 ↔ Odd x.1 := by
  simp [reflectSite]

@[simp] theorem even_reflectSite (x : Site) :
    Even (reflectSite x).1 ↔ Even x.1 := by
  simp [reflectSite]

/-- Vertical-axis reflection sends the `Y` deletion to `Y'` and reverses
the distinguished excursion orientation. -/
theorem isDeletionEnd_y_reflect (forward : Bool) (s : ℕ → Site) (k : ℕ) :
    IsDeletionEnd yDeletion' (!forward) (reflectPath s) k ↔
      IsDeletionEnd yDeletion forward s k := by
  cases forward
  · simp only [Bool.not_false, IsDeletionEnd, if_true, yDeletion',
      yDeletion, Bool.false_eq_true, if_false, reflectPath,
      odd_reflectSite, reflectSite_add, reflectSite_east]
    constructor <;> rintro ⟨hk, hp, hs, hr⟩
    · refine ⟨hk, Int.not_even_iff_odd.mpr hp, ?_, reflectSite_injective hr⟩
      apply reflectSite_injective
      simpa only [reflectSite_add, reflectSite_neg, reflectSite_east,
        neg_neg] using hs
    · refine ⟨hk, Int.not_even_iff_odd.mp hp, ?_,
        congrArg reflectSite hr⟩
      simpa only [reflectSite_add, reflectSite_neg, reflectSite_east,
        neg_neg] using congrArg reflectSite hs
  · simp only [Bool.not_true, IsDeletionEnd, Bool.false_eq_true, if_false,
      yDeletion', yDeletion, if_true, reflectPath, odd_reflectSite,
      reflectSite_add, reflectSite_neg, reflectSite_east]
    constructor <;> rintro ⟨hk, hp, hs, hr⟩
    · refine ⟨hk, Int.not_odd_iff_even.mp hp, ?_, reflectSite_injective hr⟩
      apply reflectSite_injective
      simpa only [reflectSite_add, reflectSite_east] using hs
    · refine ⟨hk, Int.not_odd_iff_even.mpr hp, ?_,
        congrArg reflectSite hr⟩
      simpa only [reflectSite_add, reflectSite_east] using
        congrArg reflectSite hs

theorem deletionEndsThrough_y_reflect (forward : Bool)
    (s : ℕ → Site) (n : ℕ) :
    deletionEndsThrough yDeletion' (!forward) (reflectPath s) n =
      deletionEndsThrough yDeletion forward s n := by
  ext k
  simp only [deletionEndsThrough, Finset.mem_filter]
  rw [isDeletionEnd_y_reflect]

theorem deletionRemovedTimes_y_reflect (forward : Bool)
    (s : ℕ → Site) (n : ℕ) :
    deletionRemovedTimes yDeletion' (!forward) (reflectPath s) n =
      deletionRemovedTimes yDeletion forward s n := by
  unfold deletionRemovedTimes deletionCompletedRemovedTimes
    deletionPartialRemovedTimes
  rw [deletionEndsThrough_y_reflect]
  by_cases h : IsDeletionEnd yDeletion forward s (n + 1)
  · have h' := (isDeletionEnd_y_reflect forward s (n + 1)).mpr h
    simp [h, h']
  · have h' : ¬ IsDeletionEnd yDeletion' (!forward)
        (reflectPath s) (n + 1) := fun h' ↦
      h ((isDeletionEnd_y_reflect forward s (n + 1)).mp h')
    simp [h, h']

/-- Profile equivariance under the origin-fixing reflection. -/
theorem deletionExternalLocalTime_y_reflect (forward : Bool)
    (s : ℕ → Site) (n : ℕ) (x : Site) :
    deletionExternalLocalTime yDeletion' (!forward) (reflectPath s) n
        (reflectSite x) =
      deletionExternalLocalTime yDeletion forward s n x := by
  unfold deletionExternalLocalTime deletionRetainedTimes
  rw [deletionRemovedTimes_y_reflect]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _
  exact reflectSite_injective.eq_iff

/-- The increment permutation induced by vertical-axis reflection. -/
def reflectDirection (e : Direction) : Direction :=
  match e.1 with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3

theorem reflectDirection_injective : Function.Injective reflectDirection := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp [reflectDirection] at h ⊢

theorem reflectDirection_surjective : Function.Surjective reflectDirection := by
  intro y
  fin_cases y
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

noncomputable def reflectDirectionEquiv : Direction ≃ Direction :=
  Equiv.ofBijective reflectDirection
    ⟨reflectDirection_injective, reflectDirection_surjective⟩

@[simp] theorem directionStep_reflectDirection (e : Direction) :
    directionStep (reflectDirection e) = reflectSite (directionStep e) := by
  fin_cases e <;> norm_num [reflectDirection, directionStep, reflectSite]

def reflectIncrements (ω : ℕ → Direction) : ℕ → Direction :=
  fun n ↦ reflectDirection (ω n)

theorem simpleRandomWalk_reflectIncrements (ω : ℕ → Direction) (n : ℕ) :
    simpleRandomWalk (reflectIncrements ω) n =
      reflectSite (simpleRandomWalk ω n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [simpleRandomWalk_succ', simpleRandomWalk_succ', ih]
      simp [reflectIncrements]

theorem directionLaw_map_reflectDirection :
    directionLaw.map reflectDirection = directionLaw := by
  let p := PMF.uniformOfFintype Direction
  have hp : p.map reflectDirection = p := by
    apply PMF.ext
    intro b
    rw [PMF.map_apply]
    simp only [p, PMF.uniformOfFintype_apply]
    change (∑' a, if b = reflectDirectionEquiv a then
      (Fintype.card Direction : ENNReal)⁻¹ else 0) = _
    rw [Equiv.tsum_eq reflectDirectionEquiv
      (fun c ↦ if b = c then (Fintype.card Direction : ENNReal)⁻¹ else 0)]
    simp
  unfold directionLaw
  calc
    (PMF.uniformOfFintype Direction).toMeasure.map reflectDirection =
        ((PMF.uniformOfFintype Direction).map reflectDirection).toMeasure :=
      PMF.toMeasure_map reflectDirection (PMF.uniformOfFintype Direction)
        (measurable_from_top : Measurable reflectDirection)
    _ = (PMF.uniformOfFintype Direction).toMeasure :=
      congrArg PMF.toMeasure hp

/-- Vertical-axis reflection preserves the iid increment law and hence is the
law-preserving transport between the two column-profile encodings. -/
theorem incrementLaw_map_reflectIncrements :
    incrementLaw.map reflectIncrements = incrementLaw := by
  unfold incrementLaw reflectIncrements
  rw [Measure.infinitePi_map_pi]
  · congr 2
    funext n
    exact directionLaw_map_reflectDirection
  · intro n
    exact measurable_from_top

/-! ### Identification of the `X₁` profiles with the paper decompositions -/

theorem isDeletionEnd_xEast_forward_iff
    (s : ℕ → Site) (k : ℕ) :
    IsDeletionEnd (xDeletion east) true s k ↔ IsLazyEnd s k := by
  simp only [IsDeletionEnd, if_true, xDeletion, vec, east, IsLazyEnd, paperE1]
  constructor
  · rintro ⟨hk, heven, hstep, hreturn⟩
    refine ⟨hk, heven, ?_, hreturn⟩
    apply Prod.ext
    · have h := congrArg Prod.fst hstep
      norm_num at h ⊢
      omega
    · have h := congrArg Prod.snd hstep
      norm_num at h ⊢
      omega
  · rintro ⟨hk, heven, hstep, hreturn⟩
    refine ⟨hk, heven, ?_, hreturn⟩
    apply Prod.ext
    · have h := congrArg Prod.fst hstep
      norm_num at h ⊢
      omega
    · have h := congrArg Prod.snd hstep
      norm_num at h ⊢
      omega

theorem isDeletionEnd_xEast_primed_iff
    (s : ℕ → Site) (k : ℕ) :
    IsDeletionEnd (xDeletion east) false s k ↔ IsPrimedLazyEnd s k := by
  rw [isDeletionEnd_xEast_primed_paperFormula]
  unfold IsPrimedLazyEnd
  constructor <;> rintro ⟨hk, hodd, hs, hr⟩
  · refine ⟨?_, hodd, hs, hr⟩
    rcases hodd with ⟨r, hr⟩
    omega
  · exact ⟨by omega, hodd, hs, hr⟩

theorem deletionEndsThrough_xEast_forward
    (s : ℕ → Site) (n : ℕ) :
    deletionEndsThrough (xDeletion east) true s n = lazyEndsThrough s n := by
  ext k
  simp only [deletionEndsThrough, lazyEndsThrough, Finset.mem_filter,
    Finset.mem_Icc]
  rw [isDeletionEnd_xEast_forward_iff]

theorem deletionEndsThrough_xEast_primed
    (s : ℕ → Site) (n : ℕ) :
    deletionEndsThrough (xDeletion east) false s n = primedLazyEndsThrough s n := by
  ext k
  simp only [deletionEndsThrough, primedLazyEndsThrough, Finset.mem_filter,
    Finset.mem_Icc]
  rw [isDeletionEnd_xEast_primed_iff]
  constructor
  · rintro ⟨⟨hk2, hkn⟩, hk⟩
    exact ⟨⟨hk.1, hkn⟩, hk⟩
  · rintro ⟨⟨hk3, hkn⟩, hk⟩
    exact ⟨⟨by omega, hkn⟩, hk⟩

theorem deletionRemovedTimes_xEast_forward
    (s : ℕ → Site) (n : ℕ) :
    deletionRemovedTimes (xDeletion east) true s n = lazyRemovedTimes s n := by
  unfold deletionRemovedTimes deletionCompletedRemovedTimes deletionPartialRemovedTimes
    lazyRemovedTimes completedLazyRemovedTimes partialLazyRemovedTimes
  rw [deletionEndsThrough_xEast_forward]
  by_cases h : IsLazyEnd s (n + 1)
  · have h' := (isDeletionEnd_xEast_forward_iff s (n + 1)).mpr h
    simp [h, h']
  · have h' : ¬ IsDeletionEnd (xDeletion east) true s (n + 1) :=
      fun h' ↦ h ((isDeletionEnd_xEast_forward_iff s (n + 1)).mp h')
    simp [h, h']

theorem deletionRemovedTimes_xEast_primed
    (s : ℕ → Site) (n : ℕ) :
    deletionRemovedTimes (xDeletion east) false s n = primedRemovedTimes s n := by
  unfold deletionRemovedTimes deletionCompletedRemovedTimes deletionPartialRemovedTimes
    primedRemovedTimes primedCompletedRemovedTimes primedPartialRemovedTimes
  rw [deletionEndsThrough_xEast_primed]
  by_cases h : IsPrimedLazyEnd s (n + 1)
  · have h' := (isDeletionEnd_xEast_primed_iff s (n + 1)).mpr h
    simp [h, h']
  · have h' : ¬ IsDeletionEnd (xDeletion east) false s (n + 1) :=
      fun h' ↦ h ((isDeletionEnd_xEast_primed_iff s (n + 1)).mp h')
    simp [h, h']

/-- The forward generic `X₁` deletion is definitionally the unprimed
external profile of HLOZ (2.12). -/
theorem deletionExternalLocalTime_xEast_forward
    (s : ℕ → Site) (n : ℕ) (x : Site) :
    deletionExternalLocalTime (xDeletion east) true s n x =
      paperExternalLocalTime s n x := by
  unfold deletionExternalLocalTime deletionRetainedTimes paperExternalLocalTime retainedTimes
  rw [deletionRemovedTimes_xEast_forward]

/-- The backward generic `X₁` deletion is the primed external profile of
the literal paper orientation `x,x-e₁,x`. -/
theorem deletionExternalLocalTime_xEast_primed
    (s : ℕ → Site) (n : ℕ) (x : Site) :
    deletionExternalLocalTime (xDeletion east) false s n x =
      primedExternalLocalTime s n x := by
  unfold deletionExternalLocalTime deletionRetainedTimes primedExternalLocalTime
    primedRetainedTimes
  rw [deletionRemovedTimes_xEast_primed]

end Erdos1166.HLOZPairingProfiles
