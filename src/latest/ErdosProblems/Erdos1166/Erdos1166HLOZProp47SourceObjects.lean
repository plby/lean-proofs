import ErdosProblems.Erdos1166.Erdos1166HLOZDecomposition
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410
import ErdosProblems.Erdos1166.Erdos1166HLOZPairing
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Parameters

/-!
Source-level deterministic objects used in HLOZ (4.33)--(4.37).

This file deliberately contains no probability estimate and no declaration of
a "bad event" as the complement of a desired cover.  In particular, the
stopped `Theta` wrapper below only packages the two external profiles appearing
in Proposition 4.5; the inverse-clock law needed to estimate it is a separate
input.
-/

namespace Erdos1166.HLOZProp47SourceObjects

open MeasureTheory Set
open HLOZFoundation HLOZDecomposition HLOZPairing
open HLOZProp47Parameters

/-! ### The distinguished endpoint of a domino -/

/-- The opposite lattice direction. -/
def oppositeDir : Dir → Dir
  | 0 => west
  | 1 => south
  | 2 => east
  | _ => north

@[simp] theorem vec_oppositeDir_add (d : Dir) (x : Site) :
    shift (shift x (vec d)) (vec (oppositeDir d)) = x := by
  fin_cases d <;> simp [oppositeDir, shift, vec, east, north, west, south]

/-- For one of the six pairings, select the distinguished endpoint of the
domino containing `x`: chessboard-even for an `X` pairing, and the prescribed
left endpoint for `Y` or `Y'`. -/
noncomputable def distinguishedEndpoint (i : Fin 6) (x : Site) : Site :=
  by
    classical
    exact match i.1 with
      | 0 => if chessEven x then x else shift x (vec west)
      | 1 => if chessEven x then x else shift x (vec south)
      | 2 => if chessEven x then x else shift x (vec east)
      | 3 => if chessEven x then x else shift x (vec north)
      | 4 => if Even x.1 then x else shift x (vec west)
      | _ => if Odd x.1 then x else shift x (vec west)

theorem measurable_distinguishedEndpoint (i : Fin 6) :
    Measurable (distinguishedEndpoint i) := measurable_of_countable _

/-- The finite set of dominoes containing the first `k` creation sites,
represented by their distinguished endpoints. -/
noncomputable def creationDominoEndpoints (i : Fin 6) (s : ℕ → Site)
    (m k : ℕ) : Finset Site :=
  (Finset.Icc 1 k).image fun j ↦
    distinguishedEndpoint i (levelCreationSite s m j)

theorem measurable_creationDominoEndpoints (i : Fin 6) (m k : ℕ) :
    Measurable fun s : ℕ → Site ↦ creationDominoEndpoints i s m k := by
  rw [measurable_finset_iff]
  intro x
  simp only [creationDominoEndpoints, Finset.mem_image]
  apply Measurable.exists
  intro j
  by_cases hj : j ∈ Finset.Icc 1 k
  · simp only [hj, true_and]
    exact measurableSet_setOfPred.mp (measurableSet_eq_fun
      ((measurable_distinguishedEndpoint i).comp
        (measurable_levelCreationSite m j)) measurable_const)
  · simp [hj]

/-! ### The exact near-favourite set `M^k(m,α)` from (4.33) -/

/-- Natural-valued realization of the direct stopping time `T_m^k`. -/
noncomputable def directCreationTime (m k : ℕ) (s : ℕ → Site) : ℕ :=
  (firstKSitesReachLevel m k s).untopA

theorem measurable_directCreationTime (m k : ℕ) :
    Measurable (directCreationTime m k) :=
  (isStoppingTime_firstKSitesReachLevel m k).measurable'.untopA

/-- HLOZ (4.33): sites outside the first `k` creation dominoes whose local
time at `T_m^k` lies in the open interval `(m-m^α,m)`.  The visited-site
enumeration makes the mathematically finite set explicit. -/
noncomputable def nearFavoriteSites (i : Fin 6) (s : ℕ → Site)
    (m k : ℕ) (alpha : ℝ) : Finset Site := by
  classical
  exact (visitedSites s (directCreationTime m k s)).filter fun x ↦
      firstKSitesReachLevel m k s ≠ ⊤ ∧
        distinguishedEndpoint i x ∉ creationDominoEndpoints i s m k ∧
        (m : ℝ) - (m : ℝ) ^ alpha < localTime s (directCreationTime m k s) x ∧
        (localTime s (directCreationTime m k s) x : ℝ) < m

theorem finite_nearFavoriteSites (i : Fin 6) (s : ℕ → Site)
    (m k : ℕ) (alpha : ℝ) :
    Set.Finite (↑(nearFavoriteSites i s m k alpha) : Set Site) :=
  (nearFavoriteSites i s m k alpha).finite_toSet

private theorem measurableSet_variable_time
    (T : (ℕ → Site) → ℕ) (hT : Measurable T)
    (P : ℕ → (ℕ → Site) → Prop)
    (hP : ∀ n, MeasurableSet {s | P n s}) :
    MeasurableSet {s | P (T s) s} := by
  have hEq : {s | P (T s) s} = ⋃ n : ℕ, {s | T s = n} ∩ {s | P n s} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hs
      exact ⟨T s, rfl, hs⟩
    · rintro ⟨n, hn, hs⟩
      simpa [hn] using hs
  rw [hEq]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_eq_fun hT measurable_const).inter (hP n)

theorem measurable_nearFavoriteSites (i : Fin 6) (m k : ℕ) (alpha : ℝ) :
    Measurable fun s : ℕ → Site ↦ nearFavoriteSites i s m k alpha := by
  rw [measurable_finset_iff]
  intro x
  simp only [nearFavoriteSites, Finset.mem_filter]
  apply Measurable.and
  · apply measurableSet_setOfPred.mp
    exact measurableSet_variable_time (directCreationTime m k)
      (measurable_directCreationTime m k)
      (fun n s ↦ x ∈ visitedSites s n) fun n ↦
        measurableSet_setOfPred.mpr
          ((measurable_finset_mem x).comp (measurable_visitedSites_eval n))
  · apply Measurable.and
    · exact measurableSet_setOfPred.mp
        (isStoppingTime_firstKSitesReachLevel m k).measurableSet_eq_top.compl
    · apply Measurable.and
      · exact measurableSet_setOfPred.mp ((measurableSet_setOfPred.mpr
          ((measurable_finset_mem (distinguishedEndpoint i x)).comp
            (measurable_creationDominoEndpoints i m k))).compl)
      · apply Measurable.and <;> apply measurableSet_setOfPred.mp
        · exact measurableSet_variable_time (directCreationTime m k)
            (measurable_directCreationTime m k)
            (fun n s ↦ (m : ℝ) - (m : ℝ) ^ alpha < localTime s n x) fun n ↦
              measurableSet_lt measurable_const
                ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp
                  (measurable_localTime_eval n x))
        · exact measurableSet_variable_time (directCreationTime m k)
            (measurable_directCreationTime m k)
            (fun n s ↦ (localTime s n x : ℝ) < m) fun n ↦
              measurableSet_lt
                ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp
                  (measurable_localTime_eval n x)) measurable_const

theorem nearFavoriteSites_mono_alpha (i : Fin 6) (s : ℕ → Site)
    (m k : ℕ) {alpha beta : ℝ} (hm : 1 ≤ m) (hab : alpha ≤ beta) :
    nearFavoriteSites i s m k alpha ⊆ nearFavoriteSites i s m k beta := by
  intro x hx
  unfold nearFavoriteSites at hx ⊢
  rw [Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, hx.2.1, hx.2.2.1, ?_, hx.2.2.2.2⟩
  have hrpow : (m : ℝ) ^ alpha ≤ (m : ℝ) ^ beta :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) hab
  linarith [hx.2.2.2.1]

/-! ### The stopped `Theta_k` wrapper from Proposition 4.5 -/

/-- A pair of external profiles, unprimed and primed.  The first is
instantiated by `paperExternalLocalTime`; the second is the source's primed
decomposition and is kept explicit until that decomposition is constructed. -/
structure ExternalProfilePair where
  unprimed : (ℕ → Site) → ℕ → Site → ℕ
  primed : (ℕ → Site) → ℕ → Site → ℕ
  /-- Distinguished endpoints of the dominoes for the forward deletion. -/
  unprimedSites : Site → Prop
  /-- The opposite endpoints, used by the backward/primed deletion. -/
  primedSites : Site → Prop
  measurable_unprimed : ∀ n x, Measurable fun s ↦ unprimed s n x
  measurable_primed : ∀ n x, Measurable fun s ↦ primed s n x

/-- Extensionality for profile data.  The measurable fields are propositions,
so the four computational fields determine the structure. -/
@[ext] theorem ExternalProfilePair.ext (P Q : ExternalProfilePair)
    (hunprimed : P.unprimed = Q.unprimed)
    (hprimed : P.primed = Q.primed)
    (hunprimedSites : P.unprimedSites = Q.unprimedSites)
    (hprimedSites : P.primedSites = Q.primedSites) : P = Q := by
  cases P with
  | mk pu pp pus pps hmu hmp =>
    cases Q with
    | mk qu qp qus qps hqu hqp =>
      dsimp at hunprimed hprimed hunprimedSites hprimedSites
      subst qu
      subst qp
      subst qus
      subst qps
      rfl

/-- The concrete, source-correct unprimed profile. -/
noncomputable def paperUnprimedProfile :
    (ℕ → Site) → ℕ → Site → ℕ := paperExternalLocalTime

theorem measurable_paperUnprimedProfile (n : ℕ) (x : Site) :
    Measurable fun s ↦ paperUnprimedProfile s n x :=
  (measurable_paperExternalLocalTime_lookahead n x).mono
    (canonicalFiltration.le (n + 1)) le_rfl

/-- The interval `I_m=[m-m^{κ₁}+1,m)` used in the shorthand `Theta_m^k`. -/
noncomputable def thetaBandLower (m : ℕ) : ℝ :=
  (m : ℝ) - (m : ℝ) ^ kappaOne + 1

/-- One parity half of the stopped `Theta^-` or `Theta^+` set in (4.16). -/
noncomputable def stoppedThetaHalfSites
    (external : (ℕ → Site) → ℕ → Site → ℕ)
    (parity : Site → Prop) (upper : Bool) (cStar : ℝ)
    (s : ℕ → Site) (m k : ℕ) : Finset Site := by
  classical
  exact (visitedSites s (directCreationTime m k s)).filter fun x ↦
    firstKSitesReachLevel m k s ≠ ⊤ ∧ parity x ∧
        thetaBandLower m ≤ localTime s (directCreationTime m k s) x ∧
        (localTime s (directCreationTime m k s) x : ℝ) < m ∧
        if upper then
          (15 : ℝ) / 16 * m + cStar * (m : ℝ) ^ (1 - kappaOne) <
            external s (directCreationTime m k s) x
        else
          (external s (directCreationTime m k s) x : ℝ) ≤
            (15 : ℝ) / 16 * thetaBandLower m -
              cStar * (m : ℝ) ^ (1 - kappaOne)

/-- `Theta_m^k ∪ Theta'_m^k`, with the even and odd decompositions kept
separate exactly as in Proposition 4.5. -/
noncomputable def stoppedThetaSites (profiles : ExternalProfilePair)
    (cStar : ℝ) (s : ℕ → Site) (m k : ℕ) : Finset Site :=
  stoppedThetaHalfSites profiles.unprimed profiles.unprimedSites false cStar s m k ∪
    stoppedThetaHalfSites profiles.unprimed profiles.unprimedSites true cStar s m k ∪
    stoppedThetaHalfSites profiles.primed profiles.primedSites false cStar s m k ∪
    stoppedThetaHalfSites profiles.primed profiles.primedSites true cStar s m k

def stoppedThetaEvent (profiles : ExternalProfilePair) (cStar : ℝ)
    (m k : ℕ) : Set (ℕ → Site) :=
  {s | (stoppedThetaSites profiles cStar s m k).Nonempty}

theorem finite_stoppedThetaSites (profiles : ExternalProfilePair) (cStar : ℝ)
    (s : ℕ → Site) (m k : ℕ) :
    Set.Finite (↑(stoppedThetaSites profiles cStar s m k) : Set Site) :=
  (stoppedThetaSites profiles cStar s m k).finite_toSet

theorem measurable_stoppedThetaHalfSites
    (external : (ℕ → Site) → ℕ → Site → ℕ)
    (hexternal : ∀ n x, Measurable fun s ↦ external s n x)
    (parity : Site → Prop) (upper : Bool) (cStar : ℝ) (m k : ℕ) :
    Measurable fun s ↦ stoppedThetaHalfSites external parity upper cStar s m k := by
  rw [measurable_finset_iff]
  intro x
  simp only [stoppedThetaHalfSites, Finset.mem_filter]
  apply Measurable.and
  · apply measurableSet_setOfPred.mp
    exact measurableSet_variable_time (directCreationTime m k)
      (measurable_directCreationTime m k)
      (fun n s ↦ x ∈ visitedSites s n) fun n ↦
        measurableSet_setOfPred.mpr
          ((measurable_finset_mem x).comp (measurable_visitedSites_eval n))
  · apply Measurable.and
    · exact measurableSet_setOfPred.mp
        (isStoppingTime_firstKSitesReachLevel m k).measurableSet_eq_top.compl
    · apply Measurable.and measurable_const
      apply Measurable.and
      · apply measurableSet_setOfPred.mp
        exact measurableSet_variable_time (directCreationTime m k)
          (measurable_directCreationTime m k)
          (fun n s ↦ thetaBandLower m ≤ (localTime s n x : ℝ)) fun n ↦
            measurableSet_le measurable_const
              ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp
                (measurable_localTime_eval n x))
      · apply Measurable.and
        · apply measurableSet_setOfPred.mp
          exact measurableSet_variable_time (directCreationTime m k)
            (measurable_directCreationTime m k)
            (fun n s ↦ (localTime s n x : ℝ) < m) fun n ↦
              measurableSet_lt
                ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp
                  (measurable_localTime_eval n x)) measurable_const
        · apply measurableSet_setOfPred.mp
          cases upper with
          | false =>
              exact measurableSet_variable_time (directCreationTime m k)
                (measurable_directCreationTime m k)
                (fun n s ↦ (external s n x : ℝ) ≤
                  (15 : ℝ) / 16 * thetaBandLower m -
                    cStar * (m : ℝ) ^ (1 - kappaOne)) fun n ↦
                  measurableSet_le
                    ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp
                      (hexternal n x)) measurable_const
          | true =>
              exact measurableSet_variable_time (directCreationTime m k)
                (measurable_directCreationTime m k)
                (fun n s ↦ (15 : ℝ) / 16 * m +
                    cStar * (m : ℝ) ^ (1 - kappaOne) < external s n x) fun n ↦
                  measurableSet_lt measurable_const
                    ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp
                      (hexternal n x))

theorem measurable_stoppedThetaSites (profiles : ExternalProfilePair)
    (cStar : ℝ) (m k : ℕ) :
    Measurable fun s ↦ stoppedThetaSites profiles cStar s m k := by
  let A := measurable_stoppedThetaHalfSites profiles.unprimed
    profiles.measurable_unprimed profiles.unprimedSites false cStar m k
  let B := measurable_stoppedThetaHalfSites profiles.unprimed
    profiles.measurable_unprimed profiles.unprimedSites true cStar m k
  let C := measurable_stoppedThetaHalfSites profiles.primed
    profiles.measurable_primed profiles.primedSites false cStar m k
  let D := measurable_stoppedThetaHalfSites profiles.primed
    profiles.measurable_primed profiles.primedSites true cStar m k
  exact (measurable_of_countable
    (fun q : Finset Site × Finset Site × Finset Site × Finset Site ↦
      q.1 ∪ q.2.1 ∪ q.2.2.1 ∪ q.2.2.2)).comp
        (A.prodMk (B.prodMk (C.prodMk D)))

theorem measurableSet_stoppedThetaEvent (profiles : ExternalProfilePair)
    (cStar : ℝ) (m k : ℕ) :
    MeasurableSet (stoppedThetaEvent profiles cStar m k) := by
  exact measurableSet_setOfPred.mpr
    ((measurable_of_countable fun A : Finset Site ↦ A.Nonempty).comp
      (measurable_stoppedThetaSites profiles cStar m k))

/-! ### The two-sided distance bins in (4.36)--(4.37) -/

noncomputable def siteDistance (x y : Site) : ℝ :=
  Real.sqrt (siteSquaredDistance x y)

noncomputable def distanceBinLower (m : ℕ) (alpha : ℝ) : ℝ :=
  Real.exp ((m : ℝ) ^ (alpha - delta)) / 3

noncomputable def distanceBinUpper (m : ℕ) (alpha : ℝ) : ℝ :=
  Real.exp ((m : ℝ) ^ alpha)

def distanceBinEvent (m k : ℕ) (alpha : ℝ) : Set (ℕ → Site) :=
  {s | firstKSitesReachLevel m k s ≠ ⊤ ∧
    firstKSitesReachLevel m (k + 1) s ≠ ⊤ ∧
    distanceBinLower m alpha ≤
      siteDistance (levelCreationSite s m k) (levelCreationSite s m (k + 1)) ∧
    siteDistance (levelCreationSite s m k) (levelCreationSite s m (k + 1)) ≤
      distanceBinUpper m alpha}

theorem measurableSet_distanceBinEvent (m k : ℕ) (alpha : ℝ) :
    MeasurableSet (distanceBinEvent m k alpha) := by
  apply measurableSet_setOfPred.mpr
  have hp : Measurable fun s : ℕ → Site ↦
      (levelCreationSite s m k, levelCreationSite s m (k + 1)) :=
    (measurable_levelCreationSite m k).prodMk
      (measurable_levelCreationSite m (k + 1))
  apply Measurable.and
  · exact measurableSet_setOfPred.mp
      (isStoppingTime_firstKSitesReachLevel m k).measurableSet_eq_top.compl
  · apply Measurable.and
    · exact measurableSet_setOfPred.mp
        (isStoppingTime_firstKSitesReachLevel m (k + 1)).measurableSet_eq_top.compl
    · have hsq : Measurable fun s : ℕ → Site ↦
          siteSquaredDistance (levelCreationSite s m k)
            (levelCreationSite s m (k + 1)) :=
        (measurable_of_countable fun p : Site × Site ↦
          siteSquaredDistance p.1 p.2).comp hp
      have hd : Measurable fun s : ℕ → Site ↦
          siteDistance (levelCreationSite s m k)
            (levelCreationSite s m (k + 1)) :=
        (measurable_of_countable fun n : ℕ ↦ Real.sqrt n).comp hsq
      exact (measurableSet_setOfPred.mp
        (measurableSet_le measurable_const hd)).and
        (measurableSet_setOfPred.mp (measurableSet_le hd measurable_const))

/-- The full 960-point mesh used to bin distances up through `exp(m)`.
This agrees with the Proposition 4.7 `AlphaIndex`; the distinct 324-point
submesh is `ScreeningAlphaIndex`. -/
abbrev FullAlphaIndex := AlphaIndex

noncomputable def fullAlphaValue (j : FullAlphaIndex) : ℝ :=
  (j.1 + 1) * delta

def fullAlphaGrid : Finset FullAlphaIndex := Finset.univ

@[simp] theorem card_fullAlphaGrid : fullAlphaGrid.card = 960 := by
  simp [fullAlphaGrid]

theorem fullAlphaValue_pos (j : FullAlphaIndex) : 0 < fullAlphaValue j := by
  have hj : (0 : ℝ) < (j.1 : ℝ) + 1 := by positivity
  exact mul_pos hj delta_pos

theorem fullAlphaValue_le_one (j : FullAlphaIndex) : fullAlphaValue j ≤ 1 := by
  have hjNat : j.1 + 1 ≤ 960 := Nat.succ_le_iff.mpr j.2
  have hj : (j.1 : ℝ) + 1 ≤ 960 := by exact_mod_cast hjNat
  rw [fullAlphaValue, delta]
  norm_num
  linarith

theorem fullAlphaValue_last : fullAlphaValue (Fin.last 959) = 1 := by
  norm_num [fullAlphaValue, delta]

/-- Consecutive bins overlap: the next lower endpoint is one third of the
previous upper endpoint. -/
theorem distanceBinLower_succ_eq (m : ℕ) (j : Fin 959) :
    distanceBinLower m (fullAlphaValue j.succ) =
      distanceBinUpper m (fullAlphaValue j.castSucc) / 3 := by
  have hAlpha : fullAlphaValue j.succ - delta = fullAlphaValue j.castSucc := by
    rw [fullAlphaValue, fullAlphaValue, delta]
    norm_num
    push_cast
    ring
  rw [distanceBinLower, distanceBinUpper, hAlpha]

/-- The first lower endpoint is `exp(1)/3 < 1`. -/
theorem distanceBinLower_first_lt_one (m : ℕ) :
    distanceBinLower m (fullAlphaValue (0 : FullAlphaIndex)) < 1 := by
  rw [distanceBinLower, fullAlphaValue, delta]
  norm_num
  simpa using (div_lt_one (show (0 : ℝ) < 3 by norm_num)).2 Real.exp_one_lt_three

private theorem exists_distanceBin_up_to (m : ℕ) {d : ℝ}
    (hd : 1 ≤ d) : ∀ n : ℕ, (hn : n < 960) →
    d ≤ distanceBinUpper m (fullAlphaValue ⟨n, hn⟩) →
    ∃ j : FullAlphaIndex,
      distanceBinLower m (fullAlphaValue j) ≤ d ∧
        d ≤ distanceBinUpper m (fullAlphaValue j) := by
  intro n
  induction n with
  | zero =>
      intro hn hupper
      exact ⟨0, (distanceBinLower_first_lt_one m).le.trans hd, hupper⟩
  | succ n ih =>
      intro hn hupper
      let j : Fin 959 := ⟨n, by omega⟩
      by_cases hprev : d ≤
          distanceBinUpper m (fullAlphaValue j.castSucc)
      · exact ih (by omega) hprev
      · refine ⟨j.succ, ?_, hupper⟩
        rw [distanceBinLower_succ_eq m j]
        have hu : 0 ≤ distanceBinUpper m (fullAlphaValue j.castSucc) :=
          (Real.exp_pos _).le
        have hthird : distanceBinUpper m (fullAlphaValue j.castSucc) / 3 ≤
            distanceBinUpper m (fullAlphaValue j.castSucc) := by linarith
        exact hthird.trans (le_of_not_ge hprev)

/-- The full mesh covers every relevant positive lattice distance.  The
upper assumption is precisely the complement of the separate
`distance > exp(m)` case in Proposition 4.7. -/
theorem exists_fullGrid_distanceBin (m : ℕ) {d : ℝ}
    (hd : 1 ≤ d) (hlarge : d ≤ Real.exp m) :
    ∃ j : FullAlphaIndex,
      distanceBinLower m (fullAlphaValue j) ≤ d ∧
        d ≤ distanceBinUpper m (fullAlphaValue j) := by
  apply exists_distanceBin_up_to m hd 959 (by norm_num)
  have hlast : fullAlphaValue (⟨959, by norm_num⟩ : FullAlphaIndex) = 1 := by
    norm_num [fullAlphaValue, delta]
  rw [distanceBinUpper, hlast, Real.rpow_one]
  exact hlarge

theorem one_le_siteSquaredDistance {x y : Site} (hxy : x ≠ y) :
    1 ≤ siteSquaredDistance x y := by
  rw [Nat.one_le_iff_ne_zero]
  intro hzero
  have hcoords : x.1 - y.1 = 0 ∧ x.2 - y.2 = 0 := by
    simpa [siteSquaredDistance] using hzero
  apply hxy
  exact Prod.ext (sub_eq_zero.mp hcoords.1) (sub_eq_zero.mp hcoords.2)

theorem one_le_siteDistance {x y : Site} (hxy : x ≠ y) :
    1 ≤ siteDistance x y := by
  rw [siteDistance, Real.le_sqrt (by norm_num) (by positivity)]
  norm_num
  exact_mod_cast one_le_siteSquaredDistance hxy

/-- Event-level finite-grid coverage, with both source stopping times finite
and consecutive creation sites distinct made explicit. -/
theorem distanceBinEvent_fullGrid_cover {s : ℕ → Site} {m k : ℕ}
    (hk : firstKSitesReachLevel m k s ≠ ⊤)
    (hnext : firstKSitesReachLevel m (k + 1) s ≠ ⊤)
    (hne : levelCreationSite s m k ≠ levelCreationSite s m (k + 1))
    (hlarge : siteDistance (levelCreationSite s m k)
      (levelCreationSite s m (k + 1)) ≤ Real.exp m) :
    ∃ j : FullAlphaIndex, s ∈ distanceBinEvent m k (fullAlphaValue j) := by
  obtain ⟨j, hlo, hup⟩ := exists_fullGrid_distanceBin m
    (one_le_siteDistance hne) hlarge
  exact ⟨j, hk, hnext, hlo, hup⟩

/-! ### Deterministic source inclusions (4.36)--(4.37) -/

theorem measurableSet_hlozDirectAvoidanceEvent (m j : ℕ) :
    MeasurableSet (hlozDirectAvoidanceEvent m j) := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro n
  apply Measurable.imp
  · exact (measurable_of_countable
      (fun t : WithTop ℕ ↦ t < (n : WithTop ℕ))).comp
        (isStoppingTime_firstKSitesReachLevel m (j - 1)).measurable'
  · apply Measurable.imp
    · exact (measurable_of_countable
        (fun t : WithTop ℕ ↦ (n : WithTop ℕ) ≤ t)).comp
          (isStoppingTime_firstKSitesReachLevel m j).measurable'
    · apply Measurable.forall
      intro i
      apply measurable_const.imp
      apply measurable_const.imp
      exact (measurable_of_countable (fun p : Site × Site ↦ p.1 ≠ p.2)).comp
        ((measurable_pi_apply n).prodMk (measurable_levelCreationSite m i))

/-- The shifted exit-before-return information needed in (4.36), expressed
pathwise: `U_m^{k+1}` supplies no return to `L_m^k`, while the next creation
site lies outside the displayed radius. -/
def exitBeforeReturnAtNextCreation (m k : ℕ) (radius : ℝ) :
    Set (ℕ → Site) :=
  {s | firstKSitesReachLevel m k s ≠ ⊤ ∧
    firstKSitesReachLevel m (k + 1) s ≠ ⊤ ∧
    s ∈ hlozDirectAvoidanceEvent m (k + 1) ∧
    radius ≤ siteDistance (levelCreationSite s m k)
      (levelCreationSite s m (k + 1))}

theorem measurableSet_exitBeforeReturnAtNextCreation (m k : ℕ) (radius : ℝ) :
    MeasurableSet (exitBeforeReturnAtNextCreation m k radius) := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.and
  · exact measurableSet_setOfPred.mp
      (isStoppingTime_firstKSitesReachLevel m k).measurableSet_eq_top.compl
  · apply Measurable.and
    · exact measurableSet_setOfPred.mp
        (isStoppingTime_firstKSitesReachLevel m (k + 1)).measurableSet_eq_top.compl
    · apply Measurable.and
      · exact measurableSet_setOfPred.mp
          (measurableSet_hlozDirectAvoidanceEvent m (k + 1))
      · have hp : Measurable fun s : ℕ → Site ↦
            (levelCreationSite s m k, levelCreationSite s m (k + 1)) :=
          (measurable_levelCreationSite m k).prodMk
            (measurable_levelCreationSite m (k + 1))
        have hsq : Measurable fun s : ℕ → Site ↦
            siteSquaredDistance (levelCreationSite s m k)
              (levelCreationSite s m (k + 1)) :=
          (measurable_of_countable fun p : Site × Site ↦
            siteSquaredDistance p.1 p.2).comp hp
        have hd : Measurable fun s : ℕ → Site ↦
            siteDistance (levelCreationSite s m k)
              (levelCreationSite s m (k + 1)) :=
          (measurable_of_countable fun n : ℕ ↦ Real.sqrt n).comp hsq
        exact measurableSet_setOfPred.mp (measurableSet_le measurable_const hd)

/-- The high-scale deterministic inclusion (4.36).  On a mesh point above
`κ₂`, discreteness gives `κ₂ ≤ α-δ`; that arithmetic fact is the
explicit hypothesis here. -/
theorem highScale_bin_subset_exitBeforeReturn
    (m k : ℕ) (alpha : ℝ) (hm : 1 ≤ m)
    (halpha : kappaTwo ≤ alpha - delta) :
    hlozDirectAvoidanceEvent m (k + 1) ∩ distanceBinEvent m k alpha ⊆
      exitBeforeReturnAtNextCreation m k
        (Real.exp ((m : ℝ) ^ kappaTwo) / 3) := by
  rintro s ⟨havoid, hfinite, hnext, hlower, _hupper⟩
  refine ⟨hfinite, hnext, havoid, ?_⟩
  apply hlower.trans'
  rw [distanceBinLower]
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hrpow : (m : ℝ) ^ kappaTwo ≤ (m : ℝ) ^ (alpha - delta) :=
    Real.rpow_le_rpow_of_exponent_le hmReal halpha
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hrpow) (by norm_num)

/-- The event that the next creation site is already one of the candidates
in `M^k(m,β)`.  In the paper this membership is obtained from `Q_m^k`
together with the creation-domino exclusion. -/
def nextCreationIsCandidateEvent (i : Fin 6) (m k : ℕ) (beta : ℝ) :
    Set (ℕ → Site) :=
  {s | levelCreationSite s m (k + 1) ∈ nearFavoriteSites i s m k beta}

theorem measurableSet_nextCreationIsCandidateEvent
    (i : Fin 6) (m k : ℕ) (beta : ℝ) :
    MeasurableSet (nextCreationIsCandidateEvent i m k beta) := by
  apply measurableSet_setOfPred.mpr
  exact (measurable_of_countable
    (fun p : Site × Finset Site ↦ p.1 ∈ p.2)).comp
      ((measurable_levelCreationSite m (k + 1)).prodMk
        (measurable_nearFavoriteSites i m k beta))

/-- The non-geometric screen on the right side of (4.37). -/
def lowScaleScreenEvent (profiles : ExternalProfilePair) (cStar : ℝ)
    (i : Fin 6) (m k : ℕ) (beta : ℝ) : Set (ℕ → Site) :=
  {s | (nearFavoriteSites i s m k beta).Nonempty ∧
    stoppedThetaSites profiles cStar s m k = ∅ ∧
    ((nearFavoriteSites i s m k kappaOne).card : ℝ) ≤ Real.log m ^ 2}

theorem measurableSet_lowScaleScreenEvent (profiles : ExternalProfilePair)
    (cStar : ℝ) (i : Fin 6) (m k : ℕ) (beta : ℝ) :
    MeasurableSet (lowScaleScreenEvent profiles cStar i m k beta) := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.and
  · exact (measurable_of_countable fun A : Finset Site ↦ A.Nonempty).comp
      (measurable_nearFavoriteSites i m k beta)
  · apply Measurable.and
    · exact (measurable_of_countable fun A : Finset Site ↦ A = ∅).comp
        (measurable_stoppedThetaSites profiles cStar m k)
    · exact (measurable_of_countable fun A : Finset Site ↦
        (A.card : ℝ) ≤ Real.log m ^ 2).comp
          (measurable_nearFavoriteSites i m k kappaOne)

/-- The complete deterministic antecedent used in the low-scale branch of
(4.37), after the paper's `Q_m^k` implication has supplied candidate
membership. -/
def lowScaleStageEvent (profiles : ExternalProfilePair) (cStar : ℝ)
    (i : Fin 6) (m k : ℕ) (alpha : ℝ) : Set (ℕ → Site) :=
  hlozDirectAvoidanceEvent m (k + 1) ∩ distanceBinEvent m k alpha ∩
    nextCreationIsCandidateEvent i m k (alpha + delta) ∩
    {s | stoppedThetaSites profiles cStar s m k = ∅} ∩
    {s | ((nearFavoriteSites i s m k kappaOne).card : ℝ) ≤ Real.log m ^ 2}

theorem measurableSet_lowScaleStageEvent (profiles : ExternalProfilePair)
    (cStar : ℝ) (i : Fin 6) (m k : ℕ) (alpha : ℝ) :
    MeasurableSet (lowScaleStageEvent profiles cStar i m k alpha) := by
  exact ((((measurableSet_hlozDirectAvoidanceEvent m (k + 1)).inter
    (measurableSet_distanceBinEvent m k alpha)).inter
    (measurableSet_nextCreationIsCandidateEvent i m k (alpha + delta))).inter
    (measurableSet_setOfPred.mpr
      ((measurable_of_countable fun A : Finset Site ↦ A = ∅).comp
        (measurable_stoppedThetaSites profiles cStar m k)))).inter
    (measurableSet_setOfPred.mpr
      ((measurable_of_countable fun A : Finset Site ↦
        (A.card : ℝ) ≤ Real.log m ^ 2).comp
          (measurable_nearFavoriteSites i m k kappaOne)))

/-- The deterministic inclusion (4.37): the distance/avoidance factors give
the shifted exit-before-return event, while candidate membership, empty
`Theta`, and the cardinality control give the displayed screen. -/
theorem lowScaleStage_subset_exit_and_screen
    (profiles : ExternalProfilePair) (cStar : ℝ)
    (i : Fin 6) (m k : ℕ) (alpha : ℝ) :
    lowScaleStageEvent profiles cStar i m k alpha ⊆
      exitBeforeReturnAtNextCreation m k (distanceBinLower m alpha) ∩
        lowScaleScreenEvent profiles cStar i m k (alpha + delta) := by
  rintro s ⟨⟨⟨⟨havoid, hbin⟩, hcand⟩, htheta⟩, hcard⟩
  rcases hbin with ⟨hfinite, hnext, hlower, _hupper⟩
  refine ⟨⟨hfinite, hnext, havoid, hlower⟩, ?_⟩
  exact ⟨⟨levelCreationSite s m (k + 1), hcand⟩, htheta, hcard⟩

end Erdos1166.HLOZProp47SourceObjects
