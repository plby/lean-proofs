/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410PotentialRace
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47SourceAssembly

/-!
# The finite-candidate union step in HLOZ Lemma 4.10

This file supplies the deterministic truncation in the proof of Lemma 4.10
of Hao--Li--Okada--Zheng.  The stopping times `σ_i^j` enumerate the
sites in the finite candidate set `F_j`.  Consequently, outside the event
`|F_j| > cap`, every `σ_i^j` with `i > cap` is infinite.  The countable
union in `hlozLemma410BPrimeEvent_inter_subset_iUnion` therefore becomes a
finite union, and a uniform post-hit race estimate costs exactly the factor
`cap`.

The subsequent source application chooses one such datum for each exponent
band `β_j`.  Its only remaining probabilistic input is the candidate-count
tail (Proposition 4.8 in the paper); the post-hit race input is discharged by
`Erdos1166HLOZLemma410PotentialRace`.
-/

namespace Erdos1166.HLOZLemma410SourceBands

open MeasureTheory Set
open scoped ENNReal BigOperators
open HLOZFoundation
open HLOZProp47Parameters
open HLOZPairing HLOZProp47SourceObjects HLOZProp47SourceAssembly

/-- Equality of distinguished domino endpoints for two distinct sites means
that the sites form the selected domino.  This is the concrete link between
the source `PairFree` history and the endpoint exclusion in (4.33). -/
theorem pairingRelation_of_distinguishedEndpoint_eq
    (i : Fin 6) (x y : Site) (hne : x ≠ y)
    (h : distinguishedEndpoint i x = distinguishedEndpoint i y) :
    pairingRelation i x y := by
  fin_cases i
  · by_cases hx : chessEven x <;> by_cases hy : chessEven y
    · simp only [distinguishedEndpoint, hx, hy, if_pos] at h
      exact (hne h).elim
    · left
      refine ⟨hx, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, east, west] at h ⊢
      omega
    · right
      refine ⟨hy, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, east, west] at h ⊢
      omega
    · simp only [distinguishedEndpoint, hx, hy, if_neg] at h
      exfalso
      apply hne
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, west] at h ⊢
      omega
  · by_cases hx : chessEven x <;> by_cases hy : chessEven y
    · simp only [distinguishedEndpoint, hx, hy, if_pos] at h
      exact (hne h).elim
    · left
      refine ⟨hx, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, north, south] at h ⊢
      omega
    · right
      refine ⟨hy, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, north, south] at h ⊢
      omega
    · simp only [distinguishedEndpoint, hx, hy, if_neg] at h
      exfalso
      apply hne
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, south] at h ⊢
      omega
  · by_cases hx : chessEven x <;> by_cases hy : chessEven y
    · simp only [distinguishedEndpoint, hx, hy, if_pos] at h
      exact (hne h).elim
    · left
      refine ⟨hx, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, east, west] at h ⊢
      omega
    · right
      refine ⟨hy, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, east, west] at h ⊢
      omega
    · simp only [distinguishedEndpoint, hx, hy, if_neg] at h
      exfalso
      apply hne
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, east] at h ⊢
      omega
  · by_cases hx : chessEven x <;> by_cases hy : chessEven y
    · simp only [distinguishedEndpoint, hx, hy, if_pos] at h
      exact (hne h).elim
    · left
      refine ⟨hx, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, north, south] at h ⊢
      omega
    · right
      refine ⟨hy, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, north, south] at h ⊢
      omega
    · simp only [distinguishedEndpoint, hx, hy, if_neg] at h
      exfalso
      apply hne
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, north] at h ⊢
      omega
  · by_cases hx : Even x.1 <;> by_cases hy : Even y.1
    · simp only [distinguishedEndpoint, hx, hy, if_pos] at h
      exact (hne h).elim
    · left
      refine ⟨hx, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, east, west] at h ⊢
      omega
    · right
      refine ⟨hy, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, east, west] at h ⊢
      omega
    · simp only [distinguishedEndpoint, hx, hy, if_neg] at h
      exfalso
      apply hne
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, west] at h ⊢
      omega
  · by_cases hx : Odd x.1 <;> by_cases hy : Odd y.1
    · simp only [distinguishedEndpoint, hx, hy, if_pos] at h
      exact (hne h).elim
    · left
      refine ⟨hx, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, east, west] at h ⊢
      omega
    · right
      refine ⟨hy, ?_⟩
      simp only [distinguishedEndpoint, hx, hy, if_pos, if_neg] at h
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, east, west] at h ⊢
      omega
    · simp only [distinguishedEndpoint, hx, hy, if_neg] at h
      exfalso
      apply hne
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp [shift, vec, west] at h ⊢
      omega

/-! ## The source `β_j` bands

For the concrete parameters in `HLOZProp47Parameters`, 454 bands suffice
uniformly for every `α ≤ κ₂`.  The `j`th `Fin 454` value below represents
the paper's band number `j+1`; `sourceBetaPrevious` is `β_j` in the lower
endpoint of its race count and `sourceBeta` is `β_{j+1}` in the candidate
threshold.
-/

abbrev SourceBetaBandIndex := Fin 454

noncomputable def sourceBetaStep (alpha : ℝ) : ℝ :=
  kappaOne - alpha - delta

noncomputable def sourceBetaNat (alpha : ℝ) (j : ℕ) : ℝ :=
  alpha + delta + (j : ℝ) * sourceBetaStep alpha

noncomputable def sourceBetaPrevious
    (alpha : ℝ) (j : SourceBetaBandIndex) : ℝ :=
  sourceBetaNat alpha j.1

noncomputable def sourceBeta
    (alpha : ℝ) (j : SourceBetaBandIndex) : ℝ :=
  sourceBetaNat alpha (j.1 + 1)

theorem sourceBetaStep_pos {alpha : ℝ} (halpha : alpha ≤ kappaTwo) :
    0 < sourceBetaStep alpha := by
  norm_num [sourceBetaStep, kappaOne, kappaTwo, delta] at halpha ⊢
  linarith

theorem sourceBeta_eq_previous_add
    (alpha : ℝ) (j : SourceBetaBandIndex) :
    sourceBeta alpha j = sourceBetaPrevious alpha j + sourceBetaStep alpha := by
  rw [sourceBeta, sourceBetaPrevious, sourceBetaNat, sourceBetaNat]
  push_cast
  ring

theorem sourceBetaPrevious_zero (alpha : ℝ) :
    sourceBetaPrevious alpha (0 : SourceBetaBandIndex) = alpha + delta := by
  simp [sourceBetaPrevious, sourceBetaNat]

/-- At the last uniform band, `β₄₅₄ ≥ 1`; this is the exact endpoint which
makes the real local-time bands cover every possible nonnegative local time. -/
theorem one_le_sourceBeta_last {alpha : ℝ} (halpha : alpha ≤ kappaTwo) :
    1 ≤ sourceBeta alpha (Fin.last 453) := by
  norm_num [sourceBeta, sourceBetaNat, sourceBetaStep,
    kappaOne, kappaTwo, delta] at halpha ⊢
  linarith

theorem sourceBetaNat_succ (alpha : ℝ) (j : ℕ) :
    sourceBetaNat alpha (j + 1) =
      sourceBetaNat alpha j + sourceBetaStep alpha := by
  rw [sourceBetaNat, sourceBetaNat]
  push_cast
  ring

/-- Elementary adjacent-band selection for a decreasing sequence of real
cutoffs. -/
theorem exists_adjacent_band {f : ℕ → ℝ} {N : ℕ} (hN : 0 < N)
    (hmono : ∀ j < N, f (j + 1) ≤ f j) {u : ℝ}
    (huTop : u ≤ f 0) (huBottom : f N ≤ u) :
    ∃ j < N, f (j + 1) ≤ u ∧ u ≤ f j := by
  induction N using Nat.strong_induction_on generalizing f u with
  | h N ih =>
      by_cases hfirst : f 1 ≤ u
      · exact ⟨0, hN, by simpa using hfirst, huTop⟩
      · have hN1 : 1 < N := by
          by_contra hnot
          have hNle : N ≤ 1 := Nat.le_of_not_gt hnot
          have hNeq : N = 1 := by omega
          subst N
          exact hfirst huBottom
        let g : ℕ → ℝ := fun j ↦ f (j + 1)
        have hgmono : ∀ j < N - 1, g (j + 1) ≤ g j := by
          intro j hj
          dsimp [g]
          simpa only [Nat.add_assoc] using hmono (j + 1) (by omega)
        have hgbottom : g (N - 1) ≤ u := by
          dsimp [g]
          rw [Nat.sub_add_cancel (by omega : 1 ≤ N)]
          exact huBottom
        obtain ⟨j, hj, hjlo, hjhi⟩ :=
          ih (N - 1) (by omega) (f := g) (u := u) (by omega) hgmono
            (le_of_lt (lt_of_not_ge hfirst)) hgbottom
        refine ⟨j + 1, by omega, ?_, ?_⟩
        · simpa only [g, Nat.add_assoc] using hjlo
        · exact hjhi

/-- Integer cutoff `m - ⌈m^β_j⌉` for the source candidate set `F_j`. -/
noncomputable def sourceBetaCandidateThreshold
    (m : ℕ) (alpha : ℝ) (j : SourceBetaBandIndex) : ℕ :=
  m - Nat.ceil ((m : ℝ) ^ sourceBeta alpha j)

/-- Integer race length `⌈m^β_{j-1}⌉-1`.  This is the largest uniform
integer which remains valid even when the upper real band endpoint is met
with equality. -/
noncomputable def sourceBetaRaceCount
    (m : ℕ) (alpha : ℝ) (j : SourceBetaBandIndex) : ℕ :=
  Nat.ceil ((m : ℝ) ^ sourceBetaPrevious alpha j) - 1

/-- Integer radius enclosing the source ball of radius `exp(m^α)`. -/
noncomputable def sourceLemma410Radius (m : ℕ) (alpha : ℝ) : ℕ :=
  Nat.ceil (Real.exp ((m : ℝ) ^ alpha))

/-- The exact finite lattice ball used for all candidate sets in one
Lemma‑4.10 application. -/
noncomputable def sourceLemma410Window (m : ℕ) (alpha : ℝ) :
    Site → Finset Site :=
  hlozLatticeBallSq ((sourceLemma410Radius m alpha) ^ 2)

theorem sourceLemma410Window_geometry (m : ℕ) (alpha : ℝ) :
    ∀ c x, x ∈ sourceLemma410Window m alpha c →
      siteSquaredDistance x c ≤ (sourceLemma410Radius m alpha) ^ 2 := by
  intro c x hx
  exact (Finset.mem_filter.mp hx).2

/-- A Euclidean distance bound places a lattice site in the concrete finite
window used in the source decomposition. -/
theorem mem_sourceLemma410Window_of_distance_le
    {m : ℕ} {alpha : ℝ} {c x : Site}
    (h : siteDistance x c ≤ Real.exp ((m : ℝ) ^ alpha)) :
    x ∈ sourceLemma410Window m alpha c := by
  let R := sourceLemma410Radius m alpha
  have hExpR : Real.exp ((m : ℝ) ^ alpha) ≤ (R : ℝ) := by
    exact Nat.le_ceil _
  have hdistR : siteDistance x c ≤ (R : ℝ) := h.trans hExpR
  have hsqReal : (siteSquaredDistance x c : ℝ) ≤ (R : ℝ) ^ 2 := by
    rw [siteDistance, Real.sqrt_le_iff] at hdistR
    exact hdistR.2
  have hsq : siteSquaredDistance x c ≤ R ^ 2 := by
    exact_mod_cast hsqReal
  have hcoord₁ : (x.1 - c.1).natAbs ≤ R ^ 2 := by
    refine (Nat.le_mul_self _).trans ?_
    apply le_trans ?_ hsq
    simp only [siteSquaredDistance, pow_two]
    omega
  have hcoord₂ : (x.2 - c.2).natAbs ≤ R ^ 2 := by
    refine (Nat.le_mul_self _).trans ?_
    apply le_trans ?_ hsq
    simp only [siteSquaredDistance, pow_two]
    omega
  have habs₁ : |x.1 - c.1| ≤ (R ^ 2 : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hcoord₁
  have habs₂ : |x.2 - c.2| ≤ (R ^ 2 : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hcoord₂
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_,
    Finset.mem_Icc.mpr ?_⟩, hsq⟩
  · rcases (abs_sub_le_iff.mp habs₁) with ⟨h₁, h₂⟩
    change c.1 - (R ^ 2 : ℤ) ≤ x.1 ∧ x.1 ≤ c.1 + (R ^ 2 : ℤ)
    omega
  · rcases (abs_sub_le_iff.mp habs₂) with ⟨h₁, h₂⟩
    change c.2 - (R ^ 2 : ℤ) ≤ x.2 ∧ x.2 ≤ c.2 + (R ^ 2 : ℤ)
    omega

/-- Local time, being integer-valued and changing by at most one per time
step, assumes every intermediate post-time increment. -/
theorem exists_time_with_localTime_sub_eq
    (s : ℕ → Site) (x : Site) {l u q : ℕ} (hlu : l ≤ u)
    (hq : q ≤ localTime s u x - localTime s l x) :
    ∃ n ∈ Finset.Icc l u,
      localTime s n x - localTime s l x = q := by
  induction u generalizing q with
  | zero =>
      have hl : l = 0 := by omega
      subst l
      refine ⟨0, by simp, ?_⟩
      omega
  | succ u ih =>
      by_cases hlu' : l ≤ u
      · by_cases hq' : q ≤ localTime s u x - localTime s l x
        · obtain ⟨n, hn, heq⟩ := ih hlu' hq'
          exact ⟨n, Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans
              (Nat.le_succ u)⟩, heq⟩
        · refine ⟨u + 1, by simp [hlu], ?_⟩
          have hmono := localTime_mono (s := s) hlu' x
          have hmonoSucc := localTime_mono (s := s) hlu x
          rw [localTime_succ] at hq ⊢
          split_ifs at hq ⊢ <;> omega
      · have hl : l = u + 1 := by omega
        subst l
        refine ⟨u + 1, by simp, ?_⟩
        omega

/-- Pair-freeness of the first `k+1` creation sites excludes the next site
from every domino represented by the first `k` sites. -/
theorem distinguishedEndpoint_nextCreation_not_mem
    (s : ℕ → Site) (m k : ℕ) (i : Fin 6)
    (hm : 0 < m) (hk : 0 < k)
    (hnextfinite : firstKSitesReachLevel m (k + 1) s ≠ ⊤)
    (hfree : PairFree (pairingRelation i)
      (levelCreationSitesUpTo s m (k + 1))) :
    distinguishedEndpoint i (levelCreationSite s m (k + 1)) ∉
      creationDominoEndpoints i s m k := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨j, hj, hend⟩
  have hjIcc := Finset.mem_Icc.mp hj
  have hjpos : 0 < j := by omega
  have hjlt : j < k + 1 := by omega
  have hne : levelCreationSite s m j ≠ levelCreationSite s m (k + 1) :=
    levelCreationSite_ne_of_lt s m hm hjpos hjlt hnextfinite
  have hjmem : levelCreationSite s m j ∈
      levelCreationSitesUpTo s m (k + 1) := by
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  have hnextmem : levelCreationSite s m (k + 1) ∈
      levelCreationSitesUpTo s m (k + 1) := by
    apply Finset.mem_image.mpr
    exact ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, rfl⟩
  exact (hfree _ hjmem _ hnextmem hne)
    (pairingRelation_of_distinguishedEndpoint_eq i _ _ hne hend)

/-- Before its creation threshold, the next creation site is still below
level `m`. -/
theorem nextCreation_localTime_lt_at_previous
    (s : ℕ → Site) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hnextfinite : firstKSitesReachLevel m (k + 1) s ≠ ⊤) :
    localTime s (firstKSitesReachLevel m k s).untopA
      (levelCreationSite s m (k + 1)) < m := by
  have hkfinite : firstKSitesReachLevel m k s ≠ ⊤ := by
    exact ne_top_of_le_ne_top hnextfinite
      (firstKSitesReachLevel_mono_k s m (Nat.le_succ k))
  let t := (firstKSitesReachLevel m k s).untopA
  let x := levelCreationSite s m (k + 1)
  by_contra hnot
  change ¬localTime s t x < m at hnot
  have hmle : m ≤ localTime s t x := by omega
  have hxvisited : x ∈ visitedSites s t := by
    by_contra hx
    have hz := localTime_eq_zero_of_not_mem_visitedSites hx
    omega
  have hxlevel : x ∈ sitesAtLeastLevel s t m :=
    Finset.mem_filter.mpr ⟨hxvisited, hmle⟩
  have hsites := sitesAtLeastLevel_at_threshold_eq_creationSites
    s m k hm hk hkfinite
  rw [hsites] at hxlevel
  rcases Finset.mem_image.mp hxlevel with ⟨j, hj, heq⟩
  have hjIcc := Finset.mem_Icc.mp hj
  have hne := levelCreationSite_ne_of_lt s m hm (by omega : 0 < j)
    (by omega : j < k + 1) hnextfinite
  exact hne heq

/-- If all the non-cutoff clauses of `M^k(m,β)` hold but the next creation
site is absent, its old local time lies below the real cutoff. -/
theorem nextCreation_localTime_le_cutoff_of_not_nearFavorite
    (s : ℕ → Site) (m k : ℕ) (i : Fin 6) (beta : ℝ)
    (hm : 2 ≤ m) (hbeta : beta ≤ 1)
    (hkfinite : firstKSitesReachLevel m k s ≠ ⊤)
    (hend : distinguishedEndpoint i (levelCreationSite s m (k + 1)) ∉
      creationDominoEndpoints i s m k)
    (hlt : localTime s (firstKSitesReachLevel m k s).untopA
      (levelCreationSite s m (k + 1)) < m)
    (hnot : levelCreationSite s m (k + 1) ∉
      nearFavoriteSites i s m k beta) :
    (localTime s (firstKSitesReachLevel m k s).untopA
        (levelCreationSite s m (k + 1)) : ℝ) ≤
      (m : ℝ) - (m : ℝ) ^ beta := by
  let t := (firstKSitesReachLevel m k s).untopA
  let x := levelCreationSite s m (k + 1)
  change (localTime s t x : ℝ) ≤ (m : ℝ) - (m : ℝ) ^ beta
  have hmone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hpLe : (m : ℝ) ^ beta ≤ (m : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hmone hbeta
  by_cases hzero : localTime s t x = 0
  · rw [hzero]
    norm_num
    linarith
  · have hxvisited : x ∈ visitedSites s t := by
      by_contra hx
      exact hzero (localTime_eq_zero_of_not_mem_visitedSites hx)
    by_contra hcut
    apply hnot
    apply Finset.mem_filter.mpr
    refine ⟨hxvisited, hkfinite, hend, ?_, ?_⟩
    · exact lt_of_not_ge hcut
    · have hlt' : localTime s (directCreationTime m k s) x < m := by
        simpa [directCreationTime, t, x] using hlt
      exact_mod_cast hlt'

/-- At the first post-threshold hit of a site different from the threshold
position, local time has increased by exactly one. -/
theorem localTime_candidateFirstHitAfter_eq_add_one
    (s : ℕ → Site) (τ : (ℕ → Site) → WithTop ℕ) (x : Site)
    (hτfinite : τ s ≠ ⊤) (hxstart : s (τ s).untopA ≠ x)
    (hHfinite : candidateFirstHitAfter τ x s ≠ ⊤) :
    localTime s (candidateFirstHitAfter τ x s).untopA x =
      localTime s (τ s).untopA x + 1 := by
  let t := (τ s).untopA
  let H := candidateFirstHitAfter τ x s
  let h := H.untopA
  have hHdef : H = postHitSiteTime x t s := by
    simp [H, candidateFirstHitAfter, hτfinite, t]
  have hHcoe : (h : WithTop ℕ) = H := by
    dsimp only [h]
    rw [WithTop.untopA_eq_untop hHfinite]
    exact WithTop.coe_untop _ hHfinite
  have hth : t ≤ h := by
    apply WithTop.coe_le_coe.mp
    exact (le_hittingAfter s).trans_eq (hHdef.symm.trans hHcoe.symm)
  have hxAtH : s h = x := by
    have hpostfinite : postHitSiteTime x t s ≠ ⊤ := by
      rw [← hHdef]
      exact hHfinite
    have hxmem := hittingAfter_mem_set_of_ne_top
      (u := HLOZFoundation.coordinateProcess) (s := ({x} : Set Site))
      (n := t) (ω := s) hpostfinite
    change s (postHitSiteTime x t s).untopA = x at hxmem
    have hu : (postHitSiteTime x t s).untopA = h := by
      rw [← hHdef, ← hHcoe]
      rfl
    simpa [hu] using hxmem
  have htlth : t < h := by
    apply lt_of_le_of_ne hth
    intro heq
    apply hxstart
    simpa [t, heq] using hxAtH
  have hbefore : localTime s (h - 1) x = localTime s t x := by
    apply localTime_eq_of_avoid_Ioc s x (by omega)
    intro n htn hnh hnx
    have hnH : (n : WithTop ℕ) < postHitSiteTime x t s := by
      rw [← hHdef, ← hHcoe]
      exact WithTop.coe_lt_coe.mpr (show n < h by omega)
    exact notMem_of_lt_hittingAfter hnH (le_of_lt htn)
      (by simpa [HLOZFoundation.coordinateProcess] using hnx)
  have hpos : 0 < h := by omega
  obtain ⟨h', hh⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  change localTime s h x = localTime s t x + 1
  have hxAtH' : s (h' + 1) = x := by simpa [hh] using hxAtH
  have hbefore' : localTime s h' x = localTime s t x := by
    simpa [hh] using hbefore
  rw [hh, localTime_succ, if_pos hxAtH', hbefore']

theorem source_siteDistance_comm (x y : Site) :
    siteDistance x y = siteDistance y x := by
  unfold siteDistance siteSquaredDistance
  have h₁ : (x.1 - y.1).natAbs = (y.1 - x.1).natAbs := by
    rw [show x.1 - y.1 = -(y.1 - x.1) by ring, Int.natAbs_neg]
  have h₂ : (x.2 - y.2).natAbs = (y.2 - x.2).natAbs := by
    rw [show x.2 - y.2 = -(y.2 - x.2) by ring, Int.natAbs_neg]
  rw [h₁, h₂]

/-- Deterministic `B_j ⊆ B'_j` step in the proof of HLOZ Lemma 4.10: a
failure of the initial near-favourite screen belongs to one of the 454
source events `B'_j`.
The proof selects the adjacent real local-time band, rounds its two
endpoints in the safe directions, and uses `U_m^{k+1}` to turn the remaining
visits to the next creation site into the post-hit race. -/
theorem lemma410FailureEvent_subset_sourceBetaBand_cover
    (m : ℕ) (i : Fin 6) (r : StageIndex) (alpha : ℝ)
    (hm : 2 ≤ m) (halpha : alpha ≤ kappaTwo) :
    lemma410FailureEvent m i r alpha ⊆
      ⋃ j : SourceBetaBandIndex,
        hlozLemma410BPrimeEvent (sourceLemma410Window m alpha)
          m (stageNumber r)
          (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j) ∩
        prefixPairingEvent m i (stageNumber r + 1) := by
  intro s hs
  rcases hs with ⟨⟨⟨hprefix, havoid⟩, hbin⟩, hnot⟩
  let k := stageNumber r
  let Tk := firstKSitesReachLevel m k s
  let Tnext := firstKSitesReachLevel m (k + 1) s
  let t := Tk.untopA
  let u := Tnext.untopA
  let x := levelCreationSite s m (k + 1)
  let y := levelCreationSite s m k
  let L := localTime s t x
  have hk : 0 < k := by dsimp [k, stageNumber]; omega
  have hkfinite : Tk ≠ ⊤ := by simpa [Tk, k] using hbin.1
  have hnextfinite : Tnext ≠ ⊤ := by simpa [Tnext, k] using hbin.2.1
  have hfree : PairFree (pairingRelation i)
      (levelCreationSitesUpTo s m (k + 1)) := by
    simpa [prefixPairingEvent, k] using hprefix.2
  have hend : distinguishedEndpoint i x ∉ creationDominoEndpoints i s m k := by
    simpa [x] using distinguishedEndpoint_nextCreation_not_mem
      s m k i (by omega) hk hnextfinite hfree
  have hlt : L < m := by
    simpa [L, t, Tk, x] using nextCreation_localTime_lt_at_previous
      s m k (by omega) hk hnextfinite
  have hbeta0 : alpha + delta ≤ 1 := by
    norm_num [kappaTwo, delta] at halpha ⊢
    linarith
  have hcut : (L : ℝ) ≤ (m : ℝ) - (m : ℝ) ^ (alpha + delta) := by
    apply nextCreation_localTime_le_cutoff_of_not_nearFavorite
      s m k i (alpha + delta) hm hbeta0 hkfinite hend hlt
    simpa [nextCreationIsCandidateEvent, k, x] using hnot
  let f : ℕ → ℝ := fun j ↦
    (m : ℝ) - (m : ℝ) ^ sourceBetaNat alpha j
  have hmone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hfmono : ∀ j < 454, f (j + 1) ≤ f j := by
    intro j _hj
    have hexp : sourceBetaNat alpha j ≤ sourceBetaNat alpha (j + 1) := by
      rw [sourceBetaNat_succ]
      linarith [sourceBetaStep_pos halpha]
    have hp := Real.rpow_le_rpow_of_exponent_le hmone hexp
    dsimp [f]
    linarith
  have hfTop : (L : ℝ) ≤ f 0 := by
    simpa [f, sourceBetaNat] using hcut
  have hbetaLast : 1 ≤ sourceBetaNat alpha 454 := by
    simpa [sourceBeta, sourceBetaNat] using one_le_sourceBeta_last halpha
  have hpowLast : (m : ℝ) ≤ (m : ℝ) ^ sourceBetaNat alpha 454 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hmone hbetaLast
  have hfBottom : f 454 ≤ (L : ℝ) := by
    dsimp [f]
    have hLnonneg : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith
  obtain ⟨j, hj, hjlow, hjhigh⟩ :=
    exists_adjacent_band (f := f) (N := 454) (by omega) hfmono hfTop hfBottom
  let J : SourceBetaBandIndex := ⟨j, hj⟩
  apply Set.mem_iUnion_of_mem J
  refine ⟨?_, hprefix⟩
  have hBandLow : (m : ℝ) - (m : ℝ) ^ sourceBeta alpha J ≤ (L : ℝ) := by
    simpa [f, sourceBeta, J] using hjlow
  have hBandHigh : (L : ℝ) ≤
      (m : ℝ) - (m : ℝ) ^ sourceBetaPrevious alpha J := by
    simpa [f, sourceBetaPrevious, J] using hjhigh
  have hwindow : x ∈ sourceLemma410Window m alpha y := by
    apply mem_sourceLemma410Window_of_distance_le
    rw [source_siteDistance_comm]
    simpa [x, y, k, distanceBinUpper] using hbin.2.2.2
  have hcandidate : sourceBetaCandidateThreshold m alpha J ≤ L := by
    have hpceil : (m : ℝ) ^ sourceBeta alpha J ≤
        (Nat.ceil ((m : ℝ) ^ sourceBeta alpha J) : ℝ) := Nat.le_ceil _
    have hmReal : (m : ℝ) ≤
        (L : ℝ) + Nat.ceil ((m : ℝ) ^ sourceBeta alpha J) := by
      linarith
    have hmNat : m ≤ L + Nat.ceil ((m : ℝ) ^ sourceBeta alpha J) := by
      exact_mod_cast hmReal
    unfold sourceBetaCandidateThreshold
    omega
  have hxF : x ∈ hlozCandidateSitesAtTime (sourceLemma410Window m alpha)
      s t (sourceBetaCandidateThreshold m alpha J) :=
    Finset.mem_filter.mpr ⟨hwindow, hcandidate⟩
  have hTkCoe : (t : WithTop ℕ) = Tk := by
    dsimp [t]
    rw [WithTop.untopA_eq_untop hkfinite]
    exact WithTop.coe_untop _ hkfinite
  have hnextCoe : (u : WithTop ℕ) = Tnext := by
    dsimp [u]
    rw [WithTop.untopA_eq_untop hnextfinite]
    exact WithTop.coe_untop _ hnextfinite
  have htu : t ≤ u := by
    apply WithTop.coe_le_coe.mp
    exact hTkCoe.trans_le ((firstKSitesReachLevel_mono_k s m
      (Nat.le_succ k)).trans_eq hnextCoe.symm)
  have hxy : y ≠ x := by
    exact levelCreationSite_ne_of_lt s m (by omega) hk
      (Nat.lt_succ_self k) hnextfinite
  have hxstart : s t ≠ x := by
    simpa [t, Tk, y, levelCreationSite] using hxy
  let sigma := candidateFirstHitAfter (firstKSitesReachLevel m k) x
  have hsigmafinite : sigma s ≠ ⊤ := by
    have hle : postHitSiteTime x t s ≤ (u : WithTop ℕ) := by
      apply hittingAfter_le_of_mem htu
      change s u = x
      rfl
    have hpfinite : postHitSiteTime x t s ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) hle
    simpa [sigma, candidateFirstHitAfter, hkfinite, t, Tk] using hpfinite
  let v := (sigma s).untopA
  have hsigmaLe : sigma s ≤ (u : WithTop ℕ) := by
    have hle : postHitSiteTime x t s ≤ (u : WithTop ℕ) := by
      apply hittingAfter_le_of_mem htu
      change s u = x
      rfl
    simpa [sigma, candidateFirstHitAfter, hkfinite, t, Tk] using hle
  have hvu : v ≤ u := by
    have hvcoe : (v : WithTop ℕ) = sigma s := by
      dsimp [v]
      rw [WithTop.untopA_eq_untop hsigmafinite]
      exact WithTop.coe_untop _ hsigmafinite
    exact WithTop.coe_le_coe.mp (hvcoe.trans_le hsigmaLe)
  have hxAtSigma : s v = x := by
    have hpostfinite : postHitSiteTime x t s ≠ ⊤ := by
      simpa [sigma, candidateFirstHitAfter, hkfinite, t, Tk] using hsigmafinite
    have hxmem := hittingAfter_mem_set_of_ne_top
      (u := HLOZFoundation.coordinateProcess) (s := ({x} : Set Site))
      (n := t) (ω := s) hpostfinite
    change s (postHitSiteTime x t s).untopA = x at hxmem
    have heq : postHitSiteTime x t s = sigma s := by
      simp [sigma, candidateFirstHitAfter, hkfinite, t, Tk]
    simpa [v, heq] using hxmem
  have hvlocal : localTime s v x = L + 1 := by
    simpa [v, sigma, L, t, Tk] using
      localTime_candidateFirstHitAfter_eq_add_one s
        (firstKSitesReachLevel m k) x hkfinite hxstart hsigmafinite
  have hnextLocal : localTime s u x = m := by
    simpa [u, Tnext, x] using levelCreationSite_localTime_eq
      s m (k + 1) (by omega) (by omega) hnextfinite
  let q := sourceBetaRaceCount m alpha J
  have hpPos : 0 < (m : ℝ) ^ sourceBetaPrevious alpha J := by positivity
  have hceilPos : 0 < Nat.ceil ((m : ℝ) ^ sourceBetaPrevious alpha J) :=
    Nat.ceil_pos.mpr hpPos
  have hLceil : L + Nat.ceil ((m : ℝ) ^ sourceBetaPrevious alpha J) ≤ m := by
    have hLm : L ≤ m := by omega
    have hpDiff : (m : ℝ) ^ sourceBetaPrevious alpha J ≤ (m - L : ℕ) := by
      rw [Nat.cast_sub hLm]
      linarith
    have hc : Nat.ceil ((m : ℝ) ^ sourceBetaPrevious alpha J) ≤ m - L :=
      Nat.ceil_le.mpr hpDiff
    omega
  have hqInc : q ≤ localTime s u x - localTime s v x := by
    dsimp [q, sourceBetaRaceCount]
    rw [hnextLocal, hvlocal]
    omega
  obtain ⟨n, hn, hnlocal⟩ := exists_time_with_localTime_sub_eq
    s x hvu hqInc
  have hpostLe : postNthHitTime x q v s ≤ (u : WithTop ℕ) := by
    calc
      postNthHitTime x q v s ≤ (n : WithTop ℕ) := by
        apply hittingAfter_le_of_mem (Finset.mem_Icc.mp hn).1
        simpa only [Set.mem_singleton_iff] using hnlocal
      _ ≤ (u : WithTop ℕ) := WithTop.coe_le_coe.mpr (Finset.mem_Icc.mp hn).2
  have hvgt : t < v := by
    have hvlocal' := hvlocal
    by_contra hnotv
    have hvt : v ≤ t := by omega
    have hmono := localTime_mono (s := s) hvt x
    omega
  have htargetGt : (u : WithTop ℕ) < postHitSiteTime y v s := by
    by_contra hnotgt
    have hle : postHitSiteTime y v s ≤ (u : WithTop ℕ) := by
      simpa only [not_lt] using hnotgt
    obtain ⟨n, hnIcc, hny⟩ := (hittingAfter_le_iff
      (u := HLOZFoundation.coordinateProcess) (s := ({y} : Set Site))
      (n := v) (ω := s) (i := u)).mp hle
    have htn : t < n := hvgt.trans_le hnIcc.1
    have havoidK : s ∈ hlozDirectAvoidanceEvent m (k + 1) := by
      simpa [k] using havoid
    apply havoidK n
      (by change Tk < (n : WithTop ℕ); rw [← hTkCoe];
          exact WithTop.coe_lt_coe.mpr htn)
      (by change (n : WithTop ℕ) ≤ Tnext; rw [← hnextCoe];
          exact WithTop.coe_le_coe.mpr hnIcc.2)
      k (by omega) (by omega)
    simpa [HLOZFoundation.coordinateProcess, y] using hny
  refine ⟨?_, ?_, ?_⟩
  · simpa [k] using hprefix.1
  · simpa [t, Tk, x] using hxF
  · refine ⟨hsigmafinite, ?_⟩
    simpa [sigma, v, x, y, k, hxAtSigma] using
      hpostLe.trans_lt htargetGt

/-- The concrete unconditional race bound supplied by the planar potential
kernel at the source radius. -/
noncomputable def sourceBetaRaceBound
    (m : ℕ) (alpha : ℝ) (j : SourceBetaBandIndex) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-((sourceBetaRaceCount m alpha j : ℝ) *
    (1 / (24 * Real.log (sourceLemma410Radius m alpha))))))

/-- The exceptional event on which the source candidate set `F_j` has more
than the deterministic cap used in the finite union bound. -/
def hlozCandidateCapFailureEvent (window : Site → Finset Site)
    (m k qCandidate cap : ℕ) : Set (ℕ → Site) :=
  {s | cap < (hlozCandidateSitesAtTime window s
    (firstKSitesReachLevel m k s).untopA qCandidate).card}

/-- Outside the candidate-cap failure event, the countable stopping-time
union in HLOZ Lemma 4.10 truncates at `cap`. -/
theorem hlozLemma410BPrimeEvent_inter_subset_capFailure_union_finset
    (window : Site → Finset Site) (m k qCandidate qRace cap : ℕ)
    (hm : 0 < m) (hk : 0 < k) (P : Set (ℕ → Site)) :
    hlozLemma410BPrimeEvent window m k qCandidate qRace ∩ P ⊆
      (hlozCandidateCapFailureEvent window m k qCandidate cap ∩ P) ∪
        ⋃ i ∈ Finset.Icc 1 cap,
          (hlozPostHitRaceEvent m k
              (hlozSigma window m k qCandidate i) qRace ∩
            hlozThresholdTimeEventK m k ∩ P) := by
  intro s hs
  have hall := hlozLemma410BPrimeEvent_inter_subset_iUnion
    window m k qCandidate qRace hm hk P hs
  simp only [Set.mem_iUnion] at hall
  rcases hall with ⟨i, hi, hAi⟩
  by_cases hcap : cap < (hlozCandidateSitesAtTime window s
      (firstKSitesReachLevel m k s).untopA qCandidate).card
  · exact Or.inl ⟨hcap, hs.2⟩
  · apply Or.inr
    have hcardCap : (hlozCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA qCandidate).card ≤ cap :=
      Nat.le_of_not_gt hcap
    have hiCard : i ≤ (hlozCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA qCandidate).card := by
      by_contra hnot
      have htop := hlozCandidateTime_eq_top_of_card_lt
        (τ := firstKSitesReachLevel m k) (window := window)
        (q := qCandidate) (i := i) (s := s)
        (ne_top_of_lt hAi.1.2) (Nat.lt_of_not_ge hnot)
      exact hAi.1.1.1 htop
    apply Set.mem_iUnion_of_mem i
    apply Set.mem_iUnion_of_mem (Finset.mem_Icc.mpr
      ⟨hi, hiCard.trans hcardCap⟩)
    exact hAi

/-- Probability form of the finite-candidate union step.  It requires no
independence: the candidate-count tail is separated by a union bound, and
every one of the remaining `cap` races is bounded uniformly. -/
theorem measure_hlozLemma410BPrimeEvent_inter_le_capFailure_add
    (μ : Measure (ℕ → Site))
    (window : Site → Finset Site) (m k qCandidate qRace cap : ℕ)
    (hm : 0 < m) (hk : 0 < k) (P : Set (ℕ → Site)) (raceBound : ℝ≥0∞)
    (hrace : HasHLOZLemma410PostHitRaceEstimate μ window
      m k qCandidate qRace (fun _ ↦ raceBound)) :
    μ (hlozLemma410BPrimeEvent window m k qCandidate qRace ∩ P) ≤
      μ (hlozCandidateCapFailureEvent window m k qCandidate cap ∩ P) +
        cap * raceBound := by
  calc
    μ (hlozLemma410BPrimeEvent window m k qCandidate qRace ∩ P) ≤
        μ ((hlozCandidateCapFailureEvent window m k qCandidate cap ∩ P) ∪
          ⋃ i ∈ Finset.Icc 1 cap,
            (hlozPostHitRaceEvent m k
                (hlozSigma window m k qCandidate i) qRace ∩
              hlozThresholdTimeEventK m k ∩ P)) :=
      measure_mono (hlozLemma410BPrimeEvent_inter_subset_capFailure_union_finset
        window m k qCandidate qRace cap hm hk P)
    _ ≤ μ (hlozCandidateCapFailureEvent window m k qCandidate cap ∩ P) +
        μ (⋃ i ∈ Finset.Icc 1 cap,
          (hlozPostHitRaceEvent m k
              (hlozSigma window m k qCandidate i) qRace ∩
            hlozThresholdTimeEventK m k ∩ P)) := measure_union_le _ _
    _ ≤ μ (hlozCandidateCapFailureEvent window m k qCandidate cap ∩ P) +
        ∑ i ∈ Finset.Icc 1 cap,
          μ (hlozPostHitRaceEvent m k
              (hlozSigma window m k qCandidate i) qRace ∩
            hlozThresholdTimeEventK m k ∩ P) := by
      gcongr
      exact measure_biUnion_finset_le _ _
    _ ≤ μ (hlozCandidateCapFailureEvent window m k qCandidate cap ∩ P) +
        ∑ _i ∈ Finset.Icc 1 cap, raceBound := by
      gcongr with i hi
      calc
        μ (hlozPostHitRaceEvent m k
              (hlozSigma window m k qCandidate i) qRace ∩
            hlozThresholdTimeEventK m k ∩ P) ≤
            μ (hlozPostHitRaceEvent m k
              (hlozSigma window m k qCandidate i) qRace) := by
          exact measure_mono (by intro s hs; exact hs.1.1)
        _ ≤ raceBound := hrace i (Finset.mem_Icc.mp hi).1
    _ = μ (hlozCandidateCapFailureEvent window m k qCandidate cap ∩ P) +
        cap * raceBound := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Nat.card_Icc]
      rfl

/-- The finite `β_j`-band union in probability form.  The hypothesis
`hcover` is the deterministic partition into the paper's events `B'_j`;
`hcap` is precisely the candidate-cardinality tail supplied by Proposition
4.8; and `hrace` is the strong-Markov race estimate. -/
theorem measure_le_sum_candidateCapTail_add_race_of_band_cover
    {ι : Type*} [Fintype ι]
    (μ : Measure (ℕ → Site)) (E P : Set (ℕ → Site))
    (window : ι → Site → Finset Site)
    (m k : ℕ) (qCandidate qRace cap : ι → ℕ)
    (raceBound capTail : ι → ℝ≥0∞)
    (hm : 0 < m) (hk : 0 < k)
    (hcover : E ⊆ ⋃ j : ι,
      hlozLemma410BPrimeEvent (window j) m k
        (qCandidate j) (qRace j) ∩ P)
    (hrace : ∀ j,
      HasHLOZLemma410PostHitRaceEstimate μ (window j)
        m k (qCandidate j) (qRace j) (fun _ ↦ raceBound j))
    (hcap : ∀ j,
      μ (hlozCandidateCapFailureEvent (window j) m k
        (qCandidate j) (cap j) ∩ P) ≤ capTail j) :
    μ E ≤ ∑ j : ι, (capTail j + cap j * raceBound j) := by
  calc
    μ E ≤ μ (⋃ j : ι,
        hlozLemma410BPrimeEvent (window j) m k
          (qCandidate j) (qRace j) ∩ P) := measure_mono hcover
    _ ≤ ∑ j : ι, μ (hlozLemma410BPrimeEvent (window j) m k
          (qCandidate j) (qRace j) ∩ P) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ j : ι,
        (μ (hlozCandidateCapFailureEvent (window j) m k
            (qCandidate j) (cap j) ∩ P) + cap j * raceBound j) := by
      gcongr with j
      exact measure_hlozLemma410BPrimeEvent_inter_le_capFailure_add
        μ (window j) m k (qCandidate j) (qRace j) (cap j)
        hm hk P (raceBound j) (hrace j)
    _ ≤ ∑ j : ι, (capTail j + cap j * raceBound j) := by
      gcongr with j
      exact hcap j

end Erdos1166.HLOZLemma410SourceBands
