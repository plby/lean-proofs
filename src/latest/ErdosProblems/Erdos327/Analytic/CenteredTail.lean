import ErdosProblems.Erdos327.Analytic.CutoffMoment
import ErdosProblems.Erdos327.Analytic.Regularity

/-!
# Centered maximal tails

Finite-cutoff exponential Markov bounds and the grid reduction used for
centered prime-factor regularity.
-/

namespace Erdos327.Analytic

open Finset Real

/-- Integers up to `Y` violating the centered threshold at one fixed
cutoff `X`. -/
noncomputable def fixedCutoffExceptional
    (L X Y : ℕ) (A K : ℝ) : Finset ℕ :=
  (Icc 1 Y).filter fun n ↦
    A * log (log X / log L) + K <
      (primeFactorCountBetween L X n : ℝ)

/-- Full-rough integers violating the threshold at one cutoff. -/
noncomputable def fixedCutoffRoughExceptional
    (L X Y : ℕ) (A K : ℝ) : Finset ℕ :=
  (Icc 1 Y).filter fun n ↦
    Rough L n ∧
      A * log (log X / log L) + K <
        (primeFactorCountBetween L X n : ℝ)

/-- Odd-rough integers violating the threshold at one cutoff. -/
noncomputable def fixedCutoffOddRoughExceptional
    (L X Y : ℕ) (A K : ℝ) : Finset ℕ :=
  (Icc 1 Y).filter fun n ↦
    OddRough L n ∧
      A * log (log X / log L) + K <
        (primeFactorCountBetween L X n : ℝ)

/-- Exponential Markov inequality for a finite family of natural-valued
statistics. -/
theorem card_filter_lt_natStat_mul_rpow_le_sum
    {s : Finset ℕ} {f : ℕ → ℕ} {B z : ℝ}
    (hz : 1 ≤ z) :
    (((s.filter fun n ↦ B < (f n : ℝ)).card : ℕ) : ℝ) * z ^ B ≤
      ∑ n ∈ s, z ^ f n := by
  let t := s.filter fun n ↦ B < (f n : ℝ)
  have hterm (n : ℕ) (hn : n ∈ t) :
      z ^ B ≤ z ^ f n := by
    have hnB : B ≤ (f n : ℝ) :=
      (mem_filter.mp hn).2.le
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hz hnB
  calc
    (((t.card : ℕ) : ℝ) * z ^ B)
        = ∑ n ∈ t, z ^ B := by simp
    _ ≤ ∑ n ∈ t, z ^ f n :=
      sum_le_sum fun n hn ↦ hterm n hn
    _ ≤ ∑ n ∈ s, z ^ f n := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro n hnS hnT
      positivity

theorem card_filter_lt_natStat_le_sum_div_rpow
    {s : Finset ℕ} {f : ℕ → ℕ} {B z : ℝ}
    (hz : 1 ≤ z) :
    (((s.filter fun n ↦ B < (f n : ℝ)).card : ℕ) : ℝ) ≤
      (∑ n ∈ s, z ^ f n) / z ^ B := by
  have hzpos : 0 < z := zero_lt_one.trans_le hz
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hzpos B)).2
    (card_filter_lt_natStat_mul_rpow_le_sum hz)

/-- Fixed-cutoff unrestricted Markov bound, with the moment left in exact
finite-sum form. -/
theorem card_fixedCutoffExceptional_le_moment
    {L X Y : ℕ} {A K z : ℝ} (hz : 1 ≤ z) :
    ((fixedCutoffExceptional L X Y A K).card : ℝ) ≤
      (∑ n ∈ Icc 1 Y,
          z ^ primeFactorCountBetween L X n) /
        z ^ (A * log (log X / log L) + K) := by
  exact card_filter_lt_natStat_le_sum_div_rpow hz

/-- Fixed-cutoff full-rough Markov bound. -/
theorem card_fixedCutoffRoughExceptional_le_moment
    {L X Y : ℕ} {A K z : ℝ} (hz : 1 ≤ z) :
    ((fixedCutoffRoughExceptional L X Y A K).card : ℝ) ≤
      (∑ n ∈ Icc 1 Y,
          if Rough L n then
            z ^ primeFactorCountBetween L X n else 0) /
        z ^ (A * log (log X / log L) + K) := by
  let s := (Icc 1 Y).filter (Rough L)
  have hs :
      fixedCutoffRoughExceptional L X Y A K =
        s.filter (fun n ↦
          A * log (log X / log L) + K <
            (primeFactorCountBetween L X n : ℝ)) := by
    ext n
    simp [fixedCutoffRoughExceptional, s, and_left_comm,
      and_assoc]
  rw [hs]
  have hmarkov :=
    card_filter_lt_natStat_le_sum_div_rpow
      (s := s) (f := primeFactorCountBetween L X)
      (B := A * log (log X / log L) + K) hz
  calc
    (((s.filter fun n ↦
        A * log (log X / log L) + K <
          (primeFactorCountBetween L X n : ℝ)).card : ℕ) : ℝ)
        ≤ (∑ n ∈ s, z ^ primeFactorCountBetween L X n) /
            z ^ (A * log (log X / log L) + K) :=
      hmarkov
    _ = (∑ n ∈ Icc 1 Y,
          if Rough L n then
            z ^ primeFactorCountBetween L X n else 0) /
        z ^ (A * log (log X / log L) + K) := by
      congr 1
      rw [sum_filter]

/-- Fixed-cutoff odd-rough Markov bound. -/
theorem card_fixedCutoffOddRoughExceptional_le_moment
    {L X Y : ℕ} {A K z : ℝ} (hz : 1 ≤ z) :
    ((fixedCutoffOddRoughExceptional L X Y A K).card : ℝ) ≤
      (∑ n ∈ Icc 1 Y,
          if OddRough L n then
            z ^ primeFactorCountBetween L X n else 0) /
        z ^ (A * log (log X / log L) + K) := by
  let s := (Icc 1 Y).filter (OddRough L)
  have hs :
      fixedCutoffOddRoughExceptional L X Y A K =
        s.filter (fun n ↦
          A * log (log X / log L) + K <
            (primeFactorCountBetween L X n : ℝ)) := by
    ext n
    simp [fixedCutoffOddRoughExceptional, s, and_left_comm,
      and_assoc]
  rw [hs]
  have hmarkov :=
    card_filter_lt_natStat_le_sum_div_rpow
      (s := s) (f := primeFactorCountBetween L X)
      (B := A * log (log X / log L) + K) hz
  calc
    (((s.filter fun n ↦
        A * log (log X / log L) + K <
          (primeFactorCountBetween L X n : ℝ)).card : ℕ) : ℝ)
        ≤ (∑ n ∈ s, z ^ primeFactorCountBetween L X n) /
            z ^ (A * log (log X / log L) + K) :=
      hmarkov
    _ = (∑ n ∈ Icc 1 Y,
          if OddRough L n then
            z ^ primeFactorCountBetween L X n else 0) /
        z ^ (A * log (log X / log L) + K) := by
      congr 1
      rw [sum_filter]

/-- Fixed-cutoff unrestricted estimate after inserting the uniform
cutoff moment. -/
theorem card_fixedCutoffExceptional_le_mertens
    {L X Y : ℕ} {A K z : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hz1 : 1 ≤ z) (hz52 : z ≤ 5 / 2) :
    ((fixedCutoffExceptional L X Y A K).card : ℝ) ≤
      (2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp
          (primeInvSumUpper Y +
            (z - 1) * primeInvTailUpper (L - 1) (min X Y) + 38)) /
        z ^ (A * log (log X / log L) + K) := by
  refine (card_fixedCutoffExceptional_le_moment hz1).trans ?_
  exact div_le_div_of_nonneg_right
    (centeredUnrestrictedCutoffMoment
      hL hLX hLY hY hz1 hz52)
    (Real.rpow_nonneg (le_trans (by norm_num) hz1) _)

/-- Fixed-cutoff full-rough estimate after inserting the uniform moment. -/
theorem card_fixedCutoffRoughExceptional_le_mertens
    {L X Y : ℕ} {A K z : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hz1 : 1 ≤ z) (hz52 : z ≤ 5 / 2) :
    ((fixedCutoffRoughExceptional L X Y A K).card : ℝ) ≤
      (2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp
          (z * primeInvTailUpper (L - 1) (min X Y) +
            primeInvTailUpper (min X Y) Y + 38)) /
        z ^ (A * log (log X / log L) + K) := by
  refine (card_fixedCutoffRoughExceptional_le_moment hz1).trans ?_
  exact div_le_div_of_nonneg_right
    (centeredFullRoughCutoffMoment
      hL hLX hLY hY hz1 hz52)
    (Real.rpow_nonneg (le_trans (by norm_num) hz1) _)

/-- Fixed-cutoff odd-rough estimate after inserting the uniform moment. -/
theorem card_fixedCutoffOddRoughExceptional_le_mertens
    {L X Y : ℕ} {A K z : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hz1 : 1 ≤ z) (hz52 : z ≤ 5 / 2) :
    ((fixedCutoffOddRoughExceptional L X Y A K).card : ℝ) ≤
      (2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp
          (z * primeInvTailUpper (L - 1) (min X Y) +
            primeInvTailUpper (min X Y) Y + 38)) /
        z ^ (A * log (log X / log L) + K) := by
  refine (card_fixedCutoffOddRoughExceptional_le_moment hz1).trans ?_
  exact div_le_div_of_nonneg_right
    (centeredOddRoughCutoffMoment
      hL hLX hLY hY hz1 hz52)
    (Real.rpow_nonneg (le_trans (by norm_num) hz1) _)

/-- Union of the fixed-cutoff exceptional sets attached to a finite
grid. -/
noncomputable def gridExceptional
    (L Y : ℕ) (A K : ℝ) (grid : Finset ℕ) : Finset ℕ :=
  grid.biUnion fun X ↦ fixedCutoffExceptional L X Y A K

noncomputable def gridRoughExceptional
    (L Y : ℕ) (A K : ℝ) (grid : Finset ℕ) : Finset ℕ :=
  grid.biUnion fun X ↦ fixedCutoffRoughExceptional L X Y A K

noncomputable def gridOddRoughExceptional
    (L Y : ℕ) (A K : ℝ) (grid : Finset ℕ) : Finset ℕ :=
  grid.biUnion fun X ↦ fixedCutoffOddRoughExceptional L X Y A K

theorem card_gridExceptional_le_sum
    (L Y : ℕ) (A K : ℝ) (grid : Finset ℕ) :
    (gridExceptional L Y A K grid).card ≤
      ∑ X ∈ grid, (fixedCutoffExceptional L X Y A K).card := by
  unfold gridExceptional
  exact card_biUnion_le

theorem card_gridRoughExceptional_le_sum
    (L Y : ℕ) (A K : ℝ) (grid : Finset ℕ) :
    (gridRoughExceptional L Y A K grid).card ≤
      ∑ X ∈ grid, (fixedCutoffRoughExceptional L X Y A K).card := by
  unfold gridRoughExceptional
  exact card_biUnion_le

theorem card_gridOddRoughExceptional_le_sum
    (L Y : ℕ) (A K : ℝ) (grid : Finset ℕ) :
    (gridOddRoughExceptional L Y A K grid).card ≤
      ∑ X ∈ grid, (fixedCutoffOddRoughExceptional L X Y A K).card := by
  unfold gridOddRoughExceptional
  exact card_biUnion_le

/-- An explicit grid-coverage hypothesis: every failure of the actual
`CutoffRegular` predicate is witnessed at one of the grid cutoffs. -/
def RegularityGridCovers
    (L Y : ℕ) (A K : ℝ) (grid : Finset ℕ) : Prop :=
  ∀ n ∈ Icc 1 Y, ¬CutoffRegular L A K n →
    ∃ X ∈ grid,
      A * log (log X / log L) + K <
        (primeFactorCountBetween L X n : ℝ)

theorem irregular_upto_subset_gridExceptional
    {L Y : ℕ} {A K : ℝ} {grid : Finset ℕ}
    (hgrid : RegularityGridCovers L Y A K grid) :
    (Icc 1 Y).filter (fun n ↦ ¬CutoffRegular L A K n) ⊆
      gridExceptional L Y A K grid := by
  intro n hn
  have hnIcc := (mem_filter.mp hn).1
  have hnreg := (mem_filter.mp hn).2
  rcases hgrid n hnIcc hnreg with ⟨X, hXgrid, hX⟩
  unfold gridExceptional
  rw [mem_biUnion]
  exact ⟨X, hXgrid, mem_filter.mpr ⟨hnIcc, hX⟩⟩

theorem irregular_rough_upto_subset_gridRoughExceptional
    {L Y : ℕ} {A K : ℝ} {grid : Finset ℕ}
    (hgrid : RegularityGridCovers L Y A K grid) :
    (Icc 1 Y).filter
        (fun n ↦ Rough L n ∧ ¬CutoffRegular L A K n) ⊆
      gridRoughExceptional L Y A K grid := by
  intro n hn
  have hnIcc := (mem_filter.mp hn).1
  have hnrough := (mem_filter.mp hn).2.1
  have hnreg := (mem_filter.mp hn).2.2
  rcases hgrid n hnIcc hnreg with ⟨X, hXgrid, hX⟩
  unfold gridRoughExceptional
  rw [mem_biUnion]
  exact ⟨X, hXgrid,
    mem_filter.mpr ⟨hnIcc, hnrough, hX⟩⟩

theorem irregular_oddRough_upto_subset_gridOddRoughExceptional
    {L Y : ℕ} {A K : ℝ} {grid : Finset ℕ}
    (hgrid : RegularityGridCovers L Y A K grid) :
    (Icc 1 Y).filter
        (fun n ↦ OddRough L n ∧ ¬CutoffRegular L A K n) ⊆
      gridOddRoughExceptional L Y A K grid := by
  intro n hn
  have hnIcc := (mem_filter.mp hn).1
  have hnrough := (mem_filter.mp hn).2.1
  have hnreg := (mem_filter.mp hn).2.2
  rcases hgrid n hnIcc hnreg with ⟨X, hXgrid, hX⟩
  unfold gridOddRoughExceptional
  rw [mem_biUnion]
  exact ⟨X, hXgrid,
    mem_filter.mpr ⟨hnIcc, hnrough, hX⟩⟩

/-- The logarithmic scale used by centered regularity. -/
noncomputable def cutoffLogScale (L X : ℕ) : ℝ :=
  log (log X / log L)

theorem cutoffLogScale_nonneg
    {L X : ℕ} (hL : 3 ≤ L) (hLX : L ≤ X) :
    0 ≤ cutoffLogScale L X := by
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogMono : log (L : ℝ) ≤ log (X : ℝ) := by
    exact log_le_log (by positivity) (by exact_mod_cast hLX)
  unfold cutoffLogScale
  exact log_nonneg ((le_div_iff₀ hlogL).2 (by simpa using hlogMono))

theorem cutoffLogScale_mono
    {L X X' : ℕ} (hL : 3 ≤ L)
    (hLX : L ≤ X) (hXX' : X ≤ X') :
    cutoffLogScale L X ≤ cutoffLogScale L X' := by
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogX : 0 < log (X : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogMono : log (X : ℝ) ≤ log (X' : ℝ) :=
    log_le_log (by exact_mod_cast (show 0 < X by omega))
      (by exact_mod_cast hXX')
  have hratio :
      log (X : ℝ) / log L ≤ log (X' : ℝ) / log L :=
    div_le_div_of_nonneg_right hlogMono hlogL.le
  unfold cutoffLogScale
  exact log_le_log (div_pos hlogX hlogL) hratio

private theorem filter_eq_pred
    {α : Type*} (l : List α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ a ∈ l, (P a ↔ Q a)) :
    l.filter P = l.filter Q := by
  induction l with
  | nil => simp
  | cons p l ih =>
      have ih' : l.filter P = l.filter Q :=
        ih (fun a ha ↦ hPQ a (by simp [ha]))
      have hpq := hPQ p (by simp)
      by_cases hp : P p
      · have hq : Q p := hpq.mp hp
        simp [hp, hq, ih']
      · have hq : ¬Q p := fun h ↦ hp (hpq.mpr h)
        simp [hp, hq, ih']

private theorem filter_primeRange_length_eq_of_ge
    (l : List ℕ) (n L X X' : ℕ)
    (hl : ∀ p ∈ l, p ≤ n) (hnX : n ≤ X) (hnX' : n ≤ X') :
    (l.filter fun p ↦ L ≤ p ∧ p ≤ X).length =
      (l.filter fun p ↦ L ≤ p ∧ p ≤ X').length := by
  congr 1
  apply filter_eq_pred
  intro p hp
  have hpN : p ≤ n := hl p hp
  have hpX : p ≤ X := hpN.trans hnX
  have hpX' : p ≤ X' := hpN.trans hnX'
  simp [hpX, hpX']

theorem primeFactorCountBetween_eq_of_ge
    (L n : ℕ) {X X' : ℕ} (hnX : n ≤ X) (hnX' : n ≤ X') :
    primeFactorCountBetween L X n =
      primeFactorCountBetween L X' n := by
  unfold primeFactorCountBetween
  exact filter_primeRange_length_eq_of_ge
    n.primeFactorsList n L X X'
    (fun p hp ↦ Nat.le_of_mem_primeFactorsList hp) hnX hnX'

/-- Candidate cutoffs whose logarithmic scale is at most the grid
level `j`. -/
noncomputable def logGridCandidates
    (L Y j : ℕ) : Finset ℕ :=
  (Icc L Y).filter fun X ↦ cutoffLogScale L X ≤ j

/-- The largest cutoff in the `j`th logarithmic grid bucket. -/
noncomputable def logGridCutoff
    (L Y j : ℕ) : ℕ :=
  if h : (logGridCandidates L Y j).Nonempty then
    (logGridCandidates L Y j).max' h
  else L

theorem logGridCandidates_nonempty
    {L Y j : ℕ} (hL : 3 ≤ L) (hLY : L ≤ Y) :
    (logGridCandidates L Y j).Nonempty := by
  refine ⟨L, ?_⟩
  have hlogLne : log (L : ℝ) ≠ 0 :=
    ne_of_gt (log_pos (by exact_mod_cast (show 1 < L by omega)))
  unfold logGridCandidates
  rw [mem_filter, mem_Icc]
  refine ⟨⟨le_rfl, hLY⟩, ?_⟩
  unfold cutoffLogScale
  rw [div_self hlogLne, log_one]
  positivity

theorem logGridCutoff_mem
    {L Y j : ℕ} (hL : 3 ≤ L) (hLY : L ≤ Y) :
    logGridCutoff L Y j ∈ logGridCandidates L Y j := by
  unfold logGridCutoff
  rw [dif_pos (logGridCandidates_nonempty hL hLY)]
  exact max'_mem _ _

theorem logGridCutoff_bounds
    {L Y j : ℕ} (hL : 3 ≤ L) (hLY : L ≤ Y) :
    L ≤ logGridCutoff L Y j ∧ logGridCutoff L Y j ≤ Y := by
  have hmem := logGridCutoff_mem (j := j) hL hLY
  exact (mem_Icc.mp (mem_filter.mp hmem).1)

theorem cutoffLogScale_logGridCutoff_le
    {L Y j : ℕ} (hL : 3 ≤ L) (hLY : L ≤ Y) :
    cutoffLogScale L (logGridCutoff L Y j) ≤ j := by
  exact (mem_filter.mp (logGridCutoff_mem (j := j) hL hLY)).2

theorem le_logGridCutoff_of_scale_le
    {L Y X j : ℕ} (hL : 3 ≤ L) (hLY : L ≤ Y)
    (hX : X ∈ Icc L Y) (hscale : cutoffLogScale L X ≤ j) :
    X ≤ logGridCutoff L Y j := by
  have hmem : X ∈ logGridCandidates L Y j :=
    mem_filter.mpr ⟨hX, hscale⟩
  unfold logGridCutoff
  rw [dif_pos (logGridCandidates_nonempty hL hLY)]
  exact le_max' _ _ hmem

/-- Last index required to reach the scale of `Y`. -/
noncomputable def logGridLastIndex (L Y : ℕ) : ℕ :=
  ⌈cutoffLogScale L Y⌉₊

/-- Finite unit-step logarithmic grid, represented by its indices. -/
noncomputable def logarithmicGridIndices (L Y : ℕ) : Finset ℕ :=
  range (logGridLastIndex L Y + 1)

/-- Threshold assigned to grid level `j`; the one-step loss is what
permits interpolation from an arbitrary cutoff to the upper endpoint of
its bucket. -/
noncomputable def logGridThreshold
    (A K : ℝ) (j : ℕ) : ℝ :=
  A * (j - 1 : ℕ) + K

/-- Every failure for an integer `n ≤ Y` has a witness cutoff between
`L` and `Y`. -/
theorem cutoffRegular_failure_bounded
    {L Y n : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hLY : L ≤ Y) (hn : n ∈ Icc 1 Y)
    (hA : 0 ≤ A) (hreg : ¬CutoffRegular L A K n) :
    ∃ X ∈ Icc L Y,
      A * cutoffLogScale L X + K <
        (primeFactorCountBetween L X n : ℝ) := by
  rcases not_cutoffRegular_iff.mp hreg with ⟨x, hLx, hx⟩
  by_cases hxY : x ≤ Y
  · exact ⟨x, mem_Icc.mpr ⟨hLx, hxY⟩, by
      simpa [cutoffLogScale] using hx⟩
  · have hYx : Y ≤ x := Nat.le_of_lt (Nat.lt_of_not_ge hxY)
    have hnY : n ≤ Y := (mem_Icc.mp hn).2
    have hcount :
        primeFactorCountBetween L Y n =
          primeFactorCountBetween L x n :=
      primeFactorCountBetween_eq_of_ge L n hnY (hnY.trans hYx)
    have hscale :
        cutoffLogScale L Y ≤ cutoffLogScale L x :=
      cutoffLogScale_mono hL hLY hYx
    refine ⟨Y, mem_Icc.mpr ⟨hLY, le_rfl⟩, ?_⟩
    have hthreshold :
        A * cutoffLogScale L Y + K ≤
          A * cutoffLogScale L x + K := by
      linarith [mul_le_mul_of_nonneg_left hscale hA]
    rw [hcount]
    exact hthreshold.trans_lt (by
      simpa [cutoffLogScale] using hx)

/-- The unit-step logarithmic grid covers every failure of the actual
`CutoffRegular` predicate, with the explicit one-level threshold loss. -/
theorem logarithmicGrid_covers
    {L Y n : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hLY : L ≤ Y) (hn : n ∈ Icc 1 Y)
    (hA : 0 ≤ A) (hreg : ¬CutoffRegular L A K n) :
    ∃ j ∈ logarithmicGridIndices L Y,
      logGridThreshold A K j <
        (primeFactorCountBetween L (logGridCutoff L Y j) n : ℝ) := by
  rcases cutoffRegular_failure_bounded hL hLY hn hA hreg with
    ⟨x, hxIcc, hxFail⟩
  let t := cutoffLogScale L x
  let j : ℕ := ⌈t⌉₊
  have ht0 : 0 ≤ t :=
    cutoffLogScale_nonneg hL (mem_Icc.mp hxIcc).1
  have htY : t ≤ cutoffLogScale L Y :=
    cutoffLogScale_mono hL (mem_Icc.mp hxIcc).1 (mem_Icc.mp hxIcc).2
  have hjLast : j ≤ logGridLastIndex L Y := by
    unfold j logGridLastIndex
    exact Nat.ceil_mono htY
  have hjMem : j ∈ logarithmicGridIndices L Y := by
    rw [logarithmicGridIndices, mem_range]
    omega
  have htj : t ≤ (j : ℝ) := by
    unfold j
    exact Nat.le_ceil t
  have hxCutoff :
      x ≤ logGridCutoff L Y j :=
    le_logGridCutoff_of_scale_le hL hLY hxIcc htj
  have hcountMono :
      primeFactorCountBetween L x n ≤
        primeFactorCountBetween L (logGridCutoff L Y j) n :=
    primeFactorCountBetween_mono_right L n hxCutoff
  have hjLower : ((j - 1 : ℕ) : ℝ) ≤ t := by
    by_cases hj0 : j = 0
    · rw [hj0]
      norm_num
      exact ht0
    · have hjCeil : ⌈t⌉₊ = j := by rfl
      have hceil := (Nat.ceil_eq_iff hj0).mp hjCeil
      exact hceil.1.le
  refine ⟨j, hjMem, ?_⟩
  unfold logGridThreshold
  have hthreshold :
      A * (j - 1 : ℕ) + K ≤ A * t + K :=
    by linarith [mul_le_mul_of_nonneg_left hjLower hA]
  have hcountMonoReal :
      (primeFactorCountBetween L x n : ℝ) ≤
        primeFactorCountBetween L (logGridCutoff L Y j) n := by
    exact_mod_cast hcountMono
  exact (hthreshold.trans_lt hxFail).trans_le hcountMonoReal

/-- Level exceptional set for the concrete logarithmic grid. -/
noncomputable def logGridLevelExceptional
    (L Y : ℕ) (A K : ℝ) (j : ℕ) : Finset ℕ :=
  (Icc 1 Y).filter fun n ↦
    logGridThreshold A K j <
      (primeFactorCountBetween L (logGridCutoff L Y j) n : ℝ)

noncomputable def logGridLevelRoughExceptional
    (L Y : ℕ) (A K : ℝ) (j : ℕ) : Finset ℕ :=
  (Icc 1 Y).filter fun n ↦
    Rough L n ∧ logGridThreshold A K j <
      (primeFactorCountBetween L (logGridCutoff L Y j) n : ℝ)

noncomputable def logGridLevelOddRoughExceptional
    (L Y : ℕ) (A K : ℝ) (j : ℕ) : Finset ℕ :=
  (Icc 1 Y).filter fun n ↦
    OddRough L n ∧ logGridThreshold A K j <
      (primeFactorCountBetween L (logGridCutoff L Y j) n : ℝ)

noncomputable def logarithmicGridExceptional
    (L Y : ℕ) (A K : ℝ) : Finset ℕ :=
  (logarithmicGridIndices L Y).biUnion
    (logGridLevelExceptional L Y A K)

noncomputable def logarithmicGridRoughExceptional
    (L Y : ℕ) (A K : ℝ) : Finset ℕ :=
  (logarithmicGridIndices L Y).biUnion
    (logGridLevelRoughExceptional L Y A K)

noncomputable def logarithmicGridOddRoughExceptional
    (L Y : ℕ) (A K : ℝ) : Finset ℕ :=
  (logarithmicGridIndices L Y).biUnion
    (logGridLevelOddRoughExceptional L Y A K)

theorem irregular_upto_subset_logarithmicGridExceptional
    {L Y : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hLY : L ≤ Y) (hA : 0 ≤ A) :
    (Icc 1 Y).filter (fun n ↦ ¬CutoffRegular L A K n) ⊆
      logarithmicGridExceptional L Y A K := by
  intro n hn
  have hnIcc := (mem_filter.mp hn).1
  have hnreg := (mem_filter.mp hn).2
  rcases logarithmicGrid_covers hL hLY hnIcc hA hnreg with
    ⟨j, hj, hjFail⟩
  unfold logarithmicGridExceptional
  rw [mem_biUnion]
  exact ⟨j, hj, mem_filter.mpr ⟨hnIcc, hjFail⟩⟩

theorem irregular_rough_upto_subset_logarithmicGridRoughExceptional
    {L Y : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hLY : L ≤ Y) (hA : 0 ≤ A) :
    (Icc 1 Y).filter
        (fun n ↦ Rough L n ∧ ¬CutoffRegular L A K n) ⊆
      logarithmicGridRoughExceptional L Y A K := by
  intro n hn
  have hnIcc := (mem_filter.mp hn).1
  have hnrough := (mem_filter.mp hn).2.1
  have hnreg := (mem_filter.mp hn).2.2
  rcases logarithmicGrid_covers hL hLY hnIcc hA hnreg with
    ⟨j, hj, hjFail⟩
  unfold logarithmicGridRoughExceptional
  rw [mem_biUnion]
  exact ⟨j, hj, mem_filter.mpr ⟨hnIcc, hnrough, hjFail⟩⟩

theorem irregular_oddRough_upto_subset_logarithmicGridOddRoughExceptional
    {L Y : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hLY : L ≤ Y) (hA : 0 ≤ A) :
    (Icc 1 Y).filter
        (fun n ↦ OddRough L n ∧ ¬CutoffRegular L A K n) ⊆
      logarithmicGridOddRoughExceptional L Y A K := by
  intro n hn
  have hnIcc := (mem_filter.mp hn).1
  have hnrough := (mem_filter.mp hn).2.1
  have hnreg := (mem_filter.mp hn).2.2
  rcases logarithmicGrid_covers hL hLY hnIcc hA hnreg with
    ⟨j, hj, hjFail⟩
  unfold logarithmicGridOddRoughExceptional
  rw [mem_biUnion]
  exact ⟨j, hj, mem_filter.mpr ⟨hnIcc, hnrough, hjFail⟩⟩

theorem card_logarithmicGridExceptional_le_sum
    (L Y : ℕ) (A K : ℝ) :
    (logarithmicGridExceptional L Y A K).card ≤
      ∑ j ∈ logarithmicGridIndices L Y,
        (logGridLevelExceptional L Y A K j).card := by
  unfold logarithmicGridExceptional
  exact card_biUnion_le

theorem card_logarithmicGridRoughExceptional_le_sum
    (L Y : ℕ) (A K : ℝ) :
    (logarithmicGridRoughExceptional L Y A K).card ≤
      ∑ j ∈ logarithmicGridIndices L Y,
        (logGridLevelRoughExceptional L Y A K j).card := by
  unfold logarithmicGridRoughExceptional
  exact card_biUnion_le

theorem card_logarithmicGridOddRoughExceptional_le_sum
    (L Y : ℕ) (A K : ℝ) :
    (logarithmicGridOddRoughExceptional L Y A K).card ≤
      ∑ j ∈ logarithmicGridIndices L Y,
        (logGridLevelOddRoughExceptional L Y A K j).card := by
  unfold logarithmicGridOddRoughExceptional
  exact card_biUnion_le

end Erdos327.Analytic
