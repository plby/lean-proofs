import ErdosProblems.Erdos1165.PreStoppingFiber

open scoped BigOperators

namespace Erdos1165.PreStoppingSpatialLaw

open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber
open ShiftedPrefixBridge PrefixLevelTruncation PreStoppingFiber
open HLOZPathEvents

noncomputable section

/-!
# The deterministic spatial law on a stopped insertion fibre

This file closes the point-set seam between the global level condition at a
stopping time and the spatial-domino truncations.  A lattice site is assigned
to the unique base of its horizontal domino in either checkerboard
orientation.  Consequently every site is either an endpoint of an external
domino or has no insertion contribution at all.  The global bound on all
local times can therefore be split exactly into

* bounds at sites not covered by the external dominoes;
* bounds on the distinguished external dominoes; and
* the coordinatewise HLOZ truncation on all remaining external dominoes.

The last section combines this deterministic split with the terminal form of
`levelFavorite` from `PreStoppingFiber`.
-/

/-! ## Canonical oriented domino bases -/

/-- The base of the horizontal domino containing `y` in the selected HLOZ
checkerboard orientation. -/
noncomputable def dominoBase (o : Orientation) (y : Point) : Point := by
  classical
  exact match o with
    | .even => if EvenPoint y then y else y - e₁
    | .shifted => if OddPoint y then y else y + e₁

theorem evenPoint_or_oddPoint (y : Point) : EvenPoint y ∨ OddPoint y := by
  change pointParity y = 0 ∨ pointParity y = 1
  have hlt : (pointParity y).val < 2 := ZMod.val_lt _
  have hval : (pointParity y).val = 0 ∨ (pointParity y).val = 1 := by omega
  rcases hval with hval | hval
  · left
    exact (ZMod.val_eq_zero _).mp hval
  · right
    exact (ZMod.val_eq_one (by norm_num) _).mp hval

theorem dominoBase_compatible (o : Orientation) (y : Point) :
    OrientationCompatible o (dominoBase o y) := by
  classical
  cases o with
  | even =>
      by_cases hy : EvenPoint y
      · simpa [dominoBase, hy]
      · have hyOdd : OddPoint y := (evenPoint_or_oddPoint y).resolve_left hy
        change EvenPoint (if EvenPoint y then y else y - e₁)
        rw [if_neg hy]
        rw [EvenPoint, pointParity_sub_e₁, hyOdd]
        decide
  | shifted =>
      by_cases hy : OddPoint y
      · simpa [dominoBase, hy]
      · have hyEven : EvenPoint y := (evenPoint_or_oddPoint y).resolve_right hy
        change OddPoint (if OddPoint y then y else y + e₁)
        rw [if_neg hy]
        rw [OddPoint, pointParity_add_e₁, hyEven]
        decide

theorem point_eq_dominoBase_or_middle (o : Orientation) (y : Point) :
    y = dominoBase o y ∨ y = excursionMiddle o (dominoBase o y) := by
  classical
  rcases y with ⟨y₁, y₂⟩
  cases o with
  | even =>
      by_cases hy : EvenPoint (y₁, y₂)
      · exact Or.inl (by simp [dominoBase, hy])
      · exact Or.inr (by simp [dominoBase, hy, excursionMiddle, e₁])
  | shifted =>
      by_cases hy : OddPoint (y₁, y₂)
      · exact Or.inl (by simp [dominoBase, hy])
      · exact Or.inr (by simp [dominoBase, hy, excursionMiddle, e₁])

theorem dominoBase_eq_self_of_compatible {o : Orientation} {b : Point}
    (hb : OrientationCompatible o b) : dominoBase o b = b := by
  classical
  cases o with
  | even =>
      change EvenPoint b at hb
      simp [dominoBase, hb]
  | shifted =>
      change OddPoint b at hb
      simp [dominoBase, hb]

theorem dominoBase_middle_of_compatible {o : Orientation} {b : Point}
    (hb : OrientationCompatible o b) :
    dominoBase o (excursionMiddle o b) = b := by
  classical
  rcases b with ⟨b₁, b₂⟩
  cases o with
  | even =>
      have hodd : OddPoint (excursionMiddle .even (b₁, b₂)) :=
        even_middle_is_odd hb
      have hnotEven : ¬EvenPoint (excursionMiddle .even (b₁, b₂)) := by
        intro heven
        rw [OddPoint, heven] at hodd
        exact zero_ne_one hodd
      have hnotEven' : ¬EvenPoint (b₁ + 1, b₂) := by
        simpa [excursionMiddle, e₁] using hnotEven
      simp [dominoBase, hnotEven', excursionMiddle, e₁]
  | shifted =>
      have heven : EvenPoint (excursionMiddle .shifted (b₁, b₂)) :=
        shifted_middle_is_even hb
      have hnotOdd : ¬OddPoint (excursionMiddle .shifted (b₁, b₂)) := by
        intro hodd
        rw [EvenPoint, hodd] at heven
        exact one_ne_zero heven
      have hnotOdd' : ¬OddPoint (b₁ - 1, b₂) := by
        simpa [excursionMiddle, e₁] using hnotOdd
      simp [dominoBase, hnotOdd', excursionMiddle, e₁]

theorem externalBase_compatible {o : Orientation} {i : ℕ} {x : Point}
    (r : Fin i → RetainedBlock o) (hx : OrientationCompatible o x)
    (k : Fin (i + 1)) : OrientationCompatible o (externalBase x r k) := by
  have hpar := pointParity_externalBase x r k
  cases o with
  | even =>
      change EvenPoint x at hx
      change EvenPoint (externalBase x r k)
      exact hpar.trans hx
  | shifted =>
      change OddPoint x at hx
      change OddPoint (externalBase x r k)
      exact hpar.trans hx

theorem dominoBase_externalBase {o : Orientation} {i : ℕ} {x : Point}
    (r : Fin i → RetainedBlock o) (hx : OrientationCompatible o x)
    (k : Fin (i + 1)) :
    dominoBase o (externalBase x r k) = externalBase x r k :=
  dominoBase_eq_self_of_compatible (externalBase_compatible r hx k)

theorem dominoBase_externalMiddle {o : Orientation} {i : ℕ} {x : Point}
    (r : Fin i → RetainedBlock o) (hx : OrientationCompatible o x)
    (k : Fin (i + 1)) :
    dominoBase o (excursionMiddle o (externalBase x r k)) = externalBase x r k :=
  dominoBase_middle_of_compatible (externalBase_compatible r hx k)

/-! ## External coverage and fixed-only sites -/

/-- An external domino covering `y`, when its canonical base occurs in the
fixed retained trace. -/
def externalDominoOfSite {o : Orientation} {i : ℕ} {x : Point}
    (r : Fin i → RetainedBlock o) (y : Point)
    (hy : dominoBase o y ∈ externalDominoBases x r) : ExternalDomino x r :=
  ⟨dominoBase o y, hy⟩

@[simp] theorem externalDominoOfSite_val {o : Orientation} {i : ℕ} {x : Point}
    (r : Fin i → RetainedBlock o) (y : Point)
    (hy : dominoBase o y ∈ externalDominoBases x r) :
    (externalDominoOfSite r y hy : Point) = dominoBase o y := rfl

theorem site_eq_externalDomino_base_or_middle {o : Orientation} {i : ℕ}
    {x : Point} (r : Fin i → RetainedBlock o) (y : Point)
    (hy : dominoBase o y ∈ externalDominoBases x r) :
    y = (externalDominoOfSite r y hy : Point) ∨
      y = excursionMiddle o (externalDominoOfSite r y hy : Point) := by
  simpa using point_eq_dominoBase_or_middle o y

/-- A site whose canonical domino base is absent from the external trace has
zero lazy local time for every insertion vector. -/
theorem insertionLazyLocalTime_eq_zero_of_dominoBase_not_mem
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (hx : OrientationCompatible o x) (y : Point)
    (hy : dominoBase o y ∉ externalDominoBases x r) :
    insertionLazyLocalTime x r q y = 0 := by
  classical
  unfold insertionLazyLocalTime
  apply Finset.sum_eq_zero
  intro k _
  have hkMem : externalBase x r k ∈ externalDominoBases x r :=
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have hkBase : externalBase x r k ≠ y := by
    intro h
    apply hy
    rw [← h, dominoBase_externalBase r hx k]
    exact hkMem
  have hkMiddle : excursionMiddle o (externalBase x r k) ≠ y := by
    intro h
    apply hy
    rw [← h, dominoBase_externalMiddle r hx k]
    exact hkMem
  simp [hkBase, hkMiddle]

theorem even_fixedOnly_localTime {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks ω n = insertGapVector r q) (y : Point)
    (hy : dominoBase .even y ∉ externalDominoBases (0, 0) r) :
    listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) y =
      fixedEvenPrefixLocalTime ω n r y := by
  rw [even_fixedFiber_localTime ω n r q hword]
  rw [insertionLazyLocalTime_eq_zero_of_dominoBase_not_mem
    (0, 0) r q even_start_compatible y hy]
  omega

theorem shifted_fixedOnly_localTime {i : ℕ} (ω : StepPath) (n : ℕ)
    (hn : 0 < n) (r : Fin i → RetainedBlock .shifted)
    (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q) (y : Point)
    (hy : dominoBase .shifted y ∉
      externalDominoBases (trajectory ω 1) r) :
    listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) y =
      fixedShiftedPrefixLocalTime ω n r y := by
  rw [shifted_fixedFiber_localTime ω n hn r q hword]
  rw [insertionLazyLocalTime_eq_zero_of_dominoBase_not_mem
    (trajectory ω 1) r q (shifted_start_compatible ω) y hy]
  omega

/-! ## Favorite locations and their oriented domino bases -/

/-- The oriented bases of the actual favorite sites at a finite time. -/
def favoriteDominoBases (o : Orientation) (s : WalkPath) (n : ℕ) : Finset Point :=
  (favoriteSites s n).image (dominoBase o)

theorem mem_favoriteDominoBases_iff (o : Orientation) (s : WalkPath)
    (n : ℕ) (b : Point) :
    b ∈ favoriteDominoBases o s n ↔
      ∃ y ∈ favoriteSites s n, dominoBase o y = b := by
  simp [favoriteDominoBases]

theorem favorite_site_base_mem (o : Orientation) (s : WalkPath) (n : ℕ)
    {y : Point} (hy : y ∈ favoriteSites s n) :
    dominoBase o y ∈ favoriteDominoBases o s n := by
  exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

/-- At terminal level data with positive threshold count, the threshold sites
are exactly the actual favorite locations. -/
theorem thresholdSites_eq_favoriteSites_of_terminal
    (s : WalkPath) (n m k : ℕ) (hk : 0 < k)
    (hcount : thresholdCount s n m = k)
    (hbelow : ∀ y : Point, localTime s n y < m + 1) :
    thresholdSites s n m = favoriteSites s n := by
  have hmaxLe : maxLocalTime s n ≤ m :=
    (thresholdCount_succ_level_eq_zero_iff s n m).mp
      ((thresholdCount_eq_zero_iff_forall_lt s n (m + 1)
        (Nat.zero_lt_succ m)).mpr hbelow)
  have hnonempty : (thresholdSites s n m).Nonempty := by
    rw [← Finset.card_pos, ← thresholdCount, hcount]
    exact hk
  obtain ⟨y, hy⟩ := hnonempty
  have hydata := (mem_thresholdSites s n m y).mp hy
  have hmaxGe : m ≤ maxLocalTime s n :=
    hydata.2.trans (localTime_le_maxLocalTime s n (x := y) hydata.1)
  have hmax : maxLocalTime s n = m := Nat.le_antisymm hmaxLe hmaxGe
  rw [← thresholdSites_at_max_eq_favoriteSites s n, hmax]

theorem localTime_eq_listLocalTime (s : WalkPath) (n : ℕ) (y : Point) :
    localTime s n y =
      listLocalTime (finitePathList (pathPrefix s n)) y := by
  unfold localTime localTimePrefix finitePathList
  exact finiteLocalTime_eq_listLocalTime (pathPrefix s n) y

/-- On a genuine stopped level atom satisfying the favorite condition, the
sites that have reached level `m` are precisely the actual favorites at the
terminal time. -/
theorem thresholdSites_eq_favoriteSites_at_truncatedLevelTime
    (m k cutoff n : ℕ) (ω : StepPath) (hk : 0 < k) (hn : n < cutoff)
    (htime : truncatedLevelTime m k cutoff ω = n)
    (hfavorite : levelFavorite (trajectory ω) m k) :
    thresholdSites (trajectory ω) n m = favoriteSites (trajectory ω) n := by
  have hcreation : ThresholdCreation (trajectory ω) m k n :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff n ω hn).mp htime
  have hcount : thresholdCount (trajectory ω) n m = k :=
    thresholdCount_eq_of_creation hk hcreation
  have hbelow : ∀ y : Point, localTime (trajectory ω) n y < m + 1 :=
    (levelFavorite_iff_all_localTime_lt_succ_at_truncatedLevelTime
      m k cutoff n ω hk hn htime).mp hfavorite
  exact thresholdSites_eq_favoriteSites_of_terminal
    (trajectory ω) n m k hk hcount hbelow

/-! ## The exact global spatial factorization -/

/-- The part of the even-prefix level predicate which is not an away-domino
truncation: all fixed-only sites and all endpoints of distinguished external
dominoes. -/
def EvenDistinguishedCondition {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (level : ℕ) (D : Finset Point) : Prop :=
  (∀ y : Point, dominoBase .even y ∉ externalDominoBases (0, 0) r →
      fixedEvenPrefixLocalTime ω n r y < level) ∧
    ∀ b : ExternalDomino (0, 0) r, b.1 ∈ D →
      fixedEvenPrefixLocalTime ω n r b.1 +
          dominoLazyTotal (0, 0) r q b < level ∧
        fixedEvenPrefixLocalTime ω n r (excursionMiddle .even b.1) +
          dominoLazyTotal (0, 0) r q b < level

/-- Literal prefix-corrected truncation on the non-distinguished even
dominoes. -/
def EvenPrefixDominoTruncation {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (level : ℕ) (D : Finset Point) : Prop :=
  ∀ b : ExternalDomino (0, 0) r, b.1 ∉ D →
    dominoLazyTotal (0, 0) r q b <
      level - fixedEvenPrefixDominoMax ω n r b

/-- Shifted analogue of `EvenDistinguishedCondition`; its fixed part includes
the time-zero atom. -/
def ShiftedDistinguishedCondition {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (level : ℕ) (D : Finset Point) : Prop :=
  (∀ y : Point,
      dominoBase .shifted y ∉ externalDominoBases (trajectory ω 1) r →
        fixedShiftedPrefixLocalTime ω n r y < level) ∧
    ∀ b : ExternalDomino (trajectory ω 1) r, b.1 ∈ D →
      fixedShiftedPrefixLocalTime ω n r b.1 +
          dominoLazyTotal (trajectory ω 1) r q b < level ∧
        fixedShiftedPrefixLocalTime ω n r (excursionMiddle .shifted b.1) +
          dominoLazyTotal (trajectory ω 1) r q b < level

/-- Literal prefix-corrected truncation on the non-distinguished shifted
dominoes. -/
def ShiftedPrefixDominoTruncation {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (level : ℕ) (D : Finset Point) : Prop :=
  ∀ b : ExternalDomino (trajectory ω 1) r, b.1 ∉ D →
    dominoLazyTotal (trajectory ω 1) r q b <
      level - fixedShiftedPrefixDominoMax ω n r b

theorem even_allLocalTimesBelow_iff_distinguished_and_dominoTruncation
    {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks ω n = insertGapVector r q)
    (level : ℕ) (D : Finset Point) :
    (∀ y : Point,
      listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) y < level) ↔
      EvenDistinguishedCondition ω n r q level D ∧
        EvenPrefixDominoTruncation ω n r q level D := by
  rw [EvenPrefixDominoTruncation]
  rw [← even_actualEndpointsBelow_iff_dominoTruncation ω n r q hword level D]
  constructor
  · intro hall
    exact ⟨⟨fun y _ ↦ by
      rw [← even_fixedOnly_localTime ω n r q hword y ‹_›]
      exact hall y, fun b _ ↦ ⟨by
        rw [← even_fixedFiber_localTime_at_base ω n r q hword b]
        exact hall b.1, by
        rw [← even_fixedFiber_localTime_at_middle ω n r q hword b]
        exact hall (excursionMiddle .even b.1)⟩⟩,
      fun b _ ↦ ⟨hall b.1, hall (excursionMiddle .even b.1)⟩⟩
  · rintro ⟨⟨hfixed, hdist⟩, haway⟩ y
    by_cases hy : dominoBase .even y ∈ externalDominoBases (0, 0) r
    · let b : ExternalDomino (0, 0) r := externalDominoOfSite r y hy
      have hend : y = (b : Point) ∨ y = excursionMiddle .even (b : Point) :=
        site_eq_externalDomino_base_or_middle r y hy
      by_cases hb : b.1 ∈ D
      · rcases hdist b hb with ⟨hbase, hmiddle⟩
        have hbase' :
            listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) b.1 <
              level := by
          rw [even_fixedFiber_localTime_at_base ω n r q hword b]
          exact hbase
        have hmiddle' :
            listLocalTime (finitePathList (pathPrefix (trajectory ω) n))
                (excursionMiddle .even b.1) < level := by
          rw [even_fixedFiber_localTime_at_middle ω n r q hword b]
          exact hmiddle
        rcases hend with hend | hend
        · simpa only [hend] using hbase'
        · simpa only [hend] using hmiddle'
      · rcases haway b hb with ⟨hbase, hmiddle⟩
        rcases hend with hend | hend
        · simpa only [hend] using hbase
        · simpa only [hend] using hmiddle
    · rw [even_fixedOnly_localTime ω n r q hword y hy]
      exact hfixed y hy

theorem shifted_allLocalTimesBelow_iff_distinguished_and_dominoTruncation
    {i : ℕ} (ω : StepPath) (n : ℕ) (hn : 0 < n)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q)
    (level : ℕ) (D : Finset Point) :
    (∀ y : Point,
      listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) y < level) ↔
      ShiftedDistinguishedCondition ω n r q level D ∧
        ShiftedPrefixDominoTruncation ω n r q level D := by
  rw [ShiftedPrefixDominoTruncation]
  rw [← shifted_actualEndpointsBelow_iff_dominoTruncation
    ω n hn r q hword level D]
  constructor
  · intro hall
    exact ⟨⟨fun y _ ↦ by
      rw [← shifted_fixedOnly_localTime ω n hn r q hword y ‹_›]
      exact hall y, fun b _ ↦ ⟨by
        rw [← shifted_fixedFiber_localTime_at_base ω n hn r q hword b]
        exact hall b.1, by
        rw [← shifted_fixedFiber_localTime_at_middle ω n hn r q hword b]
        exact hall (excursionMiddle .shifted b.1)⟩⟩,
      fun b _ ↦ ⟨hall b.1, hall (excursionMiddle .shifted b.1)⟩⟩
  · rintro ⟨⟨hfixed, hdist⟩, haway⟩ y
    by_cases hy : dominoBase .shifted y ∈
        externalDominoBases (trajectory ω 1) r
    · let b : ExternalDomino (trajectory ω 1) r := externalDominoOfSite r y hy
      have hend : y = (b : Point) ∨ y = excursionMiddle .shifted (b : Point) :=
        site_eq_externalDomino_base_or_middle r y hy
      by_cases hb : b.1 ∈ D
      · rcases hdist b hb with ⟨hbase, hmiddle⟩
        have hbase' :
            listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) b.1 <
              level := by
          rw [shifted_fixedFiber_localTime_at_base ω n hn r q hword b]
          exact hbase
        have hmiddle' :
            listLocalTime (finitePathList (pathPrefix (trajectory ω) n))
                (excursionMiddle .shifted b.1) < level := by
          rw [shifted_fixedFiber_localTime_at_middle ω n hn r q hword b]
          exact hmiddle
        rcases hend with hend | hend
        · simpa only [hend] using hbase'
        · simpa only [hend] using hmiddle'
      · rcases haway b hb with ⟨hbase, hmiddle⟩
        rcases hend with hend | hend
        · simpa only [hend] using hbase
        · simpa only [hend] using hmiddle
    · rw [shifted_fixedOnly_localTime ω n hn r q hword y hy]
      exact hfixed y hy

/-! ## Stopped-atom favorite predicates -/

/-- On an even-oriented stopped insertion atom, the terminal favorite
predicate is exactly the distinguished-coordinate predicate times the
prefix-corrected truncations on every other external domino.  The
distinguished bases are obtained from the actual favorite locations, rather
than supplied as unrelated data. -/
theorem even_levelFavorite_iff_distinguished_and_dominoTruncation_at_stoppedAtom
    {i : ℕ} (m k cutoff n : ℕ) (ω : StepPath) (hk : 0 < k)
    (hn : n < cutoff) (htime : truncatedLevelTime m k cutoff ω = n)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks ω n = insertGapVector r q) :
    levelFavorite (trajectory ω) m k ↔
      EvenDistinguishedCondition ω n r q (m + 1)
          (favoriteDominoBases .even (trajectory ω) n) ∧
        EvenPrefixDominoTruncation ω n r q (m + 1)
          (favoriteDominoBases .even (trajectory ω) n) := by
  rw [levelFavorite_iff_all_localTime_lt_succ_at_truncatedLevelTime
    m k cutoff n ω hk hn htime]
  simp_rw [localTime_eq_listLocalTime]
  exact even_allLocalTimesBelow_iff_distinguished_and_dominoTruncation
    ω n r q hword (m + 1) (favoriteDominoBases .even (trajectory ω) n)

/-- Shifted analogue of
`even_levelFavorite_iff_distinguished_and_dominoTruncation_at_stoppedAtom`.
The time-zero atom is included in the fixed-only/distinguished factor. -/
theorem shifted_levelFavorite_iff_distinguished_and_dominoTruncation_at_stoppedAtom
    {i : ℕ} (m k cutoff n : ℕ) (ω : StepPath) (hk : 0 < k)
    (hn : n < cutoff) (hpos : 0 < n)
    (htime : truncatedLevelTime m k cutoff ω = n)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q) :
    levelFavorite (trajectory ω) m k ↔
      ShiftedDistinguishedCondition ω n r q (m + 1)
          (favoriteDominoBases .shifted (trajectory ω) n) ∧
        ShiftedPrefixDominoTruncation ω n r q (m + 1)
          (favoriteDominoBases .shifted (trajectory ω) n) := by
  rw [levelFavorite_iff_all_localTime_lt_succ_at_truncatedLevelTime
    m k cutoff n ω hk hn htime]
  simp_rw [localTime_eq_listLocalTime]
  exact shifted_allLocalTimesBelow_iff_distinguished_and_dominoTruncation
    ω n hpos r q hword (m + 1) (favoriteDominoBases .shifted (trajectory ω) n)

end

end Erdos1165.PreStoppingSpatialLaw
