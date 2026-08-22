import ErdosProblems.Erdos1165.PrefixConditionalLaw
import ErdosProblems.Erdos1165.HLOZPathEvents

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.PreStoppingFiber

open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber
open PrefixConditionalLaw
open HLOZPathEvents

/-!
# Finite pre-stopping insertion fibres

The atoms below end at their own stopping time.  This makes the variable
length insertion words prefix-free without adding a future block: two nested
cylinders cannot both assert different values of the same stopping time.
-/

/-- Directions spelling a block word, followed by a fixed boundary tail. -/
def insertionPrefixList {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) : List Direction :=
  (insertGapVector r q).flatMap (fun b ↦ [b.1, b.2]) ++ tail

@[simp] theorem insertionPrefixList_length {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) :
    (insertionPrefixList r q tail).length =
      2 * (i + ∑ k, q k) + tail.length := by
  simp [insertionPrefixList, insertGapVector_length]
  omega

/-- A list of known length, viewed as a finite increment vector. -/
def directionVectorOfList (v : List Direction) : Fin v.length → Direction :=
  fun j ↦ v.get j

@[simp] theorem ofFn_directionVectorOfList (v : List Direction) :
    List.ofFn (directionVectorOfList v) = v := by
  exact List.ofFn_get v

theorem stepPrefix_extendPrefix (n : ℕ) (v : Fin n → Direction) :
    stepPrefix n (extendPrefix v) = v := by
  funext j
  simp [stepPrefix, extendPrefix, j.isLt]

/-- Equality of a finite stopping time is determined by the corresponding
increment prefix. -/
theorem stoppingTime_eq_of_stepPrefix_eq {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) {ω ω' : StepPath} {n : ℕ}
    (hω : τ ω = n) (hp : stepPrefix n ω' = stepPrefix n ω) :
    τ ω' = n := by
  have hn := hτ.measurableSet_eq n
  rw [incrementFiltration_apply] at hn
  obtain ⟨S, hS, hpre⟩ := hn
  have hmem : ω ∈ stepPrefix n ⁻¹' S := by
    rw [hpre]
    exact hω
  have hmem' : ω' ∈ stepPrefix n ⁻¹' S := by
    change stepPrefix n ω' ∈ S
    rw [hp]
    exact hmem
  rw [hpre] at hmem'
  exact hmem'

/-! ## The capped level clock before its artificial cutoff -/

/-- Strictly before the deterministic cutoff, equality of the capped level
clock with `n` is exactly the genuine first-threshold-creation event at `n`.
This is the point where the artificial cutoff branch is separated from the
pre-stopping fibre. -/
theorem truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
    (m k cutoff n : ℕ) (ω : StepPath) (hn : n < cutoff) :
    truncatedLevelTime m k cutoff ω = n ↔
      ThresholdCreation (trajectory ω) m k n := by
  classical
  constructor
  · intro htime
    by_cases hreach : ReachesThreshold (trajectory ω) m k
    · have hfind : Nat.find hreach = n := by
        unfold truncatedLevelTime at htime
        rw [dif_pos hreach] at htime
        omega
      simpa [hfind] using thresholdCreation_natFind hreach
    · unfold truncatedLevelTime at htime
      rw [dif_neg hreach] at htime
      omega
  · intro hcreation
    let hreach : ReachesThreshold (trajectory ω) m k := ⟨n, hcreation.1⟩
    have hfind_le : Nat.find hreach ≤ n := Nat.find_min' hreach hcreation.1
    have hn_le_find : n ≤ Nat.find hreach := by
      by_contra hnot
      have hlt : Nat.find hreach < n := Nat.lt_of_not_ge hnot
      have hsmall := hcreation.2 (Nat.find hreach) hlt
      exact (Nat.not_le_of_gt hsmall) (Nat.find_spec hreach)
    have hfind : Nat.find hreach = n := Nat.le_antisymm hfind_le hn_le_find
    unfold truncatedLevelTime
    rw [dif_pos hreach, hfind, min_eq_left hn.le]

/-- At a positive time and positive level, first creation of the `k`-th
threshold site is a terminal condition: the terminal threshold count is
exactly `k`, and the final position has just made its `m`-th visit.  Thus the
apparently prefix-wide stopping predicate reduces to the favorite-count datum
plus one distinguished-site local-time equality. -/
theorem thresholdCreation_iff_terminal_count_and_new_localTime
    (s : WalkPath) (m k n : ℕ) (hm : 0 < m) (hk : 0 < k) (hn : 0 < n) :
    ThresholdCreation s m k n ↔
      thresholdCount s n m = k ∧ localTime s n (s n) = m := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [Nat.succ_eq_add_one]
  constructor
  · intro hcreation
    have hcount : thresholdCount s (q + 1) m = k :=
      thresholdCount_eq_of_creation hk hcreation
    refine ⟨hcount, ?_⟩
    have hnew : s (q + 1) ∉ thresholdSites s q m := by
      intro hold
      have hsub : thresholdSites s (q + 1) m ⊆ thresholdSites s q m := by
        intro x hx
        have hx' := thresholdSites_succ_subset_insert s q m hx
        rw [Finset.mem_insert] at hx'
        rcases hx' with hxeq | hxold
        · simpa [hxeq] using hold
        · exact hxold
      have hcard := Finset.card_le_card hsub
      change thresholdCount s (q + 1) m ≤ thresholdCount s q m at hcard
      have hprior := hcreation.2 q (Nat.lt_succ_self q)
      omega
    have hprev : localTime s q (s (q + 1)) < m := by
      exact Nat.lt_of_not_ge
        (fun hlocal ↦ hnew ((mem_thresholdSites_iff s q m _ hm).mpr hlocal))
    have hfinal : m ≤ localTime s (q + 1) (s (q + 1)) :=
      (mem_thresholdSites_iff s (q + 1) m _ hm).mp
        (position_mem_thresholdSites_of_creation hk hcreation)
    have hstep : localTime s (q + 1) (s (q + 1)) =
        localTime s q (s (q + 1)) + 1 := by
      simpa using localTime_succ s q (s (q + 1))
    omega
  · rintro ⟨hcount, hlocal⟩
    refine ⟨hcount.ge, ?_⟩
    have hsucc : localTime s (q + 1) (s (q + 1)) =
        localTime s q (s (q + 1)) + 1 := by
      simpa using localTime_succ s q (s (q + 1))
    have hprevLocal : localTime s q (s (q + 1)) < m := by omega
    have hnotOld : s (q + 1) ∉ thresholdSites s q m := by
      intro hmem
      have := (mem_thresholdSites_iff s q m _ hm).mp hmem
      omega
    have hnew : s (q + 1) ∈ thresholdSites s (q + 1) m :=
      (mem_thresholdSites_iff s (q + 1) m _ hm).mpr hlocal.ge
    have hsub : thresholdSites s q m ⊆ thresholdSites s (q + 1) m :=
      thresholdSites_mono_time s m (Nat.le_succ q)
    have hproper : thresholdSites s q m ⊂ thresholdSites s (q + 1) m := by
      refine ⟨hsub, ?_⟩
      intro hreverse
      exact hnotOld (hreverse hnew)
    have hcard := Finset.card_lt_card hproper
    change thresholdCount s q m < thresholdCount s (q + 1) m at hcard
    rw [hcount] at hcard
    intro j hj
    have hjq : j ≤ q := Nat.lt_succ_iff.mp hj
    exact (thresholdCount_mono_time s m hjq).trans_lt hcard

/-- Once the genuine `k`-th level clock has been fixed strictly before the
cap, the event `M_m^k` is exactly the terminal condition that no site has yet
reached level `m+1`.  This removes the existential time appearing in
`levelFavorite` from each stopped prefix atom. -/
theorem levelFavorite_iff_nextLevel_zero_at_truncatedLevelTime
    (m k cutoff n : ℕ) (ω : StepPath) (hk : 0 < k) (hn : n < cutoff)
    (htime : truncatedLevelTime m k cutoff ω = n) :
    levelFavorite (trajectory ω) m k ↔
      thresholdCount (trajectory ω) n (m + 1) = 0 := by
  have hcreation : ThresholdCreation (trajectory ω) m k n :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff n ω hn).mp htime
  have hcount : thresholdCount (trajectory ω) n m = k :=
    thresholdCount_eq_of_creation hk hcreation
  constructor
  · intro hlevel
    obtain ⟨q, hqcount, hqnext⟩ :=
      (levelFavorite_iff_thresholdCounts (trajectory ω) m k hk).mp hlevel
    have hnq : n ≤ q := by
      by_contra hnot
      have hqn : q < n := Nat.lt_of_not_ge hnot
      have hsmall := hcreation.2 q hqn
      omega
    have hmono := thresholdCount_mono_time (trajectory ω) (m + 1) hnq
    change thresholdCount (trajectory ω) n (m + 1) ≤
      thresholdCount (trajectory ω) q (m + 1) at hmono
    rw [hqnext] at hmono
    exact Nat.eq_zero_of_le_zero hmono
  · intro hnext
    apply (levelFavorite_iff_thresholdCounts (trajectory ω) m k hk).mpr
    exact ⟨n, hcount, hnext⟩

/-- Equivalent local-time form of the same stopped `M_m^k` datum.  This is
the literal global inequality whose endpoint part is converted to domino
truncation in `PrefixLevelTruncation`. -/
theorem levelFavorite_iff_all_localTime_lt_succ_at_truncatedLevelTime
    (m k cutoff n : ℕ) (ω : StepPath) (hk : 0 < k) (hn : n < cutoff)
    (htime : truncatedLevelTime m k cutoff ω = n) :
    levelFavorite (trajectory ω) m k ↔
      ∀ x : Point, localTime (trajectory ω) n x < m + 1 := by
  rw [levelFavorite_iff_nextLevel_zero_at_truncatedLevelTime
    m k cutoff n ω hk hn htime]
  exact thresholdCount_eq_zero_iff_forall_lt
    (trajectory ω) n (m + 1) (Nat.zero_lt_succ m)

/-- The deterministic length of one insertion prefix. -/
abbrev insertionPrefixLength {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) : ℕ :=
  (insertionPrefixList r q tail).length

/-- The exact pre-stopping atom associated with one insertion vector. -/
def stoppedInsertionAtom (τ : StepPath → ℕ) {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) : Set StepPath :=
  {ω | τ ω = insertionPrefixLength r q tail ∧
    incrementPrefixList (insertionPrefixLength r q tail) ω =
      insertionPrefixList r q tail}

/-- Whether the deterministic insertion prefix is itself stopped at its end. -/
def StoppingAccepted (τ : StepPath → ℕ) {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) : Prop :=
  τ (extendPrefix (directionVectorOfList (insertionPrefixList r q tail))) =
    insertionPrefixLength r q tail

/-- For one deterministic insertion word ending before the cap, the
`StoppingAccepted` index predicate has no hidden probabilistic content: it is
precisely first creation of the threshold by that finite word. -/
theorem stoppingAccepted_truncatedLevelTime_iff_thresholdCreation
    {o : Orientation} {i : ℕ} (m k cutoff : ℕ)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction)
    (hlt : insertionPrefixLength r q tail < cutoff) :
    StoppingAccepted (truncatedLevelTime m k cutoff) r q tail ↔
      ThresholdCreation
        (trajectory
          (extendPrefix (directionVectorOfList (insertionPrefixList r q tail))))
        m k (insertionPrefixLength r q tail) := by
  exact truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
    m k cutoff (insertionPrefixLength r q tail) _ hlt

/-- Terminal-data form of the accepted-index predicate.  It isolates exactly
the distinguished last site; the remaining terminal threshold-site bounds
are the coordinatewise truncations handled by `PrefixLevelTruncation`. -/
theorem stoppingAccepted_truncatedLevelTime_iff_terminal
    {o : Orientation} {i : ℕ} (m k cutoff : ℕ)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) (hm : 0 < m) (hk : 0 < k)
    (hpos : 0 < insertionPrefixLength r q tail)
    (hlt : insertionPrefixLength r q tail < cutoff) :
    StoppingAccepted (truncatedLevelTime m k cutoff) r q tail ↔
      let s := trajectory
        (extendPrefix (directionVectorOfList (insertionPrefixList r q tail)))
      thresholdCount s (insertionPrefixLength r q tail) m = k ∧
        localTime s (insertionPrefixLength r q tail)
          (s (insertionPrefixLength r q tail)) = m := by
  rw [stoppingAccepted_truncatedLevelTime_iff_thresholdCreation
    m k cutoff r q tail hlt]
  exact thresholdCreation_iff_terminal_count_and_new_localTime _ m k _ hm hk hpos

theorem incrementPrefixList_eq_iff_stepPrefix_eq_directionVector
    (ω : StepPath) (v : List Direction) :
    incrementPrefixList v.length ω = v ↔
      stepPrefix v.length ω = directionVectorOfList v := by
  constructor
  · intro h
    apply List.ofFn_injective
    simpa [incrementPrefixList] using h
  · intro h
    unfold incrementPrefixList
    rw [h, ofFn_directionVectorOfList]

/-- On an accepted word the stopping constraint is automatic, so the atom is
an ordinary exact prefix cylinder. -/
theorem stoppedInsertionAtom_eq_cylinder {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) (hacc : StoppingAccepted τ r q tail) :
    stoppedInsertionAtom τ r q tail =
      {ω | stepPrefix (insertionPrefixLength r q tail) ω =
        directionVectorOfList (insertionPrefixList r q tail)} := by
  ext ω
  unfold stoppedInsertionAtom
  simp only [Set.mem_ofPred_eq]
  rw [incrementPrefixList_eq_iff_stepPrefix_eq_directionVector]
  constructor
  · exact fun h ↦ h.2
  · intro hp
    refine ⟨?_, hp⟩
    apply stoppingTime_eq_of_stepPrefix_eq hτ hacc
    rw [stepPrefix_extendPrefix]
    exact hp

/-- Exact probability of one accepted stopped insertion atom. -/
theorem fairSteps_stoppedInsertionAtom {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) (hacc : StoppingAccepted τ r q tail) :
    fairSteps (stoppedInsertionAtom τ r q tail) =
      (1 / 4 : ℝ≥0∞) ^ insertionPrefixLength r q tail := by
  rw [stoppedInsertionAtom_eq_cylinder hτ r q tail hacc]
  exact Erdos1165.fairSteps_stepPrefix_singleton_mass _ _

/-- Real point mass of one exact prefix word. -/
noncomputable def insertionPrefixMass {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) : ℝ :=
  (1 / 4 : ℝ) ^ insertionPrefixLength r q tail

/-- The common mass factor carried by a fixed external word and boundary
tail. -/
noncomputable def prefixFiberConstant (i : ℕ) (tail : List Direction) : ℝ :=
  (1 / 4 : ℝ) ^ tail.length * (16 * (1 / 15 : ℝ) ^ (i + 1))

/-- The point mass is a fibre-wide constant times the product geometric
weight.  Crucially, the constant does not depend on the insertion vector. -/
theorem insertionPrefixMass_eq_const_mul_gapVectorMass
    {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) :
    insertionPrefixMass r q tail =
      prefixFiberConstant i tail * gapVectorMass q := by
  classical
  unfold insertionPrefixMass insertionPrefixLength prefixFiberConstant
  rw [insertionPrefixList_length, pow_add, pow_mul]
  have hfour : (1 / 4 : ℝ) ^ 2 = 1 / 16 := by norm_num
  rw [hfour]
  unfold gapVectorMass geometricGapMass
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum, pow_add]
  have hbase :
      (1 / 16 : ℝ) ^ i =
        16 * (1 / 15 : ℝ) ^ (i + 1) * (15 / 16 : ℝ) ^ (i + 1) := by
    symm
    calc
      16 * (1 / 15 : ℝ) ^ (i + 1) * (15 / 16 : ℝ) ^ (i + 1) =
          16 * ((1 / 15 : ℝ) ^ (i + 1) * (15 / 16 : ℝ) ^ (i + 1)) := by
            ring
      _ = 16 * (((1 / 15 : ℝ) * (15 / 16 : ℝ)) ^ (i + 1)) := by
            rw [mul_pow]
      _ = (1 / 16 : ℝ) ^ i := by
            norm_num
            rw [pow_succ]
            ring
  rw [hbase]
  ring

theorem fairSteps_stoppedInsertionAtom_eq_ofReal {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) (hacc : StoppingAccepted τ r q tail) :
    fairSteps (stoppedInsertionAtom τ r q tail) =
      ENNReal.ofReal (insertionPrefixMass r q tail) := by
  rw [fairSteps_stoppedInsertionAtom hτ r q tail hacc]
  unfold insertionPrefixMass
  rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 1 / 4)]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  norm_num

theorem pairDirectionList_flatMap_blocks (w : List Block) :
    pairDirectionList (w.flatMap (fun b ↦ [b.1, b.2])) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [pairDirectionList, ih]

theorem insertionPrefixList_injective {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (tail : List Direction) :
    Function.Injective (fun q : Fin (i + 1) → ℕ ↦ insertionPrefixList r q tail) := by
  intro q q' h
  unfold insertionPrefixList at h
  have hflat := List.append_cancel_right h
  have hword := congrArg pairDirectionList hflat
  rw [pairDirectionList_flatMap_blocks, pairDirectionList_flatMap_blocks] at hword
  exact insertGapVector_injective r hword

/-- Surjectivity of insertion coordinates on a fixed external retained word. -/
theorem exists_insertGapVector_of_delete_eq (o : Orientation) (w : List Block)
    {i : ℕ} (r : Fin i → RetainedBlock o)
    (hdelete : deleteRemovableBlocks o w = retainedWord r) :
    ∃ q : Fin (i + 1) → ℕ, insertGapVector r q = w := by
  obtain ⟨i', r', q, hq⟩ := exists_insertGapVector o w
  have hre : retainedWord r' = retainedWord r := by
    rw [← hdelete, ← hq]
    exact (deleteRemovableBlocks_insertGapVector r' q).symm
  have hi : i' = i := by
    have := congrArg List.length hre
    simpa [retainedWord] using this
  subst i'
  have hr : r' = r := by
    funext k
    apply Subtype.ext
    have hof := List.ofFn_injective hre
    exact congrFun hof k
  subst r'
  exact ⟨q, hq⟩

/-- Fixed-word surjectivity with the intrinsic deterministic coordinate cap. -/
theorem exists_capped_insertGapVector_of_delete_eq (o : Orientation) (w : List Block)
    {i : ℕ} (r : Fin i → RetainedBlock o)
    (hdelete : deleteRemovableBlocks o w = retainedWord r) :
    ∃ q : CappedCoordinates i w.length,
      insertGapVector r (fun k ↦ (q k : ℕ)) = w := by
  obtain ⟨q, hq⟩ := exists_insertGapVector_of_delete_eq o w r hdelete
  have hlen : i + ∑ k, q k = w.length := by
    rw [← hq]
    exact (insertGapVector_length r q).symm
  have hbound : ∀ k, q k < w.length + 1 := by
    intro k
    have hk : q k ≤ ∑ j, q j :=
      Finset.single_le_sum (s := Finset.univ) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ k)
    omega
  exact ⟨fun k ↦ ⟨q k, hbound k⟩, hq⟩

theorem pairDirectionList_length (v : List Direction) :
    (pairDirectionList v).length = v.length / 2 := by
  induction v using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp [pairDirectionList]
  | cons_cons a b v ih _ =>
      simp [pairDirectionList, ih]
      omega

/-- Accepted stopped atoms are prefix-free, even though their deterministic
cylinder lengths vary with the insertion vector. -/
theorem stoppedInsertionAtom_pairwise_disjoint {τ : StepPath → ℕ}
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (tail : List Direction) :
    Pairwise fun q q' : Fin (i + 1) → ℕ ↦
      Disjoint (stoppedInsertionAtom τ r q tail)
        (stoppedInsertionAtom τ r q' tail) := by
  intro q q' hqq'
  rw [Set.disjoint_left]
  intro ω hq hq'
  apply hqq'
  apply insertionPrefixList_injective r tail
  have hlen : insertionPrefixLength r q tail = insertionPrefixLength r q' tail :=
    hq.1.symm.trans hq'.1
  unfold stoppedInsertionAtom at hq hq'
  simp only [Set.mem_ofPred_eq] at hq hq'
  rw [hlen] at hq
  exact hq.2.symm.trans hq'.2

/-! ## A finite capped partition and its exact mass transport -/

/-- Capped insertion vectors satisfying arbitrary fixed fibre data and ending
at the supplied finite stopping time. -/
abbrev AcceptedCappedCoordinates (τ : StepPath → ℕ)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) (cap : ℕ)
    (tail : List Direction) (P : CappedCoordinates i cap → Prop) :=
  {q : CappedCoordinates i cap //
    P q ∧ StoppingAccepted τ r (fun k ↦ (q k : ℕ)) tail}

noncomputable instance acceptedCappedCoordinatesFintype (τ : StepPath → ℕ)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) (cap : ℕ)
    (tail : List Direction) (P : CappedCoordinates i cap → Prop) :
    Fintype (AcceptedCappedCoordinates τ r cap tail P) :=
  Fintype.ofFinite _

/-- The finite union of all accepted stopped atoms in a capped fibre. -/
def preStoppingFiberEvent (τ : StepPath → ℕ)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) (cap : ℕ)
    (tail : List Direction) (P : CappedCoordinates i cap → Prop) : Set StepPath :=
  ⋃ q : AcceptedCappedCoordinates τ r cap tail P,
    stoppedInsertionAtom τ r (fun k ↦ (q.1 k : ℕ)) tail

/-- The accepted capped atoms form a genuine finite prefix-free partition. -/
theorem acceptedCappedAtoms_pairwise_disjoint (τ : StepPath → ℕ)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) (cap : ℕ)
    (tail : List Direction) (P : CappedCoordinates i cap → Prop) :
    Pairwise fun q q' : AcceptedCappedCoordinates τ r cap tail P ↦
      Disjoint (stoppedInsertionAtom τ r (fun k ↦ (q.1 k : ℕ)) tail)
        (stoppedInsertionAtom τ r (fun k ↦ (q'.1 k : ℕ)) tail) := by
  intro q q' hqq'
  apply stoppedInsertionAtom_pairwise_disjoint r tail
  intro h
  apply hqq'
  apply Subtype.ext
  funext k
  apply Fin.ext
  exact congrFun h k

/-- Measurability of the finite stopped insertion fibre. -/
theorem measurableSet_preStoppingFiberEvent {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (cap : ℕ) (tail : List Direction)
    (P : CappedCoordinates i cap → Prop) :
    MeasurableSet (preStoppingFiberEvent τ r cap tail P) := by
  classical
  exact MeasurableSet.iUnion fun q ↦ by
    rw [stoppedInsertionAtom_eq_cylinder hτ r _ tail q.2.2]
    exact measurableSet_eq_fun (measurable_stepPrefix _) measurable_const

/-- Every stopped prefix below `cutoff`, with fixed retained word and fixed
boundary tail, belongs to the corresponding capped insertion partition. -/
theorem mem_preStoppingFiberEvent_of_fixed_external
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    {o : Orientation} {i cutoff : ℕ} (r : Fin i → RetainedBlock o)
    (tail : List Direction) (ω : StepPath) (hcut : τ ω ≤ cutoff)
    (hdelete : deleteRemovableBlocks o (prefixBlockWord (τ ω) ω) = retainedWord r)
    (htail : prefixDirectionTail (τ ω) ω = tail) :
    ω ∈ preStoppingFiberEvent τ r cutoff tail (fun _ ↦ True) := by
  classical
  let w := prefixBlockWord (τ ω) ω
  obtain ⟨q, hq⟩ := exists_capped_insertGapVector_of_delete_eq o w r hdelete
  have hwlen : w.length ≤ cutoff := by
    calc
      w.length = (incrementPrefixList (τ ω) ω).length / 2 :=
        pairDirectionList_length _
      _ = (τ ω) / 2 := by simp [incrementPrefixList]
      _ ≤ τ ω := Nat.div_le_self _ _
      _ ≤ cutoff := hcut
  let qc : CappedCoordinates i cutoff := fun k ↦
    ⟨q k, (q k).isLt.trans_le (Nat.succ_le_succ hwlen)⟩
  have hqnat : (fun k ↦ (qc k : ℕ)) = fun k ↦ (q k : ℕ) := by rfl
  have hword : insertGapVector r (fun k ↦ (qc k : ℕ)) = w := by
    rw [hqnat]
    exact hq
  have hlist : insertionPrefixList r (fun k ↦ (qc k : ℕ)) tail =
      incrementPrefixList (τ ω) ω := by
    unfold insertionPrefixList
    rw [hword, ← htail]
    exact incrementPrefixList_decompose (τ ω) ω
  have hlength : insertionPrefixLength r (fun k ↦ (qc k : ℕ)) tail = τ ω := by
    have := congrArg List.length hlist
    simpa [insertionPrefixLength, incrementPrefixList] using this
  have hlist' :
      incrementPrefixList
          (insertionPrefixLength r (fun k ↦ (qc k : ℕ)) tail) ω =
        insertionPrefixList r (fun k ↦ (qc k : ℕ)) tail := by
    rw [hlength]
    exact hlist.symm
  have hpω :
      stepPrefix (insertionPrefixLength r (fun k ↦ (qc k : ℕ)) tail) ω =
      directionVectorOfList
        (insertionPrefixList r (fun k ↦ (qc k : ℕ)) tail) :=
    (incrementPrefixList_eq_iff_stepPrefix_eq_directionVector _ _).mp hlist'
  have hacc : StoppingAccepted τ r (fun k ↦ (qc k : ℕ)) tail := by
    apply stoppingTime_eq_of_stepPrefix_eq hτ hlength.symm
    rw [stepPrefix_extendPrefix]
    exact hpω.symm
  unfold preStoppingFiberEvent
  apply Set.mem_iUnion.mpr
  refine ⟨⟨qc, trivial, hacc⟩, ?_⟩
  change τ ω = _ ∧ incrementPrefixList _ ω = _
  exact ⟨hlength.symm, hlist'⟩

theorem fairSteps_preStoppingFiberEvent {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (cap : ℕ) (tail : List Direction)
    (P : CappedCoordinates i cap → Prop) :
    fairSteps (preStoppingFiberEvent τ r cap tail P) =
      ENNReal.ofReal
        (∑ q : AcceptedCappedCoordinates τ r cap tail P,
          insertionPrefixMass r (fun k ↦ (q.1 k : ℕ)) tail) := by
  classical
  have hmeas : ∀ q : AcceptedCappedCoordinates τ r cap tail P,
      MeasurableSet (stoppedInsertionAtom τ r (fun k ↦ (q.1 k : ℕ)) tail) := by
    intro q
    rw [stoppedInsertionAtom_eq_cylinder hτ r _ tail q.2.2]
    exact measurableSet_eq_fun (measurable_stepPrefix _) measurable_const
  have hdis : Pairwise fun q q' : AcceptedCappedCoordinates τ r cap tail P ↦
      Disjoint (stoppedInsertionAtom τ r (fun k ↦ (q.1 k : ℕ)) tail)
        (stoppedInsertionAtom τ r (fun k ↦ (q'.1 k : ℕ)) tail) := by
    exact acceptedCappedAtoms_pairwise_disjoint τ r cap tail P
  unfold preStoppingFiberEvent
  rw [measure_iUnion hdis hmeas]
  simp_rw [show ∀ q : AcceptedCappedCoordinates τ r cap tail P,
      fairSteps (stoppedInsertionAtom τ r (fun k ↦ (q.1 k : ℕ)) tail) =
        ENNReal.ofReal
          (insertionPrefixMass r (fun k ↦ (q.1 k : ℕ)) tail) from
    fun q ↦ fairSteps_stoppedInsertionAtom_eq_ofReal hτ r _ tail q.2.2]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg]
  · intro q _
    unfold insertionPrefixMass
    positivity

/-- Exact transport of the finite stopped-prefix partition to the geometric
coordinate weights used in the spatial disintegration. -/
theorem fairSteps_preStoppingFiberEvent_eq_geometricSum {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (cap : ℕ) (tail : List Direction)
    (P : CappedCoordinates i cap → Prop) :
    fairSteps (preStoppingFiberEvent τ r cap tail P) =
      ENNReal.ofReal
        (prefixFiberConstant i tail *
          ∑ q : AcceptedCappedCoordinates τ r cap tail P,
            gapVectorMass (fun k ↦ (q.1 k : ℕ))) := by
  rw [fairSteps_preStoppingFiberEvent hτ r cap tail P]
  congr 1
  simp_rw [insertionPrefixMass_eq_const_mul_gapVectorMass]
  rw [Finset.mul_sum]

/-! ## Distinguished-domino marginalization -/

/-- Adding and then summing arbitrary finite distinguished-domino data only
contributes a common factor, which cancels from the away-domino conditional
law. -/
theorem distinguished_marginal_conditional_factorization
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ)
    {δ : Type*} [Fintype δ] (distinguishedMass : δ → ℝ)
    (hDist : (∑ d, distinguishedMass d) ≠ 0)
    (ℓ : UpperTruncatedDominoTotals x r D upper) :
    (∑ d, upperTotalsJointMass x r D upper ℓ * distinguishedMass d) /
        (∑ z : UpperTruncatedDominoTotals x r D upper,
          ∑ d, upperTotalsJointMass x r D upper z * distinguishedMass d) =
      ∏ b : AwayDomino x r D,
        upperTruncatedDominoMass x r upper b.1 (ℓ b) := by
  classical
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [mul_div_mul_right _ _ hDist]
  exact upperTotals_conditional_factorization x r D upper ℓ

end Erdos1165.PreStoppingFiber
