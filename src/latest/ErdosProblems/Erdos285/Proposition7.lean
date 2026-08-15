import ErdosProblems.Erdos285.ExactCorrection
import ErdosProblems.Erdos285.Lemma15
import ErdosProblems.Erdos285.Lemma16
import ErdosProblems.Erdos285.LcmTelescope
import ErdosProblems.Erdos285.PrimePowers
import ErdosProblems.Erdos285.RoughCounts

/-!
# Martin's Proposition 7: descent and cardinality bookkeeping

This file contains the part of Proposition 7 which is independent of the
congruence calculations in Lemmas 15 and 16.  An `EliminationStep` records the
output of either lemma.  Its new rational has a strictly smaller largest exact
prime-power part, and every denominator introduced at the step is tagged by
the part which was eliminated.  Strong induction then proves termination,
pairwise distinctness of all denominators, and the bound `2 * piStar y` on the
number of terms.

The final section proves the finite-set bookkeeping for Martin's telescoping
padding operation.  Replacing the largest denominator `n` by `m + 1` larger
denominators increases the cardinality by exactly `m`, preserves the reciprocal
sum, and gives an explicit square bound for every new denominator.
-/

namespace Erdos285.Proposition7

open Finset
open scoped BigOperators

noncomputable section

open PrimePowers

lemma initialLcm_mono {x y : ℕ} (hxy : x ≤ y) :
    initialLcm x ≤ initialLcm y := by
  have hdiv : initialLcm x ∣ initialLcm y := by
    apply Finset.lcm_dvd
    intro n hn
    exact Finset.dvd_lcm (s := Icc 1 y) (f := id)
      (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hxy⟩)
  have hpos : 0 < initialLcm y := Nat.pos_of_ne_zero (by simp [initialLcm])
  exact Nat.le_of_dvd hpos hdiv

/-! ## Strict growth of the prime-power counting function -/

/-- Passing a prime-power endpoint strictly increases `piStar`. -/
lemma piStar_lt_of_lt_of_isPrimePow {x q : ℕ} (hxq : x < q)
    (hq : IsPrimePow q) : piStar x < piStar q := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨primePowersUpTo_mono hxq.le, ?_⟩
  intro heq
  have hqmem : q ∈ primePowersUpTo q := mem_primePowersUpTo.mpr ⟨hq, le_rfl⟩
  have : q ∈ primePowersUpTo x := heq.symm ▸ hqmem
  exact (not_le_of_gt hxq) (mem_primePowersUpTo.mp this).2

lemma piStar_eq_succ_pred_of_isPrimePow {q : ℕ} (hq : IsPrimePow q) :
    piStar q = piStar (q - 1) + 1 := by
  have hqpos : 0 < q := hq.pos
  have hqnot : q ∉ primePowersUpTo (q - 1) := by
    intro hmem
    have hle := (mem_primePowersUpTo.mp hmem).2
    omega
  have heq : primePowersUpTo q = insert q (primePowersUpTo (q - 1)) := by
    ext t
    rw [mem_primePowersUpTo]
    simp only [Finset.mem_insert, mem_primePowersUpTo]
    constructor
    · rintro ⟨htpp, htq⟩
      by_cases ht : t = q
      · exact Or.inl ht
      · exact Or.inr ⟨htpp, by omega⟩
    · rintro (rfl | ⟨htpp, htq⟩)
      · exact ⟨hq, le_rfl⟩
      · exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩
  rw [piStar, piStar, heq, Finset.card_insert_of_notMem hqnot]

lemma piStar_eq_pred_of_not_isPrimePow {q : ℕ} (hq : ¬ IsPrimePow q) :
    piStar q = piStar (q - 1) := by
  have heq : primePowersUpTo q = primePowersUpTo (q - 1) := by
    ext t
    rw [mem_primePowersUpTo, mem_primePowersUpTo]
    constructor
    · rintro ⟨htpp, htq⟩
      exact ⟨htpp, by
        by_cases ht : t = q
        · exact False.elim (hq (ht ▸ htpp))
        · have htpos := htpp.pos
          omega⟩
    · rintro ⟨htpp, htq⟩
      exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩
  change (primePowersUpTo q).card = (primePowersUpTo (q - 1)).card
  exact congrArg Finset.card heq

/-! ## A generic Lemma 15/16 step -/

/--
The common output needed from Martin's Lemmas 15 and 16 at a rational `r`.

The concrete lemmas additionally provide interval and exponential estimates.
Those estimates imply `le_bound`; the recursion itself needs only the fields
below.  `tagged` is what makes denominators introduced at different stages
automatically distinct.
-/
structure EliminationStep (B : ℕ) (r : ℚ) (U : Finset ℕ) : Prop where
  card_le_two : U.card ≤ 2
  zero_not_mem : 0 ∉ U
  le_bound : ∀ n ∈ U, n ≤ B
  tagged : ∀ n ∈ U,
    largestPrimePowerPart n = largestPrimePowerPart r.den
  descends :
    largestPrimePowerPart (r - UnitFractions.rec_sum U).den <
      largestPrimePowerPart r.den

/-- Lemma 16 supplies the concrete current-factor step below `lo`.  The sole
numerical input is the source bound `initialLcm lo ≤ B`. -/
theorem exists_eliminationStep_of_lemma16
    (B lo : ℕ) (hL : initialLcm lo ≤ B)
    (r : ℚ) (hden : r.den ≠ 1)
    (hrlo : largestPrimePowerPart r.den ≤ lo) :
    ∃ U : Finset ℕ, EliminationStep B r U := by
  have hden2 : 2 ≤ r.den := by
    have := r.den_pos
    omega
  let q := largestPrimePowerPart r.den
  have hqpp : IsPrimePow q := (largestPrimePowerPart_spec hden2).1
  obtain ⟨p, e, hp, he, hqpow⟩ := (isPrimePow_nat_iff q).mp hqpp
  obtain ⟨a, n, haPos, haLe, hpa, haL, hnEq, hnLower, hqN, hqNpart,
      hnSmooth, hnLargest, hdesc⟩ :=
    Lemma16.smallPrimePower_elimination (p := p) (e := e) (q := q)
      r hp he hqpow.symm rfl
  have hnPos : 0 < n := by
    rw [hnEq]
    have hLpos : 0 < initialLcm q :=
      Nat.pos_of_ne_zero (by simp [initialLcm])
    exact Nat.div_pos
      (Nat.le_of_dvd hLpos haL) haPos
  have hnLeLq : n ≤ initialLcm q := by
    rw [hnEq]
    exact Nat.div_le_self _ _
  have hnB : n ≤ B :=
    hnLeLq.trans ((initialLcm_mono hrlo).trans hL)
  refine ⟨{n}, ?_⟩
  refine
    { card_le_two := by simp
      zero_not_mem := by
        simp only [Finset.mem_singleton]
        exact hnPos.ne'.symm
      le_bound := ?_
      tagged := ?_
      descends := ?_ }
  · intro m hm
    simp only [Finset.mem_singleton] at hm
    subst m
    exact hnB
  · intro m hm
    simp only [Finset.mem_singleton] at hm
    subst m
    exact hnLargest
  · simpa [UnitFractions.rec_sum] using hdesc

/-- A Lemma 16 step together with its exact share of the telescoping
reciprocal budget. -/
structure SmallEliminationStep (B : ℕ) (r : ℚ) (U : Finset ℕ) : Prop
    extends EliminationStep B r U where
  card_le_one : U.card ≤ 1
  rec_sum_le_cost : UnitFractions.rec_sum U ≤
    LcmTelescope.primePowerCost (largestPrimePowerPart r.den)

theorem exists_smallEliminationStep_of_lemma16
    (B lo : ℕ) (hL : initialLcm lo ≤ B)
    (r : ℚ) (hden : r.den ≠ 1)
    (hrlo : largestPrimePowerPart r.den ≤ lo) :
    ∃ U : Finset ℕ, SmallEliminationStep B r U := by
  have hden2 : 2 ≤ r.den := by
    have := r.den_pos
    omega
  let q := largestPrimePowerPart r.den
  have hqpp : IsPrimePow q := (largestPrimePowerPart_spec hden2).1
  obtain ⟨p, e, hp, he, hqpow⟩ := (isPrimePow_nat_iff q).mp hqpp
  obtain ⟨a, n, haPos, haLe, hpa, haL, hnEq, hnLower, hqN, hqNpart,
      hnSmooth, hnLargest, hdesc⟩ :=
    Lemma16.smallPrimePower_elimination (p := p) (e := e) (q := q)
      r hp he hqpow.symm rfl
  have hLpos : 0 < initialLcm q :=
    Nat.pos_of_ne_zero (by simp [initialLcm])
  have hnPos : 0 < n := by
    rw [hnEq]
    exact Nat.div_pos (Nat.le_of_dvd hLpos haL) haPos
  have hnLeLq : n ≤ initialLcm q := by
    rw [hnEq]
    exact Nat.div_le_self _ _
  have hnB : n ≤ B :=
    hnLeLq.trans ((initialLcm_mono hrlo).trans hL)
  have hunitEq : (1 : ℚ) / n = (a : ℚ) / initialLcm q := by
    rw [hnEq, Nat.cast_div_charZero haL]
    have haQ : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hLQ : (initialLcm q : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hLpos.ne'
    field_simp [haQ, hLQ]
  have hcost : (1 : ℚ) / n ≤ LcmTelescope.primePowerCost q := by
    have hmin : q.minFac = p := by
      rw [← hqpow, hp.pow_minFac he.ne']
    rw [hunitEq, LcmTelescope.primePowerCost, hmin]
    exact (div_le_div_iff_of_pos_right (by exact_mod_cast hLpos)).2
      (by exact_mod_cast haLe)
  refine ⟨{n}, ?_⟩
  refine
    { toEliminationStep :=
        { card_le_two := by simp
          zero_not_mem := by simpa using hnPos.ne
          le_bound := by
            intro m hm
            simp only [Finset.mem_singleton] at hm
            subst m
            exact hnB
          tagged := by
            intro m hm
            simp only [Finset.mem_singleton] at hm
            subst m
            exact hnLargest
          descends := by simpa [UnitFractions.rec_sum] using hdesc }
      card_le_one := by simp
      rec_sum_le_cost := by simpa [UnitFractions.rec_sum, q] using hcost }

/--
The result of running all elimination steps.  The final residual is an integer;
`tag_le` remembers enough information to prove disjointness at the preceding
recursive stage.
-/
structure EliminationResult (B : ℕ) (r : ℚ) (E : Finset ℕ) : Prop where
  zero_not_mem : 0 ∉ E
  le_bound : ∀ n ∈ E, n ≤ B
  card_le : E.card ≤ 2 * piStar (largestPrimePowerPart r.den)
  tag_le : ∀ n ∈ E,
    largestPrimePowerPart n ≤ largestPrimePowerPart r.den
  residual_isInt : ∃ z : ℤ, r - UnitFractions.rec_sum E = z

/-- The Lemma 16 descent with the reciprocal cost retained.  Since Lemma 16
adds one denominator at each visited prime power, its cost is bounded by the
exact LCM telescope below the initial largest part. -/
structure SmallEliminationResult (B : ℕ) (r : ℚ) (E : Finset ℕ) : Prop where
  zero_not_mem : 0 ∉ E
  le_bound : ∀ n ∈ E, n ≤ B
  card_le : E.card ≤ piStar (largestPrimePowerPart r.den)
  tag_le : ∀ n ∈ E,
    largestPrimePowerPart n ≤ largestPrimePowerPart r.den
  residual_isInt : ∃ z : ℤ, r - UnitFractions.rec_sum E = z
  rec_sum_le_cost : UnitFractions.rec_sum E ≤
    LcmTelescope.smallPrimePowerCost (largestPrimePowerPart r.den)

/-- Complete current-factor Lemma 16 descent, including Martin's telescoping
budget. -/
theorem exists_smallEliminationResult_of_lemma16
    (B lo : ℕ) (hL : initialLcm lo ≤ B)
    (r : ℚ) (hrlo : largestPrimePowerPart r.den ≤ lo) :
    ∃ E : Finset ℕ, SmallEliminationResult B r E := by
  suffices hmain : ∀ q : ℕ, ∀ s : ℚ,
      largestPrimePowerPart s.den = q → q ≤ lo →
        ∃ E : Finset ℕ, SmallEliminationResult B s E by
    exact hmain (largestPrimePowerPart r.den) r rfl hrlo
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro s hqeq hqlo
      by_cases hden : s.den = 1
      · refine ⟨∅, ?_⟩
        refine
          { zero_not_mem := by simp
            le_bound := by simp
            card_le := by simp
            tag_le := by simp
            residual_isInt := ?_
            rec_sum_le_cost := ?_ }
        · simpa using isInt_of_primePowerParts_empty
            ((den_eq_one_iff_primePowerParts_empty s).mp hden)
        · simp only [UnitFractions.rec_sum, Finset.sum_empty]
          rw [LcmTelescope.smallPrimePowerCost]
          exact Finset.sum_nonneg fun t _ ↦
            LcmTelescope.primePowerCost_nonneg t
      · obtain ⟨U, hU⟩ :=
          exists_smallEliminationStep_of_lemma16 B lo hL s hden
            (hqeq.trans_le hqlo)
        let s' : ℚ := s - UnitFractions.rec_sum U
        have hdesc : largestPrimePowerPart s'.den < q := by
          simpa [s', hqeq] using hU.descends
        obtain ⟨E, hE⟩ := ih (largestPrimePowerPart s'.den) hdesc s' rfl
          (hdesc.le.trans hqlo)
        have hden2 : 2 ≤ s.den := by
          have := s.den_pos
          omega
        have hqpp : IsPrimePow q := by
          rw [← hqeq]
          exact (largestPrimePowerPart_spec hden2).1
        have hpi : piStar (largestPrimePowerPart s'.den) < piStar q :=
          piStar_lt_of_lt_of_isPrimePow hdesc hqpp
        have hdisjoint : Disjoint U E := by
          rw [Finset.disjoint_left]
          intro n hnU hnE
          have htagU : largestPrimePowerPart n = q := by
            simpa [hqeq] using hU.tagged n hnU
          have htagE := hE.tag_le n hnE
          omega
        refine ⟨U ∪ E, ?_⟩
        refine
          { zero_not_mem := ?_
            le_bound := ?_
            card_le := ?_
            tag_le := ?_
            residual_isInt := ?_
            rec_sum_le_cost := ?_ }
        · simpa only [Finset.mem_union, not_or] using
            ⟨hU.zero_not_mem, hE.zero_not_mem⟩
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · exact hU.le_bound n hnU
          · exact hE.le_bound n hnE
        · rw [Finset.card_union_of_disjoint hdisjoint]
          calc
            U.card + E.card ≤ 1 + piStar (largestPrimePowerPart s'.den) :=
              Nat.add_le_add hU.card_le_one hE.card_le
            _ ≤ piStar q := by omega
            _ = piStar (largestPrimePowerPart s.den) := by rw [hqeq]
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · rw [hU.tagged n hnU, hqeq]
          · exact (hE.tag_le n hnE).trans hdesc.le |>.trans_eq hqeq.symm
        · obtain ⟨z, hz⟩ := hE.residual_isInt
          refine ⟨z, ?_⟩
          rw [UnitFractions.rec_sum_disjoint hdisjoint]
          dsimp [s'] at hz
          linarith
        · rw [UnitFractions.rec_sum_disjoint hdisjoint]
          calc
            UnitFractions.rec_sum U + UnitFractions.rec_sum E ≤
                LcmTelescope.primePowerCost q +
                  LcmTelescope.smallPrimePowerCost
                    (largestPrimePowerPart s'.den) := by
              exact add_le_add (by simpa [hqeq] using hU.rec_sum_le_cost)
                hE.rec_sum_le_cost
            _ ≤ LcmTelescope.smallPrimePowerCost q :=
              LcmTelescope.primePowerCost_add_smallPrimePowerCost_of_lt
                hdesc hqpp
            _ = LcmTelescope.smallPrimePowerCost
                (largestPrimePowerPart s.den) := by rw [hqeq]

/-- A rational integer of absolute value less than one is zero. -/
lemma eq_zero_of_isInt_of_abs_lt_one {r : ℚ} (hint : ∃ z : ℤ, r = z)
    (hr : |r| < 1) : r = 0 := by
  obtain ⟨z, rfl⟩ := hint
  have hz : |z| < 1 := by exact_mod_cast hr
  have hznonneg : 0 ≤ |z| := abs_nonneg z
  have habs : |z| = 0 := by omega
  simp only [abs_eq_zero] at habs
  simp [habs]

/-- The terminal integer residual is zero as soon as the independent size
estimate places it in `(-1,1)`. -/
lemma EliminationResult.residual_eq_zero {B : ℕ} {r : ℚ} {E : Finset ℕ}
    (h : EliminationResult B r E)
    (hsmall : |r - UnitFractions.rec_sum E| < 1) :
    r - UnitFractions.rec_sum E = 0 :=
  eq_zero_of_isInt_of_abs_lt_one h.residual_isInt hsmall

/--
Well-founded prime-power elimination.

The argument `step` is an ordinary theorem argument.  Supplying the concrete
Lemma 15 branch above the logarithmic cutoff and the Lemma 16 branch below it
therefore introduces no new declaration-level assumption.
-/
theorem exists_eliminationResult
    (B : ℕ)
    (step : ∀ r : ℚ, r.den ≠ 1 →
      ∃ U : Finset ℕ, EliminationStep B r U)
    (r : ℚ) :
    ∃ E : Finset ℕ, EliminationResult B r E := by
  suffices hmain : ∀ q : ℕ, ∀ r : ℚ,
      largestPrimePowerPart r.den = q →
        ∃ E : Finset ℕ, EliminationResult B r E by
    exact hmain (largestPrimePowerPart r.den) r rfl
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro r hqeq
      by_cases hden : r.den = 1
      · refine ⟨∅, ?_⟩
        refine
          { zero_not_mem := by simp
            le_bound := by simp
            card_le := by simp
            tag_le := by simp
            residual_isInt := ?_ }
        have hempty : primePowerParts r.den = ∅ :=
          (den_eq_one_iff_primePowerParts_empty r).mp hden
        simpa using isInt_of_primePowerParts_empty (r := r) hempty
      · obtain ⟨U, hU⟩ := step r hden
        let r' : ℚ := r - UnitFractions.rec_sum U
        have hdesc : largestPrimePowerPart r'.den < q := by
          simpa [r', hqeq] using hU.descends
        obtain ⟨E, hE⟩ := ih (largestPrimePowerPart r'.den) hdesc r' rfl
        have hden2 : 2 ≤ r.den := by
          have := r.den_pos
          omega
        have hqpp : IsPrimePow q := by
          rw [← hqeq]
          exact (largestPrimePowerPart_spec hden2).1
        have hpi : piStar (largestPrimePowerPart r'.den) < piStar q :=
          piStar_lt_of_lt_of_isPrimePow hdesc hqpp
        have hdisjoint : Disjoint U E := by
          rw [Finset.disjoint_left]
          intro n hnU hnE
          have htagU : largestPrimePowerPart n = q := by
            simpa [hqeq] using hU.tagged n hnU
          have htagE : largestPrimePowerPart n ≤
              largestPrimePowerPart r'.den := hE.tag_le n hnE
          omega
        refine ⟨U ∪ E, ?_⟩
        refine
          { zero_not_mem := ?_
            le_bound := ?_
            card_le := ?_
            tag_le := ?_
            residual_isInt := ?_ }
        · simpa only [Finset.mem_union, not_or] using
            ⟨hU.zero_not_mem, hE.zero_not_mem⟩
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · exact hU.le_bound n hnU
          · exact hE.le_bound n hnE
        · rw [Finset.card_union_of_disjoint hdisjoint]
          calc
            U.card + E.card ≤ 2 + 2 * piStar (largestPrimePowerPart r'.den) :=
              Nat.add_le_add hU.card_le_two hE.card_le
            _ ≤ 2 * piStar q := by omega
            _ = 2 * piStar (largestPrimePowerPart r.den) := by rw [hqeq]
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · rw [hU.tagged n hnU, hqeq]
          · exact (hE.tag_le n hnE).trans hdesc.le |>.trans_eq hqeq.symm
        · obtain ⟨z, hz⟩ := hE.residual_isInt
          refine ⟨z, ?_⟩
          rw [UnitFractions.rec_sum_disjoint hdisjoint]
          dsimp [r'] at hz
          linarith

/-- A version whose cardinality and tags are bounded by any ambient cutoff
`y` containing the initial largest prime-power part. -/
theorem exists_eliminationResult_le
    (B y : ℕ)
    (step : ∀ r : ℚ, r.den ≠ 1 →
      ∃ U : Finset ℕ, EliminationStep B r U)
    (r : ℚ) (hr : largestPrimePowerPart r.den ≤ y) :
    ∃ E : Finset ℕ,
      0 ∉ E ∧
      (∀ n ∈ E, n ≤ B) ∧
      E.card ≤ 2 * piStar y ∧
      (∀ n ∈ E, largestPrimePowerPart n ≤ y) ∧
      ∃ z : ℤ, r - UnitFractions.rec_sum E = z := by
  obtain ⟨E, hE⟩ := exists_eliminationResult B step r
  refine ⟨E, hE.zero_not_mem, hE.le_bound, ?_, ?_, hE.residual_isInt⟩
  · exact hE.card_le.trans (Nat.mul_le_mul_left 2 (piStar_mono hr))
  · intro n hn
    exact (hE.tag_le n hn).trans hr

/-- The current-factor recursion when the concrete Lemma 16 step is available
only below an ambient cutoff. -/
theorem exists_eliminationResult_below
    (B lo : ℕ)
    (step : ∀ r : ℚ, r.den ≠ 1 →
      largestPrimePowerPart r.den ≤ lo →
        ∃ U : Finset ℕ, EliminationStep B r U)
    (r : ℚ) (hrlo : largestPrimePowerPart r.den ≤ lo) :
    ∃ E : Finset ℕ, EliminationResult B r E := by
  suffices hmain : ∀ q : ℕ, ∀ r : ℚ,
      largestPrimePowerPart r.den = q → q ≤ lo →
        ∃ E : Finset ℕ, EliminationResult B r E by
    exact hmain (largestPrimePowerPart r.den) r rfl hrlo
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro r hqeq hqlo
      by_cases hden : r.den = 1
      · refine ⟨∅, ?_⟩
        refine
          { zero_not_mem := by simp
            le_bound := by simp
            card_le := by simp
            tag_le := by simp
            residual_isInt := ?_ }
        simpa using isInt_of_primePowerParts_empty
          ((den_eq_one_iff_primePowerParts_empty r).mp hden)
      · obtain ⟨U, hU⟩ := step r hden (hqeq.trans_le hqlo)
        let r' : ℚ := r - UnitFractions.rec_sum U
        have hdesc : largestPrimePowerPart r'.den < q := by
          simpa [r', hqeq] using hU.descends
        obtain ⟨E, hE⟩ := ih (largestPrimePowerPart r'.den) hdesc r' rfl
          (hdesc.le.trans hqlo)
        have hden2 : 2 ≤ r.den := by
          have := r.den_pos
          omega
        have hqpp : IsPrimePow q := by
          rw [← hqeq]
          exact (largestPrimePowerPart_spec hden2).1
        have hpi : piStar (largestPrimePowerPart r'.den) < piStar q :=
          piStar_lt_of_lt_of_isPrimePow hdesc hqpp
        have hdisjoint : Disjoint U E := by
          rw [Finset.disjoint_left]
          intro n hnU hnE
          have htagU : largestPrimePowerPart n = q := by
            simpa [hqeq] using hU.tagged n hnU
          have htagE := hE.tag_le n hnE
          omega
        refine ⟨U ∪ E, ?_⟩
        refine
          { zero_not_mem := ?_
            le_bound := ?_
            card_le := ?_
            tag_le := ?_
            residual_isInt := ?_ }
        · simpa only [Finset.mem_union, not_or] using
            ⟨hU.zero_not_mem, hE.zero_not_mem⟩
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · exact hU.le_bound n hnU
          · exact hE.le_bound n hnE
        · rw [Finset.card_union_of_disjoint hdisjoint]
          calc
            U.card + E.card ≤
                2 + 2 * piStar (largestPrimePowerPart r'.den) :=
              Nat.add_le_add hU.card_le_two hE.card_le
            _ ≤ 2 * piStar q := by omega
            _ = 2 * piStar (largestPrimePowerPart r.den) := by rw [hqeq]
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · rw [hU.tagged n hnU, hqeq]
          · exact (hE.tag_le n hnE).trans hdesc.le |>.trans_eq hqeq.symm
        · obtain ⟨z, hz⟩ := hE.residual_isInt
          refine ⟨z, ?_⟩
          rw [UnitFractions.rec_sum_disjoint hdisjoint]
          dsimp [r'] at hz
          linarith

/-! ## Scheduling Lemma 15 through all large prime powers -/

/-- The output of Lemma 15 when it is run at a scheduled prime power `q`.
Unlike `EliminationStep`, the scheduled `q` need not currently occur in the
reduced denominator. -/
structure ScheduledStep (r : ℚ) (q : ℕ) (U : Finset ℕ) : Prop where
  card_le_two : U.card ≤ 2
  card_eq_two_of_odd : Odd q → U.card = 2
  zero_not_mem : 0 ∉ U
  tagged : ∀ n ∈ U, largestPrimePowerPart n = q
  lower : ∀ n ∈ U, q ^ 2 ≤ 5 * n
  upper : ∀ n ∈ U, n ≤ q ^ 2
  descends :
    largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q

/-- The total reciprocal majorant charged to the prime-power stages in
`(lo,q]`.  Each Lemma 15 stage costs at most `10/t^2`. -/
def largeSquareCost (lo q : ℕ) : ℝ :=
  ∑ t ∈ RoughCounts.largePrimePowers q lo, 10 / (t : ℝ) ^ 2

lemma largePrimePowers_succ_of_isPrimePow {lo q : ℕ} (hloq : lo < q)
    (hq : IsPrimePow q) :
    RoughCounts.largePrimePowers q lo =
      insert q (RoughCounts.largePrimePowers (q - 1) lo) := by
  ext t
  simp only [RoughCounts.largePrimePowers, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_insert]
  constructor
  · rintro ⟨⟨hlt, htle⟩, htpp⟩
    by_cases htq : t = q
    · exact Or.inl htq
    · exact Or.inr ⟨⟨hlt, by omega⟩, htpp⟩
  · rintro (rfl | ⟨⟨hlt, htle⟩, htpp⟩)
    · exact ⟨⟨by omega, le_rfl⟩, hq⟩
    · exact ⟨⟨hlt, htle.trans (Nat.sub_le q 1)⟩, htpp⟩

lemma largePrimePowers_pred_of_not_isPrimePow {lo q : ℕ}
    (hq : ¬ IsPrimePow q) :
    RoughCounts.largePrimePowers q lo =
      RoughCounts.largePrimePowers (q - 1) lo := by
  ext t
  simp only [RoughCounts.largePrimePowers, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlt, htle⟩, htpp⟩
    exact ⟨⟨hlt, by
      by_cases htq : t = q
      · exact False.elim (hq (htq ▸ htpp))
      · omega⟩, htpp⟩
  · rintro ⟨⟨hlt, htle⟩, htpp⟩
    exact ⟨⟨hlt, htle.trans (Nat.sub_le q 1)⟩, htpp⟩

lemma largeSquareCost_succ_of_isPrimePow {lo q : ℕ} (hloq : lo < q)
    (hq : IsPrimePow q) :
    largeSquareCost lo q = largeSquareCost lo (q - 1) + 10 / (q : ℝ) ^ 2 := by
  rw [largeSquareCost, largeSquareCost,
    largePrimePowers_succ_of_isPrimePow hloq hq]
  have hnot : q ∉ RoughCounts.largePrimePowers (q - 1) lo := by
    rw [RoughCounts.largePrimePowers, Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [Finset.sum_insert hnot]
  ring

lemma largeSquareCost_pred_of_not_isPrimePow {lo q : ℕ}
    (hq : ¬ IsPrimePow q) :
    largeSquareCost lo q = largeSquareCost lo (q - 1) := by
  simp only [largeSquareCost,
    largePrimePowers_pred_of_not_isPrimePow hq]

lemma ScheduledStep.rec_sum_le_cost {r : ℚ} {q : ℕ} {U : Finset ℕ}
    (hq : IsPrimePow q) (h : ScheduledStep r q U) :
    (UnitFractions.rec_sum U : ℝ) ≤ 10 / (q : ℝ) ^ 2 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hterm : ∀ n ∈ U, (1 : ℝ) / n ≤ 5 / (q : ℝ) ^ 2 := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (Nat.pos_of_ne_zero (fun hn0 ↦ h.zero_not_mem (hn0 ▸ hn)))
    rw [div_le_div_iff₀ hnpos (sq_pos_of_pos hqpos)]
    norm_num
    exact_mod_cast h.lower n hn
  rw [UnitFractions.rec_sum]
  push_cast
  calc
    (∑ n ∈ U, (1 : ℝ) / n) ≤ U.card * (5 / (q : ℝ) ^ 2) := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul U (fun n ↦ (1 : ℝ) / n)
        (5 / (q : ℝ) ^ 2) hterm
    _ ≤ 2 * (5 / (q : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h.card_le_two)
        (div_nonneg (by positivity) (sq_nonneg _))
    _ = 10 / (q : ℝ) ^ 2 := by ring

/-- The concrete scheduled step supplied by Martin's Lemma 15. -/
theorem exists_scheduledStep_of_lemma15
    (q : ℕ) (hqpp : IsPrimePow q) (hq4 : 4 ≤ q)
    (r : ℚ) (hr : largestPrimePowerPart r.den ≤ q) :
    ∃ U : Finset ℕ, ScheduledStep r q U := by
  obtain ⟨U, hinterval, hodd, heven, htag, hdesc⟩ :=
    MartinCorrection.exists_elimination_set q hqpp hq4 r hr
  have hcard : U.card ≤ 2 := by
    rcases Nat.even_or_odd q with hqeven | hqodd
    · exact (heven hqeven).trans (by omega)
    · rw [hodd hqodd]
  have hzero : 0 ∉ U := by
    intro h0
    have hlower := (hinterval 0 h0).1
    have hqpos := hqpp.pos
    norm_num at hlower
    omega
  exact ⟨U,
    { card_le_two := hcard
      card_eq_two_of_odd := hodd
      zero_not_mem := hzero
      tagged := htag
      lower := fun n hn ↦ (hinterval n hn).1
      upper := fun n hn ↦ (hinterval n hn).2
      descends := hdesc }⟩

/-- The result of processing every prime power in `(lo,q]`, in decreasing
order. -/
structure ScheduledResult (lo q : ℕ) (r : ℚ)
    (E : Finset ℕ) (s : ℚ) : Prop where
  zero_not_mem : 0 ∉ E
  card_le : E.card ≤ 2 * (piStar q - piStar lo)
  tag_range : ∀ n ∈ E,
    lo < largestPrimePowerPart n ∧ largestPrimePowerPart n ≤ q
  denominator_range : ∀ n ∈ E,
    largestPrimePowerPart n ^ 2 ≤ 5 * n ∧
      n ≤ largestPrimePowerPart n ^ 2
  residual_eq : s = r - UnitFractions.rec_sum E
  residual_smooth : largestPrimePowerPart s.den ≤ lo
  rec_sum_le_cost : (UnitFractions.rec_sum E : ℝ) ≤ largeSquareCost lo q
  odd_stage : ∀ t, lo < t → t ≤ q → IsPrimePow t → Odd t →
    ∃ U ⊆ E, U.card = 2 ∧
      ∀ n ∈ U, largestPrimePowerPart n = t

/--
Run Lemma 15 at every large prime power, including prime powers which do not
occur in the current reduced denominator.  This is the source-faithful
schedule responsible for the eventual near-exact term count.
-/
theorem exists_scheduledResult
    (lo : ℕ) (hlo : 1 ≤ lo)
    (step : ∀ q : ℕ, ∀ r : ℚ, lo < q → IsPrimePow q →
      largestPrimePowerPart r.den ≤ q →
        ∃ U : Finset ℕ, ScheduledStep r q U)
    (q : ℕ) (r : ℚ) (hrq : largestPrimePowerPart r.den ≤ q) :
    ∃ E : Finset ℕ, ∃ s : ℚ, ScheduledResult lo q r E s := by
  induction q using Nat.strong_induction_on generalizing r with
  | h q ih =>
      by_cases hqlo : q ≤ lo
      · refine ⟨∅, r, ?_⟩
        refine
          { zero_not_mem := by simp
            card_le := by
              simp only [Finset.card_empty, zero_le]
            tag_range := by simp
            denominator_range := by simp
            residual_eq := by simp
            residual_smooth := hrq.trans hqlo
            rec_sum_le_cost := by
              simp only [UnitFractions.rec_sum, Finset.sum_empty, Rat.cast_zero]
              exact Finset.sum_nonneg fun _ _ ↦
                div_nonneg (by positivity) (sq_nonneg _)
            odd_stage := ?_ }
        intro t hlot htq
        omega
      · have hloq : lo < q := Nat.lt_of_not_ge hqlo
        by_cases hqpp : IsPrimePow q
        · obtain ⟨U, hU⟩ := step q r hloq hqpp hrq
          let r' : ℚ := r - UnitFractions.rec_sum U
          have hdesc : largestPrimePowerPart r'.den < q := by
            simpa [r'] using hU.descends
          obtain ⟨E, s, hE⟩ := ih (q - 1) (by omega) r' (by omega)
          have hdisjoint : Disjoint U E := by
            rw [Finset.disjoint_left]
            intro n hnU hnE
            have htagU := hU.tagged n hnU
            have htagE := (hE.tag_range n hnE).2
            omega
          refine ⟨U ∪ E, s, ?_⟩
          refine
            { zero_not_mem := ?_
              card_le := ?_
              tag_range := ?_
              denominator_range := ?_
              residual_eq := ?_
              residual_smooth := hE.residual_smooth
              rec_sum_le_cost := ?_
              odd_stage := ?_ }
          · simpa only [Finset.mem_union, not_or] using
              ⟨hU.zero_not_mem, hE.zero_not_mem⟩
          · rw [Finset.card_union_of_disjoint hdisjoint]
            calc
              U.card + E.card ≤ 2 + 2 * (piStar (q - 1) - piStar lo) :=
                Nat.add_le_add hU.card_le_two hE.card_le
              _ = 2 * (piStar q - piStar lo) := by
                have hloPred : lo ≤ q - 1 := by omega
                have hpiLo : piStar lo ≤ piStar (q - 1) := piStar_mono hloPred
                rw [piStar_eq_succ_pred_of_isPrimePow hqpp]
                omega
          · intro n hn
            rcases Finset.mem_union.mp hn with hnU | hnE
            · rw [hU.tagged n hnU]
              exact ⟨hloq, le_rfl⟩
            · have hnrange := hE.tag_range n hnE
              exact ⟨hnrange.1, hnrange.2.trans (Nat.sub_le q 1)⟩
          · intro n hn
            rcases Finset.mem_union.mp hn with hnU | hnE
            · rw [hU.tagged n hnU]
              exact ⟨hU.lower n hnU, hU.upper n hnU⟩
            · exact hE.denominator_range n hnE
          · rw [hE.residual_eq, UnitFractions.rec_sum_disjoint hdisjoint]
            dsimp [r']
            ring
          · rw [UnitFractions.rec_sum_disjoint hdisjoint, Rat.cast_add,
              largeSquareCost_succ_of_isPrimePow hloq hqpp]
            nlinarith [hU.rec_sum_le_cost hqpp, hE.rec_sum_le_cost]
          · intro t hlot htq htpp htodd
            rcases lt_or_eq_of_le htq with htlt | rfl
            · obtain ⟨V, hVE, hVcard, hVtag⟩ :=
                hE.odd_stage t hlot (by omega) htpp htodd
              exact ⟨V, hVE.trans subset_union_right, hVcard, hVtag⟩
            · exact ⟨U, subset_union_left, hU.card_eq_two_of_odd htodd, hU.tagged⟩
        · have hnext : largestPrimePowerPart r.den ≤ q - 1 := by
            by_contra hnot
            have heq : largestPrimePowerPart r.den = q := by omega
            have hden2 : 2 ≤ r.den := by
              have hpartle := largestPrimePowerPart_le (n := r.den)
              omega
            exact hqpp (heq ▸ (largestPrimePowerPart_spec hden2).1)
          obtain ⟨E, s, hE⟩ := ih (q - 1) (by omega) r hnext
          refine ⟨E, s, ?_⟩
          refine
            { zero_not_mem := hE.zero_not_mem
              card_le := ?_
              tag_range := ?_
              denominator_range := hE.denominator_range
              residual_eq := hE.residual_eq
              residual_smooth := hE.residual_smooth
              rec_sum_le_cost := by
                simpa [largeSquareCost_pred_of_not_isPrimePow hqpp] using
                  hE.rec_sum_le_cost
              odd_stage := ?_ }
          · simpa [piStar_eq_pred_of_not_isPrimePow hqpp] using hE.card_le
          · intro n hn
            have hnrange := hE.tag_range n hn
            exact ⟨hnrange.1, hnrange.2.trans (Nat.sub_le q 1)⟩
          · intro t hlot htq htpp htodd
            have htlt : t < q := lt_of_le_of_ne htq (fun heq ↦ hqpp (heq ▸ htpp))
            exact hE.odd_stage t hlot (by omega) htpp htodd

/-! ## Mixed Lemma 15 / Lemma 16 recursion -/

/-- The complete preliminary correction before the final cardinality padding
step. -/
structure PreliminaryResult (B lo y : ℕ) (r : ℚ) (E : Finset ℕ) : Prop where
  zero_not_mem : 0 ∉ E
  le_bound : ∀ n ∈ E, n ≤ B
  card_le : E.card ≤ 2 * piStar y
  tag_le : ∀ n ∈ E, largestPrimePowerPart n ≤ y
  residual_isInt : ∃ z : ℤ, r - UnitFractions.rec_sum E = z
  odd_large_stage : ∀ t, lo < t → t ≤ y → IsPrimePow t → Odd t →
    ∃ U ⊆ E, U.card = 2 ∧
      (∀ n ∈ U, largestPrimePowerPart n = t) ∧
      ∀ n ∈ U, t ^ 2 ≤ 5 * n

lemma PreliminaryResult.residual_eq_zero {B lo y : ℕ} {r : ℚ}
    {E : Finset ℕ} (h : PreliminaryResult B lo y r E)
    (hsmall : |r - UnitFractions.rec_sum E| < 1) :
    r - UnitFractions.rec_sum E = 0 :=
  eq_zero_of_isInt_of_abs_lt_one h.residual_isInt hsmall

/--
Assemble the large scheduled Lemma 15 recursion and the remaining current-
factor Lemma 16 recursion.  Both inputs are ordinary theorem arguments; the
concrete Proposition 7 theorem supplies them from the two proved lemmas.
-/
theorem exists_preliminaryResult
    (B lo y : ℕ) (hlo : 1 ≤ lo) (hloy : lo ≤ y) (hyB : y ^ 2 ≤ B)
    (largeStep : ∀ q : ℕ, ∀ r : ℚ, lo < q → IsPrimePow q →
      largestPrimePowerPart r.den ≤ q →
        ∃ U : Finset ℕ, ScheduledStep r q U)
    (smallStep : ∀ r : ℚ, r.den ≠ 1 →
      largestPrimePowerPart r.den ≤ lo →
        ∃ U : Finset ℕ, EliminationStep B r U)
    (r : ℚ) (hry : largestPrimePowerPart r.den ≤ y) :
    ∃ E : Finset ℕ, PreliminaryResult B lo y r E := by
  obtain ⟨A, s, hA⟩ := exists_scheduledResult lo hlo largeStep y r hry
  obtain ⟨C, hC⟩ :=
    exists_eliminationResult_below B lo smallStep s hA.residual_smooth
  have hdisjoint : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro n hnA hnC
    have hnAlo := (hA.tag_range n hnA).1
    have hnCle := (hC.tag_le n hnC).trans hA.residual_smooth
    omega
  refine ⟨A ∪ C, ?_⟩
  refine
    { zero_not_mem := ?_
      le_bound := ?_
      card_le := ?_
      tag_le := ?_
      residual_isInt := ?_
      odd_large_stage := ?_ }
  · simpa only [Finset.mem_union, not_or] using
      ⟨hA.zero_not_mem, hC.zero_not_mem⟩
  · intro n hn
    rcases Finset.mem_union.mp hn with hnA | hnC
    · exact (hA.denominator_range n hnA).2.trans
        (Nat.pow_le_pow_left (hA.tag_range n hnA).2 2) |>.trans hyB
    · exact hC.le_bound n hnC
  · rw [Finset.card_union_of_disjoint hdisjoint]
    calc
      A.card + C.card ≤
          2 * (piStar y - piStar lo) +
            2 * piStar (largestPrimePowerPart s.den) :=
        Nat.add_le_add hA.card_le hC.card_le
      _ ≤ 2 * (piStar y - piStar lo) + 2 * piStar lo := by
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_left 2 (piStar_mono hA.residual_smooth)) _
      _ = 2 * piStar y := by
        have hpile : piStar lo ≤ piStar y := piStar_mono hloy
        omega
  · intro n hn
    rcases Finset.mem_union.mp hn with hnA | hnC
    · exact (hA.tag_range n hnA).2
    · exact (hC.tag_le n hnC).trans hA.residual_smooth |>.trans hloy
  · obtain ⟨z, hz⟩ := hC.residual_isInt
    refine ⟨z, ?_⟩
    rw [UnitFractions.rec_sum_disjoint hdisjoint]
    linarith [hA.residual_eq]
  · intro t hlot hty htpp htodd
    obtain ⟨U, hUA, hUcard, hUtag⟩ := hA.odd_stage t hlot hty htpp htodd
    refine ⟨U, hUA.trans subset_union_left, hUcard, hUtag, ?_⟩
    intro n hn
    have hden := hA.denominator_range n (hUA hn)
    simpa [hUtag n hn] using hden.1

/-- The preliminary correction instantiated with the proved versions of
Martin's Lemmas 15 and 16.  The remaining hypotheses are only the explicit
cutoff and size inequalities used in Proposition 7. -/
theorem exists_preliminaryResult_of_lemmas
    (lo y : ℕ) (hlo : 3 ≤ lo) (hloy : lo ≤ y)
    (hL : initialLcm lo ≤ y ^ 2)
    (r : ℚ) (hry : largestPrimePowerPart r.den ≤ y) :
    ∃ E : Finset ℕ, PreliminaryResult (y ^ 2) lo y r E := by
  apply exists_preliminaryResult (y ^ 2) lo y (by omega) hloy le_rfl
  · intro q s hloq hqpp hs
    exact exists_scheduledStep_of_lemma15 q hqpp (by omega) s hs
  · exact exists_eliminationStep_of_lemma16 (y ^ 2) lo hL
  · exact hry

/-- A preliminary correction carrying the quantitative estimate needed to
show that its terminal integer is zero. -/
structure BudgetedPreliminaryResult (lo y : ℕ) (r : ℚ)
    (E : Finset ℕ) : Prop extends PreliminaryResult (y ^ 2) lo y r E where
  rec_sum_lt : (UnitFractions.rec_sum E : ℝ) < 1 + largeSquareCost lo y

/-- Lemmas 15 and 16, combined with the exact small-prime-power telescope. -/
theorem exists_budgetedPreliminaryResult_of_lemmas
    (lo y : ℕ) (hlo : 3 ≤ lo) (hloy : lo ≤ y)
    (hL : initialLcm lo ≤ y ^ 2)
    (r : ℚ) (hry : largestPrimePowerPart r.den ≤ y) :
    ∃ E : Finset ℕ, BudgetedPreliminaryResult lo y r E := by
  obtain ⟨A, s, hA⟩ := exists_scheduledResult lo (by omega)
    (fun q t hloq hqpp ht ↦
      exists_scheduledStep_of_lemma15 q hqpp (by omega) t ht)
    y r hry
  obtain ⟨C, hC⟩ :=
    exists_smallEliminationResult_of_lemma16 (y ^ 2) lo hL s
      hA.residual_smooth
  have hdisjoint : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro n hnA hnC
    have hnAlo := (hA.tag_range n hnA).1
    have hnCle := (hC.tag_le n hnC).trans hA.residual_smooth
    omega
  refine ⟨A ∪ C, ?_⟩
  refine
    { toPreliminaryResult :=
        { zero_not_mem := by
            simpa only [Finset.mem_union, not_or] using
              ⟨hA.zero_not_mem, hC.zero_not_mem⟩
          le_bound := ?_
          card_le := ?_
          tag_le := ?_
          residual_isInt := ?_
          odd_large_stage := ?_ }
      rec_sum_lt := ?_ }
  · intro n hn
    rcases Finset.mem_union.mp hn with hnA | hnC
    · exact (hA.denominator_range n hnA).2.trans
        (Nat.pow_le_pow_left (hA.tag_range n hnA).2 2)
    · exact hC.le_bound n hnC
  · rw [Finset.card_union_of_disjoint hdisjoint]
    calc
      A.card + C.card ≤
          2 * (piStar y - piStar lo) +
            piStar (largestPrimePowerPart s.den) :=
        Nat.add_le_add hA.card_le hC.card_le
      _ ≤ 2 * (piStar y - piStar lo) + piStar lo := by
        exact Nat.add_le_add_left (piStar_mono hA.residual_smooth) _
      _ ≤ 2 * (piStar y - piStar lo) + 2 * piStar lo := by omega
      _ = 2 * piStar y := by
        have hpile : piStar lo ≤ piStar y := piStar_mono hloy
        omega
  · intro n hn
    rcases Finset.mem_union.mp hn with hnA | hnC
    · exact (hA.tag_range n hnA).2
    · exact (hC.tag_le n hnC).trans hA.residual_smooth |>.trans hloy
  · obtain ⟨z, hz⟩ := hC.residual_isInt
    refine ⟨z, ?_⟩
    rw [UnitFractions.rec_sum_disjoint hdisjoint]
    linarith [hA.residual_eq]
  · intro t hlot hty htpp htodd
    obtain ⟨U, hUA, hUcard, hUtag⟩ :=
      hA.odd_stage t hlot hty htpp htodd
    refine ⟨U, hUA.trans subset_union_left, hUcard, hUtag, ?_⟩
    intro n hn
    have hden := hA.denominator_range n (hUA hn)
    simpa [hUtag n hn] using hden.1
  · have hCltQ : UnitFractions.rec_sum C < 1 :=
      hC.rec_sum_le_cost.trans_lt
        (LcmTelescope.smallPrimePowerCost_lt_one _)
    have hClt : (UnitFractions.rec_sum C : ℝ) < 1 := by
      exact_mod_cast hCltQ
    rw [UnitFractions.rec_sum_disjoint hdisjoint, Rat.cast_add]
    linarith [hA.rec_sum_le_cost]

/-! ## Telescoping padding -/

/-- The denominators in the telescoping replacement of `1/n`. -/
def paddingTerms (n m : ℕ) : Finset ℕ :=
  {n + m} ∪ (Finset.range m).image (fun j ↦ (n + j) * (n + j + 1))

lemma paddingProduct_strictMono (n : ℕ) (hn : 0 < n) :
    StrictMono (fun j : ℕ ↦ (n + j) * (n + j + 1)) := by
  intro a b hab
  nlinarith [Nat.add_pos_left hn a, Nat.add_pos_left hn b]

lemma paddingTerms_product_gt {n m j : ℕ} (hn : 0 < n) (_hj : j < m) :
    n < (n + j) * (n + j + 1) := by
  nlinarith [Nat.add_pos_left hn j]

lemma paddingTerms_product_le {n m j : ℕ} (hj : j < m) :
    (n + j) * (n + j + 1) ≤ (n + m) ^ 2 := by
  have h1 : n + j + 1 ≤ n + m := by omega
  have h2 : n + j ≤ n + m := by omega
  nlinarith

/-- The telescoping replacement has exactly `m + 1` distinct denominators.
The condition `m < n` prevents the linear denominator `n+m` from colliding
with a quadratic denominator. -/
lemma card_paddingTerms (n m : ℕ) (hn : 0 < n) (hm : m < n) :
    (paddingTerms n m).card = m + 1 := by
  have hinj : Set.InjOn (fun j : ℕ ↦ (n + j) * (n + j + 1)) (Finset.range m) :=
    (paddingProduct_strictMono n hn).injective.injOn
  have hcardImage : ((Finset.range m).image
      (fun j ↦ (n + j) * (n + j + 1))).card = m := by
    rw [Finset.card_image_iff.mpr hinj]
    simp
  have hnotmem : n + m ∉ (Finset.range m).image
      (fun j ↦ (n + j) * (n + j + 1)) := by
    intro hmem
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hmem
    have hjm : j < m := Finset.mem_range.mp hj
    have hquad : 2 * n ≤ (n + j) * (n + j + 1) := by
      nlinarith [Nat.add_pos_left hn j]
    have hlin : n + m < 2 * n := by omega
    omega
  rw [paddingTerms, Finset.card_union_of_disjoint]
  · simp [hcardImage, Nat.add_comm]
  · simpa [Finset.disjoint_left] using hnotmem

lemma zero_not_mem_paddingTerms {n m : ℕ} (hn : 0 < n) :
    0 ∉ paddingTerms n m := by
  rw [paddingTerms, Finset.mem_union, not_or]
  refine ⟨?_, ?_⟩
  · intro h
    simp only [Finset.mem_singleton] at h
    omega
  simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
  intro j hj
  exact Nat.ne_of_gt (Nat.mul_pos (Nat.add_pos_left hn j) (by omega))

lemma mem_paddingTerms_le_square {n m a : ℕ} (ha : a ∈ paddingTerms n m) :
    a ≤ (n + m) ^ 2 := by
  rcases Finset.mem_union.mp ha with ha | ha
  · simp only [Finset.mem_singleton] at ha
    subst a
    nlinarith
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact paddingTerms_product_le (Finset.mem_range.mp hj)

lemma paddingTerms_above {n m a : ℕ} (hn : 0 < n) (hm : 0 < m)
    (ha : a ∈ paddingTerms n m) : n < a := by
  rcases Finset.mem_union.mp ha with ha | ha
  · have heq : a = n + m := Finset.mem_singleton.mp ha
    omega
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact paddingTerms_product_gt hn (Finset.mem_range.mp hj)

/-- The reciprocal sum of all padding terms is exactly the original unit
fraction. -/
lemma rec_sum_paddingTerms (n m : ℕ) (hn : 0 < n) (hm : m < n) :
    UnitFractions.rec_sum (paddingTerms n m) = (1 : ℚ) / n := by
  have hdisj : Disjoint ({n + m} : Finset ℕ)
      ((Finset.range m).image (fun j ↦ (n + j) * (n + j + 1))) := by
    rw [Finset.disjoint_left]
    intro a ha haImage
    simp only [Finset.mem_singleton] at ha
    subst a
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp haImage
    have hjm : j < m := Finset.mem_range.mp hj
    have hquad : 2 * n ≤ (n + j) * (n + j + 1) := by
      nlinarith [Nat.add_pos_left hn j]
    have hlin : n + m < 2 * n := by omega
    omega
  rw [paddingTerms, UnitFractions.rec_sum_disjoint hdisj]
  simp only [UnitFractions.rec_sum, Finset.sum_singleton]
  have himage :
      ∑ a ∈ (Finset.range m).image (fun j ↦ (n + j) * (n + j + 1)),
          (1 : ℚ) / a =
        ∑ j ∈ Finset.range m, (1 : ℚ) / ((n + j) * (n + j + 1) : ℕ) := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact (paddingProduct_strictMono n hn).injective hab
  rw [himage]
  exact (ExactCorrection.unitFraction_telescoping n m hn).symm

/-- Replace the largest member of `A` by the telescoping padding set. -/
def padAt (A : Finset ℕ) (n m : ℕ) : Finset ℕ :=
  A.erase n ∪ paddingTerms n m

/--
Source-faithful exact-cardinality padding interface.

If `n` is the largest denominator of a nonempty positive finite set and the
required deficit `m` is smaller than `n`, then `padAt A n m` has exactly
`A.card + m` members, has the same reciprocal sum, remains positive, and all
its denominators are at most `(n+m)^2`.
-/
theorem padAt_spec {A : Finset ℕ} {n m : ℕ}
    (hnA : n ∈ A) (hnmax : ∀ a ∈ A, a ≤ n)
    (hzero : 0 ∉ A) (hm : m < n) :
    (padAt A n m).card = A.card + m ∧
      UnitFractions.rec_sum (padAt A n m) = UnitFractions.rec_sum A ∧
      0 ∉ padAt A n m ∧
      ∀ a ∈ padAt A n m, a ≤ (n + m) ^ 2 := by
  have hn : 0 < n := by
    have : n ≠ 0 := by
      intro hn0
      exact hzero (hn0 ▸ hnA)
    omega
  have hdisj : Disjoint (A.erase n) (paddingTerms n m) := by
    rw [Finset.disjoint_left]
    intro a haA haP
    have han : a ≤ n := hnmax a (Finset.mem_of_mem_erase haA)
    rcases eq_or_lt_of_le (Nat.zero_le m) with hm0 | hmpos
    · subst m
      simp [paddingTerms] at haP
      subst a
      simp at haA
    · exact (not_lt_of_ge han) (paddingTerms_above hn hmpos haP)
  have hcardErase : (A.erase n).card = A.card - 1 := by
    rw [Finset.card_erase_of_mem hnA]
  have hsumErase : UnitFractions.rec_sum (A.erase n) + (1 : ℚ) / n =
      UnitFractions.rec_sum A := by
    simpa [UnitFractions.rec_sum] using
      (Finset.sum_erase_add (s := A) (f := fun a : ℕ ↦ (1 : ℚ) / a) hnA)
  have hcardPos : 0 < A.card := Finset.card_pos.mpr ⟨n, hnA⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [padAt, Finset.card_union_of_disjoint hdisj, hcardErase,
      card_paddingTerms n m hn hm]
    omega
  · rw [padAt, UnitFractions.rec_sum_disjoint hdisj,
      rec_sum_paddingTerms n m hn hm]
    exact hsumErase
  · rw [padAt, Finset.mem_union, not_or]
    exact ⟨fun h ↦ hzero (Finset.mem_of_mem_erase h), zero_not_mem_paddingTerms hn⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with haA | haP
    · have han : a ≤ n := hnmax a (Finset.mem_of_mem_erase haA)
      calc
        a ≤ n := han
        _ ≤ (n + m) ^ 2 := by nlinarith
    · exact mem_paddingTerms_le_square haP

/-- Padding directly to a prescribed target cardinality. -/
theorem exists_padded_to_card {A : Finset ℕ} {n K : ℕ}
    (hnA : n ∈ A) (hnmax : ∀ a ∈ A, a ≤ n)
    (hzero : 0 ∉ A) (hcard : A.card ≤ K)
    (hdeficit : K - A.card < n) :
    ∃ E : Finset ℕ,
      E.card = K ∧
      UnitFractions.rec_sum E = UnitFractions.rec_sum A ∧
      0 ∉ E ∧
      ∀ a ∈ E, a ≤ (n + (K - A.card)) ^ 2 := by
  let m := K - A.card
  refine ⟨padAt A n m, ?_⟩
  obtain ⟨hcardPad, hsumPad, hzeroPad, hboundPad⟩ :=
    padAt_spec hnA hnmax hzero hdeficit
  refine ⟨?_, hsumPad, hzeroPad, hboundPad⟩
  dsimp [m] at hcardPad ⊢
  omega

/-! ## Final padding bound -/

/--
Turn a preliminary exact correction into the exact cardinality
`2 * piStar y`.  Bertrand's postulate supplies an odd prime in `(y/2,y]`;
the scheduled Lemma 15 stage at that prime provides a denominator large enough
to absorb the entire cardinality deficit.  The square estimate from
`padAt_spec` is then at most `2*y^4`.
-/
theorem exists_exactCard_of_preliminary
    {lo y : ℕ} {r : ℚ} {A : Finset ℕ}
    (hy : 40 ≤ y) (hlo : lo < y / 2)
    (hA : PreliminaryResult (y ^ 2) lo y r A)
    (hsmall : |r - UnitFractions.rec_sum A| < 1) :
    ∃ E : Finset ℕ,
      E.card = 2 * piStar y ∧
      UnitFractions.rec_sum E = r ∧
      0 ∉ E ∧
      ∀ n ∈ E, n ≤ 2 * y ^ 4 := by
  have hyhalf : y / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hyhp, hpyle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (y / 2) hyhalf
  have hpy : p ≤ y := hpyle.trans (by omega)
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpp : IsPrimePow p := ⟨p, 1, hp.prime, by omega, by simp⟩
  obtain ⟨U, hUA, hUcard, hUtag, hUlower⟩ :=
    hA.odd_large_stage p (hlo.trans hyhp) hpy hpp hpodd
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨n, hnU⟩ := hUne
  have hnA : n ∈ A := hUA hnU
  have hAne : A.Nonempty := ⟨n, hnA⟩
  let N : ℕ := A.max' hAne
  have hnN : n ≤ N := by
    exact Finset.le_max' A n hnA
  have hNmem : N ∈ A := Finset.max'_mem A hAne
  have hNmax : ∀ a ∈ A, a ≤ N := by
    intro a ha
    exact Finset.le_max' A a ha
  have hNupper : N ≤ y ^ 2 := hA.le_bound N hNmem
  let K : ℕ := 2 * piStar y
  let d : ℕ := K - A.card
  have hcardAK : A.card ≤ K := by
    simpa [K] using hA.card_le
  have hKle : K ≤ 2 * y := by
    dsimp [K]
    exact Nat.mul_le_mul_left 2 (piStar_le y)
  have hdle : d ≤ 2 * y := by
    exact (Nat.sub_le K A.card).trans hKle
  have hyhalfBound : y ≤ 2 * (y / 2) + 1 := by omega
  have hpSq : 10 * y < p ^ 2 := by
    nlinarith
  have hpn : p ^ 2 ≤ 5 * n := hUlower n hnU
  have hnlarge : 2 * y < n := by nlinarith
  have hdN : d < N := hdle.trans_lt (hnlarge.trans_le hnN)
  obtain ⟨E, hEcard, hEsum, hEzero, hEbound⟩ :=
    exists_padded_to_card hNmem hNmax hA.zero_not_mem hcardAK hdN
  have hAsum : UnitFractions.rec_sum A = r := by
    have hz := hA.residual_eq_zero hsmall
    linarith
  have hsumBound : N + d ≤ y ^ 2 + 2 * y := Nat.add_le_add hNupper hdle
  have hfour : 4 * (N + d) ≤ 5 * y ^ 2 := by
    nlinarith [show 8 * y ≤ y ^ 2 by nlinarith]
  have hsquare : (N + d) ^ 2 ≤ 2 * y ^ 4 := by
    nlinarith [sq_nonneg (4 * (N + d)), sq_nonneg (5 * y ^ 2)]
  refine ⟨E, ?_, ?_, hEzero, ?_⟩
  · simpa [K] using hEcard
  · exact hEsum.trans hAsum
  · intro a ha
    exact (hEbound a ha).trans (by simpa [N, d] using hsquare)

/-- Converting a Chebyshev bound at a cutoff into the concrete `y^2` LCM
bound required by the small-prime-power construction. -/
lemma initialLcm_le_sq_of_chebyshev {lo y : ℕ} (hy : 1 ≤ y)
    (hlo : (lo : ℝ) ≤ Real.log (y : ℝ))
    (hpsi : chebyshev_second (lo : ℝ) ≤ 2 * (lo : ℝ)) :
    initialLcm lo ≤ y ^ 2 := by
  have hLpos : (0 : ℝ) < initialLcm lo := by
    exact_mod_cast
      (Nat.pos_of_ne_zero (by simp [initialLcm] : initialLcm lo ≠ 0))
  have hypos : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hy)
  have hlogL : Real.log (initialLcm lo : ℝ) =
      chebyshev_second (lo : ℝ) := by
    change Real.log (Nat.lcmUpto lo : ℝ) = Chebyshev.psi (lo : ℝ)
    exact (Chebyshev.psi_eq_log_lcmUpto lo).symm
  have hlogle : Real.log (initialLcm lo : ℝ) ≤
      2 * Real.log (y : ℝ) := by
    rw [hlogL]
    linarith
  have hexp := Real.exp_le_exp.mpr hlogle
  rw [Real.exp_log hLpos] at hexp
  have hrhs : Real.exp (2 * Real.log (y : ℝ)) = (y : ℝ) ^ 2 := by
    rw [show 2 * Real.log (y : ℝ) =
      Real.log (y : ℝ) + Real.log (y : ℝ) by ring,
      Real.exp_add, Real.exp_log hypos]
    ring
  rw [hrhs] at hexp
  exact_mod_cast hexp

/-- A convenient elementary cutoff separation used by the eventual wrapper. -/
lemma log_lt_quarter_natCast (y : ℕ) (hy : 40 ≤ y) :
    Real.log (y : ℝ) < (y : ℝ) / 4 := by
  have hyR : (0 : ℝ) < y := by positivity
  have hdiv : 0 < (y : ℝ) / 8 := div_pos hyR (by norm_num)
  have hbase := Real.log_le_sub_one_of_pos hdiv
  have hlog2 : Real.log (2 : ℝ) < 1 := by
    nlinarith [Real.log_two_lt_d9]
  have hlog8 : Real.log (8 : ℝ) < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    nlinarith
  have hdecomp : Real.log (y : ℝ) =
      Real.log 8 + Real.log ((y : ℝ) / 8) := by
    rw [Real.log_div hyR.ne' (by norm_num : (8 : ℝ) ≠ 0)]
    linarith
  rw [hdecomp]
  have hyR40 : (40 : ℝ) ≤ y := by exact_mod_cast hy
  nlinarith

lemma naturalLogCutoff_lt_half (y : ℕ) (hy : 40 ≤ y) :
    RoughCounts.naturalLogCutoff y < y / 2 := by
  have hy1 : 1 ≤ y := by omega
  have hlognonneg : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hy1)
  have hfloor : ((RoughCounts.naturalLogCutoff y : ℕ) : ℝ) ≤
      Real.log (y : ℝ) := Nat.floor_le hlognonneg
  have hlog := log_lt_quarter_natCast y hy
  have hnat : y < 4 * (y / 2) := by omega
  have hreal : (y : ℝ) < 4 * ((y / 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hquarter : (y : ℝ) / 4 < ((y / 2 : ℕ) : ℝ) := by
    nlinarith
  exact_mod_cast hfloor.trans_lt (hlog.trans hquarter)

/-- Finite, quantitative form of Martin's Proposition 7.  The positive
constant `c` is arbitrary; the source's `1/log y` is the case `c = 1`, while
the upper-bound assembly uses `c = 1/6` to absorb the fifth-root floor. -/
theorem proposition7_of_cutoff
    {c : ℝ} (_hc : 0 < c) {lo y : ℕ} {r : ℚ}
    (hy : 40 ≤ y) (hlo : 3 ≤ lo) (hloy : lo ≤ y)
    (hlohalf : lo < y / 2) (hL : initialLcm lo ≤ y ^ 2)
    (hry : largestPrimePowerPart r.den ≤ y)
    (hrLower : c / Real.log (y : ℝ) < (r : ℝ))
    (hrUpper : (r : ℝ) < 1)
    (htail : largeSquareCost lo y < c / Real.log (y : ℝ)) :
    ∃ E : Finset ℕ,
      E.card = 2 * piStar y ∧
      UnitFractions.rec_sum E = r ∧
      0 ∉ E ∧
      ∀ n ∈ E, n ≤ 2 * y ^ 4 := by
  obtain ⟨A, hA⟩ :=
    exists_budgetedPreliminaryResult_of_lemmas lo y hlo hloy hL r hry
  have hsumlt : (UnitFractions.rec_sum A : ℝ) < 1 + (r : ℝ) := by
    linarith [hA.rec_sum_lt]
  have hsum_nonnegQ : 0 ≤ UnitFractions.rec_sum A :=
    UnitFractions.rec_sum_nonneg
  have hsum_nonneg : (0 : ℝ) ≤ UnitFractions.rec_sum A := by
    exact_mod_cast hsum_nonnegQ
  have hresLower : (-1 : ℝ) < (r : ℝ) - UnitFractions.rec_sum A := by
    linarith
  have hresUpper : (r : ℝ) - UnitFractions.rec_sum A < 1 := by
    linarith
  have hsmallR : |(r : ℝ) - UnitFractions.rec_sum A| < 1 :=
    (abs_lt).2 ⟨hresLower, hresUpper⟩
  have hsmall : |r - UnitFractions.rec_sum A| < (1 : ℚ) := by
    exact_mod_cast hsmallR
  exact exists_exactCard_of_preliminary hy hlohalf hA.toPreliminaryResult hsmall

/-- At the natural logarithmic cutoff, the small denominators supplied by
Lemma 16 are eventually at most `y^2`. -/
lemma eventually_initialLcm_naturalLogCutoff_le_sq :
    ∀ᶠ y : ℕ in Filter.atTop,
      initialLcm (RoughCounts.naturalLogCutoff y) ≤ y ^ 2 := by
  have hc2 : 2 * Real.log 2 < (2 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  have hpsiReal := (chebyshev_upper_explicit hc2).bound
  have hcutReal : Filter.Tendsto
      (fun y : ℕ ↦ (RoughCounts.naturalLogCutoff y : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp
      RoughCounts.naturalLogCutoff_tendsto_atTop
  have hpsi := hcutReal.eventually hpsiReal
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), hpsi]
      with y hy hpsiY
  have hlognonneg : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hy)
  have hcutle : (RoughCounts.naturalLogCutoff y : ℝ) ≤
      Real.log (y : ℝ) := Nat.floor_le hlognonneg
  apply initialLcm_le_sq_of_chebyshev hy hcutle
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (chebyshev_second_nonneg _)] using hpsiY

/-- Unconditional eventual form of Martin's Proposition 7.  All congruence,
descent, reciprocal-mass, and LCM estimates have been discharged; the only
remaining assumptions are the mathematical hypotheses on the input rational.
-/
theorem eventually_proposition7 {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in Filter.atTop, ∀ r : ℚ,
      largestPrimePowerPart r.den ≤ y →
      c / Real.log (y : ℝ) < (r : ℝ) →
      (r : ℝ) < 1 →
      ∃ E : Finset ℕ,
        E.card = 2 * piStar y ∧
        UnitFractions.rec_sum E = r ∧
        0 ∉ E ∧
        ∀ n ∈ E, n ≤ 2 * y ^ 4 := by
  have htail :=
    RoughCounts.eventually_sum_ten_div_primePower_sq_lt_div_log hc
  have hcut3 := RoughCounts.naturalLogCutoff_tendsto_atTop.eventually
    (Filter.eventually_ge_atTop (3 : ℕ))
  filter_upwards [Filter.eventually_ge_atTop (40 : ℕ), htail, hcut3,
    eventually_initialLcm_naturalLogCutoff_le_sq]
      with y hy htailY hcut3Y hLY
  intro r hry hrLower hrUpper
  apply proposition7_of_cutoff hc hy hcut3Y
  · exact (naturalLogCutoff_lt_half y hy).le.trans (Nat.div_le_self y 2)
  · exact naturalLogCutoff_lt_half y hy
  · exact hLY
  · exact hry
  · exact hrLower
  · exact hrUpper
  · simpa [largeSquareCost] using htailY

#print axioms eventually_proposition7

end

end Erdos285.Proposition7
