import Mathlib

/-!
# Arithmetic bookkeeping for cyclic subset-sum growth

This file contains the purely finite part of the growth argument in
Conlon--Fox--Pham, Lemma 3.1.  The states are represented by a monotone
sequence `a : ℕ → ℕ`; only the values through `q` are used.  A stage is
called bad when it satisfies one of the two slow-growth alternatives in the
paper.  The theorem at the end shows that a sequence which remains below
`x / 4` has fewer than `4*u` nonbad stages.
-/

namespace Erdos54

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## A filtered multiplicative-growth invariant -/

/-- The stages below `n` at which `P` holds. -/
def growthStages (P : ℕ → Prop) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter P

@[simp] theorem growthStages_zero (P : ℕ → Prop) :
    growthStages P 0 = ∅ := by
  simp [growthStages]

theorem growthStages_succ (P : ℕ → Prop) (n : ℕ) :
    growthStages P (n + 1) =
      if P n then insert n (growthStages P n) else growthStages P n := by
  classical
  unfold growthStages
  rw [Finset.range_add_one, Finset.filter_insert]

@[simp] theorem card_growthStages_succ (P : ℕ → Prop) (n : ℕ) :
    (growthStages P (n + 1)).card =
      (growthStages P n).card + if P n then 1 else 0 := by
  classical
  rw [growthStages_succ]
  by_cases h : P n
  · simp [h, growthStages, Finset.mem_filter]
  · simp [h]

/-- Every selected step multiplies the state by more than `d/c`; monotone
unselected steps do not lose any of the accumulated growth. -/
theorem pow_mul_lt_of_filtered_growth
    {a : ℕ → ℕ} {P : ℕ → Prop} {c d q : ℕ}
    (hc : 0 < c) (ha0 : 0 < a 0) (ha : Monotone a)
    (hgrowth : ∀ i < q, P i → c * a i < d * a (i + 1))
    (hP : (growthStages P q).Nonempty) :
    c ^ (growthStages P q).card * a 0 <
      d ^ (growthStages P q).card * a q := by
  have hinvariant : ∀ n ≤ q,
      c ^ (growthStages P n).card * a 0 ≤
          d ^ (growthStages P n).card * a n ∧
        ((growthStages P n).Nonempty →
          c ^ (growthStages P n).card * a 0 <
            d ^ (growthStages P n).card * a n) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hnq : n < q := by omega
        specialize ih (by omega)
        rw [card_growthStages_succ]
        by_cases hPn : P n
        · simp only [hPn, if_true]
          rw [pow_succ, pow_succ]
          have han : 0 < a n := ha0.trans_le (ha (Nat.zero_le n))
          have hd : 0 < d := by
            by_contra hd0
            simp only [Nat.not_lt, Nat.le_zero] at hd0
            simpa [hd0] using hgrowth n hnq hPn
          have hstep :
              c ^ (growthStages P n).card * c * a 0 <
                d ^ (growthStages P n).card * d * a (n + 1) := by
            calc
              c ^ (growthStages P n).card * c * a 0 =
                  c * (c ^ (growthStages P n).card * a 0) := by ring
              _ ≤ c * (d ^ (growthStages P n).card * a n) :=
                Nat.mul_le_mul_left c ih.1
              _ = d ^ (growthStages P n).card * (c * a n) := by ring
              _ < d ^ (growthStages P n).card * (d * a (n + 1)) := by
                exact Nat.mul_lt_mul_of_pos_left (hgrowth n hnq hPn)
                  (pow_pos hd _)
              _ = d ^ (growthStages P n).card * d * a (n + 1) := by ring
          exact ⟨hstep.le, fun _ ↦ hstep⟩
        · simp only [hPn, if_false, add_zero]
          refine ⟨ih.1.trans (Nat.mul_le_mul_left _ (ha (Nat.le_succ n))), ?_⟩
          intro hnonempty
          have heq : growthStages P (n + 1) = growthStages P n := by
            rw [growthStages_succ]
            simp [hPn]
          have hnonempty' : (growthStages P n).Nonempty := by
            rwa [heq] at hnonempty
          exact (ih.2 hnonempty').trans_le
            (Nat.mul_le_mul_left _ (ha (Nat.le_succ n)))
  exact (hinvariant q le_rfl).2 hP

/-- A variant of `pow_mul_lt_of_filtered_growth` anchored at any lower bound
which holds at every selected stage.  This is useful when the sequence only
enters the large-state regime after some initial stages. -/
theorem pow_mul_lt_of_filtered_growth_from_lower_bound
    {a : ℕ → ℕ} {P : ℕ → Prop} {L c d q : ℕ}
    (hL : 0 < L) (hc : 0 < c) (ha : Monotone a)
    (hbelow : ∀ i < q, P i → L ≤ a i)
    (hgrowth : ∀ i < q, P i → c * a i < d * a (i + 1))
    (hP : (growthStages P q).Nonempty) :
    c ^ (growthStages P q).card * L <
      d ^ (growthStages P q).card * a q := by
  have hinvariant : ∀ n ≤ q, (growthStages P n).Nonempty →
      c ^ (growthStages P n).card * L <
        d ^ (growthStages P n).card * a n := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hnq : n < q := by omega
        specialize ih (by omega)
        intro hnonempty
        rw [card_growthStages_succ]
        by_cases hPn : P n
        · simp only [hPn, if_true]
          rw [pow_succ, pow_succ]
          have han : 0 < a n := hL.trans_le (hbelow n hnq hPn)
          have hd : 0 < d := by
            have hright : 0 < d * a (n + 1) :=
              (Nat.mul_pos hc han).trans (hgrowth n hnq hPn)
            exact Nat.pos_of_mul_pos_right hright
          by_cases hprev : (growthStages P n).Nonempty
          · have hprefix := ih hprev
            calc
              c ^ (growthStages P n).card * c * L =
                  c * (c ^ (growthStages P n).card * L) := by ring
              _ < c * (d ^ (growthStages P n).card * a n) :=
                Nat.mul_lt_mul_of_pos_left hprefix hc
              _ = d ^ (growthStages P n).card * (c * a n) := by ring
              _ < d ^ (growthStages P n).card * (d * a (n + 1)) :=
                Nat.mul_lt_mul_of_pos_left (hgrowth n hnq hPn) (pow_pos hd _)
              _ = d ^ (growthStages P n).card * d * a (n + 1) := by ring
          · have hempty : growthStages P n = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp hprev
            simp only [hempty, Finset.card_empty, pow_zero, one_mul]
            exact (Nat.mul_le_mul_left c (hbelow n hnq hPn)).trans_lt
              (hgrowth n hnq hPn)
        · simp only [hPn, if_false, add_zero]
          have heq : growthStages P (n + 1) = growthStages P n := by
            rw [growthStages_succ]
            simp [hPn]
          have hprev : (growthStages P n).Nonempty := by
            rwa [heq] at hnonempty
          exact (ih hprev).trans_le
            (Nat.mul_le_mul_left _ (ha (Nat.le_succ n)))
  exact hinvariant q le_rfl hP

/-! ## The two CFP regimes -/

/-- Stages in the small-state regime which fail the first slow-growth
alternative. -/
def smallNonbadStages (a : ℕ → ℕ) (x u q : ℕ) : Finset ℕ :=
  growthStages (fun i ↦ u * a i ≤ x ∧ 3 * a i < 2 * a (i + 1)) q

/-- Stages in the large-state regime which fail the second slow-growth
alternative. -/
def largeNonbadStages (a : ℕ → ℕ) (x u R q : ℕ) : Finset ℕ :=
  growthStages
    (fun i ↦ x < u * a i ∧ (R + 1) * a i < R * a (i + 1)) q

/-- CFP's definition of a bad stage, written without division. -/
def cyclicBadStages (a : ℕ → ℕ) (x u R q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun i ↦
    (u * a i ≤ x ∧ 2 * a (i + 1) ≤ 3 * a i) ∨
      (x < u * a i ∧ 4 * a i < x ∧
        R * a (i + 1) ≤ (R + 1) * a i)

/-- The complementary set of stages below `q`. -/
def cyclicNonbadStages (a : ℕ → ℕ) (x u R q : ℕ) : Finset ℕ :=
  Finset.range q \ cyclicBadStages a x u R q

/-- Bernoulli's inequality in the exact integral form used to group `R`
large-regime growth stages into one doubling. -/
theorem two_mul_pow_le_succ_pow (R : ℕ) (hR : 0 < R) :
    2 * R ^ R ≤ (R + 1) ^ R := by
  have hbern := pow_add_mul_le_add_pow (R := ℕ)
    (a := R) (b := 1) (by omega) (by omega) R
  have hpow : R * R ^ (R - 1) = R ^ R := by
    calc
      R * R ^ (R - 1) = R ^ (R - 1) * R := by ring
      _ = R ^ ((R - 1) + 1) := (pow_succ R (R - 1)).symm
      _ = R ^ R := by rw [Nat.sub_add_cancel hR]
  simpa [hpow, two_mul, add_comm] using hbern

/-- Once there are at least `3*u` factors, the factor `(3/2)` beats the
remaining `3^u` allowance. -/
theorem two_pow_mul_three_pow_lt_three_pow {u k : ℕ}
    (hu : 0 < u) (hk : 3 * u ≤ k) :
    2 ^ k * 3 ^ u < 3 ^ k := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hbase : 24 ^ u < 27 ^ u :=
    Nat.pow_lt_pow_left (by norm_num) hu.ne'
  have he : 2 ^ e ≤ 3 ^ e := Nat.pow_le_pow_left (by omega) e
  have hmul : 2 ^ e * 24 ^ u < 3 ^ e * 27 ^ u :=
    Nat.mul_lt_mul_of_le_of_lt he hbase (pow_pos (by omega) _)
  convert hmul using 1
  · simp only [pow_add, pow_mul]
    norm_num
    calc
      8 ^ u * 2 ^ e * 3 ^ u = 2 ^ e * (8 ^ u * 3 ^ u) := by ring
      _ = 2 ^ e * 24 ^ u := by rw [← mul_pow]; norm_num
  · simp only [pow_add, pow_mul]
    norm_num
    ring

/-- There are fewer than `3*u` fast stages before the process leaves the
small-state regime. -/
theorem smallNonbadStages_card_lt_three_mul
    {a : ℕ → ℕ} {x u q : ℕ}
    (hu : 0 < u) (ha0 : 0 < a 0) (ha : Monotone a)
    (hxpow : x ≤ 3 ^ u) (hfinal : 4 * a q < x) :
    (smallNonbadStages a x u q).card < 3 * u := by
  by_contra h
  have hk : 3 * u ≤ (smallNonbadStages a x u q).card := by omega
  have hkpos : 0 < (smallNonbadStages a x u q).card :=
    (mul_pos (by omega) hu).trans_le hk
  have hnonempty : (smallNonbadStages a x u q).Nonempty :=
    Finset.card_pos.mp hkpos
  have hgrowth :
      3 ^ (smallNonbadStages a x u q).card * a 0 <
        2 ^ (smallNonbadStages a x u q).card * a q := by
    apply pow_mul_lt_of_filtered_growth (c := 3) (d := 2)
      (P := fun i ↦ u * a i ≤ x ∧ 3 * a i < 2 * a (i + 1))
      (q := q) (by omega) ha0 ha
    · intro i hi hPi
      exact hPi.2
    · simpa [smallNonbadStages] using hnonempty
  have haq : a q < 3 ^ u := by omega
  have hthree : 3 ^ (smallNonbadStages a x u q).card <
      2 ^ (smallNonbadStages a x u q).card * 3 ^ u := by
    calc
      3 ^ (smallNonbadStages a x u q).card ≤
          3 ^ (smallNonbadStages a x u q).card * a 0 :=
        Nat.le_mul_of_pos_right _ ha0
      _ < 2 ^ (smallNonbadStages a x u q).card * a q := hgrowth
      _ < 2 ^ (smallNonbadStages a x u q).card * 3 ^ u :=
        Nat.mul_lt_mul_of_pos_left haq (pow_pos (by omega) _)
  exact (not_lt_of_ge
    (two_pow_mul_three_pow_lt_three_pow hu hk).le) hthree

/-- `R*v` factors of `(R+1)/R` produce at least the factor `2^v`.
The extra factors after `R*v` only improve the estimate. -/
theorem two_pow_mul_pow_le_succ_pow {R v k : ℕ}
    (hR : 0 < R) (hk : R * v ≤ k) :
    2 ^ v * R ^ k ≤ (R + 1) ^ k := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hbase := two_mul_pow_le_succ_pow R hR
  have hgroup : 2 ^ v * R ^ (R * v) ≤ (R + 1) ^ (R * v) := by
    have hp := Nat.pow_le_pow_left hbase v
    simpa only [mul_pow, pow_mul] using hp
  calc
    2 ^ v * R ^ (R * v + e) =
        (2 ^ v * R ^ (R * v)) * R ^ e := by rw [pow_add]; ring
    _ ≤ (R + 1) ^ (R * v) * (R + 1) ^ e := by
      exact Nat.mul_le_mul hgroup (Nat.pow_le_pow_left (by omega) e)
    _ = (R + 1) ^ (R * v + e) := (pow_add (R + 1) (R * v) e).symm

/-- The number of fast stages in the large-state regime is at most `R*v`.
The proof applies the lower-bound growth invariant to the rescaled sequence
`u * a i`, so it does not require the original sequence to start in the
large-state regime. -/
theorem largeNonbadStages_card_le_mul
    {a : ℕ → ℕ} {x u R v q : ℕ}
    (hu : 0 < u) (hR : 0 < R) (ha0 : 0 < a 0) (ha : Monotone a)
    (huPow : u ≤ 2 ^ v) (hfinal : 4 * a q < x) :
    (largeNonbadStages a x u R q).card ≤ R * v := by
  by_contra h
  have hk : R * v ≤ (largeNonbadStages a x u R q).card := by omega
  have hkpos : 0 < (largeNonbadStages a x u R q).card := by omega
  have hnonempty : (largeNonbadStages a x u R q).Nonempty :=
    Finset.card_pos.mp hkpos
  have haqpos : 0 < a q := ha0.trans_le (ha (Nat.zero_le q))
  have hx : 0 < x := (Nat.mul_pos (by omega) haqpos).trans hfinal
  let b : ℕ → ℕ := fun i ↦ u * a i
  have hbmono : Monotone b := fun _ _ hij ↦
    Nat.mul_le_mul_left u (ha hij)
  have hgrowth :
      (R + 1) ^ (largeNonbadStages a x u R q).card * x <
        R ^ (largeNonbadStages a x u R q).card * b q := by
    apply pow_mul_lt_of_filtered_growth_from_lower_bound
      (a := b) (L := x) (c := R + 1) (d := R)
      (P := fun i ↦ x < u * a i ∧
        (R + 1) * a i < R * a (i + 1))
      (q := q) hx (by omega) hbmono
    · intro i hi hPi
      exact hPi.1.le
    · intro i hi hPi
      dsimp [b]
      have := Nat.mul_lt_mul_of_pos_left hPi.2 hu
      simpa only [mul_assoc, mul_left_comm u, mul_comm u] using this
    · simpa [largeNonbadStages] using hnonempty
  have hnum :
      2 ^ v * R ^ (largeNonbadStages a x u R q).card ≤
        (R + 1) ^ (largeNonbadStages a x u R q).card :=
    two_pow_mul_pow_le_succ_pow hR hk
  have hscaled :
      R ^ (largeNonbadStages a x u R q).card * (2 ^ v * x) <
        R ^ (largeNonbadStages a x u R q).card * (u * a q) := by
    calc
      R ^ (largeNonbadStages a x u R q).card * (2 ^ v * x) =
          (2 ^ v * R ^ (largeNonbadStages a x u R q).card) * x := by ring
      _ ≤ (R + 1) ^ (largeNonbadStages a x u R q).card * x :=
        Nat.mul_le_mul_right x hnum
      _ < R ^ (largeNonbadStages a x u R q).card * b q := hgrowth
      _ = R ^ (largeNonbadStages a x u R q).card * (u * a q) := by rfl
  have htwo : 2 ^ v * x < u * a q :=
    Nat.lt_of_mul_lt_mul_left hscaled
  have hux : u * x ≤ 2 ^ v * x := Nat.mul_le_mul_right x huPow
  have hxa : x < a q := by
    apply Nat.lt_of_mul_lt_mul_left (a := u)
    exact hux.trans_lt htwo
  omega

/-- Every nonbad stage belongs to one of the two fast-growth regimes. -/
theorem cyclicNonbadStages_subset_fastStages
    {a : ℕ → ℕ} {x u R q : ℕ} (ha : Monotone a)
    (hfinal : 4 * a q < x) :
    cyclicNonbadStages a x u R q ⊆
      smallNonbadStages a x u q ∪ largeNonbadStages a x u R q := by
  intro i hi
  have hiq : i < q := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
  have hnBad : i ∉ cyclicBadStages a x u R q :=
    (Finset.mem_sdiff.mp hi).2
  have haiq : a i ≤ a q := ha hiq.le
  have hfour : 4 * a i < x :=
    (Nat.mul_le_mul_left 4 haiq).trans_lt hfinal
  have hnBad' : ¬ ((u * a i ≤ x ∧ 2 * a (i + 1) ≤ 3 * a i) ∨
      (x < u * a i ∧ 4 * a i < x ∧
        R * a (i + 1) ≤ (R + 1) * a i)) := by
    intro hbad
    apply hnBad
    simp only [cyclicBadStages, Finset.mem_filter, Finset.mem_range]
    exact ⟨hiq, hbad⟩
  simp only [Finset.mem_union, smallNonbadStages, largeNonbadStages,
    growthStages, Finset.mem_filter, Finset.mem_range]
  by_cases hsmall : u * a i ≤ x
  · left
    refine ⟨hiq, hsmall, ?_⟩
    have hnotSlow : ¬ 2 * a (i + 1) ≤ 3 * a i := by
      intro hslow
      exact hnBad' (Or.inl ⟨hsmall, hslow⟩)
    omega
  · right
    have hlarge : x < u * a i := by omega
    refine ⟨hiq, hlarge, ?_⟩
    have hnotSlow : ¬ R * a (i + 1) ≤ (R + 1) * a i := by
      intro hslow
      exact hnBad' (Or.inr ⟨hlarge, hfour, hslow⟩)
    omega

/-- Pure bad-stage count from CFP Lemma 3.1: fewer than `4*u` stages can
fail both slow-growth alternatives. -/
theorem cyclicNonbadStages_card_lt_four_mul
    {a : ℕ → ℕ} {x u R v q : ℕ}
    (hu : 0 < u) (hR : 2 ≤ R) (hRu : R ≤ u)
    (ha0 : 0 < a 0) (ha : Monotone a)
    (hxpow : x ≤ 3 ^ u) (huPow : u ≤ 2 ^ v) (hRv : R * v ≤ u)
    (hfinal : 4 * a q < x) :
    (cyclicNonbadStages a x u R q).card < 4 * u := by
  have hsubset := cyclicNonbadStages_subset_fastStages
    (u := u) (R := R) ha hfinal
  have hcard : (cyclicNonbadStages a x u R q).card ≤
      (smallNonbadStages a x u q).card +
        (largeNonbadStages a x u R q).card := by
    exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hsmall := smallNonbadStages_card_lt_three_mul
    (a := a) (x := x) (u := u) (q := q) hu ha0 ha hxpow hfinal
  have hlarge := largeNonbadStages_card_le_mul
    (a := a) (x := x) (u := u) (R := R) (v := v) (q := q)
    hu (by omega) ha0 ha huPow hfinal
  omega

/-- If the process has at least `5*u` stages, at least `u` of them are bad. -/
theorem cyclicBadStages_card_ge
    {a : ℕ → ℕ} {x u R v q : ℕ}
    (hu : 0 < u) (hR : 2 ≤ R) (hRu : R ≤ u)
    (ha0 : 0 < a 0) (ha : Monotone a)
    (hxpow : x ≤ 3 ^ u) (huPow : u ≤ 2 ^ v) (hRv : R * v ≤ u)
    (hfinal : 4 * a q < x) (hq : 5 * u ≤ q) :
    u ≤ (cyclicBadStages a x u R q).card := by
  have hnonbad := cyclicNonbadStages_card_lt_four_mul
    hu hR hRu ha0 ha hxpow huPow hRv hfinal
  have hbadSub : cyclicBadStages a x u R q ⊆ Finset.range q := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hpartition := Finset.card_sdiff_add_card
    (Finset.range q) (cyclicBadStages a x u R q)
  have hunion : Finset.range q ∪ cyclicBadStages a x u R q = Finset.range q :=
    Finset.union_eq_left.mpr hbadSub
  rw [hunion, Finset.card_range] at hpartition
  change (cyclicNonbadStages a x u R q).card +
    (cyclicBadStages a x u R q).card = q at hpartition
  omega

end

end Erdos54
