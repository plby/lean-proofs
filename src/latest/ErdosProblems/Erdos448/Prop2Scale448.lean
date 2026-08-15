import ErdosProblems.Erdos448.Basic

namespace Erdos448Scratch.Prop2Scale

open scoped BigOperators

/-!
This file isolates the completely finite part of Erdős--Tenenbaum,
Proposition 2, after specializing `sigma = theta = 2`, `y = 1/2`, and
`epsilon = 1/5`.  The analytic normality assertion is exposed as the
pointwise hypothesis `Equation7`; everything after it is finite divisor,
gcd, and dyadic-scale bookkeeping.
-/

/-- `Omega(m,B)`: prime factors of `m` below `B`, counted with
multiplicity.  This is the natural-valued version of the paper's notation. -/
def omegaBelowNat (m B : ℕ) : ℕ :=
  ∑ p ∈ m.factorization.support.filter (fun p => p < B), m.factorization p

/-- The paper's symmetric ordered close-pair relation: the two entries are
distinct and their ratio lies strictly between `1/2` and `2`. -/
def closeDivisorPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (n.divisors.product n.divisors).filter fun p =>
    p.1 ≠ p.2 ∧ p.1 < 2 * p.2 ∧ p.2 < 2 * p.1

lemma mem_closeDivisorPairs_iff {n a b : ℕ} :
    (a, b) ∈ closeDivisorPairs n ↔
      a ∈ n.divisors ∧ b ∈ n.divisors ∧
        a ≠ b ∧ a < 2 * b ∧ b < 2 * a := by
  simp [closeDivisorPairs, and_assoc]

/-- One of the two orientations, used when the symmetric sum is split. -/
def increasingCloseDivisorPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (closeDivisorPairs n).filter fun p => p.1 < p.2

lemma increasingCloseDivisorPairs_subset (n : ℕ) :
    increasingCloseDivisorPairs n ⊆ closeDivisorPairs n :=
  Finset.filter_subset _ _

def decreasingCloseDivisorPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (closeDivisorPairs n).filter fun p => p.2 < p.1

def swapPair (p : ℕ × ℕ) : ℕ × ℕ := (p.2, p.1)

@[simp] lemma swapPair_swapPair (p : ℕ × ℕ) : swapPair (swapPair p) = p := by
  cases p
  rfl

lemma swapPair_mem_close_iff {n : ℕ} {p : ℕ × ℕ} :
    swapPair p ∈ closeDivisorPairs n ↔ p ∈ closeDivisorPairs n := by
  rcases p with ⟨a, b⟩
  simp only [swapPair, mem_closeDivisorPairs_iff]
  aesop

lemma closeDivisorPairs_eq_orientations (n : ℕ) :
    closeDivisorPairs n =
      increasingCloseDivisorPairs n ∪ decreasingCloseDivisorPairs n := by
  ext p
  simp only [increasingCloseDivisorPairs, decreasingCloseDivisorPairs,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hp
    have hne := (mem_closeDivisorPairs_iff.mp hp).2.2.1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hp, hlt⟩
    · exact Or.inr ⟨hp, hgt⟩
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp

lemma increasing_disjoint_decreasing (n : ℕ) :
    Disjoint (increasingCloseDivisorPairs n) (decreasingCloseDivisorPairs n) := by
  rw [Finset.disjoint_left]
  intro p hpinc hpdec
  have hinc := (Finset.mem_filter.mp hpinc).2
  have hdec := (Finset.mem_filter.mp hpdec).2
  omega

/-- Splitting the symmetric ordered source sum into one orientation pairs
each increasing pair with its reversal. -/
theorem sum_closeDivisorPairs_eq_sum_increasing_add_swap
    (n : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ closeDivisorPairs n, F p =
      ∑ p ∈ increasingCloseDivisorPairs n, (F p + F (swapPair p)) := by
  have hdec :
      (∑ p ∈ decreasingCloseDivisorPairs n, F p) =
        ∑ p ∈ increasingCloseDivisorPairs n, F (swapPair p) := by
    apply Finset.sum_bij (fun p hp => swapPair p)
    · intro p hp
      have hp' : p ∈ closeDivisorPairs n ∧ p.2 < p.1 := by
        simpa [decreasingCloseDivisorPairs] using hp
      apply Finset.mem_filter.mpr
      exact ⟨swapPair_mem_close_iff.mpr hp'.1, hp'.2⟩
    · intro p hp q hq heq
      have := congrArg swapPair heq
      simpa only [swapPair_swapPair] using this
    · intro q hq
      refine ⟨swapPair q, ?_, by simp⟩
      have hq' : q ∈ closeDivisorPairs n ∧ q.1 < q.2 := by
        simpa [increasingCloseDivisorPairs] using hq
      apply Finset.mem_filter.mpr
      exact ⟨swapPair_mem_close_iff.mpr hq'.1, hq'.2⟩
    · intro p hp
      simp only [swapPair_swapPair]
  rw [closeDivisorPairs_eq_orientations n,
    Finset.sum_union (increasing_disjoint_decreasing n), hdec,
    Finset.sum_add_distrib]

/-- The common factor extracted from a close divisor pair. -/
def pairCommon (p : ℕ × ℕ) : ℕ := Nat.gcd p.1 p.2

/-- The left coprime component after extracting the gcd. -/
def pairReducedLeft (p : ℕ × ℕ) : ℕ := p.1 / pairCommon p

/-- The right coprime component after extracting the gcd. -/
def pairReducedRight (p : ℕ × ℕ) : ℕ := p.2 / pairCommon p

/-- Right-closed dyadic scale of the reduced left component.  For `d > 1`,
this is the unique `k` such that `2^k < d ≤ 2^(k+1)`. -/
def pairScale (p : ℕ × ℕ) : ℕ := Nat.log 2 (pairReducedLeft p - 1)

/-- Pairs whose reduced left component lies on the `k`th dyadic scale. -/
def closeDivisorPairsAtScale (n k : ℕ) : Finset (ℕ × ℕ) :=
  (closeDivisorPairs n).filter fun p => pairScale p = k

lemma mem_closeDivisorPairsAtScale_iff {n k : ℕ} {p : ℕ × ℕ} :
    p ∈ closeDivisorPairsAtScale n k ↔
      p ∈ closeDivisorPairs n ∧ pairScale p = k := by
  simp [closeDivisorPairsAtScale]

lemma close_pair_left_pos {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) : 0 < p.1 := by
  rcases mem_closeDivisorPairs_iff.mp hp with ⟨ha, _, _, _, _⟩
  exact Nat.pos_of_mem_divisors ha

lemma close_pair_right_pos {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) : 0 < p.2 := by
  rcases mem_closeDivisorPairs_iff.mp hp with ⟨_, hb, _, _, _⟩
  exact Nat.pos_of_mem_divisors hb

lemma pairCommon_pos {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) : 0 < pairCommon p := by
  exact Nat.gcd_pos_of_pos_left _ (close_pair_left_pos hp)

lemma pairReducedLeft_pos {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) : 0 < pairReducedLeft p := by
  exact Nat.div_pos
    (Nat.gcd_le_left _ (close_pair_left_pos hp)) (pairCommon_pos hp)

lemma pairReducedRight_pos {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) : 0 < pairReducedRight p := by
  exact Nat.div_pos
    (Nat.gcd_le_right _ (close_pair_right_pos hp)) (pairCommon_pos hp)

/-- Extracting the gcd reconstructs the left member of the original pair. -/
lemma pairReducedLeft_mul_pairCommon {n : ℕ} {p : ℕ × ℕ}
    (_hp : p ∈ closeDivisorPairs n) :
    pairReducedLeft p * pairCommon p = p.1 := by
  exact Nat.div_mul_cancel (Nat.gcd_dvd_left p.1 p.2)

/-- Extracting the gcd reconstructs the right member of the original pair. -/
lemma pairReducedRight_mul_pairCommon {n : ℕ} {p : ℕ × ℕ}
    (_hp : p ∈ closeDivisorPairs n) :
    pairReducedRight p * pairCommon p = p.2 := by
  exact Nat.div_mul_cancel (Nat.gcd_dvd_right p.1 p.2)

/-- The two reduced components are coprime. -/
lemma pairReduced_coprime {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) :
    Nat.Coprime (pairReducedLeft p) (pairReducedRight p) := by
  exact Nat.coprime_div_gcd_div_gcd (pairCommon_pos hp)

/-- Division by the positive common factor preserves the close-pair
orientation. -/
lemma pairReduced_close {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) :
    pairReducedLeft p ≠ pairReducedRight p ∧
      pairReducedLeft p < 2 * pairReducedRight p ∧
      pairReducedRight p < 2 * pairReducedLeft p := by
  have hg := pairCommon_pos hp
  have ha := pairReducedLeft_mul_pairCommon hp
  have hb := pairReducedRight_mul_pairCommon hp
  rcases mem_closeDivisorPairs_iff.mp hp with ⟨_, _, hne, hab, hba⟩
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    apply hne
    rw [← ha, ← hb, heq]
  · apply (Nat.mul_lt_mul_right hg).mp
    rw [Nat.mul_assoc, ha, hb]
    exact hab
  · apply (Nat.mul_lt_mul_right hg).mp
    rw [Nat.mul_assoc, ha, hb]
    exact hba

lemma two_le_pairReducedLeft {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) : 2 ≤ pairReducedLeft p := by
  rcases pairReduced_close hp with ⟨hne, hforward, hbackward⟩
  have hleft := pairReducedLeft_pos hp
  have hright := pairReducedRight_pos hp
  omega

/-- A reduced left component at least three has positive source scale.  In
the paper this lower bound is supplied by the roughness factor `chi(d,2)`. -/
lemma pairScale_pos_of_three_le {p : ℕ × ℕ}
    (hthree : 3 ≤ pairReducedLeft p) : 0 < pairScale p := by
  apply Nat.log_pos (by decide)
  omega

/-- The reduced product times the gcd is the lcm of the original pair. -/
lemma reducedProduct_mul_common_eq_lcm {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) :
    pairReducedLeft p * pairReducedRight p * pairCommon p =
      Nat.lcm p.1 p.2 := by
  have hg := pairCommon_pos hp
  have ha := pairReducedLeft_mul_pairCommon hp
  have hb := pairReducedRight_mul_pairCommon hp
  apply Nat.eq_of_mul_eq_mul_left hg
  calc
    pairCommon p * (pairReducedLeft p * pairReducedRight p * pairCommon p) =
        (pairReducedLeft p * pairCommon p) *
          (pairReducedRight p * pairCommon p) := by ring
    _ = p.1 * p.2 := by rw [ha, hb]
    _ = pairCommon p * Nat.lcm p.1 p.2 := by
      simpa [pairCommon, mul_comm] using (Nat.gcd_mul_lcm p.1 p.2).symm

/-- Consequently the reduced product times the gcd divides `n`. -/
lemma reducedProduct_mul_common_dvd {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) :
    pairReducedLeft p * pairReducedRight p * pairCommon p ∣ n := by
  rw [reducedProduct_mul_common_eq_lcm hp]
  rcases mem_closeDivisorPairs_iff.mp hp with ⟨ha, hb, _, _, _⟩
  exact Nat.lcm_dvd (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb)

/-- The gcd coordinates used after the factorization `a = dt`, `b = d't`. -/
def gcdCoordinates (p : ℕ × ℕ) : (ℕ × ℕ) × ℕ :=
  ((pairReducedLeft p, pairReducedRight p), pairCommon p)

lemma gcdCoordinates_reconstruct_left {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) :
    (gcdCoordinates p).1.1 * (gcdCoordinates p).2 = p.1 :=
  pairReducedLeft_mul_pairCommon hp

lemma gcdCoordinates_reconstruct_right {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) :
    (gcdCoordinates p).1.2 * (gcdCoordinates p).2 = p.2 :=
  pairReducedRight_mul_pairCommon hp

/-- Gcd coordinates are injective on close pairs, since multiplying the
reduced components by `t` reconstructs the original pair. -/
lemma gcdCoordinates_injOn (n : ℕ) :
    Set.InjOn gcdCoordinates (closeDivisorPairs n : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  apply Prod.ext
  · rw [← gcdCoordinates_reconstruct_left hp,
      ← gcdCoordinates_reconstruct_left hq, heq]
  · rw [← gcdCoordinates_reconstruct_right hp,
      ← gcdCoordinates_reconstruct_right hq, heq]

lemma pairReducedLeft_mem_divisors {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) : pairReducedLeft p ∈ n.divisors := by
  rcases mem_closeDivisorPairs_iff.mp hp with ⟨ha, _, _, _, _⟩
  apply Nat.mem_divisors.mpr
  refine ⟨?_, (Nat.mem_divisors.mp ha).2⟩
  have hred_dvd_left : pairReducedLeft p ∣ p.1 :=
    ⟨pairCommon p, (pairReducedLeft_mul_pairCommon hp).symm⟩
  exact hred_dvd_left.trans (Nat.dvd_of_mem_divisors ha)

lemma pairReducedRight_mem_divisors {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) : pairReducedRight p ∈ n.divisors := by
  rcases mem_closeDivisorPairs_iff.mp hp with ⟨_, hb, _, _, _⟩
  apply Nat.mem_divisors.mpr
  refine ⟨?_, (Nat.mem_divisors.mp hb).2⟩
  have hred_dvd_right : pairReducedRight p ∣ p.2 :=
    ⟨pairCommon p, (pairReducedRight_mul_pairCommon hp).symm⟩
  exact hred_dvd_right.trans (Nat.dvd_of_mem_divisors hb)

lemma pairCommon_mem_divisors {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) : pairCommon p ∈ n.divisors := by
  rcases mem_closeDivisorPairs_iff.mp hp with ⟨ha, _, _, _, _⟩
  apply Nat.mem_divisors.mpr
  refine ⟨?_, (Nat.mem_divisors.mp ha).2⟩
  exact (Nat.gcd_dvd_left p.1 p.2).trans (Nat.dvd_of_mem_divisors ha)

/-- The reduced left component lies in the source's right-closed dyadic
block `(2^k,2^(k+1)]`. -/
lemma pairReducedLeft_mem_dyadic_scale {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) :
    2 ^ pairScale p < pairReducedLeft p ∧
      pairReducedLeft p ≤ 2 ^ (pairScale p + 1) := by
  have hsubpos : 0 < pairReducedLeft p - 1 := by
    have htwo := two_le_pairReducedLeft hp
    omega
  have hlower := Nat.pow_log_le_self 2 hsubpos.ne'
  have hupper := Nat.lt_pow_succ_log_self (b := 2) (by decide)
    (pairReducedLeft p - 1)
  constructor
  · change 2 ^ Nat.log 2 (pairReducedLeft p - 1) < pairReducedLeft p
    omega
  · change pairReducedLeft p ≤
      2 ^ (Nat.log 2 (pairReducedLeft p - 1) + 1)
    omega

/-- The source's right-closed scale is at most the formal half-open scale. -/
lemma pairScale_le_formalScale {n : ℕ} {p : ℕ × ℕ}
    (_hp : p ∈ closeDivisorPairs n) :
    pairScale p ≤ Nat.log 2 (pairReducedLeft p) := by
  exact Nat.log_mono_right (Nat.sub_le _ _)

/-- The formal half-open scale differs from the source scale by at most one. -/
lemma formalScale_le_pairScale_add_one {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) :
    Nat.log 2 (pairReducedLeft p) ≤ pairScale p + 1 := by
  have hupper := (pairReducedLeft_mem_dyadic_scale hp).2
  have hlog := Nat.log_mono_right (b := 2) hupper
  rw [Nat.log_pow (by decide)] at hlog
  exact hlog

/-- Every occurring reduced scale is bounded by the block containing `n`. -/
lemma pairScale_lt_log_add_one {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairs n) :
    pairScale p < Nat.log 2 n + 1 := by
  rcases mem_closeDivisorPairs_iff.mp hp with ⟨ha, _, _, _, _⟩
  have hred_le : pairReducedLeft p ≤ p.1 := Nat.div_le_self _ _
  have ha_le_n : p.1 ≤ n := Nat.divisor_le ha
  apply Nat.lt_succ_of_le
  exact (pairScale_le_formalScale hp).trans
    (Nat.log_mono_right (hred_le.trans ha_le_n))

/-- Expanded triples on the source's `k`th right-closed scale.  The relation
between `d,d'` remains symmetric and ordered; no coprimality condition is
imposed in this enlarged sum. -/
def expandedScaleTriples (n k : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((n.divisors.product n.divisors).product n.divisors).filter fun q =>
    q.1.1 ≠ q.1.2 ∧ q.1.1 < 2 * q.1.2 ∧ q.1.2 < 2 * q.1.1 ∧
      2 ^ k < q.1.1 ∧ q.1.1 ≤ 2 ^ (k + 1) ∧
      q.1.1 * q.1.2 * q.2 ∣ n

lemma mem_expandedScaleTriples_iff {n k : ℕ} {d d' t : ℕ} :
    ((d, d'), t) ∈ expandedScaleTriples n k ↔
      d ∈ n.divisors ∧ d' ∈ n.divisors ∧ t ∈ n.divisors ∧
      d ≠ d' ∧ d < 2 * d' ∧ d' < 2 * d ∧
      2 ^ k < d ∧ d ≤ 2 ^ (k + 1) ∧
      d * d' * t ∣ n := by
  simp [expandedScaleTriples, and_assoc]

/-- The product condition is equivalent to the paper's inner residual
divisibility condition in the direction needed for consuming a triple. -/
lemma expandedScaleTriple_t_dvd_residual {n k d d' t : ℕ}
    (hq : ((d, d'), t) ∈ expandedScaleTriples n k) :
    t ∣ n / (d * d') := by
  have hq' := mem_expandedScaleTriples_iff.mp hq
  rcases hq' with ⟨hd, hd', ht, hne, hforward, hbackward,
    hlower, hupper, hprod⟩
  have hbase : d * d' ∣ n := by
    exact (dvd_mul_right (d * d') t).trans hprod
  apply (Nat.dvd_div_iff_mul_dvd hbase).2
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    hprod

lemma gcdCoordinates_mem_expandedScaleTriples {n k : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ closeDivisorPairsAtScale n k) :
    gcdCoordinates p ∈ expandedScaleTriples n k := by
  have hpclose := (mem_closeDivisorPairsAtScale_iff.mp hp).1
  have hscale := (mem_closeDivisorPairsAtScale_iff.mp hp).2
  rw [mem_expandedScaleTriples_iff]
  refine ⟨pairReducedLeft_mem_divisors hpclose,
    pairReducedRight_mem_divisors hpclose,
    pairCommon_mem_divisors hpclose, ?_⟩
  rcases pairReduced_close hpclose with ⟨hne, hforward, hbackward⟩
  rcases pairReducedLeft_mem_dyadic_scale hpclose with ⟨hlower, hupper⟩
  rw [← hscale]
  exact ⟨hne, hforward, hbackward, hlower, hupper,
    reducedProduct_mul_common_dvd hpclose⟩

/-- The selected close-pair numerator in the specialized function `f`.
The predicate is the paper's selected-divisor predicate `chiStar`. -/
noncomputable def selectedClosePairMass (selected : ℕ → Prop)
    [DecidablePred selected] (n : ℕ) : ℝ :=
  ∑ p ∈ closeDivisorPairs n, if selected p.1 then 1 else 0

/-- The `k`th gcd-reduced weighted numerator. -/
noncomputable def gcdScaleMass
    (omegaBelow : ℕ → ℕ → ℕ) (n k : ℕ) : ℝ :=
  ∑ p ∈ closeDivisorPairsAtScale n k,
    ((1 : ℝ) / 2) ^ omegaBelow p.1 (2 ^ k)

/-- The fully expanded `f_k` numerator. -/
noncomputable def expandedScaleMass
    (omegaBelow : ℕ → ℕ → ℕ) (n k : ℕ) : ℝ :=
  ∑ q ∈ expandedScaleTriples n k,
    ((1 : ℝ) / 2) ^ omegaBelow (q.1.1 * q.2) (2 ^ k)

/-- Gcd reduction injects the pair-scale mass into the expanded triple sum.
This is the exact finite factorization step `a = dt`, `b = d't`. -/
theorem gcdScaleMass_le_expandedScaleMass
    (omegaBelow : ℕ → ℕ → ℕ) (n k : ℕ) :
    gcdScaleMass omegaBelow n k ≤ expandedScaleMass omegaBelow n k := by
  classical
  let I := (closeDivisorPairsAtScale n k).image gcdCoordinates
  have hinj : Set.InjOn gcdCoordinates
      (closeDivisorPairsAtScale n k : Set (ℕ × ℕ)) := by
    intro p hp q hq heq
    exact gcdCoordinates_injOn n
      (mem_closeDivisorPairsAtScale_iff.mp hp).1
      (mem_closeDivisorPairsAtScale_iff.mp hq).1 heq
  have hrewrite : gcdScaleMass omegaBelow n k =
      ∑ q ∈ I, ((1 : ℝ) / 2) ^ omegaBelow (q.1.1 * q.2) (2 ^ k) := by
    unfold gcdScaleMass
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      have hpclose := (mem_closeDivisorPairsAtScale_iff.mp hp).1
      rw [gcdCoordinates_reconstruct_left hpclose]
    · exact hinj
  rw [hrewrite]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact gcdCoordinates_mem_expandedScaleTriples hp
  · intro q hq hnot
    positivity

/-- The normalized specialized close-pair function `f`. -/
noncomputable def normalizedSelectedClosePairMoment
    (selected : ℕ → Prop) [DecidablePred selected] (n : ℕ) : ℝ :=
  selectedClosePairMass selected n / (n.divisors.card : ℝ)

/-- The normalized expanded scale function `f_k(1/2,n)`. -/
noncomputable def normalizedExpandedScaleMoment
    (omegaBelow : ℕ → ℕ → ℕ) (n k : ℕ) : ℝ :=
  expandedScaleMass omegaBelow n k / (n.divisors.card : ℝ)

/-- The specialized coefficient in equation (7). -/
noncomputable def specializedScaleCoefficient (ξ : ℝ) (k : ℕ) : ℝ :=
  (2 * Real.log ξ).rpow ((7 / 10 : ℝ) * Real.log 2) *
    (k : ℝ).rpow ((7 / 10 : ℝ) * Real.log 2)

/-- Equation (7), specialized to the fixed parameters. -/
def Equation7 (selected : ℕ → Prop) (omegaBelow : ℕ → ℕ → ℕ) (ξ : ℝ) : Prop :=
  ∀ n p, p ∈ closeDivisorPairs n → selected p.1 →
    (1 : ℝ) ≤ specializedScaleCoefficient ξ (pairScale p) *
      ((1 : ℝ) / 2) ^ omegaBelow p.1 (2 ^ pairScale p)

/-- A dyadic selected-divisor predicate presented by the exact specialized
normality consequence used in equation (7).  The concentration argument is
responsible for proving that most divisors satisfy this predicate. -/
def dyadicEquation7Selected
    (omegaBelow : ℕ → ℕ → ℕ) (ξ : ℝ) (m : ℕ) : Prop :=
  ∀ k : ℕ,
    (1 : ℝ) ≤ specializedScaleCoefficient ξ k *
      ((1 : ℝ) / 2) ^ omegaBelow m (2 ^ k)

theorem dyadicEquation7Selected_satisfies
    (omegaBelow : ℕ → ℕ → ℕ) (ξ : ℝ) :
    Equation7 (dyadicEquation7Selected omegaBelow ξ) omegaBelow ξ := by
  intro n p hp hselected
  exact hselected (pairScale p)

lemma closePairScales_subset_range (n : ℕ) :
    (closeDivisorPairs n).image pairScale ⊆
      Finset.range (Nat.log 2 n + 1) := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
  exact Finset.mem_range.mpr (pairScale_lt_log_add_one hp)

/-- Abstract finite fiber decomposition. -/
theorem selectedClosePairMass_le_scaleSum_of_pointwise
    (selected : ℕ → Prop) (weight : ℕ → ℕ → ℝ)
    (coefficient : ℕ → ℝ) (n : ℕ) [DecidablePred selected]
    (hpoint : ∀ p ∈ closeDivisorPairs n, selected p.1 →
      (1 : ℝ) ≤ coefficient (pairScale p) *
        weight p.1 (2 ^ pairScale p))
    (hnonneg : ∀ p ∈ closeDivisorPairs n,
      0 ≤ coefficient (pairScale p) * weight p.1 (2 ^ pairScale p)) :
    selectedClosePairMass selected n ≤
      ∑ k ∈ (closeDivisorPairs n).image pairScale,
        coefficient k *
          ∑ p ∈ closeDivisorPairsAtScale n k, weight p.1 (2 ^ k) := by
  classical
  have hterm : ∀ p ∈ closeDivisorPairs n,
      (if selected p.1 then (1 : ℝ) else 0) ≤
        coefficient (pairScale p) * weight p.1 (2 ^ pairScale p) := by
    intro p hp
    by_cases hs : selected p.1
    · simpa [hs] using hpoint p hp hs
    · simpa [hs] using hnonneg p hp
  calc
    selectedClosePairMass selected n ≤
        ∑ p ∈ closeDivisorPairs n,
          coefficient (pairScale p) * weight p.1 (2 ^ pairScale p) := by
      exact Finset.sum_le_sum hterm
    _ = ∑ k ∈ (closeDivisorPairs n).image pairScale,
          ∑ p ∈ closeDivisorPairs n with pairScale p = k,
            coefficient (pairScale p) * weight p.1 (2 ^ pairScale p) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun p hp => Finset.mem_image_of_mem pairScale hp) _
    _ = ∑ k ∈ (closeDivisorPairs n).image pairScale,
          coefficient k *
            ∑ p ∈ closeDivisorPairsAtScale n k, weight p.1 (2 ^ k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr
      · ext p
        simp [closeDivisorPairsAtScale]
      · intro p hp
        have hscale : pairScale p = k := by
          exact (mem_closeDivisorPairsAtScale_iff.mp hp).2
        simp [hscale]

/-- The exact specialized Proposition 2 finite inequality. -/
theorem selectedClosePairMass_le_specializedScaleSum
    (selected : ℕ → Prop) (omegaBelow : ℕ → ℕ → ℕ) (ξ : ℝ) (n : ℕ)
    [DecidablePred selected] (hξ : 1 ≤ ξ)
    (h7 : Equation7 selected omegaBelow ξ) :
    selectedClosePairMass selected n ≤
      ∑ k ∈ (closeDivisorPairs n).image pairScale,
        specializedScaleCoefficient ξ k * gcdScaleMass omegaBelow n k := by
  apply selectedClosePairMass_le_scaleSum_of_pointwise
    (selected := selected) (weight := fun m B => ((1 : ℝ) / 2) ^ omegaBelow m B)
    (coefficient := specializedScaleCoefficient ξ) (n := n)
  intro p hp hs
  exact h7 n p hp hs
  intro p hp
  apply mul_nonneg
  · unfold specializedScaleCoefficient
    apply mul_nonneg
    · apply Real.rpow_nonneg
      exact mul_nonneg (by norm_num) (Real.log_nonneg hξ)
    · apply Real.rpow_nonneg
      positivity
  · positivity

/-- Range-indexed form, matching the paper's sum over all relevant scales. -/
theorem selectedClosePairMass_le_specializedRangeScaleSum
    (selected : ℕ → Prop) (omegaBelow : ℕ → ℕ → ℕ) (ξ : ℝ) (n : ℕ)
    [DecidablePred selected] (hξ : 1 ≤ ξ)
    (h7 : Equation7 selected omegaBelow ξ) :
    selectedClosePairMass selected n ≤
      ∑ k ∈ Finset.range (Nat.log 2 n + 1),
        specializedScaleCoefficient ξ k * gcdScaleMass omegaBelow n k := by
  calc
    selectedClosePairMass selected n ≤
        ∑ k ∈ (closeDivisorPairs n).image pairScale,
          specializedScaleCoefficient ξ k * gcdScaleMass omegaBelow n k :=
      selectedClosePairMass_le_specializedScaleSum selected omegaBelow ξ n hξ h7
    _ ≤ ∑ k ∈ Finset.range (Nat.log 2 n + 1),
          specializedScaleCoefficient ξ k * gcdScaleMass omegaBelow n k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (closePairScales_subset_range n)
      intro k hk hnot
      apply mul_nonneg
      · unfold specializedScaleCoefficient
        apply mul_nonneg
        · apply Real.rpow_nonneg
          exact mul_nonneg (by norm_num) (Real.log_nonneg hξ)
        · apply Real.rpow_nonneg
          positivity
      · exact Finset.sum_nonneg fun p hp => by positivity

/-- Final expanded-triple form of the specialized finite Proposition 2. -/
theorem selectedClosePairMass_le_specializedExpandedRangeScaleSum
    (selected : ℕ → Prop) (omegaBelow : ℕ → ℕ → ℕ) (ξ : ℝ) (n : ℕ)
    [DecidablePred selected] (hξ : 1 ≤ ξ)
    (h7 : Equation7 selected omegaBelow ξ) :
    selectedClosePairMass selected n ≤
      ∑ k ∈ Finset.range (Nat.log 2 n + 1),
        specializedScaleCoefficient ξ k * expandedScaleMass omegaBelow n k := by
  calc
    selectedClosePairMass selected n ≤
        ∑ k ∈ Finset.range (Nat.log 2 n + 1),
          specializedScaleCoefficient ξ k * gcdScaleMass omegaBelow n k :=
      selectedClosePairMass_le_specializedRangeScaleSum
        selected omegaBelow ξ n hξ h7
    _ ≤ ∑ k ∈ Finset.range (Nat.log 2 n + 1),
          specializedScaleCoefficient ξ k * expandedScaleMass omegaBelow n k := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left
        (gcdScaleMass_le_expandedScaleMass omegaBelow n k)
      unfold specializedScaleCoefficient
      apply mul_nonneg
      · apply Real.rpow_nonneg
        exact mul_nonneg (by norm_num) (Real.log_nonneg hξ)
      · apply Real.rpow_nonneg
        positivity

/-- Normalized form of Proposition 2, with the same divisor-count
denominator on `f` and on every `f_k`. -/
theorem normalizedSelectedClosePairMoment_le_specializedExpandedScaleSum
    (selected : ℕ → Prop) (omegaBelow : ℕ → ℕ → ℕ) (ξ : ℝ) (n : ℕ)
    [DecidablePred selected] (hξ : 1 ≤ ξ)
    (h7 : Equation7 selected omegaBelow ξ) :
    normalizedSelectedClosePairMoment selected n ≤
      ∑ k ∈ Finset.range (Nat.log 2 n + 1),
        specializedScaleCoefficient ξ k *
          normalizedExpandedScaleMoment omegaBelow n k := by
  have hnum := selectedClosePairMass_le_specializedExpandedRangeScaleSum
    selected omegaBelow ξ n hξ h7
  unfold normalizedSelectedClosePairMoment normalizedExpandedScaleMoment
  calc
    selectedClosePairMass selected n / (n.divisors.card : ℝ) ≤
        (∑ k ∈ Finset.range (Nat.log 2 n + 1),
          specializedScaleCoefficient ξ k * expandedScaleMass omegaBelow n k) /
            (n.divisors.card : ℝ) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = ∑ k ∈ Finset.range (Nat.log 2 n + 1),
          specializedScaleCoefficient ξ k *
            (expandedScaleMass omegaBelow n k / (n.divisors.card : ℝ)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_div_assoc]

/-! ## Formal-bin wrapper for the natural-grid selector -/

/-- Strictly increasing pairs from one formal half-open dyadic fibre. -/
def formalPairsInBin (D : Finset ℕ) (k : ℕ) : Finset (ℕ × ℕ) :=
  ((D.filter fun d => Nat.log 2 d = k).product
    (D.filter fun d => Nat.log 2 d = k)).filter fun p => p.1 < p.2

/-- Ordered off-diagonal pairs from one formal half-open dyadic fibre.
This is the exact pair set counted by the off-diagonal part of the finite
Cauchy energy. -/
def formalOrderedPairsInBin (D : Finset ℕ) (k : ℕ) : Finset (ℕ × ℕ) :=
  (D.filter fun d => Nat.log 2 d = k).offDiag

lemma mem_formalPairsInBin_iff {D : Finset ℕ} {k a b : ℕ} :
    (a, b) ∈ formalPairsInBin D k ↔
      a ∈ D ∧ b ∈ D ∧ Nat.log 2 a = k ∧ Nat.log 2 b = k ∧ a < b := by
  simp only [formalPairsInBin, Finset.mem_filter, Finset.mem_product,
    Prod.fst, Prod.snd]
  aesop

lemma mem_formalOrderedPairsInBin_iff {D : Finset ℕ} {k a b : ℕ} :
    (a, b) ∈ formalOrderedPairsInBin D k ↔
      a ∈ D ∧ b ∈ D ∧ Nat.log 2 a = k ∧ Nat.log 2 b = k ∧ a ≠ b := by
  simp [formalOrderedPairsInBin, and_left_comm, and_comm, and_assoc]

lemma card_formalPairsInBin (D : Finset ℕ) (k : ℕ) :
    (formalPairsInBin D k).card =
      (D.filter fun d => Nat.log 2 d = k).card.choose 2 := by
  simpa [formalPairsInBin] using
    (Finset.card_product_filter_lt
      (s := D.filter fun d => Nat.log 2 d = k))

private lemma sq_eq_self_add_two_mul_choose_two (m : ℕ) :
    m ^ 2 = m + 2 * m.choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        m.succ ^ 2 = m ^ 2 + 2 * m + 1 := by
          simp only [Nat.succ_eq_add_one]
          ring
        _ = (m + 2 * m.choose 2) + 2 * m + 1 := by rw [ih]
        _ = m.succ + 2 * m.succ.choose 2 := by
          rw [show (2 : ℕ) = Nat.succ 1 by rfl, Nat.choose_succ_succ,
            Nat.choose_one_right]
          simp only [Nat.succ_eq_add_one]
          ring

/-- Every unordered pair has exactly two orientations. -/
lemma card_formalOrderedPairsInBin (D : Finset ℕ) (k : ℕ) :
    (formalOrderedPairsInBin D k).card =
      2 * (formalPairsInBin D k).card := by
  rw [formalOrderedPairsInBin, Finset.offDiag_card, card_formalPairsInBin]
  have h := sq_eq_self_add_two_mul_choose_two
    (D.filter fun d => Nat.log 2 d = k).card
  simp only [pow_two] at h
  omega

lemma selectedDyadicUnorderedPairCount_eq_formalPairCards (D : Finset ℕ) :
    Erdos448.selectedDyadicUnorderedPairCount D =
      ∑ k ∈ D.image (Nat.log 2), (formalPairsInBin D k).card := by
  simp only [Erdos448.selectedDyadicUnorderedPairCount,
    Erdos448.sameBinUnorderedPairCount, card_formalPairsInBin]

/-! ### Reindexing unordered formal-bin pairs by their reduced gcd scale -/

/-- All increasing pairs in a common original formal dyadic bin. -/
def formalUnorderedPairs (D : Finset ℕ) : Finset (ℕ × ℕ) :=
  (D.product D).filter fun p =>
    p.1 < p.2 ∧ Nat.log 2 p.1 = Nat.log 2 p.2

lemma mem_formalUnorderedPairs_iff {D : Finset ℕ} {a b : ℕ} :
    (a, b) ∈ formalUnorderedPairs D ↔
      a ∈ D ∧ b ∈ D ∧ a < b ∧ Nat.log 2 a = Nat.log 2 b := by
  simp [formalUnorderedPairs, and_assoc]

lemma formalPairsInBin_pairwiseDisjoint (D : Finset ℕ) :
    (D.image (Nat.log 2) : Set ℕ).PairwiseDisjoint
      (formalPairsInBin D) := by
  intro i hi j hj hij
  change Disjoint (formalPairsInBin D i) (formalPairsInBin D j)
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hiScale := (mem_formalPairsInBin_iff.mp hpi).2.2.1
  have hjScale := (mem_formalPairsInBin_iff.mp hpj).2.2.1
  exact hij (hiScale.symm.trans hjScale)

lemma biUnion_formalPairsInBin (D : Finset ℕ) :
    (D.image (Nat.log 2)).biUnion (formalPairsInBin D) =
      formalUnorderedPairs D := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨k, hk, hpk⟩
    rcases mem_formalPairsInBin_iff.mp hpk with
      ⟨ha, hb, haScale, hbScale, hab⟩
    exact mem_formalUnorderedPairs_iff.mpr
      ⟨ha, hb, hab, haScale.trans hbScale.symm⟩
  · intro hp
    rcases mem_formalUnorderedPairs_iff.mp hp with ⟨ha, hb, hab, hscale⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.log 2 p.1, Finset.mem_image.mpr ⟨p.1, ha, rfl⟩, ?_⟩
    exact mem_formalPairsInBin_iff.mpr ⟨ha, hb, rfl, hscale.symm, hab⟩

lemma selectedDyadicUnorderedPairCount_eq_card_formalUnorderedPairs
    (D : Finset ℕ) :
    Erdos448.selectedDyadicUnorderedPairCount D =
      (formalUnorderedPairs D).card := by
  rw [selectedDyadicUnorderedPairCount_eq_formalPairCards,
    ← Finset.card_biUnion (formalPairsInBin_pairwiseDisjoint D),
    biUnion_formalPairsInBin]

/-- Formal dyadic scale of the smaller reduced gcd component. -/
def reducedFormalPairScale (p : ℕ × ℕ) : ℕ :=
  Nat.log 2 (pairReducedLeft p)

/-- Same-original-bin pairs whose smaller reduced gcd component has scale
`k`. -/
def reducedFormalPairsAtScale (D : Finset ℕ) (k : ℕ) :
    Finset (ℕ × ℕ) :=
  (formalUnorderedPairs D).filter fun p => reducedFormalPairScale p = k

lemma mem_reducedFormalPairsAtScale_iff {D : Finset ℕ} {k : ℕ}
    {p : ℕ × ℕ} :
    p ∈ reducedFormalPairsAtScale D k ↔
      p ∈ formalUnorderedPairs D ∧ reducedFormalPairScale p = k := by
  simp [reducedFormalPairsAtScale]

lemma selectedDyadicUnorderedPairCount_eq_reducedScalePairCards
    (D : Finset ℕ) :
    Erdos448.selectedDyadicUnorderedPairCount D =
      ∑ k ∈ (formalUnorderedPairs D).image reducedFormalPairScale,
        (reducedFormalPairsAtScale D k).card := by
  rw [selectedDyadicUnorderedPairCount_eq_card_formalUnorderedPairs,
    Finset.card_eq_sum_card_image reducedFormalPairScale
      (formalUnorderedPairs D)]
  rfl

/-- Exact formal-bin bridge from the unordered statistic used in `Basic`
to the ordered off-diagonal pair set used by the symmetric source sum. -/
lemma two_mul_selectedDyadicUnorderedPairCount_eq_orderedPairCards
    (D : Finset ℕ) :
    2 * Erdos448.selectedDyadicUnorderedPairCount D =
      ∑ k ∈ D.image (Nat.log 2), (formalOrderedPairsInBin D k).card := by
  rw [selectedDyadicUnorderedPairCount_eq_formalPairCards,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact (card_formalOrderedPairsInBin D k).symm

/-- Two positive integers in one formal dyadic bin form a symmetric close
pair.  Reversal makes the selected larger member the first coordinate. -/
lemma swap_mem_closeDivisorPairs_of_formalPair
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) {p : ℕ × ℕ}
    (hp : p ∈ formalPairsInBin D k) :
    swapPair p ∈ closeDivisorPairs n := by
  rcases mem_formalPairsInBin_iff.mp hp with ⟨haD, hbD, haScale, hbScale, hab⟩
  have ha := hD haD
  have hb := hD hbD
  have haPos := Nat.pos_of_mem_divisors ha
  have hbPos := Nat.pos_of_mem_divisors hb
  have haLower : 2 ^ k ≤ p.1 := by
    rw [← haScale]
    exact Nat.pow_log_le_self 2 haPos.ne'
  have hbUpper : p.2 < 2 ^ (k + 1) := by
    rw [← hbScale]
    exact Nat.lt_pow_succ_log_self (by decide) _
  rw [mem_closeDivisorPairs_iff]
  refine ⟨hb, ha, hab.ne', ?_, ?_⟩
  · change p.2 < 2 * p.1
    rw [pow_succ] at hbUpper
    omega
  · change p.1 < 2 * p.2
    omega

/-- Either orientation of an off-diagonal same-bin pair is a member of the
symmetric close-pair set. -/
lemma mem_closeDivisorPairs_of_formalOrderedPair
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) {p : ℕ × ℕ}
    (hp : p ∈ formalOrderedPairsInBin D k) :
    p ∈ closeDivisorPairs n := by
  rcases mem_formalOrderedPairsInBin_iff.mp hp with
    ⟨haD, hbD, haScale, hbScale, hab⟩
  have ha := hD haD
  have hb := hD hbD
  have haPos := Nat.pos_of_mem_divisors ha
  have hbPos := Nat.pos_of_mem_divisors hb
  have haLower : 2 ^ k ≤ p.1 := by
    rw [← haScale]
    exact Nat.pow_log_le_self 2 haPos.ne'
  have hbLower : 2 ^ k ≤ p.2 := by
    rw [← hbScale]
    exact Nat.pow_log_le_self 2 hbPos.ne'
  have haUpper : p.1 < 2 ^ (k + 1) := by
    rw [← haScale]
    exact Nat.lt_pow_succ_log_self (by decide) _
  have hbUpper : p.2 < 2 ^ (k + 1) := by
    rw [← hbScale]
    exact Nat.lt_pow_succ_log_self (by decide) _
  rw [mem_closeDivisorPairs_iff]
  refine ⟨ha, hb, hab, ?_, ?_⟩
  · rw [pow_succ] at haUpper
    omega
  · rw [pow_succ] at hbUpper
    omega

/-- An increasing pair in a common original formal bin is close in its
unswapped orientation. -/
lemma mem_closeDivisorPairs_of_formalUnorderedPair
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) {p : ℕ × ℕ}
    (hp : p ∈ formalUnorderedPairs D) :
    p ∈ closeDivisorPairs n := by
  rcases mem_formalUnorderedPairs_iff.mp hp with ⟨ha, hb, hab, hscale⟩
  have hbin : p ∈ formalPairsInBin D (Nat.log 2 p.1) :=
    mem_formalPairsInBin_iff.mpr ⟨ha, hb, rfl, hscale.symm, hab⟩
  exact swapPair_mem_close_iff.mp
    (swap_mem_closeDivisorPairs_of_formalPair hD hbin)

lemma pairReducedLeft_lt_pairReducedRight_of_formalUnorderedPair
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) {p : ℕ × ℕ}
    (hp : p ∈ formalUnorderedPairs D) :
    pairReducedLeft p < pairReducedRight p := by
  have hclose := mem_closeDivisorPairs_of_formalUnorderedPair hD hp
  have hg := pairCommon_pos hclose
  apply (Nat.mul_lt_mul_right hg).mp
  rw [pairReducedLeft_mul_pairCommon hclose,
    pairReducedRight_mul_pairCommon hclose]
  exact (mem_formalUnorderedPairs_iff.mp hp).2.2.1

/-- Formal-scale gcd coordinates, with the larger selected member first. -/
def formalGcdCoordinates (p : ℕ × ℕ) : (ℕ × ℕ) × ℕ :=
  gcdCoordinates (swapPair p)

/-- Gcd coordinates retaining the orientation of an ordered formal pair. -/
def formalOrderedGcdCoordinates (p : ℕ × ℕ) : (ℕ × ℕ) × ℕ :=
  gcdCoordinates p

/-- Expanded triples retaining the formal bin of the original products
`dt` and `d't`.  The selected member is `dt`, so the weight is `Omega(dt,2^k)`. -/
def formalExpandedScaleTriples (n k : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((n.divisors.product n.divisors).product n.divisors).filter fun q =>
    q.1.1 * q.2 ≠ q.1.2 * q.2 ∧
      q.1.1 * q.2 < 2 * (q.1.2 * q.2) ∧
      q.1.2 * q.2 < 2 * (q.1.1 * q.2) ∧
      2 ^ k ≤ q.1.1 * q.2 ∧ q.1.1 * q.2 < 2 ^ (k + 1) ∧
      2 ^ k ≤ q.1.2 * q.2 ∧ q.1.2 * q.2 < 2 ^ (k + 1) ∧
      q.1.1 * q.1.2 * q.2 ∣ n

lemma mem_formalExpandedScaleTriples_iff {n k d d' t : ℕ} :
    ((d, d'), t) ∈ formalExpandedScaleTriples n k ↔
      d ∈ n.divisors ∧ d' ∈ n.divisors ∧ t ∈ n.divisors ∧
      d * t ≠ d' * t ∧ d * t < 2 * (d' * t) ∧
      d' * t < 2 * (d * t) ∧
      2 ^ k ≤ d * t ∧ d * t < 2 ^ (k + 1) ∧
      2 ^ k ≤ d' * t ∧ d' * t < 2 ^ (k + 1) ∧ d * d' * t ∣ n := by
  simp [formalExpandedScaleTriples, and_assoc]

noncomputable def formalExpandedScaleMass
    (omegaAtLogScale : ℕ → ℕ → ℕ) (n k : ℕ) : ℝ :=
  ∑ q ∈ formalExpandedScaleTriples n k,
    ((1 : ℝ) / 2) ^ omegaAtLogScale (q.1.1 * q.2) k

/-- Proposition-2 enlargement indexed by the dyadic scale of the smaller
reduced gcd component `d`.  The weight remains on the original selected
divisor `d*t`; coprimality and the original same-bin condition have been
dropped, as permitted by nonnegativity. -/
def reducedFormalExpandedScaleTriples (n k : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  ((n.divisors.product n.divisors).product n.divisors).filter fun q =>
    q.1.1 < q.1.2 ∧
      q.1.1 < 2 * q.1.2 ∧ q.1.2 < 2 * q.1.1 ∧
      2 ^ k ≤ q.1.1 ∧ q.1.1 < 2 ^ (k + 1) ∧
      q.1.1 * q.1.2 * q.2 ∣ n

lemma mem_reducedFormalExpandedScaleTriples_iff {n k d d' t : ℕ} :
    ((d, d'), t) ∈ reducedFormalExpandedScaleTriples n k ↔
      d ∈ n.divisors ∧ d' ∈ n.divisors ∧ t ∈ n.divisors ∧
      d < d' ∧ d < 2 * d' ∧ d' < 2 * d ∧
      2 ^ k ≤ d ∧ d < 2 ^ (k + 1) ∧ d * d' * t ∣ n := by
  simp [reducedFormalExpandedScaleTriples, and_assoc]

noncomputable def reducedFormalExpandedScaleMass
    (omegaAtLogScale : ℕ → ℕ → ℕ) (n k : ℕ) : ℝ :=
  ∑ q ∈ reducedFormalExpandedScaleTriples n k,
    ((1 : ℝ) / 2) ^ omegaAtLogScale (q.1.1 * q.2) k

/-- Every reduced-scale expanded triple automatically satisfies the exact
finite truncation `2^(2k) ≤ n`. -/
lemma two_pow_two_mul_le_of_mem_reducedFormalExpandedScaleTriples
    {n k : ℕ} {q : (ℕ × ℕ) × ℕ}
    (hq : q ∈ reducedFormalExpandedScaleTriples n k) :
    2 ^ (2 * k) ≤ n := by
  rcases q with ⟨⟨d, d'⟩, t⟩
  rcases mem_reducedFormalExpandedScaleTriples_iff.mp hq with
    ⟨hd, hd', ht, hdd', hclose1, hclose2, hk, hkUpper, hdvd⟩
  have hk' : 2 ^ k ≤ d' := hk.trans hdd'.le
  have hpow : 2 ^ (2 * k) ≤ d * d' := by
    rw [show 2 * k = k + k by omega, pow_add]
    exact Nat.mul_le_mul hk hk'
  have htPos := Nat.pos_of_mem_divisors ht
  have hmul : d * d' ≤ d * d' * t := by
    simpa using Nat.mul_le_mul_left (d * d') htPos
  have hnPos : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
  exact hpow.trans (hmul.trans (Nat.le_of_dvd hnPos hdvd))

lemma formalGcdCoordinates_mem_expanded
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) {p : ℕ × ℕ}
    (hp : p ∈ formalPairsInBin D k) :
    formalGcdCoordinates p ∈ formalExpandedScaleTriples n k := by
  have hclose := swap_mem_closeDivisorPairs_of_formalPair hD hp
  rcases mem_formalPairsInBin_iff.mp hp with
    ⟨haD, hbD, haScale, hbScale, hab⟩
  have ha := hD haD
  have hb := hD hbD
  have haPos := Nat.pos_of_mem_divisors ha
  have hbPos := Nat.pos_of_mem_divisors hb
  have haBlock : 2 ^ k ≤ p.1 ∧ p.1 < 2 ^ (k + 1) := by
    rw [← haScale]
    exact ⟨Nat.pow_log_le_self 2 haPos.ne',
      Nat.lt_pow_succ_log_self (by decide) _⟩
  have hbBlock : 2 ^ k ≤ p.2 ∧ p.2 < 2 ^ (k + 1) := by
    rw [← hbScale]
    exact ⟨Nat.pow_log_le_self 2 hbPos.ne',
      Nat.lt_pow_succ_log_self (by decide) _⟩
  have hleft := gcdCoordinates_reconstruct_left hclose
  have hright := gcdCoordinates_reconstruct_right hclose
  rw [mem_formalExpandedScaleTriples_iff]
  refine ⟨pairReducedLeft_mem_divisors hclose,
    pairReducedRight_mem_divisors hclose, pairCommon_mem_divisors hclose, ?_⟩
  simp only [formalGcdCoordinates]
  change
    (gcdCoordinates (swapPair p)).1.1 * (gcdCoordinates (swapPair p)).2 ≠
        (gcdCoordinates (swapPair p)).1.2 * (gcdCoordinates (swapPair p)).2 ∧
      _
  rw [hleft, hright]
  exact ⟨hab.ne', (mem_closeDivisorPairs_iff.mp hclose).2.2.2.1,
    (mem_closeDivisorPairs_iff.mp hclose).2.2.2.2,
    hbBlock.1, hbBlock.2, haBlock.1, haBlock.2,
    reducedProduct_mul_common_dvd hclose⟩

/-- The oriented gcd coordinates land in the same symmetric enlarged sum;
the first reconstructed product is exactly the divisor carrying the weight. -/
lemma formalOrderedGcdCoordinates_mem_expanded
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) {p : ℕ × ℕ}
    (hp : p ∈ formalOrderedPairsInBin D k) :
    formalOrderedGcdCoordinates p ∈ formalExpandedScaleTriples n k := by
  have hclose := mem_closeDivisorPairs_of_formalOrderedPair hD hp
  rcases mem_formalOrderedPairsInBin_iff.mp hp with
    ⟨haD, hbD, haScale, hbScale, hab⟩
  have ha := hD haD
  have hb := hD hbD
  have haPos := Nat.pos_of_mem_divisors ha
  have hbPos := Nat.pos_of_mem_divisors hb
  have haBlock : 2 ^ k ≤ p.1 ∧ p.1 < 2 ^ (k + 1) := by
    rw [← haScale]
    exact ⟨Nat.pow_log_le_self 2 haPos.ne',
      Nat.lt_pow_succ_log_self (by decide) _⟩
  have hbBlock : 2 ^ k ≤ p.2 ∧ p.2 < 2 ^ (k + 1) := by
    rw [← hbScale]
    exact ⟨Nat.pow_log_le_self 2 hbPos.ne',
      Nat.lt_pow_succ_log_self (by decide) _⟩
  have hleft := gcdCoordinates_reconstruct_left hclose
  have hright := gcdCoordinates_reconstruct_right hclose
  rw [mem_formalExpandedScaleTriples_iff]
  refine ⟨pairReducedLeft_mem_divisors hclose,
    pairReducedRight_mem_divisors hclose, pairCommon_mem_divisors hclose, ?_⟩
  simp only [formalOrderedGcdCoordinates]
  change
    (gcdCoordinates p).1.1 * (gcdCoordinates p).2 ≠
        (gcdCoordinates p).1.2 * (gcdCoordinates p).2 ∧ _
  rw [hleft, hright]
  exact ⟨hab, (mem_closeDivisorPairs_iff.mp hclose).2.2.2.1,
    (mem_closeDivisorPairs_iff.mp hclose).2.2.2.2,
    haBlock.1, haBlock.2, hbBlock.1, hbBlock.2,
    reducedProduct_mul_common_dvd hclose⟩

lemma gcdCoordinates_mem_reducedFormalExpanded
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) {p : ℕ × ℕ}
    (hp : p ∈ reducedFormalPairsAtScale D k) :
    gcdCoordinates p ∈ reducedFormalExpandedScaleTriples n k := by
  rcases mem_reducedFormalPairsAtScale_iff.mp hp with ⟨hpFormal, hscale⟩
  have hclose := mem_closeDivisorPairs_of_formalUnorderedPair hD hpFormal
  have hdPos := pairReducedLeft_pos hclose
  have hblock : 2 ^ k ≤ pairReducedLeft p ∧
      pairReducedLeft p < 2 ^ (k + 1) := by
    rw [← hscale]
    exact ⟨Nat.pow_log_le_self 2 hdPos.ne',
      Nat.lt_pow_succ_log_self (by decide) _⟩
  rw [mem_reducedFormalExpandedScaleTriples_iff]
  refine ⟨pairReducedLeft_mem_divisors hclose,
    pairReducedRight_mem_divisors hclose, pairCommon_mem_divisors hclose,
    pairReducedLeft_lt_pairReducedRight_of_formalUnorderedPair hD hpFormal,
    (pairReduced_close hclose).2.1, (pairReduced_close hclose).2.2,
    hblock.1, hblock.2, reducedProduct_mul_common_dvd hclose⟩

lemma gcdCoordinates_injOn_reducedFormalPairsAtScale
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) :
    Set.InjOn gcdCoordinates
      (reducedFormalPairsAtScale D k : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  exact gcdCoordinates_injOn n
    (mem_closeDivisorPairs_of_formalUnorderedPair hD
      (mem_reducedFormalPairsAtScale_iff.mp hp).1)
    (mem_closeDivisorPairs_of_formalUnorderedPair hD
      (mem_reducedFormalPairsAtScale_iff.mp hq).1) heq

lemma reducedFormalPairScale_lt_left
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) {p : ℕ × ℕ}
    (hp : p ∈ formalUnorderedPairs D) :
    reducedFormalPairScale p < p.1 := by
  have hclose := mem_closeDivisorPairs_of_formalUnorderedPair hD hp
  have hlog : Nat.log 2 (pairReducedLeft p) < pairReducedLeft p :=
    Nat.log_lt_self 2 (pairReducedLeft_pos hclose).ne'
  exact hlog.trans_le (Nat.div_le_self _ _)

lemma formalGcdCoordinates_injOn
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) :
    Set.InjOn formalGcdCoordinates (formalPairsInBin D k : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  have hpclose := swap_mem_closeDivisorPairs_of_formalPair hD hp
  have hqclose := swap_mem_closeDivisorPairs_of_formalPair hD hq
  have hswap : swapPair p = swapPair q :=
    gcdCoordinates_injOn n hpclose hqclose heq
  have := congrArg swapPair hswap
  simpa only [swapPair_swapPair] using this

lemma formalOrderedGcdCoordinates_injOn
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) :
    Set.InjOn formalOrderedGcdCoordinates
      (formalOrderedPairsInBin D k : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  exact gcdCoordinates_injOn n
    (mem_closeDivisorPairs_of_formalOrderedPair hD hp)
    (mem_closeDivisorPairs_of_formalOrderedPair hD hq) heq

noncomputable def formalPairScaleMass
    (omegaAtLogScale : ℕ → ℕ → ℕ) (D : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ p ∈ formalPairsInBin D k,
    ((1 : ℝ) / 2) ^ omegaAtLogScale p.2 k

/-- The symmetric ordered formal-bin mass.  Its weight is on the first
member, matching the `Omega(d*t,2^k)` convention in Proposition 2. -/
noncomputable def formalOrderedPairScaleMass
    (omegaAtLogScale : ℕ → ℕ → ℕ) (D : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ p ∈ formalOrderedPairsInBin D k,
    ((1 : ℝ) / 2) ^ omegaAtLogScale p.1 k

/-- Pair mass indexed by the reduced smaller gcd scale, but weighted on the
selected original first divisor. -/
noncomputable def reducedFormalPairScaleMass
    (omegaAtLogScale : ℕ → ℕ → ℕ) (D : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ p ∈ reducedFormalPairsAtScale D k,
    ((1 : ℝ) / 2) ^ omegaAtLogScale p.1 k

/-- Gcd expansion at a fixed formal scale. -/
theorem formalPairScaleMass_le_expandedScaleMass
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (omegaAtLogScale : ℕ → ℕ → ℕ) :
    formalPairScaleMass omegaAtLogScale D k ≤
      formalExpandedScaleMass omegaAtLogScale n k := by
  classical
  let I := (formalPairsInBin D k).image formalGcdCoordinates
  have hinj := formalGcdCoordinates_injOn (n := n) (k := k) hD
  have hrewrite : formalPairScaleMass omegaAtLogScale D k =
      ∑ q ∈ I, ((1 : ℝ) / 2) ^
        omegaAtLogScale (q.1.1 * q.2) k := by
    unfold formalPairScaleMass
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      have hclose := swap_mem_closeDivisorPairs_of_formalPair hD hp
      simp only [formalGcdCoordinates]
      rw [gcdCoordinates_reconstruct_left hclose]
      rfl
    · exact hinj
  rw [hrewrite]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact formalGcdCoordinates_mem_expanded hD hp
  · intro q hq hnot
    positivity

/-- Gcd expansion of both orientations at a fixed formal scale. -/
theorem formalOrderedPairScaleMass_le_expandedScaleMass
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (omegaAtLogScale : ℕ → ℕ → ℕ) :
    formalOrderedPairScaleMass omegaAtLogScale D k ≤
      formalExpandedScaleMass omegaAtLogScale n k := by
  classical
  let I := (formalOrderedPairsInBin D k).image formalOrderedGcdCoordinates
  have hinj := formalOrderedGcdCoordinates_injOn (n := n) (k := k) hD
  have hrewrite : formalOrderedPairScaleMass omegaAtLogScale D k =
      ∑ q ∈ I, ((1 : ℝ) / 2) ^
        omegaAtLogScale (q.1.1 * q.2) k := by
    unfold formalOrderedPairScaleMass
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      have hclose := mem_closeDivisorPairs_of_formalOrderedPair hD hp
      simp only [formalOrderedGcdCoordinates]
      rw [gcdCoordinates_reconstruct_left hclose]
    · exact hinj
  rw [hrewrite]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact formalOrderedGcdCoordinates_mem_expanded hD hp
  · intro q hq hnot
    positivity

/-- Reduced-scale gcd expansion with exact weight `Omega(d*t,2^k)`. -/
theorem reducedFormalPairScaleMass_le_expandedScaleMass
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (omegaAtLogScale : ℕ → ℕ → ℕ) :
    reducedFormalPairScaleMass omegaAtLogScale D k ≤
      reducedFormalExpandedScaleMass omegaAtLogScale n k := by
  classical
  let I := (reducedFormalPairsAtScale D k).image gcdCoordinates
  have hinj := gcdCoordinates_injOn_reducedFormalPairsAtScale
    (n := n) (k := k) hD
  have hrewrite : reducedFormalPairScaleMass omegaAtLogScale D k =
      ∑ q ∈ I, ((1 : ℝ) / 2) ^
        omegaAtLogScale (q.1.1 * q.2) k := by
    unfold reducedFormalPairScaleMass
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      have hpFormal := (mem_reducedFormalPairsAtScale_iff.mp hp).1
      have hclose := mem_closeDivisorPairs_of_formalUnorderedPair hD hpFormal
      rw [gcdCoordinates_reconstruct_left hclose]
    · exact hinj
  rw [hrewrite]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact gcdCoordinates_mem_reducedFormalExpanded hD hp
  · intro q hq hnot
    positivity

noncomputable def formalScaleCoefficient (A : ℝ) (k : ℕ) : ℝ :=
  A * (k : ℝ) ^ (2 / 5 : ℝ)

/-- The only formally exceptional scale. -/
def formalScaleZeroPairTerm (D : Finset ℕ) : ℕ :=
  (formalPairsInBin D 0).card

lemma formalScaleZeroPairTerm_eq_zero
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) :
    formalScaleZeroPairTerm D = 0 := by
  rw [formalScaleZeroPairTerm, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨p, hp⟩
  rcases mem_formalPairsInBin_iff.mp hp with
    ⟨haD, hbD, haScale, hbScale, hab⟩
  have ha := hD haD
  have hb := hD hbD
  have haPos := Nat.pos_of_mem_divisors ha
  have hbPos := Nat.pos_of_mem_divisors hb
  have haUpper := Nat.lt_pow_succ_log_self (b := 2) (by decide) p.1
  have hbUpper := Nat.lt_pow_succ_log_self (b := 2) (by decide) p.2
  rw [haScale] at haUpper
  rw [hbScale] at hbUpper
  norm_num at haUpper hbUpper
  omega

/-- The finite range of formal scales that can contain a divisor `d` with
`d^2 ≤ n`.  This is the lower-half truncation retained after the selector
condition itself is dropped from the enlarged nonnegative sum. -/
def lowerHalfFormalScales (n : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 n + 1)).filter fun k => 2 ^ (2 * k) ≤ n

lemma four_pow_eq_two_pow_two_mul (k : ℕ) :
    4 ^ k = 2 ^ (2 * k) := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]

lemma mem_lowerHalfFormalScales_iff_log_four
    {n k : ℕ} (hn : n ≠ 0) :
    k ∈ lowerHalfFormalScales n ↔ k ≤ Nat.log 4 n := by
  rw [lowerHalfFormalScales, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hkrange, hpow⟩
    apply Nat.le_log_of_pow_le (by decide)
    rwa [four_pow_eq_two_pow_two_mul]
  · intro hk
    have hfour : 4 ^ k ≤ n :=
      (Nat.pow_le_pow_right (by decide : 0 < (4 : ℕ)) hk).trans
        (Nat.pow_log_le_self 4 hn)
    have htwoFour : 2 ^ k ≤ 4 ^ k :=
      Nat.pow_le_pow_left (by norm_num) k
    have hklog : k ≤ Nat.log 2 n :=
      Nat.le_log_of_pow_le (by decide) (htwoFour.trans hfour)
    exact ⟨Nat.lt_succ_of_le hklog, by
      rwa [← four_pow_eq_two_pow_two_mul]⟩

lemma lowerHalfFormalScales_eq_Icc (n : ℕ) (hn : n ≠ 0) :
    lowerHalfFormalScales n = Finset.Icc 0 (Nat.log 4 n) := by
  ext k
  rw [mem_lowerHalfFormalScales_iff_log_four hn]
  simp

lemma Icc_zero_eq_insert_Icc_one (M : ℕ) :
    Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
  ext k
  simp
  omega

lemma formalScale_mem_lowerHalfFormalScales
    {n d k : ℕ} (hd : d ∈ n.divisors) (hscale : Nat.log 2 d = k)
    (hlowerHalf : d * d ≤ n) :
    k ∈ lowerHalfFormalScales n := by
  have hdPos := Nat.pos_of_mem_divisors hd
  have hpow : 2 ^ k ≤ d := by
    rw [← hscale]
    exact Nat.pow_log_le_self 2 hdPos.ne'
  have hsq : 2 ^ (2 * k) ≤ n := by
    rw [show 2 * k = k + k by omega, pow_add]
    exact (Nat.mul_le_mul hpow hpow).trans hlowerHalf
  have hklog : k ≤ Nat.log 2 n := by
    rw [← hscale]
    exact Nat.log_mono_right (Nat.divisor_le hd)
  rw [lowerHalfFormalScales, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hklog, hsq⟩

lemma formalScaleImage_subset_lowerHalfFormalScales
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (hlowerHalf : ∀ d ∈ D, d * d ≤ n) :
    D.image (Nat.log 2) ⊆ lowerHalfFormalScales n := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨d, hd, rfl⟩
  exact formalScale_mem_lowerHalfFormalScales (hD hd) rfl (hlowerHalf d hd)

/-- Zero-tail statement on the authoritative reduced scale: it uses only
gcd factorization and divisibility, with no lower-half selector. -/
lemma reducedFormalPairScaleImage_subset_lowerHalfFormalScales
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) :
    (formalUnorderedPairs D).image reducedFormalPairScale ⊆
      lowerHalfFormalScales n := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
  have hAtScale : p ∈
      reducedFormalPairsAtScale D (reducedFormalPairScale p) :=
    mem_reducedFormalPairsAtScale_iff.mpr ⟨hp, rfl⟩
  have hq := gcdCoordinates_mem_reducedFormalExpanded hD hAtScale
  have hpow :=
    two_pow_two_mul_le_of_mem_reducedFormalExpandedScaleTriples hq
  have hclose := mem_closeDivisorPairs_of_formalUnorderedPair hD hp
  have hklog : reducedFormalPairScale p ≤ Nat.log 2 n := by
    unfold reducedFormalPairScale
    exact Nat.log_mono_right
      (Nat.divisor_le (pairReducedLeft_mem_divisors hclose))
  rw [lowerHalfFormalScales, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hklog, hpow⟩

/-- The dyadic summand after the exceptional `k=0` fibre has been removed. -/
noncomputable def positiveFormalScaleSummand
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (n k : ℕ) : ℝ :=
  if k = 0 then 0 else
    formalScaleCoefficient A k * formalExpandedScaleMass omegaAtLogScale n k

lemma positiveFormalScaleSummand_nonneg
    (omegaAtLogScale : ℕ → ℕ → ℕ) {A : ℝ} (hA : 0 ≤ A)
    (n k : ℕ) :
    0 ≤ positiveFormalScaleSummand omegaAtLogScale A n k := by
  rw [positiveFormalScaleSummand]
  split_ifs
  · exact le_rfl
  · apply mul_nonneg
    · exact mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · unfold formalExpandedScaleMass
      positivity

/-- Consumer interface for the natural-grid selector's pointwise weight
theorem. -/
def FormalBinWeightProperty
    (selected : ℕ → Prop) (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) : Prop :=
  ∀ d k, selected d → Nat.log 2 d = k → 0 < k →
    (1 : ℝ) ≤ formalScaleCoefficient A k *
      ((1 : ℝ) / 2) ^ omegaAtLogScale d k

/-- Dynamic version of the pointwise weight interface.  The selector may
depend on the ambient integer; the lower-half condition is deliberately not
part of this interface. -/
def DynamicFormalBinWeightProperty
    (P : ℕ → ℕ → Prop) (omegaAtLogScale : ℕ → ℕ → ℕ)
    (A : ℝ) : Prop :=
  ∀ n d k, P n d → Nat.log 2 d = k → 0 < k →
    (1 : ℝ) ≤ formalScaleCoefficient A k *
      ((1 : ℝ) / 2) ^ omegaAtLogScale d k

/-- Pointwise interface for NaturalGrid's arbitrary-scale theorem.  The
selected original divisor need not have formal scale `k`; only `k < d` is
required. -/
def ReducedFormalBinWeightProperty
    (selected : ℕ → Prop) (omegaAtLogScale : ℕ → ℕ → ℕ)
    (A : ℝ) : Prop :=
  ∀ d k, selected d → 0 < k → k < d →
    (1 : ℝ) ≤ formalScaleCoefficient A k *
      ((1 : ℝ) / 2) ^ omegaAtLogScale d k

/-- The finite exceptional reduced scale. -/
def reducedFormalScaleZeroPairTerm (D : Finset ℕ) : ℕ :=
  (reducedFormalPairsAtScale D 0).card

lemma reducedFormalScaleZeroPairTerm_eq_zero
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors) :
    reducedFormalScaleZeroPairTerm D = 0 := by
  rw [reducedFormalScaleZeroPairTerm, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨p, hp⟩
  rcases mem_reducedFormalPairsAtScale_iff.mp hp with
    ⟨hpFormal, hscale⟩
  have hclose := mem_closeDivisorPairs_of_formalUnorderedPair hD hpFormal
  have hdPos := pairReducedLeft_pos hclose
  have hdlt : pairReducedLeft p < 2 := by
    apply (Nat.log_eq_zero_iff.mp ?_).resolve_right
    · exact (by decide)
    · simpa [reducedFormalPairScale] using hscale
  have hdd' := pairReducedLeft_lt_pairReducedRight_of_formalUnorderedPair
    hD hpFormal
  have hclose' := (pairReduced_close hclose).2.2
  omega

/-- The definitive reduced-scale summand after proving the zero fibre empty.
It is independent of the selected divisor set. -/
noncomputable def reducedPositiveFormalScaleSummand
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ)
    (n k : ℕ) : ℝ :=
  if k = 0 then 0 else
    formalScaleCoefficient A k *
      reducedFormalExpandedScaleMass omegaAtLogScale n k

lemma reducedPositiveFormalScaleSummand_nonneg
    (omegaAtLogScale : ℕ → ℕ → ℕ) {A : ℝ} (hA : 0 ≤ A)
    (n k : ℕ) :
    0 ≤ reducedPositiveFormalScaleSummand omegaAtLogScale A n k := by
  rw [reducedPositiveFormalScaleSummand]
  split_ifs
  · exact le_rfl
  · apply mul_nonneg
    · exact mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · unfold reducedFormalExpandedScaleMass
      positivity

/-- Reduced-scale Proposition-2 summand, with `k=0` kept as an explicit
finite cardinality term. -/
noncomputable def reducedFormalScaleSummand
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ)
    (D : Finset ℕ) (n k : ℕ) : ℝ :=
  if k = 0 then (reducedFormalScaleZeroPairTerm D : ℝ) else
    formalScaleCoefficient A k *
      reducedFormalExpandedScaleMass omegaAtLogScale n k

lemma reducedFormalScaleSummand_eq_positive
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (k : ℕ) :
    reducedFormalScaleSummand omegaAtLogScale A D n k =
      reducedPositiveFormalScaleSummand omegaAtLogScale A n k := by
  by_cases hk : k = 0
  · subst k
    simp [reducedFormalScaleSummand, reducedPositiveFormalScaleSummand,
      reducedFormalScaleZeroPairTerm_eq_zero hD]
  · simp [reducedFormalScaleSummand, reducedPositiveFormalScaleSummand, hk]

lemma sum_lowerHalf_reducedPositiveFormalScaleSummand_eq_Icc
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ)
    {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ lowerHalfFormalScales n,
        reducedPositiveFormalScaleSummand omegaAtLogScale A n k =
      ∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
        formalScaleCoefficient A k *
          reducedFormalExpandedScaleMass omegaAtLogScale n k := by
  rw [lowerHalfFormalScales_eq_Icc n hn, Icc_zero_eq_insert_Icc_one,
    Finset.sum_insert]
  · simp only [reducedPositiveFormalScaleSummand, if_pos, Nat.cast_zero,
      zero_add]
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by simp at hk; omega
    rw [if_neg hk0]
  · simp

lemma reducedFormalScaleSummand_nonneg
    (omegaAtLogScale : ℕ → ℕ → ℕ) {A : ℝ} (hA : 0 ≤ A)
    (D : Finset ℕ) (n k : ℕ) :
    0 ≤ reducedFormalScaleSummand omegaAtLogScale A D n k := by
  rw [reducedFormalScaleSummand]
  split_ifs
  · positivity
  · apply mul_nonneg
    · exact mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · unfold reducedFormalExpandedScaleMass
      positivity

/-- Divisors satisfying both the dynamic regularity predicate and the
lower-half cutoff. -/
noncomputable def dynamicLowerHalfSelectedDivisors
    (P : ℕ → ℕ → Prop) (n : ℕ) : Finset ℕ := by
  classical
  exact n.divisors.filter fun d => P n d ∧ d * d ≤ n

lemma dynamicLowerHalfSelectedDivisors_subset
    (P : ℕ → ℕ → Prop) (n : ℕ) :
    dynamicLowerHalfSelectedDivisors P n ⊆ n.divisors := by
  classical
  exact Finset.filter_subset _ _

lemma mem_dynamicLowerHalfSelectedDivisors_iff
    {P : ℕ → ℕ → Prop} {n d : ℕ} :
    d ∈ dynamicLowerHalfSelectedDivisors P n ↔
      d ∈ n.divisors ∧ P n d ∧ d * d ≤ n := by
  classical
  simp [dynamicLowerHalfSelectedDivisors, and_assoc]

/-- At each positive formal scale, the selected unordered pairs are
dominated by the Rankin-weighted gcd-expanded `f_k`. -/
theorem card_formalPairsInBin_le_weighted_expandedScale
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : FormalBinWeightProperty selected omegaAtLogScale A)
    (hk : 0 < k) :
    ((formalPairsInBin D k).card : ℝ) ≤
      formalScaleCoefficient A k *
        formalExpandedScaleMass omegaAtLogScale n k := by
  have hpair : ((formalPairsInBin D k).card : ℝ) ≤
      formalScaleCoefficient A k * formalPairScaleMass omegaAtLogScale D k := by
    rw [show ((formalPairsInBin D k).card : ℝ) =
      ∑ _p ∈ formalPairsInBin D k, (1 : ℝ) by simp]
    unfold formalPairScaleMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rcases mem_formalPairsInBin_iff.mp hp with
      ⟨haD, hbD, haScale, hbScale, hab⟩
    exact hweight p.2 k (hselected p.2 hbD) hbScale hk
  calc
    ((formalPairsInBin D k).card : ℝ) ≤
        formalScaleCoefficient A k * formalPairScaleMass omegaAtLogScale D k := hpair
    _ ≤ formalScaleCoefficient A k *
          formalExpandedScaleMass omegaAtLogScale n k := by
      apply mul_le_mul_of_nonneg_left
        (formalPairScaleMass_le_expandedScaleMass hD omegaAtLogScale)
      exact mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The two orientations are simultaneously dominated at a positive scale.
This is the version that preserves the factor two from the off-diagonal
Cauchy energy and ultimately changes `5/2` into `5/4`. -/
theorem card_formalOrderedPairsInBin_le_weighted_expandedScale
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : FormalBinWeightProperty selected omegaAtLogScale A)
    (hk : 0 < k) :
    ((formalOrderedPairsInBin D k).card : ℝ) ≤
      formalScaleCoefficient A k *
        formalExpandedScaleMass omegaAtLogScale n k := by
  have hpair : ((formalOrderedPairsInBin D k).card : ℝ) ≤
      formalScaleCoefficient A k *
        formalOrderedPairScaleMass omegaAtLogScale D k := by
    rw [show ((formalOrderedPairsInBin D k).card : ℝ) =
      ∑ _p ∈ formalOrderedPairsInBin D k, (1 : ℝ) by simp]
    unfold formalOrderedPairScaleMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rcases mem_formalOrderedPairsInBin_iff.mp hp with
      ⟨haD, hbD, haScale, hbScale, hab⟩
    exact hweight p.1 k (hselected p.1 haD) haScale hk
  calc
    ((formalOrderedPairsInBin D k).card : ℝ) ≤
        formalScaleCoefficient A k *
          formalOrderedPairScaleMass omegaAtLogScale D k := hpair
    _ ≤ formalScaleCoefficient A k *
          formalExpandedScaleMass omegaAtLogScale n k := by
      apply mul_le_mul_of_nonneg_left
        (formalOrderedPairScaleMass_le_expandedScaleMass hD omegaAtLogScale)
      exact mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Positive reduced scales are controlled by the arbitrary-scale
NaturalGrid weight and the gcd-expanded mass. -/
theorem card_reducedFormalPairsAtScale_le_weighted_expandedScale
    {n k : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : ReducedFormalBinWeightProperty selected omegaAtLogScale A)
    (hk : 0 < k) :
    ((reducedFormalPairsAtScale D k).card : ℝ) ≤
      formalScaleCoefficient A k *
        reducedFormalExpandedScaleMass omegaAtLogScale n k := by
  have hpair : ((reducedFormalPairsAtScale D k).card : ℝ) ≤
      formalScaleCoefficient A k *
        reducedFormalPairScaleMass omegaAtLogScale D k := by
    rw [show ((reducedFormalPairsAtScale D k).card : ℝ) =
      ∑ _p ∈ reducedFormalPairsAtScale D k, (1 : ℝ) by simp]
    unfold reducedFormalPairScaleMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rcases mem_reducedFormalPairsAtScale_iff.mp hp with
      ⟨hpFormal, hscale⟩
    have hkleft : k < p.1 := by
      rw [← hscale]
      exact reducedFormalPairScale_lt_left hD hpFormal
    exact hweight p.1 k
      (hselected p.1 (mem_formalUnorderedPairs_iff.mp hpFormal).1)
      hk hkleft
  calc
    ((reducedFormalPairsAtScale D k).card : ℝ) ≤
        formalScaleCoefficient A k *
          reducedFormalPairScaleMass omegaAtLogScale D k := hpair
    _ ≤ formalScaleCoefficient A k *
          reducedFormalExpandedScaleMass omegaAtLogScale n k := by
      apply mul_le_mul_of_nonneg_left
        (reducedFormalPairScaleMass_le_expandedScaleMass hD omegaAtLogScale)
      exact mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Formal-bin Proposition 2, before normalization.  The `k=0` term is
displayed explicitly; for divisor sets it is proved to vanish above. -/
theorem selectedDyadicUnorderedPairCount_le_formalExpandedScaleSum
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : FormalBinWeightProperty selected omegaAtLogScale A) :
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
      ∑ k ∈ D.image (Nat.log 2),
        if k = 0 then (formalScaleZeroPairTerm D : ℝ)
        else formalScaleCoefficient A k *
          formalExpandedScaleMass omegaAtLogScale n k := by
  rw [selectedDyadicUnorderedPairCount_eq_formalPairCards]
  push_cast
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [formalScaleZeroPairTerm]
  · rw [if_neg hk0]
    exact card_formalPairsInBin_le_weighted_expandedScale
      hD selected hselected omegaAtLogScale A hA hweight (Nat.pos_of_ne_zero hk0)

/-- Symmetric ordered Proposition 2 in the exact normalization required by
the finite Cauchy theorem. -/
theorem two_mul_selectedDyadicUnorderedPairCount_le_formalExpandedScaleSum
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : FormalBinWeightProperty selected omegaAtLogScale A) :
    (2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
      ∑ k ∈ D.image (Nat.log 2),
        if k = 0 then (2 * formalScaleZeroPairTerm D : ℝ)
        else formalScaleCoefficient A k *
          formalExpandedScaleMass omegaAtLogScale n k := by
  calc
    (2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) =
        (((2 * Erdos448.selectedDyadicUnorderedPairCount D : ℕ)) : ℝ) := by
      norm_num
    _ = ∑ k ∈ D.image (Nat.log 2),
          ((formalOrderedPairsInBin D k).card : ℝ) := by
      rw [two_mul_selectedDyadicUnorderedPairCount_eq_orderedPairCards]
      push_cast
      rfl
    _ ≤ ∑ k ∈ D.image (Nat.log 2),
          if k = 0 then (2 * formalScaleZeroPairTerm D : ℝ)
          else formalScaleCoefficient A k *
            formalExpandedScaleMass omegaAtLogScale n k := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        simp [card_formalOrderedPairsInBin, formalScaleZeroPairTerm]
      · rw [if_neg hk0]
        exact card_formalOrderedPairsInBin_le_weighted_expandedScale
          hD selected hselected omegaAtLogScale A hA hweight
            (Nat.pos_of_ne_zero hk0)

/-! ### Authoritative reduced-scale Proposition-2 wrapper -/

/-- Reindex the selected unordered statistic by the smaller reduced gcd
scale.  Positive scales use the exact `Omega(d*t,2^k)` weight; scale zero is
retained as a finite cardinality term. -/
theorem selectedDyadicUnorderedPairCount_le_reducedScaleImageSum
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : ReducedFormalBinWeightProperty selected omegaAtLogScale A) :
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
      ∑ k ∈ (formalUnorderedPairs D).image reducedFormalPairScale,
        reducedFormalScaleSummand omegaAtLogScale A D n k := by
  rw [selectedDyadicUnorderedPairCount_eq_reducedScalePairCards]
  push_cast
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [reducedFormalScaleSummand, reducedFormalScaleZeroPairTerm]
  · rw [reducedFormalScaleSummand, if_neg hk0]
    exact card_reducedFormalPairsAtScale_le_weighted_expandedScale
      hD selected hselected omegaAtLogScale A hA hweight
        (Nat.pos_of_ne_zero hk0)

/-- Definitive finite Proposition 2: the reduced-scale image has zero tail
outside `2^(2k) ≤ n`, so it may be enlarged to the explicit finite scale
range without retaining the selection predicate. -/
theorem selectedDyadicUnorderedPairCount_le_reducedLowerHalfScaleSum
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : ReducedFormalBinWeightProperty selected omegaAtLogScale A) :
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
      ∑ k ∈ lowerHalfFormalScales n,
        reducedFormalScaleSummand omegaAtLogScale A D n k := by
  calc
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
        ∑ k ∈ (formalUnorderedPairs D).image reducedFormalPairScale,
          reducedFormalScaleSummand omegaAtLogScale A D n k :=
      selectedDyadicUnorderedPairCount_le_reducedScaleImageSum
        hD selected hselected omegaAtLogScale A hA hweight
    _ ≤ ∑ k ∈ lowerHalfFormalScales n,
          reducedFormalScaleSummand omegaAtLogScale A D n k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (reducedFormalPairScaleImage_subset_lowerHalfFormalScales hD)
      intro k hk hnot
      exact reducedFormalScaleSummand_nonneg omegaAtLogScale hA D n k

/-- Consumer form with no selected-set dependence on the right. -/
theorem selectedDyadicUnorderedPairCount_le_reducedPositiveLowerHalfScaleSum
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : ReducedFormalBinWeightProperty selected omegaAtLogScale A) :
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
      ∑ k ∈ lowerHalfFormalScales n,
        reducedPositiveFormalScaleSummand omegaAtLogScale A n k := by
  calc
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
        ∑ k ∈ lowerHalfFormalScales n,
          reducedFormalScaleSummand omegaAtLogScale A D n k :=
      selectedDyadicUnorderedPairCount_le_reducedLowerHalfScaleSum
        hD selected hselected omegaAtLogScale A hA hweight
    _ = ∑ k ∈ lowerHalfFormalScales n,
          reducedPositiveFormalScaleSummand omegaAtLogScale A n k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact reducedFormalScaleSummand_eq_positive hD omegaAtLogScale A k

/-- Final finite Proposition 2 over the exact interval `1 ≤ k ≤ log₄ n`.
The coefficient is visibly `A * k^(2/5)` and the mass is the symmetric-free
gcd enlargement with exact weight on `d*t`. -/
theorem selectedDyadicUnorderedPairCount_le_reducedScaleIccSum
    {n : ℕ} {D : Finset ℕ} (hn : n ≠ 0) (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : ReducedFormalBinWeightProperty selected omegaAtLogScale A) :
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
        formalScaleCoefficient A k *
          reducedFormalExpandedScaleMass omegaAtLogScale n k := by
  calc
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
        ∑ k ∈ lowerHalfFormalScales n,
          reducedPositiveFormalScaleSummand omegaAtLogScale A n k :=
      selectedDyadicUnorderedPairCount_le_reducedPositiveLowerHalfScaleSum
        hD selected hselected omegaAtLogScale A hA hweight
    _ = ∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
          formalScaleCoefficient A k *
            reducedFormalExpandedScaleMass omegaAtLogScale n k :=
      sum_lowerHalf_reducedPositiveFormalScaleSummand_eq_Icc
        omegaAtLogScale A hn

/-- The coefficient-free positive reduced-scale moment. -/
noncomputable def reducedFormalExpandedIccMoment
    (omegaAtLogScale : ℕ → ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
    (k : ℝ) ^ (2 / 5 : ℝ) *
      reducedFormalExpandedScaleMass omegaAtLogScale n k

lemma reducedScaleIccSum_eq_constant_mul
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
      formalScaleCoefficient A k *
        reducedFormalExpandedScaleMass omegaAtLogScale n k) =
      A * reducedFormalExpandedIccMoment omegaAtLogScale n := by
  unfold formalScaleCoefficient reducedFormalExpandedIccMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Proposition 2 in the exact advertised `A * Σ k^(2/5) f_k` form. -/
theorem selectedDyadicUnorderedPairCount_le_constant_mul_reducedIccMoment
    {n : ℕ} {D : Finset ℕ} (hn : n ≠ 0) (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : ReducedFormalBinWeightProperty selected omegaAtLogScale A) :
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
      A * reducedFormalExpandedIccMoment omegaAtLogScale n := by
  calc
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
        ∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
          formalScaleCoefficient A k *
            reducedFormalExpandedScaleMass omegaAtLogScale n k :=
      selectedDyadicUnorderedPairCount_le_reducedScaleIccSum
        hn hD selected hselected omegaAtLogScale A hA hweight
    _ = A * reducedFormalExpandedIccMoment omegaAtLogScale n :=
      reducedScaleIccSum_eq_constant_mul omegaAtLogScale A n

theorem normalizedSelectedDyadicPairs_le_reducedScaleIccSum
    {n : ℕ} {D : Finset ℕ} (hn : n ≠ 0) (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : ReducedFormalBinWeightProperty selected omegaAtLogScale A) :
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) /
        n.divisors.card ≤
      (∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
        formalScaleCoefficient A k *
          reducedFormalExpandedScaleMass omegaAtLogScale n k) /
            n.divisors.card := by
  exact div_le_div_of_nonneg_right
    (selectedDyadicUnorderedPairCount_le_reducedScaleIccSum
      hn hD selected hselected omegaAtLogScale A hA hweight)
    (by positivity)

theorem five_halves_normalizedSelectedPairs_le_reducedScaleIccSum
    {n : ℕ} {D : Finset ℕ} (hn : n ≠ 0) (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : ReducedFormalBinWeightProperty selected omegaAtLogScale A) :
    (5 / 2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) /
        n.divisors.card ≤
      (5 / 2 : ℝ) *
        (∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
          formalScaleCoefficient A k *
            reducedFormalExpandedScaleMass omegaAtLogScale n k) /
              n.divisors.card := by
  have h := normalizedSelectedDyadicPairs_le_reducedScaleIccSum
    hn hD selected hselected omegaAtLogScale A hA hweight
  calc
    (5 / 2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) /
        n.divisors.card =
      (5 / 2 : ℝ) *
        ((Erdos448.selectedDyadicUnorderedPairCount D : ℝ) /
          n.divisors.card) := by ring
    _ ≤ (5 / 2 : ℝ) *
        ((∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
          formalScaleCoefficient A k *
            reducedFormalExpandedScaleMass omegaAtLogScale n k) /
              n.divisors.card) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (5 / 2 : ℝ) *
        (∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
          formalScaleCoefficient A k *
            reducedFormalExpandedScaleMass omegaAtLogScale n k) /
              n.divisors.card := by ring

/-- Normalized statistic delivered directly to the analytic mean-value
argument. -/
theorem normalizedSelectedDyadicPairs_le_reducedLowerHalfScaleSum
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : ReducedFormalBinWeightProperty selected omegaAtLogScale A) :
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) /
        n.divisors.card ≤
      (∑ k ∈ lowerHalfFormalScales n,
        reducedFormalScaleSummand omegaAtLogScale A D n k) /
          n.divisors.card := by
  exact div_le_div_of_nonneg_right
    (selectedDyadicUnorderedPairCount_le_reducedLowerHalfScaleSum
      hD selected hselected omegaAtLogScale A hA hweight)
    (by positivity)

/-- Exact factor matching the close-pair term in `Basic`. -/
theorem five_halves_normalizedSelectedPairs_le_reducedLowerHalfScaleSum
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : ReducedFormalBinWeightProperty selected omegaAtLogScale A) :
    (5 / 2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) /
        n.divisors.card ≤
      (5 / 2 : ℝ) *
        (∑ k ∈ lowerHalfFormalScales n,
          reducedFormalScaleSummand omegaAtLogScale A D n k) /
            n.divisors.card := by
  have h := normalizedSelectedDyadicPairs_le_reducedLowerHalfScaleSum
    hD selected hselected omegaAtLogScale A hA hweight
  calc
    (5 / 2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) /
        n.divisors.card =
      (5 / 2 : ℝ) *
        ((Erdos448.selectedDyadicUnorderedPairCount D : ℝ) /
          n.divisors.card) := by ring
    _ ≤ (5 / 2 : ℝ) *
        ((∑ k ∈ lowerHalfFormalScales n,
          reducedFormalScaleSummand omegaAtLogScale A D n k) /
            n.divisors.card) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (5 / 2 : ℝ) *
        (∑ k ∈ lowerHalfFormalScales n,
          reducedFormalScaleSummand omegaAtLogScale A D n k) /
            n.divisors.card := by ring

/-- If all selected divisors lie in the lower half, only scales satisfying
`2^(2k) ≤ n` remain.  The enlarged summand itself has no lower-half or
selector condition. -/
theorem two_mul_selectedDyadicUnorderedPairCount_le_lowerHalfScaleSum
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (hlowerHalf : ∀ d ∈ D, d * d ≤ n)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : FormalBinWeightProperty selected omegaAtLogScale A) :
    (2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
      ∑ k ∈ lowerHalfFormalScales n,
        positiveFormalScaleSummand omegaAtLogScale A n k := by
  calc
    (2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) ≤
        ∑ k ∈ D.image (Nat.log 2),
          if k = 0 then (2 * formalScaleZeroPairTerm D : ℝ)
          else formalScaleCoefficient A k *
            formalExpandedScaleMass omegaAtLogScale n k :=
      two_mul_selectedDyadicUnorderedPairCount_le_formalExpandedScaleSum
        hD selected hselected omegaAtLogScale A hA hweight
    _ = ∑ k ∈ D.image (Nat.log 2),
          positiveFormalScaleSummand omegaAtLogScale A n k := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        simp [positiveFormalScaleSummand,
          formalScaleZeroPairTerm_eq_zero hD]
      · simp [positiveFormalScaleSummand, hk0]
    _ ≤ ∑ k ∈ lowerHalfFormalScales n,
          positiveFormalScaleSummand omegaAtLogScale A n k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (formalScaleImage_subset_lowerHalfFormalScales hD hlowerHalf)
      intro k hk hnot
      exact positiveFormalScaleSummand_nonneg omegaAtLogScale hA n k

/-- Dynamic-selector specialization.  It selects
`D_n = {d | n : P n d ∧ d^2 ≤ n}`, uses both conditions before the
gcd expansion, and then retains only the scale truncation. -/
theorem dynamicLowerHalfSelectedPairs_le_lowerHalfScaleSum
    (P : ℕ → ℕ → Prop) (omegaAtLogScale : ℕ → ℕ → ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hweight : DynamicFormalBinWeightProperty P omegaAtLogScale A)
    (n : ℕ) :
    (2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount
      (dynamicLowerHalfSelectedDivisors P n) : ℝ) ≤
      ∑ k ∈ lowerHalfFormalScales n,
        positiveFormalScaleSummand omegaAtLogScale A n k := by
  classical
  let D := dynamicLowerHalfSelectedDivisors P n
  have hD : D ⊆ n.divisors := dynamicLowerHalfSelectedDivisors_subset P n
  have hselected : ∀ d ∈ D, P n d := by
    intro d hd
    exact (mem_dynamicLowerHalfSelectedDivisors_iff.mp hd).2.1
  have hlowerHalf : ∀ d ∈ D, d * d ≤ n := by
    intro d hd
    exact (mem_dynamicLowerHalfSelectedDivisors_iff.mp hd).2.2
  apply two_mul_selectedDyadicUnorderedPairCount_le_lowerHalfScaleSum
    hD hlowerHalf (P n) hselected omegaAtLogScale A hA
  intro d k hd hscale hk
  exact hweight n d k hd hscale hk

/-- Normalization by the full divisor count, ready for the analytic mean
estimate. -/
theorem normalizedDynamicLowerHalfSelectedPairs_le_lowerHalfScaleSum
    (P : ℕ → ℕ → Prop) (omegaAtLogScale : ℕ → ℕ → ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hweight : DynamicFormalBinWeightProperty P omegaAtLogScale A)
    (n : ℕ) :
    (2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount
        (dynamicLowerHalfSelectedDivisors P n) : ℝ) /
        n.divisors.card ≤
      (∑ k ∈ lowerHalfFormalScales n,
        positiveFormalScaleSummand omegaAtLogScale A n k) /
          n.divisors.card := by
  exact div_le_div_of_nonneg_right
    (dynamicLowerHalfSelectedPairs_le_lowerHalfScaleSum
      P omegaAtLogScale A hA hweight n)
    (by positivity)

/-- Exact bridge to `Basic.four_fifths_tau_div_tauPlus_le_normalized_closePairs`:
its `(5/2)` times the unordered statistic is bounded by `(5/4)` times the
symmetric expanded formal-bin mass. -/
theorem five_halves_dynamicPairTerm_le_five_fourths_lowerHalfScaleSum
    (P : ℕ → ℕ → Prop) (omegaAtLogScale : ℕ → ℕ → ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hweight : DynamicFormalBinWeightProperty P omegaAtLogScale A)
    (n : ℕ) :
    (5 / 2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount
        (dynamicLowerHalfSelectedDivisors P n) : ℝ) /
        n.divisors.card ≤
      (5 / 4 : ℝ) *
        (∑ k ∈ lowerHalfFormalScales n,
          positiveFormalScaleSummand omegaAtLogScale A n k) /
            n.divisors.card := by
  have h := normalizedDynamicLowerHalfSelectedPairs_le_lowerHalfScaleSum
    P omegaAtLogScale A hA hweight n
  calc
    (5 / 2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount
          (dynamicLowerHalfSelectedDivisors P n) : ℝ) /
          n.divisors.card =
        (5 / 4 : ℝ) *
          ((2 : ℝ) * (Erdos448.selectedDyadicUnorderedPairCount
            (dynamicLowerHalfSelectedDivisors P n) : ℝ) /
              n.divisors.card) := by ring
    _ ≤ (5 / 4 : ℝ) *
          ((∑ k ∈ lowerHalfFormalScales n,
            positiveFormalScaleSummand omegaAtLogScale A n k) /
              n.divisors.card) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (5 / 4 : ℝ) *
          (∑ k ∈ lowerHalfFormalScales n,
            positiveFormalScaleSummand omegaAtLogScale A n k) /
              n.divisors.card := by ring

/-- Normalized wrapper feeding the finite Cauchy theorem directly. -/
theorem normalizedSelectedDyadicPairs_le_formalExpandedScaleSum
    {n : ℕ} {D : Finset ℕ} (hD : D ⊆ n.divisors)
    (selected : ℕ → Prop) (hselected : ∀ d ∈ D, selected d)
    (omegaAtLogScale : ℕ → ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweight : FormalBinWeightProperty selected omegaAtLogScale A) :
    (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) / D.card ≤
      (∑ k ∈ D.image (Nat.log 2),
        if k = 0 then (formalScaleZeroPairTerm D : ℝ)
        else formalScaleCoefficient A k *
          formalExpandedScaleMass omegaAtLogScale n k) / D.card := by
  exact div_le_div_of_nonneg_right
    (selectedDyadicUnorderedPairCount_le_formalExpandedScaleSum
      hD selected hselected omegaAtLogScale A hA hweight)
    (by positivity)

end Erdos448Scratch.Prop2Scale
