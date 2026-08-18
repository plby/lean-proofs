import ErdosProblems.Erdos981.Core
import ErdosProblems.Erdos387.AnalyticInputs
import ErdosProblems.Erdos981.External.Erdos980.NaturalChebotarev.WeightedToCounting

open scoped BigOperators
open Filter Finset Asymptotics

namespace Erdos981

def test_primeResiduePred (q a n : ℕ) : Prop :=
  n.Prime ∧ n % q = a

lemma test_logWeightedCount_succ_eq_thetaAP (q a N : ℕ) :
    Erdos980.NaturalChebotarev.logWeightedCount
        (test_primeResiduePred q a) (N + 1) =
      Erdos387.thetaAP q a (N : ℝ) := by
  classical
  rw [Erdos387.thetaAP_eq_sum_filter]
  unfold Erdos980.NaturalChebotarev.logWeightedCount
  rw [Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Iic,
      Nat.floor_natCast, test_primeResiduePred]
    omega
  · intro n hn
    by_cases h : test_primeResiduePred q a n
    · rw [if_pos h, if_pos (show n.Prime ∧ n % q = a from h)]
    · rw [if_neg h, if_neg (show ¬(n.Prime ∧ n % q = a) from h)]

lemma test_isEquivalent_of_succ
    {f : ℕ → ℝ} {A : ℝ} (hA : 0 < A)
    (h : (fun n : ℕ => f (n + 1)) ~[atTop] (fun n : ℕ => A * (n : ℝ))) :
    f ~[atTop] (fun n : ℕ => A * (n : ℝ)) := by
  have hpred : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro m
    refine ⟨m + 1, ?_⟩
    intro n hn
    omega
  have hcomp := h.comp_tendsto hpred
  have hcomp' : f ~[atTop] (fun n : ℕ => A * ((n - 1 : ℕ) : ℝ)) := by
    apply hcomp.congr'
    · filter_upwards [eventually_ge_atTop 1] with n hn
      simp [hn]
    · exact EventuallyEq.rfl
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hpredRatio : Tendsto
      (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    have honeSub : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ))
        atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hinv
    have heq : (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / (n : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [Nat.cast_sub hn]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      field_simp
      norm_num
    simpa using honeSub.congr' heq
  have htargetNe : ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_ne_zero hA.ne' (by exact_mod_cast (by omega : n ≠ 0))
  have hshift : (fun n : ℕ => A * ((n - 1 : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => A * (n : ℝ)) := by
    rw [isEquivalent_iff_tendsto_one htargetNe]
    apply hpredRatio.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    change ((n - 1 : ℕ) : ℝ) / (n : ℝ) =
      (A * ((n - 1 : ℕ) : ℝ)) / (A * (n : ℝ))
    rw [mul_div_mul_left _ _ hA.ne']
  exact hcomp'.trans hshift

lemma test_primeResidueCount_isEquivalent
    {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) (haq : a < q) :
    (fun N : ℕ =>
      (Erdos980.NaturalChebotarev.predicateCount
        (test_primeResiduePred q a) N : ℝ)) ~[atTop]
      (fun N : ℕ => (1 / (Nat.totient q : ℝ)) *
        (N : ℝ) / Real.log (N : ℝ)) := by
  have hphi : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have htheta := (Erdos387.thetaAP_isEquivalent hq ha haq).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hsucc :
      (fun N : ℕ => Erdos980.NaturalChebotarev.logWeightedCount
        (test_primeResiduePred q a) (N + 1)) ~[atTop]
        (fun N : ℕ => (1 / (Nat.totient q : ℝ)) * (N : ℝ)) := by
    refine (htheta.congr_left ?_).congr_right ?_
    · exact Eventually.of_forall fun N =>
        (test_logWeightedCount_succ_eq_thetaAP q a N).symm
    · exact Eventually.of_forall fun N => by
        simp only [Function.comp_apply, div_eq_mul_inv]
        ring
  have hweighted := test_isEquivalent_of_succ (by positivity) hsucc
  exact Erdos980.NaturalChebotarev.predicateCount_isEquivalent_of_logWeightedCount
    (test_primeResiduePred q a) (by positivity) hweighted

def test_patternModulus (M : ℕ) : ℕ := 4 * M.factorial

lemma test_patternModulus_pos (M : ℕ) : 0 < test_patternModulus M := by
  unfold test_patternModulus
  positivity

lemma test_four_mul_dvd_patternModulus {n M : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    4 * n ∣ test_patternModulus M := by
  unfold test_patternModulus
  exact Nat.mul_dvd_mul_left 4 (Nat.dvd_factorial (by omega) hnM)

lemma test_jacobiSym_eq_of_patternResidue {M p a n : ℕ}
    (hn : 1 ≤ n) (hnM : n ≤ M)
    (hp : p.Coprime (test_patternModulus M))
    (ha : a.Coprime (test_patternModulus M))
    (haQ : a < test_patternModulus M)
    (hpa : p % test_patternModulus M = a) :
    jacobiSym (n : ℤ) p = jacobiSym (n : ℤ) a := by
  let Q := test_patternModulus M
  have hdvd : 4 * n ∣ Q := test_four_mul_dvd_patternModulus hn hnM
  let χ := attachedQuadraticCharacter n Q hdvd
  have hmod : Nat.ModEq Q p a := by
    change p % Q = a % Q
    rw [hpa, Nat.mod_eq_of_lt haQ]
  have hperiod := χ.periodic hmod
  have hχp : χ p = jacobiSym (n : ℤ) p := by
    exact attachedQuadraticCharacter_apply_coprime hdvd hp
  have hχa : χ a = jacobiSym (n : ℤ) a := by
    exact attachedQuadraticCharacter_apply_coprime hdvd ha
  rw [← hχp, ← hχa]
  exact hperiod

lemma test_legendrePartialSum_eq_of_patternResidue {M p a N : ℕ}
    (hN : N ≤ M)
    (hp : p.Coprime (test_patternModulus M))
    (ha : a.Coprime (test_patternModulus M))
    (haQ : a < test_patternModulus M)
    (hpa : p % test_patternModulus M = a) :
    legendrePartialSum p N = legendrePartialSum a N := by
  unfold legendrePartialSum
  apply Finset.sum_congr rfl
  intro k hk
  apply test_jacobiSym_eq_of_patternResidue (M := M) (n := k + 1)
  · omega
  · have hkN := Finset.mem_range.mp hk
    omega
  · exact hp
  · exact ha
  · exact haQ
  · exact hpa

lemma test_truncatedThreshold_eq_of_patternResidue {ε : ℝ} {M p a : ℕ}
    (hp : p.Coprime (test_patternModulus M))
    (ha : a.Coprime (test_patternModulus M))
    (haQ : a < test_patternModulus M)
    (hpa : p % test_patternModulus M = a) :
    truncatedThreshold ε p M = truncatedThreshold ε a M := by
  have hprop : ∀ m, IsTruncatedThreshold ε p M m ↔
      IsTruncatedThreshold ε a M m := by
    intro m
    constructor
    · rintro ⟨hm, hsum⟩
      refine ⟨hm, ?_⟩
      intro N hmN hNM
      rw [← test_legendrePartialSum_eq_of_patternResidue hNM hp ha haQ hpa]
      exact hsum N hmN hNM
    · rintro ⟨hm, hsum⟩
      refine ⟨hm, ?_⟩
      intro N hmN hNM
      rw [test_legendrePartialSum_eq_of_patternResidue hNM hp ha haQ hpa]
      exact hsum N hmN hNM
  apply Nat.le_antisymm
  · apply truncatedThreshold_minimal
    exact (hprop _).mpr (truncatedThreshold_spec ε a M)
  · apply truncatedThreshold_minimal
    exact (hprop _).mp (truncatedThreshold_spec ε p M)

def test_reducedPatternResidues (M : ℕ) : Finset ℕ :=
  (Finset.range (test_patternModulus M)).filter fun a =>
    a.Coprime (test_patternModulus M)

def test_primeResidueFinset (q a x : ℕ) : Finset ℕ :=
  ((Finset.range x).filter Nat.Prime).filter fun p => p % q = a

noncomputable def test_truncatedCoprimePrimeSum (ε : ℝ) (M x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range x).filter (fun p =>
      p.Prime ∧ p.Coprime (test_patternModulus M)),
    (truncatedThreshold ε p M : ℝ)

noncomputable def test_residueTruncatedConstant (ε : ℝ) (M : ℕ) : ℝ :=
  ∑ a ∈ test_reducedPatternResidues M,
    (truncatedThreshold ε a M : ℝ) /
      Nat.totient (test_patternModulus M)

lemma test_primeResidueFinset_card_eq_predicateCount (q a x : ℕ) :
    (test_primeResidueFinset q a x).card =
      Erdos980.NaturalChebotarev.predicateCount
        (test_primeResiduePred q a) x := by
  classical
  unfold test_primeResidueFinset
  unfold Erdos980.NaturalChebotarev.predicateCount
  congr 1
  ext p
  simp [test_primeResiduePred, and_comm, and_left_comm]

lemma test_primeResidueFinset_pairwiseDisjoint (M x : ℕ) :
    Set.PairwiseDisjoint (↑(test_reducedPatternResidues M) : Set ℕ)
      (fun a => test_primeResidueFinset (test_patternModulus M) a x) := by
  classical
  let t := (Finset.range x).filter Nat.Prime
  have h := Set.pairwiseDisjoint_filter
    (fun p : ℕ => p % test_patternModulus M)
    (↑(test_reducedPatternResidues M) : Set ℕ) t
  simpa [t, test_primeResidueFinset] using h

lemma test_biUnion_primeResidueFinset_eq (M x : ℕ) :
    (test_reducedPatternResidues M).biUnion
        (fun a => test_primeResidueFinset (test_patternModulus M) a x) =
      (Finset.range x).filter (fun p =>
        p.Prime ∧ p.Coprime (test_patternModulus M)) := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range,
    test_reducedPatternResidues, test_primeResidueFinset]
  constructor
  · rintro ⟨a, ⟨haQ, haCop⟩, ⟨⟨hpx, hp⟩, hpa⟩⟩
    have hmod : Nat.ModEq (test_patternModulus M) p a := by
      change p % test_patternModulus M = a % test_patternModulus M
      rw [hpa, Nat.mod_eq_of_lt haQ]
    have hgcd := hmod.gcd_eq
    have hpCop : p.Coprime (test_patternModulus M) := by
      rw [Nat.coprime_iff_gcd_eq_one, hgcd]
      exact haCop.gcd_eq_one
    exact ⟨hpx, hp, hpCop⟩
  · rintro ⟨hpx, hp, hpCop⟩
    let a := p % test_patternModulus M
    have haQ : a < test_patternModulus M :=
      Nat.mod_lt p (test_patternModulus_pos M)
    have hmod : Nat.ModEq (test_patternModulus M) p a := by
      change p % test_patternModulus M = a % test_patternModulus M
      simp [a, Nat.mod_eq_of_lt haQ]
    have hgcd := hmod.gcd_eq
    have haCop : a.Coprime (test_patternModulus M) := by
      rw [Nat.coprime_iff_gcd_eq_one, ← hgcd]
      exact hpCop.gcd_eq_one
    exact ⟨a, ⟨haQ, haCop⟩, ⟨⟨hpx, hp⟩, rfl⟩⟩

lemma test_truncatedCoprimePrimeSum_eq_residue_sum
    (ε : ℝ) (M x : ℕ) :
    test_truncatedCoprimePrimeSum ε M x =
      ∑ a ∈ test_reducedPatternResidues M,
        (truncatedThreshold ε a M : ℝ) *
          ((test_primeResidueFinset (test_patternModulus M) a x).card : ℝ) := by
  classical
  let Q := test_patternModulus M
  have hdisj := test_primeResidueFinset_pairwiseDisjoint M x
  rw [test_truncatedCoprimePrimeSum,
    ← test_biUnion_primeResidueFinset_eq M x,
    Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro a ha
  have haData := Finset.mem_filter.mp ha
  have haQ : a < Q := Finset.mem_range.mp haData.1
  have haCop : a.Coprime Q := haData.2
  calc
    ∑ p ∈ test_primeResidueFinset Q a x,
        (truncatedThreshold ε p M : ℝ) =
      ∑ _p ∈ test_primeResidueFinset Q a x,
        (truncatedThreshold ε a M : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpData := Finset.mem_filter.mp hp
          have hpPrimeData := Finset.mem_filter.mp hpData.1
          have hpa := hpData.2
          have hmod : Nat.ModEq Q p a := by
            change p % Q = a % Q
            rw [hpa, Nat.mod_eq_of_lt haQ]
          have hpCop : p.Coprime Q := by
            rw [Nat.coprime_iff_gcd_eq_one, hmod.gcd_eq]
            exact haCop.gcd_eq_one
          exact_mod_cast test_truncatedThreshold_eq_of_patternResidue
            hpCop haCop haQ hpa
    _ = (truncatedThreshold ε a M : ℝ) *
        ((test_primeResidueFinset Q a x).card : ℝ) := by
      simp [mul_comm]

noncomputable def test_pntScale (x : ℕ) : ℝ :=
  (x : ℝ) / Real.log (x : ℝ)

lemma test_eventually_pntScale_pos :
    ∀ᶠ x : ℕ in atTop, 0 < test_pntScale x := by
  filter_upwards [eventually_ge_atTop 2] with x hx
  unfold test_pntScale
  exact div_pos (by exact_mod_cast (by omega : 0 < x))
    (Real.log_pos (by exact_mod_cast hx))

lemma test_tendsto_normalized_of_const_mul_isEquivalent
    {f scale : ℕ → ℝ} {d : ℝ} (hd : 0 < d)
    (hscale : ∀ᶠ x : ℕ in atTop, 0 < scale x)
    (h : f ~[atTop] (fun x => d * scale x)) :
    Tendsto (fun x => f x / scale x) atTop (nhds d) := by
  have htargetNe : ∀ᶠ x : ℕ in atTop, d * scale x ≠ 0 := by
    filter_upwards [hscale] with x hx
    exact mul_ne_zero hd.ne' hx.ne'
  have hratio : Tendsto (fun x => f x / (d * scale x)) atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one htargetNe).mp h
  have hmul : Tendsto (fun x => d * (f x / (d * scale x)))
      atTop (nhds (d * 1)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => d) atTop (nhds d)).mul hratio
  have heq : (fun x => d * (f x / (d * scale x))) =ᶠ[atTop]
      (fun x => f x / scale x) := by
    filter_upwards [hscale] with x hx
    have hs : scale x ≠ 0 := hx.ne'
    field_simp [hd.ne', hs]
  simpa using hmul.congr' heq

lemma test_primeResidueFinset_normalized_tendsto
    {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) (haq : a < q) :
    Tendsto
      (fun x => ((test_primeResidueFinset q a x).card : ℝ) / test_pntScale x)
      atTop (nhds (1 / (Nat.totient q : ℝ))) := by
  have hequiv := test_primeResidueCount_isEquivalent hq ha haq
  have hequiv' :
      (fun x => ((test_primeResidueFinset q a x).card : ℝ)) ~[atTop]
        (fun x => (1 / (Nat.totient q : ℝ)) * test_pntScale x) := by
    refine (hequiv.congr_left ?_).congr_right ?_
    · exact Eventually.of_forall fun x => by
        change (Erdos980.NaturalChebotarev.predicateCount
          (test_primeResiduePred q a) x : ℝ) =
            ((test_primeResidueFinset q a x).card : ℝ)
        exact_mod_cast (test_primeResidueFinset_card_eq_predicateCount q a x).symm
    · exact Eventually.of_forall fun x => by
        unfold test_pntScale
        ring
  apply test_tendsto_normalized_of_const_mul_isEquivalent
    (by
      have hphi : (0 : ℝ) < Nat.totient q := by
        exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
      positivity)
    test_eventually_pntScale_pos hequiv'

lemma test_truncatedCoprimePrimeSum_normalized_tendsto
    (ε : ℝ) (M : ℕ) :
    Tendsto (fun x => test_truncatedCoprimePrimeSum ε M x / test_pntScale x)
      atTop (nhds (test_residueTruncatedConstant ε M)) := by
  let Q := test_patternModulus M
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (test_patternModulus_pos M))
  have hterms : ∀ a ∈ test_reducedPatternResidues M,
      Tendsto
        (fun x => (truncatedThreshold ε a M : ℝ) *
          ((test_primeResidueFinset Q a x).card : ℝ) / test_pntScale x)
        atTop
        (nhds ((truncatedThreshold ε a M : ℝ) /
          Nat.totient Q)) := by
    intro a ha
    have haData := Finset.mem_filter.mp ha
    have haQ : a < Q := Finset.mem_range.mp haData.1
    have haCop : a.Coprime Q := haData.2
    have hcount := test_primeResidueFinset_normalized_tendsto hQ haCop haQ
    have hmul : Tendsto
        (fun x => (truncatedThreshold ε a M : ℝ) *
          (((test_primeResidueFinset Q a x).card : ℝ) / test_pntScale x))
        atTop
        (nhds ((truncatedThreshold ε a M : ℝ) *
          (1 / (Nat.totient Q : ℝ)))) :=
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (truncatedThreshold ε a M : ℝ)) atTop
          (nhds (truncatedThreshold ε a M : ℝ))).mul hcount
    simpa only [div_eq_mul_inv, mul_assoc, one_mul] using hmul
  have hsum := tendsto_finsetSum (test_reducedPatternResidues M) hterms
  apply hsum.congr'
  exact Eventually.of_forall fun x => by
    dsimp only
    dsimp [Q]
    rw [test_truncatedCoprimePrimeSum_eq_residue_sum]
    simp only [Finset.sum_div]

noncomputable def test_truncatedOddPrimeSum (ε : ℝ) (M x : ℕ) : ℝ :=
  ∑ p ∈ oddPrimesBelow x, (truncatedThreshold ε p M : ℝ)

noncomputable def test_exceptionalTruncatedPrimeSum (ε : ℝ) (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (test_patternModulus M + 1)).filter (fun p =>
      p.Prime ∧ Odd p ∧ ¬p.Coprime (test_patternModulus M)),
    (truncatedThreshold ε p M : ℝ)

lemma test_truncatedOddPrimeSum_eq_coprime_add_exceptional
    (ε : ℝ) (M : ℕ) {x : ℕ} (hx : test_patternModulus M + 1 ≤ x) :
    test_truncatedOddPrimeSum ε M x =
      test_truncatedCoprimePrimeSum ε M x +
        test_exceptionalTruncatedPrimeSum ε M := by
  classical
  let Q := test_patternModulus M
  let good := (Finset.range x).filter fun p => p.Prime ∧ p.Coprime Q
  let bad := (Finset.range x).filter fun p => p.Prime ∧ Odd p ∧ ¬p.Coprime Q
  let exceptional := (Finset.range (Q + 1)).filter fun p =>
    p.Prime ∧ Odd p ∧ ¬p.Coprime Q
  have hbad : bad = exceptional := by
    ext p
    simp only [bad, exceptional, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hpx, hp, hpodd, hpnot⟩
      have hpdvd : p ∣ Q := by
        rw [hp.coprime_iff_not_dvd] at hpnot
        exact Classical.byContradiction hpnot
      have hpQ : p ≤ Q := Nat.le_of_dvd (test_patternModulus_pos M) hpdvd
      exact ⟨by omega, hp, hpodd, hpnot⟩
    · rintro ⟨hpQ, hp, hpodd, hpnot⟩
      exact ⟨by omega, hp, hpodd, hpnot⟩
  have hoddUnion : oddPrimesBelow x = good ∪ bad := by
    ext p
    simp only [oddPrimesBelow, good, bad, Finset.mem_filter,
      Finset.mem_range, Finset.mem_union]
    constructor
    · rintro ⟨hpx, hp, hpodd⟩
      by_cases hcop : p.Coprime Q
      · exact Or.inl ⟨hpx, hp, hcop⟩
      · exact Or.inr ⟨hpx, hp, hpodd, hcop⟩
    · rintro (⟨hpx, hp, hcop⟩ | ⟨hpx, hp, hpodd, hcop⟩)
      · have hpodd : Odd p := by
          have h2Q : 2 ∣ Q := by
            dsimp [Q, test_patternModulus]
            exact ⟨2 * M.factorial, by ring⟩
          exact (Nat.coprime_two_right).mp (hcop.coprime_dvd_right h2Q)
        exact ⟨hpx, hp, hpodd⟩
      · exact ⟨hpx, hp, hpodd⟩
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro p hpg hpb
    have hg := (Finset.mem_filter.mp hpg).2.2
    have hb := (Finset.mem_filter.mp hpb).2.2.2
    exact hb hg
  rw [test_truncatedOddPrimeSum, hoddUnion, Finset.sum_union hdisj,
    test_truncatedCoprimePrimeSum, test_exceptionalTruncatedPrimeSum,
    hbad]

lemma test_const_div_pntScale_tendsto_zero (C : ℝ) :
    Tendsto (fun x : ℕ => C / test_pntScale x) atTop (nhds 0) := by
  have hlogdiv : Tendsto
      (fun x : ℕ => Real.log (x : ℝ) / (x : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hmul := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (nhds C)).mul
    hlogdiv
  have heq : (fun x : ℕ => C * (Real.log (x : ℝ) / (x : ℝ))) =ᶠ[atTop]
      (fun x : ℕ => C / test_pntScale x) := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    unfold test_pntScale
    have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
    have hlog0 : Real.log (x : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hx))
    field_simp
  simpa using hmul.congr' heq

lemma test_truncatedOddPrimeSum_normalized_tendsto
    (ε : ℝ) (M : ℕ) :
    Tendsto (fun x => test_truncatedOddPrimeSum ε M x / test_pntScale x)
      atTop (nhds (test_residueTruncatedConstant ε M)) := by
  have hcop := test_truncatedCoprimePrimeSum_normalized_tendsto ε M
  have hexc := test_const_div_pntScale_tendsto_zero
    (test_exceptionalTruncatedPrimeSum ε M)
  have hadd := hcop.add hexc
  have heq : (fun x =>
      test_truncatedCoprimePrimeSum ε M x / test_pntScale x +
        test_exceptionalTruncatedPrimeSum ε M / test_pntScale x) =ᶠ[atTop]
      (fun x => test_truncatedOddPrimeSum ε M x / test_pntScale x) := by
    filter_upwards [eventually_ge_atTop (test_patternModulus M + 1)] with x hx
    rw [← add_div, ← test_truncatedOddPrimeSum_eq_coprime_add_exceptional ε M hx]
  simpa using hadd.congr' heq

end Erdos981
