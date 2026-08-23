/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 771.
https://www.erdosproblems.com/forum/thread/771

Informal authors:
- Noga Alon
- Gregory Freiman

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos771.md
-/
import Mathlib
import PrimeNumberTheoremAnd.Consequences
import ErdosProblems.Erdos469
import ErdosProblems.Erdos38
import ErdosProblems.Erdos285.RoughCounts
import ErdosProblems.Erdos55.FiniteSums
import ErdosProblems.Erdos54.CyclicGrowth
import ErdosProblems.Erdos636.External.Erdos88.Fourier
import ErdosProblems.Erdos387.LocalDensity
import ErdosProblems.Erdos387.UniformAnalyticInputs

/-!
# Erdős Problem 771

The detailed mathematical proof and Leanization map are in tex/771.tex.
-/

open Filter Finset Nat Real
open scoped BigOperators Topology

syntax (name := answerSyntax771) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

namespace Erdos771

noncomputable section

/-- A finite set has no subset whose sum is the positive target m. -/
def AvoidsSubsetSum (m : ℕ) (S : Finset ℕ) : Prop :=
  m ∉ S.subsetSum

/-- The exact quantifier order in Problem 771. -/
def AdmissibleCard (n k : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ S : Finset ℕ,
      S ⊆ Finset.Icc 1 n ∧ S.card = k ∧ AvoidsSubsetSum m S

local instance decidableAdmissibleCard (n : ℕ) : DecidablePred (AdmissibleCard n) :=
  fun _ => Classical.propDecidable _

/-- The largest cardinality that works simultaneously for every positive target. -/
noncomputable def erdosF (n : ℕ) : ℕ :=
  Nat.findGreatest (AdmissibleCard n) n

lemma admissibleCard_zero (n : ℕ) : AdmissibleCard n 0 := by
  intro m hm
  refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
  simpa [AvoidsSubsetSum, Finset.subsetSum] using hm.ne'

lemma erdosF_le (n : ℕ) : erdosF n ≤ n :=
  by simpa [erdosF] using Nat.findGreatest_le n (P := AdmissibleCard n)

lemma erdosF_spec (n : ℕ) : AdmissibleCard n (erdosF n) := by
  exact Nat.findGreatest_spec (m := 0) (Nat.zero_le n) (admissibleCard_zero n)

lemma AdmissibleCard.mono_card {n k l : ℕ}
    (hk : AdmissibleCard n k) (hlk : l ≤ k) :
    AdmissibleCard n l := by
  intro m hm
  obtain ⟨S, hSn, hScard, havoid⟩ := hk m hm
  have hlS : l ≤ S.card := by simpa [hScard] using hlk
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hlS
  refine ⟨T, hTS.trans hSn, hTcard, ?_⟩
  intro hmT
  exact havoid (Finset.subsetSum_mono hTS hmT)

lemma admissibleCard_iff_le_erdosF {n k : ℕ} (hk : k ≤ n) :
    AdmissibleCard n k ↔ k ≤ erdosF n := by
  constructor
  · exact fun h => Nat.le_findGreatest hk h
  · exact fun h => (erdosF_spec n).mono_card h

/-- A criterion for an upper bound: one positive target represented by every
large subset rules out that cardinality in the universal avoidance problem. -/
lemma erdosF_lt_of_all_large_represent {n m k : ℕ} (hm : 0 < m)
    (hrep : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 n → k ≤ S.card →
      m ∈ S.subsetSum) :
    erdosF n < k := by
  by_contra hnot
  have hk : k ≤ erdosF n := Nat.le_of_not_gt hnot
  obtain ⟨S, hSn, hScard, havoid⟩ := erdosF_spec n m hm
  exact havoid (hrep S hSn (by simpa [hScard] using hk))

/-! ## The smallest nondivisor -/

lemma exists_nondivisor (m : ℕ) (hm : 0 < m) :
    ∃ d : ℕ, 0 < d ∧ ¬d ∣ m := by
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  exact Nat.not_dvd_of_pos_of_lt hm (Nat.lt_succ_self m)

/-- The least positive integer which does not divide a positive integer `m`. -/
noncomputable def leastNondivisor (m : ℕ) (hm : 0 < m) : ℕ :=
  Nat.find (exists_nondivisor m hm)

lemma leastNondivisor_spec (m : ℕ) (hm : 0 < m) :
    0 < leastNondivisor m hm ∧ ¬leastNondivisor m hm ∣ m := by
  exact Nat.find_spec (exists_nondivisor m hm)

lemma leastNondivisor_le {m d : ℕ} (hm : 0 < m)
    (hd : 0 < d) (hnd : ¬d ∣ m) :
    leastNondivisor m hm ≤ d := by
  exact Nat.find_min' (exists_nondivisor m hm) ⟨hd, hnd⟩

lemma dvd_of_pos_lt_leastNondivisor {m d : ℕ} (hm : 0 < m)
    (hd : 0 < d) (hds : d < leastNondivisor m hm) : d ∣ m := by
  by_contra hnd
  exact (Nat.find_min (exists_nondivisor m hm) hds) ⟨hd, hnd⟩

lemma two_le_leastNondivisor (m : ℕ) (hm : 0 < m) :
    2 ≤ leastNondivisor m hm := by
  have hone : (1 : ℕ) ∣ m := one_dvd m
  have hne : leastNondivisor m hm ≠ 1 := fun h =>
    (leastNondivisor_spec m hm).2 (h ▸ hone)
  have hpos : 0 < leastNondivisor m hm := (leastNondivisor_spec m hm).1
  omega

/-- The least positive nondivisor is necessarily a prime power. -/
lemma leastNondivisor_isPrimePow (m : ℕ) (hm : 0 < m) :
    IsPrimePow (leastNondivisor m hm) := by
  let s := leastNondivisor m hm
  have hs2 : 2 ≤ s := by simpa [s] using two_le_leastNondivisor m hm
  have hspos : 0 < s := by omega
  have hsne : s ≠ 0 := hspos.ne'
  by_contra hnotpp
  have hsL : s ∣ Nat.lcmUpto (s - 1) := by
    rw [← Nat.factorization_le_iff_dvd hsne (Nat.lcmUpto_ne_zero _)]
    intro p
    by_cases hp : p.Prime
    · rw [Nat.factorization_lcmUpto _ hp]
      have hpowDvd : p ^ (s.factorization p) ∣ s :=
        (hp.pow_dvd_iff_le_factorization hsne).2 le_rfl
      have hfacLog : s.factorization p ≤ p.log s :=
        Nat.le_log_of_pow_le hp.one_lt (Nat.le_of_dvd hspos hpowDvd)
      have hlogEq : p.log (s - 1) = p.log s := by
        have hsPred : s - 1 ≠ 0 := by omega
        have hsSucc : s - 1 + 1 = s := by omega
        rw [← hsSucc]
        apply (Nat.log_eq_log_succ_iff hp.one_lt hsPred).2
        rw [hsSucc]
        intro hpowEq
        apply hnotpp
        apply (isPrimePow_nat_iff s).2
        refine ⟨p, p.log s, hp, ?_, hpowEq⟩
        by_contra hzero
        have hz : p.log s = 0 := Nat.eq_zero_of_not_pos hzero
        rw [hz] at hpowEq
        simp at hpowEq
        omega
      rw [hlogEq]
      exact hfacLog
    · rw [Nat.factorization_eq_zero_of_not_prime s hp,
        Nat.factorization_eq_zero_of_not_prime (Nat.lcmUpto (s - 1)) hp]
  have hLdvd : Nat.lcmUpto (s - 1) ∣ m := by
    apply Finset.lcm_dvd
    intro d hd
    have hdI := Finset.mem_Icc.mp hd
    have hdlt : d < s := by omega
    exact dvd_of_pos_lt_leastNondivisor hm hdI.1 (by simpa [s] using hdlt)
  exact (leastNondivisor_spec m hm).2 (by
    simpa [s] using hsL.trans hLdvd)

/-! ## Maximal lcm cutoffs -/

/-- The largest `r ≤ X` for which `lcm(1,...,r) ≤ X`. -/
def lcmCutoff (X : ℕ) : ℕ :=
  Nat.findGreatest (fun r => Nat.lcmUpto r ≤ X) X

lemma lcmCutoff_le (X : ℕ) : lcmCutoff X ≤ X := by
  exact Nat.findGreatest_le X

lemma dvd_lcmUpto {d r : ℕ} (hd : 0 < d) (hdr : d ≤ r) :
    d ∣ Nat.lcmUpto r := by
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hd, hdr⟩)

lemma lcmUpto_cutoff_le {X : ℕ} (hX : 1 ≤ X) :
    Nat.lcmUpto (lcmCutoff X) ≤ X := by
  exact Nat.findGreatest_spec (P := fun r => Nat.lcmUpto r ≤ X)
    (m := 0) (Nat.zero_le X) (by simpa [Nat.lcmUpto] using hX)

lemma cutoff_next_lcm_gt {X : ℕ} (hX : 1 ≤ X) :
    X < Nat.lcmUpto (lcmCutoff X + 1) := by
  by_contra hnot
  have hnext : Nat.lcmUpto (lcmCutoff X + 1) ≤ X := Nat.le_of_not_gt hnot
  by_cases hcut : lcmCutoff X < X
  · have hs : lcmCutoff X + 1 ≤ X := Nat.succ_le_of_lt hcut
    have hle := Nat.le_findGreatest (P := fun r => Nat.lcmUpto r ≤ X) hs hnext
    have hle' : lcmCutoff X + 1 ≤ lcmCutoff X := by
      simpa [lcmCutoff] using hle
    omega

  · have heq : lcmCutoff X = X := by
      exact Nat.le_antisymm (lcmCutoff_le X) (Nat.le_of_not_gt hcut)
    have hdvd : X + 1 ∣ Nat.lcmUpto (X + 1) :=
      dvd_lcmUpto (Nat.succ_pos X) le_rfl
    have hlower := Nat.le_of_dvd (Nat.lcmUpto_pos (X + 1)) hdvd
    rw [heq] at hnext
    omega

lemma lcmUpto_succ_le_mul (r : ℕ) :
    Nat.lcmUpto (r + 1) ≤ (r + 1) * Nat.lcmUpto r := by
  have hdiv : Nat.lcmUpto (r + 1) ∣ (r + 1) * Nat.lcmUpto r := by
    apply Finset.lcm_dvd
    intro d hd
    have hdI := Finset.mem_Icc.mp hd
    rcases hdI.2.eq_or_lt with heq | hlt
    · subst d
      exact dvd_mul_right (r + 1) (Nat.lcmUpto r)
    · exact (dvd_lcmUpto hdI.1 (by omega)).mul_left (r + 1)
  exact Nat.le_of_dvd (mul_pos (Nat.succ_pos r) (Nat.lcmUpto_pos r)) hdiv

lemma cutoff_succ_not_dvd {X : ℕ} (hX : 1 ≤ X) :
    ¬lcmCutoff X + 1 ∣ Nat.lcmUpto (lcmCutoff X) := by
  intro hdiv
  have hall : ∀ d ∈ Finset.Icc 1 (lcmCutoff X + 1),
      d ∣ Nat.lcmUpto (lcmCutoff X) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rcases hd.2.eq_or_lt with heq | hlt
    · simpa [heq] using hdiv
    · exact dvd_lcmUpto hd.1 (by omega)
  have hnext_dvd : Nat.lcmUpto (lcmCutoff X + 1) ∣
      Nat.lcmUpto (lcmCutoff X) := by
    exact Finset.lcm_dvd hall
  have hle : Nat.lcmUpto (lcmCutoff X + 1) ≤
      Nat.lcmUpto (lcmCutoff X) :=
    Nat.le_of_dvd (Nat.lcmUpto_pos _) hnext_dvd
  exact (Nat.not_lt_of_ge (hle.trans (lcmUpto_cutoff_le hX)))
    (cutoff_next_lcm_gt hX)

lemma leastNondivisor_lcmCutoff {X : ℕ} (hX : 1 ≤ X) :
    leastNondivisor (Nat.lcmUpto (lcmCutoff X)) (Nat.lcmUpto_pos _) =
      lcmCutoff X + 1 := by
  apply Nat.le_antisymm
  · exact leastNondivisor_le (Nat.lcmUpto_pos _)
      (Nat.succ_pos _) (cutoff_succ_not_dvd hX)
  · by_contra hnot
    have hlt : leastNondivisor (Nat.lcmUpto (lcmCutoff X))
        (Nat.lcmUpto_pos _) < lcmCutoff X + 1 := Nat.lt_of_not_ge hnot
    have hsle : leastNondivisor (Nat.lcmUpto (lcmCutoff X))
        (Nat.lcmUpto_pos _) ≤ lcmCutoff X := by omega
    have hspos : 0 < leastNondivisor (Nat.lcmUpto (lcmCutoff X))
        (Nat.lcmUpto_pos _) := (leastNondivisor_spec _ _).1
    have hdvd : leastNondivisor (Nat.lcmUpto (lcmCutoff X))
        (Nat.lcmUpto_pos _) ∣ Nat.lcmUpto (lcmCutoff X) :=
      dvd_lcmUpto hspos hsle
    exact (leastNondivisor_spec _ _).2 hdvd

lemma lcmCutoff_tendsto_atTop : Tendsto lcmCutoff atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro R
  refine ⟨max R (Nat.lcmUpto R), fun X hX => ?_⟩
  have hRX : R ≤ X := (le_max_left R (Nat.lcmUpto R)).trans hX
  have hLX : Nat.lcmUpto R ≤ X :=
    (le_max_right R (Nat.lcmUpto R)).trans hX
  exact Nat.le_findGreatest hRX hLX

/-- The weak prime number theorem in the quotient form used for both
sides of the maximal-LCM cutoff. -/
lemma chebyshev_psi_ratio_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  have hden : ∀ᶠ x : ℝ in atTop, (id x : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hx.ne'
  exact (Asymptotics.isEquivalent_iff_tendsto_one hden).mp WeakPNT''

/-! ## The prime-power endpoint -/

/-- In the additive cyclic group of prime-power order, its subgroup of order
`p` is contained in every nonzero cyclic subgroup.  This explicit natural
multiple form is the arithmetic input used by the subset-sum growth proof. -/
lemma primePower_socle_is_nsmul {p a i : ℕ} (hp : p.Prime) (ha : 0 < a)
    (u : ZMod (p ^ a)) (hu : u ≠ 0) :
    ∃ k : ℕ, k • u = (i * p ^ (a - 1) : ZMod (p ^ a)) := by
  let N := p ^ a
  have hNpos : 0 < N := pow_pos hp.pos a
  letI : NeZero N := ⟨hNpos.ne'⟩
  have huval : 0 < u.val := Nat.pos_of_ne_zero (ZMod.val_ne_zero u |>.mpr hu)
  let g := Nat.gcd u.val N
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right u.val hNpos
  have hgle : g ≤ N := Nat.gcd_le_right u.val hNpos
  have hglt : g < N := by
    apply lt_of_le_of_ne hgle
    intro hgeq
    have hNdiv : N ∣ u.val := by
      rw [← hgeq]
      exact Nat.gcd_dvd_left u.val N
    have hNle : N ≤ u.val := Nat.le_of_dvd huval hNdiv
    exact (Nat.not_le_of_gt u.val_lt) hNle
  have hgdiv : g ∣ p ^ a := by
    simpa [g, N] using Nat.gcd_dvd_right u.val N
  obtain ⟨b, hba, hgb⟩ := (Nat.dvd_prime_pow hp).mp hgdiv
  have hbne : b ≠ a := by
    intro hbaeq
    subst b
    have : g = N := by simpa [N] using hgb
    exact (Nat.ne_of_lt hglt) this
  have hbpred : b ≤ a - 1 := by omega
  have hpowdiv : p ^ b ∣ p ^ (a - 1) := pow_dvd_pow p hbpred
  obtain ⟨t, ht⟩ := hpowdiv
  obtain ⟨c, hcN, hc⟩ := Nat.exists_mul_mod_eq_gcd hglt
  have hmod : u.val * c ≡ g [MOD N] := by
    rw [Nat.ModEq]
    rw [hc, Nat.mod_eq_of_lt hglt]
  have hmod' : u.val * (c * (i * t)) ≡ i * p ^ (a - 1) [MOD N] := by
    have h := hmod.mul_right (i * t)
    convert h using 1
    · ring
    · rw [hgb, ht]
      ring
  refine ⟨c * (i * t), ?_⟩
  change (c * (i * t)) • (u : ZMod N) =
    (i * p ^ (a - 1) : ZMod N)
  rw [← ZMod.natCast_zmod_val u]
  rw [nsmul_eq_mul, ← Nat.cast_mul]
  rw [← Nat.cast_pow, ← Nat.cast_mul]
  rw [ZMod.natCast_eq_natCast_iff]
  simpa [Nat.mul_comm] using hmod'

lemma nsmul_mem_of_expansion_eq_zero {m : ℕ} [NeZero m] {D : Finset (ZMod m)}
    {a : ZMod m} (hzero : 0 ∈ D) (hexp : Erdos54.expansion D a = 0) :
    ∀ k : ℕ, k • a ∈ D := by
  have hempty : Erdos54.translate D a \ D = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [Erdos54.expansion] using hexp
  have hsub : Erdos54.translate D a ⊆ D := by
    intro x hx
    by_contra hxD
    have hmem : x ∈ Erdos54.translate D a \ D :=
      Finset.mem_sdiff.mpr ⟨hx, hxD⟩
    rw [hempty] at hmem
    simpa using hmem
  intro k
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
      apply hsub
      rw [Erdos54.mem_translate]
      change (k.succ • a) - a ∈ D
      rw [succ_nsmul, add_sub_cancel_right]
      exact ih

lemma expansion_pos_of_target_nsmul {m a : ℕ} [NeZero m] {D : Finset (ZMod m)}
    {z : ZMod m} (hzero : 0 ∈ D) (hmul : ∃ k : ℕ, k • (a : ZMod m) = z)
    (hnot : z ∉ Erdos54.cyclicResidueStep m D a) :
    0 < Erdos54.expansion D (a : ZMod m) := by
  by_contra hnonpos
  have hexp : Erdos54.expansion D (a : ZMod m) = 0 := Nat.eq_zero_of_not_pos hnonpos
  obtain ⟨k, rfl⟩ := hmul
  apply hnot
  exact Finset.mem_union_left _ (nsmul_mem_of_expansion_eq_zero hzero hexp k)

/-- If a residue `z` is a natural multiple of every exposed residue but is
still absent after all exposures, the subset-sum state grew at every step. -/
lemma cyclicSubsetSum_card_lower_of_not_mem {m : ℕ} [NeZero m] {z : ZMod m}
    (s : List ℕ)
    (hmul : ∀ a ∈ s, ∃ k : ℕ, k • (a : ZMod m) = z)
    (hnot : z ∉ Erdos54.cyclicSubsetSumResiduesList m s) :
    s.length + 1 ≤ (Erdos54.cyclicSubsetSumResiduesList m s).card := by
  induction s using List.reverseRecOn with
  | nil => simp [Erdos54.cyclicSubsetSumResiduesList]
  | append_singleton s a ih =>
      have hnotOld : z ∉ Erdos54.cyclicSubsetSumResiduesList m s := by
        intro hz
        exact hnot (Erdos54.cyclicSubsetSumResiduesList_mono_append m s [a] hz)
      have hmulOld : ∀ b ∈ s, ∃ k : ℕ, k • (b : ZMod m) = z := by
        intro b hb
        exact hmul b (by simp [hb])
      have hlen := ih hmulOld hnotOld
      have hmulA : ∃ k : ℕ, k • (a : ZMod m) = z := hmul a (by simp)
      have hnotStep : z ∉ Erdos54.cyclicResidueStep m
          (Erdos54.cyclicSubsetSumResiduesList m s) a := by
        simpa using hnot
      have hexp : 0 < Erdos54.expansion
          (Erdos54.cyclicSubsetSumResiduesList m s) (a : ZMod m) :=
        expansion_pos_of_target_nsmul
          (Erdos54.zero_mem_cyclicSubsetSumResiduesList m s) hmulA hnotStep
      rw [List.length_append, List.length_singleton,
        Erdos54.card_cyclicSubsetSumResiduesList_append_singleton]
      omega

/-- Alon--Freiman's prime-power endpoint lemma, in the ordered form needed
before passing back to a finset of the original integers. -/
lemma primePower_target_mem_cyclicSubsetSums {p a i : ℕ}
    (hp : p.Prime) (ha : 0 < a) (s : List ℕ)
    (hlen : s.length = p ^ a - 1)
    (hnonzero : ∀ x ∈ s, (x : ZMod (p ^ a)) ≠ 0) :
    (i * p ^ (a - 1) : ZMod (p ^ a)) ∈
      Erdos54.cyclicSubsetSumResiduesList (p ^ a) s := by
  letI : NeZero (p ^ a) := ⟨(pow_pos hp.pos a).ne'⟩
  let z : ZMod (p ^ a) := i * p ^ (a - 1)
  by_contra hnot
  have hmul : ∀ x ∈ s, ∃ k : ℕ, k • (x : ZMod (p ^ a)) = z := by
    intro x hx
    exact primePower_socle_is_nsmul hp ha (x : ZMod (p ^ a)) (hnonzero x hx)
  have hlower := cyclicSubsetSum_card_lower_of_not_mem s hmul hnot
  have hlower' : p ^ a ≤
      (Erdos54.cyclicSubsetSumResiduesList (p ^ a) s).card := by
    rw [hlen] at hlower
    have hpowa : 0 < p ^ a := pow_pos hp.pos a
    omega
  have hcard : (Erdos54.cyclicSubsetSumResiduesList (p ^ a) s).card =
      Fintype.card (ZMod (p ^ a)) := by
    apply Nat.le_antisymm
    · exact Finset.card_le_univ _
    · simpa using hlower'
  have huniv := Finset.eq_univ_of_card
    (Erdos54.cyclicSubsetSumResiduesList (p ^ a) s) hcard
  apply hnot
  rw [huniv]
  exact Finset.mem_univ z

/-- Finset form of the prime-power endpoint: `p^a-1` nonmultiples have a
subset sum in each residue `i p^(a-1)` of the order-`p` subgroup. -/
lemma exists_subset_sum_mod_primePower {p a i : ℕ} (hp : p.Prime) (ha : 0 < a)
    {S : Finset ℕ} (hcard : p ^ a - 1 ≤ S.card)
    (hnondiv : ∀ x ∈ S, ¬p ^ a ∣ x) :
    ∃ u ∈ S.subsetSum,
      (u : ZMod (p ^ a)) = (i * p ^ (a - 1) : ZMod (p ^ a)) := by
  letI : NeZero (p ^ a) := ⟨(pow_pos hp.pos a).ne'⟩
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hcard
  let l := T.toList
  have hllen : l.length = p ^ a - 1 := by simpa [l] using hTcard
  have hlnonzero : ∀ x ∈ l, (x : ZMod (p ^ a)) ≠ 0 := by
    intro x hx
    have hxT : x ∈ T := by simpa [l] using hx
    intro hzero
    exact hnondiv x (hTS hxT) ((ZMod.natCast_eq_zero_iff x (p ^ a)).mp hzero)
  have hres := primePower_target_mem_cyclicSubsetSums (i := i) hp ha l hllen hlnonzero
  rw [Erdos54.cyclicSubsetSumResiduesList_eq_subsetSumResidues
    (p ^ a) l (by simpa [l] using T.nodup_toList)] at hres
  rw [Erdos54.mem_subsetSumResidues] at hres
  obtain ⟨u, hu, hucast⟩ := hres
  have huT : u ∈ T.subsetSum := by simpa [l] using hu
  exact ⟨u, Finset.subsetSum_mono hTS huT, hucast⟩

/-! ## The elementary multiples construction -/

/-- The positive multiples of `q` which do not exceed `n`. -/
def multiplesUpTo (n q : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun a => a ≠ 0 ∧ q ∣ a

@[simp] lemma mem_multiplesUpTo {n q a : ℕ} :
    a ∈ multiplesUpTo n q ↔ a ≤ n ∧ a ≠ 0 ∧ q ∣ a := by
  simp [multiplesUpTo]

lemma multiplesUpTo_subset_Icc (n q : ℕ) :
    multiplesUpTo n q ⊆ Finset.Icc 1 n := by
  intro a ha
  rw [mem_multiplesUpTo] at ha
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr ha.2.1, ha.1⟩

@[simp] lemma card_multiplesUpTo (n q : ℕ) :
    (multiplesUpTo n q).card = n / q := by
  simpa [multiplesUpTo] using Nat.card_multiples' n q

lemma dvd_subsetSum_of_mem_multiplesUpTo {n q x : ℕ}
    (hx : x ∈ (multiplesUpTo n q).subsetSum) : q ∣ x := by
  obtain ⟨T, hT, rfl⟩ := Finset.mem_subsetSum_iff.mp hx
  exact Finset.dvd_sum fun a ha => (mem_multiplesUpTo.mp (hT ha)).2.2

lemma multiplesUpTo_avoids {n q m : ℕ} (hqm : ¬q ∣ m) :
    AvoidsSubsetSum m (multiplesUpTo n q) := by
  intro hm
  exact hqm (dvd_subsetSum_of_mem_multiplesUpTo hm)

/-- Erdős--Graham's elementary lower construction for a fixed target. -/
lemma admissible_of_bounded_prime_nondivisors {n k Q : ℕ}
    (hQ : 0 < Q) (hk : k ≤ n / Q)
    (hprime : ∀ m : ℕ, 0 < m → m ≤ n * (n + 1) / 2 →
      ∃ p : ℕ, p.Prime ∧ p ≤ Q ∧ ¬p ∣ m) :
    AdmissibleCard n k := by
  intro m hm
  by_cases hlarge : n * (n + 1) / 2 < m
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq
      (s := Finset.Icc 1 n) (n := k)
      (by simpa using hk.trans (Nat.div_le_self n Q))
    refine ⟨S, hSsub, hScard, ?_⟩
    intro hsum
    obtain ⟨T, hTS, rfl⟩ := Finset.mem_subsetSum_iff.mp hsum
    have hsum_le : (∑ a ∈ T, a) ≤ ∑ a ∈ Finset.Icc 1 n, a := by
      exact Finset.sum_le_sum_of_subset (hTS.trans hSsub)
    have hinterval_sum : ∑ a ∈ Finset.Icc 1 n, a = n * (n + 1) / 2 := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      have hzero : 0 ∉ Finset.Ico 1 (n + 1) := by simp
      calc
        ∑ a ∈ Finset.Ico 1 (n + 1), a =
            ∑ a ∈ insert 0 (Finset.Ico 1 (n + 1)), a := by
              rw [Finset.sum_insert hzero]
              simp
        _ = ∑ a ∈ Finset.Ico 0 (n + 1), a := by
              rw [show insert 0 (Finset.Ico 1 (n + 1)) =
                Finset.Ico 0 (n + 1) by
                  simpa using Finset.insert_Ico_add_one_left_eq_Ico
                    (by omega : 0 < n + 1)]
        _ = ∑ a ∈ Finset.range (n + 1), a := by
              rw [Nat.Ico_zero_eq_range]
        _ = n * (n + 1) / 2 := by
              rw [Finset.sum_range_id]
              simp only [Nat.add_sub_cancel]
              rw [Nat.mul_comm]
    omega
  · obtain ⟨p, hp, hpQ, hpm⟩ := hprime m hm (Nat.le_of_not_gt hlarge)
    have hpPos : 0 < p := hp.pos
    have hcard : k ≤ (multiplesUpTo n p).card := by
      rw [card_multiplesUpTo]
      exact hk.trans (Nat.div_le_div_left hpQ hpPos)
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
    refine ⟨S, hSsub.trans (multiplesUpTo_subset_Icc n p), hScard, ?_⟩
    intro hsum
    exact hpm (dvd_subsetSum_of_mem_multiplesUpTo
      (Finset.subsetSum_mono hSsub hsum))

/-! ## The Erdős--Graham lower bound -/

/-- A real logarithmic prime cutoff, rounded upward. -/
noncomputable def primeCutoff (c : ℝ) (n : ℕ) : ℕ :=
  ⌈c * Real.log (n : ℝ)⌉₊

lemma primeCutoff_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (primeCutoff c) atTop atTop := by
  apply tendsto_nat_ceil_atTop.comp
  exact (tendsto_log_coe_at_top.const_mul_atTop hc)

lemma primeCutoff_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (primeCutoff c n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 c) := by
  let scale : ℕ → ℝ := fun n => c * Real.log (n : ℝ)
  have hscale : Tendsto scale atTop atTop :=
    tendsto_log_coe_at_top.const_mul_atTop hc
  have hceil : Tendsto (fun n : ℕ => (⌈scale n⌉₊ : ℝ) / scale n)
      atTop (𝓝 1) := tendsto_nat_ceil_div_atTop.comp hscale
  have hconst : Tendsto (fun n : ℕ => scale n / Real.log (n : ℝ))
      atTop (𝓝 c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_log_coe_at_top.eventually (eventually_ne_atTop 0)]
      with n hn
    simp [scale, hn]
  have hprod := hceil.mul hconst
  have hprod' : Tendsto (fun n : ℕ =>
      ((⌈scale n⌉₊ : ℝ) / scale n) *
        (scale n / Real.log (n : ℝ))) atTop (𝓝 c) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_ne_atTop 0)]
    with n hn
  have hscaleNe : scale n ≠ 0 := mul_ne_zero hc.ne' hn
  dsimp [primeCutoff]
  rw [show c * Real.log (n : ℝ) = scale n by rfl]
  field_simp

lemma chebyshev_theta_primeCutoff_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      Chebyshev.theta (primeCutoff c n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 c) := by
  have hden : ∀ᶠ x : ℝ in atTop, (id x : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hx.ne'
  have htheta : Tendsto (fun x : ℝ => Chebyshev.theta x / x)
      atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hden).mp chebyshev_asymptotic
  have hcutReal : Tendsto (fun n : ℕ => (primeCutoff c n : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp (primeCutoff_tendsto_atTop hc)
  have hfirst := htheta.comp hcutReal
  have hsecond := primeCutoff_ratio hc
  have hprod := hfirst.mul hsecond
  have hprod' : Tendsto (fun n : ℕ =>
      (Chebyshev.theta (primeCutoff c n : ℝ) /
          (primeCutoff c n : ℝ)) *
        ((primeCutoff c n : ℝ) / Real.log (n : ℝ)))
      atTop (𝓝 c) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_ne_atTop 0),
     hcutReal.eventually (eventually_ne_atTop 0)] with n hlog hcut
  field_simp

lemma primorial_dvd_of_primes_dvd {Q m : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ m) :
    primorial Q ∣ m := by
  rw [primorial]
  exact Finset.prod_primes_dvd _
    (fun p hp => (Finset.mem_filter.mp hp).2.prime)
    (fun p hp => h p (Finset.mem_filter.mp hp).2
      (by simpa using (Finset.mem_filter.mp hp).1))

/-- The PNT consequence used by Erdős and Graham: every positive target at
most the sum of `[1,n]` misses a prime below any fixed cutoff `c log n`,
provided `c>2` and `n` is large. -/
lemma eventually_exists_prime_nondivisor (c : ℝ) (hc : 2 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m →
      m ≤ n * (n + 1) / 2 →
      ∃ p : ℕ, p.Prime ∧ p ≤ primeCutoff c n ∧ ¬p ∣ m := by
  have hratio := chebyshev_theta_primeCutoff_ratio (show 0 < c by linarith)
  have htheta : ∀ᶠ n : ℕ in atTop,
      2 < Chebyshev.theta (primeCutoff c n : ℝ) / Real.log (n : ℝ) :=
    hratio.eventually (Ioi_mem_nhds hc)
  filter_upwards [htheta, eventually_gt_atTop 1] with n hnTheta hn
  intro m hm hmBound
  by_contra hnone
  push_neg at hnone
  have hprimdiv : primorial (primeCutoff c n) ∣ m :=
    primorial_dvd_of_primes_dvd fun p hp hpQ => hnone p hp hpQ
  have hprimle : primorial (primeCutoff c n) ≤ m :=
    Nat.le_of_dvd hm hprimdiv
  have hnpos : 0 < n := by omega
  have hquad : n * (n + 1) / 2 ≤ n * n := by
    apply Nat.div_le_of_le_mul
    nlinarith
  have hmlen : m ≤ n * n := hmBound.trans hquad
  have hlogle : Real.log (primorial (primeCutoff c n) : ℝ) ≤
      2 * Real.log (n : ℝ) := by
    calc
      Real.log (primorial (primeCutoff c n) : ℝ) ≤ Real.log (m : ℝ) :=
        Real.log_le_log (by exact_mod_cast primorial_pos (primeCutoff c n))
          (by exact_mod_cast hprimle)
      _ ≤ Real.log ((n * n : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmlen)
      _ = 2 * Real.log (n : ℝ) := by
        push_cast
        rw [Real.log_mul (by positivity) (by positivity)]
        ring
  have hthetaEq : Chebyshev.theta (primeCutoff c n : ℝ) =
      Real.log (primorial (primeCutoff c n) : ℝ) := by
    simpa using Chebyshev.theta_eq_log_primorial
      (primeCutoff c n : ℝ)
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [lt_div_iff₀ hlogpos] at hnTheta
  rw [hthetaEq] at hnTheta
  linarith

lemma eventually_erdosF_lower (c : ℝ) (hc : 2 < c) :
    ∀ᶠ n : ℕ in atTop, n / primeCutoff c n ≤ erdosF n := by
  filter_upwards
    [eventually_exists_prime_nondivisor c hc,
     (primeCutoff_tendsto_atTop (show 0 < c by linarith)).eventually
       (eventually_gt_atTop 0)] with n hprime hQ
  have hadm : AdmissibleCard n (n / primeCutoff c n) :=
    admissible_of_bounded_prime_nondivisors hQ le_rfl hprime
  exact (admissibleCard_iff_le_erdosF (Nat.div_le_self _ _)).mp hadm

lemma real_div_sub_natDiv_lt_one {n q : ℕ} (hq : 0 < q) :
    (n : ℝ) / q - (n / q : ℕ) < 1 := by
  have hdecomp : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have hmod : n % q < q := Nat.mod_lt n hq
  have hdecompR : (q : ℝ) * (n / q : ℕ) + (n % q : ℕ) = n := by
    exact_mod_cast hdecomp
  have hmodR : ((n % q : ℕ) : ℝ) < q := by exact_mod_cast hmod
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have heq : (n : ℝ) / q = (n / q : ℕ) + (n % q : ℕ) / q := by
    field_simp
    nlinarith
  rw [heq]
  simp only [add_sub_cancel_left]
  exact (div_lt_one hqR).2 hmodR

lemma natDiv_primeCutoff_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      ((n / primeCutoff c n : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 c⁻¹) := by
  let v : ℕ → ℝ := fun n =>
    ((n : ℝ) / primeCutoff c n) / ((n : ℝ) / Real.log (n : ℝ))
  let d : ℕ → ℝ := fun n =>
    v n - ((n / primeCutoff c n : ℕ) : ℝ) /
      ((n : ℝ) / Real.log (n : ℝ))
  have hQratio := primeCutoff_ratio hc
  have hv : Tendsto v atTop (𝓝 c⁻¹) := by
    have hinv := hQratio.inv₀ hc.ne'
    apply hinv.congr'
    filter_upwards
      [eventually_gt_atTop 1,
       (primeCutoff_tendsto_atTop hc).eventually (eventually_gt_atTop 0)]
        with n hn hQ
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    have hQR : (primeCutoff c n : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
    dsimp [v]
    field_simp
  have herr : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n)
      atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hdnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ d n := by
    filter_upwards
      [eventually_gt_atTop 1,
       (primeCutoff_tendsto_atTop hc).eventually (eventually_gt_atTop 0)]
        with n hn hQ
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hnorm : 0 < (n : ℝ) / Real.log (n : ℝ) := div_pos hnR hlog
    dsimp [d, v]
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_right Nat.cast_div_le hnorm.le
  have hdle : ∀ᶠ n : ℕ in atTop,
      d n ≤ Real.log (n : ℝ) / n := by
    filter_upwards
      [eventually_gt_atTop 1,
       (primeCutoff_tendsto_atTop hc).eventually (eventually_gt_atTop 0)]
        with n hn hQ
    have hnR : (0 : ℝ) < n := by positivity
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hnorm : 0 < (n : ℝ) / Real.log (n : ℝ) := div_pos hnR hlog
    have hfloor := real_div_sub_natDiv_lt_one (n := n) (q := primeCutoff c n) hQ
    dsimp [d, v]
    calc
      (n : ℝ) / primeCutoff c n / ((n : ℝ) / Real.log (n : ℝ)) -
          (n / primeCutoff c n : ℕ) / ((n : ℝ) / Real.log (n : ℝ)) =
          ((n : ℝ) / primeCutoff c n -
            (n / primeCutoff c n : ℕ)) / ((n : ℝ) / Real.log (n : ℝ)) := by ring
      _ ≤ 1 / ((n : ℝ) / Real.log (n : ℝ)) :=
        div_le_div_of_nonneg_right hfloor.le hnorm.le
      _ = Real.log (n : ℝ) / n := by field_simp
  have hd : Tendsto d atTop (𝓝 0) := squeeze_zero' hdnonneg hdle herr
  have hsub := hv.sub hd
  simpa only [sub_zero] using hsub.congr'
    (Filter.Eventually.of_forall fun n => by simp [d])

/-- The fully formal Erdős--Graham half of Problem 771. -/
lemma erdosF_ratio_lower_bound (c : ℝ) (hc : 2 < c) :
    ∀ᶠ n : ℕ in atTop,
      ((n / primeCutoff c n : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
        (erdosF n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)) := by
  filter_upwards [eventually_erdosF_lower c hc, eventually_gt_atTop 1]
    with n hbound hn
  have hnorm : 0 ≤ (n : ℝ) / Real.log (n : ℝ) := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hbound) hnorm

/-! ## Fourier coefficients of a finite subset-sum polynomial -/

namespace LocalLimit

lemma integer_character_integral (k : ℤ) :
    (∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
        if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    norm_num
  rw [if_neg hk]
  let c : ℂ := (2 * Real.pi * (k : ℝ)) * Complex.I
  have hc : c ≠ 0 := by
    have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    dsimp [c]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        (by exact_mod_cast hkreal)) Complex.I_ne_zero
  have hform : (fun t : ℝ ↦
      Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
      fun t : ℝ ↦ Complex.exp (c * t) := by
    funext t
    dsimp [c]
    push_cast
    congr 1
    ring
  rw [hform, integral_exp_mul_complex hc]
  have hper : Complex.exp (c * (1 / 2 : ℝ)) =
      Complex.exp (c * (-1 / 2 : ℝ)) := by
    rw [← mul_one (Complex.exp (c * (-1 / 2 : ℝ))),
      ← Complex.exp_int_mul_two_pi_mul_I k, ← Complex.exp_add]
    congr 1
    dsimp [c]
    push_cast
    ring
  rw [hper]
  simp

/-- The fair Bernoulli characteristic product attached to a finite set of
integer weights. -/
noncomputable def bernoulliProduct (A : Finset ℕ) (t : ℝ) : ℂ :=
  ∏ a ∈ A, (1 + Complex.exp (((2 * Real.pi * (a : ℝ) * t : ℝ) : ℂ) *
    Complex.I)) / 2

/-- The Fourier phase selecting the integer coefficient `M`. -/
noncomputable def coefficientPhase (M : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((-(2 * Real.pi * (M : ℝ) * t : ℝ) : ℂ) * Complex.I)

lemma bernoulliProduct_expand (A : Finset ℕ) (t : ℝ) :
    bernoulliProduct A t =
      (2 : ℂ) ^ (-(A.card : ℤ)) *
        ∑ T ∈ A.powerset,
          Complex.exp (((2 * Real.pi * ((∑ a ∈ T, a : ℕ) : ℝ) * t : ℝ) : ℂ) *
            Complex.I) := by
  classical
  rw [bernoulliProduct]
  have hfactor :
      (∏ a ∈ A, (1 + Complex.exp (((2 * Real.pi * (a : ℝ) * t : ℝ) : ℂ) *
          Complex.I)) / 2) =
        ∏ a ∈ A, (2 : ℂ)⁻¹ *
          (Complex.exp (((2 * Real.pi * (a : ℝ) * t : ℝ) : ℂ) * Complex.I) + 1) := by
    apply Finset.prod_congr rfl
    intro a ha
    field_simp
    ring
  rw [hfactor, Finset.prod_mul_distrib, Finset.prod_add]
  simp only [Finset.prod_const, one_pow, mul_one]
  rw [show (2 : ℂ)⁻¹ ^ A.card = (2 : ℂ) ^ (-(A.card : ℤ)) by
    rw [zpow_neg, zpow_natCast, inv_pow]]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]

noncomputable def coefficientIntegral (A : Finset ℕ) (M : ℕ) : ℂ :=
  ∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
    coefficientPhase M t * bernoulliProduct A t

lemma coefficientIntegral_eq (A : Finset ℕ) (M : ℕ) :
    coefficientIntegral A M =
      (((A.powerset.filter fun T => ∑ a ∈ T, a = M).card : ℕ) : ℝ) /
        (2 : ℝ) ^ A.card := by
  classical
  rw [coefficientIntegral]
  have hfun : (fun t : ℝ => coefficientPhase M t * bernoulliProduct A t) =
      fun t : ℝ => (2 : ℂ) ^ (-(A.card : ℤ)) *
        ∑ T ∈ A.powerset,
          coefficientPhase M t *
            Complex.exp (((2 * Real.pi * ((∑ a ∈ T, a : ℕ) : ℝ) * t : ℝ) : ℂ) *
              Complex.I) := by
    funext t
    rw [bernoulliProduct_expand]
    rw [← mul_assoc, mul_comm (coefficientPhase M t), mul_assoc,
      Finset.mul_sum]
  rw [hfun, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [coefficientPhase, ← Complex.exp_add]
    have hterm : ∀ T ∈ A.powerset,
        (∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          Complex.exp
            ((-(2 * Real.pi * (M : ℝ) * t : ℝ) : ℂ) * Complex.I +
              ((2 * Real.pi * ((∑ a ∈ T, a : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
          if (∑ a ∈ T, a) = M then 1 else 0 := by
      intro T hT
      convert integer_character_integral
        ((∑ a ∈ T, a : ℕ) - (M : ℤ)) using 1
      · congr 2
        funext t
        congr 1
        push_cast
        ring
      · simp only [Int.subNatNat_eq_coe, sub_eq_zero, Int.natCast_inj]
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_boole (fun T : Finset ℕ => ∑ a ∈ T, a = M) A.powerset]
    simp only [Nat.cast_ofNat, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_pow]
    rw [div_eq_mul_inv, mul_comm]
    congr 1
    rw [zpow_neg, zpow_natCast]
    norm_num
  · intro T hT
    apply Continuous.intervalIntegrable
    unfold coefficientPhase
    fun_prop

lemma mem_subsetSum_of_coefficientIntegral_re_pos {A : Finset ℕ} {M : ℕ}
    (hpos : 0 < (coefficientIntegral A M).re) :
    M ∈ A.subsetSum := by
  by_contra hnot
  rw [coefficientIntegral_eq] at hpos
  have hempty : A.powerset.filter (fun T => ∑ a ∈ T, a = M) = ∅ := by
    ext T
    constructor
    · intro hT
      rw [Finset.mem_filter] at hT
      exact (hnot (Finset.mem_subsetSum_iff.mpr
        ⟨T, Finset.mem_powerset.mp hT.1, hT.2⟩)).elim
    · intro hT
      simp at hT
  rw [hempty] at hpos
  norm_num at hpos

lemma bernoulliFactor_centered (x : ℝ) :
    (1 + Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)) / 2 =
      Complex.exp ((x : ℂ) * Complex.I) * (Real.cos x : ℂ) := by
  have htwo := Complex.two_cos (x : ℂ)
  rw [← Complex.ofReal_cos] at htwo
  apply (div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  calc
    1 + Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((x : ℂ) * Complex.I) *
          Complex.exp (-(x : ℂ) * Complex.I) +
        Complex.exp ((x : ℂ) * Complex.I) *
          Complex.exp ((x : ℂ) * Complex.I) := by
            rw [← Complex.exp_add, ← Complex.exp_add]
            simp
            congr 2
            ring
    _ = Complex.exp ((x : ℂ) * Complex.I) *
          (Complex.exp ((x : ℂ) * Complex.I) +
            Complex.exp (-(x : ℂ) * Complex.I)) := by ring
    _ = Complex.exp ((x : ℂ) * Complex.I) *
          ((Real.cos x : ℂ) * 2) := by
            rw [← htwo]
            congr 1
            rw [mul_comm]
    _ = (Complex.exp ((x : ℂ) * Complex.I) * (Real.cos x : ℂ)) * 2 := by
      rw [mul_assoc]

/-- Centered Bernoulli form of the subset-sum characteristic integrand. -/
lemma coefficient_integrand_centered (A : Finset ℕ) (M : ℕ) (t : ℝ) :
    coefficientPhase M t * bernoulliProduct A t =
      Complex.exp ((((2 * Real.pi *
        (((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M) * t : ℝ)) : ℂ) * Complex.I) *
        ∏ a ∈ A, (Real.cos (Real.pi * (a : ℝ) * t) : ℂ) := by
  classical
  rw [bernoulliProduct]
  have hfactor : ∀ a ∈ A,
      (1 + Complex.exp (((2 * Real.pi * (a : ℝ) * t : ℝ) : ℂ) * Complex.I)) / 2 =
        Complex.exp (((Real.pi * (a : ℝ) * t : ℝ) : ℂ) * Complex.I) *
          (Real.cos (Real.pi * (a : ℝ) * t) : ℂ) := by
    intro a ha
    convert bernoulliFactor_centered (Real.pi * (a : ℝ) * t) using 1 <;> ring
  rw [Finset.prod_congr rfl hfactor]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  unfold coefficientPhase
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The squared distance-to-the-nearest-integer energy controlling the
minor arcs. -/
noncomputable def circleEnergy (A : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ a ∈ A, ((a : ℝ) * t - (round ((a : ℝ) * t) : ℝ)) ^ 2

/-- Distance to the nearest integer, viewed as the norm on the unit additive
circle. -/
noncomputable def circleDist (x : ℝ) : ℝ :=
  ‖(x : AddCircle (1 : ℝ))‖

lemma circleDist_eq_round (x : ℝ) :
    circleDist x = |x - (round x : ℝ)| := by
  simp [circleDist, AddCircle.norm_eq]

lemma circleDist_nonneg (x : ℝ) : 0 ≤ circleDist x := norm_nonneg _

lemma circleDist_sub_le (x y : ℝ) :
    circleDist (x - y) ≤ circleDist x + circleDist y := by
  change ‖((x - y : ℝ) : AddCircle (1 : ℝ))‖ ≤ _
  rw [QuotientAddGroup.mk_sub]
  exact norm_sub_le _ _

lemma circleDist_le_abs (x : ℝ) : circleDist x ≤ |x| := by
  change ‖(x : AddCircle (1 : ℝ))‖ ≤ |x|
  simpa [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm
      (S := AddSubgroup.zmultiples (1 : ℝ)) (m := x))

lemma circleDist_add_le (x y : ℝ) :
    circleDist (x + y) ≤ circleDist x + circleDist y := by
  simpa [sub_eq_add_neg, circleDist, norm_neg] using circleDist_sub_le x (-y)

/-- Circle distance is stable under an additive perturbation, in the
one-sided form used below. -/
lemma circleDist_sub_abs_sub_le (x y : ℝ) :
    circleDist y - |x - y| ≤ circleDist x := by
  have htri : circleDist y ≤ circleDist x + circleDist (y - x) := by
    convert circleDist_add_le x (y - x) using 1 <;> ring
  have hpert : circleDist (y - x) ≤ |x - y| := by
    simpa [abs_sub_comm] using circleDist_le_abs (y - x)
  linarith

lemma circleEnergy_eq_sum_circleDist_sq (A : Finset ℕ) (t : ℝ) :
    circleEnergy A t = ∑ a ∈ A, circleDist ((a : ℝ) * t) ^ 2 := by
  rw [circleEnergy]
  apply Finset.sum_congr rfl
  intro a ha
  rw [circleDist_eq_round, sq_abs]

@[simp] lemma circleDist_neg (x : ℝ) : circleDist (-x) = circleDist x := by
  simp [circleDist]

lemma circleEnergy_abs (A : Finset ℕ) (t : ℝ) :
    circleEnergy A |t| = circleEnergy A t := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, circleEnergy_eq_sum_circleDist_sq,
      circleEnergy_eq_sum_circleDist_sq]
    apply Finset.sum_congr rfl
    intro a ha
    rw [show (a : ℝ) * -t = -((a : ℝ) * t) by ring, circleDist_neg]

lemma centeredModOne_mul (a : ℕ) (t : ℝ) :
    Erdos88.Fourier.IsCenteredModOne ((a : ℝ) * t)
      ((a : ℝ) * t - (round ((a : ℝ) * t) : ℝ)) := by
  constructor
  · exact abs_sub_round _
  · refine ⟨round ((a : ℝ) * t), ?_⟩
    push_cast
    ring

lemma norm_bernoulliProduct_le_exp_circleEnergy (A : Finset ℕ) (t : ℝ) :
    ‖bernoulliProduct A t‖ ≤ Real.exp (-circleEnergy A t) := by
  classical
  rw [bernoulliProduct, norm_prod]
  calc
    (∏ a ∈ A,
        ‖(1 + Complex.exp (((2 * Real.pi * (a : ℝ) * t : ℝ) : ℂ) *
          Complex.I)) / 2‖) =
        ∏ a ∈ A, |Real.cos (Real.pi * (a : ℝ) * t)| := by
          apply Finset.prod_congr rfl
          intro a ha
          rw [show (1 + Complex.exp
              (((2 * Real.pi * (a : ℝ) * t : ℝ) : ℂ) * Complex.I)) / 2 =
              Complex.exp (((Real.pi * (a : ℝ) * t : ℝ) : ℂ) * Complex.I) *
                (Real.cos (Real.pi * (a : ℝ) * t) : ℂ) by
            convert bernoulliFactor_centered (Real.pi * (a : ℝ) * t) using 1 <;> ring]
          rw [norm_mul, Complex.norm_exp]
          norm_num [Complex.mul_re, Complex.norm_real, Real.norm_eq_abs]
          have harg : (Real.pi : ℂ) * (a : ℂ) * (t : ℂ) =
              ((Real.pi * (a : ℝ) * t : ℝ) : ℂ) := by
            push_cast
            rfl
          rw [harg]
          rw [← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∏ a ∈ A,
        Real.exp (-(((a : ℝ) * t - (round ((a : ℝ) * t) : ℝ)) ^ 2)) := by
          apply Finset.prod_le_prod
          · intro a ha
            exact abs_nonneg _
          · intro a ha
            have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
            apply Erdos88.Fourier.abs_cos_le_exp_neg_centeredModOne_sq
              (r := Real.pi * (a : ℝ) * t)
              (d := (a : ℝ) * t - (round ((a : ℝ) * t) : ℝ))
            convert centeredModOne_mul a t using 1
            field_simp
    _ = Real.exp (-circleEnergy A t) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [circleEnergy, Finset.sum_neg_distrib]

lemma norm_coefficient_integrand_le_exp_circleEnergy
    (A : Finset ℕ) (M : ℕ) (t : ℝ) :
    ‖coefficientPhase M t * bernoulliProduct A t‖ ≤
      Real.exp (-circleEnergy A t) := by
  rw [norm_mul]
  have hphase : ‖coefficientPhase M t‖ = 1 := by
    rw [coefficientPhase, Complex.norm_exp]
    simp
  rw [hphase, one_mul]
  exact norm_bernoulliProduct_le_exp_circleEnergy A t

lemma norm_prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u v : ι → ℂ)
    (hu : ∀ i ∈ s, ‖u i‖ ≤ 1) (hv : ∀ i ∈ s, ‖v i‖ ≤ 1) :
    ‖(∏ i ∈ s, u i) - ∏ i ∈ s, v i‖ ≤
      ∑ i ∈ s, ‖u i - v i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hua := hu a (by simp)
      have hva := hv a (by simp)
      have hus : ∀ i ∈ s, ‖u i‖ ≤ 1 := fun i hi => hu i (by simp [hi])
      have hvs : ∀ i ∈ s, ‖v i‖ ≤ 1 := fun i hi => hv i (by simp [hi])
      have hpu : ‖∏ i ∈ s, u i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun i hi => norm_nonneg _) hus
      calc
        ‖u a * (∏ i ∈ s, u i) - v a * ∏ i ∈ s, v i‖ =
            ‖(u a - v a) * (∏ i ∈ s, u i) +
              v a * ((∏ i ∈ s, u i) - ∏ i ∈ s, v i)‖ := by
                congr 1
                ring
        _ ≤ ‖(u a - v a) * (∏ i ∈ s, u i)‖ +
              ‖v a * ((∏ i ∈ s, u i) - ∏ i ∈ s, v i)‖ := norm_add_le _ _
        _ = ‖u a - v a‖ * ‖∏ i ∈ s, u i‖ +
              ‖v a‖ * ‖(∏ i ∈ s, u i) - ∏ i ∈ s, v i‖ := by
                rw [norm_mul, norm_mul]
        _ ≤ ‖u a - v a‖ * 1 + 1 * (∑ i ∈ s, ‖u i - v i‖) := by
              gcongr
              exact ih hus hvs
        _ = ‖u a - v a‖ + ∑ i ∈ s, ‖u i - v i‖ := by ring

/-- Fourth-order comparison of a cosine factor with its Gaussian model. -/
lemma norm_cos_sub_gaussian_quadratic_le (y : ℝ) :
    ‖(Real.cos y : ℂ) - (1 - y ^ 2 / 2 : ℝ)‖ ≤
      |y| ^ 4 * Real.exp |y| := by
  let z : ℂ := (y : ℂ) * Complex.I
  let P : ℂ → ℂ := fun w => ∑ m ∈ Finset.range 4, w ^ m / m.factorial
  have hz : ‖z‖ = |y| := by simp [z, Real.norm_eq_abs]
  have hnz : ‖-z‖ = |y| := by simp [hz]
  have hp := Complex.norm_exp_sub_sum_le_norm_mul_exp z 4
  have hm := Complex.norm_exp_sub_sum_le_norm_mul_exp (-z) 4
  rw [hz] at hp
  rw [hnz] at hm
  have hpoly : P z + P (-z) = 2 * (1 - (y ^ 2 / 2 : ℝ) : ℂ) := by
    dsimp [P, z]
    norm_num [Finset.sum_range_succ, div_pow]
    push_cast
    simp only [mul_pow, Complex.I_sq]
    ring
  have hcos : 2 * (Real.cos y : ℂ) = Complex.exp z + Complex.exp (-z) := by
    simpa [z, Complex.ofReal_cos] using Complex.two_cos (y : ℂ)
  have hid : (Real.cos y : ℂ) - (1 - y ^ 2 / 2 : ℝ) =
      ((Complex.exp z - P z) + (Complex.exp (-z) - P (-z))) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    calc
      ((Real.cos y : ℂ) - (1 - y ^ 2 / 2 : ℝ)) * 2 =
          2 * (Real.cos y : ℂ) - 2 * (1 - y ^ 2 / 2 : ℝ) := by ring
      _ = (Complex.exp z + Complex.exp (-z)) - (P z + P (-z)) := by
        rw [hcos, hpoly]
        push_cast
        rfl
      _ = Complex.exp z - P z + (Complex.exp (-z) - P (-z)) := by ring
  rw [hid, norm_div]
  norm_num only [Complex.norm_ofNat]
  calc
    ‖(Complex.exp z - P z) + (Complex.exp (-z) - P (-z))‖ / 2 ≤
        (‖Complex.exp z - P z‖ + ‖Complex.exp (-z) - P (-z)‖) / 2 := by
          gcongr
          exact norm_add_le _ _
    _ ≤ (|y| ^ 4 * Real.exp |y| + |y| ^ 4 * Real.exp |y|) / 2 := by
          gcongr
    _ = |y| ^ 4 * Real.exp |y| := by ring

lemma norm_cos_sub_gaussian_le {y : ℝ} (hy : |y| ≤ 1) :
    ‖(Real.cos y : ℂ) - (Real.exp (-(y ^ 2) / 2) : ℝ)‖ ≤
      (Real.exp 1 + 1) * |y| ^ 4 := by
  let q : ℝ := 1 - y ^ 2 / 2
  have hcos := norm_cos_sub_gaussian_quadratic_le y
  have hexpMono : Real.exp |y| ≤ Real.exp 1 := Real.exp_le_exp.mpr hy
  have hcos' : ‖(Real.cos y : ℂ) - (q : ℂ)‖ ≤
      Real.exp 1 * |y| ^ 4 := by
    calc
      ‖(Real.cos y : ℂ) - (q : ℂ)‖ ≤ |y| ^ 4 * Real.exp |y| := by
        simpa [q] using hcos
      _ ≤ |y| ^ 4 * Real.exp 1 := mul_le_mul_of_nonneg_left hexpMono (by positivity)
      _ = Real.exp 1 * |y| ^ 4 := by ring
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have hy2 : |y| ^ 2 ≤ 1 := by nlinarith
  have hz : ‖-(y ^ 2) / 2‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_pow, abs_ofNat]
    nlinarith
  have he := Real.norm_exp_sub_one_sub_id_le hz
  have he' : ‖(q : ℂ) - (Real.exp (-(y ^ 2) / 2) : ℝ)‖ ≤ |y| ^ 4 := by
    have heReal : |q - Real.exp (-(y ^ 2) / 2)| ≤ (-(y ^ 2) / 2) ^ 2 := by
      have heReal' :
          |Real.exp (-(y ^ 2) / 2) - 1 + y ^ 2 / 2| ≤
            (-(y ^ 2) / 2) ^ 2 := by
        have hnorm : ‖-(y ^ 2) / 2‖ = y ^ 2 / 2 := by
          rw [Real.norm_eq_abs, abs_div, abs_neg,
            abs_of_nonneg (sq_nonneg y), abs_ofNat]
        rw [hnorm, Real.norm_eq_abs] at he
        convert he using 1 <;> ring
      rw [show q - Real.exp (-(y ^ 2) / 2) =
          -(Real.exp (-(y ^ 2) / 2) - 1 + y ^ 2 / 2) by dsimp [q]; ring,
        abs_neg]
      exact heReal'
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc
      |q - Real.exp (-(y ^ 2) / 2)| ≤ (-(y ^ 2) / 2) ^ 2 := heReal
      _ ≤ |y| ^ 4 := by
        have habspow : |y| ^ 4 = y ^ 4 := by
          rw [← abs_pow]
          exact abs_of_nonneg (by positivity)
        rw [habspow]
        nlinarith [sq_nonneg (y ^ 2)]
  calc
    ‖(Real.cos y : ℂ) - (Real.exp (-(y ^ 2) / 2) : ℝ)‖ =
        ‖((Real.cos y : ℂ) - q) + (q - Real.exp (-(y ^ 2) / 2))‖ := by
          congr 1
          ring
    _ ≤ ‖(Real.cos y : ℂ) - q‖ + ‖(q : ℂ) - Real.exp (-(y ^ 2) / 2)‖ :=
      norm_add_le _ _
    _ ≤ Real.exp 1 * |y| ^ 4 + |y| ^ 4 := add_le_add hcos' he'
    _ = (Real.exp 1 + 1) * |y| ^ 4 := by ring

lemma norm_cos_product_sub_gaussian_product_le
    (A : Finset ℕ) (t : ℝ)
    (ht : ∀ a ∈ A, |Real.pi * (a : ℝ) * t| ≤ 1) :
    ‖(∏ a ∈ A, (Real.cos (Real.pi * (a : ℝ) * t) : ℂ)) -
      ∏ a ∈ A, (Real.exp (-(Real.pi * (a : ℝ) * t) ^ 2 / 2) : ℂ)‖ ≤
      ∑ a ∈ A, (Real.exp 1 + 1) * |Real.pi * (a : ℝ) * t| ^ 4 := by
  calc
    ‖(∏ a ∈ A, (Real.cos (Real.pi * (a : ℝ) * t) : ℂ)) -
        ∏ a ∈ A, (Real.exp (-(Real.pi * (a : ℝ) * t) ^ 2 / 2) : ℂ)‖ ≤
        ∑ a ∈ A, ‖(Real.cos (Real.pi * (a : ℝ) * t) : ℂ) -
          (Real.exp (-(Real.pi * (a : ℝ) * t) ^ 2 / 2) : ℂ)‖ := by
      apply norm_prod_sub_prod_le_sum A
        (fun a => (Real.cos (Real.pi * (a : ℝ) * t) : ℂ))
        (fun a => (Real.exp (-(Real.pi * (a : ℝ) * t) ^ 2 / 2) : ℂ))
      · intro a ha
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_cos_le_one (Real.pi * (a : ℝ) * t)
      · intro a ha
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_one_iff.mpr
        nlinarith [sq_nonneg (Real.pi * (a : ℝ) * t)]
    _ ≤ ∑ a ∈ A, (Real.exp 1 + 1) * |Real.pi * (a : ℝ) * t| ^ 4 := by
      exact Finset.sum_le_sum fun a ha => norm_cos_sub_gaussian_le (ht a ha)

/-- The variance of the sum of independent fair Bernoulli variables with
weights in `A`. -/
noncomputable def varianceMass (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (a : ℝ) ^ 2 / 4

lemma varianceMass_nonneg (A : Finset ℕ) : 0 ≤ varianceMass A := by
  exact Finset.sum_nonneg fun a ha => by positivity

lemma varianceMass_eq_quarter_sum (A : Finset ℕ) :
    varianceMass A = (∑ a ∈ A, (a : ℝ) ^ 2) / 4 := by
  rw [varianceMass, Finset.sum_div]

lemma varianceMass_le_card_mul_sq {A : Finset ℕ} {n : ℕ}
    (hA : A ⊆ Finset.Icc 1 n) :
    varianceMass A ≤ (A.card : ℝ) * (n : ℝ) ^ 2 / 4 := by
  rw [varianceMass]
  calc
    ∑ a ∈ A, (a : ℝ) ^ 2 / 4 ≤ ∑ _a ∈ A, (n : ℝ) ^ 2 / 4 := by
      apply Finset.sum_le_sum
      intro a ha
      have han : (a : ℝ) ≤ n := by
        exact_mod_cast (Finset.mem_Icc.mp (hA ha)).2
      have ha0 : (0 : ℝ) ≤ a := by positivity
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith [sq_nonneg ((n : ℝ) - a)]
    _ = (A.card : ℝ) * (n : ℝ) ^ 2 / 4 := by simp; ring

lemma gaussianProduct_eq (A : Finset ℕ) (t : ℝ) :
    ∏ a ∈ A, (Real.exp (-(Real.pi * (a : ℝ) * t) ^ 2 / 2) : ℂ) =
      (Real.exp (-2 * Real.pi ^ 2 * varianceMass A * t ^ 2) : ℂ) := by
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  rw [varianceMass_eq_quarter_sum]
  calc
    ∑ x ∈ A, -(Real.pi * (x : ℝ) * t) ^ 2 / 2 =
        (-Real.pi ^ 2 * t ^ 2 / 2) * ∑ x ∈ A, (x : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = -2 * Real.pi ^ 2 * ((∑ x ∈ A, (x : ℝ) ^ 2) / 4) * t ^ 2 := by
      ring

lemma sum_fourth_le_four_mul_sq_mul_varianceMass {A : Finset ℕ} {n : ℕ}
    (hA : A ⊆ Finset.Icc 1 n) :
    ∑ a ∈ A, (a : ℝ) ^ 4 ≤ 4 * (n : ℝ) ^ 2 * varianceMass A := by
  rw [varianceMass_eq_quarter_sum]
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have han : a ≤ n := (Finset.mem_Icc.mp (hA ha)).2
  have hanR : (a : ℝ) ≤ n := by exact_mod_cast han
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith [sq_nonneg ((a : ℝ) ^ 2),
    mul_self_le_mul_self ha0 hanR]

/-- Distinct positive integer weights have cubic second moment. -/
lemma card_cube_le_sixteen_mul_varianceMass {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) :
    (A.card : ℝ) ^ 3 ≤ 16 * varianceMass A := by
  let k : ℝ := A.card
  let Q : ℝ := ∑ a ∈ A, (a : ℝ) ^ 2
  let U : ℝ := ∑ a ∈ A, (a : ℝ)
  have htriNat := Erdos38.sum_ge_triangular A hpos
  have hdouble : 2 * (A.card * (A.card + 1) / 2) =
      A.card * (A.card + 1) := by
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self A.card)
  have htriCast :
      (((A.card * (A.card + 1) / 2 : ℕ) : ℝ)) =
        k * (k + 1) / 2 := by
    have hdoubleR : (2 : ℝ) * (A.card * (A.card + 1) / 2 : ℕ) =
        (A.card : ℝ) * (A.card + 1) := by exact_mod_cast hdouble
    dsimp [k]
    push_cast at hdoubleR
    linarith
  have htri : k * (k + 1) / 2 ≤ U := by
    rw [← htriCast]
    have htriR : (((A.card * (A.card + 1) / 2 : ℕ) : ℝ)) ≤
        ((A.sum id : ℕ) : ℝ) := by exact_mod_cast htriNat
    simpa [U] using htriR
  have hcauchy : U ^ 2 ≤ k * Q := by
    simpa [U, k, Q] using
      (sq_sum_le_card_mul_sum_sq (s := A) (f := fun a : ℕ => (a : ℝ)))
  have hk0 : 0 ≤ k := by positivity
  have hU0 : 0 ≤ U := by
    dsimp [U]
    positivity
  have hbase : k ^ 2 / 2 ≤ U := by
    nlinarith
  have hsquare : (k ^ 2 / 2) ^ 2 ≤ U ^ 2 :=
    (sq_le_sq₀ (by positivity : 0 ≤ k ^ 2 / 2) hU0).2 hbase
  have hcubic : k ^ 3 ≤ 4 * Q := by
    by_cases hk : k = 0
    · rw [hk]
      norm_num
      dsimp [Q]
      positivity
    · have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hk)
      apply le_of_mul_le_mul_left (a := k) (by nlinarith) hkpos
  rw [varianceMass_eq_quarter_sum]
  dsimp [k, Q] at hcubic ⊢
  convert hcubic using 1 <;> ring

lemma one_sub_sum_le_prod_one_sub {u : ℕ → ℝ} (A : Finset ℕ)
    (hu0 : ∀ a ∈ A, 0 ≤ u a) (hu1 : ∀ a ∈ A, u a ≤ 1) :
    1 - ∑ a ∈ A, u a ≤ ∏ a ∈ A, (1 - u a) := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hua0 := hu0 a (by simp)
      have hua1 := hu1 a (by simp)
      have htail0 : ∀ b ∈ A, 0 ≤ u b := fun b hb => hu0 b (by simp [hb])
      have htail1 : ∀ b ∈ A, u b ≤ 1 := fun b hb => hu1 b (by simp [hb])
      have hih := ih htail0 htail1
      have hprod0 : 0 ≤ ∏ b ∈ A, (1 - u b) := by
        exact Finset.prod_nonneg fun b hb => sub_nonneg.mpr (htail1 b hb)
      calc
        1 - (u a + ∑ b ∈ A, u b) ≤
            (1 - u a) * (1 - ∑ b ∈ A, u b) := by
          have hsum0 : 0 ≤ ∑ b ∈ A, u b := Finset.sum_nonneg htail0
          nlinarith
        _ ≤ (1 - u a) * ∏ b ∈ A, (1 - u b) := by
          exact mul_le_mul_of_nonneg_left hih (sub_nonneg.mpr hua1)

lemma cosineProduct_lower (A : Finset ℕ) (t : ℝ)
    (hsmall : 2 * Real.pi ^ 2 * varianceMass A * t ^ 2 ≤ 1 / 4) :
    (3 : ℝ) / 4 ≤ ∏ a ∈ A, Real.cos (Real.pi * (a : ℝ) * t) := by
  let u : ℕ → ℝ := fun a => (Real.pi * (a : ℝ) * t) ^ 2 / 2
  have hsum : ∑ a ∈ A, u a = 2 * Real.pi ^ 2 * varianceMass A * t ^ 2 := by
    rw [varianceMass_eq_quarter_sum]
    dsimp [u]
    calc
      ∑ a ∈ A, (Real.pi * (a : ℝ) * t) ^ 2 / 2 =
          (Real.pi ^ 2 * t ^ 2 / 2) * ∑ a ∈ A, (a : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = 2 * Real.pi ^ 2 * ((∑ a ∈ A, (a : ℝ) ^ 2) / 4) * t ^ 2 := by
        ring
  have hu0 : ∀ a ∈ A, 0 ≤ u a := by
    intro a ha
    dsimp [u]
    positivity
  have hu1 : ∀ a ∈ A, u a ≤ 1 := by
    intro a ha
    have hterm : u a ≤ ∑ b ∈ A, u b :=
      Finset.single_le_sum (fun b hb => hu0 b hb) ha
    rw [hsum] at hterm
    exact hterm.trans (hsmall.trans (by norm_num))
  calc
    (3 : ℝ) / 4 ≤ 1 - ∑ a ∈ A, u a := by rw [hsum]; linarith
    _ ≤ ∏ a ∈ A, (1 - u a) := one_sub_sum_le_prod_one_sub A hu0 hu1
    _ ≤ ∏ a ∈ A, Real.cos (Real.pi * (a : ℝ) * t) := by
      apply Finset.prod_le_prod
      · intro a ha
        exact sub_nonneg.mpr (hu1 a ha)
      · intro a ha
        exact Real.one_sub_sq_div_two_le_cos

lemma coefficient_integrand_re (A : Finset ℕ) (M : ℕ) (t : ℝ) :
    (coefficientPhase M t * bernoulliProduct A t).re =
      Real.cos (2 * Real.pi *
        (((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M) * t) *
        ∏ a ∈ A, Real.cos (Real.pi * (a : ℝ) * t) := by
  rw [coefficient_integrand_centered]
  have hprod :
      (∏ a ∈ A, (Real.cos (Real.pi * (a : ℝ) * t) : ℂ)) =
        ((∏ a ∈ A, Real.cos (Real.pi * (a : ℝ) * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
  rw [hprod]
  rw [Complex.mul_re]
  rw [Complex.ofReal_re, Complex.ofReal_im]
  simp only [mul_zero, sub_zero]
  rw [Complex.exp_re]
  norm_num [Complex.mul_re, Complex.mul_im]

lemma coefficient_integrand_re_lower_core (A : Finset ℕ) (M : ℕ) (t : ℝ)
    (hvariance : 2 * Real.pi ^ 2 * varianceMass A * t ^ 2 ≤ 1 / 4)
    (hphase : |2 * Real.pi *
      (((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M) * t| ≤ 1) :
    (3 : ℝ) / 8 ≤ (coefficientPhase M t * bernoulliProduct A t).re := by
  rw [coefficient_integrand_re]
  have hcos : (1 : ℝ) / 2 ≤ Real.cos (2 * Real.pi *
      (((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M) * t) := by
    let x : ℝ := 2 * Real.pi *
      (((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M) * t
    have hsquareAbs : |x| ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg x) (by norm_num)).2 (by simpa [x] using hphase)
    have hsquare : x ^ 2 ≤ 1 := by
      simpa [sq_abs] using hsquareAbs
    calc
      (1 : ℝ) / 2 ≤ 1 - (2 * Real.pi *
          (((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M) * t) ^ 2 / 2 := by
        dsimp [x] at hsquare
        nlinarith
      _ ≤ Real.cos (2 * Real.pi *
          (((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M) * t) :=
        Real.one_sub_sq_div_two_le_cos
  have hprod := cosineProduct_lower A t hvariance
  nlinarith [mul_le_mul hcos hprod (by positivity) (by positivity)]

lemma circleEnergy_eq_four_varianceMass_mul_sq {A : Finset ℕ} {n : ℕ}
    (hn : 0 < n) (hA : A ⊆ Finset.Icc 1 n) {t : ℝ}
    (ht : |t| < 1 / (2 * n)) :
    circleEnergy A t = 4 * varianceMass A * t ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [circleEnergy, varianceMass_eq_quarter_sum]
  have hround : ∀ a ∈ A, round ((a : ℝ) * t) = 0 := by
    intro a ha
    rw [round_eq_zero_iff]
    have haN : (a : ℝ) ≤ n := by
      exact_mod_cast (Finset.mem_Icc.mp (hA ha)).2
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have hat : |(a : ℝ) * t| < 1 / 2 := by
      rw [abs_mul]
      have habsa : |(a : ℝ)| ≤ n := by simpa [abs_of_nonneg ha0] using haN
      calc
        |(a : ℝ)| * |t| ≤ (n : ℝ) * |t| :=
          mul_le_mul_of_nonneg_right habsa (abs_nonneg t)
        _ < (n : ℝ) * (1 / (2 * n)) :=
          mul_lt_mul_of_pos_left ht hnR
        _ = 1 / 2 := by field_simp
    exact Set.mem_Ico.mpr ⟨by linarith [neg_abs_le ((a : ℝ) * t)],
      by linarith [le_abs_self ((a : ℝ) * t)]⟩
  calc
    ∑ a ∈ A, ((a : ℝ) * t - (round ((a : ℝ) * t) : ℝ)) ^ 2 =
        ∑ a ∈ A, ((a : ℝ) * t) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hround a ha]
      norm_num
    _ =
        (∑ a ∈ A, (a : ℝ) ^ 2) * t ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = 4 * ((∑ a ∈ A, (a : ℝ) ^ 2) / 4) * t ^ 2 := by ring

/-- A convenient exact near-zero Gaussian envelope. -/
lemma norm_coefficient_integrand_le_near_zero {A : Finset ℕ} {n M : ℕ}
    (hn : 0 < n) (hA : A ⊆ Finset.Icc 1 n) {t : ℝ}
    (ht : |t| < 1 / (2 * n)) :
    ‖coefficientPhase M t * bernoulliProduct A t‖ ≤
      Real.exp (-4 * varianceMass A * t ^ 2) := by
  simpa [circleEnergy_eq_four_varianceMass_mul_sq hn hA ht] using
    norm_coefficient_integrand_le_exp_circleEnergy A M t

/-- If a continuous real integrand is positive on a symmetric core and is
bounded below by one global error outside it, its full circle integral is
positive as soon as the core mass exceeds that error.  This deliberately
weak form keeps the later local subset-sum argument free of unnecessary
Gaussian-tail bookkeeping. -/
lemma integral_lower_of_core_and_outer {f : ℝ → ℝ} (hf : Continuous f)
    {rho error c : ℝ} (hrho0 : 0 ≤ rho) (hrho : rho ≤ 1 / 2)
    (herror : 0 ≤ error)
    (hcore : ∀ t : ℝ, |t| ≤ rho → c ≤ f t)
    (houter : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), rho ≤ |t| →
      -error ≤ f t) :
    2 * rho * c - error ≤
      ∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), f t := by
  have hfi (a b : ℝ) : IntervalIntegrable f MeasureTheory.volume a b :=
    hf.intervalIntegrable a b
  have hleft : -(error * (1 / 2 - rho)) ≤
      ∫ t : ℝ in (-1 / 2 : ℝ)..(-rho), f t := by
    have hmono := intervalIntegral.integral_mono_on
      (by linarith : (-1 / 2 : ℝ) ≤ -rho)
      (continuous_const.intervalIntegrable _ _) (hfi _ _)
      (fun t ht => houter t
        (by constructor <;> linarith [ht.1, ht.2])
        (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2]))
    simp only [intervalIntegral.integral_const] at hmono
    convert hmono using 1 <;> ring
  have hmiddle : 2 * rho * c ≤
      ∫ t : ℝ in (-rho)..rho, f t := by
    have hmono := intervalIntegral.integral_mono_on
      (by linarith : -rho ≤ rho)
      (continuous_const.intervalIntegrable _ _) (hfi _ _)
      (fun t ht => hcore t (by
        rw [abs_le]
        exact ⟨ht.1, ht.2⟩))
    simp only [intervalIntegral.integral_const] at hmono
    convert hmono using 1 <;> ring
  have hright : -(error * (1 / 2 - rho)) ≤
      ∫ t : ℝ in rho..(1 / 2 : ℝ), f t := by
    have hmono := intervalIntegral.integral_mono_on hrho
      (continuous_const.intervalIntegrable _ _) (hfi _ _)
      (fun t ht => houter t
        (by constructor <;> linarith [ht.1, ht.2])
        (by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1))
    simp only [intervalIntegral.integral_const] at hmono
    convert hmono using 1 <;> ring
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    (hfi (-1 / 2) (-rho)) (hfi (-rho) rho)
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    ((hfi (-1 / 2) (-rho)).trans (hfi (-rho) rho))
    (hfi rho (1 / 2))
  rw [← hadd2, ← hadd1]
  nlinarith [mul_nonneg herror hrho0]

lemma continuous_coefficient_integrand_re (A : Finset ℕ) (M : ℕ) :
    Continuous fun t : ℝ =>
      (coefficientPhase M t * bernoulliProduct A t).re := by
  unfold coefficientPhase bernoulliProduct
  fun_prop

lemma cos_nonneg_of_abs_le_pi_div_two {x : ℝ}
    (hx : |x| ≤ Real.pi / 2) : 0 ≤ Real.cos x := by
  apply Real.cos_nonneg_of_mem_Icc
  rw [Set.mem_Icc]
  exact (abs_le.mp hx)

/-- On a very short arc the centered phase and every Bernoulli cosine have
nonnegative real part. -/
lemma coefficient_integrand_re_nonneg_near {A : Finset ℕ} {n M : ℕ}
    (hn : 0 < n) (hA : A ⊆ Finset.Icc 1 n)
    (hcenter : |(((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M)| ≤ 100 * n)
    {t : ℝ} (ht : |t| ≤ 1 / (1000 * n)) :
    0 ≤ (coefficientPhase M t * bernoulliProduct A t).re := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [coefficient_integrand_re]
  have hphaseAbs : |2 * Real.pi *
      (((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M) * t| ≤ Real.pi / 2 := by
    calc
      |2 * Real.pi * (((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M) * t| =
          2 * Real.pi * |(((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M)| * |t| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num),
          abs_of_pos Real.pi_pos]
      _ ≤ 2 * Real.pi * (100 * n) * (1 / (1000 * n)) := by
        gcongr
      _ = Real.pi / 5 := by field_simp; ring
      _ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hphase : 0 ≤ Real.cos (2 * Real.pi *
      (((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M) * t) :=
    cos_nonneg_of_abs_le_pi_div_two hphaseAbs
  have hfactor : ∀ a ∈ A,
      0 ≤ Real.cos (Real.pi * (a : ℝ) * t) := by
    intro a ha
    have haR : (0 : ℝ) ≤ a := by positivity
    have hanR : (a : ℝ) ≤ n := by
      exact_mod_cast (Finset.mem_Icc.mp (hA ha)).2
    apply cos_nonneg_of_abs_le_pi_div_two
    calc
      |Real.pi * (a : ℝ) * t| = Real.pi * (a : ℝ) * |t| := by
        rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg haR]
      _ ≤ Real.pi * (n : ℝ) * (1 / (1000 * n)) := by gcongr
      _ = Real.pi / 1000 := by field_simp
      _ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  exact mul_nonneg hphase (Finset.prod_nonneg hfactor)

/-- Positivity consequence of a minor-arc energy estimate.  The hypotheses
are numerical and are arranged so that later arithmetic arguments need only
supply `henergy`. -/
lemma mem_subsetSum_of_minorArcEnergy {A : Finset ℕ} {n M : ℕ} {rho E : ℝ}
    (hn : 0 < n) (hA : A ⊆ Finset.Icc 1 n) (hrho : 0 < rho)
    (hrhoNear : rho ≤ 1 / (1000 * n))
    (hvariance : 2 * Real.pi ^ 2 * varianceMass A * rho ^ 2 ≤ 1 / 4)
    (hphase : 2 * Real.pi *
      |(((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M)| * rho ≤ 1)
    (hcenter : |(((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M)| ≤ 100 * n)
    (henergy : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2),
      1 / (1000 * n) ≤ |t| → E ≤ circleEnergy A t)
    (hdecay : Real.exp (-E) < 3 * rho / 4) :
    M ∈ A.subsetSum := by
  let f : ℝ → ℝ := fun t =>
    (coefficientPhase M t * bernoulliProduct A t).re
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOneR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrhoHalf : rho ≤ 1 / 2 := by
    calc
      rho ≤ 1 / (1000 * n) := hrhoNear
      _ ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hcore : ∀ t : ℝ, |t| ≤ rho → (3 : ℝ) / 8 ≤ f t := by
    intro t ht
    apply coefficient_integrand_re_lower_core
    · have htSq : t ^ 2 ≤ rho ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg t) hrho.le).2 ht
      have hcoef : 0 ≤ 2 * Real.pi ^ 2 * varianceMass A :=
        mul_nonneg (by positivity) (varianceMass_nonneg A)
      exact (mul_le_mul_of_nonneg_left htSq hcoef).trans hvariance
    · calc
        |2 * Real.pi *
            (((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M) * t| =
            2 * Real.pi *
              |(((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M)| * |t| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num),
            abs_of_pos Real.pi_pos]
        _ ≤ 2 * Real.pi *
              |(((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M)| * rho := by
          gcongr
        _ ≤ 1 := hphase
  have houter : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), rho ≤ |t| →
      -Real.exp (-E) ≤ f t := by
    intro t htI htrho
    rcases le_total |t| (1 / (1000 * n)) with htNear | htFar
    · have hnonneg := coefficient_integrand_re_nonneg_near hn hA hcenter htNear
      exact (neg_nonpos.mpr (Real.exp_nonneg _)).trans hnonneg
    · let z := coefficientPhase M t * bernoulliProduct A t
      have hnorm0 : ‖z‖ ≤ Real.exp (-circleEnergy A t) :=
        norm_coefficient_integrand_le_exp_circleEnergy A M t
      have hnorm : ‖z‖ ≤ Real.exp (-E) :=
        hnorm0.trans (Real.exp_le_exp.mpr (neg_le_neg (henergy t htI htFar)))
      have hre : -‖z‖ ≤ z.re :=
        (abs_le.mp (Complex.abs_re_le_norm z)).1
      dsimp [f, z] at hre ⊢
      linarith
  have hlower := integral_lower_of_core_and_outer
    (continuous_coefficient_integrand_re A M) hrho.le hrhoHalf
    (Real.exp_nonneg _) hcore houter
  have hintegral : 0 < ∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), f t := by
    apply lt_of_lt_of_le _ hlower
    nlinarith
  apply mem_subsetSum_of_coefficientIntegral_re_pos
  have hint : IntervalIntegrable
      (fun t : ℝ => coefficientPhase M t * bernoulliProduct A t)
      MeasureTheory.volume (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
    apply Continuous.intervalIntegrable
    unfold coefficientPhase bernoulliProduct
    fun_prop
  have hre :
      (∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        (coefficientPhase M t * bernoulliProduct A t).re) =
      (∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        coefficientPhase M t * bernoulliProduct A t).re := by
    simpa only [RCLike.re_eq_complex_re] using
      (intervalIntegral.intervalIntegral_re hint)
  rw [coefficientIntegral, ← hre]
  dsimp [f] at hintegral
  exact hintegral

/-! ### Rational grids -/

/-- Residues whose least absolute representative is smaller than `K`. -/
def nearZeroResidues (q K : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun r => min r (q - r) < K

lemma nearZeroResidues_card_le (q K : ℕ) :
    (nearZeroResidues q K).card ≤ 2 * K := by
  let low := Finset.range K
  let high := (Finset.range K).image fun k => q - k
  have hsub : nearZeroResidues q K ⊆ low ∪ high := by
    intro r hr
    rw [nearZeroResidues, Finset.mem_filter] at hr
    rw [Finset.mem_union]
    rcases (min_lt_iff.mp hr.2) with hlo | hhi
    · exact Or.inl (Finset.mem_range.mpr hlo)
    · have hrq : r < q := Finset.mem_range.mp hr.1
      exact Or.inr (Finset.mem_image.mpr
        ⟨q - r, Finset.mem_range.mpr hhi, by omega⟩)
  calc
    (nearZeroResidues q K).card ≤ (low ∪ high).card :=
      Finset.card_le_card hsub
    _ ≤ low.card + high.card := Finset.card_union_le low high
    _ ≤ K + K := by
      dsimp [low, high]
      simpa only [Finset.card_range] using Nat.add_le_add_left
        (Finset.card_image_le (s := Finset.range K) (f := fun k => q - k)) K
    _ = 2 * K := by omega

/-- Pull the near-zero residues back through multiplication by a numerator
coprime to the denominator. -/
def twistedNearZeroResidues (q p K : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun r => min ((r * p) % q) (q - (r * p) % q) < K

lemma twistedNearZeroResidues_card_le {q p K : ℕ} (hq : 0 < q)
    (hpq : p.Coprime q) :
    (twistedNearZeroResidues q p K).card ≤ 2 * K := by
  let f : ℕ → ℕ := fun r => (r * p) % q
  have hinj : Set.InjOn f (twistedNearZeroResidues q p K : Set ℕ) := by
    intro a ha b hb hab
    have haq : a < q := Finset.mem_range.mp
      (Finset.mem_filter.mp ha).1
    have hbq : b < q := Finset.mem_range.mp
      (Finset.mem_filter.mp hb).1
    have hmul : a * p ≡ b * p [MOD q] := by
      simpa only [Nat.ModEq] using hab
    have hcancel : a ≡ b [MOD q] :=
      hmul.cancel_right_of_coprime (by simpa [Nat.gcd_comm] using hpq.gcd_eq_one)
    simpa [Nat.ModEq, Nat.mod_eq_of_lt haq, Nat.mod_eq_of_lt hbq] using hcancel
  have himage : (twistedNearZeroResidues q p K).image f ⊆
      nearZeroResidues q K := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    rw [nearZeroResidues, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq), ?_⟩
    simpa [f, twistedNearZeroResidues] using (Finset.mem_filter.mp ha).2
  calc
    (twistedNearZeroResidues q p K).card =
        ((twistedNearZeroResidues q p K).image f).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (nearZeroResidues q K).card := Finset.card_le_card himage
    _ ≤ 2 * K := nearZeroResidues_card_le q K

/-- At most `2K` residue classes can land within `K/q` of zero after
multiplication by a reduced numerator; an initial interval contains at most
`(n+1)/q+1` copies of each such class. -/
lemma card_twistedNearZero_filter_le {A : Finset ℕ} {n q p K : ℕ}
    (hq : 0 < q) (hpq : p.Coprime q) (hA : A ⊆ Finset.Icc 1 n) :
    (A.filter fun a =>
      min ((a * p) % q) (q - (a * p) % q) < K).card ≤
      (2 * K) * ((n + 1) / q + 1) := by
  let B := twistedNearZeroResidues q p K
  let bad := A.filter fun a =>
    min ((a * p) % q) (q - (a * p) % q) < K
  have hsub : bad ⊆ Erdos387.modularPreimage (n + 1) q B := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Erdos387.modularPreimage, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (by
      have := (Finset.mem_Icc.mp (hA ha.1)).2
      omega), ?_⟩
    change a % q ∈ twistedNearZeroResidues q p K
    rw [twistedNearZeroResidues, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq), ?_⟩
    have hmod : ((a % q) * p) % q = (a * p) % q := by
      simp [Nat.mul_mod]
    simpa [hmod] using ha.2
  have hBlt : ∀ r ∈ B, r < q := by
    intro r hr
    exact Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  have hcount := Erdos387.card_modularPreimage (X := n + 1) hq B hBlt
  have hBcard : B.card ≤ 2 * K :=
    twistedNearZeroResidues_card_le hq hpq
  calc
    (A.filter fun a =>
        min ((a * p) % q) (q - (a * p) % q) < K).card = bad.card := rfl
    _ ≤ (Erdos387.modularPreimage (n + 1) q B).card :=
      Finset.card_le_card hsub
    _ = B.card * ((n + 1) / q) +
        (B.filter fun r => r < (n + 1) % q).card := hcount
    _ ≤ B.card * ((n + 1) / q) + B.card := by
      gcongr
      exact Finset.filter_subset (fun r => r < (n + 1) % q) B
    _ = B.card * ((n + 1) / q + 1) := by ring
    _ ≤ (2 * K) * ((n + 1) / q + 1) := by gcongr

/-- The distance of a rational grid point from the nearest integer is the
least absolute residue divided by its denominator. -/
lemma circleDist_nat_div (m q : ℕ) :
    circleDist ((m : ℝ) / q) =
      ((min (m % q) (q - m % q) : ℕ) : ℝ) / q := by
  rw [circleDist_eq_round, abs_sub_round_div_natCast_eq]

lemma circleDist_nat_mul_div (a p q : ℕ) :
    circleDist ((a : ℝ) * ((p : ℝ) / q)) =
      ((min ((a * p) % q) (q - (a * p) % q) : ℕ) : ℝ) / q := by
  rw [show (a : ℝ) * ((p : ℝ) / q) = ((a * p : ℕ) : ℝ) / q by
    norm_num; ring]
  exact circleDist_nat_div (a * p) q

/-- A Dirichlet approximation controls every dilate by an element of
`[1,n]`; this is the perturbative half of the grid argument. -/
lemma circleDist_mul_ge_grid_sub_error {a p q n : ℕ} {t δ : ℝ}
    (ha : a ≤ n) (happrox : |t - (p : ℝ) / q| ≤ δ) :
    ((min ((a * p) % q) (q - (a * p) % q) : ℕ) : ℝ) / q -
        (n : ℝ) * δ ≤ circleDist ((a : ℝ) * t) := by
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have han : (a : ℝ) ≤ n := by exact_mod_cast ha
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans happrox
  have hscaled :
      |(a : ℝ) * t - (a : ℝ) * ((p : ℝ) / q)| ≤ (n : ℝ) * δ := by
    calc
      |(a : ℝ) * t - (a : ℝ) * ((p : ℝ) / q)| =
          (a : ℝ) * |t - (p : ℝ) / q| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg ha0]
      _ ≤ (a : ℝ) * δ := mul_le_mul_of_nonneg_left happrox ha0
      _ ≤ (n : ℝ) * δ := mul_le_mul_of_nonneg_right han hδ0
  rw [← circleDist_nat_mul_div a p q]
  have hdist := circleDist_sub_abs_sub_le ((a : ℝ) * t)
    ((a : ℝ) * ((p : ℝ) / q))
  linarith

/-- Summing a pointwise circle-distance lower bound over a subfamily. -/
lemma circleEnergy_ge_card_mul_sq {A B : Finset ℕ} {t γ : ℝ}
    (hBA : B ⊆ A) (hγ : 0 ≤ γ)
    (hdist : ∀ a ∈ B, γ ≤ circleDist ((a : ℝ) * t)) :
    (B.card : ℝ) * γ ^ 2 ≤ circleEnergy A t := by
  rw [circleEnergy_eq_sum_circleDist_sq]
  calc
    (B.card : ℝ) * γ ^ 2 = ∑ _a ∈ B, γ ^ 2 := by simp
    _ ≤ ∑ a ∈ B, circleDist ((a : ℝ) * t) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact sq_le_sq₀ hγ (circleDist_nonneg _) |>.2 (hdist a ha)
    _ ≤ ∑ a ∈ A, circleDist ((a : ℝ) * t) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hBA
      intro a haA haB
      positivity

/-- Energy supplied by elements outside the zero residue class of a small
denominator. -/
lemma circleEnergy_ge_of_many_nonmultiples {A : Finset ℕ} {n h p q : ℕ}
    {t δ γ : ℝ} (hq : 0 < q) (hpq : p.Coprime q)
    (hA : A ⊆ Finset.Icc 1 n)
    (hmany : h ≤ (A.filter fun a => ¬q ∣ a).card)
    (happrox : |t - (p : ℝ) / q| ≤ δ) (hγ : 0 ≤ γ)
    (hmargin : γ + (n : ℝ) * δ ≤ 1 / q) :
    (h : ℝ) * γ ^ 2 ≤ circleEnergy A t := by
  let B := A.filter fun a => ¬q ∣ a
  have hBsub : B ⊆ A := Finset.filter_subset _ _
  have hdist : ∀ a ∈ B, γ ≤ circleDist ((a : ℝ) * t) := by
    intro a ha
    have haA := hA (hBsub ha)
    have haq : a ≤ n := (Finset.mem_Icc.mp haA).2
    have hqna : ¬q ∣ a := (Finset.mem_filter.mp ha).2
    have hresne : (a * p) % q ≠ 0 := by
      intro hz
      have hqd : q ∣ a * p := Nat.dvd_of_mod_eq_zero hz
      exact hqna (hpq.symm.dvd_of_dvd_mul_right hqd)
    have hreslt : (a * p) % q < q := Nat.mod_lt _ hq
    have hmin : 1 ≤ min ((a * p) % q) (q - (a * p) % q) := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hzero
      rcases min_eq_zero.mp hzero with hz | hz
      · exact hresne hz
      · omega
    have hgrid : (1 : ℝ) / q ≤
        ((min ((a * p) % q) (q - (a * p) % q) : ℕ) : ℝ) / q := by
      gcongr
      exact_mod_cast hmin
    have hpert := circleDist_mul_ge_grid_sub_error haq happrox
    linarith
  have henergy := circleEnergy_ge_card_mul_sq hBsub hγ hdist
  have hcard : (h : ℝ) ≤ B.card := by exact_mod_cast hmany
  exact (mul_le_mul_of_nonneg_right hcard (sq_nonneg γ)).trans henergy

/-- Energy supplied by all but the few rational grid points nearest zero. -/
lemma circleEnergy_ge_of_few_near_grid {A : Finset ℕ} {n x p q K : ℕ}
    {t δ γ : ℝ} (hq : 0 < q) (hpq : p.Coprime q)
    (hA : A ⊆ Finset.Icc 1 n) (hcard : A.card = x)
    (hbad : (2 * K) * ((n + 1) / q + 1) ≤ x / 2)
    (happrox : |t - (p : ℝ) / q| ≤ δ) (hγ : 0 ≤ γ)
    (hmargin : γ + (n : ℝ) * δ ≤ (K : ℝ) / q) :
    (x / 2 : ℕ) * γ ^ 2 ≤ circleEnergy A t := by
  let B := A.filter fun a =>
    K ≤ min ((a * p) % q) (q - (a * p) % q)
  let C := A.filter fun a =>
    min ((a * p) % q) (q - (a * p) % q) < K
  have hpartition : B ∪ C = A := by
    ext a
    simp only [Finset.mem_union, B, C, Finset.mem_filter]
    constructor
    · rintro (⟨ha, -⟩ | ⟨ha, -⟩) <;> exact ha
    · intro ha
      rcases le_or_gt K (min ((a * p) % q) (q - (a * p) % q)) with h | h
      · exact Or.inl ⟨ha, h⟩
      · exact Or.inr ⟨ha, h⟩
  have hdisj : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro a haB haC
    simp only [B, C, Finset.mem_filter] at haB haC
    omega
  have hCcard : C.card ≤ x / 2 := by
    exact (card_twistedNearZero_filter_le hq hpq hA).trans hbad
  have hBcard : x / 2 ≤ B.card := by
    have hsum : B.card + C.card = x := by
      rw [← hcard, ← hpartition, Finset.card_union_of_disjoint hdisj]
    omega
  have hBsub : B ⊆ A := Finset.filter_subset _ _
  have hdist : ∀ a ∈ B, γ ≤ circleDist ((a : ℝ) * t) := by
    intro a ha
    have haA := hA (hBsub ha)
    have haq : a ≤ n := (Finset.mem_Icc.mp haA).2
    have hmin : K ≤ min ((a * p) % q) (q - (a * p) % q) :=
      (Finset.mem_filter.mp ha).2
    have hgrid : (K : ℝ) / q ≤
        ((min ((a * p) % q) (q - (a * p) % q) : ℕ) : ℝ) / q := by
      gcongr
    have hpert := circleDist_mul_ge_grid_sub_error haq happrox
    linarith
  have henergy := circleEnergy_ge_card_mul_sq hBsub hγ hdist
  have hcardR : ((x / 2 : ℕ) : ℝ) ≤ B.card := by exact_mod_cast hBcard
  exact (mul_le_mul_of_nonneg_right hcardR (sq_nonneg γ)).trans henergy

/-- Dirichlet approximation, normalized to a positive reduced numerator and
denominator.  The endpoint hypotheses are exactly what is needed to keep the
approximant in `(0,1)`. -/
lemma exists_reduced_rational_approx {u : ℝ} {Q : ℕ} (hQ : 0 < Q)
    (hlow : 1 / ((Q : ℝ) + 1) < u)
    (hupp : u < 1 - 1 / ((Q : ℝ) + 1)) :
    ∃ p q : ℕ, 0 < q ∧ q ≤ Q ∧ p.Coprime q ∧ 0 < p ∧ p < q ∧
      |u - (p : ℝ) / q| ≤ 1 / (((Q : ℝ) + 1) * q) := by
  obtain ⟨r, herr, hrden⟩ := Real.exists_rat_abs_sub_le_and_den_le u hQ
  have hdenR : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hdenposR : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hQposR : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  have herrWeak : |u - (r : ℝ)| ≤ 1 / ((Q : ℝ) + 1) := by
    calc
      |u - (r : ℝ)| ≤ 1 / (((Q : ℝ) + 1) * r.den) := herr
      _ ≤ 1 / ((Q : ℝ) + 1) := by
        apply one_div_le_one_div_of_le hQposR
        nlinarith
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have := (abs_le.mp herrWeak).2
    linarith
  have hrlt : (r : ℝ) < 1 := by
    have := (abs_le.mp herrWeak).1
    linarith
  let p := r.num.natAbs
  let q := r.den
  have hnumpos : 0 < r.num :=
    Rat.num_pos.mpr ((Rat.cast_pos (K := ℝ)).mp hrpos)
  have hnumcast : (r.num : ℝ) = (p : ℝ) := by
    have hi : r.num = (p : ℤ) := by
      simpa [p] using (Int.natAbs_of_nonneg hnumpos.le).symm
    simpa using congrArg (fun z : ℤ => (z : ℝ)) hi
  have hcast : (r : ℝ) = (p : ℝ) / q := by
    rw [Rat.cast_def, hnumcast]
  have hp : 0 < p := by
    exact Int.natAbs_pos.mpr hnumpos.ne'
  have hpq : p < q := by
    have hpqR : (p : ℝ) < (q : ℝ) := by
      rw [← div_lt_one hdenposR, ← hcast]
      exact hrlt
    exact Nat.cast_lt.mp hpqR
  refine ⟨p, q, r.den_pos, hrden, ?_, hp, hpq, ?_⟩
  · simpa [p, q] using r.reduced
  · simpa [hcast, q] using herr

/- The large-denominator grid uses deliberately generous constants.  Keeping
these floor-sensitive estimates separate makes the analytic theorem below
readable. -/
lemma largeGrid_bad_count {n x q : ℕ} (hq : 0 < q) (hqQ : q ≤ 1000 * n) :
    let K := (q * x) / (64 * 1001 * (n + 1))
    (2 * K) * ((n + 1) / q + 1) ≤ x / 2 := by
  dsimp only
  let K := (q * x) / (64 * 1001 * (n + 1))
  let d := (n + 1) / q + 1
  have hqdiv : q * ((n + 1) / q) ≤ n + 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n + 1) q
  have hqd : q * d ≤ 1001 * (n + 1) := by
    dsimp only [d]
    have hqn : q ≤ 1000 * (n + 1) := hqQ.trans (by omega)
    calc
      q * ((n + 1) / q + 1) = q * ((n + 1) / q) + q := by ring
      _ ≤ (n + 1) + q := Nat.add_le_add_right hqdiv q
      _ ≤ 1001 * (n + 1) := by omega
  have hK : K * (64 * 1001 * (n + 1)) ≤ q * x := by
    dsimp only [K]
    exact Nat.div_mul_le_self _ _
  have hmul := Nat.mul_le_mul_right d hK
  have hmul' := Nat.mul_le_mul_right x hqd
  have hpos : 0 < 1001 * (n + 1) := by positivity
  have h64 : 64 * (K * d) ≤ x := by
    apply Nat.le_of_mul_le_mul_right (c := 1001 * (n + 1))
    · calc
      (64 * (K * d)) * (1001 * (n + 1)) =
          (K * (64 * 1001 * (n + 1))) * d := by ring
      _ ≤ (q * x) * d := hmul
      _ = (q * d) * x := by ring
      _ ≤ (1001 * (n + 1)) * x := hmul'
      _ = x * (1001 * (n + 1)) := by ring
    · exact hpos
  have hfour : 4 * (K * d) ≤ x := by nlinarith
  dsimp only [K, d] at hfour ⊢
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
  nlinarith

lemma largeGrid_margin {n x q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hlarge : 256 * 1001 * (n + 1) ≤ q * x) :
    let K := (q * x) / (64 * 1001 * (n + 1))
    (x : ℝ) / (512 * 1001 * (n + 1)) +
        (n : ℝ) * (1 / (((1000 * n : ℕ) : ℝ) + 1) / q) ≤
      (K : ℝ) / q := by
  dsimp only
  let D : ℕ := 64 * 1001 * (n + 1)
  let K : ℕ := (q * x) / D
  have hD : 0 < D := by positivity
  have hrem : (q * x) % D < D := Nat.mod_lt _ hD
  have hdecomp : (q * x) % D + D * K = q * x := by
    simpa [K, Nat.mul_comm] using (Nat.mod_add_div (q * x) D)
  have hfloor : q * x < (K + 1) * D := by
    calc
      q * x = (q * x) % D + D * K := hdecomp.symm
      _ < D + D * K := Nat.add_lt_add_right hrem _
      _ = (K + 1) * D := by ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hfloorR : (q : ℝ) * x < ((K : ℝ) + 1) * D := by
    exact_mod_cast hfloor
  have hKlower : (q : ℝ) * x / D - 1 < K := by
    have := (div_lt_iff₀ hDR).2 hfloorR
    linarith
  have hKq : (x : ℝ) / D - 1 / q < (K : ℝ) / q := by
    calc
      (x : ℝ) / D - 1 / q =
          ((q : ℝ) * x / D - 1) / q := by field_simp
      _ < (K : ℝ) / q := div_lt_div_of_pos_right hKlower hqR
  have hlargeR : (256 * 1001 * (n + 1) : ℝ) ≤ (q : ℝ) * x := by
    exact_mod_cast hlarge
  have hinvq : 1 / (q : ℝ) ≤
      (x : ℝ) / (256 * 1001 * (n + 1)) := by
    rw [div_le_div_iff₀ hqR (by positivity : (0 : ℝ) < 256 * 1001 * (n + 1))]
    nlinarith
  have herr : (n : ℝ) *
      (1 / (((1000 * n : ℕ) : ℝ) + 1) / q) ≤ 1 / q := by
    have hA : (0 : ℝ) < ((1000 * n : ℕ) : ℝ) + 1 := by positivity
    have hnA : (n : ℝ) / (((1000 * n : ℕ) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hA]
      push_cast
      nlinarith
    calc
      (n : ℝ) * (1 / (((1000 * n : ℕ) : ℝ) + 1) / q) =
          ((n : ℝ) / (((1000 * n : ℕ) : ℝ) + 1)) / q := by ring
      _ ≤ 1 / q := div_le_div_of_nonneg_right hnA hqR.le
  have hDcast : (D : ℝ) = 64 * 1001 * (n + 1) := by
    norm_num [D]
  rw [hDcast] at hKq
  have hmain : (x : ℝ) / (512 * 1001 * (n + 1)) + 1 / q ≤
      (x : ℝ) / (64 * 1001 * (n + 1)) - 1 / q := by
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hx0 : (0 : ℝ) ≤ x := by positivity
    have ha0 : 0 ≤ (x : ℝ) / (512 * 1001 * (n + 1)) := by positivity
    have hrewrite : (x : ℝ) / (256 * 1001 * (n + 1)) =
        2 * ((x : ℝ) / (512 * 1001 * (n + 1))) := by field_simp; ring
    have hrewrite64 : (x : ℝ) / (64 * 1001 * (n + 1)) =
        8 * ((x : ℝ) / (512 * 1001 * (n + 1))) := by field_simp; ring
    rw [hrewrite] at hinvq
    rw [hrewrite64]
    nlinarith
  calc
    (x : ℝ) / (512 * 1001 * (n + 1)) +
        (n : ℝ) * (1 / (((1000 * n : ℕ) : ℝ) + 1) / q) ≤
        (x : ℝ) / (512 * 1001 * (n + 1)) + 1 / q :=
      by simpa [add_comm] using
        (add_le_add_left herr ((x : ℝ) / (512 * 1001 * (n + 1))))
    _ ≤ (x : ℝ) / (64 * 1001 * (n + 1)) - 1 / q := hmain
    _ ≤ (K : ℝ) / q := hKq.le

lemma smallGrid_margin {n x q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hsmall : q * x < 256 * 1001 * (n + 1)) :
    (x : ℝ) / (512 * 1001 * (n + 1)) +
        (n : ℝ) * (1 / (((1000 * n : ℕ) : ℝ) + 1) / q) ≤
      1 / q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmallR : (q : ℝ) * x < 256 * 1001 * (n + 1) := by
    exact_mod_cast hsmall
  have hfirst : (x : ℝ) / (512 * 1001 * (n + 1)) ≤ 1 / (2 * q) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 512 * 1001 * (n + 1))
      (by positivity : (0 : ℝ) < 2 * q)]
    nlinarith
  have hA : (0 : ℝ) < ((1000 * n : ℕ) : ℝ) + 1 := by positivity
  have hnA : (n : ℝ) / (((1000 * n : ℕ) : ℝ) + 1) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ hA (by norm_num : (0 : ℝ) < 1000)]
    push_cast
    nlinarith
  have herr : (n : ℝ) *
      (1 / (((1000 * n : ℕ) : ℝ) + 1) / q) ≤ 1 / (1000 * q) := by
    calc
      (n : ℝ) * (1 / (((1000 * n : ℕ) : ℝ) + 1) / q) =
          ((n : ℝ) / (((1000 * n : ℕ) : ℝ) + 1)) / q := by ring
      _ ≤ (1 / 1000) / q := div_le_div_of_nonneg_right hnA hqR.le
      _ = 1 / (1000 * q) := by ring
  calc
    (x : ℝ) / (512 * 1001 * (n + 1)) +
        (n : ℝ) * (1 / (((1000 * n : ℕ) : ℝ) + 1) / q) ≤
        1 / (2 * q) + 1 / (1000 * q) := add_le_add hfirst herr
    _ ≤ 1 / q := by
      field_simp
      nlinarith

/-- Quantitative minor-arc energy.  The only structural hypothesis says that
every sufficiently small modulus misses at least `h` members of `A`. -/
lemma circleEnergy_minorArc_lower {A : Finset ℕ} {n x h : ℕ}
    (hn : 0 < n) (hA : A ⊆ Finset.Icc 1 n) (hcard : A.card = x)
    (hh : h ≤ x / 2)
    (hsparse : ∀ q : ℕ, 2 ≤ q →
      q * x < 256 * 1001 * (n + 1) →
      h ≤ (A.filter fun a => ¬q ∣ a).card)
    {t : ℝ} (htlow : 1 / (1000 * n) ≤ |t|) (htupp : |t| ≤ 1 / 2) :
    (h : ℝ) * ((x : ℝ) / (512 * 1001 * (n + 1))) ^ 2 ≤
      circleEnergy A t := by
  let Q := 1000 * n
  have hQ : 0 < Q := by positivity
  have hQcast : (Q : ℝ) = 1000 * n := by simp [Q]
  have hlow : 1 / ((Q : ℝ) + 1) < |t| := by
    apply lt_of_lt_of_le _ htlow
    rw [hQcast]
    apply one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 1000 * n)
    norm_num
  have hupp : |t| < 1 - 1 / ((Q : ℝ) + 1) := by
    apply htupp.trans_lt
    rw [hQcast]
    have hden : (2 : ℝ) < 1000 * n + 1 := by
      exact_mod_cast (show 2 < 1000 * n + 1 by omega)
    have hinv : 1 / (1000 * (n : ℝ) + 1) < 1 / 2 := by
      exact one_div_lt_one_div_of_lt (by norm_num) hden
    linarith
  obtain ⟨p, q, hq, hqQ, hpq, hp, hp_lt_q, happrox⟩ :=
    exists_reduced_rational_approx hQ hlow hupp
  have hq2 : 2 ≤ q := by omega
  let δ : ℝ := 1 / (((Q : ℝ) + 1) * q)
  let γ : ℝ := (x : ℝ) / (512 * 1001 * (n + 1))
  have hγ0 : 0 ≤ γ := by positivity
  have happrox' : |(|t|) - (p : ℝ) / q| ≤ δ := by
    simpa [δ] using happrox
  have hdelta : δ = 1 / ((((1000 * n : ℕ) : ℝ) + 1) * q) := by
    simp [δ, Q]
  rw [← circleEnergy_abs A t]
  by_cases hsmall : q * x < 256 * 1001 * (n + 1)
  · apply circleEnergy_ge_of_many_nonmultiples hq hpq hA
      (hsparse q hq2 hsmall) happrox' hγ0
    rw [hdelta]
    simpa [γ, div_eq_mul_inv, mul_comm] using smallGrid_margin hn hq hsmall
  · have hlarge : 256 * 1001 * (n + 1) ≤ q * x := Nat.le_of_not_gt hsmall
    let K := (q * x) / (64 * 1001 * (n + 1))
    have hq1000 : q ≤ 1000 * n := by simpa [Q] using hqQ
    have hbad : (2 * K) * ((n + 1) / q + 1) ≤ x / 2 :=
      largeGrid_bad_count hq hq1000
    have hlargeEnergy := circleEnergy_ge_of_few_near_grid hq hpq hA hcard
      hbad happrox' hγ0
    have hmargin : γ + (n : ℝ) * δ ≤ (K : ℝ) / q := by
      rw [hdelta]
      simpa [γ, K, div_eq_mul_inv, mul_comm] using largeGrid_margin hn hq hlarge
    have hE := hlargeEnergy hmargin
    have hhR : (h : ℝ) ≤ (x / 2 : ℕ) := by exact_mod_cast hh
    exact (mul_le_mul_of_nonneg_right hhR (sq_nonneg γ)).trans hE

/-- The tiny central arc used in the positivity argument. -/
noncomputable def coreRadius (n x : ℕ) : ℝ :=
  1 / (1000000 * n * (x + 1))

/-- The explicit energy furnished by `circleEnergy_minorArc_lower`. -/
noncomputable def minorEnergy (n x h : ℕ) : ℝ :=
  (h : ℝ) * ((x : ℝ) / (512 * 1001 * (n + 1))) ^ 2

/-- Local subset-sum representation under the finite nonconcentration
hypothesis.  All analytic estimates are now explicit; `hdecay` is a single
numerical inequality that will be discharged asymptotically. -/
lemma mem_subsetSum_of_sparse {A : Finset ℕ} {n x h M : ℕ}
    (hn : 0 < n) (hA : A ⊆ Finset.Icc 1 n) (hcard : A.card = x)
    (hh : h ≤ x / 2)
    (hsparse : ∀ q : ℕ, 2 ≤ q →
      q * x < 256 * 1001 * (n + 1) →
      h ≤ (A.filter fun a => ¬q ∣ a).card)
    (hcenter : |(((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M)| ≤ 100 * n)
    (hdecay : Real.exp (-minorEnergy n x h) < 3 * coreRadius n x / 4) :
    M ∈ A.subsetSum := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hxle : x ≤ n := by
    rw [← hcard]
    exact (Finset.card_le_card hA).trans (by simp)
  have hxR : (0 : ℝ) ≤ x := by positivity
  have hxpR : (0 : ℝ) < (x : ℝ) + 1 := by positivity
  have hrho : 0 < coreRadius n x := by
    simp only [coreRadius]
    positivity
  apply mem_subsetSum_of_minorArcEnergy hn hA hrho
  · simp only [coreRadius]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 1000000 * n * (x + 1))
      (by positivity : (0 : ℝ) < 1000 * n)]
    nlinarith
  · have hV := varianceMass_le_card_mul_sq hA
    rw [hcard] at hV
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hpi0 : 0 < Real.pi := Real.pi_pos
    have hpiSq : Real.pi ^ 2 ≤ 16 := by nlinarith [sq_nonneg (Real.pi - 4)]
    simp only [coreRadius]
    have hden : (0 : ℝ) < 1000000 * n * (x + 1) := by positivity
    rw [one_div, inv_pow]
    have hx1 : (x : ℝ) ≤ (x + 1) ^ 2 := by nlinarith [sq_nonneg (x : ℝ)]
    calc
      2 * Real.pi ^ 2 * varianceMass A *
          ((1000000 * (n : ℝ) * (x + 1)) ^ 2)⁻¹ ≤
          2 * 16 * ((x : ℝ) * n ^ 2 / 4) *
            ((1000000 * (n : ℝ) * (x + 1)) ^ 2)⁻¹ := by
              gcongr
              exact varianceMass_nonneg A
      _ ≤ 1 / 4 := by
        rw [inv_eq_one_div]
        field_simp
        nlinarith
  · simp only [coreRadius]
    calc
      2 * Real.pi * |(((∑ a ∈ A, a : ℕ) : ℝ) / 2 - M)| *
          (1 / (1000000 * n * (x + 1))) ≤
          2 * Real.pi * (100 * n : ℝ) *
            (1 / (1000000 * n * (x + 1))) := by
            gcongr
      _ ≤ 1 := by
        have hpi := Real.pi_lt_four
        have hxone : (1 : ℝ) ≤ (x : ℝ) + 1 := by nlinarith
        field_simp
        nlinarith
  · exact hcenter
  · intro t htI ht
    have htupp : |t| ≤ (1 : ℝ) / 2 := by
      apply abs_le.mpr
      exact ⟨by linarith [htI.1], htI.2⟩
    exact circleEnergy_minorArc_lower hn hA hcard hh hsparse ht
      htupp
  · exact hdecay

/-- A standard cardinality estimate for a finite map with uniformly bounded
fibers. -/
lemma card_le_image_card_mul_of_fiber_bound {α β : Type*}
    [DecidableEq α] [DecidableEq β] (S : Finset α) (f : α → β) (D : ℕ)
    (hfiber : ∀ b ∈ S.image f, (S.filter fun a => f a = b).card ≤ D) :
    S.card ≤ (S.image f).card * D := by
  rw [Finset.card_eq_sum_card_fiberwise (t := S.image f) (f := f) (by
    intro a ha
    exact Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨a, Finset.mem_coe.mp ha, rfl⟩))]
  calc
    ∑ b ∈ S.image f, (S.filter fun a => f a = b).card ≤
        ∑ _b ∈ S.image f, D := Finset.sum_le_sum fun b hb => hfiber b hb
    _ = (S.image f).card * D := by simp

/-! ## Finite divisor adjustment

The Alon--Freiman argument naturally maintains an interval in one residue
progression.  The following predicate records that invariant without any
division or coercions. -/

/-- Every multiple of `q` in the closed interval `[L,U]` is a subset sum. -/
def CoversMultiples (D : Finset ℕ) (q L U : ℕ) : Prop :=
  ∀ M : ℕ, L ≤ M → M ≤ U → q ∣ M → M ∈ D.subsetSum

lemma CoversMultiples.mono_set {D E : Finset ℕ} {q L U : ℕ}
    (h : CoversMultiples D q L U) (hDE : D ⊆ E) :
    CoversMultiples E q L U := by
  intro M hLM hMU hqM
  exact Finset.subsetSum_mono hDE (h M hLM hMU hqM)

lemma CoversMultiples.shrink {D : Finset ℕ} {q L U L' U' : ℕ}
    (h : CoversMultiples D q L U) (hL : L ≤ L') (hU : U' ≤ U) :
    CoversMultiples D q L' U' := by
  intro M hL'M hMU' hqM
  exact h M (hL.trans hL'M) (hMU'.trans hU) hqM

/-- Divide a finite set by a common positive divisor. -/
def quotientPart (q : ℕ) (D : Finset ℕ) : Finset ℕ :=
  D.image fun d => d / q

lemma image_mul_quotientPart {D : Finset ℕ} {q : ℕ} (hq : 0 < q)
    (hdiv : ∀ d ∈ D, q ∣ d) :
    (quotientPart q D).image (fun d => q * d) = D := by
  ext d
  constructor
  · intro hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    simpa [Nat.mul_div_cancel' (hdiv a ha)] using ha
  · intro hd
    apply Finset.mem_image.mpr
    refine ⟨d / q, Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
    exact Nat.mul_div_cancel' (hdiv d hd)

lemma card_quotientPart {D : Finset ℕ} {q : ℕ} (hq : 0 < q)
    (hdiv : ∀ d ∈ D, q ∣ d) :
    (quotientPart q D).card = D.card := by
  rw [quotientPart]
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  change a / q = b / q at hab
  calc
    a = q * (a / q) := (Nat.mul_div_cancel' (hdiv a ha)).symm
    _ = q * (b / q) := congrArg (q * ·) hab
    _ = b := Nat.mul_div_cancel' (hdiv b hb)

lemma quotientPart_subset_Icc {D : Finset ℕ} {q n : ℕ} (hq : 0 < q)
    (hD : D ⊆ Finset.Icc 1 n) (hdiv : ∀ d ∈ D, q ∣ d) :
    quotientPart q D ⊆ Finset.Icc 1 n := by
  intro a ha
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
  have hdI := Finset.mem_Icc.mp (hD hd)
  have hqle : q ≤ d := Nat.le_of_dvd hdI.1 (hdiv d hd)
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.div_pos hqle hq)),
      (Nat.div_le_self d q).trans hdI.2⟩

lemma mem_subsetSum_of_quotientPart {D : Finset ℕ} {q x : ℕ}
    (hq : 0 < q) (hdiv : ∀ d ∈ D, q ∣ d)
    (hx : x ∈ (quotientPart q D).subsetSum) :
    q * x ∈ D.subsetSum := by
  rw [← image_mul_quotientPart hq hdiv,
    Erdos469.subsetSum_image_mul_left hq]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

lemma subsetSum_add_of_disjoint {D C : Finset ℕ} (hdisj : Disjoint D C)
    {x y : ℕ} (hx : x ∈ D.subsetSum) (hy : y ∈ C.subsetSum) :
    x + y ∈ (D ∪ C).subsetSum := by
  rw [Erdos469.subsetSum_union_eq_add_of_disjoint hdisj]
  exact Finset.mem_add.mpr ⟨x, hx, y, hy, rfl⟩

/-- A set of `k` integers in one residue class supplies a bounded correction
for every element of the subgroup generated by that residue. -/
lemma exists_bounded_residue_correction {C : Finset ℕ} {k r n M : ℕ}
    (hk : 0 < k) (hr : r < k) (hcard : C.card = k)
    (hC : C ⊆ Finset.Icc 1 n) (hres : ∀ c ∈ C, c % k = r)
    (hdiv : Nat.gcd k r ∣ M) :
    ∃ v ∈ C.subsetSum, v ≤ k * n ∧ v ≡ M [MOD k] := by
  let d := Nat.gcd k r
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left r hk
  have hdk : d ≤ k := Nat.gcd_le_left r hk
  by_cases hdeq : d = k
  · change d ∣ M at hdiv
    rw [hdeq] at hdiv
    have hMk : k ∣ M := hdiv
    refine ⟨0, Finset.zero_mem_subsetSum, by simp, ?_⟩
    exact Nat.ModEq.symm (Nat.modEq_zero_iff_dvd.mpr hMk)
  · have hdlt : d < k := lt_of_le_of_ne hdk hdeq
    obtain ⟨z, hz⟩ := hdiv
    have hdlt' : Nat.gcd r k < k := by simpa [d, Nat.gcd_comm] using hdlt
    obtain ⟨c, _hc, hc⟩ := Nat.exists_mul_mod_eq_gcd
      (k := k) (n := r) hdlt'
    let j := (c * z) % k
    have hj : j < k := Nat.mod_lt _ hk
    obtain ⟨T, hTC, hTcard⟩ := Finset.exists_subset_card_eq
      (s := C) (n := j) (by simpa [hcard] using hj.le)
    let v := ∑ a ∈ T, a
    have hvle : v ≤ k * n := by
      calc
        v ≤ ∑ _a ∈ T, n := Finset.sum_le_sum fun a ha =>
          (Finset.mem_Icc.mp (hC (hTC ha))).2
        _ = T.card * n := by simp
        _ ≤ k * n := Nat.mul_le_mul_right n (by simpa [hTcard] using hj.le)
    have hsumCong : v ≡ T.card * r [MOD k] := by
      dsimp only [v]
      convert Nat.ModEq.sum (s := T) (fun a ha =>
        (show a ≡ r [MOD k] by
          simpa [Nat.ModEq, Nat.mod_eq_of_lt hr] using hres a (hTC ha))) using 1
      simp [Nat.mul_comm]
    have hcCong : r * c ≡ d [MOD k] := by
      rw [Nat.ModEq]
      simpa [d, Nat.gcd_comm, Nat.mod_eq_of_lt hdlt] using hc
    have hjCong : j * r ≡ d * z [MOD k] := by
      have hmod : j ≡ c * z [MOD k] := Nat.mod_modEq (c * z) k
      calc
        j * r ≡ (c * z) * r [MOD k] := hmod.mul_right r
        _ = (r * c) * z := by ring
        _ ≡ d * z [MOD k] := hcCong.mul_right z
    refine ⟨v, Finset.mem_subsetSum_iff.mpr ⟨T, hTC, rfl⟩, hvle, ?_⟩
    have hcardCong : T.card * r ≡ M [MOD k] := by
      rw [hTcard]
      simpa [j, hz] using hjCong
    exact hsumCong.trans hcardCong

/-- One residue block lowers the modulus from `k` to `gcd k r`, at the
cost of moving the lower endpoint by at most `k*n`. -/
lemma CoversMultiples.adjust_residue_block {A D C : Finset ℕ}
    {n k r L U : ℕ} (hk : 0 < k) (hr : r < k)
    (hA : A ⊆ Finset.Icc 1 n) (hD : D ⊆ A) (hC : C ⊆ A)
    (hdisj : Disjoint D C) (hCcard : C.card = k)
    (hres : ∀ c ∈ C, c % k = r)
    (hcover : CoversMultiples D k L U) :
    CoversMultiples (D ∪ C) (Nat.gcd k r) (L + k * n) U := by
  intro M hLM hMU hdM
  obtain ⟨v, hvC, hvle, hvM⟩ := exists_bounded_residue_correction
    hk hr hCcard (hC.trans hA) hres hdM
  have hvMdiv : k ∣ M - v := by
    exact (Nat.modEq_iff_dvd' (hvle.trans (by omega))).mp hvM
  have hvMle : v ≤ M := hvle.trans (by omega)
  have hlow : L ≤ M - v := by omega
  have hupp : M - v ≤ U := (Nat.sub_le M v).trans hMU
  have hbase := hcover (M - v) hlow hupp hvMdiv
  have hadd := subsetSum_add_of_disjoint hdisj hbase hvC
  simpa [Nat.sub_add_cancel hvMle] using hadd

/-- If at least `k^2` elements are nonmultiples of `k`, one nonzero residue
class contains a `k`-element block. -/
lemma exists_large_nonzero_residue_block {A : Finset ℕ} {k : ℕ}
    (hk : 0 < k)
    (hlarge : k ^ 2 ≤ (A.filter fun a => ¬k ∣ a).card) :
    ∃ r : ℕ, ∃ C : Finset ℕ, 0 < r ∧ r < k ∧
      C ⊆ A.filter (fun a => ¬k ∣ a) ∧ C.card = k ∧
      ∀ c ∈ C, c % k = r := by
  let R := A.filter fun a => ¬k ∣ a
  have hk2 : 2 ≤ k := by
    by_contra hnot
    have hkone : k = 1 := by omega
    subst k
    simp at hlarge
  let f : ℕ → ℕ := fun a => a % k
  have himage : R.image f ⊆ Finset.Ico 1 k := by
    intro r hr
    obtain ⟨a, haR, rfl⟩ := Finset.mem_image.mp hr
    have ha := Finset.mem_filter.mp haR
    have hne : a % k ≠ 0 := by
      intro hz
      exact ha.2 (Nat.dvd_of_mod_eq_zero hz)
    exact Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne,
      Nat.mod_lt a hk⟩
  have hexists : ∃ r ∈ R.image f,
      k ≤ (R.filter fun a => f a = r).card := by
    by_contra hnot
    push Not at hnot
    have hfiber : ∀ r ∈ R.image f,
        (R.filter fun a => f a = r).card ≤ k - 1 := by
      intro r hr
      have hlt := hnot r hr
      omega
    have hcardR := card_le_image_card_mul_of_fiber_bound R f (k - 1) hfiber
    have himageCard : (R.image f).card ≤ k - 1 := by
      calc
        (R.image f).card ≤ (Finset.Ico 1 k).card := Finset.card_le_card himage
        _ = k - 1 := by simp
    have hupper : R.card ≤ (k - 1) ^ 2 := by
      calc
        R.card ≤ (R.image f).card * (k - 1) := hcardR
        _ ≤ (k - 1) * (k - 1) := Nat.mul_le_mul_right _ himageCard
        _ = (k - 1) ^ 2 := by ring
    have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    have hstrict : (k - 1) ^ 2 < k ^ 2 := by nlinarith
    exact (Nat.not_lt_of_ge hlarge) (hupper.trans_lt hstrict)
  obtain ⟨r, hrImage, hrFiber⟩ := hexists
  obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hrFiber
  have hrIco := Finset.mem_Ico.mp (himage hrImage)
  refine ⟨r, C, hrIco.1, hrIco.2, ?_, hCcard, ?_⟩
  · exact hCsub.trans (Finset.filter_subset _ _)
  · intro c hc
    exact (Finset.mem_filter.mp (hCsub hc)).2

/-- Repeated residue adjustment terminates at a divisor with fewer than its
square many exceptional elements.  The total number of elements adjoined is
at most `2*k`, and a uniform lower-end loss `2*k*n` pays for every step. -/
lemma exists_stable_progression {A D : Finset ℕ} {n k L U : ℕ}
    (hk : 0 < k) (hA : A ⊆ Finset.Icc 1 n) (hDA : D ⊆ A)
    (hDdiv : ∀ d ∈ D, k ∣ d) (hcover : CoversMultiples D k L U) :
    ∃ q E, 0 < q ∧ q ∣ k ∧ D ⊆ E ∧ E ⊆ A ∧
      E.card ≤ D.card + 2 * k ∧ (∀ e ∈ E, q ∣ e) ∧
      (A.filter fun a => ¬q ∣ a).card < q ^ 2 ∧
      CoversMultiples E q (L + 2 * k * n) U := by
  induction k using Nat.strong_induction_on generalizing D L with
  | h k ih =>
      by_cases hstable : (A.filter fun a => ¬k ∣ a).card < k ^ 2
      · refine ⟨k, D, hk, dvd_rfl, Finset.Subset.rfl, hDA, by omega,
          hDdiv, hstable, ?_⟩
        exact hcover.shrink (by omega) le_rfl
      · have hlarge : k ^ 2 ≤ (A.filter fun a => ¬k ∣ a).card :=
          Nat.le_of_not_gt hstable
        obtain ⟨r, C, hrpos, hrk, hCout, hCcard, hCres⟩ :=
          exists_large_nonzero_residue_block hk hlarge
        let d := Nat.gcd k r
        have hdpos : 0 < d := Nat.gcd_pos_of_pos_right k hrpos
        have hdvdK : d ∣ k := Nat.gcd_dvd_left k r
        have hdvdR : d ∣ r := Nat.gcd_dvd_right k r
        have hdlt : d < k :=
          (Nat.gcd_le_right k hrpos).trans_lt hrk
        have hdhalf : 2 * d ≤ k := by
          obtain ⟨z, hz⟩ := hdvdK
          have hz2 : 2 ≤ z := by
            by_contra hznot
            have hzle : z ≤ 1 := by omega
            interval_cases z <;> simp_all
          rw [hz]
          nlinarith
        have hCA : C ⊆ A := hCout.trans (Finset.filter_subset _ _)
        have hdisj : Disjoint D C := by
          rw [Finset.disjoint_left]
          intro a haD haC
          have haOut := (Finset.mem_filter.mp (hCout haC)).2
          exact haOut (hDdiv a haD)
        have hUnionDiv : ∀ a ∈ D ∪ C, d ∣ a := by
          intro a ha
          rcases Finset.mem_union.mp ha with haD | haC
          · exact hdvdK.trans (hDdiv a haD)
          · have hmod : a ≡ r [MOD k] := by
              simpa [Nat.ModEq, Nat.mod_eq_of_lt hrk] using hCres a haC
            have hmodD : a ≡ r [MOD d] := hmod.of_dvd hdvdK
            have hrzero : r ≡ 0 [MOD d] :=
              Nat.modEq_zero_iff_dvd.mpr hdvdR
            exact Nat.modEq_zero_iff_dvd.mp (hmodD.trans hrzero)
        have hAdjust : CoversMultiples (D ∪ C) d (L + k * n) U :=
          hcover.adjust_residue_block hk hrk hA hDA hCA hdisj hCcard hCres
        obtain ⟨q, E, hqpos, hqd, hDE, hEA, hEcard, hEdiv,
            hEstable, hEcover⟩ :=
          ih d hdlt hdpos (Finset.union_subset hDA hCA) hUnionDiv hAdjust
        refine ⟨q, E, hqpos, hqd.trans hdvdK,
          (Finset.subset_union_left.trans hDE), hEA, ?_, hEdiv,
          hEstable, ?_⟩
        · calc
            E.card ≤ (D ∪ C).card + 2 * d := hEcard
            _ ≤ (D.card + C.card) + 2 * d := by
              gcongr
              exact Finset.card_union_le D C
            _ ≤ D.card + 2 * k := by rw [hCcard]; omega
        · apply hEcover.shrink
          · calc
              (L + k * n) + 2 * d * n =
                  L + (k * n + (2 * d) * n) := by ring
              _ ≤ L + (k * n + k * n) := by
                gcongr
              _ = L + 2 * k * n := by ring
          · exact le_rfl

/-! ## Maximal-divisor extraction -/

/-- Elements of `S` divisible by `q`. -/
def divisiblePart (S : Finset ℕ) (q : ℕ) : Finset ℕ :=
  S.filter fun a => q ∣ a

/-- The loss budget used while accumulating divisors. -/
def GoodDivisor (S : Finset ℕ) (h q : ℕ) : Prop :=
  0 < q ∧ S.card ≤ (divisiblePart S q).card + h * Nat.log 2 q

local instance decidableGoodDivisor (S : Finset ℕ) (h : ℕ) :
    DecidablePred (GoodDivisor S h) := fun _ => Classical.propDecidable _

/-- The largest divisor not exceeding `n` which respects the logarithmic
loss budget. -/
noncomputable def extractionDivisor (S : Finset ℕ) (n h : ℕ) : ℕ :=
  Nat.findGreatest (GoodDivisor S h) n

lemma goodDivisor_one (S : Finset ℕ) (h : ℕ) : GoodDivisor S h 1 := by
  simp [GoodDivisor, divisiblePart]

lemma extractionDivisor_spec {S : Finset ℕ} {n h : ℕ} (hn : 1 ≤ n) :
    GoodDivisor S h (extractionDivisor S n h) := by
  exact Nat.findGreatest_spec (m := 1) hn (goodDivisor_one S h)

lemma extractionDivisor_pos {S : Finset ℕ} {n h : ℕ} (hn : 1 ≤ n) :
    0 < extractionDivisor S n h :=
  (extractionDivisor_spec hn).1

lemma extractionDivisor_le (S : Finset ℕ) (n h : ℕ) :
    extractionDivisor S n h ≤ n := Nat.findGreatest_le n

lemma quotient_filter_divisible_card {S : Finset ℕ} {k q : ℕ}
    (hk : 0 < k) :
    ((quotientPart k (divisiblePart S k)).filter fun b => q ∣ b).card =
      (divisiblePart S (k * q)).card := by
  let D := divisiblePart S k
  have hDdiv : ∀ d ∈ D, k ∣ d := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2
  rw [quotientPart, Finset.filter_image]
  rw [Finset.card_image_iff.mpr]
  · congr 1
    ext a
    simp only [Finset.mem_filter, divisiblePart, D]
    constructor
    · rintro ⟨⟨haS, hka⟩, hqa⟩
      exact ⟨haS, (Nat.dvd_div_iff_mul_dvd hka).mp hqa⟩
    · rintro ⟨haS, hkqa⟩
      have hka : k ∣ a := dvd_mul_right k q |>.trans hkqa
      exact ⟨⟨haS, hka⟩,
        (Nat.dvd_div_iff_mul_dvd hka).mpr hkqa⟩
  · intro a ha b hb hab
    change a / k = b / k at hab
    calc
      a = k * (a / k) :=
        (Nat.mul_div_cancel' (hDdiv a (Finset.mem_filter.mp ha).1)).symm
      _ = k * (b / k) := congrArg (k * ·) hab
      _ = b := Nat.mul_div_cancel'
        (hDdiv b (Finset.mem_filter.mp hb).1)

lemma extractionDivisor_sparse {S : Finset ℕ} {n h : ℕ}
    (hn : 1 ≤ n) (hhpos : 0 < h)
    (hS : S ⊆ Finset.Icc 1 n)
    (hbudget : h * Nat.log 2 n + h ≤ S.card) :
    let k := extractionDivisor S n h
    let B := quotientPart k (divisiblePart S k)
    ∀ q : ℕ, 2 ≤ q → h ≤ (B.filter fun b => ¬q ∣ b).card := by
  dsimp only
  let k := extractionDivisor S n h
  let D := divisiblePart S k
  let B := quotientPart k D
  have hkpos : 0 < k := extractionDivisor_pos hn
  have hkle : k ≤ n := extractionDivisor_le S n h
  have hgood : GoodDivisor S h k := extractionDivisor_spec hn
  have hlogle : Nat.log 2 k ≤ Nat.log 2 n := Nat.log_mono_right hkle
  have hDcard : D.card + h * Nat.log 2 k =
      B.card + h * Nat.log 2 k := by
    rw [card_quotientPart hkpos]
    intro d hd
    exact (Finset.mem_filter.mp hd).2
  intro q hq
  by_contra hnot
  have hnotlt : (B.filter fun b => ¬q ∣ b).card < h :=
    Nat.lt_of_not_ge hnot
  let Bq := B.filter fun b => q ∣ b
  have hsplit : Bq.card + (B.filter fun b => ¬q ∣ b).card = B.card := by
    simpa [Bq] using Finset.card_filter_add_card_filter_not
      (s := B) (p := fun b => q ∣ b)
  have hBqpos : 0 < Bq.card := by
    have hretain : h ≤ B.card := by
      have hlogBudget : h * Nat.log 2 k + h ≤ S.card :=
        (Nat.add_le_add_right (Nat.mul_le_mul_left h hlogle) h).trans hbudget
      rw [GoodDivisor] at hgood
      rw [hDcard] at hgood
      omega
    omega
  have hCcard : Bq.card = (divisiblePart S (k * q)).card := by
    simpa [Bq, B, D] using quotient_filter_divisible_card (S := S) hkpos
  have hkqle : k * q ≤ n := by
    have hCnonempty : (divisiblePart S (k * q)).Nonempty := by
      apply Finset.card_pos.mp
      rw [← hCcard]
      exact hBqpos
    obtain ⟨a, ha⟩ := hCnonempty
    have haData := Finset.mem_filter.mp ha
    have hapos : 0 < a := (Finset.mem_Icc.mp (hS haData.1)).1
    have hkqa : k * q ≤ a := Nat.le_of_dvd hapos haData.2
    have haS : a ∈ S := haData.1
    have haBound : a ≤ n := (Finset.mem_Icc.mp (hS haData.1)).2
    exact hkqa.trans haBound
  have hlogStep : Nat.log 2 k + 1 ≤ Nat.log 2 (k * q) := by
    rw [← Nat.log_mul_base Nat.one_lt_two hkpos.ne']
    exact Nat.log_mono_right (Nat.mul_le_mul_left k hq)
  have hnewGood : GoodDivisor S h (k * q) := by
    refine ⟨Nat.mul_pos hkpos (by omega), ?_⟩
    rw [GoodDivisor] at hgood
    rw [← hCcard]
    calc
      S.card ≤ D.card + h * Nat.log 2 k := hgood.2
      _ = B.card + h * Nat.log 2 k := hDcard
      _ ≤ Bq.card + h + h * Nat.log 2 k := by omega
      _ = Bq.card + h * (Nat.log 2 k + 1) := by ring
      _ ≤ Bq.card + h * Nat.log 2 (k * q) := by gcongr
  have hmax : k * q ≤ k := by
    simpa [k, extractionDivisor] using
      Nat.le_findGreatest (P := GoodDivisor S h) hkqle hnewGood
  nlinarith

/-- The maximal-divisor extraction and the local Fourier theorem together
produce a long initial progression.  Numerical growth is isolated in the
uniform hypothesis `hdecay`. -/
lemma exists_sparse_seed_progression {S : Finset ℕ} {n h : ℕ}
    (hn : 1 ≤ n) (hhpos : 0 < h) (hS : S ⊆ Finset.Icc 1 n)
    (hbudget : h * Nat.log 2 n + 2 * h ≤ S.card)
    (hdecay : ∀ x : ℕ,
      S.card - h * Nat.log 2 n ≤ x → x ≤ S.card →
      Real.exp (-minorEnergy n x h) < 3 * coreRadius n x / 4) :
    ∃ k D B c, 0 < k ∧ k ≤ n ∧ D ⊆ S ∧
      (∀ d ∈ D, k ∣ d) ∧ B = quotientPart k D ∧
      B.card = D.card ∧ S.card - h * Nat.log 2 n ≤ D.card ∧
      c = (∑ b ∈ B, b) / 2 ∧
      CoversMultiples D k (k * c) (k * (c + 99 * n)) := by
  let k := extractionDivisor S n h
  let D := divisiblePart S k
  let B := quotientPart k D
  let c := (∑ b ∈ B, b) / 2
  have hkpos : 0 < k := extractionDivisor_pos hn
  have hkle : k ≤ n := extractionDivisor_le S n h
  have hDS : D ⊆ S := Finset.filter_subset _ _
  have hDdiv : ∀ d ∈ D, k ∣ d := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2
  have hBcard : B.card = D.card := card_quotientPart hkpos hDdiv
  have hgood := extractionDivisor_spec (S := S) (h := h) hn
  have hlogle : Nat.log 2 k ≤ Nat.log 2 n := Nat.log_mono_right hkle
  have hDlower : S.card - h * Nat.log 2 n ≤ D.card := by
    have hgoodBound : S.card ≤ D.card + h * Nat.log 2 k := by
      simpa [GoodDivisor, D, k] using hgood.2
    have hloss : h * Nat.log 2 k ≤ h * Nat.log 2 n :=
      Nat.mul_le_mul_left h hlogle
    omega
  have hhalf : h ≤ B.card / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
    rw [hBcard]
    rw [GoodDivisor] at hgood
    have hsmall : h * Nat.log 2 k + 2 * h ≤ S.card :=
      (Nat.add_le_add_right (Nat.mul_le_mul_left h hlogle) (2 * h)).trans hbudget
    omega
  have hBsub : B ⊆ Finset.Icc 1 n :=
    quotientPart_subset_Icc hkpos (hDS.trans hS) hDdiv
  have hSparse : ∀ q : ℕ, 2 ≤ q →
      h ≤ (B.filter fun b => ¬q ∣ b).card := by
    exact extractionDivisor_sparse hn hhpos hS (by omega)
  have hBupper : B.card ≤ S.card := by
    rw [hBcard]
    exact Finset.card_le_card hDS
  have hdecayB : Real.exp (-minorEnergy n B.card h) <
      3 * coreRadius n B.card / 4 :=
    hdecay B.card (by simpa [hBcard] using hDlower) hBupper
  have hlocal : ∀ z : ℕ, c ≤ z → z ≤ c + 99 * n →
      z ∈ B.subsetSum := by
    intro z hcz hz
    apply mem_subsetSum_of_sparse (n := n) (x := B.card) (h := h)
      hn hBsub rfl hhalf
    · intro q hq _hgrid
      exact hSparse q hq
    · let T := ∑ b ∈ B, b
      have hcLow : (c : ℝ) ≤ (T : ℝ) / 2 := by
        simpa [c, T] using (Nat.cast_div_le (α := ℝ) (m := T) (n := 2))
      have hcNat : T < (c + 1) * 2 := by
        have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mp
          (Nat.lt_succ_self (T / 2))
        simpa [c, Nat.mul_comm] using this
      have hcHigh : (T : ℝ) / 2 < (c : ℝ) + 1 := by
        exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
          (by exact_mod_cast hcNat)
      have hczR : (c : ℝ) ≤ z := by exact_mod_cast hcz
      have hzR : (z : ℝ) ≤ c + 99 * n := by exact_mod_cast hz
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_le]
      constructor <;> dsimp [T] at * <;> nlinarith
    · exact hdecayB
  have hcover : CoversMultiples D k (k * c) (k * (c + 99 * n)) := by
    intro M hlow hupp hkM
    obtain ⟨z, rfl⟩ := hkM
    have hcz : c ≤ z := by
      exact (Nat.mul_le_mul_left_iff hkpos).mp
        (by simpa [Nat.mul_comm] using hlow)
    have hz : z ≤ c + 99 * n := by
      exact (Nat.mul_le_mul_left_iff hkpos).mp
        (by simpa [Nat.mul_comm] using hupp)
    exact mem_subsetSum_of_quotientPart hkpos hDdiv (hlocal z hcz hz)
  exact ⟨k, D, B, c, hkpos, hkle, hDS, hDdiv, rfl, hBcard,
    hDlower, rfl, hcover⟩

/-! ## Extending a progression through all remaining multiples -/

lemma CoversMultiples.insert {D : Finset ℕ} {a q L U : ℕ}
    (hq : 0 < q) (hLU : L ≤ U) (hqU : q ∣ U) (hqa : q ∣ a)
    (haD : a ∉ D) (ha : a ≤ U - L + q)
    (hcover : CoversMultiples D q L U) :
    CoversMultiples (insert a D) q L (U + a) := by
  intro M hLM hMU hqM
  by_cases hOld : M ≤ U
  · exact Finset.subsetSum_mono (Finset.subset_insert a D)
      (hcover M hLM hOld hqM)
  · have hdiffpos : 0 < M - U := Nat.sub_pos_of_lt (Nat.lt_of_not_ge hOld)
    have hqdiff : q ∣ M - U := by
      exact Nat.dvd_sub hqM hqU
    have hqle : q ≤ M - U := Nat.le_of_dvd hdiffpos hqdiff
    have hUqM : U + q ≤ M := by omega
    have haM : a ≤ M := by omega
    have hlow : L ≤ M - a := by omega
    have hupp : M - a ≤ U := by omega
    have hqsub : q ∣ M - a := Nat.dvd_sub hqM hqa
    obtain ⟨T, hTD, hTsum⟩ := Finset.mem_subsetSum_iff.mp
      (hcover (M - a) hlow hupp hqsub)
    apply Finset.mem_subsetSum_iff.mpr
    refine ⟨Insert.insert a T, ?_, ?_⟩
    · exact Finset.insert_subset_insert a hTD
    · rw [Finset.sum_insert]
      · simpa [hTsum, Nat.add_comm] using Nat.sub_add_cancel haM
      · exact fun haT => haD (hTD haT)

lemma CoversMultiples.add_list {D : Finset ℕ} {l : List ℕ}
    {q L U W : ℕ} (hq : 0 < q) (hLU : L ≤ U) (hqU : q ∣ U)
    (hnodup : l.Nodup) (hdisj : Disjoint l.toFinset D)
    (hTdiv : ∀ a ∈ l, q ∣ a) (hbound : ∀ a ∈ l, a ≤ W)
    (hW : W ≤ U - L + q) (hcover : CoversMultiples D q L U) :
    CoversMultiples (D ∪ l.toFinset) q L (U + l.sum) := by
  induction l generalizing D U with
  | nil => simpa using hcover
  | cons a l ih =>
      have haList : a ∉ l := (List.nodup_cons.mp hnodup).1
      have hlNodup : l.Nodup := hnodup.tail
      have haD : a ∉ D := by
        intro haD
        exact (Finset.disjoint_left.mp hdisj (by simp) haD)
      have hstep := hcover.insert hq hLU hqU (hTdiv a (by simp))
        haD ((hbound a (by simp)).trans hW)
      have hdisjTail : Disjoint l.toFinset (Insert.insert a D) := by
        rw [Finset.disjoint_insert_right]
        exact ⟨by simpa using haList, hdisj.mono_left (by simp)⟩
      have hsubmono : U - L ≤ (U + a) - L :=
        Nat.sub_le_sub_right (Nat.le_add_right U a) L
      have hWtail : W ≤ (U + a) - L + q := by omega
      have htail := ih (D := Insert.insert a D) (U := U + a)
        (by omega) (Nat.dvd_add hqU (hTdiv a (by simp)))
        hlNodup hdisjTail
        (fun b hb => hTdiv b (by simp [hb]))
        (fun b hb => hbound b (by simp [hb])) hWtail hstep
      simpa [List.toFinset_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, Finset.insert_union, Finset.union_insert] using htail

lemma CoversMultiples.add_finset {D T : Finset ℕ} {q L U W : ℕ}
    (hq : 0 < q) (hLU : L ≤ U) (hqU : q ∣ U)
    (hdisj : Disjoint T D) (hTdiv : ∀ a ∈ T, q ∣ a)
    (hbound : ∀ a ∈ T, a ≤ W) (hW : W ≤ U - L + q)
    (hcover : CoversMultiples D q L U) :
    CoversMultiples (D ∪ T) q L (U + ∑ a ∈ T, a) := by
  have h := CoversMultiples.add_list (l := T.toList) hq hLU hqU
    T.nodup_toList (by simpa using hdisj)
    (fun a ha => hTdiv a (by simpa using ha))
    (fun a ha => hbound a (by simpa using ha)) hW hcover
  simpa using h

/-- Complete finite long-progression package.  This is the combinatorial
content of Alon--Freiman's long-multiples lemma; all asymptotic input remains
in `hbudget` and `hdecay`. -/
lemma exists_long_multiples {A S : Finset ℕ} {n h : ℕ}
    (hn : 1 ≤ n) (hhpos : 0 < h) (hA : A ⊆ Finset.Icc 1 n)
    (hSA : S ⊆ A) (hbudget : h * Nat.log 2 n + 2 * h ≤ S.card)
    (hdecay : ∀ x : ℕ,
      S.card - h * Nat.log 2 n ≤ x → x ≤ S.card →
      Real.exp (-minorEnergy n x h) < 3 * coreRadius n x / 4) :
    ∃ q k c E G, 0 < q ∧ q ∣ k ∧ 0 < k ∧ k ≤ n ∧
      G = divisiblePart A q ∧ E ⊆ G ∧ E.card ≤ S.card + 2 * k ∧
      (A.filter fun a => ¬q ∣ a).card < q ^ 2 ∧
      k * (S.card - h * Nat.log 2 n) ≤ n ∧
      k * c ≤ S.card * n ∧
      CoversMultiples G q (k * c + 2 * k * n)
        (k * (c + 99 * n) + ∑ a ∈ G \ E, a) := by
  obtain ⟨k, D, B, c, hkpos, hkle, hDS, hDdiv, hB,
      hBcard, hDlower, hc, hseedCover⟩ :=
    exists_sparse_seed_progression hn hhpos (hSA.trans hA)
      hbudget hdecay
  subst B
  subst c
  let c := (∑ b ∈ quotientPart k D, b) / 2
  have hDA : D ⊆ A := hDS.trans hSA
  obtain ⟨q, E, hqpos, hqk, hDE, hEA, hEcard0, hEdiv,
      hstable, hstableCover⟩ :=
    exists_stable_progression hkpos hA hDA hDdiv hseedCover
  let G := divisiblePart A q
  have hEG : E ⊆ G := by
    intro e he
    exact Finset.mem_filter.mpr ⟨hEA he, hEdiv e he⟩
  have hEcard : E.card ≤ S.card + 2 * k := by
    exact hEcard0.trans (Nat.add_le_add_right (Finset.card_le_card hDS) (2 * k))
  have hqU : q ∣ k * (c + 99 * n) := hqk.trans (dvd_mul_right k _)
  have hLU : k * c + 2 * k * n ≤ k * (c + 99 * n) := by
    have hnpos : 0 < n := hn
    nlinarith
  have hwidthEq : k * (c + 99 * n) - (k * c + 2 * k * n) =
      97 * k * n := by
    calc
      k * (c + 99 * n) - (k * c + 2 * k * n) =
          (k * c + 99 * (k * n)) - (k * c + 2 * (k * n)) := by ring
      _ = 97 * (k * n) := by omega
      _ = 97 * k * n := by ring
  have hnWidth : n ≤
      k * (c + 99 * n) - (k * c + 2 * k * n) + q := by
    rw [hwidthEq]
    calc
      n = 1 * n := by simp
      _ ≤ k * n := Nat.mul_le_mul_right n hkpos
      _ ≤ 97 * k * n := by nlinarith
      _ ≤ 97 * k * n + q := Nat.le_add_right _ _
  let T := G \ E
  have hdisj : Disjoint T E := by
    exact (Finset.disjoint_sdiff : Disjoint E (G \ E)).symm
  have hTdiv : ∀ a ∈ T, q ∣ a := by
    intro a ha
    exact (Finset.mem_filter.mp (Finset.sdiff_subset ha)).2
  have hTbound : ∀ a ∈ T, a ≤ n := by
    intro a ha
    have haA := (Finset.mem_filter.mp (Finset.sdiff_subset ha)).1
    exact (Finset.mem_Icc.mp (hA haA)).2
  have hext := hstableCover.add_finset hqpos hLU hqU hdisj hTdiv
    hTbound hnWidth
  have hUnion : E ∪ T = G := by
    exact Finset.union_sdiff_of_subset hEG
  rw [hUnion] at hext
  have hkc : k * c ≤ S.card * n := by
    have hsumScale : k * (∑ b ∈ quotientPart k D, b) = ∑ d ∈ D, d := by
      let Q := quotientPart k D
      have hinj : Set.InjOn (fun b : ℕ => k * b) Q := by
        intro a ha b hb hab
        exact Nat.eq_of_mul_eq_mul_left hkpos hab
      calc
        k * (∑ b ∈ Q, b) = ∑ b ∈ Q, k * b := by simp [Finset.mul_sum]
        _ = ∑ d ∈ Q.image (fun b => k * b), d :=
          (Finset.sum_image (f := fun x : ℕ => x)
            (g := fun b : ℕ => k * b) hinj).symm
        _ = ∑ d ∈ D, d := by rw [image_mul_quotientPart hkpos hDdiv]
    have hcsum : c ≤ ∑ b ∈ quotientPart k D, b := Nat.div_le_self _ _
    calc
      k * c ≤ k * (∑ b ∈ quotientPart k D, b) :=
        Nat.mul_le_mul_left k hcsum
      _ = ∑ d ∈ D, d := hsumScale
      _ ≤ ∑ _d ∈ D, n := Finset.sum_le_sum fun d hd =>
        (Finset.mem_Icc.mp (hA (hDA hd))).2
      _ = D.card * n := by simp
      _ ≤ S.card * n := Nat.mul_le_mul_right n (Finset.card_le_card hDS)
  have hkLoss : k * (S.card - h * Nat.log 2 n) ≤ n := by
    have hDmult : D ⊆ multiplesUpTo n k := by
      intro d hd
      have hdI := Finset.mem_Icc.mp (hA (hDA hd))
      exact mem_multiplesUpTo.mpr ⟨hdI.2, (by omega), hDdiv d hd⟩
    have hcardD : D.card ≤ n / k := by
      simpa [card_multiplesUpTo] using Finset.card_le_card hDmult
    have hkD : k * D.card ≤ n := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hkpos).mp hcardD
    exact (Nat.mul_le_mul_left k hDlower).trans hkD
  refine ⟨q, k, c, E, G, hqpos, hqk, hkpos, hkle, rfl, hEG,
    hEcard, ?_, hkLoss, hkc, ?_⟩
  · simpa [G] using hstable
  · simpa [T, G] using hext

lemma divisiblePart_card_mul_le {A : Finset ℕ} {n q : ℕ} (hq : 0 < q)
    (hA : A ⊆ Finset.Icc 1 n) :
    q * (divisiblePart A q).card ≤ n := by
  have hsub : divisiblePart A q ⊆ multiplesUpTo n q := by
    intro a ha
    have haData := Finset.mem_filter.mp ha
    have haI := Finset.mem_Icc.mp (hA haData.1)
    exact mem_multiplesUpTo.mpr ⟨haI.2, (by omega), haData.2⟩
  have hcard := Finset.card_le_card hsub
  rw [card_multiplesUpTo] at hcard
  simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp hcard

lemma divisiblePart_sum_lower {A : Finset ℕ} {q : ℕ} (hq : 0 < q)
    (hApos : ∀ a ∈ A, 0 < a) :
    q * ((divisiblePart A q).card * ((divisiblePart A q).card + 1) / 2) ≤
      ∑ a ∈ divisiblePart A q, a := by
  let G := divisiblePart A q
  let B := quotientPart q G
  have hGdiv : ∀ g ∈ G, q ∣ g := by
    intro g hg
    exact (Finset.mem_filter.mp hg).2
  have hBcard : B.card = G.card := card_quotientPart hq hGdiv
  have hBpos : ∀ b ∈ B, 1 ≤ b := by
    intro b hb
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hb
    have hgpos : 0 < g := by
      have hgA := (Finset.mem_filter.mp hg).1
      exact hApos g hgA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
      (Nat.div_pos (Nat.le_of_dvd hgpos (hGdiv g hg)) hq))
  have htri := Erdos38.sum_ge_triangular B hBpos
  have hsumScale : q * (∑ b ∈ B, b) = ∑ g ∈ G, g := by
    have hinj : Set.InjOn (fun b : ℕ => q * b) B := by
      intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hq hab
    calc
      q * (∑ b ∈ B, b) = ∑ b ∈ B, q * b := by simp [Finset.mul_sum]
      _ = ∑ g ∈ B.image (fun b => q * b), g :=
        (Finset.sum_image (f := fun x : ℕ => x)
          (g := fun b : ℕ => q * b) hinj).symm
      _ = ∑ g ∈ G, g := by rw [image_mul_quotientPart hq hGdiv]
  calc
    q * (G.card * (G.card + 1) / 2) =
        q * (B.card * (B.card + 1) / 2) := by rw [hBcard]
    _ ≤ q * (∑ b ∈ B, b) := Nat.mul_le_mul_left q htri
    _ = ∑ g ∈ G, g := hsumScale

/-- A finite, fully explicit uniform representation theorem.  Its four
numerical hypotheses are exactly the estimates later verified for the
logarithmic seed. -/
lemma uniform_divisible_representation {A S : Finset ℕ}
    {n h s R V : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) (hhpos : 0 < h)
    (hA : A ⊆ Finset.Icc 1 n) (hSA : S ⊆ A)
    (hbudget : h * Nat.log 2 n + 2 * h ≤ S.card)
    (hdecay : ∀ x : ℕ,
      S.card - h * Nat.log 2 n ≤ x → x ≤ S.card →
      Real.exp (-minorEnergy n x h) < 3 * coreRadius n x / 4)
    (hzpos : 0 < S.card - h * Nat.log 2 n)
    (hmodulus : n / (s + 1) <
      A.card - (n / (S.card - h * Nat.log 2 n)) ^ 2)
    (hlower : S.card * n +
      2 * (n / (S.card - h * Nat.log 2 n)) * n ≤ R)
    (hupper : V +
      (S.card + 2 * (n / (S.card - h * Nat.log 2 n))) * n ≤
      let t := A.card - (n / (S.card - h * Nat.log 2 n)) ^ 2
      t * (t + 1) / 2) :
    ∃ q G, 0 < q ∧ q ≤ s ∧ G = divisiblePart A q ∧
      CoversMultiples G q R V := by
  let z := S.card - h * Nat.log 2 n
  let K := n / z
  let t₀ := A.card - K ^ 2
  obtain ⟨q, k, c, E, G, hqpos, hqk, hkpos, hkle, hG,
      hEG, hEcard, hout, hkz, hkc, hcover⟩ :=
    exists_long_multiples hn hhpos hA hSA hbudget hdecay
  have hkK : k ≤ K := by
    exact (Nat.le_div_iff_mul_le hzpos).mpr (by
      simpa [z, Nat.mul_comm] using hkz)
  have hqkLe : q ≤ k := Nat.le_of_dvd hkpos hqk
  have hqK : q ≤ K := hqkLe.trans hkK
  have hsplit : (divisiblePart A q).card +
      (A.filter fun a => ¬q ∣ a).card = A.card :=
    Finset.card_filter_add_card_filter_not (s := A) (p := fun a => q ∣ a)
  have houtK : (A.filter fun a => ¬q ∣ a).card ≤ K ^ 2 := by
    have hpow : q ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left hqK 2
    omega
  have htG : t₀ ≤ G.card := by
    rw [hG]
    dsimp [t₀]
    omega
  have hqCard : q * G.card ≤ n := by
    rw [hG]
    exact divisiblePart_card_mul_le hqpos hA
  have hqS : q ≤ s := by
    by_contra hnot
    have hsq : s + 1 ≤ q := by omega
    have hsCard : (s + 1) * G.card ≤ n :=
      (Nat.mul_le_mul_right G.card hsq).trans hqCard
    have hGdiv : G.card ≤ n / (s + 1) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by
        simpa [Nat.mul_comm] using hsCard)
    have hnum : n / (s + 1) < t₀ := by simpa [t₀, K, z] using hmodulus
    omega
  have hLowerExact : k * c + 2 * k * n ≤ R := by
    calc
      k * c + 2 * k * n ≤ S.card * n + 2 * K * n := by
        exact Nat.add_le_add hkc (Nat.mul_le_mul_right n
          (Nat.mul_le_mul_left 2 hkK))
      _ ≤ R := by simpa [K, z] using hlower
  have hGsum := divisiblePart_sum_lower hqpos
    (fun a ha => (Finset.mem_Icc.mp (hA ha)).1)
  rw [← hG] at hGsum
  have htri : t₀ * (t₀ + 1) / 2 ≤ G.card * (G.card + 1) / 2 := by
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul htG (Nat.add_le_add_right htG 1)
  have hsumLower : t₀ * (t₀ + 1) / 2 ≤ ∑ g ∈ G, g := by
    exact htri.trans ((Nat.le_mul_of_pos_left _ hqpos).trans hGsum)
  have hEsum : ∑ e ∈ E, e ≤ (S.card + 2 * K) * n := by
    calc
      ∑ e ∈ E, e ≤ ∑ _e ∈ E, n := Finset.sum_le_sum fun e he => by
        have heG := hEG he
        rw [hG] at heG
        exact (Finset.mem_Icc.mp (hA (Finset.mem_filter.mp heG).1)).2
      _ = E.card * n := by simp
      _ ≤ (S.card + 2 * K) * n := by
        gcongr
        exact hEcard.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hkK) _)
  have hsumSplit : (∑ g ∈ G \ E, g) + ∑ e ∈ E, e = ∑ g ∈ G, g :=
    Finset.sum_sdiff hEG
  have hVdiff : V ≤ ∑ g ∈ G \ E, g := by
    have hupper' : V + (S.card + 2 * K) * n ≤
        t₀ * (t₀ + 1) / 2 := by simpa [K, z, t₀] using hupper
    omega
  have hUpperExact : V ≤ k * (c + 99 * n) + ∑ g ∈ G \ E, g :=
    hVdiff.trans (Nat.le_add_left _ _)
  refine ⟨q, G, hqpos, hqS, hG, ?_⟩
  exact hcover.shrink hLowerExact hUpperExact

end LocalLimit

/-! ## Polylogarithmic parameters for the Alon--Freiman argument -/

/-- A positive integral proxy for `log n`.  The extra one makes all exact
divisions below total, including at the small values which are eventually
discarded. -/
def binaryScale (n : ℕ) : ℕ := Erdos387.binaryLogScale n

def afSeedSize (n : ℕ) : ℕ := n / binaryScale n ^ 8

def afThickness (n : ℕ) : ℕ := n / binaryScale n ^ 20

def afLowerEndpoint (n : ℕ) : ℕ :=
  n ^ 2 / (10000 * binaryScale n ^ 3)

def afUpperEndpoint (n : ℕ) : ℕ :=
  n ^ 2 / (1000 * binaryScale n ^ 2)

def afTarget (n : ℕ) : ℕ :=
  Nat.lcmUpto (lcmCutoff (afUpperEndpoint n))

def afTargetNondivisor (n : ℕ) : ℕ :=
  lcmCutoff (afUpperEndpoint n) + 1

@[simp] lemma binaryScale_eq (n : ℕ) :
    binaryScale n = Nat.log 2 n + 1 := rfl

lemma binaryScale_pos (n : ℕ) : 0 < binaryScale n := by
  simpa [binaryScale] using Erdos387.binaryLogScale_pos n

lemma eventually_binaryScale_ge (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, C ≤ binaryScale n := by
  filter_upwards [eventually_ge_atTop (2 ^ C)] with n hn
  have hlog : C ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by omega) hn
  change C ≤ Nat.log 2 n + 1
  exact hlog.trans (Nat.le_succ _)

lemma log_natCast_lt_binaryScale {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) < binaryScale n := by
  have hpow := Nat.lt_pow_succ_log_self (b := 2) (by omega) n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpowR : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast hpow
  have hloglt := Real.log_lt_log hnR hpowR
  rw [Real.log_pow] at hloglt
  have hlogTwo : Real.log (2 : ℝ) < 1 :=
    log_two_lt_d9.trans (by norm_num)
  have hscale0 : (0 : ℝ) ≤ Nat.log 2 n + 1 := by positivity
  calc
    Real.log (n : ℝ) < (Nat.log 2 n + 1 : ℕ) * Real.log 2 := hloglt
    _ ≤ (Nat.log 2 n + 1 : ℕ) := by
      norm_num
      exact mul_le_of_le_one_right hscale0 hlogTwo.le
    _ = binaryScale n := by
      change ((Nat.log 2 n + 1 : ℕ) : ℝ) =
        ((Nat.log 2 n + 1 : ℕ) : ℝ)
      rfl

/-- Every fixed power of the integral logarithmic scale, even after
multiplication by a fixed constant, is eventually bounded by `n`. -/
lemma eventually_const_mul_binaryScale_pow_le_self (C e : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * binaryScale n ^ e ≤ n := by
  filter_upwards
    [eventually_binaryScale_ge C,
      Erdos387.eventually_binaryLogScale_pow_le_half (e + 1)]
      with n hBC hpow
  change binaryScale n ^ (e + 1) ≤ n / 2 at hpow
  have htwice : 2 * binaryScale n ^ (e + 1) ≤ n := by
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hpow
  calc
    C * binaryScale n ^ e ≤ binaryScale n * binaryScale n ^ e :=
      Nat.mul_le_mul_right _ hBC
    _ = binaryScale n ^ (e + 1) := by ring
    _ ≤ 2 * binaryScale n ^ (e + 1) := by omega
    _ ≤ n := htwice

lemma eventually_one_le_afUpperEndpoint :
    ∀ᶠ n : ℕ in atTop, 1 ≤ afUpperEndpoint n := by
  filter_upwards
    [eventually_const_mul_binaryScale_pow_le_self 1000 2,
      eventually_ge_atTop 1] with n hden hn
  have hdenPos : 0 < 1000 * binaryScale n ^ 2 :=
    mul_pos (by omega) (pow_pos (binaryScale_pos n) 2)
  have hmul : n * (1000 * binaryScale n ^ 2) ≤ n ^ 2 := by
    calc
      n * (1000 * binaryScale n ^ 2) ≤ n * n :=
        Nat.mul_le_mul_left n hden
      _ = n ^ 2 := by ring
  have hnle : n ≤ afUpperEndpoint n := by
    rw [afUpperEndpoint, Nat.le_div_iff_mul_le hdenPos]
    exact hmul
  omega

lemma afUpperEndpoint_tendsto_atTop :
    Tendsto afUpperEndpoint atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (eventually_const_mul_binaryScale_pow_le_self 1000 2)
  refine ⟨max N N₀, fun n hn => ?_⟩
  have hden := hN₀ n ((le_max_right N N₀).trans hn)
  have hn : N ≤ n := (le_max_left N N₀).trans hn
  have hdenPos : 0 < 1000 * binaryScale n ^ 2 :=
    mul_pos (by omega) (pow_pos (binaryScale_pos n) 2)
  calc
    N ≤ n := hn
    _ ≤ afUpperEndpoint n := by
      rw [afUpperEndpoint, Nat.le_div_iff_mul_le hdenPos]
      calc
        n * (1000 * binaryScale n ^ 2) ≤ n * n :=
          Nat.mul_le_mul_left n hden
        _ = n ^ 2 := by ring

lemma afCutoff_tendsto_atTop :
    Tendsto (fun n => lcmCutoff (afUpperEndpoint n)) atTop atTop :=
  lcmCutoff_tendsto_atTop.comp afUpperEndpoint_tendsto_atTop

lemma eventually_afTargetNondivisor_le_three_binaryScale :
    ∀ᶠ n : ℕ in atTop,
      afTargetNondivisor n ≤ 3 * binaryScale n := by
  have hcutReal : Tendsto
      (fun n : ℕ => (lcmCutoff (afUpperEndpoint n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp afCutoff_tendsto_atTop
  have hpsi := chebyshev_psi_ratio_tendsto_one.comp hcutReal
  filter_upwards
    [eventually_one_le_afUpperEndpoint,
      eventually_binaryScale_ge 3,
      eventually_ge_atTop 2,
      hpsi.eventually (Ioi_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1))]
      with n hX hB hn hratio
  let X := afUpperEndpoint n
  let r := lcmCutoff X
  change (3 / 4 : ℝ) < Chebyshev.psi (r : ℝ) / (r : ℝ) at hratio
  have hrposR : (0 : ℝ) < r := by
    by_contra hr
    have hr0 : (r : ℝ) = 0 := le_antisymm (le_of_not_gt hr) (by positivity)
    rw [hr0] at hratio
    norm_num at hratio
  have hrpos : 0 < r := by exact_mod_cast hrposR
  have hpsiLower : (3 / 4 : ℝ) * r < Chebyshev.psi (r : ℝ) := by
    rw [show Chebyshev.psi (r : ℝ) =
      (Chebyshev.psi (r : ℝ) / r) * r by field_simp]
    exact mul_lt_mul_of_pos_right hratio hrposR
  have hL : Nat.lcmUpto r ≤ X := by
    simpa [X, r] using lcmUpto_cutoff_le (by simpa [X] using hX)
  have hpsiUpper : Chebyshev.psi (r : ℝ) ≤ Real.log (X : ℝ) := by
    rw [Chebyshev.psi_eq_log_lcmUpto]
    exact Real.log_le_log (by exact_mod_cast Nat.lcmUpto_pos r)
      (by exact_mod_cast hL)
  have hXn : X ≤ n ^ 2 := by
    dsimp [X, afUpperEndpoint]
    exact Nat.div_le_self _ _
  have hnpos : 0 < n := by omega
  have hlogX : Real.log (X : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    calc
      Real.log (X : ℝ) ≤ Real.log ((n ^ 2 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hX) (by exact_mod_cast hXn)
      _ = 2 * Real.log (n : ℝ) := by
        push_cast
        rw [Real.log_pow]
        norm_num
  have hlogn : Real.log (n : ℝ) < binaryScale n :=
    log_natCast_lt_binaryScale hnpos
  have hBR : (3 : ℝ) ≤ binaryScale n := by exact_mod_cast hB
  have hsR : ((r + 1 : ℕ) : ℝ) ≤ 3 * binaryScale n := by
    push_cast
    nlinarith
  change r + 1 ≤ 3 * binaryScale n
  exact_mod_cast hsR

lemma log_binaryScale_div_log_tendsto_zero :
    Tendsto (fun n : ℕ =>
      Real.log (binaryScale n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hconst : Tendsto (fun n : ℕ =>
      Real.log (3 : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_coe_at_top
  have hmajor : Tendsto (fun n : ℕ =>
      Real.log (3 : ℝ) / Real.log (n : ℝ) +
        Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    simpa using hconst.add Erdos285.RoughCounts.loglog_div_log_tendsto_zero
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hlogpos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    exact div_nonneg (Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ binaryScale n by
        exact (binaryScale_pos n)))) hlogpos.le
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hlogpos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hscale : (binaryScale n : ℝ) ≤ 3 * Real.log (n : ℝ) := by
      simpa [binaryScale] using
        Erdos387.binaryLogScale_cast_le_three_mul_log hn
    have hlogScale : Real.log (binaryScale n : ℝ) ≤
        Real.log (3 * Real.log (n : ℝ)) :=
      Real.log_le_log (by exact_mod_cast binaryScale_pos n) hscale
    have hlogMul : Real.log (3 * Real.log (n : ℝ)) =
        Real.log 3 + Real.log (Real.log (n : ℝ)) := by
      rw [Real.log_mul (by norm_num) hlogpos.ne']
    rw [hlogMul] at hlogScale
    rw [show Real.log 3 / Real.log (n : ℝ) +
        Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) =
        (Real.log 3 + Real.log (Real.log (n : ℝ))) /
          Real.log (n : ℝ) by ring]
    exact div_le_div_of_nonneg_right hlogScale hlogpos.le

lemma log_afUpperEndpoint_div_log_tendsto_two :
    Tendsto (fun n : ℕ =>
      Real.log (afUpperEndpoint n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 2) := by
  let err : ℕ → ℝ := fun n =>
    Real.log (2000 : ℝ) / Real.log (n : ℝ) +
      2 * (Real.log (binaryScale n : ℝ) / Real.log (n : ℝ))
  have hconst : Tendsto (fun n : ℕ =>
      Real.log (2000 : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_coe_at_top
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa [err] using hconst.add
      (log_binaryScale_div_log_tendsto_zero.const_mul 2)
  have hlowerLim : Tendsto (fun n => 2 - err n) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.sub herr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerLim tendsto_const_nhds
  · filter_upwards
      [eventually_one_le_afUpperEndpoint, eventually_ge_atTop 2]
      with n hX hn
    let B := binaryScale n
    let D := 1000 * B ^ 2
    let X := afUpperEndpoint n
    have hDpos : 0 < D := by
      dsimp [D]
      exact mul_pos (by omega) (pow_pos (binaryScale_pos n) 2)
    have hXpos : 0 < X := by dsimp [X]; omega
    have hquad : n ^ 2 < 2 * D * X := by
      have hdiv := Nat.lt_mul_div_succ (n ^ 2) hDpos
      have hsucc : X + 1 ≤ 2 * X := by omega
      calc
        n ^ 2 < D * (X + 1) := by
          simpa [X, D, B, afUpperEndpoint] using hdiv
        _ ≤ D * (2 * X) := Nat.mul_le_mul_left D hsucc
        _ = 2 * D * X := by ring
    have hnpos : 0 < n := by omega
    have hlogpos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hlogQuad : Real.log ((n ^ 2 : ℕ) : ℝ) <
        Real.log ((2 * D * X : ℕ) : ℝ) :=
      Real.log_lt_log (by positivity) (by exact_mod_cast hquad)
    have hlogRel : 2 * Real.log (n : ℝ) <
        Real.log (2000 : ℝ) + 2 * Real.log (B : ℝ) +
          Real.log (X : ℝ) := by
      have hBposR : (0 : ℝ) < B := by
        exact_mod_cast (show 0 < B by simpa [B] using binaryScale_pos n)
      have hXposR : (0 : ℝ) < X := by exact_mod_cast hXpos
      have hleft : Real.log ((n ^ 2 : ℕ) : ℝ) =
          2 * Real.log (n : ℝ) := by
        push_cast
        rw [Real.log_pow]
        norm_num

      have htwoDX : (((2 * D * X : ℕ) : ℝ)) =
          (2000 : ℝ) * (B : ℝ) ^ 2 * (X : ℝ) := by
        dsimp [D]
        norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        ring
      have hright : Real.log ((2 * D * X : ℕ) : ℝ) =
          Real.log (2000 : ℝ) + 2 * Real.log (B : ℝ) +
            Real.log (X : ℝ) := by
        rw [htwoDX]
        rw [Real.log_mul
          (mul_ne_zero (by norm_num) (pow_ne_zero _ hBposR.ne')) hXposR.ne',
          Real.log_mul (by norm_num) (pow_ne_zero _ hBposR.ne'),
          Real.log_pow]
        ring
      rwa [hleft, hright] at hlogQuad
    change 2 - (Real.log (2000 : ℝ) / Real.log (n : ℝ) +
      2 * (Real.log (B : ℝ) / Real.log (n : ℝ))) ≤
        Real.log (X : ℝ) / Real.log (n : ℝ)
    rw [le_div_iff₀ hlogpos]
    field_simp [hlogpos.ne']
    nlinarith
  · filter_upwards
      [eventually_one_le_afUpperEndpoint, eventually_ge_atTop 2]
      with n hX hn
    have hnpos : 0 < n := by omega
    have hlogpos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hXn : afUpperEndpoint n ≤ n ^ 2 := by
      exact Nat.div_le_self _ _
    rw [div_le_iff₀ hlogpos]
    calc
      Real.log (afUpperEndpoint n : ℝ) ≤
          Real.log ((n ^ 2 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hX) (by exact_mod_cast hXn)
      _ = 2 * Real.log (n : ℝ) := by
        push_cast
        rw [Real.log_pow]
        norm_num

lemma afTargetNondivisor_ratio_tendsto_two :
    Tendsto (fun n : ℕ =>
      (afTargetNondivisor n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 2) := by
  let r : ℕ → ℕ := fun n => lcmCutoff (afUpperEndpoint n)
  let s : ℕ → ℕ := fun n => r n + 1
  let L : ℕ → ℝ := fun n => Real.log (afUpperEndpoint n : ℝ)
  let ar : ℕ → ℝ := fun n => Chebyshev.psi (r n : ℝ) / (r n : ℝ)
  let bs : ℕ → ℝ := fun n => Chebyshev.psi (s n : ℝ) / (s n : ℝ)
  have hrReal : Tendsto (fun n => (r n : ℝ)) atTop atTop := by
    change Tendsto (fun n : ℕ =>
      (lcmCutoff (afUpperEndpoint n) : ℝ)) atTop atTop
    apply (tendsto_natCast_atTop_atTop.comp afCutoff_tendsto_atTop).congr'
    filter_upwards with n
    rfl
  have hsReal : Tendsto (fun n => (s n : ℝ)) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (1 : ℝ) hrReal
    apply h.congr'
    filter_upwards with n
    simp [s]
  have har : Tendsto ar atTop (𝓝 1) := by
    change Tendsto (fun n =>
      Chebyshev.psi (r n : ℝ) / (r n : ℝ)) atTop (𝓝 1)
    apply (chebyshev_psi_ratio_tendsto_one.comp hrReal).congr'
    filter_upwards with n
    rfl
  have hbs : Tendsto bs atTop (𝓝 1) := by
    change Tendsto (fun n =>
      Chebyshev.psi (s n : ℝ) / (s n : ℝ)) atTop (𝓝 1)
    apply (chebyshev_psi_ratio_tendsto_one.comp hsReal).congr'
    filter_upwards with n
    rfl
  have hLtop : Tendsto L atTop atTop := by
    change Tendsto (fun n : ℕ =>
      Real.log (afUpperEndpoint n : ℝ)) atTop atTop
    apply (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp afUpperEndpoint_tendsto_atTop)).congr'
    filter_upwards with n
    rfl
  have hlowLim : Tendsto (fun n => (bs n)⁻¹ - (L n)⁻¹)
      atTop (𝓝 1) := by
    simpa using (hbs.inv₀ one_ne_zero).sub
      (tendsto_inv_atTop_zero.comp hLtop)
  have huppLim : Tendsto (fun n => (ar n)⁻¹) atTop (𝓝 1) := by
    simpa using har.inv₀ one_ne_zero
  have hcutRatio : Tendsto (fun n => (r n : ℝ) / L n)
      atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowLim huppLim
    · filter_upwards
        [eventually_one_le_afUpperEndpoint,
          afUpperEndpoint_tendsto_atTop.eventually (eventually_gt_atTop 1),
          har.eventually (Ioi_mem_nhds zero_lt_one),
          hbs.eventually (Ioi_mem_nhds zero_lt_one)]
        with n hX hXtwo harpos hbspos
      have hLpos : 0 < L n := by
        dsimp [L]
        exact Real.log_pos (by exact_mod_cast hXtwo)
      have hnext : afUpperEndpoint n < Nat.lcmUpto (s n) := by
        simpa [s, r] using cutoff_next_lcm_gt hX
      have hlogNext : L n < Chebyshev.psi (s n : ℝ) := by
        rw [Chebyshev.psi_eq_log_lcmUpto]
        exact Real.log_lt_log (by exact_mod_cast hX) (by exact_mod_cast hnext)
      have hbsEq : bs n * (s n : ℝ) = Chebyshev.psi (s n : ℝ) := by
        dsimp [bs]
        have hsne : (s n : ℝ) ≠ 0 := by dsimp [s]; positivity
        field_simp
      have hone : (bs n)⁻¹ < (s n : ℝ) / L n := by
        rw [inv_lt_iff_one_lt_mul₀ hbspos]
        rw [show (s n : ℝ) / L n * bs n =
          ((s n : ℝ) * bs n) / L n by ring, lt_div_iff₀ hLpos]
        nlinarith
      have hsplit : (s n : ℝ) / L n =
          (r n : ℝ) / L n + (L n)⁻¹ := by
        rw [show (s n : ℝ) = (r n : ℝ) + 1 by simp [s]]
        field_simp [hLpos.ne']
      rw [hsplit] at hone
      linarith
    · filter_upwards
        [eventually_one_le_afUpperEndpoint,
          afUpperEndpoint_tendsto_atTop.eventually (eventually_gt_atTop 1),
          har.eventually (Ioi_mem_nhds zero_lt_one)]
        with n hX hXtwo harpos
      have hLpos : 0 < L n := by
        dsimp [L]
        exact Real.log_pos (by exact_mod_cast hXtwo)
      have hrposR : (0 : ℝ) < r n := by
        by_contra hr
        have hr0 : (r n : ℝ) = 0 := le_antisymm (le_of_not_gt hr) (by positivity)
        dsimp [ar] at harpos
        rw [hr0] at harpos
        norm_num at harpos
      have hprev : Nat.lcmUpto (r n) ≤ afUpperEndpoint n := by
        simpa [r] using lcmUpto_cutoff_le hX
      have hlogPrev : Chebyshev.psi (r n : ℝ) ≤ L n := by
        rw [Chebyshev.psi_eq_log_lcmUpto]
        dsimp [L]
        exact Real.log_le_log (by exact_mod_cast Nat.lcmUpto_pos (r n))
          (by exact_mod_cast hprev)
      have harEq : ar n * (r n : ℝ) = Chebyshev.psi (r n : ℝ) := by
        dsimp [ar]
        field_simp [hrposR.ne']
      have hpsiPos : 0 < Chebyshev.psi (r n : ℝ) := by
        rw [← harEq]
        positivity
      calc
        (r n : ℝ) / L n ≤
            (r n : ℝ) / Chebyshev.psi (r n : ℝ) :=
          div_le_div_of_nonneg_left hrposR.le hpsiPos hlogPrev
        _ = (ar n)⁻¹ := by
          rw [← harEq]
          field_simp [hrposR.ne', harpos.ne']
  have hsOverLog : Tendsto (fun n => (s n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 2) := by
    have hcutProd := hcutRatio.mul log_afUpperEndpoint_div_log_tendsto_two
    have hmain : Tendsto (fun n =>
        ((r n : ℝ) / L n) * (L n / Real.log (n : ℝ)))
        atTop (𝓝 2) := by simpa using hcutProd
    have hrOverLog : Tendsto (fun n =>
        (r n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 2) := by
      apply hmain.congr'
      filter_upwards
        [tendsto_log_coe_at_top.eventually (eventually_ne_atTop 0),
          hLtop.eventually (eventually_ne_atTop 0)] with n hn hLn
      field_simp
    have honeOverLog : Tendsto (fun n : ℕ =>
        (1 : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_log_coe_at_top
    have hadd : Tendsto (fun n =>
        (r n : ℝ) / Real.log (n : ℝ) + 1 / Real.log (n : ℝ))
        atTop (𝓝 2) := by simpa using hrOverLog.add honeOverLog
    apply hadd.congr'
    filter_upwards
      [tendsto_log_coe_at_top.eventually (eventually_ne_atTop 0)] with n hn
    rw [show (s n : ℝ) = (r n : ℝ) + 1 by simp [s]]
    field_simp
  simpa [afTargetNondivisor, s, r] using hsOverLog

/-- Exact size facts about the two nested polylogarithmic seed parameters.
The deliberately wide exponent gaps make every inequality elementary. -/
lemma af_seed_geometry {n : ℕ}
    (hB : 2 ≤ binaryScale n)
    (hpow : binaryScale n ^ 38 ≤ n / 2) :
    0 < afThickness n ∧
      afThickness n * Nat.log 2 n + 2 * afThickness n ≤ afSeedSize n ∧
      0 < afSeedSize n - afThickness n * Nat.log 2 n ∧
      afSeedSize n ≤ 2 * (afSeedSize n - afThickness n * Nat.log 2 n) ∧
      n / (afSeedSize n - afThickness n * Nat.log 2 n) ≤
        4 * binaryScale n ^ 8 ∧
      n ≤ 4 * binaryScale n ^ 8 *
        (afSeedSize n - afThickness n * Nat.log 2 n) := by
  let B := binaryScale n
  let y := afSeedSize n
  let h := afThickness n
  let z := y - h * Nat.log 2 n
  have hBpos : 0 < B := by dsimp [B]; exact binaryScale_pos n
  have htwoPow : 2 * B ^ 38 ≤ n := by
    change B ^ 38 ≤ n / 2 at hpow
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hpow
  have hB20le : B ^ 20 ≤ n := by
    calc
      B ^ 20 ≤ 2 * B ^ 38 := by
        have hpowle : B ^ 20 ≤ B ^ 38 := Nat.pow_le_pow_right hBpos (by omega)
        omega
      _ ≤ n := htwoPow
  have hhpos : 0 < h := by
    have hh : 0 < n / B ^ 20 := Nat.div_pos hB20le (pow_pos hBpos 20)
    simpa [h, afThickness, B] using hh
  have hypos : 0 < y := by
    have hB8le : B ^ 8 ≤ n :=
      (Nat.pow_le_pow_right hBpos (by omega : 8 ≤ 20)).trans hB20le
    have hy : 0 < n / B ^ 8 := Nat.div_pos hB8le (pow_pos hBpos 8)
    simpa [y, afSeedSize, B] using hy
  have hlog : Nat.log 2 n + 1 = B := by rfl
  have hBplus : Nat.log 2 n + 2 ≤ B ^ 2 := by
    rw [show Nat.log 2 n + 2 = B + 1 by omega]
    nlinarith
  have hB10le20 : B ^ 10 ≤ B ^ 20 :=
    Nat.pow_le_pow_right hBpos (by omega)
  have hhB20 : h * B ^ 20 ≤ n := by
    change (n / B ^ 20) * B ^ 20 ≤ n
    exact Nat.div_mul_le_self n (B ^ 20)
  have hbudgetMul : (h * Nat.log 2 n + 2 * h) * B ^ 8 ≤ n := by
    calc
      (h * Nat.log 2 n + 2 * h) * B ^ 8 =
          h * (Nat.log 2 n + 2) * B ^ 8 := by ring
      _ ≤ h * B ^ 2 * B ^ 8 := by gcongr
      _ = h * B ^ 10 := by ring
      _ ≤ h * B ^ 20 := Nat.mul_le_mul_left h hB10le20
      _ ≤ n := hhB20
  have hbudget : h * Nat.log 2 n + 2 * h ≤ y := by
    apply (Nat.le_div_iff_mul_le (pow_pos hBpos 8)).2
    simpa [y, afSeedSize, B] using hbudgetMul
  have htwolMul : (2 * (h * Nat.log 2 n)) * B ^ 8 ≤ n := by
    have htwolog : 2 * Nat.log 2 n ≤ B ^ 2 := by
      rw [← hlog]
      nlinarith
    calc
      (2 * (h * Nat.log 2 n)) * B ^ 8 =
          h * (2 * Nat.log 2 n) * B ^ 8 := by ring
      _ ≤ h * B ^ 2 * B ^ 8 := by gcongr
      _ = h * B ^ 10 := by ring
      _ ≤ h * B ^ 20 := Nat.mul_le_mul_left h hB10le20
      _ ≤ n := hhB20
  have htwol : 2 * (h * Nat.log 2 n) ≤ y := by
    apply (Nat.le_div_iff_mul_le (pow_pos hBpos 8)).2
    simpa [y, afSeedSize, B] using htwolMul
  have hzpos : 0 < z := by
    dsimp [z]
    omega
  have hyz : y ≤ 2 * z := by
    dsimp [z]
    omega
  have hnlt : n < B ^ 8 * (y + 1) := by
    simpa [y, afSeedSize, B] using Nat.lt_mul_div_succ n (pow_pos hBpos 8)
  have hny : n ≤ 2 * B ^ 8 * y := by
    have : y + 1 ≤ 2 * y := by omega
    nlinarith
  have hnz : n ≤ (4 * B ^ 8) * z := by nlinarith
  have hK : n / z ≤ 4 * B ^ 8 := Nat.div_le_of_le_mul (by
    simpa [Nat.mul_comm] using hnz)
  simpa [B, y, h, z, Nat.mul_assoc] using And.intro hhpos
    (And.intro hbudget (And.intro hzpos
      (And.intro hyz (And.intro hK hnz))))

/-- The explicit minor-arc error is exponentially smaller than the central
arc contribution for every retained seed size. -/
lemma af_seed_decay {n x : ℕ}
    (hnlarge : 10000000 < n)
    (hB : 256 * (512 * 1001) ^ 2 < binaryScale n)
    (hpow : binaryScale n ^ 38 ≤ n / 2)
    (hxlow : afSeedSize n - afThickness n * Nat.log 2 n ≤ x)
    (hxhigh : x ≤ afSeedSize n) :
    Real.exp (-LocalLimit.minorEnergy n x (afThickness n)) <
      3 * LocalLimit.coreRadius n x / 4 := by
  let B := binaryScale n
  let y := afSeedSize n
  let h := afThickness n
  let z := y - h * Nat.log 2 n
  let C : ℕ := 512 * 1001
  have hBtwo : 2 ≤ B := by
    dsimp [B] at hB ⊢
    omega
  have hgeo := af_seed_geometry hBtwo hpow
  change 0 < h ∧ h * Nat.log 2 n + 2 * h ≤ y ∧ 0 < z ∧
    y ≤ 2 * z ∧ n / z ≤ 4 * B ^ 8 ∧ n ≤ 4 * B ^ 8 * z at hgeo
  rcases hgeo with ⟨hhpos, _hbudget, hzpos, _hyz, _hK, hnz⟩
  have hnpos : 0 < n := by omega
  have hBpos : 0 < B := by omega
  have hxpos : 0 < x := hzpos.trans_le (by simpa [z] using hxlow)
  have hyle : y ≤ n := by
    dsimp [y, afSeedSize]
    exact Nat.div_le_self _ _
  have hxle : x ≤ n := hxhigh.trans hyle
  have hnSucc : n + 1 ≤ 2 * n := by omega
  have hnX : n ≤ 4 * B ^ 8 * x := by
    exact hnz.trans (Nat.mul_le_mul_left (4 * B ^ 8)
      (by simpa [z] using hxlow))
  have hcross : C * (n + 1) ≤ x * (8 * C * B ^ 8) := by
    have hnX' : n + 1 ≤ 8 * B ^ 8 * x := by
      calc
        n + 1 ≤ 2 * n := hnSucc
        _ ≤ 2 * (4 * B ^ 8 * x) := Nat.mul_le_mul_left 2 hnX
        _ = 8 * B ^ 8 * x := by ring
    nlinarith
  have hratio : (1 : ℝ) / (8 * C * B ^ 8) ≤
      (x : ℝ) / (C * (n + 1)) := by
    have hd1 : (0 : ℝ) < 8 * C * B ^ 8 := by positivity
    have hd2 : (0 : ℝ) < C * (n + 1) := by positivity
    rw [div_le_div_iff₀ hd1 hd2]
    norm_num
    exact_mod_cast hcross
  have hnltH : n < B ^ 20 * (h + 1) := by
    simpa [h, afThickness, B] using
      Nat.lt_mul_div_succ n (pow_pos hBpos 20)
  have hhDouble : h + 1 ≤ 2 * h := by omega
  have hnH : n ≤ 2 * h * B ^ 20 := by
    calc
      n ≤ B ^ 20 * (h + 1) := Nat.le_of_lt hnltH
      _ ≤ B ^ 20 * (2 * h) := Nat.mul_le_mul_left _ hhDouble
      _ = 2 * h * B ^ 20 := by ring
  have hhLower : (n : ℝ) / (2 * B ^ 20) ≤ h := by
    have hd : (0 : ℝ) < 2 * B ^ 20 := by positivity
    rw [div_le_iff₀ hd]
    exact_mod_cast (by simpa [Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hnH)
  have henergyLower :
      (n : ℝ) / (128 * C ^ 2 * B ^ 36) ≤
        LocalLimit.minorEnergy n x h := by
    have hratio0 : (0 : ℝ) ≤ 1 / (8 * C * B ^ 8) := by positivity
    have hratioSq :
        ((1 : ℝ) / (8 * C * B ^ 8)) ^ 2 ≤
          ((x : ℝ) / (C * (n + 1))) ^ 2 :=
      pow_le_pow_left₀ hratio0 hratio 2
    calc
      (n : ℝ) / (128 * C ^ 2 * B ^ 36) =
          ((n : ℝ) / (2 * B ^ 20)) *
            ((1 : ℝ) / (8 * C * B ^ 8)) ^ 2 := by
              push_cast
              field_simp
              ring
      _ ≤ (h : ℝ) * ((1 : ℝ) / (8 * C * B ^ 8)) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hhLower (sq_nonneg _)
      _ ≤ (h : ℝ) * ((x : ℝ) / (C * (n + 1))) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hratioSq (Nat.cast_nonneg h)
      _ = LocalLimit.minorEnergy n x h := by
        simp only [LocalLimit.minorEnergy]
        norm_num [C]
  have htwoPow : 2 * B ^ 38 ≤ n := by
    change B ^ 38 ≤ n / 2 at hpow
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hpow
  have hBlarge : 256 * C ^ 2 < B := by
    change 256 * C ^ 2 < B at hB
    exact hB
  have hhuge : 512 * C ^ 2 * B ^ 37 < n := by
    have hmul := Nat.mul_lt_mul_of_pos_right hBlarge
      (show 0 < 2 * B ^ 37 by positivity)
    have hstep : 512 * C ^ 2 * B ^ 37 < 2 * B ^ 38 := by
      calc
        512 * C ^ 2 * B ^ 37 =
            (256 * C ^ 2) * (2 * B ^ 37) := by ring
        _ < B * (2 * B ^ 37) := hmul
        _ = 2 * B ^ 38 := by ring
    exact hstep.trans_le htwoPow
  have hfrac : (4 : ℝ) * B <
      (n : ℝ) / (128 * C ^ 2 * B ^ 36) := by
    have hd : (0 : ℝ) < 128 * C ^ 2 * B ^ 36 := by positivity
    rw [lt_div_iff₀ hd]
    have heq : (4 : ℝ) * B * (128 * C ^ 2 * B ^ 36) =
        ((512 * C ^ 2 * B ^ 37 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [heq]
    exact_mod_cast hhuge
  have henergy : (4 : ℝ) * B < LocalLimit.minorEnergy n x h :=
    hfrac.trans_le henergyLower
  have hlog : Real.log (n : ℝ) < B := log_natCast_lt_binaryScale hnpos
  have hneg : -LocalLimit.minorEnergy n x h <
      -(4 * Real.log (n : ℝ)) := by linarith
  have hexp : Real.exp (-LocalLimit.minorEnergy n x h) <
      ((n : ℝ) ^ 4)⁻¹ := by
    calc
      Real.exp (-LocalLimit.minorEnergy n x h) <
          Real.exp (-(4 * Real.log (n : ℝ))) :=
        (Real.exp_lt_exp.mpr hneg)
      _ = ((n : ℝ) ^ 4)⁻¹ := by
        rw [show -(4 * Real.log (n : ℝ)) =
          -Real.log ((n : ℝ) ^ 4) by rw [Real.log_pow]; norm_num]
        rw [Real.exp_neg, Real.exp_log (pow_pos (by positivity) 4)]
  have hinvSmall : ((n : ℝ) ^ 4)⁻¹ <
      3 / (8000000 * (n : ℝ) ^ 2) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    rw [show ((n : ℝ) ^ 4)⁻¹ = 1 / (n : ℝ) ^ 4 by
      simp [div_eq_mul_inv]]
    rw [div_lt_div_iff₀ (pow_pos hnR 4)
      (by positivity : (0 : ℝ) < 8000000 * n ^ 2)]
    have hnlargeR : (10000000 : ℝ) < n := by exact_mod_cast hnlarge
    have height : (8000000 : ℝ) < n := by linarith
    have hnOne : (1 : ℝ) ≤ n := by
      exact_mod_cast (show 1 ≤ n by omega)
    have hfirst : 1 * (8000000 * (n : ℝ) ^ 2) <
        (n : ℝ) * (n : ℝ) ^ 2 := by
      simpa only [one_mul] using
        mul_lt_mul_of_pos_right height (sq_pos_of_pos hnR)
    have hpow34 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
      rw [show (n : ℝ) ^ 4 = (n : ℝ) ^ 3 * n by ring]
      nth_rewrite 1 [← mul_one ((n : ℝ) ^ 3)]
      exact mul_le_mul_of_nonneg_left hnOne (pow_nonneg hnR.le 3)
    calc
      1 * (8000000 * (n : ℝ) ^ 2) <
          (n : ℝ) * (n : ℝ) ^ 2 := hfirst
      _ = (n : ℝ) ^ 3 := by ring
      _ ≤ (n : ℝ) ^ 4 := hpow34
      _ ≤ 3 * (n : ℝ) ^ 4 := by
        exact le_mul_of_one_le_left (pow_nonneg hnR.le 4) (by norm_num)
  have hcoreLower : 3 / (8000000 * (n : ℝ) ^ 2) ≤
      3 * LocalLimit.coreRadius n x / 4 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hxSucc : (x : ℝ) + 1 ≤ 2 * n := by exact_mod_cast (by omega : x + 1 ≤ 2 * n)
    rw [show 3 * LocalLimit.coreRadius n x / 4 =
      3 / (4000000 * (n : ℝ) * (x + 1)) by
        simp only [LocalLimit.coreRadius]
        field_simp
        ring]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 8000000 * n ^ 2)
      (by positivity : (0 : ℝ) < 4000000 * n * (x + 1))]
    have hden : 4000000 * (n : ℝ) * ((x : ℝ) + 1) ≤
        8000000 * (n : ℝ) ^ 2 := by
      calc
        4000000 * (n : ℝ) * ((x : ℝ) + 1) ≤
            4000000 * (n : ℝ) * (2 * (n : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hxSucc (by positivity)
        _ = 8000000 * (n : ℝ) ^ 2 := by ring
    exact mul_le_mul_of_nonneg_left hden (by norm_num)
  simpa [h] using hexp.trans (hinvSmall.trans_le hcoreLower)

def afCardThreshold (n s : ℕ) : ℕ :=
  n / s + 16 * binaryScale n ^ 16 + s

lemma af_lower_numeric {n : ℕ}
    (hB : 200000 < binaryScale n)
    (hpow : binaryScale n ^ 38 ≤ n / 2) :
    afSeedSize n * n +
        2 * (n / (afSeedSize n - afThickness n * Nat.log 2 n)) * n ≤
      afLowerEndpoint n := by
  let B := binaryScale n
  let y := afSeedSize n
  let h := afThickness n
  let z := y - h * Nat.log 2 n
  let K := n / z
  let D := 10000 * B ^ 3
  have hBtwo : 2 ≤ B := by dsimp [B] at hB ⊢; omega
  have hBpos : 0 < B := by omega
  have hgeo := af_seed_geometry hBtwo hpow
  change 0 < h ∧ h * Nat.log 2 n + 2 * h ≤ y ∧ 0 < z ∧
    y ≤ 2 * z ∧ K ≤ 4 * B ^ 8 ∧ n ≤ 4 * B ^ 8 * z at hgeo
  rcases hgeo with ⟨_hh, _hbudget, _hz, _hyz, hK, _hnz⟩
  have hyB : y * B ^ 8 ≤ n := by
    change (n / B ^ 8) * B ^ 8 ≤ n
    exact Nat.div_mul_le_self n (B ^ 8)
  have hcoeffY : 20000 * B ^ 3 ≤ B ^ 8 := by
    have hbase : 20000 ≤ B := by omega
    have hbasePow : B ≤ B ^ 5 := by
      simpa using Nat.pow_le_pow_right hBpos (show 1 ≤ 5 by omega)
    calc
      20000 * B ^ 3 ≤ B * B ^ 3 := Nat.mul_le_mul_right _ hbase
      _ ≤ B ^ 5 * B ^ 3 := Nat.mul_le_mul_right _ hbasePow
      _ = B ^ 8 := by ring
  have htermY : 2 * ((y * n) * D) ≤ n ^ 2 := by
    calc
      2 * ((y * n) * D) = y * n * (20000 * B ^ 3) := by
        dsimp [D]
        ring
      _ ≤ y * n * B ^ 8 := Nat.mul_le_mul_left (y * n) hcoeffY
      _ = (y * B ^ 8) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n hyB
      _ = n ^ 2 := by ring
  have htwoPow : 2 * B ^ 38 ≤ n := by
    change B ^ 38 ≤ n / 2 at hpow
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hpow
  have hcoeffK : 160000 * B ^ 11 ≤ n := by
    have hbase : 160000 ≤ B := by omega
    calc
      160000 * B ^ 11 ≤ B * B ^ 11 := Nat.mul_le_mul_right _ hbase
      _ = B ^ 12 := by ring
      _ ≤ 2 * B ^ 38 := by
        have hp : B ^ 12 ≤ B ^ 38 :=
          Nat.pow_le_pow_right hBpos (by omega)
        omega
      _ ≤ n := htwoPow
  have htermK : 2 * (((2 * K) * n) * D) ≤ n ^ 2 := by
    calc
      2 * (((2 * K) * n) * D) = 4 * K * n * (10000 * B ^ 3) := by
        dsimp [D]
        ring
      _ ≤ 4 * (4 * B ^ 8) * n * (10000 * B ^ 3) := by gcongr
      _ = (160000 * B ^ 11) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n hcoeffK
      _ = n ^ 2 := by ring
  have hDpos : 0 < D := by dsimp [D]; positivity
  change y * n + 2 * K * n ≤ n ^ 2 / D
  rw [Nat.le_div_iff_mul_le hDpos]
  rw [add_mul]
  have hleft : 2 * (y * n * D) ≤ n ^ 2 := by
    simpa [Nat.mul_assoc] using htermY
  have hright : 2 * ((2 * K * n) * D) ≤ n ^ 2 := by
    simpa [Nat.mul_assoc] using htermK
  omega

lemma af_upper_numeric {n s aCard : ℕ}
    (hB : 200000 < binaryScale n)
    (hpow : binaryScale n ^ 38 ≤ n / 2)
    (hs : 0 < s) (hsB : s ≤ 3 * binaryScale n)
    (hcard : afCardThreshold n s ≤ aCard) :
    afUpperEndpoint n +
        (afSeedSize n +
          2 * (n / (afSeedSize n - afThickness n * Nat.log 2 n))) * n ≤
      let t := aCard -
        (n / (afSeedSize n - afThickness n * Nat.log 2 n)) ^ 2
      t * (t + 1) / 2 := by
  let B := binaryScale n
  let y := afSeedSize n
  let h := afThickness n
  let z := y - h * Nat.log 2 n
  let K := n / z
  let W := afUpperEndpoint n
  let D := 1000 * B ^ 2
  let u := n / (6 * B)
  let t := aCard - K ^ 2
  have hBtwo : 2 ≤ B := by dsimp [B] at hB ⊢; omega
  have hBpos : 0 < B := by omega
  have hgeo := af_seed_geometry hBtwo hpow
  change 0 < h ∧ h * Nat.log 2 n + 2 * h ≤ y ∧ 0 < z ∧
    y ≤ 2 * z ∧ K ≤ 4 * B ^ 8 ∧ n ≤ 4 * B ^ 8 * z at hgeo
  rcases hgeo with ⟨_hh, _hbudget, _hz, _hyz, hK, _hnz⟩
  have hKsq : K ^ 2 ≤ 16 * B ^ 16 := by
    calc
      K ^ 2 ≤ (4 * B ^ 8) ^ 2 := Nat.pow_le_pow_left hK 2
      _ = 16 * B ^ 16 := by ring
  have hdiv : n / (3 * B) ≤ n / s := by
    exact Nat.div_le_div_left hsB hs
  have huDouble : 2 * u ≤ n / (3 * B) := by
    have hden : 0 < 3 * B := by positivity
    apply (Nat.le_div_iff_mul_le hden).2
    calc
      (2 * u) * (3 * B) = u * (6 * B) := by ring
      _ ≤ n := by
        dsimp [u]
        exact Nat.div_mul_le_self n (6 * B)
  have hut : 2 * u ≤ t := by
    dsimp [t, afCardThreshold] at hcard ⊢
    change n / s + 16 * B ^ 16 + s ≤ aCard at hcard
    omega
  have htri : 2 * u ^ 2 ≤ t * (t + 1) / 2 := by
    have hfour : 4 * u ^ 2 ≤ t * (t + 1) := by
      calc
        4 * u ^ 2 = (2 * u) * (2 * u) := by ring
        _ ≤ t * t := Nat.mul_le_mul hut hut
        _ ≤ t * (t + 1) := Nat.mul_le_mul_left t (Nat.le_succ t)
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    convert hfour using 1 <;> ring
  have htwoPow : 2 * B ^ 38 ≤ n := by
    change B ^ 38 ≤ n / 2 at hpow
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hpow
  have huSix : 6 ≤ u := by
    have hsmall : 6 * (6 * B) ≤ n := by
      calc
        6 * (6 * B) ≤ B ^ 2 := by nlinarith
        _ ≤ 2 * B ^ 38 := by
          have hp : B ^ 2 ≤ B ^ 38 := Nat.pow_le_pow_right hBpos (by omega)
          omega
        _ ≤ n := htwoPow
    exact (Nat.le_div_iff_mul_le (by positivity : 0 < 6 * B)).2 hsmall
  have hnltU : n < (6 * B) * (u + 1) := by
    simpa [u] using Nat.lt_mul_div_succ n (by positivity : 0 < 6 * B)
  have hnU : n ≤ 7 * B * u := by
    calc
      n ≤ (6 * B) * (u + 1) := Nat.le_of_lt hnltU
      _ ≤ 7 * B * u := by nlinarith
  have hyB : y * B ^ 8 ≤ n := by
    change (n / B ^ 8) * B ^ 8 ≤ n
    exact Nat.div_mul_le_self n (B ^ 8)
  have hcoeffY : 1000 * B ^ 2 ≤ B ^ 8 := by
    have hbase : 1000 ≤ B := by omega
    have hp : B ≤ B ^ 6 := by
      simpa using Nat.pow_le_pow_right hBpos (show 1 ≤ 6 by omega)
    calc
      1000 * B ^ 2 ≤ B * B ^ 2 := Nat.mul_le_mul_right _ hbase
      _ ≤ B ^ 6 * B ^ 2 := Nat.mul_le_mul_right _ hp
      _ = B ^ 8 := by ring
  have hcoeffK : 8000 * B ^ 10 ≤ n := by
    have hbase : 8000 ≤ B := by omega
    calc
      8000 * B ^ 10 ≤ B * B ^ 10 := Nat.mul_le_mul_right _ hbase
      _ = B ^ 11 := by ring
      _ ≤ 2 * B ^ 38 := by
        have hp : B ^ 11 ≤ B ^ 38 := Nat.pow_le_pow_right hBpos (by omega)
        omega
      _ ≤ n := htwoPow
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hWdef : W = n ^ 2 / D := by rfl
  have hYle : y * n ≤ W := by
    rw [hWdef, Nat.le_div_iff_mul_le hDpos]
    calc
      y * n * D = y * n * (1000 * B ^ 2) := rfl
      _ ≤ y * n * B ^ 8 := Nat.mul_le_mul_left (y * n) hcoeffY
      _ = (y * B ^ 8) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n hyB
      _ = n ^ 2 := by ring
  have hKleW : (2 * K) * n ≤ W := by
    rw [hWdef, Nat.le_div_iff_mul_le hDpos]
    calc
      (2 * K) * n * D ≤ (2 * (4 * B ^ 8)) * n * D := by gcongr
      _ = (8000 * B ^ 10) * n := by
        dsimp [D]
        ring
      _ ≤ n * n := Nat.mul_le_mul_right n hcoeffK
      _ = n ^ 2 := by ring
  have hsumW : W + (y + 2 * K) * n ≤ 3 * W := by
    have hsplit : (y + 2 * K) * n = y * n + (2 * K) * n := by ring
    rw [hsplit]
    omega
  have hnSq : n ^ 2 ≤ 49 * B ^ 2 * u ^ 2 := by
    calc
      n ^ 2 ≤ (7 * B * u) ^ 2 := Nat.pow_le_pow_left hnU 2
      _ = 49 * B ^ 2 * u ^ 2 := by ring
  have hthreeW : 3 * W ≤ u ^ 2 := by
    apply Nat.le_of_mul_le_mul_right (c := D) ?_ hDpos
    calc
      (3 * W) * D = 3 * (W * D) := by ring
      _ ≤ 3 * n ^ 2 := by
        gcongr
        rw [hWdef]
        exact Nat.div_mul_le_self (n ^ 2) D
      _ ≤ 3 * (49 * B ^ 2 * u ^ 2) := Nat.mul_le_mul_left 3 hnSq
      _ ≤ u ^ 2 * D := by
        dsimp [D]
        rw [show 3 * (49 * B ^ 2 * u ^ 2) =
          147 * (B ^ 2 * u ^ 2) by ring]
        rw [show u ^ 2 * (1000 * B ^ 2) =
          1000 * (B ^ 2 * u ^ 2) by ring]
        exact Nat.mul_le_mul_right _ (by omega)
  change W + (y + 2 * K) * n ≤ t * (t + 1) / 2
  have huTwo : u ^ 2 ≤ 2 * u ^ 2 := by omega
  exact hsumW.trans (hthreeW.trans (huTwo.trans htri))

lemma af_target_margin {n s : ℕ}
    (hB : 200000 < binaryScale n)
    (hpow : binaryScale n ^ 38 ≤ n / 2)
    (hsB : s ≤ 3 * binaryScale n) :
    (afLowerEndpoint n + s * n) * s ≤ afUpperEndpoint n := by
  let B := binaryScale n
  let R := afLowerEndpoint n
  let V := afUpperEndpoint n
  let D := 1000 * B ^ 2
  have hBtwo : 2 ≤ B := by dsimp [B] at hB ⊢; omega
  have hBpos : 0 < B := by omega
  have hsB' : s ≤ 3 * B := by simpa [B] using hsB
  have hRmul : R * (10000 * B ^ 3) ≤ n ^ 2 := by
    dsimp [R, afLowerEndpoint]
    exact Nat.div_mul_le_self (n ^ 2) (10000 * B ^ 3)
  have htermR : 2 * (((R * s) * D)) ≤ n ^ 2 := by
    calc
      2 * ((R * s) * D) ≤ 2 * ((R * (3 * B)) * D) := by gcongr
      _ = R * (6000 * B ^ 3) := by
        dsimp [D]
        ring
      _ ≤ R * (10000 * B ^ 3) := by
        exact Nat.mul_le_mul_left R
          (Nat.mul_le_mul_right (B ^ 3) (by omega))
      _ ≤ n ^ 2 := hRmul
  have htwoPow : 2 * B ^ 38 ≤ n := by
    change B ^ 38 ≤ n / 2 at hpow
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hpow
  have hsmall : 18000 * B ^ 4 ≤ n := by
    have hbase : 18000 ≤ B := by omega
    calc
      18000 * B ^ 4 ≤ B * B ^ 4 := Nat.mul_le_mul_right _ hbase
      _ = B ^ 5 := by ring
      _ ≤ 2 * B ^ 38 := by
        have hp : B ^ 5 ≤ B ^ 38 := Nat.pow_le_pow_right hBpos (by omega)
        omega
      _ ≤ n := htwoPow
  have htermS : 2 * (((s * n) * s) * D) ≤ n ^ 2 := by
    calc
      2 * ((s * n * s) * D) ≤
          2 * (((3 * B) * n * (3 * B)) * D) := by gcongr
      _ = (18000 * B ^ 4) * n := by
        dsimp [D]
        ring
      _ ≤ n * n := Nat.mul_le_mul_right n hsmall
      _ = n ^ 2 := by ring
  have hDpos : 0 < D := by dsimp [D]; positivity
  change (R + s * n) * s ≤ n ^ 2 / D
  rw [Nat.le_div_iff_mul_le hDpos]
  rw [add_mul, add_mul]
  have hleft : 2 * ((R * s) * D) ≤ n ^ 2 := htermR
  have hright : 2 * (((s * n) * s) * D) ≤ n ^ 2 := htermS
  omega

/-- The quantitative Alon--Freiman representation theorem specialized to
the polylogarithmic parameters used below. -/
lemma af_uniform_representation {n s : ℕ} {A : Finset ℕ}
    (hnlarge : 10000000 < n)
    (hB : 256 * (512 * 1001) ^ 2 < binaryScale n)
    (hpow : binaryScale n ^ 38 ≤ n / 2)
    (hs : 0 < s) (hsB : s ≤ 3 * binaryScale n)
    (hA : A ⊆ Finset.Icc 1 n)
    (hcard : afCardThreshold n s ≤ A.card) :
    ∃ q G, 0 < q ∧ q ≤ s ∧ G = LocalLimit.divisiblePart A q ∧
      LocalLimit.CoversMultiples G q (afLowerEndpoint n) (afUpperEndpoint n) := by
  let B := binaryScale n
  let y := afSeedSize n
  let h := afThickness n
  let z := y - h * Nat.log 2 n
  let K := n / z
  have hBlarge : 200000 < B := by dsimp [B] at hB ⊢; omega
  have hBtwo : 2 ≤ B := by omega
  have hBpos : 0 < B := by omega
  have hscale : s ≤ B ^ 8 := by
    calc
      s ≤ 3 * B := by simpa [B] using hsB
      _ ≤ B ^ 2 := by nlinarith
      _ ≤ B ^ 8 := Nat.pow_le_pow_right hBpos (by omega)
  have hyDiv : y ≤ n / s := by
    change n / B ^ 8 ≤ n / s
    exact Nat.div_le_div_left hscale hs
  have hyCard : y ≤ A.card := by
    have hbase : n / s ≤ A.card := by
      dsimp [afCardThreshold] at hcard
      omega
    exact hyDiv.trans hbase
  obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hyCard
  have hgeo := af_seed_geometry hBtwo hpow
  change 0 < h ∧ h * Nat.log 2 n + 2 * h ≤ y ∧ 0 < z ∧
    y ≤ 2 * z ∧ K ≤ 4 * B ^ 8 ∧ n ≤ 4 * B ^ 8 * z at hgeo
  rcases hgeo with ⟨hhpos, hbudget, hzpos, _hyz, hK, _hnz⟩
  have hKsq : K ^ 2 ≤ 16 * B ^ 16 := by
    calc
      K ^ 2 ≤ (4 * B ^ 8) ^ 2 := Nat.pow_le_pow_left hK 2
      _ = 16 * B ^ 16 := by ring
  have hmodulus : n / (s + 1) < A.card - K ^ 2 := by
    have hdiv : n / (s + 1) ≤ n / s :=
      Nat.div_le_div_left (Nat.le_succ s) hs
    dsimp [afCardThreshold] at hcard
    change n / s + 16 * B ^ 16 + s ≤ A.card at hcard
    omega
  have hlower : y * n + 2 * K * n ≤ afLowerEndpoint n := by
    simpa [B, y, h, z, K] using af_lower_numeric hBlarge hpow
  have hupper : afUpperEndpoint n + (y + 2 * K) * n ≤
      let t := A.card - K ^ 2
      t * (t + 1) / 2 := by
    simpa [B, y, h, z, K] using
      af_upper_numeric hBlarge hpow hs hsB hcard
  have hdecay : ∀ x : ℕ, z ≤ x → x ≤ y →
      Real.exp (-LocalLimit.minorEnergy n x h) <
        3 * LocalLimit.coreRadius n x / 4 := by
    intro x hxz hxy
    simpa [B, y, h, z] using af_seed_decay hnlarge hB hpow hxz hxy
  have hbudgetS : h * Nat.log 2 n + 2 * h ≤ S.card := by
    simpa [hScard, y] using hbudget
  have hzS : 0 < S.card - h * Nat.log 2 n := by
    simpa [hScard, y, z] using hzpos
  have hmodulusS : n / (s + 1) <
      A.card - (n / (S.card - h * Nat.log 2 n)) ^ 2 := by
    simpa [hScard, y, z, K] using hmodulus
  have hlowerS : S.card * n +
      2 * (n / (S.card - h * Nat.log 2 n)) * n ≤ afLowerEndpoint n := by
    simpa [hScard, y, z, K] using hlower
  have hupperS : afUpperEndpoint n +
      (S.card + 2 * (n / (S.card - h * Nat.log 2 n))) * n ≤
      let t := A.card - (n / (S.card - h * Nat.log 2 n)) ^ 2
      t * (t + 1) / 2 := by
    simpa [hScard, y, z, K] using hupper
  apply LocalLimit.uniform_divisible_representation
    (n := n) (h := h) (s := s) (R := afLowerEndpoint n)
    (V := afUpperEndpoint n) (S := S)
    (by omega) hs hhpos hA hSA hbudgetS
  · intro x hxz hxy
    apply hdecay x
    · simpa [hScard, y, z] using hxz
    · simpa [hScard, y] using hxy
  · exact hzS
  · exact hmodulusS
  · exact hlowerS
  · exact hupperS

/-- The maximal-LCM target is represented by every set at the explicit
Alon--Freiman threshold, once the fixed asymptotic inequalities hold. -/
lemma afTarget_mem_subsetSum {n : ℕ} {A : Finset ℕ}
    (hnlarge : 10000000 < n)
    (hB : 256 * (512 * 1001) ^ 2 < binaryScale n)
    (hpow : binaryScale n ^ 38 ≤ n / 2)
    (hX : 1 ≤ afUpperEndpoint n)
    (hsB : afTargetNondivisor n ≤ 3 * binaryScale n)
    (hA : A ⊆ Finset.Icc 1 n)
    (hcard : afCardThreshold n (afTargetNondivisor n) ≤ A.card) :
    afTarget n ∈ A.subsetSum := by
  let X := afUpperEndpoint n
  let m := afTarget n
  let s := afTargetNondivisor n
  have hmpos : 0 < m := by dsimp [m, afTarget]; exact Nat.lcmUpto_pos _
  have hspos : 0 < s := by dsimp [s, afTargetNondivisor]; omega
  have hsleast : leastNondivisor m hmpos = s := by
    simpa [X, m, s, afTarget, afTargetNondivisor] using
      leastNondivisor_lcmCutoff (X := X) (by simpa [X] using hX)
  have hmUpper : m ≤ X := by
    simpa [X, m, afTarget] using
      lcmUpto_cutoff_le (X := X) (by simpa [X] using hX)
  have hmargin : (afLowerEndpoint n + s * n) * s ≤ X := by
    simpa [X, s] using af_target_margin
      (show 200000 < binaryScale n by omega) hpow hsB
  have hnext : X < Nat.lcmUpto (lcmCutoff X + 1) :=
    cutoff_next_lcm_gt (by simpa [X] using hX)
  have hnextUpper : Nat.lcmUpto (lcmCutoff X + 1) ≤ s * m := by
    simpa [s, m, X, afTargetNondivisor, afTarget] using
      lcmUpto_succ_le_mul (lcmCutoff X)
  have hXsm : X < s * m := hnext.trans_le hnextUpper
  have hlowDiv : afLowerEndpoint n + s * n ≤ X / s :=
    (Nat.le_div_iff_mul_le hspos).2 hmargin
  have hdivM : X / s < m := Nat.div_lt_of_lt_mul hXsm
  have hmLower : afLowerEndpoint n + s * n ≤ m :=
    hlowDiv.trans (Nat.le_of_lt hdivM)
  obtain ⟨q, G, hqpos, hqs, hG, hcover⟩ :=
    af_uniform_representation hnlarge hB hpow hspos
      (by simpa [s] using hsB) hA (by simpa [s] using hcard)
  have hGA : G ⊆ A := by
    intro g hg
    rw [hG] at hg
    exact (Finset.mem_filter.mp hg).1
  rcases hqs.eq_or_lt with hqsEq | hqsLt
  · subst q
    have hsPP : IsPrimePow s := by
      rw [← hsleast]
      exact leastNondivisor_isPrimePow m hmpos
    obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff s).mp hsPP
    let C := A.filter fun x => ¬s ∣ x
    have hdivCard : (LocalLimit.divisiblePart A s).card ≤ n / s := by
      have hmul := LocalLimit.divisiblePart_card_mul_le hspos hA
      exact (Nat.le_div_iff_mul_le hspos).2 (by
        simpa [Nat.mul_comm] using hmul)
    have hsplit : (LocalLimit.divisiblePart A s).card + C.card = A.card := by
      simpa [LocalLimit.divisiblePart, C] using
        Finset.card_filter_add_card_filter_not
          (s := A) (p := fun x => s ∣ x)
    have hCcard : s - 1 ≤ C.card := by
      dsimp [afCardThreshold] at hcard
      change n / s + 16 * binaryScale n ^ 16 + s ≤ A.card at hcard
      omega
    obtain ⟨T, hTC, hTcard⟩ := Finset.exists_subset_card_eq hCcard
    let d := p ^ (a - 1)
    have hdpos : 0 < d := by dsimp [d]; exact pow_pos hp.pos _
    have hdlt : d < s := by
      rw [← hpa]
      dsimp [d]
      exact Nat.pow_lt_pow_right hp.one_lt (by omega)
    have hdvdM : d ∣ m := by
      rw [← hsleast] at hdlt
      exact dvd_of_pos_lt_leastNondivisor hmpos hdpos hdlt
    let i := m / d
    have hi : i * d = m := by
      dsimp [i]
      simpa [Nat.mul_comm] using Nat.mul_div_cancel' hdvdM
    have hnondiv : ∀ x ∈ T, ¬p ^ a ∣ x := by
      intro x hx
      rw [hpa]
      exact (Finset.mem_filter.mp (hTC hx)).2
    have hTcardPA : p ^ a - 1 ≤ T.card := by
      rw [hTcard, hpa]
    obtain ⟨u, huT, huCast⟩ :=
      exists_subset_sum_mod_primePower (i := i) hp ha (S := T)
        hTcardPA hnondiv
    have huCastM : (u : ZMod s) = (m : ZMod s) := by
      rw [← hpa]
      calc
        (u : ZMod (p ^ a)) = (i * p ^ (a - 1) : ZMod (p ^ a)) := huCast
        _ = (m : ZMod (p ^ a)) := by
          have hi' : i * p ^ (a - 1) = m := by simpa [d] using hi
          rw [← hi']
          rw [← Nat.cast_pow, ← Nat.cast_mul]
    have huBound : u ≤ (s - 1) * n := by
      obtain ⟨U, hUT, rfl⟩ := Finset.mem_subsetSum_iff.mp huT
      calc
        ∑ x ∈ U, x ≤ ∑ _x ∈ U, n := Finset.sum_le_sum fun x hx => by
          have hxA : x ∈ A := (Finset.mem_filter.mp (hTC (hUT hx))).1
          exact (Finset.mem_Icc.mp (hA hxA)).2
        _ = U.card * n := by simp
        _ ≤ T.card * n := Nat.mul_le_mul_right n (Finset.card_le_card hUT)
        _ = (s - 1) * n := by rw [hTcard]
    have huSn : u ≤ s * n := huBound.trans
      (Nat.mul_le_mul_right n (Nat.sub_le s 1))
    have hsnM : s * n ≤ m :=
      (Nat.le_add_left (s * n) (afLowerEndpoint n)).trans hmLower
    have huM : u ≤ m := huSn.trans hsnM
    have hresLower : afLowerEndpoint n ≤ m - u := by
      apply Nat.le_sub_of_add_le
      exact (Nat.add_le_add_left huSn (afLowerEndpoint n)).trans hmLower
    have hresUpper : m - u ≤ afUpperEndpoint n := by
      exact (Nat.sub_le m u).trans (by simpa [X] using hmUpper)
    have hsRes : s ∣ m - u := by
      have hmodEq : u ≡ m [MOD s] := by
        exact (ZMod.natCast_eq_natCast_iff u m s).mp huCastM
      exact hmodEq.dvd'
    have hresG : m - u ∈ G.subsetSum :=
      hcover (m - u) hresLower hresUpper hsRes
    have hdisj : Disjoint G T := by
      rw [Finset.disjoint_left]
      intro x hxG hxT
      have hxDiv : s ∣ x := by
        rw [hG] at hxG
        exact (Finset.mem_filter.mp hxG).2
      exact (Finset.mem_filter.mp (hTC hxT)).2 hxDiv
    have hadd := LocalLimit.subsetSum_add_of_disjoint hdisj hresG huT
    have hUnion : G ∪ T ⊆ A := Finset.union_subset hGA
      (hTC.trans (Finset.filter_subset _ _))
    have hmUnion : m ∈ (G ∪ T).subsetSum := by
      simpa [Nat.sub_add_cancel huM] using hadd
    exact Finset.subsetSum_mono hUnion hmUnion
  · have hqDvd : q ∣ m := by
      apply dvd_of_pos_lt_leastNondivisor hmpos hqpos
      simpa [hsleast] using hqsLt
    have hmG : m ∈ G.subsetSum :=
      hcover m (by omega) (by simpa [X] using hmUpper) hqDvd
    exact Finset.subsetSum_mono hGA hmG

lemma eventually_erdosF_lt_afCardThreshold :
    ∀ᶠ n : ℕ in atTop,
      erdosF n < afCardThreshold n (afTargetNondivisor n) := by
  filter_upwards
    [eventually_gt_atTop 10000000,
      eventually_binaryScale_ge (256 * (512 * 1001) ^ 2 + 1),
      Erdos387.eventually_binaryLogScale_pow_le_half 38,
      eventually_one_le_afUpperEndpoint,
      eventually_afTargetNondivisor_le_three_binaryScale]
      with n hn hB hpow hX hsB
  change binaryScale n ^ 38 ≤ n / 2 at hpow
  apply erdosF_lt_of_all_large_represent (Nat.lcmUpto_pos _)
  intro A hA hcard
  exact afTarget_mem_subsetSum hn (by omega) hpow hX hsB hA hcard

lemma natDiv_afTargetNondivisor_ratio_tendsto_half :
    Tendsto (fun n : ℕ =>
      ((n / afTargetNondivisor n : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 (1 / 2 : ℝ)) := by
  let s : ℕ → ℕ := afTargetNondivisor
  let v : ℕ → ℝ := fun n =>
    ((n : ℝ) / s n) / ((n : ℝ) / Real.log (n : ℝ))
  let d : ℕ → ℝ := fun n =>
    v n - ((n / s n : ℕ) : ℝ) / ((n : ℝ) / Real.log (n : ℝ))
  have hsRatio : Tendsto (fun n : ℕ =>
      (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 2) := by
    simpa [s] using afTargetNondivisor_ratio_tendsto_two
  have hsTop : Tendsto (fun n : ℕ => (s n : ℝ)) atTop atTop := by
    have hsNat : Tendsto s atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro N
      obtain ⟨N₀, hN₀⟩ := (tendsto_atTop_atTop.mp afCutoff_tendsto_atTop) N
      refine ⟨N₀, fun n hn => ?_⟩
      exact (hN₀ n hn).trans (Nat.le_succ _)
    exact tendsto_natCast_atTop_atTop.comp hsNat
  have hv : Tendsto v atTop (𝓝 (1 / 2 : ℝ)) := by
    have hinv := hsRatio.inv₀ (by norm_num : (2 : ℝ) ≠ 0)
    have hinv' : Tendsto (fun n =>
        ((s n : ℝ) / Real.log (n : ℝ))⁻¹)
        atTop (𝓝 (1 / 2 : ℝ)) := by
      convert hinv using 1 <;> norm_num
    apply hinv'.congr'
    filter_upwards
      [eventually_gt_atTop 1,
        hsTop.eventually (eventually_ne_atTop 0)] with n hn hs
    have hnR : (0 : ℝ) < n := by positivity
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    dsimp [v]
    field_simp
  have herr : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n)
      atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hdnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ d n := by
    filter_upwards
      [eventually_gt_atTop 1,
        hsTop.eventually (eventually_gt_atTop 0)] with n hn hs
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hnorm : 0 < (n : ℝ) / Real.log (n : ℝ) := by positivity
    dsimp [d, v]
    exact sub_nonneg.mpr
      (div_le_div_of_nonneg_right Nat.cast_div_le hnorm.le)
  have hdle : ∀ᶠ n : ℕ in atTop, d n ≤ Real.log (n : ℝ) / n := by
    filter_upwards
      [eventually_gt_atTop 1,
        hsTop.eventually (eventually_gt_atTop 0)] with n hn hs
    have hnR : (0 : ℝ) < n := by positivity
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hnorm : 0 < (n : ℝ) / Real.log (n : ℝ) := by positivity
    have hfloor := real_div_sub_natDiv_lt_one (n := n) (q := s n)
      (by exact_mod_cast hs)
    dsimp [d, v]
    calc
      (n : ℝ) / s n / ((n : ℝ) / Real.log (n : ℝ)) -
          (n / s n : ℕ) / ((n : ℝ) / Real.log (n : ℝ)) =
          ((n : ℝ) / s n - (n / s n : ℕ)) /
            ((n : ℝ) / Real.log (n : ℝ)) := by ring
      _ ≤ 1 / ((n : ℝ) / Real.log (n : ℝ)) :=
        div_le_div_of_nonneg_right hfloor.le hnorm.le
      _ = Real.log (n : ℝ) / n := by field_simp
  have hd : Tendsto d atTop (𝓝 0) := squeeze_zero' hdnonneg hdle herr
  have hsub := hv.sub hd
  simpa only [sub_zero] using hsub.congr'
    (Filter.Eventually.of_forall fun n => by simp [d, s])

lemma afThreshold_seed_error_tendsto_zero :
    Tendsto (fun n : ℕ =>
      ((16 * binaryScale n ^ 16 : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 0) := by
  have hlog17 : Tendsto (fun n : ℕ =>
      Real.log (n : ℝ) ^ 17 / (n : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_pow_atTop 1 17 Real.zero_lt_one).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hBzero : Tendsto (fun n : ℕ =>
      ((16 * binaryScale n ^ 16 : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 0) := by
    have hmajor : Tendsto (fun n : ℕ =>
        (16 * 3 ^ 16 : ℝ) *
          (Real.log (n : ℝ) ^ 17 / (n : ℝ))) atTop (𝓝 0) := by
      simpa using hlog17.const_mul (16 * 3 ^ 16 : ℝ)
    apply squeeze_zero' _ _ hmajor
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hlogpos : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      exact div_nonneg (Nat.cast_nonneg _)
        (div_nonneg (Nat.cast_nonneg _) hlogpos.le)
    · filter_upwards [eventually_ge_atTop 4] with n hn
      have hnposR : (0 : ℝ) < n := by positivity
      have hlogpos : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hscale : (binaryScale n : ℝ) ≤ 3 * Real.log (n : ℝ) := by
        simpa [binaryScale] using
          Erdos387.binaryLogScale_cast_le_three_mul_log hn
      rw [show ((16 * binaryScale n ^ 16 : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) =
          16 * (binaryScale n : ℝ) ^ 16 * Real.log (n : ℝ) / n by
        norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        field_simp
        ]
      calc
        16 * (binaryScale n : ℝ) ^ 16 * Real.log (n : ℝ) / n ≤
            16 * (3 * Real.log (n : ℝ)) ^ 16 *
              Real.log (n : ℝ) / n := by
          gcongr
        _ = (16 * 3 ^ 16 : ℝ) *
            (Real.log (n : ℝ) ^ 17 / n) := by ring
  exact hBzero

lemma afThreshold_modulus_error_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (afTargetNondivisor n : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 0) := by
  have hlog2 : Tendsto (fun n : ℕ =>
      Real.log (n : ℝ) ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_pow_atTop 1 2 Real.zero_lt_one).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hsZero : Tendsto (fun n : ℕ =>
      (afTargetNondivisor n : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 0) := by
    have hmajor : Tendsto (fun n : ℕ =>
        (9 : ℝ) * (Real.log (n : ℝ) ^ 2 / (n : ℝ)))
        atTop (𝓝 0) := by
      simpa using hlog2.const_mul (9 : ℝ)
    apply squeeze_zero' _ _ hmajor
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hlogpos : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      exact div_nonneg (Nat.cast_nonneg _)
        (div_nonneg (Nat.cast_nonneg _) hlogpos.le)
    · filter_upwards
        [eventually_ge_atTop 4,
          eventually_afTargetNondivisor_le_three_binaryScale]
        with n hn hsB
      have hnposR : (0 : ℝ) < n := by positivity
      have hlogpos : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hscale : (binaryScale n : ℝ) ≤ 3 * Real.log (n : ℝ) := by
        simpa [binaryScale] using
          Erdos387.binaryLogScale_cast_le_three_mul_log hn
      have hsR : (afTargetNondivisor n : ℝ) ≤
          9 * Real.log (n : ℝ) := by
        have hsR0 : (afTargetNondivisor n : ℝ) ≤
            3 * (binaryScale n : ℝ) := by exact_mod_cast hsB
        calc
          (afTargetNondivisor n : ℝ) ≤ 3 * (binaryScale n : ℝ) := hsR0
          _ ≤ 9 * Real.log (n : ℝ) := by nlinarith
      rw [show (afTargetNondivisor n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) =
          (afTargetNondivisor n : ℝ) * Real.log (n : ℝ) / n by
        field_simp]
      calc
        (afTargetNondivisor n : ℝ) * Real.log (n : ℝ) / n ≤
            (9 * Real.log (n : ℝ)) * Real.log (n : ℝ) / n := by
          gcongr
        _ = (9 : ℝ) * (Real.log (n : ℝ) ^ 2 / n) := by ring
  exact hsZero

lemma natCast_add_div_real (a b : ℕ) (z : ℝ) :
    ((a + b : ℕ) : ℝ) / z = (a : ℝ) / z + (b : ℝ) / z := by
  norm_num only [Nat.cast_add]
  ring

lemma afThreshold_polylog_error_tendsto_zero :
    Tendsto (fun n : ℕ =>
      ((16 * binaryScale n ^ 16 + afTargetNondivisor n : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 0) := by
  have hadd : Tendsto (fun n : ℕ =>
      ((16 * binaryScale n ^ 16 : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) +
        (afTargetNondivisor n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 ((0 : ℝ) + 0)) :=
    afThreshold_seed_error_tendsto_zero.add
      afThreshold_modulus_error_tendsto_zero
  have hadd' : Tendsto (fun n : ℕ =>
      ((16 * binaryScale n ^ 16 : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) +
        (afTargetNondivisor n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 0) := by
    rw [add_zero] at hadd
    exact hadd
  apply hadd'.congr'
  exact Filter.Eventually.of_forall fun n =>
    (natCast_add_div_real (16 * binaryScale n ^ 16)
      (afTargetNondivisor n) ((n : ℝ) / Real.log (n : ℝ))).symm

lemma cardThreshold_normalize_eq_aux (n s B : ℕ) :
    ((n / s + 16 * B ^ 16 + s : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ)) =
      ((n / s : ℕ) : ℝ) / ((n : ℝ) / Real.log (n : ℝ)) +
        ((16 * B ^ 16 + s : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) := by
  rw [Nat.add_assoc]
  exact natCast_add_div_real (n / s) (16 * B ^ 16 + s)
    ((n : ℝ) / Real.log (n : ℝ))

lemma afCardThreshold_normalize_eq (n : ℕ) :
    (afCardThreshold n (afTargetNondivisor n) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ)) =
      ((n / afTargetNondivisor n : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) +
        ((16 * binaryScale n ^ 16 + afTargetNondivisor n : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) := by
  exact cardThreshold_normalize_eq_aux n (afTargetNondivisor n) (binaryScale n)

lemma afCardThreshold_ratio_tendsto_half :
    Tendsto (fun n : ℕ =>
      (afCardThreshold n (afTargetNondivisor n) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hadd : Tendsto (fun n : ℕ =>
      ((n / afTargetNondivisor n : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) +
        ((16 * binaryScale n ^ 16 + afTargetNondivisor n : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (𝓝 ((1 / 2 : ℝ) + 0)) :=
    natDiv_afTargetNondivisor_ratio_tendsto_half.add
      afThreshold_polylog_error_tendsto_zero
  have hadd' : Tendsto (fun n : ℕ =>
      ((n / afTargetNondivisor n : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) +
        ((16 * binaryScale n ^ 16 + afTargetNondivisor n : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    rw [add_zero] at hadd
    exact hadd
  apply hadd'.congr'
  exact Filter.Eventually.of_forall fun n =>
    (afCardThreshold_normalize_eq n).symm

lemma eventually_erdosF_ratio_le_afCardThreshold :
    ∀ᶠ n : ℕ in atTop,
      (erdosF n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)) ≤
        (afCardThreshold n (afTargetNondivisor n) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) := by
  filter_upwards [eventually_erdosF_lt_afCardThreshold,
      eventually_gt_atTop 1] with n hbound hn
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hnorm : 0 ≤ (n : ℝ) / Real.log (n : ℝ) := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hbound.le) hnorm

lemma exists_gt_two_inv_gt {a : ℝ} (ha : a < 1 / 2) :
    ∃ c : ℝ, 2 < c ∧ a < c⁻¹ := by
  by_cases ha0 : 0 < a
  · let c := (2 + a⁻¹) / 2
    have h2inv : 2 < a⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ ha0]
      nlinarith
    have hc2 : 2 < c := by dsimp [c]; linarith
    have hcinv : c < a⁻¹ := by dsimp [c]; linarith
    have hcpos : 0 < c := by linarith
    have hac : a * c < 1 := by
      calc
        a * c < a * a⁻¹ := mul_lt_mul_of_pos_left hcinv ha0
        _ = 1 := mul_inv_cancel₀ ha0.ne'
    have hainv : a < c⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hcpos]
      simpa [mul_comm] using hac
    exact ⟨c, hc2, hainv⟩
  · refine ⟨3, by norm_num, ?_⟩
    have hale : a ≤ 0 := le_of_not_gt ha0
    norm_num
    linarith

lemma eventually_lt_erdosF_ratio_of_lt_inv {a c : ℝ}
    (hc : 2 < c) (ha : a < c⁻¹) :
    ∀ᶠ n : ℕ in atTop,
      a < (erdosF n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)) := by
  have hcut : Tendsto (fun n : ℕ =>
      ((n / primeCutoff c n : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 c⁻¹) :=
    natDiv_primeCutoff_ratio (c := c) (by linarith)
  have hlower : ∀ᶠ n : ℕ in atTop,
      a < ((n / primeCutoff c n : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ)) :=
    (tendsto_order.1 hcut).1 a ha
  filter_upwards [hlower, erdosF_ratio_lower_bound c hc]
    with n hn hbound
  exact hn.trans_le hbound

/-- The exact extremal function in Problem 771 is asymptotic to
`n / (2 log n)`. -/
theorem erdosF_asymptotic :
    Tendsto (fun n : ℕ =>
      (erdosF n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨c, hc, hac⟩ := exists_gt_two_inv_gt ha
    exact eventually_lt_erdosF_ratio_of_lt_inv hc hac
  · intro b hb
    have hthreshold : ∀ᶠ n : ℕ in atTop,
        (afCardThreshold n (afTargetNondivisor n) : ℝ) /
            ((n : ℝ) / Real.log (n : ℝ)) < b :=
      (tendsto_order.1 afCardThreshold_ratio_tendsto_half).2 b hb
    filter_upwards [eventually_erdosF_ratio_le_afCardThreshold, hthreshold]
      with n hupper hthreshold
    exact hupper.trans_lt hthreshold

/-- Resolution of Erdős Problem 771 in the repository's Boolean-answer
convention. -/
theorem erdos_771 :
    answer(True) ↔
      Tendsto (fun n : ℕ =>
        (erdosF n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)))
        atTop (𝓝 (1 / 2 : ℝ)) := by
  constructor
  · intro _
    exact erdosF_asymptotic
  · intro _
    trivial

#print axioms erdos_771

end

end Erdos771
