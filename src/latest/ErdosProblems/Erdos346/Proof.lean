import Mathlib

/- Ported to Lean/Mathlib 4.33.0; source digest and changes are in README.md. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A Counterexample to Erdős Problem 346

Erdős and Graham asked whether every strictly increasing sequence `A = (aₙ)` of
positive integers that

* remains *complete* (every sufficiently large integer is a finite subset sum)
  after the deletion of any finite subsequence, yet
* becomes *incomplete* after the deletion of any infinite subsequence,

and whose consecutive quotients are bounded below by `1 + ε`, must satisfy
`aₙ₊₁ / aₙ → φ`, where `φ = (1 + √5) / 2` is the golden ratio.

This file formalises a counterexample, giving a negative answer.  We construct a
sequence `A` enjoying both deletion properties, with `aₙ₊₁ / aₙ ≥ 6/5` throughout,
yet whose quotients have two distinct subsequential limits `φ` and `φ + 1/4`; in
particular `(aₙ₊₁ / aₙ)` does not converge.  The packaged statement is `erdos346`.

## Construction

`A` interleaves long *unperturbed* stretches, governed by Graham's inhomogeneous
Fibonacci recurrence `aₙ₊₂ = aₙ₊₁ + aₙ ± 1`, with sparse *perturbations*
`b_{Nⱼ} = ⌊a_{Nⱼ} / 4⌋` installed at a rapidly increasing sequence of indices `Nⱼ`.

* During the unperturbed stretches Graham's bounded-gap descent makes every tail
  complete (`Approximation.every_tail_complete`) and forces the Fibonacci
  asymptotics `aₙ₊₁ / aₙ → φ`.
* A *permanent interval certificate* (`permanent_interval_certificate`) shows that
  once a tail represents a sufficiently long interval, every later admissible
  perturbation preserves its completeness; this yields finite-deletion completeness
  (`finite_deletion_complete`).
* A counting argument (`infinite_deletion_incomplete`) shows that `a_{i+1} - 1` is
  unrepresentable once infinitely many terms are deleted.
* The perturbations supply the second subsequential limit `φ + 1/4`.

## References

* [erdosproblems.com/346](https://www.erdosproblems.com/346)
* P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial
  Number Theory*, Monographies de L'Enseignement Mathématique 28 (1980), p. 57.
* R. L. Graham, *A property of Fibonacci numbers*, Fibonacci Quart. 2 (1964), 1–10.

## Conventions

Indexing starts at zero, so `a 0, a 1, …` correspond to `a₁, a₂, …` in the paper.
A set `X` of terms is *complete* when every sufficiently large integer lies in
`subsetSums`, the set of finite subset sums of `X`.  Deletion is represented by a set
of indices `D : Set ℕ`; as the constructed sequence is strictly increasing, this is
equivalent to deleting a subsequence of terms.
-/

open scoped BigOperators Topology goldenRatio
open Filter Set

namespace Erdos346

noncomputable section

/-- Finite sums of terms whose indices belong to `I`. -/
def subsetSums (a : ℕ → ℕ) (I : Set ℕ) : Set ℕ :=
  {t | ∃ F : Finset ℕ, ↑F ⊆ I ∧ ∑ i ∈ F, a i = t}

lemma subsetSums_mono {a : ℕ → ℕ} {I J : Set ℕ} (hIJ : I ⊆ J) :
    subsetSums a I ⊆ subsetSums a J := by
  rintro t ⟨F, hF, rfl⟩
  exact ⟨F, hF.trans hIJ, rfl⟩

lemma subsetSums_empty (a : ℕ → ℕ) (I : Set ℕ) : 0 ∈ subsetSums a I :=
  ⟨∅, by simp, by simp⟩

lemma subsetSums_singleton {a : ℕ → ℕ} {I : Set ℕ} {i : ℕ} (hi : i ∈ I) :
    a i ∈ subsetSums a I :=
  ⟨{i}, by simpa, by simp⟩

lemma subsetSums_add_new {a : ℕ → ℕ} {I J : Set ℕ} {i t : ℕ}
    (hIJ : I ⊆ J) (hiJ : i ∈ J) (hiI : i ∉ I) (ht : t ∈ subsetSums a I) :
    t + a i ∈ subsetSums a J := by
  obtain ⟨F, hF, hsum⟩ := ht
  have hiF : i ∉ F := fun h => hiI (hF h)
  refine ⟨insert i F, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_insert] at hj ⊢
    rcases hj with rfl | hj
    · exact hiJ
    · exact hIJ (hF hj)
  · rw [Finset.sum_insert hiF, hsum]
    omega

lemma subsetSums_complement {a : ℕ → ℕ} {B : Finset ℕ} {t : ℕ}
    (ht : t ∈ subsetSums a (↑B : Set ℕ)) :
    (∑ i ∈ B, a i) - t ∈ subsetSums a (↑B : Set ℕ) := by
  obtain ⟨F, hF, hsum⟩ := ht
  have hFB : F ⊆ B := by simpa using hF
  refine ⟨B \ F, by simp, ?_⟩
  rw [← Finset.sum_sdiff hFB, hsum, Nat.add_sub_cancel_right]

/-- The alternating unperturbed choice, shifted to zero-based indexing. -/
def parityPerturbation (n : ℕ) : ℕ := if Even n then 1 else 0

lemma parityPerturbation_le_one (n : ℕ) : parityPerturbation n ≤ 1 := by
  unfold parityPerturbation
  split <;> omega

lemma parityPerturbation_even {n : ℕ} (hn : Even n) : parityPerturbation n = 1 := by
  simp [parityPerturbation, hn]

lemma parityPerturbation_odd {n : ℕ} (hn : ¬ Even n) : parityPerturbation n = 0 := by
  simp [parityPerturbation, hn]

/--
The state at offset `r` consists of `a (r+3)` and the sum of all terms before it.
This tail-recursive presentation makes the defining prefix-sum recurrence transparent.
-/
def generatedState (b : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (5, 6)
  | r + 1 =>
      let s := generatedState b r
      (s.2 + b (r + 3), s.2 + s.1)

/-- The admissible sequence generated by the perturbation parameters `b`. -/
def generated (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | r + 3 => (generatedState b r).1

@[simp] lemma generated_zero (b : ℕ → ℕ) : generated b 0 = 1 := rfl
@[simp] lemma generated_one (b : ℕ → ℕ) : generated b 1 = 2 := rfl
@[simp] lemma generated_two (b : ℕ → ℕ) : generated b 2 = 3 := rfl
@[simp] lemma generated_three (b : ℕ → ℕ) : generated b 3 = 5 := rfl

@[simp] lemma generated_add_three (b : ℕ → ℕ) (r : ℕ) :
    generated b (r + 3) = (generatedState b r).1 := by
  rw [generated]

lemma generatedState_snd (b : ℕ → ℕ) (r : ℕ) :
    (generatedState b r).2 = ∑ i ∈ Finset.range (r + 3), generated b i := by
  induction r with
  | zero => norm_num [generatedState, generated]
  | succ r ih =>
      rw [generatedState, Finset.sum_range_succ, ih]
      congr 1

lemma generated_recurrence (b : ℕ → ℕ) {n : ℕ} (hn : 3 ≤ n) :
    generated b (n + 1) = (∑ i ∈ Finset.range n, generated b i) + b n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_comm 3 r]
  rw [show r + 3 + 1 = (r + 1) + 3 by omega, generated_add_three,
    generatedState, generatedState_snd]

lemma generatedState_lower (b : ℕ → ℕ) (r : ℕ) :
    5 ≤ (generatedState b r).1 ∧ 6 ≤ (generatedState b r).2 := by
  induction r with
  | zero => norm_num [generatedState]
  | succ r ih =>
      simp only [generatedState]
      constructor <;> omega

lemma generated_pos (b : ℕ → ℕ) (n : ℕ) : 0 < generated b n := by
  rcases n with _ | _ | _ | r
  · simp
  · simp
  · simp
  · rw [generated_add_three]
    exact (generatedState_lower b r).1.trans_lt' (by omega)

lemma generated_ge_four (b : ℕ → ℕ) {n : ℕ} (hn : 3 ≤ n) :
    4 ≤ generated b n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm, generated_add_three]
  exact (generatedState_lower b r).1.trans' (by omega)

/-- Sum of the first `n` terms. -/
def prefixSum (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, a i

@[simp] lemma prefixSum_zero (a : ℕ → ℕ) : prefixSum a 0 = 0 := by
  simp [prefixSum]

lemma prefixSum_succ (a : ℕ → ℕ) (n : ℕ) :
    prefixSum a (n + 1) = prefixSum a n + a n := by
  simp [prefixSum, Finset.sum_range_succ]

/-- Sum of the terms at indices `N+1, ..., N+q`. -/
def tailBlockSum (a : ℕ → ℕ) (N q : ℕ) : ℕ :=
  ∑ j ∈ Finset.range q, a (N + 1 + j)

@[simp] lemma tailBlockSum_zero (a : ℕ → ℕ) (N : ℕ) :
    tailBlockSum a N 0 = 0 := by
  simp [tailBlockSum]

lemma tailBlockSum_succ (a : ℕ → ℕ) (N q : ℕ) :
    tailBlockSum a N (q + 1) = tailBlockSum a N q + a (N + q + 1) := by
  simp only [tailBlockSum, Finset.sum_range_succ]
  congr 2
  omega

lemma prefixSum_add_tailBlockSum (a : ℕ → ℕ) (N q : ℕ) :
    prefixSum a (N + q + 1) = prefixSum a (N + 1) + tailBlockSum a N q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show N + (q + 1) + 1 = (N + q + 1) + 1 by omega,
        prefixSum_succ, ih, tailBlockSum_succ]
      rw [show N + q + 1 = N + 1 + q by omega]
      ac_rfl

lemma tailBlockSum_ge_length {a : ℕ → ℕ} (ha : ∀ n, 0 < a n) (N q : ℕ) :
    q ≤ tailBlockSum a N q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [tailBlockSum_succ]
      have := ha (N + q + 1)
      omega

/-! ## The permanent interval certificate -/

lemma interval_certificate_propagates
    (a b : ℕ → ℕ) {m N u L : ℕ}
    (hmN : m ≤ N)
    (ha_mono : Monotone a)
    (hrec : ∀ n, N ≤ n → a (n + 1) = prefixSum a n + b n)
    (hadm : ∀ n, N ≤ n → 4 * b n ≤ a n)
    (hinterval : ∀ t, u ≤ t → t ≤ u + L →
      t ∈ subsetSums a (Set.Icc m N))
    (hlock : 4 * prefixSum a (N + 1) ≤ 4 * (L + 1) + 3 * a N) :
    ∀ q t, u ≤ t → t ≤ u + L + tailBlockSum a N q →
      t ∈ subsetSums a (Set.Icc m (N + q)) := by
  intro q
  induction q with
  | zero =>
      intro t hut htu
      simpa using hinterval t hut htu
  | succ q ih =>
      intro t hut htu
      have hNn : N ≤ N + q := Nat.le_add_right N q
      have hmNq : m ≤ N + q := hmN.trans (Nat.le_add_right N q)
      have haN_le : a N ≤ a (N + q) := ha_mono hNn
      have hbn : 4 * b (N + q) ≤ a (N + q) := hadm (N + q) hNn
      have hbase : prefixSum a (N + 1) + b (N + q) ≤ L + 1 + a (N + q) := by
        omega
      have hpref :
          prefixSum a (N + 1) + tailBlockSum a N q = prefixSum a (N + q + 1) := by
        exact (prefixSum_add_tailBlockSum a N q).symm
      have hrecn := hrec (N + q) hNn
      have hoverlap : a (N + q + 1) ≤ L + tailBlockSum a N q + 1 := by
        have hpref' :
            prefixSum a (N + 1) + tailBlockSum a N q =
              prefixSum a (N + q) + a (N + q) := by
          calc
            _ = prefixSum a (N + q + 1) := hpref
            _ = _ := prefixSum_succ a (N + q)
        have hwith :
            a (N + q + 1) + prefixSum a (N + 1) ≤
              (L + tailBlockSum a N q + 1) + prefixSum a (N + 1) := by
          calc
            a (N + q + 1) + prefixSum a (N + 1) =
                (prefixSum a (N + q) + b (N + q)) + prefixSum a (N + 1) := by
                  rw [hrecn]
            _ = prefixSum a (N + q) +
                (prefixSum a (N + 1) + b (N + q)) := by ac_rfl
            _ ≤ prefixSum a (N + q) + (L + 1 + a (N + q)) :=
              Nat.add_le_add_left hbase _
            _ = (L + tailBlockSum a N q + 1) + prefixSum a (N + 1) := by
              omega
        exact Nat.le_of_add_le_add_right hwith
      rw [tailBlockSum_succ] at htu
      by_cases hold : t ≤ u + L + tailBlockSum a N q
      · exact subsetSums_mono (Set.Icc_subset_Icc_right (by omega)) (ih t hut hold)
      · have hnew_le_t : a (N + q + 1) ≤ t := by omega
        have hsub_lo : u ≤ t - a (N + q + 1) := by omega
        have hsub_hi : t - a (N + q + 1) ≤ u + L + tailBlockSum a N q := by
          omega
        have hrep := ih (t - a (N + q + 1)) hsub_lo hsub_hi
        have hadd := subsetSums_add_new
          (a := a) (I := Set.Icc m (N + q)) (J := Set.Icc m (N + (q + 1)))
          (i := N + q + 1) (t := t - a (N + q + 1))
          (Set.Icc_subset_Icc_right (by omega))
          (by constructor <;> omega)
          (by simp only [Set.mem_Icc, not_and_or]; omega) hrep
        convert hadd using 1
        omega

lemma permanent_interval_certificate
    (a b : ℕ → ℕ) {m N u L : ℕ}
    (hmN : m ≤ N)
    (ha_pos : ∀ n, 0 < a n)
    (ha_mono : Monotone a)
    (hrec : ∀ n, N ≤ n → a (n + 1) = prefixSum a n + b n)
    (hadm : ∀ n, N ≤ n → 4 * b n ≤ a n)
    (hinterval : ∀ t, u ≤ t → t ≤ u + L →
      t ∈ subsetSums a (Set.Icc m N))
    (hlock : 4 * prefixSum a (N + 1) ≤ 4 * (L + 1) + 3 * a N) :
    ∃ H, ∀ t, H ≤ t → t ∈ subsetSums a (Set.Ici m) := by
  refine ⟨u, fun t hut => ?_⟩
  let q := t - u
  have hq : q ≤ tailBlockSum a N q := tailBlockSum_ge_length ha_pos N q
  have htq : t = u + q := by simp [q, Nat.add_sub_of_le hut]
  have hrep := interval_certificate_propagates a b hmN ha_mono hrec hadm
    hinterval hlock q t hut (by omega)
  exact subsetSums_mono (fun i hi => hi.1) hrep

lemma generatedState_congr {b c : ℕ → ℕ} {r : ℕ}
    (hbc : ∀ n, 3 ≤ n → n < r + 3 → b n = c n) :
    generatedState b r = generatedState c r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [generatedState, generatedState]
      have hs : generatedState b r = generatedState c r :=
        ih (fun n hn hnlt => hbc n hn (by omega))
      rw [hs, hbc (r + 3) (by omega) (by omega)]

lemma generated_congr {b c : ℕ → ℕ} {N : ℕ}
    (hbc : ∀ n, 3 ≤ n → n < N → b n = c n) :
    ∀ n < N + 1, generated b n = generated c n := by
  intro n hn
  by_cases hn3 : n < 3
  · interval_cases n <;> rfl
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn3)
    simp only [add_comm 3 r, generated_add_three]
    apply congrArg Prod.fst
    apply generatedState_congr
    intro i hi hil
    apply hbc i hi
    omega

lemma generated_second_order (b : ℕ → ℕ) {n : ℕ} (hn : 3 ≤ n) :
    generated b (n + 2) + b n =
      generated b (n + 1) + generated b n + b (n + 1) := by
  rw [generated_recurrence b hn, generated_recurrence b (show 3 ≤ n + 1 by omega),
    Finset.sum_range_succ]
  omega

lemma generated_strictMono (b : ℕ → ℕ)
    (hb : ∀ n, 3 ≤ n → 4 * b n ≤ generated b n) : StrictMono (generated b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases hn : n < 4
  · interval_cases n
    · norm_num
    · norm_num
    · norm_num [generated, generatedState]
    · rw [generated_recurrence b (n := 3) (by omega)]
      norm_num [generated, generatedState]
      exact lt_of_lt_of_le (by omega : 5 < 6) (Nat.le_add_right 6 (b 3))
  · have hn4 : 4 ≤ n := Nat.le_of_not_gt hn
    have hrec := generated_second_order b (n := n - 1) (by omega)
    have hpos := generated_pos b (n - 1)
    have hadm := hb (n - 1) (by omega)
    rw [Nat.sub_add_cancel (show 1 ≤ n by omega),
      show n - 1 + 2 = n + 1 by omega] at hrec
    omega

/-- A provisional sequence, unperturbed from `cut` onward. -/
structure Approximation where
  b : ℕ → ℕ
  cut : ℕ
  cut_ge : 3 ≤ cut
  admissible : ∀ n, 3 ≤ n → 4 * b n ≤ generated b n
  eventualParity : ∀ n, cut ≤ n → b n = parityPerturbation n

namespace Approximation

/-- The integer sequence belonging to a provisional stage. -/
def seq (s : Approximation) : ℕ → ℕ := generated s.b

lemma seq_pos (s : Approximation) (n : ℕ) : 0 < s.seq n := generated_pos s.b n

lemma seq_strictMono (s : Approximation) : StrictMono s.seq :=
  generated_strictMono s.b s.admissible

/-- The completely unperturbed initial stage. -/
def initial : Approximation where
  b := parityPerturbation
  cut := 3
  cut_ge := by omega
  admissible := by
    intro n hn
    calc
      4 * parityPerturbation n ≤ 4 :=
        Nat.mul_le_mul_left 4 (parityPerturbation_le_one n)
      _ ≤ generated parityPerturbation n := generated_ge_four _ hn
  eventualParity := by
    intro n hn
    rfl

/-- Replace the parameter at `K` by `⌊a_K/4⌋`, then resume the alternating choice. -/
def modifiedB (s : Approximation) (K n : ℕ) : ℕ :=
  if n < K then s.b n
  else if n = K then s.seq K / 4
  else parityPerturbation n

lemma modifiedB_before (s : Approximation) {K n : ℕ} (hn : n < K) :
    modifiedB s K n = s.b n := by
  simp [modifiedB, hn]

lemma modifiedB_at (s : Approximation) (K : ℕ) : modifiedB s K K = s.seq K / 4 := by
  simp [modifiedB]

lemma modifiedB_after (s : Approximation) {K n : ℕ} (hn : K < n) :
    modifiedB s K n = parityPerturbation n := by
  simp [modifiedB, Nat.not_lt_of_ge hn.le, hn.ne']

lemma generated_modifiedB_eq (s : Approximation) {K n : ℕ} (hn : n ≤ K) :
    generated (modifiedB s K) n = s.seq n := by
  apply generated_congr (N := K) (fun i hi hil => modifiedB_before s hil)
  omega

/-- A single perturbation at an index beyond the current cutoff. -/
def extend (s : Approximation) (K : ℕ) (hK : s.cut ≤ K) : Approximation where
  b := modifiedB s K
  cut := K + 1
  cut_ge := s.cut_ge.trans (hK.trans (Nat.le_add_right K 1))
  admissible := by
    intro n hn
    rcases lt_trichotomy n K with hlt | heq | hgt
    · rw [modifiedB_before s hlt, generated_modifiedB_eq s hlt.le]
      exact s.admissible n hn
    · subst n
      rw [modifiedB_at, generated_modifiedB_eq s (le_refl K), seq]
      exact Nat.mul_div_le (generated s.b K) 4
    · rw [modifiedB_after s hgt]
      calc
        4 * parityPerturbation n ≤ 4 :=
          Nat.mul_le_mul_left 4 (parityPerturbation_le_one n)
        _ ≤ generated (modifiedB s K) n := generated_ge_four _ hn
  eventualParity := by
    intro n hn
    exact modifiedB_after s (by omega)

lemma extend_cut (s : Approximation) (K : ℕ) (hK : s.cut ≤ K) :
    (s.extend K hK).cut = K + 1 := rfl

lemma extend_seq_eq (s : Approximation) (K : ℕ) (hK : s.cut ≤ K) {n : ℕ}
    (hn : n ≤ K) : (s.extend K hK).seq n = s.seq n :=
  generated_modifiedB_eq s hn

end Approximation

/-! ## The Graham recurrence -/

lemma parityPerturbation_difference (n : ℕ) :
    (parityPerturbation (n + 1) : ℤ) - parityPerturbation n = -((-1 : ℤ) ^ n) := by
  by_cases hn : Even n
  · have hn' : ¬ Even (n + 1) := by
      intro hs
      exact (Nat.even_add_one.mp hs) hn
    rw [parityPerturbation_even hn, parityPerturbation_odd hn', hn.neg_one_pow]
    norm_num
  · have hnodd : Odd n := (Nat.not_even_iff_odd).mp hn
    have hn' : Even (n + 1) := hnodd.add_one
    rw [parityPerturbation_odd hn, parityPerturbation_even hn', hnodd.neg_one_pow]
    norm_num

lemma Approximation.graham_recurrence (s : Approximation) {n : ℕ} (hn : s.cut ≤ n) :
    (s.seq (n + 2) : ℤ) = s.seq (n + 1) + s.seq n - (-1 : ℤ) ^ n := by
  have hn3 : 3 ≤ n := s.cut_ge.trans hn
  have hnat := generated_second_order s.b hn3
  have hbn := s.eventualParity n hn
  have hbn1 := s.eventualParity (n + 1) (by omega)
  have hcast :
      (s.seq (n + 2) : ℤ) + s.b n =
        s.seq (n + 1) + s.seq n + s.b (n + 1) := by
    exact_mod_cast hnat
  rw [hbn, hbn1] at hcast
  have hdiff := parityPerturbation_difference n
  omega

lemma graham_block_sum
    (x : ℕ → ℕ) (K L q : ℕ)
    (hrec : ∀ n, K ≤ n →
      (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hKL : K ≤ L) :
    (∑ k ∈ Finset.range q, (x (L + k) : ℤ)) =
      (x (L + q + 1) : ℤ) - x (L + 1) +
        ∑ k ∈ Finset.range q, (-1 : ℤ) ^ (L + k) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hr := hrec (L + q) (by omega)
      rw [show L + (q + 1) + 1 = L + q + 2 by omega]
      ring_nf at hr ⊢
      omega

lemma alternating_odd_even_block (l q : ℕ) :
    ∑ k ∈ Finset.range (2 * q), (-1 : ℤ) ^ (2 * l + 1 + k) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show 2 * (q + 1) = (2 * q + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hodd : Odd (2 * l + 1 + 2 * q) := ⟨l + q, by omega⟩
      have heven : Even (2 * l + 1 + (2 * q + 1)) := ⟨l + q + 1, by omega⟩
      rw [hodd.neg_one_pow, heven.neg_one_pow]
      norm_num

lemma graham_even_block
    (x : ℕ → ℕ) (K r q : ℕ)
    (hrec : ∀ n, K ≤ n →
      (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hr : 1 ≤ r) (hKr : K ≤ 2 * r - 1) :
    (∑ k ∈ Finset.range q, (x (2 * (r + k)) : ℤ)) + q =
      (x (2 * (r + q) - 1) : ℤ) - x (2 * r - 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ]
      rw [show 2 * (r + q) - 1 = r * 2 + q * 2 - 1 by omega,
        show 2 * r - 1 = r * 2 - 1 by omega] at ih
      have harg (k : ℕ) : 2 * (r + k) = r * 2 + k * 2 := by omega
      simp_rw [harg] at ih
      have hidx : K ≤ 2 * (r + q) - 1 := by omega
      have hstep := hrec (2 * (r + q) - 1) hidx
      have hodd : Odd (2 * (r + q) - 1) := ⟨r + q - 1, by omega⟩
      rw [hodd.neg_one_pow] at hstep
      rw [show 2 * (r + q) = (2 * (r + q) - 1) + 1 by omega,
        show 2 * (r + (q + 1)) - 1 = (2 * (r + q) - 1) + 2 by omega]
      push_cast
      ring_nf at hstep ⊢
      linear_combination ih - hstep

lemma graham_odd_block
    (x : ℕ → ℕ) (K r q : ℕ)
    (hrec : ∀ n, K ≤ n →
      (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hr : 1 ≤ r) (hKr : K ≤ 2 * r - 2) :
    (∑ k ∈ Finset.range q, (x (2 * (r + k) - 1) : ℤ)) =
      (x (2 * (r + q) - 2) : ℤ) - x (2 * r - 2) + q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ]
      rw [show 2 * (r + q) - 2 = r * 2 + q * 2 - 2 by omega,
        show 2 * r - 2 = r * 2 - 2 by omega] at ih
      have harg (k : ℕ) : 2 * (r + k) - 1 = r * 2 + k * 2 - 1 := by omega
      simp_rw [harg] at ih
      have hidx : K ≤ 2 * (r + q) - 2 := by omega
      have hstep := hrec (2 * (r + q) - 2) hidx
      have heven : Even (2 * (r + q) - 2) := ⟨r + q - 1, by omega⟩
      rw [heven.neg_one_pow] at hstep
      rw [show 2 * (r + q) - 1 = (2 * (r + q) - 2) + 1 by omega,
        show 2 * (r + (q + 1)) - 2 = (2 * (r + q) - 2) + 2 by omega]
      push_cast
      ring_nf at hstep ⊢
      linear_combination ih - hstep

lemma graham_odd_term_sub_mem
    (x : ℕ → ℕ) (K m r t : ℕ)
    (hrec : ∀ n, K ≤ n →
      (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hr : 1 ≤ r) (hKr : K ≤ 2 * r - 1) (hmr : m ≤ 2 * r - 1) :
    x (2 * (r + t) - 1) - t ∈ subsetSums x (Set.Ici m) := by
  let e : ℕ ↪ ℕ :=
    ⟨fun k => 2 * (r + k), by
      intro i j hij
      dsimp at hij
      omega⟩
  let E : Finset ℕ := (Finset.range t).map e
  have hbase_not_mem : 2 * r - 1 ∉ E := by
    intro hmem
    obtain ⟨k, hk, heq⟩ := Finset.mem_map.mp hmem
    dsimp [e] at heq
    omega
  have hsumE :
      (∑ i ∈ E, x i) = ∑ k ∈ Finset.range t, x (2 * (r + k)) := by
    simp [E, e]
  have hblock := graham_even_block x K r t hrec hr hKr
  have hnat :
      (∑ k ∈ Finset.range t, x (2 * (r + k))) + t + x (2 * r - 1) =
        x (2 * (r + t) - 1) := by
    apply Int.ofNat_inj.mp
    push_cast
    omega
  refine ⟨insert (2 * r - 1) E, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact hmr
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
      change m ≤ 2 * (r + k)
      omega
  · rw [Finset.sum_insert hbase_not_mem, hsumE]
    have ht : t ≤ x (2 * (r + t) - 1) := by omega
    symm
    apply (tsub_eq_iff_eq_add_of_le ht).2
    omega

lemma graham_even_term_sub_mem
    (x : ℕ → ℕ) (K m l s t : ℕ)
    (hrec : ∀ n, K ≤ n →
      (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hKL : K ≤ 2 * l + 1) (hmL : m ≤ 2 * l + 1)
    (ht : t < x (2 * l + 2)) :
    let d := x (2 * l + 2) - 1 - t
    x (2 * (l + 2 + s + d)) - t ∈ subsetSums x (Set.Ici m) := by
  dsimp only
  let d := x (2 * l + 2) - 1 - t
  let h := l + 2 + s
  let lowEmb : ℕ ↪ ℕ :=
    ⟨fun k => 2 * l + 1 + k, by
      intro i j hij
      dsimp at hij
      omega⟩
  let highEmb : ℕ ↪ ℕ :=
    ⟨fun k => 2 * (h + k) - 1, by
      intro i j hij
      dsimp at hij
      omega⟩
  let A : Finset ℕ := (Finset.range (2 * s)).map lowEmb
  let B : Finset ℕ := (Finset.range (d + 1)).map highEmb
  have hd : d + 1 + t = x (2 * l + 2) := by
    dsimp [d]
    omega
  have hh : 1 ≤ h := by
    dsimp [h]
    omega
  have hKh : K ≤ 2 * h - 2 := by
    dsimp [h]
    omega
  have hlow := graham_block_sum x K (2 * l + 1) (2 * s) hrec hKL
  rw [alternating_odd_even_block l s] at hlow
  rw [show 2 * l + 1 + 2 * s + 1 = 2 * h - 2 by simp [h]; omega] at hlow
  have hhigh := graham_odd_block x K h (d + 1) hrec hh hKh
  rw [show 2 * (h + (d + 1)) - 2 = 2 * (h + d) by omega] at hhigh
  have hsumA :
      (∑ i ∈ A, x i) = ∑ k ∈ Finset.range (2 * s), x (2 * l + 1 + k) := by
    simp [A, lowEmb]
  have hsumB :
      (∑ i ∈ B, x i) = ∑ k ∈ Finset.range (d + 1), x (2 * (h + k) - 1) := by
    simp [B, highEmb]
  have htotal : (∑ i ∈ A, x i) + (∑ i ∈ B, x i) + t = x (2 * (h + d)) := by
    rw [hsumA, hsumB]
    apply Int.ofNat_inj.mp
    push_cast
    have hd' : ((d + 1 + t : ℕ) : ℤ) = x (2 * l + 2) := by exact_mod_cast hd
    rw [show 2 * l + 2 = 2 * l + 1 + 1 by omega] at hd'
    omega
  have hdisjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    obtain ⟨ka, hka, ha⟩ := Finset.mem_map.mp hiA
    obtain ⟨kb, hkb, hb⟩ := Finset.mem_map.mp hiB
    have hka' : ka < 2 * s := Finset.mem_range.mp hka
    have hkb' : kb < d + 1 := Finset.mem_range.mp hkb
    dsimp [lowEmb] at ha
    dsimp [highEmb] at hb
    dsimp [h] at hb
    omega
  refine ⟨A ∪ B, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_union] at hi
    rcases hi with hi | hi
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
      change m ≤ 2 * l + 1 + k
      omega
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
      change m ≤ 2 * (h + k) - 1
      dsimp [h]
      omega
  · rw [Finset.sum_union hdisjoint]
    have ht' : t ≤ x (2 * (h + d)) := by omega
    symm
    apply (tsub_eq_iff_eq_add_of_le ht').2
    omega

lemma graham_even_term_add_mem
    (x : ℕ → ℕ) (K m r t : ℕ)
    (hrec : ∀ n, K ≤ n →
      (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hKr : K ≤ 2 * r) (hmr : m ≤ 2 * r) :
    x (2 * (r + t)) + t ∈ subsetSums x (Set.Ici m) := by
  let e : ℕ ↪ ℕ :=
    ⟨fun k => 2 * (r + 1 + k) - 1, by
      intro i j hij
      dsimp at hij
      omega⟩
  let E : Finset ℕ := (Finset.range t).map e
  have hbase_not_mem : 2 * r ∉ E := by
    intro hmem
    obtain ⟨k, hk, heq⟩ := Finset.mem_map.mp hmem
    dsimp [e] at heq
    omega
  have hsumE :
      (∑ i ∈ E, x i) = ∑ k ∈ Finset.range t, x (2 * (r + 1 + k) - 1) := by
    simp [E, e]
  have hblock := graham_odd_block x K (r + 1) t hrec (by omega) (by omega)
  have hnat : x (2 * r) + (∑ k ∈ Finset.range t, x (2 * (r + 1 + k) - 1)) =
      x (2 * (r + t)) + t := by
    apply Int.ofNat_inj.mp
    push_cast
    rw [show 2 * (r + 1) - 2 = 2 * r by omega,
      show 2 * (r + 1 + t) - 2 = 2 * (r + t) by omega] at hblock
    omega
  refine ⟨insert (2 * r) E, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact hmr
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
      change m ≤ 2 * (r + 1 + k) - 1
      omega
  · rw [Finset.sum_insert hbase_not_mem, hsumE, hnat]

lemma graham_odd_term_add_mem
    (x : ℕ → ℕ) (K m L r t : ℕ)
    (hrec : ∀ n, K ≤ n →
      (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hmL : m ≤ L) (ht : t ≤ x L) (hLr : L < 2 * r - 1) (hKr : K ≤ 2 * r - 1) :
    let d := x L - t
    x (2 * (r + d) - 1) + t ∈ subsetSums x (Set.Ici m) := by
  dsimp only
  let d := x L - t
  let e : ℕ ↪ ℕ :=
    ⟨fun k => 2 * (r + k), by
      intro i j hij
      dsimp at hij
      omega⟩
  let E : Finset ℕ := (Finset.range d).map e
  have hbase_not_mem : 2 * r - 1 ∉ E := by
    intro hmem
    obtain ⟨k, hk, heq⟩ := Finset.mem_map.mp hmem
    dsimp [e] at heq
    omega
  have hL_not_mem : L ∉ insert (2 * r - 1) E := by
    simp only [Finset.mem_insert, not_or]
    constructor
    · omega
    · intro hmem
      obtain ⟨k, hk, heq⟩ := Finset.mem_map.mp hmem
      dsimp [e] at heq
      omega
  have hsumE :
      (∑ i ∈ E, x i) = ∑ k ∈ Finset.range d, x (2 * (r + k)) := by
    simp [E, e]
  have hblock := graham_even_block x K r d hrec (by omega) hKr
  have hd : d + t = x L := by dsimp [d]; omega
  have hnat : x L + x (2 * r - 1) +
      (∑ k ∈ Finset.range d, x (2 * (r + k))) = x (2 * (r + d) - 1) + t := by
    apply Int.ofNat_inj.mp
    push_cast
    have hd' : ((d + t : ℕ) : ℤ) = x L := by exact_mod_cast hd
    omega
  refine ⟨insert L (insert (2 * r - 1) E), ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_insert] at hi
    rcases hi with rfl | rfl | hi
    · exact hmL
    · exact hmL.trans hLr.le
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
      change m ≤ 2 * (r + k)
      omega
  · rw [Finset.sum_insert hL_not_mem, Finset.sum_insert hbase_not_mem, hsumE]
    simpa [d, Nat.add_assoc] using hnat

lemma strictMono_nat_lower {a : ℕ → ℕ} (ha : StrictMono a) (ha0 : 0 < a 0) (n : ℕ) :
    n + 1 ≤ a n := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hstep := ha (Nat.lt_succ_self n)
      change n + 1 + 1 ≤ a (n + 1)
      change a n < a (n + 1) at hstep
      omega

lemma Approximation.eventually_lower_neighborhood (s : Approximation) (m R : ℕ) :
    ∃ H, ∀ n, H ≤ n → ∀ t, t ≤ R →
      s.seq n - t ∈ subsetSums s.seq (Set.Ici m) := by
  let l := max s.cut m + R + 1
  let X := s.seq (2 * l + 2)
  let E := l + 2 + X
  have hKL : s.cut ≤ 2 * l + 1 := by
    dsimp [l]
    omega
  have hmL : m ≤ 2 * l + 1 := by
    dsimp [l]
    omega
  have hX : R < X := by
    have hlower := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) (2 * l + 2)
    dsimp [X]
    dsimp [l] at hlower ⊢
    omega
  refine ⟨2 * E + 1, ?_⟩
  intro n hn t htR
  rcases Nat.even_or_odd n with hneven | hnodd
  · obtain ⟨k, hk⟩ := hneven
    have hkE : E + 1 ≤ k := by
      dsimp [E] at hn ⊢
      omega
    let d := X - 1 - t
    have hdX : d < X := by
      dsimp [d]
      omega
    have hkd : l + 2 + d ≤ k := by
      dsimp [E] at hkE
      omega
    let q := k - (l + 2 + d)
    have heq : l + 2 + q + d = k := by
      dsimp [q]
      omega
    have hmem := graham_even_term_sub_mem s.seq s.cut m l q t
      (fun j hj => s.graham_recurrence hj) hKL hmL (by
        change t < X
        exact htR.trans_lt hX)
    dsimp only at hmem
    have hindex : 2 * (l + 2 + q + (X - 1 - t)) = n := by
      dsimp [d] at heq
      omega
    rwa [hindex] at hmem
  · obtain ⟨k, hk⟩ := hnodd
    have hkE : E ≤ k := by
      dsimp [E] at hn ⊢
      omega
    let r := k + 1 - t
    have hr : 1 ≤ r := by
      dsimp [r]
      dsimp [E, l] at hkE
      omega
    have hKr : s.cut ≤ 2 * r - 1 := by
      dsimp [r]
      dsimp [E, l] at hkE
      omega
    have hmr : m ≤ 2 * r - 1 := by
      dsimp [r]
      dsimp [E, l] at hkE
      omega
    have hmem := graham_odd_term_sub_mem s.seq s.cut m r t
      (fun j hj => s.graham_recurrence hj) hr hKr hmr
    have hindex : 2 * (r + t) - 1 = n := by
      dsimp [r]
      omega
    rwa [hindex] at hmem

lemma Approximation.eventually_upper_neighborhood (s : Approximation) (m R : ℕ) :
    ∃ H, ∀ n, H ≤ n → ∀ t, t ≤ R →
      s.seq n + t ∈ subsetSums s.seq (Set.Ici m) := by
  let L := max s.cut m + R + 1
  let X := s.seq L
  let E := L + X + R + 3
  have hmL : m ≤ L := by
    dsimp [L]
    omega
  have hX : R < X := by
    have hlower := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) L
    dsimp [X]
    dsimp [L] at hlower ⊢
    omega
  refine ⟨2 * E + 1, ?_⟩
  intro n hn t htR
  rcases Nat.even_or_odd n with hneven | hnodd
  · obtain ⟨k, hk⟩ := hneven
    have hkE : E + 1 ≤ k := by
      dsimp [E] at hn ⊢
      omega
    let r := k - t
    have hKr : s.cut ≤ 2 * r := by
      dsimp [r]
      dsimp [E, L] at hkE
      omega
    have hmr : m ≤ 2 * r := by
      dsimp [r]
      dsimp [E, L] at hkE
      omega
    have hmem := graham_even_term_add_mem s.seq s.cut m r t
      (fun j hj => s.graham_recurrence hj) hKr hmr
    have hindex : 2 * (r + t) = n := by
      dsimp [r]
      omega
    rwa [hindex] at hmem
  · obtain ⟨k, hk⟩ := hnodd
    have hkE : E ≤ k := by
      dsimp [E] at hn ⊢
      omega
    let d := X - t
    have hdX : d ≤ X := Nat.sub_le X t
    let r := k + 1 - d
    have hLr : L < 2 * r - 1 := by
      dsimp [r]
      dsimp [E] at hkE
      omega
    have hKr : s.cut ≤ 2 * r - 1 := by
      have hcutL : s.cut ≤ L := by
        dsimp [L]
        omega
      exact hcutL.trans hLr.le
    have hmem := graham_odd_term_add_mem s.seq s.cut m L r t
      (fun j hj => s.graham_recurrence hj) hmL (by
        change t ≤ X
        exact htR.trans hX.le) hLr hKr
    dsimp only at hmem
    have hindex : 2 * (r + (s.seq L - t)) - 1 = n := by
      change 2 * (r + (X - t)) - 1 = n
      dsimp [r, d]
      omega
    rwa [hindex] at hmem

lemma Approximation.eventually_full_neighborhood (s : Approximation) (m R : ℕ) :
    ∃ H, ∀ n, H ≤ n → ∀ z, s.seq n - R ≤ z → z ≤ s.seq n + R →
      z ∈ subsetSums s.seq (Set.Ici m) := by
  obtain ⟨Hlo, hlo⟩ := s.eventually_lower_neighborhood m R
  obtain ⟨Hhi, hhi⟩ := s.eventually_upper_neighborhood m R
  refine ⟨max Hlo Hhi, ?_⟩
  intro n hn z hzl hzu
  by_cases hz : z ≤ s.seq n
  · let t := s.seq n - z
    have ht : t ≤ R := by
      dsimp [t]
      omega
    have hmem := hlo n ((le_max_left _ _).trans hn) t ht
    have heq : s.seq n - t = z := by
      dsimp [t]
      omega
    rwa [heq] at hmem
  · let t := z - s.seq n
    have ht : t ≤ R := by
      dsimp [t]
      omega
    have hmem := hhi n ((le_max_right _ _).trans hn) t ht
    have heq : s.seq n + t = z := by
      dsimp [t]
      omega
    rwa [heq] at hmem

/-- Sum of the terms with indices in `[m,r]`; it is zero when the interval is empty. -/
def blockTotal (a : ℕ → ℕ) (m r : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico m (r + 1), a i

lemma prefixSum_add_blockTotal (a : ℕ → ℕ) {m r : ℕ} (hmr : m ≤ r + 1) :
    prefixSum a m + blockTotal a m r = prefixSum a (r + 1) := by
  simpa [prefixSum, blockTotal] using Finset.sum_range_add_sum_Ico a hmr

lemma blockTotal_succ (a : ℕ → ℕ) {m r : ℕ} (hmr : m ≤ r + 1) :
    blockTotal a m (r + 1) = blockTotal a m r + a (r + 1) := by
  simpa [blockTotal, Nat.add_assoc] using Finset.sum_Ico_succ_top hmr a

lemma blockTotal_ge_last (a : ℕ → ℕ) {m r : ℕ} (hmr : m ≤ r) :
    a r ≤ blockTotal a m r := by
  calc
    a r = ∑ i ∈ ({r} : Finset ℕ), a i := by simp
    _ ≤ ∑ i ∈ Finset.Ico m (r + 1), a i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_singleton] at hi
        subst i
        simp [hmr]
      · intro i hi hnot
        omega
    _ = blockTotal a m r := rfl

lemma Approximation.eventually_next_le_blockTotal (s : Approximation) (m : ℕ) :
    ∃ R, m ≤ R ∧ ∀ r, R ≤ r → s.seq (r + 1) ≤ blockTotal s.seq m r := by
  let R := max s.cut (max m (prefixSum s.seq m))
  refine ⟨R, by simp [R], ?_⟩
  intro r hRr
  have hcut : s.cut ≤ r := (le_max_left _ _).trans hRr
  have hm : m ≤ r := (le_max_of_le_right (le_max_left _ _)).trans hRr
  have hpref : prefixSum s.seq m + blockTotal s.seq m r = prefixSum s.seq (r + 1) :=
    prefixSum_add_blockTotal s.seq (by omega)
  have hrec := generated_recurrence s.b (s.cut_ge.trans hcut)
  have hb := s.eventualParity r hcut
  have hble : s.b r ≤ 1 := by rw [hb]; exact parityPerturbation_le_one r
  have har := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) r
  have hpm : prefixSum s.seq m ≤ r := by
    exact (le_max_of_le_right (le_max_right _ _)).trans hRr
  rw [prefixSum_succ] at hpref
  change s.seq (r + 1) = prefixSum s.seq r + s.b r at hrec
  omega

lemma finite_gap_extend
    (a : ℕ → ℕ) {m r T w : ℕ}
    (hmr : m ≤ r + 1)
    (hT : T = blockTotal a m r)
    (hnext : a (r + 1) ≤ T)
    (hcover : ∀ n, n ≤ T → ∃ z, z ∈ subsetSums a (Set.Ico m (r + 1)) ∧
      n ≤ z ∧ z ≤ n + w) :
    ∀ n, n ≤ blockTotal a m (r + 1) →
      ∃ z, z ∈ subsetSums a (Set.Ico m (r + 2)) ∧ n ≤ z ∧ z ≤ n + w := by
  intro n hn
  rw [blockTotal_succ a hmr, ← hT] at hn
  by_cases hnT : n ≤ T
  · obtain ⟨z, hz, hnz, hzw⟩ := hcover n hnT
    exact ⟨z, subsetSums_mono (Set.Ico_subset_Ico_right (by omega)) hz, hnz, hzw⟩
  · have hxn : a (r + 1) ≤ n := hnext.trans (Nat.le_of_lt (Nat.lt_of_not_ge hnT))
    have hsub : n - a (r + 1) ≤ T := by omega
    obtain ⟨z, hz, hnz, hzw⟩ := hcover (n - a (r + 1)) hsub
    refine ⟨z + a (r + 1), ?_, by omega, by omega⟩
    exact subsetSums_add_new
      (a := a) (I := Set.Ico m (r + 1)) (J := Set.Ico m (r + 2))
      (i := r + 1) (t := z)
      (Set.Ico_subset_Ico_right (by omega)) (by constructor <;> omega)
      (by simp) hz

lemma Approximation.finite_blocks_have_bounded_gap (s : Approximation) (m : ℕ) :
    ∃ R w, m ≤ R ∧ ∀ q n, n ≤ blockTotal s.seq m (R + q) →
      ∃ z, z ∈ subsetSums s.seq (Set.Ico m (R + q + 1)) ∧
        n ≤ z ∧ z ≤ n + w := by
  obtain ⟨R, hmR, hnext⟩ := s.eventually_next_le_blockTotal m
  let w := blockTotal s.seq m R
  refine ⟨R, w, hmR, ?_⟩
  intro q
  induction q with
  | zero =>
      intro n hn
      refine ⟨w, ?_, by omega, by omega⟩
      exact ⟨Finset.Ico m (R + 1), by simp, by simp [w, blockTotal]⟩
  | succ q ih =>
      intro n hn
      have hR : R ≤ R + q := Nat.le_add_right R q
      have hext := finite_gap_extend s.seq
        (m := m) (r := R + q) (T := blockTotal s.seq m (R + q)) (w := w)
        (by omega) rfl (hnext (R + q) hR) (ih)
      simpa [Nat.add_assoc] using hext n hn

lemma Approximation.bounded_gap (s : Approximation) (m : ℕ) :
    ∃ w, ∀ n, ∃ z, z ∈ subsetSums s.seq (Set.Ici m) ∧ n ≤ z ∧ z ≤ n + w := by
  obtain ⟨R, w, hmR, hblocks⟩ := s.finite_blocks_have_bounded_gap m
  refine ⟨w, ?_⟩
  intro n
  have hlast : s.seq (R + n) ≤ blockTotal s.seq m (R + n) :=
    blockTotal_ge_last s.seq (hmR.trans (Nat.le_add_right R n))
  have hlower := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) (R + n)
  have hnTotal : n ≤ blockTotal s.seq m (R + n) := by omega
  obtain ⟨z, hz, hnz, hzw⟩ := hblocks n n hnTotal
  exact ⟨z, subsetSums_mono (fun i hi => hi.1) hz, hnz, hzw⟩

lemma subsetSums_add_disjoint {a : ℕ → ℕ} {I J U : Set ℕ} {x y : ℕ}
    (hI : I ⊆ U) (hJ : J ⊆ U) (hdisj : ∀ i, i ∈ I → i ∈ J → False)
    (hx : x ∈ subsetSums a I) (hy : y ∈ subsetSums a J) :
    x + y ∈ subsetSums a U := by
  obtain ⟨F, hF, hsumF⟩ := hx
  obtain ⟨G, hG, hsumG⟩ := hy
  have hFG : Disjoint F G := by
    apply Finset.disjoint_left.mpr
    intro i hiF hiG
    exact hdisj i (hF hiF) (hG hiG)
  refine ⟨F ∪ G, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact hI (hF hi)
    · exact hJ (hG hi)
  · rw [Finset.sum_union hFG, hsumF, hsumG]

lemma term_le_finset_sum (a : ℕ → ℕ) {F : Finset ℕ} {i : ℕ} (hi : i ∈ F) :
    a i ≤ ∑ j ∈ F, a j := by
  calc
    a i = ∑ j ∈ ({i} : Finset ℕ), a j := by simp
    _ ≤ ∑ j ∈ F, a j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa using hi
      · intro j hj hnot
        omega

lemma subsetSums_restrict_below
    {a : ℕ → ℕ} (ha : Monotone a) {m k z : ℕ}
    (hz : z ∈ subsetSums a (Set.Ici m)) (hzk : z < a k) :
    z ∈ subsetSums a (Set.Ico m k) := by
  obtain ⟨F, hF, hsum⟩ := hz
  refine ⟨F, ?_, hsum⟩
  intro i hi
  have hmi : m ≤ i := hF hi
  refine ⟨hmi, ?_⟩
  by_contra hnot
  have hki : k ≤ i := Nat.le_of_not_gt hnot
  have hxki : a k ≤ a i := ha hki
  have hile : a i ≤ z := by rw [← hsum]; exact term_le_finset_sum a hi
  omega

lemma block_gap_complement
    (a : ℕ → ℕ) {m r H A B w : ℕ}
    (hQ : ∀ n, H ≤ n → n ≤ A →
      ∃ z, z ∈ subsetSums a (Set.Ico m (r + 1)) ∧ n ≤ z ∧ z ≤ n + w)
    (hB : B = blockTotal a m r) (hHB : H + w ≤ B) (hAB : A + w ≤ B) :
    ∀ n, B - A - w ≤ n → n ≤ B - H - w →
      ∃ z, z ∈ subsetSums a (Set.Ico m (r + 1)) ∧ n ≤ z ∧ z ≤ n + w := by
  intro n hnlo hnhi
  have hnBH : n + w + H ≤ B := by omega
  let p := B - (n + w)
  have hpH : H ≤ p := by dsimp [p]; omega
  have hpA : p ≤ A := by dsimp [p]; omega
  obtain ⟨z, hz, hpz, hzp⟩ := hQ p hpH hpA
  have htotal : (∑ i ∈ Finset.Ico m (r + 1), a i) = B := by
    simpa [blockTotal] using hB.symm
  have hz' : z ∈ subsetSums a (↑(Finset.Ico m (r + 1)) : Set ℕ) := by simpa using hz
  have hzcomp := subsetSums_complement hz'
  rw [htotal] at hzcomp
  have hzcomp' : B - z ∈ subsetSums a (Set.Ico m (r + 1)) := by simpa using hzcomp
  refine ⟨B - z, hzcomp', ?_, ?_⟩ <;> (dsimp [p] at hpz hzp; omega)

lemma translated_gap_decreases
    (a : ℕ → ℕ) {m r H B u w : ℕ}
    (hw : 1 ≤ w) (hmr : m ≤ r + 1)
    (hQ : ∀ n, H ≤ n → n ≤ B →
      ∃ z, z ∈ subsetSums a (Set.Ico m (r + 1)) ∧ n ≤ z ∧ z ≤ n + w)
    (hu : u ∈ subsetSums a (Set.Ici (r + 1)))
    (hu1 : u + 1 ∈ subsetSums a (Set.Ici (r + 1))) :
    ∀ n, H + u + 1 ≤ n → n ≤ B + u →
      ∃ z, z ∈ subsetSums a (Set.Ici m) ∧ n ≤ z ∧ z ≤ n + (w - 1) := by
  intro n hnlo hnhi
  let p := n - u - 1
  have hpH : H ≤ p := by dsimp [p]; omega
  have hpB : p ≤ B := by dsimp [p]; omega
  obtain ⟨z, hz, hpz, hzw⟩ := hQ p hpH hpB
  have hdisj : ∀ i, i ∈ Set.Ico m (r + 1) → i ∈ Set.Ici (r + 1) → False := by
    intro i hi hj
    exact (not_lt_of_ge hj) hi.2
  by_cases hzp : z = p
  · refine ⟨z + (u + 1), subsetSums_add_disjoint
        (I := Set.Ico m (r + 1)) (J := Set.Ici (r + 1)) (U := Set.Ici m)
        (fun i hi => hi.1) (fun i hi => hmr.trans hi) hdisj hz hu1, ?_, ?_⟩
    · dsimp [p] at hzp
      omega
    · dsimp [p] at hzp
      omega
  · have hpz' : p + 1 ≤ z := by omega
    refine ⟨z + u, subsetSums_add_disjoint
        (I := Set.Ico m (r + 1)) (J := Set.Ici (r + 1)) (U := Set.Ici m)
        (fun i hi => hi.1) (fun i hi => hmr.trans hi) hdisj hz hu, ?_, ?_⟩
    · omega
    · omega

lemma Approximation.graham_upper_step (s : Approximation) {n : ℕ} (hn : s.cut ≤ n) :
    s.seq (n + 2) ≤ s.seq (n + 1) + s.seq n + 1 := by
  have hrec := s.graham_recurrence hn
  rcases neg_one_pow_eq_or ℤ n with hp | hp <;> rw [hp] at hrec <;> omega

lemma Approximation.graham_lower_step (s : Approximation) {n : ℕ} (hn : s.cut ≤ n) :
    s.seq (n + 1) + s.seq n ≤ s.seq (n + 2) + 1 := by
  have hrec := s.graham_recurrence hn
  rcases neg_one_pow_eq_or ℤ n with hp | hp <;> rw [hp] at hrec <;> omega

lemma Approximation.consecutive_translations (s : Approximation) {r : ℕ}
    (hcut : s.cut ≤ r + 1) :
    ∃ u, u ∈ subsetSums s.seq (Set.Ici (r + 1)) ∧
      u + 1 ∈ subsetSums s.seq (Set.Ici (r + 1)) ∧
      u ≤ s.seq (r + 3) ∧ s.seq (r + 3) ≤ u + 1 := by
  have hone : s.seq (r + 3) ∈ subsetSums s.seq (Set.Ici (r + 1)) :=
    ⟨{r + 3}, by
      intro i hi
      simp only [Finset.mem_coe, Finset.mem_singleton] at hi
      subst i
      change r + 1 ≤ r + 3
      omega, by simp⟩
  have hpair : s.seq (r + 1) + s.seq (r + 2) ∈
      subsetSums s.seq (Set.Ici (r + 1)) := by
    refine ⟨{r + 1, r + 2}, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · change r + 1 ≤ r + 1
        omega
      · change r + 1 ≤ r + 2
        omega
    · rw [Finset.sum_pair (by omega)]
  have hrec := s.graham_recurrence hcut
  rw [show r + 1 + 2 = r + 3 by omega, show r + 1 + 1 = r + 2 by omega] at hrec
  rcases Nat.even_or_odd (r + 1) with heven | hodd
  · rw [heven.neg_one_pow] at hrec
    have heq : s.seq (r + 3) + 1 = s.seq (r + 1) + s.seq (r + 2) := by
      omega
    refine ⟨s.seq (r + 3), hone, ?_, by omega, by omega⟩
    rwa [heq]
  · rw [hodd.neg_one_pow] at hrec
    have heq : s.seq (r + 1) + s.seq (r + 2) + 1 = s.seq (r + 3) := by
      omega
    refine ⟨s.seq (r + 1) + s.seq (r + 2), hpair, ?_, by omega, by omega⟩
    rwa [heq]

lemma Approximation.eventually_blockTotal_add_le_two_next (s : Approximation) (m C : ℕ) :
    ∃ R, m ≤ R ∧ ∀ r, R ≤ r → blockTotal s.seq m r + C ≤ 2 * s.seq (r + 1) := by
  let R := max (s.cut + 1) (max m (C + 2))
  refine ⟨R, by simp [R], ?_⟩
  intro r hR
  have hcutPrev : s.cut ≤ r - 1 := by
    dsimp [R] at hR
    omega
  have hcut : s.cut ≤ r := hcutPrev.trans (Nat.sub_le r 1)
  have hcutNext : s.cut ≤ r + 1 := by omega
  have hm : m ≤ r := by
    dsimp [R] at hR
    omega
  have hC : C + 2 ≤ r := by
    dsimp [R] at hR
    omega
  have hprev := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) (r - 1)
  have hlower := s.graham_lower_step hcutPrev
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r), show r - 1 + 2 = r + 1 by omega] at hlower
  have hdiff : s.seq r + C + 1 ≤ s.seq (r + 1) := by omega
  have hupper := s.graham_upper_step hcut
  have hseq : s.seq (r + 2) + C ≤ 2 * s.seq (r + 1) := by omega
  have hpref := prefixSum_add_blockTotal s.seq (m := m) (r := r) (by omega)
  have hgen := generated_recurrence s.b (n := r + 1) (s.cut_ge.trans hcutNext)
  change s.seq (r + 2) = prefixSum s.seq (r + 1) + s.b (r + 1) at hgen
  omega

lemma Approximation.gap_descent (s : Approximation) (m H w : ℕ) (hw : 1 ≤ w)
    (hgap : ∀ n, H ≤ n → ∃ z, z ∈ subsetSums s.seq (Set.Ici m) ∧
      n ≤ z ∧ z ≤ n + w) :
    ∃ H', ∀ n, H' ≤ n → ∃ z, z ∈ subsetSums s.seq (Set.Ici m) ∧
      n ≤ z ∧ z ≤ n + (w - 1) := by
  let C := prefixSum s.seq m + H + w + 6
  obtain ⟨Hnear, hnear⟩ := s.eventually_full_neighborhood m C
  obtain ⟨Rmargin, hmMargin, hmargin⟩ :=
    s.eventually_blockTotal_add_le_two_next m (w + 1)
  obtain ⟨Rnext, hmNext, hnext⟩ := s.eventually_next_le_blockTotal m
  let R := max Rmargin (max Rnext (max Hnear (H + w + m + s.cut + C + 3)))
  have hmR : m ≤ R := by
    dsimp [R]
    omega
  have hlocal : ∀ r, R ≤ r → ∀ n,
      s.seq (r + 3) - C ≤ n → n ≤ s.seq (r + 4) - C →
      ∃ z, z ∈ subsetSums s.seq (Set.Ici m) ∧
        n ≤ z ∧ z ≤ n + (w - 1) := by
    intro r hRr n hnlo hnhi
    have hrMargin : Rmargin ≤ r := (le_max_left _ _).trans hRr
    have hrNext : Rnext ≤ r :=
      (le_max_of_le_right (le_max_left _ _)).trans hRr
    have hrNear : Hnear ≤ r + 3 := by
      dsimp [R] at hRr
      omega
    have hm : m ≤ r := hmR.trans hRr
    have hcut : s.cut ≤ r + 1 := by
      dsimp [R] at hRr
      omega
    let T := blockTotal s.seq m r
    let A := s.seq (r + 1) - w - 1
    let B := T - H - w
    have hlast : s.seq r ≤ T := by
      dsimp [T]
      exact blockTotal_ge_last s.seq hm
    have hrlower := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) r
    have hHT : H + w ≤ T := by
      dsimp [R] at hRr
      omega
    have hxw : w + 1 ≤ s.seq (r + 1) := by
      have := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) (r + 1)
      dsimp [R] at hRr
      omega
    have hAT : A + w ≤ T := by
      have hnxt := hnext r hrNext
      dsimp [A, T]
      omega
    have hQlow : ∀ p, H ≤ p → p ≤ A →
        ∃ z, z ∈ subsetSums s.seq (Set.Ico m (r + 1)) ∧ p ≤ z ∧ z ≤ p + w := by
      intro p hpH hpA
      obtain ⟨z, hz, hpz, hzw⟩ := hgap p hpH
      have hzlt : z < s.seq (r + 1) := by
        dsimp [A] at hpA
        omega
      exact ⟨z, subsetSums_restrict_below s.seq_strictMono.monotone hz hzlt, hpz, hzw⟩
    have hQhigh := block_gap_complement s.seq hQlow (B := T) rfl hHT hAT
    have hcentral : ∀ p, H ≤ p → p ≤ B →
        ∃ z, z ∈ subsetSums s.seq (Set.Ico m (r + 1)) ∧ p ≤ z ∧ z ≤ p + w := by
      intro p hpH hpB
      by_cases hpA : p ≤ A
      · exact hQlow p hpH hpA
      · have hmargin' := hmargin r hrMargin
        have hover : T - A - w ≤ A + 1 := by
          dsimp [T, A] at hmargin' ⊢
          omega
        exact hQhigh p (by omega) (by simpa [B] using hpB)
    obtain ⟨u, hu, hu1, hule, hule1⟩ := s.consecutive_translations hcut
    have htranslated := translated_gap_decreases s.seq hw (hmR.trans (hRr.trans (by omega)))
      hcentral hu hu1
    have hJupper : s.seq (r + 4) ≤ B + u + C := by
      have hpref := prefixSum_add_blockTotal s.seq (m := m) (r := r) (by omega)
      have hb := s.eventualParity (r + 1) hcut
      have hble : s.b (r + 1) ≤ 1 := by rw [hb]; exact parityPerturbation_le_one _
      have hgen := generated_recurrence s.b (n := r + 1) (s.cut_ge.trans hcut)
      change s.seq (r + 2) = prefixSum s.seq (r + 1) + s.b (r + 1) at hgen
      have hupper := s.graham_upper_step (show s.cut ≤ r + 2 by omega)
      rw [show r + 2 + 2 = r + 4 by omega, show r + 2 + 1 = r + 3 by omega] at hupper
      dsimp [B, T, C]
      omega
    by_cases hncenter : n ≤ s.seq (r + 3) + C
    · refine ⟨n, hnear (r + 3) hrNear n ?_ hncenter, le_rfl, ?_⟩
      · exact hnlo
      · omega
    · apply htranslated n
      · omega
      · dsimp [B] at hJupper ⊢
        omega
  let H' := s.seq (R + 3) - C
  refine ⟨H', ?_⟩
  have hchain : ∀ q n, H' ≤ n → n ≤ s.seq (R + q + 4) - C →
      ∃ z, z ∈ subsetSums s.seq (Set.Ici m) ∧ n ≤ z ∧ z ≤ n + (w - 1) := by
    intro q
    induction q with
    | zero =>
        intro n hnlo hnhi
        apply hlocal R (le_refl R) n
        · exact hnlo
        · simpa using hnhi
    | succ q ih =>
        intro n hnlo hnhi
        by_cases hprev : n ≤ s.seq (R + q + 4) - C
        · exact ih n hnlo hprev
        · apply hlocal (R + q + 1) (by omega) n
          · simpa [Nat.add_assoc] using Nat.le_of_lt (Nat.lt_of_not_ge hprev)
          · simpa [Nat.add_assoc] using hnhi
  intro n hn
  let q := n + C
  have hlower := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) (R + q + 4)
  apply hchain q n hn
  dsimp [q] at hlower ⊢
  apply Nat.le_sub_of_add_le
  omega

lemma Approximation.gap_bound_to_completeness (s : Approximation) (m : ℕ) :
    ∀ w H, (∀ n, H ≤ n → ∃ z, z ∈ subsetSums s.seq (Set.Ici m) ∧
      n ≤ z ∧ z ≤ n + w) →
      ∃ H', ∀ n, H' ≤ n → n ∈ subsetSums s.seq (Set.Ici m)
  | 0, H, hgap => by
      refine ⟨H, ?_⟩
      intro n hn
      obtain ⟨z, hz, hnz, hzn⟩ := hgap n hn
      have : z = n := by omega
      rwa [this] at hz
  | w + 1, H, hgap => by
      obtain ⟨H', hgap'⟩ := s.gap_descent m H (w + 1) (by omega) hgap
      apply s.gap_bound_to_completeness m w H'
      simpa using hgap'

lemma Approximation.every_tail_complete (s : Approximation) (m : ℕ) :
    ∃ H, ∀ n, H ≤ n → n ∈ subsetSums s.seq (Set.Ici m) := by
  obtain ⟨w, hgap⟩ := s.bounded_gap m
  exact s.gap_bound_to_completeness m w 0 (by simpa using hgap)

/-! ## Fibonacci asymptotics of an unperturbed continuation -/

/-- Adding the alternating sign turns the inhomogeneous recurrence into Fibonacci's recurrence. -/
def Approximation.adjusted (s : Approximation) (n : ℕ) : ℤ :=
  s.seq n + (-1 : ℤ) ^ n

lemma Approximation.adjusted_recurrence (s : Approximation) {n : ℕ} (hn : s.cut ≤ n) :
    s.adjusted (n + 2) = s.adjusted (n + 1) + s.adjusted n := by
  have hrec := s.graham_recurrence hn
  have hp1 : (-1 : ℤ) ^ (n + 1) = -((-1 : ℤ) ^ n) := by
    rw [pow_succ]
    ring
  have hp2 : (-1 : ℤ) ^ (n + 2) = (-1 : ℤ) ^ n := by
    rw [show n + 2 = n + 1 + 1 by omega, pow_succ, hp1]
    ring
  simp only [adjusted, hp1, hp2]
  omega

lemma Approximation.adjusted_fibonacci (s : Approximation) (q : ℕ) :
    s.adjusted (s.cut + q + 1) =
      (Nat.fib q : ℤ) * s.adjusted s.cut +
        Nat.fib (q + 1) * s.adjusted (s.cut + 1) := by
  let P := fun q => s.adjusted (s.cut + q + 1) =
    (Nat.fib q : ℤ) * s.adjusted s.cut +
      Nat.fib (q + 1) * s.adjusted (s.cut + 1)
  have hpair : ∀ q, P q ∧ P (q + 1) := by
    intro q
    induction q with
    | zero =>
        constructor
        · simp [P]
        · have hrec := s.adjusted_recurrence (le_refl s.cut)
          norm_num [P, Nat.fib] at hrec ⊢
          rw [show s.cut + 1 + 1 = s.cut + 2 from by omega]
          omega
    | succ q ih =>
        refine ⟨ih.2, ?_⟩
        have hrec := s.adjusted_recurrence (show s.cut ≤ s.cut + q + 1 by omega)
        rw [show s.cut + q + 1 + 2 = s.cut + (q + 2) + 1 by omega,
          show s.cut + q + 1 + 1 = s.cut + (q + 1) + 1 by omega] at hrec
        change P (q + 2)
        dsimp [P]
        rw [hrec, ih.1, ih.2]
        have hf2 : Nat.fib (q + 2) = Nat.fib q + Nat.fib (q + 1) :=
          Nat.fib_add_two
        have hf3 : Nat.fib (q + 2 + 1) = Nat.fib (q + 1) + Nat.fib (q + 2) := by
          simpa [Nat.add_assoc] using (Nat.fib_add_two (n := q + 1))
        rw [hf2, hf3, hf2]
        push_cast
        ring
  exact (hpair q).1

lemma tendsto_fib_succ_atTop :
    Tendsto (fun q : ℕ => Nat.fib (q + 1)) atTop atTop := by
  refine tendsto_atTop_mono' atTop (f₁ := fun q : ℕ => q)
    (f₂ := fun q : ℕ => Nat.fib (q + 1)) ?_ tendsto_id
  exact Eventually.of_forall fun q => by
    change q ≤ Nat.fib (q + 1)
    have h := Nat.le_fib_add_one (q + 1)
    omega

lemma tendsto_alternating_div_fib (c : ℕ) :
    Tendsto (fun q : ℕ => ((-1 : ℝ) ^ (c + q) / Nat.fib (q + 1)))
      atTop (nhds 0) := by
  have hfibReal : Tendsto (fun q : ℕ => (Nat.fib (q + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_fib_succ_atTop
  have hinv : Tendsto (fun q : ℕ => ((Nat.fib (q + 1) : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hfibReal
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply hinv.congr'
  filter_upwards with q
  rw [Real.norm_eq_abs, abs_div, abs_neg_one_pow, abs_of_nonneg (Nat.cast_nonneg _)]
  simp

lemma Approximation.seq_tendsto_atTop (s : Approximation) :
    Tendsto (fun n : ℕ => (s.seq n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (Eventually.of_forall fun (n : ℕ) => show (n : ℝ) ≤ (s.seq n : ℝ) by
      exact_mod_cast (strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) n |>.trans' (by omega)))
  exact tendsto_natCast_atTop_atTop

lemma Approximation.adjusted_pos (s : Approximation) (n : ℕ) : 0 < (s.adjusted n : ℝ) := by
  have hseq := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) n
  rcases neg_one_pow_eq_or ℤ n with hp | hp
  · rw [adjusted, hp]
    push_cast
    positivity
  · rw [adjusted, hp]
    push_cast
    have hn : 1 ≤ s.seq n := s.seq_pos n
    norm_num
    have hnpos : 0 < n := by
      by_contra h
      have : n = 0 := Nat.eq_zero_of_not_pos h
      subst n
      norm_num at hp
    have hmono := s.seq_strictMono hnpos
    have hmono' : 1 < s.seq n := by
      simpa [Approximation.seq] using hmono
    exact_mod_cast hmono'

lemma Approximation.ratio_tendsto (s : Approximation) :
    Tendsto (fun n : ℕ => (s.seq (n + 1) : ℝ) / s.seq n) atTop (nhds φ) := by
  let A : ℝ := s.adjusted s.cut
  let D : ℝ := s.adjusted (s.cut + 1)
  have hA : 0 < A := by dsimp [A]; exact s.adjusted_pos s.cut
  have hD : 0 < D := by dsimp [D]; exact s.adjusted_pos (s.cut + 1)
  have hforward :
      Tendsto (fun q : ℕ => (Nat.fib (q + 2) : ℝ) / Nat.fib (q + 1))
        atTop (nhds φ) := by
    have h := tendsto_fib_succ_div_fib_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.add_assoc] using h
  have hbackward :
      Tendsto (fun q : ℕ => (Nat.fib q : ℝ) / Nat.fib (q + 1))
        atTop (nhds (-ψ)) := tendsto_fib_div_fib_succ_atTop
  have halt1 :
      Tendsto (fun q : ℕ => (-1 : ℝ) ^ (s.cut + q + 1) / Nat.fib (q + 1))
        atTop (nhds 0) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      tendsto_alternating_div_fib (s.cut + 1)
  have halt2 :
      Tendsto (fun q : ℕ => (-1 : ℝ) ^ (s.cut + q + 2) / Nat.fib (q + 1))
        atTop (nhds 0) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      tendsto_alternating_div_fib (s.cut + 2)
  have hnum : Tendsto (fun q : ℕ =>
      A + ((Nat.fib (q + 2) : ℝ) / Nat.fib (q + 1)) * D -
        (-1 : ℝ) ^ (s.cut + q + 2) / Nat.fib (q + 1))
      atTop (nhds (A + φ * D)) := by
    simpa using (tendsto_const_nhds.add (hforward.mul_const D)).sub halt2
  have hden : Tendsto (fun q : ℕ =>
      ((Nat.fib q : ℝ) / Nat.fib (q + 1)) * A + D -
        (-1 : ℝ) ^ (s.cut + q + 1) / Nat.fib (q + 1))
      atTop (nhds ((-ψ) * A + D)) := by
    simpa using ((hbackward.mul_const A).add tendsto_const_nhds).sub halt1
  have hden_pos : 0 < (-ψ) * A + D := by
    have hpsi : 0 < -ψ := neg_pos.mpr Real.goldenConj_neg
    positivity
  have hquot : Tendsto (fun q : ℕ =>
      (A + ((Nat.fib (q + 2) : ℝ) / Nat.fib (q + 1)) * D -
          (-1 : ℝ) ^ (s.cut + q + 2) / Nat.fib (q + 1)) /
        (((Nat.fib q : ℝ) / Nat.fib (q + 1)) * A + D -
          (-1 : ℝ) ^ (s.cut + q + 1) / Nat.fib (q + 1)))
      atTop (nhds ((A + φ * D) / ((-ψ) * A + D))) :=
    hnum.div hden hden_pos.ne'
  have hvalue : (A + φ * D) / ((-ψ) * A + D) = φ := by
    rw [← Real.inv_goldenRatio]
    field_simp [Real.goldenRatio_ne_zero]
  rw [hvalue] at hquot
  have hshift : Tendsto (fun q : ℕ =>
      (s.seq (s.cut + q + 2) : ℝ) / s.seq (s.cut + q + 1)) atTop (nhds φ) := by
    apply hquot.congr'
    filter_upwards with q
    have hfib : 0 < (Nat.fib (q + 1) : ℝ) := by
      exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < q + 1))
    have hq := s.adjusted_fibonacci q
    have hq1 := s.adjusted_fibonacci (q + 1)
    have hqR := congrArg (fun z : ℤ => (z : ℝ)) hq
    have hq1R := congrArg (fun z : ℤ => (z : ℝ)) hq1
    simp only [Approximation.adjusted] at hqR hq1R
    push_cast at hqR hq1R
    have hseq0 : (s.seq (s.cut + q + 1) : ℝ) =
        (Nat.fib q : ℝ) * A + Nat.fib (q + 1) * D -
          (-1 : ℝ) ^ (s.cut + q + 1) := by
      dsimp [A, D, Approximation.adjusted]
      push_cast
      linarith [hqR]
    have hseq1 : (s.seq (s.cut + q + 2) : ℝ) =
        (Nat.fib (q + 1) : ℝ) * A + Nat.fib (q + 2) * D -
          (-1 : ℝ) ^ (s.cut + q + 2) := by
      rw [show s.cut + (q + 1) + 1 = s.cut + q + 2 by omega,
        show q + 1 + 1 = q + 2 by omega] at hq1R
      dsimp [A, D, Approximation.adjusted]
      push_cast
      linarith [hq1R]
    have hnumEq :
        A + ((Nat.fib (q + 2) : ℝ) / Nat.fib (q + 1)) * D -
            (-1 : ℝ) ^ (s.cut + q + 2) / Nat.fib (q + 1) =
          (s.seq (s.cut + q + 2) : ℝ) / Nat.fib (q + 1) := by
      rw [hseq1]
      field_simp [hfib.ne']
    have hdenEq :
        ((Nat.fib q : ℝ) / Nat.fib (q + 1)) * A + D -
            (-1 : ℝ) ^ (s.cut + q + 1) / Nat.fib (q + 1) =
          (s.seq (s.cut + q + 1) : ℝ) / Nat.fib (q + 1) := by
      rw [hseq0]
      field_simp [hfib.ne']
    rw [hnumEq, hdenEq]
    field_simp [hfib.ne', Nat.cast_ne_zero.mpr (s.seq_pos _).ne']
  apply (tendsto_add_atTop_iff_nat (s.cut + 1)).1
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift

lemma Approximation.b_div_tendsto_zero (s : Approximation) :
    Tendsto (fun n : ℕ => (s.b n : ℝ) / s.seq n) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / s.seq n) atTop (nhds 0) := by
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp s.seq_tendsto_atTop
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop s.cut] with n hn
    have hb := s.eventualParity n hn
    have hble : s.b n ≤ 1 := by rw [hb]; exact parityPerturbation_le_one n
    change (s.b n : ℝ) / s.seq n ≤ (1 : ℝ) / s.seq n
    exact div_le_div_of_nonneg_right (by exact_mod_cast hble) (Nat.cast_nonneg _)
  · exact hinv

lemma Approximation.prefix_ratio_tendsto (s : Approximation) :
    Tendsto (fun n : ℕ => (prefixSum s.seq n : ℝ) / s.seq n) atTop (nhds φ) := by
  have hlim := s.ratio_tendsto.sub s.b_div_tendsto_zero
  have hlim' : Tendsto (fun n : ℕ =>
      (s.seq (n + 1) : ℝ) / s.seq n - (s.b n : ℝ) / s.seq n) atTop (nhds φ) := by
    simpa using hlim
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop s.cut] with n hn
  have hrec := generated_recurrence s.b (s.cut_ge.trans hn)
  change s.seq (n + 1) = prefixSum s.seq n + s.b n at hrec
  push_cast [hrec]
  rw [div_sub_div_same, add_sub_cancel_right]

lemma Approximation.exists_permanent_certificate (s : Approximation) (m : ℕ) :
    ∃ N u L, m ≤ N ∧ 3 ≤ N ∧
      (∀ t, u ≤ t → t ≤ u + L → t ∈ subsetSums s.seq (Set.Icc m N)) ∧
      4 * prefixSum s.seq (N + 1) ≤ 4 * (L + 1) + 3 * s.seq N := by
  obtain ⟨H, hcomplete⟩ := s.every_tail_complete m
  have hratioShift : Tendsto (fun N : ℕ =>
      (prefixSum s.seq (N + 1) : ℝ) / s.seq (N + 1)) atTop (nhds φ) := by
    have h := s.prefix_ratio_tendsto.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.add_assoc] using h
  have hlt : ∀ᶠ N in atTop,
      (prefixSum s.seq (N + 1) : ℝ) / s.seq (N + 1) < 2 :=
    hratioShift.eventually_lt_const Real.goldenRatio_lt_two
  let K := max m (max (2 * H) (4 * (prefixSum s.seq m + 2 * H) + s.cut + 3))
  obtain ⟨N, hNratio, hNK⟩ := (hlt.and (eventually_ge_atTop K)).exists
  have hmN : m ≤ N := by
    dsimp [K] at hNK
    omega
  have hcutN : s.cut ≤ N := by
    dsimp [K] at hNK
    omega
  let T := blockTotal s.seq m N
  have hpref : prefixSum s.seq m + T = prefixSum s.seq (N + 1) := by
    dsimp [T]
    exact prefixSum_add_blockTotal s.seq (by omega)
  have hTlt : T < 2 * s.seq (N + 1) := by
    have hden : (0 : ℝ) < s.seq (N + 1) := by exact_mod_cast s.seq_pos (N + 1)
    have hmul := (div_lt_iff₀ hden).mp hNratio
    have hprefLt : prefixSum s.seq (N + 1) < 2 * s.seq (N + 1) := by
      exact_mod_cast hmul
    omega
  have hlast : s.seq N ≤ T := by
    dsimp [T]
    exact blockTotal_ge_last s.seq hmN
  have hNlarge := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) N
  have htwoH : 2 * H ≤ T := by
    dsimp [K] at hNK
    omega
  let L := T - 2 * H
  have hHL : H + L = T - H := by
    dsimp [L]
    omega
  have hsets : Set.Ico m (N + 1) = Set.Icc m N := by
    ext i
    simp only [Set.mem_Ico, Set.mem_Icc]
    omega
  have hfirst : ∀ t, H ≤ t → t ≤ s.seq (N + 1) - 1 →
      t ∈ subsetSums s.seq (Set.Ico m (N + 1)) := by
    intro t htH hta
    have htmem := hcomplete t htH
    exact subsetSums_restrict_below s.seq_strictMono.monotone htmem (by omega)
  have hsecond : ∀ t, T - s.seq (N + 1) + 1 ≤ t → t ≤ T - H →
      t ∈ subsetSums s.seq (Set.Ico m (N + 1)) := by
    intro t htlo hthi
    let q := T - t
    have hqH : H ≤ q := by dsimp [q]; omega
    have hqa : q ≤ s.seq (N + 1) - 1 := by dsimp [q]; omega
    have hqmem := hfirst q hqH hqa
    have hqmem' : q ∈ subsetSums s.seq (↑(Finset.Ico m (N + 1)) : Set ℕ) := by
      simpa using hqmem
    have hcomp := subsetSums_complement hqmem'
    have htotal : ∑ i ∈ Finset.Ico m (N + 1), s.seq i = T := rfl
    rw [htotal] at hcomp
    have heq : T - q = t := by dsimp [q]; omega
    rw [heq] at hcomp
    simpa using hcomp
  refine ⟨N, H, L, hmN, s.cut_ge.trans hcutN, ?_, ?_⟩
  · intro t htH htu
    have htTH : t ≤ T - H := by rw [← hHL]; exact htu
    have htmem : t ∈ subsetSums s.seq (Set.Ico m (N + 1)) := by
      by_cases hta : t ≤ s.seq (N + 1) - 1
      · exact hfirst t htH hta
      · apply hsecond t
        · omega
        · exact htTH
    rwa [hsets] at htmem
  · dsimp [L]
    dsimp [K] at hNK
    omega

/-- The finite data that permanently locks one tail as complete. -/
structure PermanentCertificate (s : Approximation) (m : ℕ) where
  N : ℕ
  u : ℕ
  L : ℕ
  start_le : m ≤ N
  three_le : 3 ≤ N
  interval : ∀ t, u ≤ t → t ≤ u + L → t ∈ subsetSums s.seq (Set.Icc m N)
  lock : 4 * prefixSum s.seq (N + 1) ≤ 4 * (L + 1) + 3 * s.seq N

lemma Approximation.certificate_nonempty (s : Approximation) (m : ℕ) :
    Nonempty (PermanentCertificate s m) := by
  obtain ⟨N, u, L, hmN, hN3, hinterval, hlock⟩ := s.exists_permanent_certificate m
  exact ⟨⟨N, u, L, hmN, hN3, hinterval, hlock⟩⟩

noncomputable def Approximation.certificate (s : Approximation) (m : ℕ) :
    PermanentCertificate s m := Classical.choice (s.certificate_nonempty m)

/-- All choices made at stage `j`, before the perturbation is installed. -/
structure StepChoice (j : ℕ) (s : Approximation) where
  K : ℕ
  cut_le : s.cut ≤ K
  cert : PermanentCertificate s j
  cert_le : cert.N ≤ K
  ratio_close :
    |(s.seq K : ℝ) / s.seq (K - 1) - φ| < (1 : ℝ) / (j + 1)
  prefix_close :
    |(prefixSum s.seq K : ℝ) / s.seq K - φ| < (1 : ℝ) / (j + 1)

lemma stepChoice_nonempty (j : ℕ) (s : Approximation) : Nonempty (StepChoice j s) := by
  let cert := s.certificate j
  let ε : ℝ := 1 / (j + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.mp s.ratio_tendsto ε hε
  obtain ⟨M₂, hM₂⟩ := Metric.tendsto_atTop.mp s.prefix_ratio_tendsto ε hε
  let k := max M₁ (max M₂ (max s.cut cert.N))
  let K := k + 1
  have hk₁ : M₁ ≤ k := by simp [k]
  have hk₂ : M₂ ≤ K := by
    dsimp [K, k]
    exact (le_max_left M₂ (max s.cut cert.N)).trans
      ((le_max_right M₁ (max M₂ (max s.cut cert.N))).trans (Nat.le_succ _))
  have hcut : s.cut ≤ K := by
    dsimp [K, k]
    exact ((le_max_left s.cut cert.N).trans (le_max_right M₂ (max s.cut cert.N))).trans
      ((le_max_right M₁ (max M₂ (max s.cut cert.N))).trans (Nat.le_succ _))
  have hcert : cert.N ≤ K := by
    dsimp [K, k]
    exact ((le_max_right s.cut cert.N).trans (le_max_right M₂ (max s.cut cert.N))).trans
      ((le_max_right M₁ (max M₂ (max s.cut cert.N))).trans (Nat.le_succ _))
  refine ⟨⟨K, hcut, cert, hcert, ?_, ?_⟩⟩
  · have hdist := hM₁ k hk₁
    rw [show K - 1 = k by simp [K]]
    simpa [ε, Real.dist_eq] using hdist
  · have hdist := hM₂ K hk₂
    simpa [ε, Real.dist_eq] using hdist

noncomputable def chooseStep (j : ℕ) (s : Approximation) : StepChoice j s :=
  Classical.choice (stepChoice_nonempty j s)

noncomputable def nextApproximation (j : ℕ) (s : Approximation) : Approximation :=
  s.extend (chooseStep j s).K (chooseStep j s).cut_le

noncomputable def stages : ℕ → Approximation
  | 0 => Approximation.initial
  | j + 1 => nextApproximation j (stages j)

noncomputable def perturbationIndex (j : ℕ) : ℕ := (chooseStep j (stages j)).K

@[simp] lemma stages_zero : stages 0 = Approximation.initial := rfl

lemma stages_succ (j : ℕ) : stages (j + 1) = nextApproximation j (stages j) := rfl

lemma stages_cut_succ (j : ℕ) : (stages (j + 1)).cut = perturbationIndex j + 1 := rfl

lemma stages_seq_succ_eq (j : ℕ) {n : ℕ} (hn : n ≤ perturbationIndex j) :
    (stages (j + 1)).seq n = (stages j).seq n := by
  simpa [stages_succ, nextApproximation, perturbationIndex] using
    Approximation.extend_seq_eq (stages j) (chooseStep j (stages j)).K
      (chooseStep j (stages j)).cut_le hn

lemma perturbationIndex_strictMono : StrictMono perturbationIndex := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hnext := (chooseStep (j + 1) (stages (j + 1))).cut_le
  rw [stages_cut_succ] at hnext
  change perturbationIndex j + 1 ≤ perturbationIndex (j + 1) at hnext
  exact hnext

lemma stages_cut_mono : Monotone (fun j => (stages j).cut) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [stages_cut_succ]
  exact (chooseStep j (stages j)).cut_le.trans (Nat.le_succ _)

lemma stages_cut_ge_index (j : ℕ) : j + 3 ≤ (stages j).cut := by
  induction j with
  | zero => norm_num [stages, Approximation.initial]
  | succ j ih =>
      rw [stages_cut_succ]
      have hcut := (chooseStep j (stages j)).cut_le
      change (stages j).cut ≤ perturbationIndex j at hcut
      omega

lemma stages_b_succ_eq (j : ℕ) {n : ℕ} (hn : n < (stages j).cut) :
    (stages (j + 1)).b n = (stages j).b n := by
  rw [stages_succ]
  change Approximation.modifiedB (stages j) (perturbationIndex j) n = (stages j).b n
  apply Approximation.modifiedB_before
  exact hn.trans_le (chooseStep j (stages j)).cut_le

lemma stages_b_stable {j k n : ℕ} (hjk : j ≤ k) (hn : n < (stages j).cut) :
    (stages k).b n = (stages j).b n := by
  induction k with
  | zero =>
      have : j = 0 := by omega
      subst j
      rfl
  | succ k ih =>
      by_cases hj : j = k + 1
      · subst j
        rfl
      · have hjk' : j ≤ k := by omega
        have hn' : n < (stages k).cut := hn.trans_le (stages_cut_mono hjk')
        rw [stages_b_succ_eq k hn', ih hjk']

noncomputable def finalB (n : ℕ) : ℕ := (stages (n + 1)).b n

def finalSeq : ℕ → ℕ := generated finalB

lemma finalB_eq_stage {j n : ℕ} (hn : n < (stages j).cut) : finalB n = (stages j).b n := by
  by_cases hj : j ≤ n + 1
  · exact stages_b_stable hj hn
  · have hnj : n + 1 ≤ j := by omega
    have hncut : n < (stages (n + 1)).cut := by
      have := stages_cut_ge_index (n + 1)
      omega
    exact (stages_b_stable hnj hncut).symm

lemma finalSeq_eq_stage {j n : ℕ} (hn : n < (stages j).cut) :
    finalSeq n = (stages j).seq n := by
  change generated finalB n = generated (stages j).b n
  apply generated_congr (N := n)
  · intro i hi hin
    exact finalB_eq_stage (hin.trans hn)
  · omega

lemma finalSeq_eq_at_perturbation (j : ℕ) {n : ℕ} (hn : n ≤ perturbationIndex j) :
    finalSeq n = (stages j).seq n := by
  calc
    finalSeq n = (stages (j + 1)).seq n := finalSeq_eq_stage (by rw [stages_cut_succ]; omega)
    _ = (stages j).seq n := stages_seq_succ_eq j hn

lemma final_admissible (n : ℕ) (hn : 3 ≤ n) : 4 * finalB n ≤ finalSeq n := by
  have hncut : n < (stages (n + 1)).cut := by
    have := stages_cut_ge_index (n + 1)
    omega
  rw [finalB, finalSeq_eq_stage hncut]
  exact (stages (n + 1)).admissible n hn

lemma finalSeq_pos (n : ℕ) : 0 < finalSeq n := generated_pos finalB n

lemma finalSeq_strictMono : StrictMono finalSeq := generated_strictMono finalB final_admissible

lemma subsetSums_congr_on {a c : ℕ → ℕ} {I : Set ℕ}
    (h : ∀ i, i ∈ I → a i = c i) : subsetSums a I = subsetSums c I := by
  ext t
  constructor
  · rintro ⟨F, hF, hsum⟩
    refine ⟨F, hF, ?_⟩
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (h i (hF hi)).symm
  · rintro ⟨F, hF, hsum⟩
    refine ⟨F, hF, ?_⟩
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro i hi
    exact h i (hF hi)

lemma final_every_tail_complete (m : ℕ) :
    ∃ H, ∀ n, H ≤ n → n ∈ subsetSums finalSeq (Set.Ici m) := by
  let choice := chooseStep m (stages m)
  let cert := choice.cert
  have hNle : cert.N ≤ perturbationIndex m := choice.cert_le
  have heq : ∀ i, i ∈ Set.Icc m cert.N → finalSeq i = (stages m).seq i := by
    intro i hi
    exact finalSeq_eq_at_perturbation m (hi.2.trans hNle)
  have hinterval : ∀ t, cert.u ≤ t → t ≤ cert.u + cert.L →
      t ∈ subsetSums finalSeq (Set.Icc m cert.N) := by
    intro t htu hut
    rw [subsetSums_congr_on heq]
    exact cert.interval t htu hut
  have hpref : prefixSum finalSeq (cert.N + 1) =
      prefixSum (stages m).seq (cert.N + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply finalSeq_eq_at_perturbation m
    have hiN : i ≤ cert.N := by simp only [Finset.mem_range] at hi; omega
    exact hiN.trans hNle
  have hseqN : finalSeq cert.N = (stages m).seq cert.N :=
    finalSeq_eq_at_perturbation m hNle
  apply permanent_interval_certificate finalSeq finalB cert.start_le finalSeq_pos
    finalSeq_strictMono.monotone
  · intro n hn
    exact generated_recurrence finalB (cert.three_le.trans hn)
  · intro n hn
    exact final_admissible n (cert.three_le.trans hn)
  · exact hinterval
  · rw [hpref, hseqN]
    exact cert.lock

lemma finite_deletion_complete (D : Set ℕ) (hD : D.Finite) :
    ∃ H, ∀ n, H ≤ n → n ∈ subsetSums finalSeq Dᶜ := by
  let m := ∑ i ∈ hD.toFinset, (i + 1)
  have hbound : ∀ i, i ∈ D → i < m := by
    intro i hi
    have hiF : i ∈ hD.toFinset := by simpa using hi
    have hle := term_le_finset_sum (fun j => j + 1) hiF
    dsimp [m]
    omega
  obtain ⟨H, htail⟩ := final_every_tail_complete m
  refine ⟨H, ?_⟩
  intro n hn
  apply subsetSums_mono (I := Set.Ici m) (J := Dᶜ) ?_ (htail n hn)
  intro i him hiD
  exact (not_lt_of_ge him) (hbound i hiD)

lemma infinite_deletion_incomplete (D : Set ℕ) (hD : D.Infinite) :
    ∀ H, ∃ n, H ≤ n ∧ n ∉ subsetSums finalSeq Dᶜ := by
  intro H
  obtain ⟨p₀, hp₀D, hp₀⟩ := hD.exists_gt 0
  obtain ⟨p₁, hp₁D, hp₁⟩ := hD.exists_gt p₀
  obtain ⟨p₂, hp₂D, hp₂⟩ := hD.exists_gt p₁
  obtain ⟨i, hiD, hi⟩ := hD.exists_gt (max p₂ (H + 3))
  let M := finalSeq (i + 1) - 1
  have hi3 : 3 ≤ i := by omega
  have hHM : H ≤ M := by
    have hlower := strictMono_nat_lower finalSeq_strictMono (finalSeq_pos 0) (i + 1)
    dsimp [M]
    omega
  refine ⟨M, hHM, ?_⟩
  rintro ⟨F, hF, hsum⟩
  have hFi : ∀ k, k ∈ F → k < i := by
    intro k hk
    have hkD : k ∉ D := hF hk
    by_contra hki
    have hik : i ≤ k := Nat.le_of_not_gt hki
    rcases hik.eq_or_lt with rfl | hik
    · exact hkD hiD
    · have hseqle : finalSeq (i + 1) ≤ finalSeq k :=
        finalSeq_strictMono.monotone (by omega)
      have hterm : finalSeq k ≤ M := by
        rw [← hsum]
        exact term_le_finset_sum finalSeq hk
      have hpos := finalSeq_pos (i + 1)
      dsimp [M] at hterm
      omega
  let P : Finset ℕ := {p₀, p₁, p₂}
  have hPF : Disjoint P F := by
    apply Finset.disjoint_left.mpr
    intro k hkP hkF
    have hknot : k ∉ D := hF hkF
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hkP
    rcases hkP with rfl | rfl | rfl
    · exact hknot hp₀D
    · exact hknot hp₁D
    · exact hknot hp₂D
  have hsub : P ∪ F ⊆ Finset.range i := by
    intro k hk
    simp only [Finset.mem_union, Finset.mem_range] at hk ⊢
    rcases hk with hk | hk
    · simp only [P, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> omega
    · exact hFi k hk
  have hsumle : (∑ k ∈ P ∪ F, finalSeq k) ≤ prefixSum finalSeq i := by
    dsimp [prefixSum]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k hk hnot
    omega
  have hPthree : 3 ≤ ∑ k ∈ P, finalSeq k := by
    have hp₀pos := finalSeq_pos p₀
    have hp₁pos := finalSeq_pos p₁
    have hp₂pos := finalSeq_pos p₂
    simp only [P]
    rw [Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp; omega), Finset.sum_singleton]
    omega
  rw [Finset.sum_union hPF, hsum] at hsumle
  have hrec := generated_recurrence finalB hi3
  change finalSeq (i + 1) = prefixSum finalSeq i + finalB i at hrec
  dsimp [M] at hsumle
  omega

lemma final_growth_nat (n : ℕ) : 6 * finalSeq n ≤ 5 * finalSeq (n + 1) := by
  by_cases hn : n < 5
  · interval_cases n
    · norm_num [finalSeq, generated, generatedState]
    · norm_num [finalSeq, generated, generatedState]
    · norm_num [finalSeq, generated, generatedState]
    · have hrec := generated_recurrence finalB (n := 3) (by omega)
      change finalSeq 4 = prefixSum finalSeq 3 + finalB 3 at hrec
      norm_num [prefixSum, finalSeq, generated, generatedState] at hrec ⊢
      omega
    · have hrec3 := generated_recurrence finalB (n := 3) (by omega)
      change finalSeq 4 = prefixSum finalSeq 3 + finalB 3 at hrec3
      have hrec := generated_second_order finalB (n := 3) (by omega)
      change finalSeq 5 + finalB 3 = finalSeq 4 + finalSeq 3 + finalB 4 at hrec
      have hadm := final_admissible 3 (by omega)
      norm_num [prefixSum, finalSeq, generated, generatedState] at hrec3 hadm ⊢
      omega
  · have hn5 : 5 ≤ n := Nat.le_of_not_gt hn
    have hrec0 := generated_second_order finalB (n := n - 2) (by omega)
    have hrec1 := generated_second_order finalB (n := n - 1) (by omega)
    rw [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at hrec0
    rw [show n - 1 + 2 = n + 1 by omega, Nat.sub_add_cancel (by omega : 1 ≤ n)] at hrec1
    change finalSeq n + finalB (n - 2) =
      finalSeq (n - 1) + finalSeq (n - 2) + finalB (n - 1) at hrec0
    change finalSeq (n + 1) + finalB (n - 1) =
      finalSeq n + finalSeq (n - 1) + finalB n at hrec1
    have hmono := finalSeq_strictMono (show n - 2 < n - 1 by omega)
    have hadmPrev := final_admissible (n - 1) (by omega)
    have hupper : 4 * finalSeq n < 9 * finalSeq (n - 1) := by omega
    have hlower : 4 * finalSeq n + 3 * finalSeq (n - 1) ≤ 4 * finalSeq (n + 1) := by
      omega
    omega

lemma final_growth_ratio (n : ℕ) :
    (6 : ℝ) / 5 ≤ (finalSeq (n + 1) : ℝ) / finalSeq n := by
  have hgrowth := final_growth_nat n
  have hpos : (0 : ℝ) < finalSeq n := by exact_mod_cast finalSeq_pos n
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hpos).2
  exact_mod_cast (show 6 * finalSeq n ≤ finalSeq (n + 1) * 5 by omega)

lemma final_prefix_eq_stage_at_perturbation (j : ℕ) :
    prefixSum finalSeq (perturbationIndex j) =
      prefixSum (stages j).seq (perturbationIndex j) := by
  apply Finset.sum_congr rfl
  intro i hi
  apply finalSeq_eq_at_perturbation j
  simp only [Finset.mem_range] at hi
  omega

lemma pre_perturbation_close (j : ℕ) :
    |(finalSeq (perturbationIndex j) : ℝ) /
        finalSeq (perturbationIndex j - 1) - φ| < (1 : ℝ) / (j + 1) := by
  have hK := (chooseStep j (stages j)).ratio_close
  rw [finalSeq_eq_at_perturbation j (le_refl _),
    finalSeq_eq_at_perturbation j (Nat.sub_le _ _)]
  exact hK

lemma prefix_at_perturbation_close (j : ℕ) :
    |(prefixSum finalSeq (perturbationIndex j) : ℝ) /
        finalSeq (perturbationIndex j) - φ| < (1 : ℝ) / (j + 1) := by
  rw [final_prefix_eq_stage_at_perturbation j,
    finalSeq_eq_at_perturbation j (le_refl _)]
  exact (chooseStep j (stages j)).prefix_close

lemma tendsto_of_abs_sub_lt_one_div {f : ℕ → ℝ} {x : ℝ}
    (h : ∀ j, |f j - x| < (1 : ℝ) / (j + 1)) : Tendsto f atTop (nhds x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hone : Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hone ε hε
  refine ⟨J, ?_⟩
  intro j hj
  have hsmall : (1 : ℝ) / (j + 1) < ε := by
    have := hJ j hj
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 1 / (j + 1))] at this
    exact this
  rw [Real.dist_eq]
  exact (h j).trans hsmall

lemma pre_perturbation_tendsto :
    Tendsto (fun j : ℕ => (finalSeq (perturbationIndex j) : ℝ) /
      finalSeq (perturbationIndex j - 1)) atTop (nhds φ) :=
  tendsto_of_abs_sub_lt_one_div pre_perturbation_close

lemma prefix_at_perturbation_tendsto :
    Tendsto (fun j : ℕ => (prefixSum finalSeq (perturbationIndex j) : ℝ) /
      finalSeq (perturbationIndex j)) atTop (nhds φ) :=
  tendsto_of_abs_sub_lt_one_div prefix_at_perturbation_close

lemma finalSeq_tendsto_atTop : Tendsto (fun n : ℕ => (finalSeq n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (Eventually.of_forall fun (n : ℕ) => show (n : ℝ) ≤ (finalSeq n : ℝ) by
      exact_mod_cast
        (strictMono_nat_lower finalSeq_strictMono (finalSeq_pos 0) n |>.trans' (by omega)))
  exact tendsto_natCast_atTop_atTop

lemma values_at_perturbations_tendsto_atTop :
    Tendsto (fun j : ℕ => (finalSeq (perturbationIndex j) : ℝ)) atTop atTop :=
  finalSeq_tendsto_atTop.comp perturbationIndex_strictMono.tendsto_atTop

lemma floor_quarter_ratio_tendsto :
    Tendsto (fun j : ℕ =>
      ((finalSeq (perturbationIndex j) / 4 : ℕ) : ℝ) / finalSeq (perturbationIndex j))
      atTop (nhds ((1 : ℝ) / 4)) := by
  have hinv : Tendsto (fun j : ℕ => (1 : ℝ) / finalSeq (perturbationIndex j))
      atTop (nhds 0) := by
    simpa [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp values_at_perturbations_tendsto_atTop
  have herr : Tendsto (fun j : ℕ => (1 : ℝ) / 4 -
      ((finalSeq (perturbationIndex j) / 4 : ℕ) : ℝ) / finalSeq (perturbationIndex j))
      atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hinv
    · exact Eventually.of_forall fun j => by
        let x := finalSeq (perturbationIndex j)
        have hx : (0 : ℝ) < x := by exact_mod_cast finalSeq_pos (perturbationIndex j)
        have hmul : 4 * (x / 4) ≤ x := Nat.mul_div_le x 4
        change 0 ≤ (1 : ℝ) / 4 - ((x / 4 : ℕ) : ℝ) / (x : ℝ)
        apply sub_nonneg.mpr
        apply (div_le_iff₀ hx).2
        have hmulR : (4 : ℝ) * (x / 4 : ℕ) ≤ (x : ℝ) := by exact_mod_cast hmul
        norm_num [div_eq_mul_inv] at hmulR ⊢
        linarith
    · exact Eventually.of_forall fun j => by
        let x := finalSeq (perturbationIndex j)
        have hxnat : 0 < x := finalSeq_pos (perturbationIndex j)
        have hx : (0 : ℝ) < x := by exact_mod_cast hxnat
        have hmod := Nat.mod_lt x (by omega : 0 < 4)
        have hdecomp := Nat.mod_add_div x 4
        have hlt : x < 4 * (x / 4) + 4 := by omega
        change (1 : ℝ) / 4 - ((x / 4 : ℕ) : ℝ) / (x : ℝ) ≤ 1 / (x : ℝ)
        apply (le_div_iff₀ hx).2
        have heq : ((1 : ℝ) / 4 - ((x / 4 : ℕ) : ℝ) / (x : ℝ)) * x =
            (x : ℝ) / 4 - (x / 4 : ℕ) := by
          field_simp [hx.ne']
        rw [heq]
        have hltR : (x : ℝ) < 4 * (x / 4 : ℕ) + 4 := by exact_mod_cast hlt
        linarith
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ) / 4) atTop (nhds ((1 : ℝ) / 4)) :=
    tendsto_const_nhds
  simpa only [sub_sub_cancel, sub_zero] using hconst.sub herr

lemma finalB_at_perturbation (j : ℕ) :
    finalB (perturbationIndex j) = finalSeq (perturbationIndex j) / 4 := by
  calc
    finalB (perturbationIndex j) = (stages (j + 1)).b (perturbationIndex j) :=
      finalB_eq_stage (by rw [stages_cut_succ]; omega)
    _ = (stages j).seq (perturbationIndex j) / 4 := by
      rw [stages_succ]
      change Approximation.modifiedB (stages j) (perturbationIndex j)
        (perturbationIndex j) = _
      exact Approximation.modifiedB_at _ _
    _ = finalSeq (perturbationIndex j) / 4 := by
      rw [finalSeq_eq_at_perturbation j (le_refl _)]

lemma post_perturbation_decomposition (j : ℕ) :
    (finalSeq (perturbationIndex j + 1) : ℝ) / finalSeq (perturbationIndex j) =
      (prefixSum finalSeq (perturbationIndex j) : ℝ) / finalSeq (perturbationIndex j) +
        ((finalSeq (perturbationIndex j) / 4 : ℕ) : ℝ) /
          finalSeq (perturbationIndex j) := by
  have hK3 : 3 ≤ perturbationIndex j :=
    (stages j).cut_ge.trans (chooseStep j (stages j)).cut_le
  have hrec := generated_recurrence finalB hK3
  change finalSeq (perturbationIndex j + 1) =
    prefixSum finalSeq (perturbationIndex j) + finalB (perturbationIndex j) at hrec
  rw [finalB_at_perturbation] at hrec
  push_cast [hrec]
  ring

lemma post_perturbation_tendsto :
    Tendsto (fun j : ℕ => (finalSeq (perturbationIndex j + 1) : ℝ) /
      finalSeq (perturbationIndex j)) atTop (nhds (φ + (1 : ℝ) / 4)) := by
  have h := prefix_at_perturbation_tendsto.add floor_quarter_ratio_tendsto
  apply h.congr'
  exact Eventually.of_forall fun j => (post_perturbation_decomposition j).symm

/-- The two subsequential limits force the full quotient sequence not to converge. -/
lemma final_quotients_not_convergent :
    ¬ ∃ x : ℝ, Tendsto (fun n : ℕ => (finalSeq (n + 1) : ℝ) / finalSeq n)
      atTop (nhds x) := by
  rintro ⟨x, hx⟩
  have hKtop : Tendsto perturbationIndex atTop atTop :=
    perturbationIndex_strictMono.tendsto_atTop
  have hpreSub : Tendsto (fun j => perturbationIndex j - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hKtop
  have hpreX := hx.comp hpreSub
  have hpostX := hx.comp hKtop
  have hKpos (j : ℕ) : 1 ≤ perturbationIndex j := by
    have hK3 := (stages j).cut_ge.trans (chooseStep j (stages j)).cut_le
    change 1 ≤ (chooseStep j (stages j)).K
    omega
  have hpreX' : Tendsto (fun j => (finalSeq (perturbationIndex j) : ℝ) /
      finalSeq (perturbationIndex j - 1)) atTop (nhds x) := by
    convert hpreX using 1
    funext j
    simp only [Function.comp_apply]
    rw [Nat.sub_add_cancel (hKpos j)]
  have hpreEq : x = φ := tendsto_nhds_unique hpreX' pre_perturbation_tendsto
  have hpostEq : x = φ + (1 : ℝ) / 4 :=
    tendsto_nhds_unique hpostX post_perturbation_tendsto
  rw [hpreEq] at hpostEq
  norm_num at hpostEq

/-!
The main result, with deletion represented by sets of indices. Since `finalSeq` is strictly
increasing, this is equivalent to deleting finite or infinite subsequences of its terms.
-/
theorem erdos346 :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 0 < a n) ∧
      (∀ D : Set ℕ, D.Finite →
        ∃ H, ∀ n, H ≤ n → n ∈ subsetSums a Dᶜ) ∧
      (∀ D : Set ℕ, D.Infinite →
        ∀ H, ∃ n, H ≤ n ∧ n ∉ subsetSums a Dᶜ) ∧
      (∀ n, (6 : ℝ) / 5 ≤ (a (n + 1) : ℝ) / a n) ∧
      (∃ N : ℕ → ℕ, StrictMono N ∧
        Tendsto (fun j => (a (N j) : ℝ) / a (N j - 1)) atTop (nhds φ) ∧
        Tendsto (fun j => (a (N j + 1) : ℝ) / a (N j))
          atTop (nhds (φ + (1 : ℝ) / 4))) ∧
      ¬ ∃ x : ℝ, Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (nhds x) := by
  refine ⟨finalSeq, finalSeq_strictMono, finalSeq_pos, finite_deletion_complete,
    infinite_deletion_incomplete, final_growth_ratio, ?_, final_quotients_not_convergent⟩
  exact ⟨perturbationIndex, perturbationIndex_strictMono,
    pre_perturbation_tendsto, post_perturbation_tendsto⟩

#print axioms Erdos346.erdos346

end

end Erdos346
