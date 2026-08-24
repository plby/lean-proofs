/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1179.
https://www.erdosproblems.com/forum/thread/1179

Informal authors:
- Paul Erdős
- Richard R. Hall

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1179.md
-/
import Mathlib
import ErdosProblems.Erdos807.SecondMoment
import ErdosProblems.Erdos807.Parameters

/-!
# Erdős Problem 1179

For a finite abelian group `G` and a finite set `A ⊆ G`, this file counts the
subsets of `A` having each prescribed sum.  It proves the elementary sharp
lower bound and the Erdős--Hall asymptotic upper bound, including the transfer
from independent ordered samples to the literal uniform distribution on
fixed-cardinality subsets.

The detailed mathematical proof and the dictionary used in this formalization
are in `tex/1179.tex`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos1179

universe u

section BasicDefinitions

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The sum of the elements of a finite subset of an additive group. -/
def subsetSum (S : Finset G) : G := ∑ x ∈ S, x

/-- The number of subsets of `A` having sum `g`. -/
noncomputable def setRepCount (A : Finset G) (g : G) : ℕ := by
  classical
  exact (A.powerset.filter fun S ↦ subsetSum S = g).card

/-- The relative-uniformity conclusion in Problem 1179. -/
def SetBalanced (ε : ℝ) (A : Finset G) : Prop :=
  ∀ g : G,
    |(setRepCount A g : ℝ) - (2 : ℝ) ^ A.card / Fintype.card G| ≤
      ε * ((2 : ℝ) ^ A.card / Fintype.card G)

/-- The finite type of `k`-element subsets of `G`. -/
abbrev KSubsets (G : Type*) [Fintype G] (k : ℕ) :=
  {A : Finset G // A.card = k}

/-- Literal uniform probability on a nonempty finite sample type. -/
noncomputable def uniformProbability {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) : ℝ :=
  (Nat.card {ω // P ω} : ℝ) / Fintype.card Ω

/-- Probability that a uniform `k`-subset is `ε`-balanced. -/
noncomputable def subsetSuccessProbability (ε : ℝ) (k : ℕ) : ℝ :=
  uniformProbability (fun A : KSubsets G k ↦ SetBalanced ε A.1)

/-- Boolean coefficient vectors, used as the labelled subsets of a tuple. -/
abbrev BitVec (k : ℕ) := Fin k → Bool

/-- Sum the coordinates selected by a Boolean coefficient vector. -/
def tupleSubsetSum {k : ℕ} (a : Fin k → G) (e : BitVec k) : G :=
  ∑ i, if e i then a i else 0

/-- Number of Boolean coefficient vectors representing `g` from `a`. -/
noncomputable def tupleRepCount {k : ℕ} (a : Fin k → G) (g : G) : ℕ := by
  classical
  exact (Finset.univ.filter fun e : BitVec k ↦ tupleSubsetSum a e = g).card

/-- Balancedness for an independently sampled ordered tuple. -/
def TupleBalanced {k : ℕ} (ε : ℝ) (a : Fin k → G) : Prop :=
  ∀ g : G,
    |(tupleRepCount a g : ℝ) - (2 : ℝ) ^ k / Fintype.card G| ≤
      ε * ((2 : ℝ) ^ k / Fintype.card G)

/-- Probability that a uniform ordered tuple is balanced. -/
noncomputable def tupleSuccessProbability (ε : ℝ) (k : ℕ) : ℝ :=
  uniformProbability (fun a : Fin k → G ↦ TupleBalanced ε a)

end BasicDefinitions

section RepresentationAlgebra

variable {G : Type*} [AddCommGroup G] [Fintype G]

@[simp] lemma card_bitVec (k : ℕ) : Fintype.card (BitVec k) = 2 ^ k := by
  simp [BitVec]

noncomputable def natIndicator (P : Prop) : ℕ := by
  classical
  exact if P then 1 else 0

lemma tupleRepCount_eq_sum_indicator {k : ℕ} (a : Fin k → G) (g : G) :
    tupleRepCount a g =
      ∑ e : BitVec k, natIndicator (tupleSubsetSum a e = g) := by
  classical
  rw [tupleRepCount, Finset.card_filter]
  rfl

/-- The representation function has total mass `2 ^ k`. -/
lemma sum_tupleRepCount {k : ℕ} (a : Fin k → G) :
    ∑ g : G, tupleRepCount a g = 2 ^ k := by
  classical
  unfold tupleRepCount
  calc
    ∑ g : G, (Finset.univ.filter fun e : BitVec k ↦ tupleSubsetSum a e = g).card =
        (Finset.univ : Finset (BitVec k)).card := by
      symm
      simpa only [Finset.sum_const_zero, Finset.sum_filter, Finset.mem_univ, true_and] using
        (Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset (BitVec k)))
          (t := (Finset.univ : Finset G))
          (f := tupleSubsetSum a) (fun _ _ ↦ Finset.mem_univ _))
    _ = Fintype.card (BitVec k) := Finset.card_univ
    _ = 2 ^ k := card_bitVec k

/-- A representation count is bounded by the number of Boolean vectors. -/
lemma tupleRepCount_le_pow {k : ℕ} (a : Fin k → G) (g : G) :
    tupleRepCount a g ≤ 2 ^ k := by
  classical
  rw [tupleRepCount, ← card_bitVec k, ← Finset.card_univ]
  exact Finset.card_filter_le _ _

@[simp] lemma tupleSubsetSum_append {k s : ℕ} (a : Fin k → G) (b : Fin s → G)
    (e : BitVec k) (f : BitVec s) :
    tupleSubsetSum (Fin.append a b) (Fin.append e f) =
      tupleSubsetSum a e + tupleSubsetSum b f := by
  rw [tupleSubsetSum, Fin.sum_univ_add]
  simp [tupleSubsetSum]

/-- Concatenating tuples convolves their representation functions. -/
lemma tupleRepCount_append {k s : ℕ} (a : Fin k → G) (b : Fin s → G) (g : G) :
    tupleRepCount (Fin.append a b) g =
      ∑ f : BitVec s, tupleRepCount a (g - tupleSubsetSum b f) := by
  classical
  rw [tupleRepCount_eq_sum_indicator]
  rw [← (Fin.appendEquiv k s).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ e : BitVec k, ∑ f : BitVec s,
    natIndicator (tupleSubsetSum (Fin.append a b) (Fin.append e f) = g)) = _
  simp only [tupleSubsetSum_append]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [tupleRepCount_eq_sum_indicator]
  apply Finset.sum_congr rfl
  intro e _
  simp only [natIndicator]
  rw [eq_sub_iff_add_eq]

@[simp] lemma tupleSubsetSum_insertNth {k : ℕ} (p : Fin (k + 1)) (x : G)
    (a : Fin k → G) (e : BitVec (k + 1)) :
    tupleSubsetSum (p.insertNth x a) e =
      (if e p then x else 0) +
        tupleSubsetSum a (fun j ↦ e (p.succAbove j)) := by
  rw [tupleSubsetSum, Fin.sum_univ_succAbove _ p]
  simp [tupleSubsetSum]

lemma sum_natIndicator_add_eq (c g : G) :
    ∑ x : G, natIndicator (x + c = g) = 1 := by
  classical
  simp only [natIndicator, eq_sub_iff_add_eq.symm]
  simp

lemma sum_natIndicator_eq_add (c g : G) :
    ∑ x : G, natIndicator (c = x + g) = 1 := by
  classical
  simp only [natIndicator]
  have h : ∀ x : G, (c = x + g) ↔ x = c - g := fun x ↦ by
    constructor <;> intro hx
    · exact eq_sub_iff_add_eq.mpr hx.symm
    · exact (eq_sub_iff_add_eq.mp hx).symm
  simp_rw [h]
  simp

/-- A nontrivial Boolean affine equation holds for exactly a `1 / |G|`
fraction of all tuples.  This is the solve-one-coordinate count. -/
lemma sum_affine_collision_indicator {k : ℕ} (e f : BitVec k) (hef : e ≠ f)
    (u v : G) :
    ∑ a : Fin k → G,
      natIndicator (tupleSubsetSum a e + u = tupleSubsetSum a f + v) =
        Fintype.card G ^ (k - 1) := by
  classical
  cases k with
  | zero =>
      exact (hef (Subsingleton.elim e f)).elim
  | succ n =>
      obtain ⟨p, hp⟩ : ∃ p : Fin (n + 1), e p ≠ f p := by
        by_contra h
        push_neg at h
        exact hef (funext h)
      rw [← (Fin.insertNthEquiv (fun _ : Fin (n + 1) ↦ G) p).sum_comp]
      rw [Fintype.sum_prod_type]
      change (∑ x : G, ∑ a : Fin n → G,
        natIndicator
          (tupleSubsetSum (p.insertNth x a) e + u =
            tupleSubsetSum (p.insertNth x a) f + v)) = _
      rw [Finset.sum_comm]
      calc
        (∑ a : Fin n → G, ∑ x : G,
          natIndicator
            (tupleSubsetSum (p.insertNth x a) e + u =
              tupleSubsetSum (p.insertNth x a) f + v)) =
            ∑ _a : Fin n → G, 1 := by
          apply Finset.sum_congr rfl
          intro a _
          cases hep : e p <;> cases hfp : f p
          · exact (hp (by simp [hep, hfp])).elim
          · simpa [tupleSubsetSum_insertNth, hep, hfp, add_assoc, add_comm,
                add_left_comm] using
              sum_natIndicator_eq_add
                (tupleSubsetSum a (fun j ↦ e (p.succAbove j)) + u)
                (tupleSubsetSum a (fun j ↦ f (p.succAbove j)) + v)
          · simpa [tupleSubsetSum_insertNth, hep, hfp, add_assoc] using
              sum_natIndicator_add_eq
                (tupleSubsetSum a (fun j ↦ e (p.succAbove j)) + u)
                (tupleSubsetSum a (fun j ↦ f (p.succAbove j)) + v)
          · exact (hp (by simp [hep, hfp])).elim
        _ = Fintype.card G ^ n := by simp

/-- Two distinct Boolean coefficient vectors collide for exactly a `1 / |G|`
fraction of all tuples. -/
lemma sum_collision_indicator {k : ℕ} (e f : BitVec k) (hef : e ≠ f) :
    ∑ a : Fin k → G,
      natIndicator (tupleSubsetSum a e = tupleSubsetSum a f) =
        Fintype.card G ^ (k - 1) := by
  simpa using sum_affine_collision_indicator (G := G) e f hef 0 0

lemma natIndicator_and (P Q : Prop) :
    natIndicator P * natIndicator Q = natIndicator (P ∧ Q) := by
  classical
  by_cases hP : P <;> by_cases hQ : Q <;> simp [natIndicator, hP, hQ]

lemma sum_common_value_indicator (x y : G) :
    ∑ g : G, natIndicator (x = g) * natIndicator (y = g) =
      natIndicator (x = y) := by
  classical
  by_cases h : x = y
  · subst y
    simp [natIndicator]
  · simp only [natIndicator]
    simp [h]

/-- `∑ R(g)^2` counts ordered pairs of Boolean vectors with the same sum. -/
lemma sum_tupleRepCount_sq {k : ℕ} (a : Fin k → G) :
    ∑ g : G, tupleRepCount a g ^ 2 =
      ∑ e : BitVec k, ∑ f : BitVec k,
        natIndicator (tupleSubsetSum a e = tupleSubsetSum a f) := by
  classical
  simp_rw [tupleRepCount_eq_sum_indicator, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  exact sum_common_value_indicator _ _

/-- The exact total collision count, before division by the number of tuples. -/
lemma sum_sum_tupleRepCount_sq (k : ℕ) :
    ∑ a : Fin k → G, ∑ g : G, tupleRepCount a g ^ 2 =
      2 ^ k * Fintype.card G ^ k +
        2 ^ k * (2 ^ k - 1) * Fintype.card G ^ (k - 1) := by
  classical
  simp_rw [sum_tupleRepCount_sq]
  rw [Finset.sum_comm]
  calc
    (∑ e : BitVec k, ∑ a : Fin k → G, ∑ f : BitVec k,
        natIndicator (tupleSubsetSum a e = tupleSubsetSum a f)) =
      ∑ _e : BitVec k,
        (Fintype.card G ^ k +
          (2 ^ k - 1) * Fintype.card G ^ (k - 1)) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.sum_comm]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e)]
        have hoff :
            ∑ f ∈ (Finset.univ.erase e : Finset (BitVec k)),
                ∑ a : Fin k → G,
                  natIndicator (tupleSubsetSum a e = tupleSubsetSum a f) =
              (2 ^ k - 1) * Fintype.card G ^ (k - 1) := by
          calc
            _ = ∑ _f ∈ (Finset.univ.erase e : Finset (BitVec k)),
                  Fintype.card G ^ (k - 1) := by
                apply Finset.sum_congr rfl
                intro f hf
                exact sum_collision_indicator e f
                  (Finset.ne_of_mem_erase hf).symm
            _ = (2 ^ k - 1) * Fintype.card G ^ (k - 1) := by
                simp [card_bitVec]
        rw [hoff]
        simp [natIndicator, Fintype.card_fun, add_comm]
    _ = 2 ^ k * Fintype.card G ^ k +
          2 ^ k * (2 ^ k - 1) * Fintype.card G ^ (k - 1) := by
      simp [card_bitVec]
      ring

/-- Squared `L²` distance of the representation function from its mean. -/
noncomputable def tupleDispersion {k : ℕ} (a : Fin k → G) : ℝ :=
  ∑ g : G,
    ((tupleRepCount a g : ℝ) -
      (2 : ℝ) ^ k / Fintype.card G) ^ 2

lemma tupleDispersion_eq {k : ℕ} (a : Fin k → G) :
    tupleDispersion a =
      (∑ g : G, (tupleRepCount a g : ℝ) ^ 2) -
        (2 : ℝ) ^ (2 * k) / Fintype.card G := by
  classical
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by positivity
  have hmass : ∑ g : G, (tupleRepCount a g : ℝ) = (2 : ℝ) ^ k := by
    exact_mod_cast sum_tupleRepCount a
  unfold tupleDispersion
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hmiddle :
      ∑ g : G,
          2 * (tupleRepCount a g : ℝ) *
            ((2 : ℝ) ^ k / Fintype.card G) =
        2 * (2 : ℝ) ^ k * ((2 : ℝ) ^ k / Fintype.card G) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hmass]
  rw [hmiddle]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 by ring]
  field_simp
  ring

/-- Erdős--Rényi's exact dispersion identity on the finite uniform tuple
space. -/
theorem expectation_tupleDispersion (k : ℕ) :
    Erdos807.FiniteUniform.expectation
        (fun a : Fin k → G ↦ tupleDispersion a) =
      (2 : ℝ) ^ k * (1 - 1 / Fintype.card G) := by
  classical
  have hN0 : (Fintype.card G : ℝ) ≠ 0 := by positivity
  have hpow0 : (Fintype.card G : ℝ) ^ k ≠ 0 := pow_ne_zero _ hN0
  rw [Erdos807.FiniteUniform.expectation_eq_sum_div]
  simp_rw [tupleDispersion_eq]
  rw [Finset.sum_sub_distrib]
  have henergy :
      ∑ a : Fin k → G, ∑ g : G, (tupleRepCount a g : ℝ) ^ 2 =
        (2 : ℝ) ^ k * (Fintype.card G : ℝ) ^ k +
          (2 : ℝ) ^ k * ((2 : ℝ) ^ k - 1) *
            (Fintype.card G : ℝ) ^ (k - 1) := by
    have hnat := sum_sum_tupleRepCount_sq (G := G) k
    calc
      _ = ((∑ a : Fin k → G, ∑ g : G, tupleRepCount a g ^ 2 : ℕ) : ℝ) := by
        push_cast
        rfl
      _ = ((2 ^ k * Fintype.card G ^ k +
          2 ^ k * (2 ^ k - 1) * Fintype.card G ^ (k - 1) : ℕ) : ℝ) := by
        rw [hnat]
      _ = _ := by
        push_cast
        rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))]
        norm_num
  rw [henergy]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [show (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 by ring]
  by_cases hk : k = 0
  · subst k
    simp [hN0]
  · have hpow : (Fintype.card G : ℝ) ^ k =
        (Fintype.card G : ℝ) ^ (k - 1) * Fintype.card G := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      simp [pow_succ]
    rw [hpow]
    field_simp
    ring

/-- Number of Boolean sums of a block whose translate lands in `H`. -/
noncomputable def blockHitCount {s : ℕ} (H : Finset G) (b : Fin s → G)
    (g : G) : ℕ := by
  classical
  exact (Finset.univ.filter fun e : BitVec s ↦
    g - tupleSubsetSum b e ∈ H).card

lemma blockHitCount_eq_sum {s : ℕ} (H : Finset G) (b : Fin s → G) (g : G) :
    blockHitCount H b g =
      ∑ e : BitVec s,
        natIndicator (g - tupleSubsetSum b e ∈ H) := by
  classical
  rw [blockHitCount, Finset.card_filter]
  unfold natIndicator
  apply Finset.sum_congr rfl
  intro e _
  split <;> rfl

lemma mem_indicator_eq_sum (H : Finset G) (x : G) :
    natIndicator (x ∈ H) = ∑ h ∈ H, natIndicator (x = h) := by
  classical
  simp [natIndicator]

/-- Ordered pairs of distinct block subsets which both hit `H` at `g`. -/
noncomputable def blockCollisionAt {s : ℕ} (H : Finset G) (b : Fin s → G)
    (g : G) : ℕ :=
  ∑ e : BitVec s, ∑ f ∈ (Finset.univ.erase e : Finset (BitVec s)),
    natIndicator (g - tupleSubsetSum b e ∈ H) *
      natIndicator (g - tupleSubsetSum b f ∈ H)

/-- Total ordered collision mass over all translates. -/
noncomputable def blockCollisionMass {s : ℕ} (H : Finset G)
    (b : Fin s → G) : ℕ :=
  ∑ g : G, blockCollisionAt H b g

lemma blockCollisionAt_pos_of_two_hits {s : ℕ} (H : Finset G)
    (b : Fin s → G) (g : G) (h : 2 ≤ blockHitCount H b g) :
    0 < blockCollisionAt H b g := by
  classical
  rw [blockHitCount] at h
  have h' : 1 < (Finset.univ.filter fun e : BitVec s ↦
      g - tupleSubsetSum b e ∈ H).card := by omega
  rw [Finset.one_lt_card] at h'
  obtain ⟨e, he, f, hf, hef⟩ := h'
  have he' := (Finset.mem_filter.mp he).2
  have hf' := (Finset.mem_filter.mp hf).2
  unfold blockCollisionAt
  have hterm :
      0 < natIndicator (g - tupleSubsetSum b e ∈ H) *
        natIndicator (g - tupleSubsetSum b f ∈ H) := by
    simp [natIndicator, he', hf']
  apply Finset.sum_pos'
  · exact fun _ _ ↦ Nat.zero_le _
  · refine ⟨e, Finset.mem_univ e, ?_⟩
    apply Finset.sum_pos'
    · exact fun _ _ ↦ Nat.zero_le _
    · exact ⟨f, Finset.mem_erase.mpr ⟨hef.symm, Finset.mem_univ f⟩, hterm⟩

lemma blockCollisionAt_ge_one_of_two_hits {s : ℕ} (H : Finset G)
    (b : Fin s → G) (g : G) (h : 2 ≤ blockHitCount H b g) :
    1 ≤ blockCollisionAt H b g :=
  blockCollisionAt_pos_of_two_hits H b g h

lemma sub_eq_iff_add_eq' (g x h : G) : g - x = h ↔ x + h = g := by
  constructor <;> intro heq
  · rw [sub_eq_iff_eq_add] at heq
    simpa [add_comm] using heq.symm
  · rw [sub_eq_iff_eq_add]
    simpa [add_comm] using heq.symm

lemma sum_two_hit_indicators {s : ℕ} (H : Finset G) (b : Fin s → G)
    (e f : BitVec s) :
    ∑ g : G,
        natIndicator (g - tupleSubsetSum b e ∈ H) *
          natIndicator (g - tupleSubsetSum b f ∈ H) =
      ∑ h ∈ H, ∑ h' ∈ H,
        natIndicator
          (tupleSubsetSum b e + h = tupleSubsetSum b f + h') := by
  classical
  simp_rw [mem_indicator_eq_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h' _
  simpa only [sub_eq_iff_add_eq'] using
    sum_common_value_indicator
      (tupleSubsetSum b e + h) (tupleSubsetSum b f + h')

/-- Exact finite collision identity for a random block. -/
lemma sum_blockCollisionMass (H : Finset G) (s : ℕ) :
    ∑ b : Fin s → G, blockCollisionMass H b =
      2 ^ s * (2 ^ s - 1) * H.card ^ 2 *
        Fintype.card G ^ (s - 1) := by
  classical
  unfold blockCollisionMass blockCollisionAt
  have hreorder₁ :
      (∑ b : Fin s → G, ∑ g : G, ∑ e : BitVec s,
        ∑ f ∈ (Finset.univ.erase e : Finset (BitVec s)),
          natIndicator (g - tupleSubsetSum b e ∈ H) *
            natIndicator (g - tupleSubsetSum b f ∈ H)) =
      ∑ b : Fin s → G, ∑ e : BitVec s,
        ∑ f ∈ (Finset.univ.erase e : Finset (BitVec s)), ∑ g : G,
          natIndicator (g - tupleSubsetSum b e ∈ H) *
            natIndicator (g - tupleSubsetSum b f ∈ H) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_comm]
  rw [hreorder₁]
  simp_rw [sum_two_hit_indicators]
  have hreorder₂ :
      (∑ b : Fin s → G, ∑ e : BitVec s,
        ∑ f ∈ (Finset.univ.erase e : Finset (BitVec s)),
          ∑ h ∈ H, ∑ h' ∈ H,
            natIndicator
              (tupleSubsetSum b e + h = tupleSubsetSum b f + h')) =
      ∑ e : BitVec s,
        ∑ f ∈ (Finset.univ.erase e : Finset (BitVec s)),
          ∑ h ∈ H, ∑ h' ∈ H, ∑ b : Fin s → G,
            natIndicator
              (tupleSubsetSum b e + h = tupleSubsetSum b f + h') := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.sum_comm]
  rw [hreorder₂]
  calc
    (∑ e : BitVec s,
        ∑ f ∈ (Finset.univ.erase e : Finset (BitVec s)),
          ∑ h ∈ H, ∑ h' ∈ H, ∑ b : Fin s → G,
            natIndicator
              (tupleSubsetSum b e + h = tupleSubsetSum b f + h')) =
      ∑ e : BitVec s,
        ∑ f ∈ (Finset.univ.erase e : Finset (BitVec s)),
          ∑ _h ∈ H, ∑ _h' ∈ H, Fintype.card G ^ (s - 1) := by
        apply Finset.sum_congr rfl
        intro e _
        apply Finset.sum_congr rfl
        intro f hf
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro h' _
        exact sum_affine_collision_indicator e f
          (Finset.ne_of_mem_erase hf).symm h h'
    _ = 2 ^ s * (2 ^ s - 1) * H.card ^ 2 *
          Fintype.card G ^ (s - 1) := by
      simp [card_bitVec]
      ring

end RepresentationAlgebra

section BooleanRelations

variable {K : Type*} [AddCommGroup K] [Fintype K]

/-- The coefficient occurring after subtracting two Boolean relations. -/
def signedTerm (p q : Bool) (x : K) : K :=
  if p then (if q then 0 else x) else (if q then -x else 0)

lemma sum_signedTerm {m : ℕ} (x : Fin m → K) (e f : BitVec m) :
    ∑ i, signedTerm (e i) (f i) (x i) =
      tupleSubsetSum x e - tupleSubsetSum x f := by
  rw [tupleSubsetSum, tupleSubsetSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases e i <;> cases f i <;> simp [signedTerm]

lemma signedTerm_self (p : Bool) (x : K) : signedTerm p p x = 0 := by
  cases p <;> simp [signedTerm]

lemma signedTerm_left_injective {p q : Bool} (hpq : p ≠ q) :
    Function.Injective (signedTerm p q : K → K) := by
  intro x y hxy
  cases p <;> cases q
  · exact (hpq rfl).elim
  · exact neg_injective hxy
  · exact hxy
  · exact (hpq rfl).elim

/-- If a Boolean relation difference is supported on `I ∪ {j}` and has a
nonzero `j`-coefficient, its equation determines coordinate `j` from the
coordinates in `I`. -/
lemma pivot_determines_coordinate {m : ℕ} (I : Finset (Fin m)) (j : Fin m)
    (hjI : j ∉ I) (e f : BitVec m) (hej : e j ≠ f j)
    (hsupp : ∀ i, i ∉ insert j I → e i = f i)
    (x y : Fin m → K)
    (hxe : tupleSubsetSum x e = 0) (hxf : tupleSubsetSum x f = 0)
    (hye : tupleSubsetSum y e = 0) (hyf : tupleSubsetSum y f = 0)
    (hxy : ∀ i ∈ I, x i = y i) : x j = y j := by
  classical
  have hsumx : ∑ i, signedTerm (e i) (f i) (x i) = 0 := by
    rw [sum_signedTerm, hxe, hxf, sub_self]
  have hsumy : ∑ i, signedTerm (e i) (f i) (y i) = 0 := by
    rw [sum_signedTerm, hye, hyf, sub_self]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at hsumx hsumy
  have hrest :
      (∑ i ∈ (Finset.univ.erase j : Finset (Fin m)),
          signedTerm (e i) (f i) (x i)) =
        ∑ i ∈ (Finset.univ.erase j : Finset (Fin m)),
          signedTerm (e i) (f i) (y i) := by
    apply Finset.sum_congr rfl
    intro i hiErase
    by_cases hi : i ∈ I
    · rw [hxy _ hi]
    · have hne : i ≠ j := (Finset.mem_erase.mp hiErase).1
      have hout : i ∉ insert j I := by simp [hne, hi]
      rw [hsupp _ hout]
      simp [signedTerm_self]
  have hpivot : signedTerm (e j) (f j) (x j) =
      signedTerm (e j) (f j) (y j) := by
    rw [hrest] at hsumx
    exact add_left_cancel (hsumx.trans hsumy.symm)
  exact signedTerm_left_injective hej hpivot

/-- No two rows of `R` have a difference supported on `I`. -/
def RelationIndependent {m : ℕ} (R : Finset (BitVec m))
    (I : Finset (Fin m)) : Prop :=
  ∀ e ∈ R, ∀ f ∈ R, (∀ j, j ∉ I → e j = f j) → e = f

lemma relationIndependent_empty {m : ℕ} (R : Finset (BitVec m)) :
    RelationIndependent R ∅ := by
  intro e _ f _ h
  funext j
  exact h j (by simp)

lemma relationIndependent_card_bound {m : ℕ} {R : Finset (BitVec m)}
    {I : Finset (Fin m)} (hI : RelationIndependent R I) :
    R.card ≤ 2 ^ (m - I.card) := by
  classical
  let C := {j : Fin m // j ∉ I}
  let restrict : ↥R → C → Bool := fun e j ↦ e.1 j.1
  have hinj : Function.Injective restrict := by
    intro e f hef
    apply Subtype.ext
    apply hI e.1 e.2 f.1 f.2
    intro j hj
    exact congrFun hef ⟨j, hj⟩
  have hc := Fintype.card_le_of_injective restrict hinj
  simpa [restrict, C, Fintype.card_fun, Fintype.card_subtype_compl,
    card_bitVec] using hc

/-- Tuples in a finite abelian group satisfying every Boolean relation in
`R`. -/
noncomputable def relationSolutions {m : ℕ} (R : Finset (BitVec m)) :
    Finset (Fin m → K) := by
  classical
  exact Finset.univ.filter fun x ↦
    ∀ e ∈ R, tupleSubsetSum x e = 0

/-- Erdős--Hall's Boolean-relation lemma.  `d = clog₂ |R|` independent
Boolean relations remove at least `d` freely choosable group coordinates. -/
theorem card_relationSolutions_le {m : ℕ} (R : Finset (BitVec m))
    (hR : 2 ≤ R.card) :
    (relationSolutions (K := K) R).card ≤
      Fintype.card K ^ (m - Nat.clog 2 R.card) := by
  classical
  let candidates :=
    (Finset.univ.powerset : Finset (Finset (Fin m))).filter
      (RelationIndependent R)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, relationIndependent_empty]
  obtain ⟨I, hIcand, hImax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  have hIsub : I ⊆ (Finset.univ : Finset (Fin m)) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hIcand).1
  have hIind : RelationIndependent R I :=
    (Finset.mem_filter.mp hIcand).2
  have hnotind (j : Fin m) (hj : j ∉ I) :
      ¬ RelationIndependent R (insert j I) := by
    intro hind
    have hmem : insert j I ∈ candidates := by
      simp [candidates, hind]
    have hle := hImax (insert j I) hmem
    simp [Finset.card_insert_of_notMem hj] at hle
  have hpivot (j : Fin m) (hj : j ∉ I) :
      ∃ e ∈ R, ∃ f ∈ R,
        e ≠ f ∧ ∀ i, i ∉ insert j I → e i = f i := by
    have hn := hnotind j hj
    simp only [RelationIndependent, not_forall, _root_.not_imp] at hn
    obtain ⟨e, heR, f, hfR, hagree, hef⟩ := hn
    exact ⟨e, heR, f, hfR, hef, hagree⟩
  have hIcard : I.card ≤ m - Nat.clog 2 R.card := by
    have hRpow : R.card ≤ 2 ^ (m - I.card) :=
      relationIndependent_card_bound hIind
    have hRle : R.card ≤ 2 ^ m := by
      calc
        R.card ≤ Fintype.card (BitVec m) := by
          simpa using Finset.card_le_univ R
        _ = 2 ^ m := card_bitVec m
    have hdle : Nat.clog 2 R.card ≤ m := Nat.clog_le_of_le_pow hRle
    by_contra hle
    have hExp : m - I.card ≤ Nat.clog 2 R.card - 1 := by omega
    have hpowle : 2 ^ (m - I.card) ≤
        2 ^ (Nat.clog 2 R.card - 1) := by
      exact Nat.pow_le_pow_right (by norm_num) hExp
    have hpowlt : 2 ^ (Nat.clog 2 R.card - 1) < R.card :=
      Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    omega
  let restrict : ↥(relationSolutions (K := K) R) → ↥I → K :=
    fun x i ↦ x.1 i.1
  have hrestrict : Function.Injective restrict := by
    intro x y hxy
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ I
    · exact congrFun hxy ⟨j, hj⟩
    · obtain ⟨e, heR, f, hfR, hef, hsupp⟩ := hpivot j hj
      have hxsol := (Finset.mem_filter.mp x.2).2
      have hysol := (Finset.mem_filter.mp y.2).2
      apply pivot_determines_coordinate I j hj e f
      · intro heq
        apply hef
        apply hIind e heR f hfR
        intro i hiI
        by_cases hi : i = j
        · simpa [hi] using heq
        · exact hsupp i (by simp [hi, hiI])
      · exact hsupp
      · exact hxsol e heR
      · exact hxsol f hfR
      · exact hysol e heR
      · exact hysol f hfR
      · intro i hi
        exact congrFun hxy ⟨i, hi⟩
  have hcard := Fintype.card_le_of_injective restrict hrestrict
  calc
    (relationSolutions (K := K) R).card =
        Fintype.card ↥(relationSolutions (K := K) R) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (↥I → K) := hcard
    _ = Fintype.card K ^ I.card := by simp [Fintype.card_fun]
    _ ≤ Fintype.card K ^ (m - Nat.clog 2 R.card) := by
      exact Nat.pow_le_pow_right Fintype.card_pos hIcard

end BooleanRelations

section CharacterMoment

variable {G : Type*} [AddCommGroup G] [Fintype G]

abbrev Dual (G : Type*) [AddCommGroup G] := AddChar G ℂ

/-- Boolean relations among an `m`-tuple of characters. -/
noncomputable def characterRelations {m : ℕ} (χ : Fin m → Dual G) :
    Finset (BitVec m) := by
  classical
  exact Finset.univ.filter fun e ↦ tupleSubsetSum χ e = 0

/-- Number of Boolean relations among a tuple of characters. -/
noncomputable def characterRelationCount {m : ℕ} (χ : Fin m → Dual G) : ℕ :=
  (characterRelations χ).card

@[simp] lemma tupleSubsetSum_cons {m : ℕ} (a : G) (x : Fin m → G)
    (p : Bool) (e : BitVec m) :
    tupleSubsetSum (Fin.cons a x) (Fin.cons p e) =
      (if p then a else 0) + tupleSubsetSum x e := by
  rw [tupleSubsetSum, Fin.sum_univ_succ]
  simp [tupleSubsetSum]

/-- Expanding `∏ᵢ (1 + χᵢ(a))` selects a Boolean subfamily of the
characters. -/
lemma prod_one_add_character_eq_sum {m : ℕ} (χ : Fin m → Dual G) (a : G) :
    ∏ i, (1 + χ i a) =
      ∑ e : BitVec m, (tupleSubsetSum χ e) a := by
  classical
  induction m with
  | zero => simp [tupleSubsetSum]
  | succ m ih =>
      rw [← Fin.cons_self_tail χ]
      rw [Fin.prod_univ_succ]
      rw [← (Fin.consEquiv (fun _ : Fin (m + 1) ↦ Bool)).sum_comp]
      rw [Fintype.sum_prod_type]
      have hcons (p : Bool) (e : BitVec m) :
          (Fin.consEquiv (fun _ : Fin (m + 1) ↦ Bool)) (p, e) =
            Fin.cons p e := rfl
      simp_rw [hcons, tupleSubsetSum_cons]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
      rw [show (∑ p : Bool, ∑ e : BitVec m,
          ((if p then χ 0 else 0) +
            tupleSubsetSum (Fin.tail χ) e) a) =
        (∑ e : BitVec m, tupleSubsetSum (Fin.tail χ) e a) +
          χ 0 a *
            (∑ e : BitVec m,
              tupleSubsetSum (Fin.tail χ) e a) by
        simp [AddChar.add_apply, Finset.mul_sum]
        ac_rfl]
      rw [← ih (Fin.tail χ)]
      simp only [Fin.tail]
      ring

noncomputable def complexIndicator (P : Prop) (z : ℂ) : ℂ := by
  classical
  exact if P then z else 0

lemma sum_character_apply (x : G) :
    ∑ χ : Dual G, χ x =
      complexIndicator (x = 0) (Fintype.card G : ℂ) := by
  classical
  unfold complexIndicator
  simpa using AddChar.sum_apply_eq_ite x

lemma sum_character_product_at {m : ℕ} (χ : Fin m → Dual G) :
    ∑ a : G, ∏ i, χ i a =
      complexIndicator ((∑ i, χ i) = 0) (Fintype.card G : ℂ) := by
  classical
  have happly (a : G) : (∑ i, χ i) a = ∏ i, χ i a := by
    simp
  simp_rw [← happly]
  unfold complexIndicator
  simpa using AddChar.sum_eq_ite (∑ i, χ i)

/-- The corresponding expansion for one character evaluated on all entries
of a tuple. -/
lemma prod_one_add_single_character_eq_sum {k : ℕ} (ψ : Dual G)
    (a : Fin k → G) :
    ∏ i, (1 + ψ (a i)) =
      ∑ e : BitVec k, ψ (tupleSubsetSum a e) := by
  classical
  induction k with
  | zero => simp [tupleSubsetSum]
  | succ k ih =>
      rw [← Fin.cons_self_tail a]
      rw [Fin.prod_univ_succ]
      rw [← (Fin.consEquiv (fun _ : Fin (k + 1) ↦ Bool)).sum_comp]
      rw [Fintype.sum_prod_type]
      have hcons (p : Bool) (e : BitVec k) :
          (Fin.consEquiv (fun _ : Fin (k + 1) ↦ Bool)) (p, e) =
            Fin.cons p e := rfl
      simp_rw [hcons, tupleSubsetSum_cons]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
      rw [show (∑ p : Bool, ∑ e : BitVec k,
          ψ ((if p then a 0 else 0) + tupleSubsetSum (Fin.tail a) e)) =
        (∑ e : BitVec k, ψ (tupleSubsetSum (Fin.tail a) e)) +
          ψ (a 0) *
            (∑ e : BitVec k, ψ (tupleSubsetSum (Fin.tail a) e)) by
        simp [AddChar.map_add_eq_mul, Finset.mul_sum]
        ac_rfl]
      rw [← ih (Fin.tail a)]
      simp only [Fin.tail]
      ring

/-- Fourier inversion for the tuple representation function. -/
lemma tupleRepCount_fourier {k : ℕ} (a : Fin k → G) (g : G) :
    (tupleRepCount a g : ℂ) =
      (1 / (Fintype.card G : ℂ)) *
        ∑ ψ : Dual G,
          ψ (-g) * ∏ i, (1 + ψ (a i)) := by
  classical
  have hN0 : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp_rw [prod_one_add_single_character_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner (e : BitVec k) :
      ∑ ψ : Dual G, ψ (-g) * ψ (tupleSubsetSum a e) =
        complexIndicator (tupleSubsetSum a e = g)
          (Fintype.card G : ℂ) := by
    have heval (ψ : Dual G) :
        ψ (-g) * ψ (tupleSubsetSum a e) =
          ψ (tupleSubsetSum a e - g) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      abel
    simp_rw [heval]
    rw [sum_character_apply]
    unfold complexIndicator
    by_cases h : tupleSubsetSum a e = g
    · simp [h]
    · simp [h, sub_ne_zero.mpr h]
  have hsum :
      (∑ e : BitVec k, ∑ ψ : Dual G,
        ψ (-g) * ψ (tupleSubsetSum a e)) =
      ∑ e : BitVec k,
        complexIndicator (tupleSubsetSum a e = g)
          (Fintype.card G : ℂ) := by
    apply Finset.sum_congr rfl
    intro e _
    exact hinner e
  simp_rw [← Finset.mul_sum]
  rw [hsum]
  rw [tupleRepCount_eq_sum_indicator]
  unfold complexIndicator natIndicator
  field_simp
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  split <;> simp

lemma sum_neg_character_product {m : ℕ} (χ : Fin m → Dual G) :
    ∑ g : G, ∏ i, χ i (-g) =
      complexIndicator ((∑ i, χ i) = 0) (Fintype.card G : ℂ) := by
  classical
  calc
    (∑ g : G, ∏ i, χ i (-g)) = ∑ g : G, ∏ i, χ i g := by
      exact Equiv.sum_comp (Equiv.neg G) (fun g : G ↦ ∏ i, χ i g)
    _ = _ := sum_character_product_at χ

lemma sum_prod_one_add_characters {m : ℕ} (χ : Fin m → Dual G) :
    ∑ a : G, ∏ i, (1 + χ i a) =
      (Fintype.card G : ℂ) * characterRelationCount χ := by
  classical
  simp_rw [prod_one_add_character_eq_sum]
  rw [Finset.sum_comm]
  have hchar (e : BitVec m) :
      ∑ a : G, (tupleSubsetSum χ e) a =
        complexIndicator (tupleSubsetSum χ e = 0)
          (Fintype.card G : ℂ) := by
    unfold complexIndicator
    simpa using AddChar.sum_eq_ite (tupleSubsetSum χ e)
  simp_rw [hchar]
  unfold complexIndicator characterRelationCount characterRelations
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  split <;> simp

/-- Summing the character product over every `q`-tuple factors coordinate by
coordinate. -/
lemma sum_tuple_prod_one_add_characters {q m : ℕ}
    (χ : Fin m → Dual G) :
    ∑ a : Fin q → G, ∏ j, ∏ i, (1 + χ i (a j)) =
      ((Fintype.card G : ℂ) * characterRelationCount χ) ^ q := by
  classical
  rw [← Fintype.sum_pow (fun x : G ↦ ∏ i, (1 + χ i x)) q]
  rw [sum_prod_one_add_characters]

lemma tupleRepCount_pow_fourier {q m : ℕ} (a : Fin q → G) (g : G) :
    (tupleRepCount a g : ℂ) ^ m =
      (1 / (Fintype.card G : ℂ)) ^ m *
        ∑ χ : Fin m → Dual G,
          (∏ i, χ i (-g)) *
            ∏ j, ∏ i, (1 + χ i (a j)) := by
  classical
  rw [tupleRepCount_fourier, mul_pow, Fintype.sum_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]

/-- Exact Fourier expansion of the total `m`-th moment, before normalizing
the finite tuple and group averages. -/
lemma sum_sum_tupleRepCount_pow (q m : ℕ) :
    ∑ a : Fin q → G, ∑ g : G, (tupleRepCount a g : ℂ) ^ m =
      (1 / (Fintype.card G : ℂ)) ^ m *
        ∑ χ : Fin m → Dual G,
          complexIndicator ((∑ i, χ i) = 0) (Fintype.card G : ℂ) *
            (((Fintype.card G : ℂ) * characterRelationCount χ) ^ q) := by
  classical
  simp_rw [tupleRepCount_pow_fourier]
  simp_rw [← Finset.mul_sum]
  change (1 / (Fintype.card G : ℂ)) ^ m *
      (∑ a : Fin q → G, ∑ g : G, ∑ χ : Fin m → Dual G,
        (∏ i, χ i (-g)) * ∏ j, ∏ i, (1 + χ i (a j))) = _
  congr 1
  have hreorder :
      (∑ a : Fin q → G, ∑ g : G, ∑ χ : Fin m → Dual G,
        (∏ i, χ i (-g)) * ∏ j, ∏ i, (1 + χ i (a j))) =
      ∑ χ : Fin m → Dual G, ∑ g : G, ∑ a : Fin q → G,
        (∏ i, χ i (-g)) * ∏ j, ∏ i, (1 + χ i (a j)) := by
    calc
      _ = ∑ g : G, ∑ a : Fin q → G, ∑ χ : Fin m → Dual G,
          (∏ i, χ i (-g)) * ∏ j, ∏ i, (1 + χ i (a j)) := by
        rw [Finset.sum_comm]
      _ = ∑ g : G, ∑ χ : Fin m → Dual G, ∑ a : Fin q → G,
          (∏ i, χ i (-g)) * ∏ j, ∏ i, (1 + χ i (a j)) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  rw [hreorder]
  apply Finset.sum_congr rfl
  intro χ _
  rw [show (∑ g : G, ∑ a : Fin q → G,
      (∏ i, χ i (-g)) * ∏ j, ∏ i, (1 + χ i (a j))) =
    (∑ g : G, ∏ i, χ i (-g)) *
      (∑ a : Fin q → G, ∏ j, ∏ i, (1 + χ i (a j))) by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]]
  rw [sum_neg_character_product]
  rw [sum_tuple_prod_one_add_characters]

/-- The relation-count sum which controls the critical moment. -/
lemma sum_characterRelationCount_pow_le (m : ℕ) :
    ∑ χ : Fin m → Dual G,
        characterRelationCount χ ^ Nat.log 2 (Fintype.card G) ≤
      Fintype.card G ^ m * 2 ^ (2 ^ m) := by
  classical
  let allRelations : Finset (Finset (BitVec m)) := Finset.univ.powerset
  have hmaps : ∀ χ ∈ (Finset.univ : Finset (Fin m → Dual G)),
      characterRelations χ ∈ allRelations := by
    intro χ _
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun χ : Fin m → Dual G ↦
      characterRelationCount χ ^ Nat.log 2 (Fintype.card G))]
  calc
    (∑ R ∈ allRelations,
        ∑ χ ∈ (Finset.univ.filter fun χ : Fin m → Dual G ↦
          characterRelations χ = R),
            characterRelationCount χ ^ Nat.log 2 (Fintype.card G)) ≤
      ∑ _R ∈ allRelations, Fintype.card G ^ m := by
        apply Finset.sum_le_sum
        intro R hR
        have hinner :
            (∑ χ ∈ (Finset.univ.filter fun χ : Fin m → Dual G ↦
              characterRelations χ = R),
                characterRelationCount χ ^ Nat.log 2 (Fintype.card G)) =
              (Finset.univ.filter fun χ : Fin m → Dual G ↦
                characterRelations χ = R).card *
                  R.card ^ Nat.log 2 (Fintype.card G) := by
          apply Finset.sum_const_nat
          intro χ hχ
          rw [characterRelationCount]
          exact congrArg
            (fun n : ℕ ↦ n ^ Nat.log 2 (Fintype.card G))
            (congrArg Finset.card (Finset.mem_filter.mp hχ).2)
        rw [hinner]
        by_cases hlarge : 2 ≤ R.card
        · have hfiber :
              (Finset.univ.filter fun χ : Fin m → Dual G ↦
                characterRelations χ = R).card ≤
                (relationSolutions (K := Dual G) R).card := by
            apply Finset.card_le_card
            intro χ hχ
            rw [Finset.mem_filter] at hχ
            unfold relationSolutions
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            intro e heR
            have heRel : e ∈ characterRelations χ := by
              rw [hχ.2]
              exact heR
            exact (Finset.mem_filter.mp heRel).2
          have hfiber' := hfiber.trans
            (card_relationSolutions_le (K := Dual G) R hlarge)
          have hdle : Nat.clog 2 R.card ≤ m :=
            Nat.clog_le_of_le_pow <| by
              calc
                R.card ≤ Fintype.card (BitVec m) := by
                  simpa using Finset.card_le_univ R
                _ = 2 ^ m := card_bitVec m
          have hrelpow :
              R.card ^ Nat.log 2 (Fintype.card G) ≤
                Fintype.card G ^ Nat.clog 2 R.card := by
            calc
              R.card ^ Nat.log 2 (Fintype.card G) ≤
                  (2 ^ Nat.clog 2 R.card) ^
                    Nat.log 2 (Fintype.card G) :=
                Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _
              _ = (2 ^ Nat.log 2 (Fintype.card G)) ^
                    Nat.clog 2 R.card := by
                rw [← pow_mul, ← pow_mul]
                exact congrArg (fun z : ℕ ↦ 2 ^ z) (Nat.mul_comm _ _)
              _ ≤ Fintype.card G ^ Nat.clog 2 R.card :=
                Nat.pow_le_pow_left
                  (Nat.pow_log_le_self 2 Fintype.card_ne_zero) _
          calc
            _ ≤ Fintype.card (Dual G) ^ (m - Nat.clog 2 R.card) *
                R.card ^ Nat.log 2 (Fintype.card G) :=
              Nat.mul_le_mul_right _ hfiber'
            _ ≤ Fintype.card G ^ (m - Nat.clog 2 R.card) *
                Fintype.card G ^ Nat.clog 2 R.card := by
              rw [AddChar.card_eq]
              exact Nat.mul_le_mul_left _ hrelpow
            _ = Fintype.card G ^ m := by
              rw [← pow_add]
              congr 1
              omega
        · have hsmall : R.card ≤ 1 := by omega
          have hpowle :
              R.card ^ Nat.log 2 (Fintype.card G) ≤ 1 := by
            exact (Nat.pow_le_pow_left hsmall _).trans (by simp)
          calc
            _ ≤ Fintype.card (Fin m → Dual G) * 1 := by
              apply Nat.mul_le_mul
              · exact Finset.card_le_univ _
              · exact hpowle
            _ = Fintype.card G ^ m := by
              simp [Fintype.card_fun, AddChar.card_eq]
    _ = allRelations.card * Fintype.card G ^ m := by
      simp [Finset.sum_const_nat]
    _ = Fintype.card G ^ m * 2 ^ (2 ^ m) := by
      simp [allRelations, card_bitVec]
      ring

/-- The character moment identity is real-valued; this is the form used by
the finite Markov estimate below. -/
lemma sum_sum_tupleRepCount_pow_real (q m : ℕ) :
    ∑ a : Fin q → G, ∑ g : G, (tupleRepCount a g : ℝ) ^ m =
      (1 / (Fintype.card G : ℝ)) ^ m *
        ∑ χ : Fin m → Dual G,
          (if (∑ i, χ i) = 0 then (Fintype.card G : ℝ) else 0) *
            (((Fintype.card G : ℝ) * characterRelationCount χ) ^ q) := by
  apply Complex.ofReal_injective
  push_cast
  rw [sum_sum_tupleRepCount_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  by_cases hχ : (∑ i, χ i) = 0 <;> simp [complexIndicator, hχ]

/-- After averaging over the tuple and over the target group element, the
`m`-th moment is bounded by the unconditioned character-relation sum. -/
lemma normalized_tuple_moment_le (q m : ℕ) :
    (∑ a : Fin q → G, ∑ g : G, (tupleRepCount a g : ℝ) ^ m) /
        ((Fintype.card G : ℝ) ^ q * Fintype.card G) ≤
      (∑ χ : Fin m → Dual G,
          (characterRelationCount χ : ℝ) ^ q) /
        (Fintype.card G : ℝ) ^ m := by
  classical
  let N : ℝ := Fintype.card G
  have hN : 0 < N := by positivity
  have hsum :
      (∑ χ : Fin m → Dual G,
          (if (∑ i, χ i) = 0 then N else 0) *
            ((N * characterRelationCount χ) ^ q)) ≤
        N ^ q * N *
          ∑ χ : Fin m → Dual G,
            (characterRelationCount χ : ℝ) ^ q := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ _
    by_cases hχ : (∑ i, χ i) = 0
    · simp only [hχ, if_true]
      push_cast
      rw [mul_pow]
      ring_nf
      exact le_rfl
    · simp only [hχ, if_false, zero_mul]
      positivity
  rw [sum_sum_tupleRepCount_pow_real]
  calc
    (1 / N) ^ m *
          (∑ χ : Fin m → Dual G,
            (if (∑ i, χ i) = 0 then N else 0) *
              ((N * characterRelationCount χ) ^ q)) /
        (N ^ q * N) ≤
      (1 / N) ^ m *
          (N ^ q * N *
            ∑ χ : Fin m → Dual G,
              (characterRelationCount χ : ℝ) ^ q) /
        (N ^ q * N) := by
      gcongr
    _ = (∑ χ : Fin m → Dual G,
          (characterRelationCount χ : ℝ) ^ q) / N ^ m := by
      rw [one_div, inv_pow]
      field_simp [hN.ne']

/-- Erdős--Hall's critical high-moment estimate at
`q = floor(log₂ |G|)`. -/
theorem critical_tuple_moment_le (m : ℕ) :
    (∑ a : Fin (Nat.log 2 (Fintype.card G)) → G,
        ∑ g : G, (tupleRepCount a g : ℝ) ^ m) /
        ((Fintype.card G : ℝ) ^ Nat.log 2 (Fintype.card G) *
          Fintype.card G) ≤
      (2 : ℝ) ^ (2 ^ m) := by
  calc
    _ ≤ (∑ χ : Fin m → Dual G,
          (characterRelationCount χ : ℝ) ^
            Nat.log 2 (Fintype.card G)) /
        (Fintype.card G : ℝ) ^ m :=
      normalized_tuple_moment_le (G := G) _ _
    _ ≤ (2 : ℝ) ^ (2 ^ m) := by
      have hnat := sum_characterRelationCount_pow_le (G := G) m
      have hreal :
          (∑ χ : Fin m → Dual G,
              (characterRelationCount χ : ℝ) ^
                Nat.log 2 (Fintype.card G)) ≤
            (Fintype.card G : ℝ) ^ m * (2 : ℝ) ^ (2 ^ m) := by
        exact_mod_cast hnat
      rw [div_le_iff₀ (by positivity :
        0 < (Fintype.card G : ℝ) ^ m)]
      simpa [mul_comm] using hreal

end CharacterMoment

section FiniteProbabilityBounds

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The high-moment estimate and Markov's inequality control the largest
representation count in the critical prefix. -/
theorem prefix_failure_probability_le (m t : ℕ) :
    uniformProbability
        (fun a : Fin (Nat.log 2 (Fintype.card G)) → G ↦
          ∃ g : G, 2 ^ t < tupleRepCount a g) ≤
      (Fintype.card G : ℝ) * (2 : ℝ) ^ (2 ^ m) /
        (2 : ℝ) ^ (t * m) := by
  classical
  let q := Nat.log 2 (Fintype.card G)
  let X : (Fin q → G) → ℝ := fun a ↦
    ∑ g : G, (tupleRepCount a g : ℝ) ^ m
  have hmono : ∀ a : Fin q → G,
      (∃ g : G, 2 ^ t < tupleRepCount a g) →
        (2 : ℝ) ^ (t * m) ≤ X a := by
    intro a ha
    obtain ⟨g, hg⟩ := ha
    rw [pow_mul]
    have hterm : ((2 : ℝ) ^ t) ^ m ≤
        (tupleRepCount a g : ℝ) ^ m := by
      gcongr
      exact_mod_cast hg.le
    have hsingle : (tupleRepCount a g : ℝ) ^ m ≤
        ∑ x : G, (tupleRepCount a x : ℝ) ^ m :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun x : G ↦ (tupleRepCount a x : ℝ) ^ m)
        (fun x _ ↦ by positivity) (Finset.mem_univ g)
    exact hterm.trans hsingle
  have hmarkov := Erdos807.FiniteUniform.probability_le_expectation_div
    (X := X) (fun a ↦ Finset.sum_nonneg fun g _ ↦ by positivity)
    (show 0 < (2 : ℝ) ^ (t * m) by positivity)
  have hprob :
      uniformProbability
          (fun a : Fin q → G ↦ ∃ g : G, 2 ^ t < tupleRepCount a g) ≤
        Erdos807.FiniteUniform.expectation X /
          (2 : ℝ) ^ (t * m) := by
    calc
      _ ≤ Erdos807.FiniteUniform.probability
          (fun a : Fin q → G ↦ (2 : ℝ) ^ (t * m) ≤ X a) :=
        Erdos807.FiniteUniform.probability_mono hmono
      _ ≤ _ := hmarkov
  refine hprob.trans ?_
  have hmoment := critical_tuple_moment_le (G := G) m
  have hN : 0 < (Fintype.card G : ℝ) := by positivity
  have hq : 0 < (Fintype.card G : ℝ) ^ q := by positivity
  have hEX : Erdos807.FiniteUniform.expectation X ≤
      (Fintype.card G : ℝ) * (2 : ℝ) ^ (2 ^ m) := by
    rw [Erdos807.FiniteUniform.expectation_eq_sum_div]
    rw [show Fintype.card (Fin q → G) = Fintype.card G ^ q by simp]
    push_cast
    simp only [X]
    change (∑ a : Fin q → G,
        ∑ g : G, (tupleRepCount a g : ℝ) ^ m) /
          (Fintype.card G : ℝ) ^ q ≤ _
    change (∑ a : Fin q → G,
        ∑ g : G, (tupleRepCount a g : ℝ) ^ m) /
          ((Fintype.card G : ℝ) ^ q * Fintype.card G) ≤ _ at hmoment
    rw [div_le_iff₀ hq]
    rw [div_le_iff₀ (mul_pos hq hN)] at hmoment
    nlinarith
  exact div_le_div_of_nonneg_right hEX (by positivity)

/-- The mean value of the representation function of a `k`-tuple. -/
noncomputable def tupleMean (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k / Fintype.card G

/-- Targets at which a tuple is not within relative error `η` of its
mean. -/
noncomputable def exceptionalTargets {k : ℕ} (η : ℝ) (a : Fin k → G) :
    Finset G := by
  classical
  exact Finset.univ.filter fun g ↦
    η * tupleMean (G := G) k <
      |(tupleRepCount a g : ℝ) - tupleMean (G := G) k|

lemma not_mem_exceptionalTargets {k : ℕ} {η : ℝ} {a : Fin k → G}
    {g : G} (hg : g ∉ exceptionalTargets η a) :
    |(tupleRepCount a g : ℝ) - tupleMean (G := G) k| ≤
      η * tupleMean (G := G) k := by
  classical
  simpa [exceptionalTargets] using hg

/-- Every exceptional target contributes at least the square of the
prescribed deviation to the dispersion. -/
lemma exceptionalTargets_card_mul_sq_le_dispersion {k : ℕ} (η : ℝ)
    (a : Fin k → G) (hη : 0 ≤ η) :
    (exceptionalTargets η a).card *
        (η * tupleMean (G := G) k) ^ 2 ≤
      tupleDispersion a := by
  classical
  unfold tupleDispersion
  calc
    ((exceptionalTargets η a).card : ℝ) *
          (η * tupleMean (G := G) k) ^ 2 =
        ∑ _g ∈ exceptionalTargets η a,
          (η * tupleMean (G := G) k) ^ 2 := by simp
    _ ≤ ∑ g ∈ exceptionalTargets η a,
          ((tupleRepCount a g : ℝ) - tupleMean (G := G) k) ^ 2 := by
      apply Finset.sum_le_sum
      intro g hg
      have hg' := (Finset.mem_filter.mp hg).2
      have hmean : 0 ≤ tupleMean (G := G) k := by
        unfold tupleMean
        positivity
      have habs :
          |(tupleRepCount a g : ℝ) - tupleMean (G := G) k| ^ 2 =
            ((tupleRepCount a g : ℝ) - tupleMean (G := G) k) ^ 2 :=
        sq_abs _
      nlinarith [mul_nonneg hη hmean]
    _ ≤ ∑ g : G,
          ((tupleRepCount a g : ℝ) - tupleMean (G := G) k) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro g _ _
      positivity

/-- Markov's inequality for the size of the first exceptional set, expressed
with an arbitrary positive real threshold. -/
theorem exceptionalTargets_probability_le {k : ℕ} {η A : ℝ}
    (hη : 0 < η) (hA : 0 < A) :
    uniformProbability
        (fun a : Fin k → G ↦ A ≤ (exceptionalTargets η a).card) ≤
      ((2 : ℝ) ^ k * (1 - 1 / Fintype.card G)) /
        (A * (η * tupleMean (G := G) k) ^ 2) := by
  classical
  have hmean : 0 < tupleMean (G := G) k := by
    unfold tupleMean
    positivity
  have hthreshold : 0 < A * (η * tupleMean (G := G) k) ^ 2 := by
    positivity
  calc
    uniformProbability
        (fun a : Fin k → G ↦ A ≤ (exceptionalTargets η a).card) ≤
      Erdos807.FiniteUniform.probability
        (fun a : Fin k → G ↦
          A * (η * tupleMean (G := G) k) ^ 2 ≤ tupleDispersion a) := by
        apply Erdos807.FiniteUniform.probability_mono
        intro a ha
        calc
          A * (η * tupleMean (G := G) k) ^ 2 ≤
              (exceptionalTargets η a).card *
                (η * tupleMean (G := G) k) ^ 2 := by gcongr
          _ ≤ tupleDispersion a :=
            exceptionalTargets_card_mul_sq_le_dispersion η a hη.le
    _ ≤ Erdos807.FiniteUniform.expectation
          (fun a : Fin k → G ↦ tupleDispersion a) /
        (A * (η * tupleMean (G := G) k) ^ 2) := by
      apply Erdos807.FiniteUniform.probability_le_expectation_div
      · intro a
        unfold tupleDispersion
        positivity
      · exact hthreshold
    _ = _ := by rw [expectation_tupleDispersion]

lemma tupleMean_add (k s : ℕ) :
    tupleMean (G := G) (k + s) =
      (2 : ℝ) ^ s * tupleMean (G := G) k := by
  unfold tupleMean
  rw [pow_add]
  ring

/-- A finite sum in which at most one summand is exceptional. -/
lemma sum_bounds_of_at_most_one_exception {I : Type*} [Fintype I]
    (P : I → Prop) [DecidablePred P] (x : I → ℝ) (L U M : ℝ)
    (hL : 0 ≤ L) (hU : 0 ≤ U) (hM : 0 ≤ M)
    (hgood : ∀ i, ¬ P i → L ≤ x i ∧ x i ≤ U)
    (hbad : ∀ i, P i → 0 ≤ x i ∧ x i ≤ M)
    (hone : (Finset.univ.filter P).card ≤ 1) :
    ((Fintype.card I : ℝ) - 1) * L ≤ ∑ i, x i ∧
      ∑ i, x i ≤ (Fintype.card I : ℝ) * U + M := by
  classical
  let T : Finset I := Finset.univ.filter P
  have hsplit :
      (∑ i ∈ T, x i) + ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), x i =
        ∑ i, x i := by
    simpa [T] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ P x)
  have hTcard : (T.card : ℝ) ≤ 1 := by exact_mod_cast hone
  have hTc : ((Finset.univ.filter fun i : I ↦ ¬ P i).card : ℝ) =
      (Fintype.card I : ℝ) - (T.card : ℝ) := by
    have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset I)) P
    have hcard' : (T.card : ℝ) +
        ((Finset.univ.filter fun i : I ↦ ¬ P i).card : ℝ) =
          Fintype.card I := by
      exact_mod_cast hcard
    linarith
  constructor
  · rw [← hsplit]
    have hbadnonneg : 0 ≤ ∑ i ∈ T, x i := by
      apply Finset.sum_nonneg
      intro i hi
      exact (hbad i (Finset.mem_filter.mp hi).2).1
    have hgoodlower :
        ((Finset.univ.filter fun i : I ↦ ¬ P i).card : ℝ) * L ≤
          ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), x i := by
      rw [Finset.card_eq_sum_ones]
      push_cast
      simp_rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      simpa using (hgood i (Finset.mem_filter.mp hi).2).1
    calc
      ((Fintype.card I : ℝ) - 1) * L ≤
          ((Fintype.card I : ℝ) - T.card) * L := by
        gcongr
      _ = ((Finset.univ.filter fun i : I ↦ ¬ P i).card : ℝ) * L := by
        rw [hTc]
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), x i :=
        hgoodlower
      _ ≤ (∑ i ∈ T, x i) +
          ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), x i := by
        linarith
  · rw [← hsplit]
    have hbadupper : ∑ i ∈ T, x i ≤ (T.card : ℝ) * M := by
      rw [Finset.card_eq_sum_ones]
      push_cast
      simp_rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      simpa using (hbad i (Finset.mem_filter.mp hi).2).2
    have hgoodupper :
        ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), x i ≤
          ((Finset.univ.filter fun i : I ↦ ¬ P i).card : ℝ) * U := by
      rw [Finset.card_eq_sum_ones]
      push_cast
      simp_rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      simpa using (hgood i (Finset.mem_filter.mp hi).2).2
    calc
      (∑ i ∈ T, x i) +
          ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), x i ≤
        (T.card : ℝ) * M +
          ((Finset.univ.filter fun i : I ↦ ¬ P i).card : ℝ) * U :=
        add_le_add hbadupper hgoodupper
      _ ≤ 1 * M + (Fintype.card I : ℝ) * U := by
        gcongr
        have hc := Finset.card_le_univ
          (s := Finset.univ.filter fun i : I ↦ ¬ P i)
        exact_mod_cast hc
      _ = (Fintype.card I : ℝ) * U + M := by ring

/-- Deterministic Erdős--Hall smoothing: if no translate contains two
exceptional block sums, adjoining the block increases the relative error by
at most `δ`. -/
theorem smooth_append_at_of_one_hit {k s : ℕ} (a : Fin k → G)
    (b : Fin s → G) (g : G)
    {η δ M : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hδ : 0 ≤ δ)
    (hsmall : 1 ≤ δ * (2 : ℝ) ^ s)
    (hmax : ∀ g : G, (tupleRepCount a g : ℝ) ≤ M)
    (hM : M ≤ δ * (2 : ℝ) ^ s * tupleMean (G := G) k)
    (hone : blockHitCount (exceptionalTargets η a) b g ≤ 1) :
      |(tupleRepCount (Fin.append a b) g : ℝ) -
          tupleMean (G := G) (k + s)| ≤
        (η + δ) * tupleMean (G := G) (k + s) := by
  classical
  let μ := tupleMean (G := G) k
  let H := exceptionalTargets η a
  let P : BitVec s → Prop := fun e ↦ g - tupleSubsetSum b e ∈ H
  let x : BitVec s → ℝ := fun e ↦
    tupleRepCount a (g - tupleSubsetSum b e)
  have hμ : 0 < μ := by unfold μ tupleMean; positivity
  have hgood : ∀ e, ¬ P e →
      (1 - η) * μ ≤ x e ∧ x e ≤ (1 + η) * μ := by
    intro e he
    have he' : g - tupleSubsetSum b e ∉ exceptionalTargets η a := he
    have habs := not_mem_exceptionalTargets he'
    rw [abs_le] at habs
    constructor <;> dsimp [x, μ] at * <;> linarith
  have hbad : ∀ e, P e → 0 ≤ x e ∧ x e ≤ M := by
    intro e _
    exact ⟨by dsimp [x]; positivity, hmax _⟩
  have hcard : (Finset.univ.filter P).card ≤ 1 := by
    simpa [P, H, blockHitCount] using hone
  have hbds := sum_bounds_of_at_most_one_exception P x
    ((1 - η) * μ) ((1 + η) * μ) M
    (mul_nonneg (sub_nonneg.mpr hη₁) hμ.le)
    (mul_nonneg (by linarith) hμ.le)
    ((show 0 ≤ (tupleRepCount a 0 : ℝ) by positivity).trans (hmax 0))
    hgood hbad hcard
  have hrep : (tupleRepCount (Fin.append a b) g : ℝ) = ∑ e, x e := by
    rw [tupleRepCount_append]
    push_cast
    rfl
  have hcardBit : (Fintype.card (BitVec s) : ℝ) = (2 : ℝ) ^ s := by
    exact_mod_cast card_bitVec s
  rw [hrep, tupleMean_add, abs_le]
  rw [hcardBit] at hbds
  constructor
  · calc
      -((η + δ) * ((2 : ℝ) ^ s * μ)) ≤
          (((2 : ℝ) ^ s - 1) * ((1 - η) * μ)) -
            (2 : ℝ) ^ s * μ := by
        nlinarith [hsmall, hμ.le]
      _ ≤ (∑ e, x e) - (2 : ℝ) ^ s * μ := by linarith [hbds.1]
  · calc
      (∑ e, x e) - (2 : ℝ) ^ s * μ ≤
          ((2 : ℝ) ^ s * ((1 + η) * μ) + M) -
            (2 : ℝ) ^ s * μ := by linarith [hbds.2]
      _ ≤ (η + δ) * ((2 : ℝ) ^ s * μ) := by
        nlinarith [hM]

theorem smooth_append_of_one_hit {k s : ℕ} (a : Fin k → G) (b : Fin s → G)
    {η δ M : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hδ : 0 ≤ δ)
    (hsmall : 1 ≤ δ * (2 : ℝ) ^ s)
    (hmax : ∀ g : G, (tupleRepCount a g : ℝ) ≤ M)
    (hM : M ≤ δ * (2 : ℝ) ^ s * tupleMean (G := G) k)
    (hone : ∀ g : G,
      blockHitCount (exceptionalTargets η a) b g ≤ 1) :
    ∀ g : G,
      |(tupleRepCount (Fin.append a b) g : ℝ) -
          tupleMean (G := G) (k + s)| ≤
        (η + δ) * tupleMean (G := G) (k + s) := by
  intro g
  exact smooth_append_at_of_one_hit a b g hη₀ hη₁ hδ hsmall hmax hM
    (hone g)

lemma card_le_blockCollisionMass_of_two_hits {s : ℕ} (H T : Finset G)
    (b : Fin s → G)
    (hT : ∀ g ∈ T, 2 ≤ blockHitCount H b g) :
    T.card ≤ blockCollisionMass H b := by
  classical
  unfold blockCollisionMass
  rw [Finset.card_eq_sum_ones]
  calc
    ∑ _g ∈ T, 1 ≤ ∑ g ∈ T, blockCollisionAt H b g := by
      apply Finset.sum_le_sum
      intro g hg
      exact blockCollisionAt_ge_one_of_two_hits H b g (hT g hg)
    _ ≤ ∑ g : G, blockCollisionAt H b g := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      intro g _ _
      exact Nat.zero_le _

/-- The next exceptional set is pointwise supported on collision translates,
and hence its cardinality is bounded by the collision mass. -/
theorem exceptionalTargets_append_card_le_collision {k s : ℕ}
    (a : Fin k → G) (b : Fin s → G) {η δ M : ℝ}
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hδ : 0 ≤ δ)
    (hsmall : 1 ≤ δ * (2 : ℝ) ^ s)
    (hmax : ∀ g : G, (tupleRepCount a g : ℝ) ≤ M)
    (hM : M ≤ δ * (2 : ℝ) ^ s * tupleMean (G := G) k) :
    (exceptionalTargets (η + δ) (Fin.append a b)).card ≤
      blockCollisionMass (exceptionalTargets η a) b := by
  classical
  apply card_le_blockCollisionMass_of_two_hits
  intro g hg
  by_contra htwo
  have hone : blockHitCount (exceptionalTargets η a) b g ≤ 1 := by omega
  have hsmooth := smooth_append_at_of_one_hit a b g hη₀ hη₁ hδ
    hsmall hmax hM hone
  exact (not_lt_of_ge hsmooth) (Finset.mem_filter.mp hg).2

/-- Collision mass has the expected first-moment tail bound under a uniform
random block. -/
theorem blockCollision_probability_le {s : ℕ} (hs : 1 ≤ s)
    (H : Finset G) {A : ℝ} (hA : 0 < A) :
    uniformProbability
        (fun b : Fin s → G ↦ A ≤ blockCollisionMass H b) ≤
      ((2 : ℝ) ^ s * ((2 : ℝ) ^ s - 1) * H.card ^ 2) /
        ((Fintype.card G : ℝ) * A) := by
  classical
  have hmarkov := Erdos807.FiniteUniform.probability_nat_cast_ge_le_expectation_div
    (X := fun b : Fin s → G ↦ blockCollisionMass H b) hA
  calc
    uniformProbability
        (fun b : Fin s → G ↦ A ≤ blockCollisionMass H b) ≤
      Erdos807.FiniteUniform.natExpectation
          (fun b : Fin s → G ↦ blockCollisionMass H b) / A := hmarkov
    _ = _ := by
      rw [Erdos807.FiniteUniform.natExpectation_eq_sum_div]
      have hsum := sum_blockCollisionMass (G := G) H s
      have hsum' :
          ∑ b : Fin s → G, (blockCollisionMass H b : ℝ) =
            (2 : ℝ) ^ s * ((2 : ℝ) ^ s - 1) * H.card ^ 2 *
              (Fintype.card G : ℝ) ^ (s - 1) := by
        calc
          _ = ((∑ b : Fin s → G, blockCollisionMass H b : ℕ) : ℝ) := by
            push_cast
            rfl
          _ = ((2 ^ s * (2 ^ s - 1) * H.card ^ 2 *
              Fintype.card G ^ (s - 1) : ℕ) : ℝ) := by rw [hsum]
          _ = _ := by
            push_cast
            rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))]
            norm_num
      rw [hsum']
      simp only [Fintype.card_fun, Fintype.card_fin]
      push_cast
      have hN : (Fintype.card G : ℝ) ≠ 0 := by positivity
      have hpow : (Fintype.card G : ℝ) ^ s =
          (Fintype.card G : ℝ) ^ (s - 1) * Fintype.card G := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
        simp [pow_succ]
      rw [hpow]
      field_simp

section UniformProducts

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

lemma uniformProbability_equiv (e : X ≃ Y) (P : Y → Prop) :
    uniformProbability (fun x : X ↦ P (e x)) = uniformProbability P := by
  classical
  unfold uniformProbability
  rw [Nat.card_congr (e.subtypeEquiv fun _ ↦ Iff.rfl)]
  rw [Fintype.card_congr e]

lemma uniformProbability_prod_fiber (R : X → Y → Prop) :
    uniformProbability (fun z : X × Y ↦ R z.1 z.2) =
      Erdos807.FiniteUniform.expectation
        (fun x : X ↦ uniformProbability (R x)) := by
  classical
  let e : {z : X × Y // R z.1 z.2} ≃
      Σ x : X, {y : Y // R x y} :=
    { toFun := fun z ↦ ⟨z.1.1, z.1.2, z.2⟩
      invFun := fun z ↦ ⟨(z.1, z.2.1), z.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hcard : Nat.card {z : X × Y // R z.1 z.2} =
      ∑ x : X, Nat.card {y : Y // R x y} := by
    rw [Nat.card_congr e, Nat.card_sigma]
  unfold uniformProbability Erdos807.FiniteUniform.expectation
  rw [hcard, Fintype.card_prod]
  push_cast
  rw [Finset.sum_div]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [div_div, mul_comm]

/-- A conditional union bound on a finite product space. -/
lemma uniformProbability_prod_failure_le (P : X → Prop) (Q : X → Y → Prop)
    {u : ℝ} (hu : 0 ≤ u)
    (hQ : ∀ x, ¬ P x → uniformProbability (Q x) ≤ u) :
    uniformProbability (fun z : X × Y ↦ P z.1 ∨ Q z.1 z.2) ≤
      uniformProbability P + u := by
  classical
  rw [uniformProbability_prod_fiber
    (R := fun x : X ↦ fun y : Y ↦ P x ∨ Q x y)]
  calc
    Erdos807.FiniteUniform.expectation
        (fun x : X ↦ uniformProbability (fun y ↦ P x ∨ Q x y)) ≤
      Erdos807.FiniteUniform.expectation
        (fun x : X ↦ Erdos807.FiniteUniform.indicator (P x) + u) := by
      apply Erdos807.FiniteUniform.expectation_mono
      intro x
      by_cases hx : P x
      · have hp : uniformProbability (fun y : Y ↦ P x ∨ Q x y) ≤ 1 :=
          Erdos807.FiniteUniform.probability_le_one
            (fun y : Y ↦ P x ∨ Q x y)
        simpa [Erdos807.FiniteUniform.indicator, hx] using hp.trans (by linarith)
      · simpa [Erdos807.FiniteUniform.indicator, hx] using hQ x hx
    _ = uniformProbability P + u := by
      rw [Erdos807.FiniteUniform.expectation_add]
      rw [Erdos807.FiniteUniform.expectation_indicator]
      rw [Erdos807.FiniteUniform.expectation_const]
      rfl

lemma uniformProbability_prod_left (P : X → Prop) :
    uniformProbability (fun z : X × Y ↦ P z.1) = uniformProbability P := by
  rw [uniformProbability_prod_fiber (R := fun x : X ↦ fun _ : Y ↦ P x)]
  have hconst : (fun x : X ↦ uniformProbability (fun _ : Y ↦ P x)) =
      fun x : X ↦ Erdos807.FiniteUniform.indicator (P x) := by
    funext x
    by_cases hx : P x
    · simp [uniformProbability, Erdos807.FiniteUniform.indicator, hx,
        Erdos807.FiniteUniform.card_ne_zero]
    · simp [uniformProbability, Erdos807.FiniteUniform.indicator, hx]
  rw [hconst]
  rw [Erdos807.FiniteUniform.expectation_indicator]
  rfl

lemma uniformProbability_append {k s : ℕ} (P : (Fin (k + s) → G) → Prop) :
    uniformProbability
        (fun z : (Fin k → G) × (Fin s → G) ↦ P (Fin.append z.1 z.2)) =
      uniformProbability P :=
  uniformProbability_equiv (Fin.appendEquiv k s) P

lemma uniformProbability_not (P : X → Prop) :
    uniformProbability (fun x ↦ ¬ P x) = 1 - uniformProbability P := by
  classical
  change Erdos807.FiniteUniform.probability (fun x ↦ ¬ P x) =
    1 - Erdos807.FiniteUniform.probability P
  rw [← Erdos807.FiniteUniform.expectation_indicator,
    ← Erdos807.FiniteUniform.expectation_indicator]
  have hind : (fun x : X ↦ Erdos807.FiniteUniform.indicator (¬ P x)) =
      fun x ↦ 1 - Erdos807.FiniteUniform.indicator (P x) := by
    funext x
    by_cases hx : P x <;> simp [Erdos807.FiniteUniform.indicator, hx]
  rw [hind]
  unfold Erdos807.FiniteUniform.expectation
  rw [Finset.sum_sub_distrib]
  simp [Erdos807.FiniteUniform.card_ne_zero]
  field_simp

end UniformProducts

/-- State propagated by the Erdős--Hall smoothing iteration.  The first
conjunct remembers the critical-prefix maximum; the second controls the
current exceptional set. -/
def HallState (q t e k : ℕ) (η : ℝ) (a : Fin k → G) : Prop :=
  (∀ g : G, (tupleRepCount a g : ℝ) ≤ (2 : ℝ) ^ (k - q + t)) ∧
    (exceptionalTargets η a).card * (2 : ℝ) ^ e ≤ Fintype.card G

lemma tupleRepCount_append_le_of_max {k s B : ℕ} (a : Fin k → G)
    (b : Fin s → G) (hB : ∀ g : G, tupleRepCount a g ≤ B) (g : G) :
    tupleRepCount (Fin.append a b) g ≤ 2 ^ s * B := by
  rw [tupleRepCount_append]
  calc
    ∑ f : BitVec s, tupleRepCount a (g - tupleSubsetSum b f) ≤
        ∑ _f : BitVec s, B := by
      apply Finset.sum_le_sum
      intro f _
      exact hB _
    _ = 2 ^ s * B := by simp [card_bitVec]

lemma hallState_max_append {q t e k s : ℕ} (hqk : q ≤ k) {η : ℝ}
    {a : Fin k → G} (ha : HallState q t e k η a) (b : Fin s → G) :
    ∀ g : G,
      (tupleRepCount (Fin.append a b) g : ℝ) ≤
        (2 : ℝ) ^ ((k + s) - q + t) := by
  intro g
  have hnat := tupleRepCount_append_le_of_max a b
    (B := 2 ^ (k - q + t)) (fun x ↦ by exact_mod_cast ha.1 x) g
  have hreal : (tupleRepCount (Fin.append a b) g : ℝ) ≤
      (2 : ℝ) ^ s * (2 : ℝ) ^ (k - q + t) := by
    exact_mod_cast hnat
  calc
    _ ≤ (2 : ℝ) ^ s * (2 : ℝ) ^ (k - q + t) := hreal
    _ = (2 : ℝ) ^ ((k + s) - q + t) := by
      rw [← pow_add]
      congr 1
      omega

/-- One smoothing block propagates `HallState` unless its collision mass
crosses the next threshold. -/
lemma hallState_append_of_collision_bound {q t e e' k s : ℕ}
    (hqk : q ≤ k) (a : Fin k → G) (b : Fin s → G) {η δ : ℝ}
    (ha : HallState q t e k η a)
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hδ : 0 ≤ δ)
    (hsmall : 1 ≤ δ * (2 : ℝ) ^ s)
    (hscale : (2 : ℝ) ^ (k - q + t) ≤
      δ * (2 : ℝ) ^ s * tupleMean (G := G) k)
    (hcollision : (blockCollisionMass (exceptionalTargets η a) b : ℝ) *
      (2 : ℝ) ^ e' ≤ Fintype.card G) :
    HallState q t e' (k + s) (η + δ) (Fin.append a b) := by
  constructor
  · exact hallState_max_append hqk ha b
  · have hcard := exceptionalTargets_append_card_le_collision a b hη₀
      hη₁ hδ hsmall ha.1 hscale
    have hcard' : ((exceptionalTargets (η + δ) (Fin.append a b)).card : ℝ) ≤
        blockCollisionMass (exceptionalTargets η a) b := by exact_mod_cast hcard
    exact (mul_le_mul_of_nonneg_right hcard' (by positivity)).trans hcollision

/-- Conditional failure probability of one smoothing block. -/
theorem hallState_step_failure_le {q t e e' k s : ℕ}
    (hs : 1 ≤ s) (hqk : q ≤ k) (a : Fin k → G) {η δ : ℝ}
    (ha : HallState q t e k η a)
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hδ : 0 ≤ δ)
    (hsmall : 1 ≤ δ * (2 : ℝ) ^ s)
    (hscale : (2 : ℝ) ^ (k - q + t) ≤
      δ * (2 : ℝ) ^ s * tupleMean (G := G) k) :
    uniformProbability
        (fun b : Fin s → G ↦
          ¬ HallState q t e' (k + s) (η + δ) (Fin.append a b)) ≤
      (2 : ℝ) ^ (2 * s + e') / (2 : ℝ) ^ (2 * e) := by
  classical
  let H := exceptionalTargets η a
  let N : ℝ := Fintype.card G
  let A : ℝ := N / (2 : ℝ) ^ e'
  have hN : 0 < N := by positivity
  have hA : 0 < A := by unfold A; positivity
  have hmono : ∀ b : Fin s → G,
      ¬ HallState q t e' (k + s) (η + δ) (Fin.append a b) →
        A ≤ blockCollisionMass H b := by
    intro b hb
    by_contra hmass
    have hmass' : (blockCollisionMass H b : ℝ) * (2 : ℝ) ^ e' ≤ N := by
      have : (blockCollisionMass H b : ℝ) < A := lt_of_not_ge hmass
      unfold A at this
      rw [lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ e')] at this
      exact this.le
    exact hb (hallState_append_of_collision_bound hqk a b ha hη₀ hη₁ hδ
      hsmall hscale hmass')
  calc
    uniformProbability
        (fun b : Fin s → G ↦
          ¬ HallState q t e' (k + s) (η + δ) (Fin.append a b)) ≤
      uniformProbability (fun b : Fin s → G ↦
        A ≤ blockCollisionMass H b) := by
          apply Erdos807.FiniteUniform.probability_mono
          exact hmono
    _ ≤ ((2 : ℝ) ^ s * ((2 : ℝ) ^ s - 1) * H.card ^ 2) /
        (N * A) := blockCollision_probability_le hs H hA
    _ ≤ (2 : ℝ) ^ (2 * s + e') / (2 : ℝ) ^ (2 * e) := by
      have hH : (H.card : ℝ) * (2 : ℝ) ^ e ≤ N := ha.2
      have hH₀ : 0 ≤ (H.card : ℝ) := by positivity
      have hB : 0 < (2 : ℝ) ^ s := by positivity
      have hC : 0 < (2 : ℝ) ^ e := by positivity
      have hD : 0 < (2 : ℝ) ^ e' := by positivity
      have hHsq : (H.card : ℝ) ^ 2 * ((2 : ℝ) ^ e) ^ 2 ≤ N ^ 2 := by
        have hsquare := (sq_le_sq₀
          (mul_nonneg hH₀ hC.le) hN.le).2 hH
        simpa [mul_pow] using hsquare
      unfold A
      rw [div_le_iff₀ (mul_pos hN (div_pos hN hD))]
      have hrhs :
          (2 : ℝ) ^ (2 * s + e') / (2 : ℝ) ^ (2 * e) *
              (N * (N / (2 : ℝ) ^ e')) =
            ((2 : ℝ) ^ s) ^ 2 * N ^ 2 /
              (((2 : ℝ) ^ e) ^ 2) := by
        rw [pow_add, pow_mul, pow_mul]
        field_simp
        simp only [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [hrhs]
      rw [le_div_iff₀ (sq_pos_of_pos hC)]
      have hBB : (2 : ℝ) ^ s * ((2 : ℝ) ^ s - 1) ≤
          ((2 : ℝ) ^ s) ^ 2 := by nlinarith
      have h₁ := mul_le_mul_of_nonneg_right hBB
        (mul_nonneg (sq_nonneg (H.card : ℝ)) (sq_nonneg ((2 : ℝ) ^ e)))
      have h₂ := mul_le_mul_of_nonneg_left hHsq (sq_nonneg ((2 : ℝ) ^ s))
      calc
        (2 : ℝ) ^ s * ((2 : ℝ) ^ s - 1) * H.card ^ 2 *
            ((2 : ℝ) ^ e) ^ 2 ≤
          ((2 : ℝ) ^ s) ^ 2 *
            (H.card ^ 2 * ((2 : ℝ) ^ e) ^ 2) := by
              nlinarith [h₁]
        _ ≤ ((2 : ℝ) ^ s) ^ 2 * N ^ 2 := h₂

/-- Add one independent block to a probabilistic `HallState` estimate. -/
theorem hallState_failure_append_le {q t e e' k s : ℕ}
    (hs : 1 ≤ s) (hqk : q ≤ k) {η δ p : ℝ}
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hδ : 0 ≤ δ)
    (hsmall : 1 ≤ δ * (2 : ℝ) ^ s)
    (hscale : (2 : ℝ) ^ (k - q + t) ≤
      δ * (2 : ℝ) ^ s * tupleMean (G := G) k)
    (hp : uniformProbability
      (fun a : Fin k → G ↦ ¬ HallState q t e k η a) ≤ p) :
    uniformProbability
        (fun c : Fin (k + s) → G ↦
          ¬ HallState q t e' (k + s) (η + δ) c) ≤
      p + (2 : ℝ) ^ (2 * s + e') / (2 : ℝ) ^ (2 * e) := by
  classical
  let P : (Fin k → G) → Prop := fun a ↦ ¬ HallState q t e k η a
  let Q : (Fin k → G) → (Fin s → G) → Prop := fun a b ↦
    ¬ HallState q t e' (k + s) (η + δ) (Fin.append a b)
  have hQ : ∀ a, ¬ P a →
      uniformProbability (Q a) ≤
        (2 : ℝ) ^ (2 * s + e') / (2 : ℝ) ^ (2 * e) := by
    intro a ha
    exact hallState_step_failure_le hs hqk a (not_not.mp ha) hη₀ hη₁ hδ
      hsmall hscale
  have hprod := uniformProbability_prod_failure_le P Q
    (by positivity : 0 ≤ (2 : ℝ) ^ (2 * s + e') / (2 : ℝ) ^ (2 * e)) hQ
  calc
    uniformProbability
        (fun c : Fin (k + s) → G ↦
          ¬ HallState q t e' (k + s) (η + δ) c) =
      uniformProbability (fun z : (Fin k → G) × (Fin s → G) ↦
        Q z.1 z.2) := by
          exact (uniformProbability_append
            (fun c : Fin (k + s) → G ↦
              ¬ HallState q t e' (k + s) (η + δ) c)).symm
    _ ≤ uniformProbability (fun z : (Fin k → G) × (Fin s → G) ↦
        P z.1 ∨ Q z.1 z.2) := by
          apply Erdos807.FiniteUniform.probability_mono
          intro z hz
          exact Or.inr hz
    _ ≤ uniformProbability P +
        (2 : ℝ) ^ (2 * s + e') / (2 : ℝ) ^ (2 * e) := hprod
    _ ≤ p + (2 : ℝ) ^ (2 * s + e') / (2 : ℝ) ^ (2 * e) := by
      gcongr

lemma critical_prefix_max_after_initial_block (q t : ℕ)
    (a : Fin q → G) (b : Fin (8 * t) → G)
    (ha : ∀ g : G, tupleRepCount a g ≤ 2 ^ t) :
    ∀ g : G,
      (tupleRepCount (Fin.append a b) g : ℝ) ≤
        (2 : ℝ) ^ ((q + 8 * t) - q + t) := by
  intro g
  have h := tupleRepCount_append_le_of_max a b ha g
  have h' : (tupleRepCount (Fin.append a b) g : ℝ) ≤
      (2 : ℝ) ^ (8 * t) * (2 : ℝ) ^ t := by exact_mod_cast h
  calc
    _ ≤ (2 : ℝ) ^ (8 * t) * (2 : ℝ) ^ t := h'
    _ = _ := by
      rw [← pow_add]
      congr 1
      omega

/-- The unconditional dispersion estimate gives the first small exceptional
set after the initial block of length `8t`. -/
theorem first_exception_failure_le (t : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    let q := Nat.log 2 (Fintype.card G)
    uniformProbability
        (fun a : Fin (q + 8 * t) → G ↦
          (Fintype.card G : ℝ) <
            (exceptionalTargets δ a).card * (2 : ℝ) ^ (6 * t)) ≤
      2 / (δ ^ 2 * (2 : ℝ) ^ (2 * t)) := by
  classical
  dsimp only
  let q := Nat.log 2 (Fintype.card G)
  let N : ℝ := Fintype.card G
  let A : ℝ := N / (2 : ℝ) ^ (6 * t)
  have hN : 0 < N := by positivity
  have hA : 0 < A := by unfold A; positivity
  have hmono : ∀ a : Fin (q + 8 * t) → G,
      N < (exceptionalTargets δ a).card * (2 : ℝ) ^ (6 * t) →
        A ≤ (exceptionalTargets δ a).card := by
    intro a ha
    unfold A
    rw [div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (6 * t))]
    exact ha.le
  calc
    uniformProbability
        (fun a : Fin (q + 8 * t) → G ↦
          N < (exceptionalTargets δ a).card * (2 : ℝ) ^ (6 * t)) ≤
      uniformProbability
        (fun a : Fin (q + 8 * t) → G ↦
          A ≤ (exceptionalTargets δ a).card) := by
            apply Erdos807.FiniteUniform.probability_mono
            exact hmono
    _ ≤ ((2 : ℝ) ^ (q + 8 * t) * (1 - 1 / N)) /
        (A * (δ * tupleMean (G := G) (q + 8 * t)) ^ 2) :=
      exceptionalTargets_probability_le hδ hA
    _ ≤ 2 / (δ ^ 2 * (2 : ℝ) ^ (2 * t)) := by
      have hNleNat : Fintype.card G ≤ 2 * 2 ^ q := by
        calc
          Fintype.card G ≤ 2 ^ (q + 1) := by
            apply Nat.le_of_lt
            dsimp [q]
            exact Nat.lt_pow_succ_log_self (by norm_num) _
          _ = 2 * 2 ^ q := by rw [pow_succ]; ring
      have hNle : N ≤ 2 * (2 : ℝ) ^ q := by
        unfold N
        exact_mod_cast hNleNat
      have hone : 1 - 1 / N ≤ 1 := by
        have : 0 ≤ 1 / N := by positivity
        linarith
      have hone₀ : 0 ≤ 1 - 1 / N := by
        rw [sub_nonneg, div_le_one hN]
        unfold N
        exact_mod_cast (show 1 ≤ Fintype.card G from Fintype.card_pos)
      unfold A tupleMean
      have hden : 0 <
          (N / (2 : ℝ) ^ (6 * t)) *
            (δ * ((2 : ℝ) ^ (q + 8 * t) / N)) ^ 2 := by positivity
      rw [div_le_iff₀ hden]
      have hpowq : 0 < (2 : ℝ) ^ q := by positivity
      rw [div_mul_eq_mul_div]
      field_simp
      rw [pow_add, pow_mul, pow_mul, pow_mul]
      have hmul := mul_le_mul_of_nonneg_right hNle
        (show 0 ≤ ((2 : ℝ) ^ 8) ^ t by positivity)
      have hfactor : ((2 : ℝ) ^ 6) ^ t * ((2 : ℝ) ^ 2) ^ t =
          ((2 : ℝ) ^ 8) ^ t := by
        rw [← mul_pow]
        norm_num
      calc
        (N - 1) * ((2 : ℝ) ^ 6) ^ t * ((2 : ℝ) ^ 2) ^ t =
            (N - 1) * (((2 : ℝ) ^ 6) ^ t * ((2 : ℝ) ^ 2) ^ t) := by ring
        _ = (N - 1) * ((2 : ℝ) ^ 8) ^ t := by rw [hfactor]
        _ ≤ N * ((2 : ℝ) ^ 8) ^ t := by
          gcongr
          linarith
        _ ≤ 2 * (2 : ℝ) ^ q * ((2 : ℝ) ^ 8) ^ t := hmul
        _ = (2 : ℝ) ^ q * ((2 : ℝ) ^ 8) ^ t * 2 := by ring

/-- Initial `HallState` failure bound: a critical-prefix moment estimate plus
the first dispersion estimate. -/
theorem initial_hallState_failure_le (m t : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    let q := Nat.log 2 (Fintype.card G)
    uniformProbability
        (fun c : Fin (q + 8 * t) → G ↦
          ¬ HallState q t (6 * t) (q + 8 * t) δ c) ≤
      (Fintype.card G : ℝ) * (2 : ℝ) ^ (2 ^ m) /
          (2 : ℝ) ^ (t * m) +
        2 / (δ ^ 2 * (2 : ℝ) ^ (2 * t)) := by
  classical
  dsimp only
  let q := Nat.log 2 (Fintype.card G)
  let P : (Fin q → G) → Prop := fun a ↦
    ∃ g : G, 2 ^ t < tupleRepCount a g
  let Q : (Fin q → G) → (Fin (8 * t) → G) → Prop := fun a b ↦
    (Fintype.card G : ℝ) <
      (exceptionalTargets δ (Fin.append a b)).card * (2 : ℝ) ^ (6 * t)
  have himp : ∀ z : (Fin q → G) × (Fin (8 * t) → G),
      ¬ HallState q t (6 * t) (q + 8 * t) δ (Fin.append z.1 z.2) →
        P z.1 ∨ Q z.1 z.2 := by
    intro z hz
    by_contra hbad
    rw [not_or] at hbad
    apply hz
    constructor
    · apply critical_prefix_max_after_initial_block
      intro g
      by_contra hg
      exact hbad.1 ⟨g, lt_of_not_ge hg⟩
    · exact le_of_not_gt hbad.2
  calc
    uniformProbability
        (fun c : Fin (q + 8 * t) → G ↦
          ¬ HallState q t (6 * t) (q + 8 * t) δ c) =
      uniformProbability
        (fun z : (Fin q → G) × (Fin (8 * t) → G) ↦
          ¬ HallState q t (6 * t) (q + 8 * t) δ
            (Fin.append z.1 z.2)) := by
      exact (uniformProbability_append
        (fun c : Fin (q + 8 * t) → G ↦
          ¬ HallState q t (6 * t) (q + 8 * t) δ c)).symm
    _ ≤ uniformProbability
        (fun z : (Fin q → G) × (Fin (8 * t) → G) ↦
          P z.1 ∨ Q z.1 z.2) := by
      apply Erdos807.FiniteUniform.probability_mono
      exact himp
    _ ≤ uniformProbability
          (fun z : (Fin q → G) × (Fin (8 * t) → G) ↦ P z.1) +
        uniformProbability
          (fun z : (Fin q → G) × (Fin (8 * t) → G) ↦ Q z.1 z.2) :=
      Erdos807.FiniteUniform.probability_or_le _ _
    _ = uniformProbability P +
        uniformProbability
          (fun c : Fin (q + 8 * t) → G ↦
            (Fintype.card G : ℝ) <
              (exceptionalTargets δ c).card * (2 : ℝ) ^ (6 * t)) := by
      rw [uniformProbability_prod_left]
      congr 1
      exact uniformProbability_append
        (fun c : Fin (q + 8 * t) → G ↦
          (Fintype.card G : ℝ) <
            (exceptionalTargets δ c).card * (2 : ℝ) ^ (6 * t))
    _ ≤ ((Fintype.card G : ℝ) * (2 : ℝ) ^ (2 ^ m) /
          (2 : ℝ) ^ (t * m)) +
        2 / (δ ^ 2 * (2 : ℝ) ^ (2 * t)) := by
      gcongr
      · exact prefix_failure_probability_le (G := G) m t
      · exact first_exception_failure_le (G := G) t hδ

def hallLength (q t n : ℕ) : ℕ := q + 8 * t + n * (2 * t)

def hallExponent (t n : ℕ) : ℕ := (2 ^ n + 5) * t

@[simp] lemma hallLength_zero (q t : ℕ) : hallLength q t 0 = q + 8 * t := by
  simp [hallLength]

lemma hallLength_succ (q t n : ℕ) :
    hallLength q t (n + 1) = hallLength q t n + 2 * t := by
  simp [hallLength, add_mul]
  ring

@[simp] lemma hallExponent_zero (t : ℕ) : hallExponent t 0 = 6 * t := by
  simp [hallExponent]

lemma hallExponent_step_identity (t n : ℕ) :
    2 * (2 * t) + hallExponent t (n + 1) + t =
      2 * hallExponent t n := by
  simp [hallExponent, pow_succ]
  ring

lemma hall_step_error_eq (t n : ℕ) :
    (2 : ℝ) ^ (2 * (2 * t) + hallExponent t (n + 1)) /
        (2 : ℝ) ^ (2 * hallExponent t n) =
      1 / (2 : ℝ) ^ t := by
  have hpow : (2 : ℝ) ^ (2 * hallExponent t n) =
      (2 : ℝ) ^ (2 * (2 * t) + hallExponent t (n + 1)) *
        (2 : ℝ) ^ t := by
    rw [← pow_add]
    congr 1
    exact (hallExponent_step_identity t n).symm
  rw [hpow]
  field_simp

/-- The dyadic inequality needed in every smoothing step. -/
lemma hall_smoothing_scale {q t k : ℕ} (hqk : q ≤ k) {δ : ℝ}
    (hcard : (Fintype.card G : ℝ) ≤ 2 * (2 : ℝ) ^ q)
    (hδ : 2 ≤ δ * (2 : ℝ) ^ t) :
    (2 : ℝ) ^ (k - q + t) ≤
      δ * (2 : ℝ) ^ (2 * t) * tupleMean (G := G) k := by
  have hN : 0 < (Fintype.card G : ℝ) := by positivity
  unfold tupleMean
  rw [show δ * (2 : ℝ) ^ (2 * t) *
      ((2 : ℝ) ^ k / Fintype.card G) =
        (δ * (2 : ℝ) ^ (2 * t) * (2 : ℝ) ^ k) /
          Fintype.card G by ring]
  rw [le_div_iff₀ hN]
  have hleft := mul_le_mul_of_nonneg_left hcard
    (show 0 ≤ (2 : ℝ) ^ (k - q + t) by positivity)
  have hright := mul_le_mul_of_nonneg_right hδ
    (show 0 ≤ (2 : ℝ) ^ (k - q + t) * (2 : ℝ) ^ q by positivity)
  calc
    (2 : ℝ) ^ (k - q + t) * Fintype.card G ≤
        (2 : ℝ) ^ (k - q + t) * (2 * (2 : ℝ) ^ q) := hleft
    _ = 2 * ((2 : ℝ) ^ (k - q + t) * (2 : ℝ) ^ q) := by ring
    _ ≤ (δ * (2 : ℝ) ^ t) *
        ((2 : ℝ) ^ (k - q + t) * (2 : ℝ) ^ q) := hright
    _ = δ * (2 : ℝ) ^ (2 * t) * (2 : ℝ) ^ k := by
      calc
        (δ * (2 : ℝ) ^ t) *
            ((2 : ℝ) ^ (k - q + t) * (2 : ℝ) ^ q) =
          δ * (2 : ℝ) ^ (t + (k - q + t) + q) := by
            rw [pow_add, pow_add]
            ring
        _ = δ * (2 : ℝ) ^ (2 * t + k) := by
          congr 2
          omega
        _ = δ * (2 : ℝ) ^ (2 * t) * (2 : ℝ) ^ k := by
          rw [pow_add]
          ring

/-- Iteration of the smoothing kernel.  Each length-`2t` block costs at most
`2^{-t}` in failure probability. -/
theorem iterated_hallState_failure_le (m t n : ℕ) {δ : ℝ}
    (ht : 1 ≤ t) (hδ : 0 < δ)
    (hsmall : 1 ≤ δ * (2 : ℝ) ^ (2 * t))
    (hscale : 2 ≤ δ * (2 : ℝ) ^ t)
    (htolerance : (n + 1 : ℝ) * δ ≤ 1) :
    let q := Nat.log 2 (Fintype.card G)
    uniformProbability
        (fun a : Fin (hallLength q t n) → G ↦
          ¬ HallState q t (hallExponent t n) (hallLength q t n)
            ((n + 1 : ℝ) * δ) a) ≤
      (Fintype.card G : ℝ) * (2 : ℝ) ^ (2 ^ m) /
          (2 : ℝ) ^ (t * m) +
        2 / (δ ^ 2 * (2 : ℝ) ^ (2 * t)) +
        n / (2 : ℝ) ^ t := by
  classical
  dsimp only
  let q := Nat.log 2 (Fintype.card G)
  induction n with
  | zero =>
      rw [hallLength_zero, hallExponent_zero]
      norm_num
      exact initial_hallState_failure_le (G := G) m t hδ
  | succ n ih =>
      have htolerance' : (n + 1 : ℝ) * δ ≤ 1 := by
        have hn : (n + 1 : ℝ) ≤ (n + 2 : ℝ) := by norm_num
        have hmul := mul_le_mul_of_nonneg_right hn hδ.le
        have htolerance₂ : (n + 2 : ℝ) * δ ≤ 1 := by
          have hcast : (n + 2 : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by
            push_cast
            ring
          rw [hcast]
          exact htolerance
        exact hmul.trans htolerance₂
      have hih := ih htolerance'
      have hqk : q ≤ hallLength q t n := by
        unfold hallLength
        simpa [Nat.add_assoc] using Nat.le_add_right q (8 * t + n * (2 * t))
      have hcard : (Fintype.card G : ℝ) ≤ 2 * (2 : ℝ) ^ q := by
        have hn : Fintype.card G ≤ 2 * 2 ^ q := by
          calc
            Fintype.card G ≤ 2 ^ (q + 1) := by
              apply Nat.le_of_lt
              dsimp [q]
              exact Nat.lt_pow_succ_log_self (by norm_num) _
            _ = 2 * 2 ^ q := by rw [pow_succ]; ring
        exact_mod_cast hn
      have hstep := hallState_failure_append_le (G := G)
        (q := q) (t := t) (e := hallExponent t n)
        (e' := hallExponent t (n + 1)) (k := hallLength q t n)
        (s := 2 * t) (by omega) hqk
        (hη₀ := mul_nonneg (by positivity) hδ.le)
        (hη₁ := htolerance') (hδ := hδ.le) hsmall
        (hall_smoothing_scale hqk hcard hscale) hih
      rw [hall_step_error_eq] at hstep
      rw [← hallLength_succ q t n] at hstep
      simpa [q, Nat.cast_add, Nat.cast_one, add_mul, div_eq_mul_inv,
        add_assoc, add_left_comm, add_comm] using hstep

lemma hallState_implies_balanced {q t e k : ℕ} {ε : ℝ}
    (hcard : Fintype.card G < 2 ^ e) {a : Fin k → G}
    (ha : HallState q t e k ε a) : TupleBalanced ε a := by
  classical
  have hempty : exceptionalTargets ε a = ∅ := by
    apply Finset.card_eq_zero.mp
    by_contra hne
    have hpos : 1 ≤ (exceptionalTargets ε a).card := Nat.one_le_iff_ne_zero.mpr hne
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
    have hlarge : (2 : ℝ) ^ e ≤
        (exceptionalTargets ε a).card * (2 : ℝ) ^ e := by
      have hpos' : (1 : ℝ) ≤ (exceptionalTargets ε a).card := by exact_mod_cast hpos
      nlinarith
    have hcard' : (Fintype.card G : ℝ) < (2 : ℝ) ^ e := by
      exact_mod_cast hcard
    linarith [ha.2]
  intro g
  unfold tupleMean at *
  exact not_mem_exceptionalTargets (by rw [hempty]; simp)

/-- Explicit finite Erdős--Hall bound for independent ordered samples. -/
theorem finite_tuple_success_lower_bound (m t n : ℕ) {ε δ : ℝ}
    (ht : 1 ≤ t) (hδ : 0 < δ)
    (hsmall : 1 ≤ δ * (2 : ℝ) ^ (2 * t))
    (hscale : 2 ≤ δ * (2 : ℝ) ^ t)
    (herror : (n + 1 : ℝ) * δ = ε) (hε : ε ≤ 1)
    (hfinish : Fintype.card G < 2 ^ hallExponent t n) :
    let q := Nat.log 2 (Fintype.card G)
    1 - ((Fintype.card G : ℝ) * (2 : ℝ) ^ (2 ^ m) /
          (2 : ℝ) ^ (t * m) +
        2 / (δ ^ 2 * (2 : ℝ) ^ (2 * t)) +
        n / (2 : ℝ) ^ t) ≤
      tupleSuccessProbability (G := G) ε (hallLength q t n) := by
  classical
  dsimp only
  let q := Nat.log 2 (Fintype.card G)
  have htolerance : (n + 1 : ℝ) * δ ≤ 1 := by rw [herror]; exact hε
  have hstate := iterated_hallState_failure_le (G := G) m t n ht hδ
    hsmall hscale htolerance
  have hfail : uniformProbability
      (fun a : Fin (hallLength q t n) → G ↦ ¬ TupleBalanced ε a) ≤
      (Fintype.card G : ℝ) * (2 : ℝ) ^ (2 ^ m) /
          (2 : ℝ) ^ (t * m) +
        2 / (δ ^ 2 * (2 : ℝ) ^ (2 * t)) +
        n / (2 : ℝ) ^ t := by
    calc
      uniformProbability
          (fun a : Fin (hallLength q t n) → G ↦ ¬ TupleBalanced ε a) ≤
        uniformProbability
          (fun a : Fin (hallLength q t n) → G ↦
            ¬ HallState q t (hallExponent t n) (hallLength q t n)
              ((n + 1 : ℝ) * δ) a) := by
        apply Erdos807.FiniteUniform.probability_mono
        intro a hnot hstateGood
        apply hnot
        rw [herror] at hstateGood
        exact hallState_implies_balanced hfinish hstateGood
      _ ≤ _ := hstate
  rw [uniformProbability_not] at hfail
  unfold tupleSuccessProbability
  linarith

end FiniteProbabilityBounds

section TupleSetTransfer

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def selectedImage {k : ℕ} (a : Fin k → G) (e : BitVec k) :
    Finset G := by
  classical
  exact (Finset.univ.filter fun i ↦ e i).image a

noncomputable def tupleRange {k : ℕ} (a : Fin k → G) : Finset G := by
  classical
  exact Finset.univ.image a

lemma selectedImage_subset_range {k : ℕ} (a : Fin k → G) (e : BitVec k) :
    selectedImage a e ⊆ tupleRange a := by
  classical
  intro x hx
  rw [selectedImage, Finset.mem_image] at hx
  obtain ⟨i, _, rfl⟩ := hx
  simp [tupleRange]

lemma selectedImage_sum {k : ℕ} (a : Fin k → G) (ha : Function.Injective a)
    (e : BitVec k) : subsetSum (selectedImage a e) = tupleSubsetSum a e := by
  classical
  unfold selectedImage subsetSum tupleSubsetSum
  rw [Finset.sum_image]
  · simp [Finset.sum_filter]
  · exact fun i _ j _ hij ↦ ha hij

/-- Boolean selections of an injective tuple are exactly the subsets of its
range. -/
noncomputable def bitVecPowersetEquiv {k : ℕ} (a : Fin k → G)
    (ha : Function.Injective a) :
    BitVec k ≃ ↑(tupleRange a).powerset := by
  classical
  refine
    { toFun := fun e ↦ ⟨selectedImage a e, Finset.mem_powerset.mpr
        (selectedImage_subset_range a e)⟩
      invFun := fun S i ↦ if a i ∈ S.1 then true else false
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    funext i
    cases hei : e i <;> simp [selectedImage, hei, ha.eq_iff]
  · intro S
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      change x ∈ (Finset.univ.filter fun i ↦
        if a i ∈ S.1 then true else false).image a at hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      simpa using hi
    · intro hx
      have hxrange := Finset.mem_powerset.mp S.2 hx
      rw [tupleRange, Finset.mem_image] at hxrange
      obtain ⟨i, _, hi⟩ := hxrange
      subst x
      change a i ∈ (Finset.univ.filter fun j ↦
        if a j ∈ S.1 then true else false).image a
      rw [Finset.mem_image]
      exact ⟨i, by simpa, rfl⟩

/-- On an injective tuple, labelled Boolean selections and literal subsets
give the same representation count. -/
lemma tupleRepCount_eq_setRepCount_range {k : ℕ} (a : Fin k → G)
    (ha : Function.Injective a) (g : G) :
    tupleRepCount a g = setRepCount (tupleRange a) g := by
  classical
  let E := bitVecPowersetEquiv a ha
  have hpred : ∀ e : BitVec k,
      tupleSubsetSum a e = g ↔ subsetSum (E e).1 = g := by
    intro e
    rw [← selectedImage_sum a ha e]
    rfl
  have heq : {e : BitVec k // tupleSubsetSum a e = g} ≃
      {S : ↑(tupleRange a).powerset // subsetSum S.1 = g} :=
    E.subtypeEquiv hpred
  unfold tupleRepCount setRepCount
  calc
    (Finset.univ.filter fun e : BitVec k ↦ tupleSubsetSum a e = g).card =
        Fintype.card {e : BitVec k // tupleSubsetSum a e = g} := by
      simp [Fintype.card_subtype]
    _ = Fintype.card {S : ↑(tupleRange a).powerset // subsetSum S.1 = g} :=
      Fintype.card_congr heq
    _ = ((tupleRange a).powerset.filter fun S ↦ subsetSum S = g).card := by
      rw [Fintype.card_subtype]
      have hfa := Finset.filter_attach
        (p := fun S : Finset G ↦ subsetSum S = g) (tupleRange a).powerset
      have hc := congrArg Finset.card hfa
      simpa using hc

lemma tupleRange_card {k : ℕ} (a : Fin k → G) (ha : Function.Injective a) :
    (tupleRange a).card = k := by
  classical
  unfold tupleRange
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    exact ha hij

lemma tupleBalanced_iff_range {k : ℕ} {ε : ℝ} (a : Fin k → G)
    (ha : Function.Injective a) :
    TupleBalanced ε a ↔ SetBalanced ε (tupleRange a) := by
  unfold TupleBalanced SetBalanced
  rw [tupleRange_card a ha]
  constructor <;> intro h g
  · simpa [tupleRepCount_eq_setRepCount_range a ha g] using h g
  · simpa [tupleRepCount_eq_setRepCount_range a ha g] using h g

/-- Ordered tuples without repetitions. -/
abbrev InjectiveTuples (G : Type*) (k : ℕ) :=
  {a : Fin k → G // Function.Injective a}

/-- A fixed, arbitrary ordering of each `k`-element subset. -/
noncomputable def enumerateKSubset {k : ℕ} (A : KSubsets G k) : Fin k ≃ A := by
  classical
  exact Fintype.equivOfCardEq (by simp [A.2])

noncomputable def orderedKSubset {k : ℕ} (A : KSubsets G k)
    (σ : Equiv.Perm (Fin k)) : Fin k → G :=
  fun i ↦ (enumerateKSubset A (σ i)).1

lemma orderedKSubset_injective {k : ℕ} (A : KSubsets G k)
    (σ : Equiv.Perm (Fin k)) : Function.Injective (orderedKSubset A σ) := by
  intro i j hij
  exact σ.injective ((enumerateKSubset A).injective (Subtype.ext hij))

@[simp] lemma tupleRange_orderedKSubset {k : ℕ} (A : KSubsets G k)
    (σ : Equiv.Perm (Fin k)) : tupleRange (orderedKSubset A σ) = A.1 := by
  classical
  ext x
  simp only [tupleRange, Finset.mem_image, Finset.mem_univ, true_and,
    orderedKSubset]
  constructor
  · rintro ⟨i, rfl⟩
    exact (enumerateKSubset A (σ i)).2
  · intro hx
    obtain ⟨j, hj⟩ := (enumerateKSubset A).surjective ⟨x, hx⟩
    refine ⟨σ.symm j, ?_⟩
    simpa [orderedKSubset] using congrArg Subtype.val hj

abbrev BadKSubsets (G : Type*) [AddCommGroup G] [Fintype G]
    (ε : ℝ) (k : ℕ) :=
  {A : KSubsets G k // ¬ SetBalanced ε A.1}

abbrev BadInjectiveTuples (G : Type*) [AddCommGroup G] [Fintype G]
    (ε : ℝ) (k : ℕ) :=
  {a : Fin k → G // Function.Injective a ∧ ¬ TupleBalanced ε a}

/-- Give a bad set its canonical ordering, modified by a permutation. -/
noncomputable def badSubsetOrder {k : ℕ} {ε : ℝ}
    (x : BadKSubsets G ε k × Equiv.Perm (Fin k)) :
    BadInjectiveTuples G ε k := by
  refine ⟨orderedKSubset x.1.1 x.2, orderedKSubset_injective x.1.1 x.2, ?_⟩
  intro hbal
  apply x.1.2
  rw [← tupleRange_orderedKSubset x.1.1 x.2]
  exact (tupleBalanced_iff_range _ (orderedKSubset_injective x.1.1 x.2)).mp hbal

lemma badSubsetOrder_injective {k : ℕ} {ε : ℝ} :
    Function.Injective (badSubsetOrder (G := G) (k := k) (ε := ε)) := by
  classical
  rintro ⟨xA, xσ⟩ ⟨yA, yσ⟩ hxy
  have hfun : orderedKSubset xA.1 xσ = orderedKSubset yA.1 yσ :=
    congrArg Subtype.val hxy
  have hrange : xA.1.1 = yA.1.1 := by
    rw [← tupleRange_orderedKSubset xA.1 xσ,
      ← tupleRange_orderedKSubset yA.1 yσ]
    exact congrArg tupleRange hfun
  have hsets : xA = yA := by
    apply Subtype.ext
    exact Subtype.ext hrange
  subst yA
  congr 1
  apply Equiv.ext
  intro i
  apply (enumerateKSubset xA.1).injective
  apply Subtype.ext
  simpa [orderedKSubset] using congrFun hfun i

/-- Every bad `k`-set has at least `k!` distinct bad injective orderings. -/
lemma factorial_mul_card_badKSubsets_le {k : ℕ} {ε : ℝ} :
    k.factorial * Nat.card (BadKSubsets G ε k) ≤
      Nat.card (BadInjectiveTuples G ε k) := by
  classical
  have h := Nat.card_le_card_of_injective
    (badSubsetOrder (G := G) (k := k) (ε := ε)) badSubsetOrder_injective
  simpa [Nat.card_prod, Nat.card_perm, Nat.card_fin, Fintype.card_perm,
    Fintype.card_fin, mul_comm] using h

/-- Injective tuples are equivalent to embeddings. -/
def injectiveTuplesEmbeddingEquiv {k : ℕ} :
    InjectiveTuples G k ≃ (Fin k ↪ G) :=
  { toFun := fun a ↦ ⟨a.1, a.2⟩
    invFun := fun a ↦ ⟨a, a.injective⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

lemma card_injectiveTuples {k : ℕ} :
    Nat.card (InjectiveTuples G k) =
      k.factorial * Fintype.card (KSubsets G k) := by
  classical
  rw [Nat.card_congr injectiveTuplesEmbeddingEquiv, Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_finset_len,
    Nat.descFactorial_eq_factorial_mul_choose]

/-- The Boolean vector selecting a single coordinate. -/
def singleBit {k : ℕ} (i : Fin k) : BitVec k := fun j ↦ decide (j = i)

@[simp] lemma tupleSubsetSum_singleBit {k : ℕ} (a : Fin k → G) (i : Fin k) :
    tupleSubsetSum a (singleBit i) = a i := by
  classical
  simp [tupleSubsetSum, singleBit]

lemma singleBit_ne {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    singleBit i ≠ singleBit j := by
  intro h
  have hi := congrFun h i
  simp [singleBit, hij] at hi

noncomputable def collisionPairs (k : ℕ) : Finset (Fin k × Fin k) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter fun p ↦ p.1 ≠ p.2

noncomputable def coordinateCollision {k : ℕ} (p : Fin k × Fin k) :
    Finset (Fin k → G) := by
  classical
  exact Finset.univ.filter fun a ↦ a p.1 = a p.2

/-- For distinct coordinates, exactly `|G|^(k-1)` tuples agree at those
coordinates. -/
lemma card_coordinate_collision {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    (coordinateCollision (G := G) (i, j)).card =
      Fintype.card G ^ (k - 1) := by
  classical
  unfold coordinateCollision
  rw [Finset.card_filter]
  have h := sum_affine_collision_indicator
    (G := G) (singleBit i) (singleBit j) (singleBit_ne hij) 0 0
  simpa [natIndicator] using h

noncomputable def noninjectiveTuplesFinset (G : Type*) [Fintype G] (k : ℕ) :
    Finset (Fin k → G) := by
  classical
  exact Finset.univ.filter fun a ↦ ¬ Function.Injective a

noncomputable def collisionUnion (G : Type*) [Fintype G] (k : ℕ) :
    Finset (Fin k → G) := by
  classical
  exact (collisionPairs k).biUnion (coordinateCollision (G := G))

lemma noninjective_subset_collisionUnion {k : ℕ} :
    noninjectiveTuplesFinset G k ⊆
      collisionUnion G k := by
  classical
  intro a ha
  rw [noninjectiveTuplesFinset, Finset.mem_filter] at ha
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp ha.2
  rw [collisionUnion, Finset.mem_biUnion]
  refine ⟨(i, j), ?_, ?_⟩
  · simp [collisionPairs, hne]
  · simp [coordinateCollision, hij]

/-- Elementary birthday bound for an ordered `k`-tuple. -/
lemma card_noninjective_tuples_le {k : ℕ} :
    Nat.card {a : Fin k → G // ¬ Function.Injective a} ≤
      k ^ 2 * Fintype.card G ^ (k - 1) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (noninjectiveTuplesFinset G k).card ≤ _
  calc
    (noninjectiveTuplesFinset G k).card ≤
        (collisionUnion G k).card :=
      Finset.card_le_card noninjective_subset_collisionUnion
    _ ≤ ∑ p ∈ collisionPairs k, (coordinateCollision (G := G) p).card :=
      by
        unfold collisionUnion
        exact Finset.card_biUnion_le
    _ = (collisionPairs k).card * Fintype.card G ^ (k - 1) := by
      calc
        ∑ p ∈ collisionPairs k, (coordinateCollision (G := G) p).card =
            ∑ _p ∈ collisionPairs k, Fintype.card G ^ (k - 1) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [collisionPairs, Finset.mem_filter] at hp
          exact card_coordinate_collision hp.2
        _ = _ := by simp
    _ ≤ k ^ 2 * Fintype.card G ^ (k - 1) := by
      apply Nat.mul_le_mul_right
      calc
        (collisionPairs k).card ≤
            ((Finset.univ : Finset (Fin k)) ×ˢ Finset.univ).card :=
          Finset.card_filter_le _ _
        _ = k ^ 2 := by simp [pow_two]

lemma card_badInjectiveTuples_le {k : ℕ} {ε : ℝ} :
    Nat.card (BadInjectiveTuples G ε k) ≤
      Nat.card {a : Fin k → G // ¬ TupleBalanced ε a} := by
  exact Nat.card_le_card_of_injective
    (fun a : BadInjectiveTuples G ε k ↦
      (⟨a.1, a.2.2⟩ : {a : Fin k → G // ¬ TupleBalanced ε a}))
    (by
      intro x y h
      exact Subtype.ext (congrArg (fun z ↦ z.1) h))

lemma card_KSubsets_pos {k : ℕ} (hk : k ≤ Fintype.card G) :
    0 < Fintype.card (KSubsets G k) := by
  rw [Fintype.card_finset_len]
  exact Nat.choose_pos hk

lemma card_injectiveTuples_pos {k : ℕ} (hk : k ≤ Fintype.card G) :
    0 < Nat.card (InjectiveTuples G k) := by
  rw [card_injectiveTuples]
  exact Nat.mul_pos (Nat.factorial_pos k) (card_KSubsets_pos hk)

/-- Exact conditioning comparison: failure for a uniform set is at most the
number of bad tuples divided by the number of injective tuples. -/
lemma subset_failure_le_badTuples_div_injective {k : ℕ} {ε : ℝ}
    (hk : k ≤ Fintype.card G) :
    uniformProbability (fun A : KSubsets G k ↦ ¬ SetBalanced ε A.1) ≤
      (Nat.card {a : Fin k → G // ¬ TupleBalanced ε a} : ℝ) /
        Nat.card (InjectiveTuples G k) := by
  unfold uniformProbability
  have hS : (0 : ℝ) < Fintype.card (KSubsets G k) := by
    exact_mod_cast card_KSubsets_pos hk
  have hI : (0 : ℝ) < Nat.card (InjectiveTuples G k) := by
    exact_mod_cast card_injectiveTuples_pos hk
  apply (div_le_div_iff₀ hS hI).2
  exact_mod_cast (calc
    Nat.card (BadKSubsets G ε k) * Nat.card (InjectiveTuples G k) =
        (k.factorial * Nat.card (BadKSubsets G ε k)) *
          Fintype.card (KSubsets G k) := by
      rw [card_injectiveTuples]
      ac_rfl
    _ ≤ Nat.card (BadInjectiveTuples G ε k) *
          Fintype.card (KSubsets G k) :=
      Nat.mul_le_mul_right _ factorial_mul_card_badKSubsets_le
    _ ≤ Nat.card {a : Fin k → G // ¬ TupleBalanced ε a} *
          Fintype.card (KSubsets G k) :=
      Nat.mul_le_mul_right _ card_badInjectiveTuples_le)

lemma card_injective_add_noninjective {k : ℕ} :
    Nat.card (InjectiveTuples G k) +
        Nat.card {a : Fin k → G // ¬ Function.Injective a} =
      Fintype.card G ^ k := by
  classical
  letI : Fintype (InjectiveTuples G k) := Fintype.ofFinite _
  letI : Fintype {a : Fin k → G // ¬ Function.Injective a} := Fintype.ofFinite _
  have hle : Fintype.card (InjectiveTuples G k) ≤
      Fintype.card (Fin k → G) := Fintype.card_subtype_le _
  have hc := Fintype.card_subtype_compl (fun a : Fin k → G ↦ Function.Injective a)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [hc, Nat.add_sub_of_le hle, Fintype.card_fun, Fintype.card_fin]

/-- The fraction of injective tuples is at least the elementary birthday
lower bound `1 - k² / |G|`. -/
lemma birthday_lower_bound {k : ℕ} (hk : 1 ≤ k) :
    1 - (k : ℝ) ^ 2 / Fintype.card G ≤
      (Nat.card (InjectiveTuples G k) : ℝ) /
        (Fintype.card G : ℝ) ^ k := by
  have hN : (0 : ℝ) < Fintype.card G := by positivity
  have hT : (0 : ℝ) < (Fintype.card G : ℝ) ^ k := by positivity
  have hbad :
      (Nat.card {a : Fin k → G // ¬ Function.Injective a} : ℝ) ≤
        (k : ℝ) ^ 2 * (Fintype.card G : ℝ) ^ (k - 1) := by
    exact_mod_cast card_noninjective_tuples_le (G := G) (k := k)
  have hpow : (Fintype.card G : ℝ) ^ k =
      (Fintype.card G : ℝ) ^ (k - 1) * Fintype.card G := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
  have hratio :
      (Nat.card {a : Fin k → G // ¬ Function.Injective a} : ℝ) /
          (Fintype.card G : ℝ) ^ k ≤
        (k : ℝ) ^ 2 / Fintype.card G := by
    apply (div_le_div_iff₀ hT hN).2
    calc
      (Nat.card {a : Fin k → G // ¬ Function.Injective a} : ℝ) *
          Fintype.card G ≤
        ((k : ℝ) ^ 2 * (Fintype.card G : ℝ) ^ (k - 1)) *
          Fintype.card G :=
        mul_le_mul_of_nonneg_right hbad hN.le
      _ = (k : ℝ) ^ 2 * (Fintype.card G : ℝ) ^ k := by rw [hpow]; ring
  have hpartition :
      (Nat.card (InjectiveTuples G k) : ℝ) +
          Nat.card {a : Fin k → G // ¬ Function.Injective a} =
        (Fintype.card G : ℝ) ^ k := by
    exact_mod_cast card_injective_add_noninjective (G := G) (k := k)
  have hinjratio :
      (Nat.card (InjectiveTuples G k) : ℝ) /
          (Fintype.card G : ℝ) ^ k =
        1 -
          (Nat.card {a : Fin k → G // ¬ Function.Injective a} : ℝ) /
            (Fintype.card G : ℝ) ^ k := by
    field_simp
    linarith
  rw [hinjratio]
  linarith

/-- Finite transfer from Hall's independent-tuple estimate to literal
uniform `k`-subsets. -/
theorem subset_failure_le_tuple_failure {k : ℕ} {ε : ℝ}
    (hk1 : 1 ≤ k) (hkG : k ≤ Fintype.card G)
    (hcollision : (k : ℝ) ^ 2 / Fintype.card G < 1) :
    uniformProbability (fun A : KSubsets G k ↦ ¬ SetBalanced ε A.1) ≤
      uniformProbability (fun a : Fin k → G ↦ ¬ TupleBalanced ε a) /
        (1 - (k : ℝ) ^ 2 / Fintype.card G) := by
  let c : ℝ := (k : ℝ) ^ 2 / Fintype.card G
  let I : ℝ := Nat.card (InjectiveTuples G k)
  let T : ℝ := (Fintype.card G : ℝ) ^ k
  let B : ℝ := Nat.card {a : Fin k → G // ¬ TupleBalanced ε a}
  have hden : 0 < 1 - c := sub_pos.mpr hcollision
  have hfrac : 0 < I / T := lt_of_lt_of_le hden (birthday_lower_bound hk1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hI : 0 < I := by dsimp [I]; exact_mod_cast card_injectiveTuples_pos hkG
  calc
    uniformProbability (fun A : KSubsets G k ↦ ¬ SetBalanced ε A.1) ≤
        B / I := subset_failure_le_badTuples_div_injective hkG
    _ = (B / T) / (I / T) := by field_simp
    _ ≤ (B / T) / (1 - c) := by
      apply (div_le_div_iff₀ hfrac hden).2
      exact mul_le_mul_of_nonneg_left (birthday_lower_bound hk1) (by positivity)
    _ = _ := by
      unfold B T c uniformProbability
      simp [Fintype.card_fun, Fintype.card_fin]

end TupleSetTransfer

section AsymptoticParameters

/-- Dyadic exponent of the group order. -/
def hallQ (N : ℕ) : ℕ := Nat.log 2 N

/-- Moment order: the ceiling of the binary logarithm of `hallQ`. -/
def hallM (N : ℕ) : ℕ := Nat.clog 2 (hallQ N)

/-- Number of smoothing rounds.  A square-root choice is enough and makes
the overhead visibly `o(hallQ N)`. -/
def hallRounds (N : ℕ) : ℕ := Nat.sqrt (hallM N) + 1

/-- Initial block length, rounded upward. -/
noncomputable def hallBlock (N : ℕ) : ℕ :=
  ⌈(4 : ℝ) * hallQ N / hallM N⌉₊

/-- The explicit cardinality used in the Erdős--Hall construction. -/
noncomputable def erdos1179Size (N : ℕ) : ℕ :=
  hallLength (hallQ N) (hallBlock N) (hallRounds N)

noncomputable def hallDelta (ε : ℝ) (N : ℕ) : ℝ :=
  ε / (hallRounds N + 1)

noncomputable def hallFailureBound (ε : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) * (2 : ℝ) ^ (2 ^ hallM N) /
      (2 : ℝ) ^ (hallBlock N * hallM N) +
    2 / (hallDelta ε N ^ 2 * (2 : ℝ) ^ (2 * hallBlock N)) +
    hallRounds N / (2 : ℝ) ^ hallBlock N

noncomputable def subsetFailureBound (ε : ℝ) (N : ℕ) : ℝ :=
  hallFailureBound ε N /
    (1 - (erdos1179Size N : ℝ) ^ 2 / N)

lemma hallQ_tendsto_atTop : Tendsto hallQ atTop atTop := by
  convert Erdos807.tendsto_logParameter_atTop using 1
  funext N
  rfl

lemma hallM_tendsto_atTop : Tendsto hallM atTop atTop := by
  rw [tendsto_atTop]
  intro C
  filter_upwards [hallQ_tendsto_atTop.eventually_ge_atTop (2 ^ C + 1)] with N hN
  rw [hallM]
  have hp : 2 ^ C < hallQ N := by omega
  exact (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < (2 : ℕ))).mpr hp |>.le

lemma hallRounds_tendsto_atTop : Tendsto hallRounds atTop atTop := by
  rw [tendsto_atTop]
  intro C
  filter_upwards [hallM_tendsto_atTop.eventually_ge_atTop (C ^ 2)] with N hN
  unfold hallRounds
  have hs : C ≤ Nat.sqrt (hallM N) := Nat.le_sqrt'.mpr hN
  omega

lemma hallM_pos_eventually : ∀ᶠ N in atTop, 0 < hallM N :=
  hallM_tendsto_atTop.eventually (eventually_gt_atTop 0)

lemma hallQ_one_lt_eventually : ∀ᶠ N in atTop, 1 < hallQ N :=
  hallQ_tendsto_atTop.eventually (eventually_gt_atTop 1)

lemma hallM_pow_bounds {N : ℕ} (hQ : 1 < hallQ N) :
    2 ^ (hallM N - 1) < hallQ N ∧ hallQ N ≤ 2 ^ hallM N := by
  constructor
  · simpa [hallM, Nat.pred_eq_sub_one] using
      Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hQ
  · exact (Nat.clog_le_iff_le_pow (by norm_num : 1 < (2 : ℕ))).mp le_rfl

/-- Powers of two dominate the square needed for the chosen number of
smoothing rounds. -/
lemma square_le_two_pow (r : ℕ) (hr : 4 ≤ r) : r ^ 2 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      rw [pow_succ]
      have hquad : (r + 1) ^ 2 ≤ 2 * r ^ 2 := by
        nlinarith
      calc
        (r + 1) ^ 2 ≤ 2 * r ^ 2 := hquad
        _ ≤ 2 * 2 ^ r := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (r + 1) := by rw [pow_succ]; omega

lemma self_le_two_pow_sqrt_add_one (x : ℕ) :
    x ≤ 2 ^ (Nat.sqrt x + 1) := by
  by_cases hs : 3 ≤ Nat.sqrt x
  · have hxlt : x < (Nat.sqrt x + 1) ^ 2 := by
      simpa [pow_two] using Nat.lt_succ_sqrt x
    exact le_trans (Nat.le_of_lt hxlt)
      (square_le_two_pow _ (by omega))
  · have hxlt : x < (Nat.sqrt x + 1) ^ 2 := by
      simpa [pow_two] using Nat.lt_succ_sqrt x
    interval_cases h : Nat.sqrt x <;> norm_num at hxlt ⊢ <;> omega

lemma hallRounds_finish_power (N : ℕ) :
    hallM N ≤ 2 ^ hallRounds N := by
  simpa [hallRounds] using self_le_two_pow_sqrt_add_one (hallM N)

lemma hallBlock_mul_hallM {N : ℕ} (hM : 0 < hallM N) :
    4 * hallQ N ≤ hallBlock N * hallM N := by
  have hceil := Nat.le_ceil ((4 : ℝ) * hallQ N / hallM N)
  have hM' : (0 : ℝ) < hallM N := by exact_mod_cast hM
  change (4 : ℝ) * hallQ N / hallM N ≤ (hallBlock N : ℝ) at hceil
  have hreal : (4 : ℝ) * hallQ N ≤ (hallBlock N : ℝ) * hallM N := by
    calc
      (4 : ℝ) * hallQ N = ((4 : ℝ) * hallQ N / hallM N) * hallM N := by
        field_simp
      _ ≤ (hallBlock N : ℝ) * hallM N :=
        mul_le_mul_of_nonneg_right hceil hM'.le
  exact_mod_cast hreal

lemma hallBlock_pos {N : ℕ} (hQ : 0 < hallQ N) (hM : 0 < hallM N) :
    0 < hallBlock N := by
  rw [hallBlock, Nat.ceil_pos]
  positivity

lemma self_div_two_pow_tendsto_zero :
    Tendsto (fun x : ℕ ↦ (x : ℝ) / (2 : ℝ) ^ x) atTop (nhds 0) := by
  simpa using tendsto_pow_const_div_const_pow_of_one_lt 1
    (by norm_num : (1 : ℝ) < 2)

lemma two_pow_div_self_tendsto_atTop :
    Tendsto (fun x : ℕ ↦ (2 : ℝ) ^ x / x) atTop atTop := by
  have hpos : ∀ᶠ x : ℕ in atTop, 0 < (x : ℝ) / (2 : ℝ) ^ x := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
    positivity
  have hwithin :
      Tendsto (fun x : ℕ ↦ (x : ℝ) / (2 : ℝ) ^ x) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨self_div_two_pow_tendsto_zero, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  convert hinv using 1
  funext x
  simp [inv_div]

lemma sqrt_add_one_div_self_tendsto_zero :
    Tendsto (fun x : ℕ ↦ (Nat.sqrt x + 1 : ℝ) / x) atTop (nhds 0) := by
  let u : ℕ → ℝ := fun x ↦ (Real.sqrt x + 1) / x
  have hsqrtTop : Tendsto (fun x : ℕ ↦ Real.sqrt (x : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto u atTop (nhds 0) := by
    have hsum := hsqrtTop.inv_tendsto_atTop.add
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    have hsum' : Tendsto
        (fun x : ℕ ↦ (Real.sqrt (x : ℝ))⁻¹ + ((x : ℝ))⁻¹)
        atTop (nhds 0) := by simpa using hsum
    apply hsum'.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
    have hx' : (0 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx)
    have hs : Real.sqrt (x : ℝ) ≠ 0 := (Real.sqrt_pos.2 hx').ne'
    dsimp [u]
    field_simp
    nlinarith [Real.sq_sqrt hx'.le]
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) _ hu
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
  have hx' : (0 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx)
  have hsqrt : (Nat.sqrt x : ℝ) ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' x
  dsimp [u]
  exact div_le_div_of_nonneg_right (by linarith) hx'.le

lemma hallRounds_div_hallM_tendsto_zero :
    Tendsto (fun N : ℕ ↦ (hallRounds N : ℝ) / hallM N) atTop (nhds 0) := by
  have h := sqrt_add_one_div_self_tendsto_zero.comp hallM_tendsto_atTop
  convert h using 1
  funext N
  simp [hallRounds]

lemma hallM_div_hallQ_tendsto_zero :
    Tendsto (fun N : ℕ ↦ (hallM N : ℝ) / hallQ N) atTop (nhds 0) := by
  have hupper : Tendsto
      (fun N : ℕ ↦ 2 * ((hallM N : ℝ) / (2 : ℝ) ^ hallM N))
      atTop (nhds 0) :=
    by
      simpa only [Function.comp_apply, mul_zero] using
        (self_div_two_pow_tendsto_zero.comp hallM_tendsto_atTop).const_mul 2
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) _ hupper
  filter_upwards [hallQ_one_lt_eventually, hallM_pos_eventually] with N hQ hM
  have hp := (hallM_pow_bounds hQ).1
  have hpow : (2 : ℕ) ^ hallM N < 2 * hallQ N := by
    calc
      (2 : ℕ) ^ hallM N = (2 : ℕ) ^ (hallM N - 1) * 2 := by
        rw [← pow_succ]
        congr 2
        omega
      _ = 2 * 2 ^ (hallM N - 1) := Nat.mul_comm _ _
      _ < 2 * hallQ N :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < (2 : ℕ))).2 hp
  have hQ' : (0 : ℝ) < hallQ N := by exact_mod_cast hQ.trans' Nat.zero_lt_one
  have hp' : (2 : ℝ) ^ hallM N < 2 * hallQ N := by exact_mod_cast hpow
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ hallM N := by positivity
  rw [show 2 * ((hallM N : ℝ) / (2 : ℝ) ^ hallM N) =
    (2 * hallM N : ℝ) / (2 : ℝ) ^ hallM N by ring]
  apply (div_le_div_iff₀ hQ' hpowpos).2
  nlinarith

lemma hallBlock_tendsto_atTop : Tendsto hallBlock atTop atTop := by
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  have hbase : Tendsto
      (fun N : ℕ ↦ (1 / 2 : ℝ) *
        ((2 : ℝ) ^ hallM N / hallM N)) atTop atTop :=
    (two_pow_div_self_tendsto_atTop.comp hallM_tendsto_atTop).const_mul_atTop
      (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hbase
  filter_upwards [hallQ_one_lt_eventually, hallM_pos_eventually] with N hQ hM
  have hp := (hallM_pow_bounds hQ).1
  have hpow : (2 : ℝ) ^ hallM N < 2 * hallQ N := by
    exact_mod_cast (show (2 : ℕ) ^ hallM N < 2 * hallQ N by
      calc
        (2 : ℕ) ^ hallM N = (2 : ℕ) ^ (hallM N - 1) * 2 := by
          rw [← pow_succ]
          congr 2
          omega
        _ = 2 * 2 ^ (hallM N - 1) := Nat.mul_comm _ _
        _ < 2 * hallQ N :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < (2 : ℕ))).2 hp)
  have hM' : (0 : ℝ) < hallM N := by exact_mod_cast hM
  have hceil := Nat.le_ceil ((4 : ℝ) * hallQ N / hallM N)
  change (4 : ℝ) * hallQ N / hallM N ≤ (hallBlock N : ℝ) at hceil
  calc
    (1 / 2 : ℝ) * ((2 : ℝ) ^ hallM N / hallM N) ≤
        (4 : ℝ) * hallQ N / hallM N := by
      calc
        (1 / 2 : ℝ) * ((2 : ℝ) ^ hallM N / hallM N) =
            ((1 / 2 : ℝ) * (2 : ℝ) ^ hallM N) / hallM N := by ring
        _ ≤ ((4 : ℝ) * hallQ N) / hallM N := by
          apply div_le_div_of_nonneg_right _ hM'.le
          nlinarith
        _ = _ := by ring
    _ ≤ (hallBlock N : ℝ) := hceil

lemma hallBlock_cast_lt {N : ℕ} (hM : 0 < hallM N) :
    (hallBlock N : ℝ) < (4 : ℝ) * hallQ N / hallM N + 1 := by
  have hnonneg : (0 : ℝ) ≤ (4 : ℝ) * hallQ N / hallM N := by positivity
  simpa only [hallBlock] using Nat.ceil_lt_add_one hnonneg

lemma hallRounds_div_hallQ_tendsto_zero :
    Tendsto (fun N : ℕ ↦ (hallRounds N : ℝ) / hallQ N) atTop (nhds 0) := by
  have hprod := hallRounds_div_hallM_tendsto_zero.mul hallM_div_hallQ_tendsto_zero
  have hprod' : Tendsto
      (fun N : ℕ ↦ ((hallRounds N : ℝ) / hallM N) *
        ((hallM N : ℝ) / hallQ N)) atTop (nhds 0) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [hallM_pos_eventually] with N hM
  field_simp

lemma hallOverheadRatio_tendsto_zero :
    Tendsto
      (fun N : ℕ ↦
        ((8 * hallBlock N + hallRounds N * (2 * hallBlock N) : ℕ) : ℝ) /
          hallQ N)
      atTop (nhds 0) := by
  let U : ℕ → ℝ := fun N ↦
    32 / (hallM N : ℝ) + 8 / hallQ N +
      8 * ((hallRounds N : ℝ) / hallM N) +
      2 * ((hallRounds N : ℝ) / hallQ N)
  have hMinv : Tendsto (fun N : ℕ ↦ ((hallM N : ℝ))⁻¹) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop.comp hallM_tendsto_atTop).inv_tendsto_atTop
  have hQinv : Tendsto (fun N : ℕ ↦ ((hallQ N : ℝ))⁻¹) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop.comp hallQ_tendsto_atTop).inv_tendsto_atTop
  have hU : Tendsto U atTop (nhds 0) := by
    dsimp [U]
    convert (((hMinv.const_mul 32).add (hQinv.const_mul 8)).add
      (hallRounds_div_hallM_tendsto_zero.const_mul 8)).add
        (hallRounds_div_hallQ_tendsto_zero.const_mul 2) using 1 <;> ring
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) _ hU
  filter_upwards [hallM_pos_eventually, hallQ_one_lt_eventually] with N hM hQ
  have hM' : (0 : ℝ) < hallM N := by exact_mod_cast hM
  have hQ' : (0 : ℝ) < hallQ N := by exact_mod_cast hQ.trans' Nat.zero_lt_one
  have ht := le_of_lt (hallBlock_cast_lt hM)
  dsimp [U]
  push_cast
  calc
    ((8 : ℝ) * hallBlock N + hallRounds N * (2 * hallBlock N)) / hallQ N =
        (8 + 2 * hallRounds N) * hallBlock N / hallQ N := by ring
    _ ≤ (8 + 2 * hallRounds N) *
          ((4 : ℝ) * hallQ N / hallM N + 1) / hallQ N := by
      gcongr
    _ = 32 / (hallM N : ℝ) + 8 / hallQ N +
          8 * ((hallRounds N : ℝ) / hallM N) +
          2 * ((hallRounds N : ℝ) / hallQ N) := by
      field_simp
      ring

lemma erdos1179Size_div_hallQ_tendsto_one :
    Tendsto (fun N : ℕ ↦ (erdos1179Size N : ℝ) / hallQ N) atTop (nhds 1) := by
  have h : Tendsto
      (fun N : ℕ ↦ (1 : ℝ) +
        ((8 * hallBlock N + hallRounds N * (2 * hallBlock N) : ℕ) : ℝ) /
          hallQ N) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hallOverheadRatio_tendsto_zero)
  apply h.congr'
  filter_upwards [hallQ_one_lt_eventually] with N hQ
  have hQ0 : (hallQ N : ℝ) ≠ 0 := by positivity
  unfold erdos1179Size hallLength
  push_cast
  field_simp
  ring

lemma hallQ_div_logb_tendsto_one :
    Tendsto (fun N : ℕ ↦ (hallQ N : ℝ) / Real.logb 2 N) atTop (nhds 1) := by
  let L : ℕ → ℝ := fun N ↦ Real.logb 2 N
  have hL : Tendsto L atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun N ↦ (L N)⁻¹) atTop (nhds 0) := hL.inv_tendsto_atTop
  have hgap : Tendsto (fun N ↦ 1 - (hallQ N : ℝ) / L N) atTop (nhds 0) := by
    apply squeeze_zero' _ _ hInv
    · filter_upwards [hL.eventually (eventually_gt_atTop 0)] with N hLN
      have hfloor : (hallQ N : ℝ) ≤ L N := by
        exact Real.natLog_le_logb N 2
      exact sub_nonneg.mpr ((div_le_one hLN).mpr hfloor)
    · filter_upwards [hL.eventually (eventually_gt_atTop 0)] with N hLN
      have hf : ⌊L N⌋₊ = hallQ N := by
        simpa [L, hallQ] using Real.natFloor_logb_natCast 2 N
      have hlt := Nat.lt_floor_add_one (L N)
      rw [hf] at hlt
      have hgaplt : L N - hallQ N < 1 := by linarith
      rw [show 1 - (hallQ N : ℝ) / L N =
        (L N - hallQ N) / L N by field_simp]
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (le_of_lt hgaplt) hLN.le
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hsub := hone.sub hgap
  convert hsub using 1
  · funext N
    dsimp [L]
    ring
  · norm_num

/-- The explicit Erdős--Hall size is asymptotic to the real binary
logarithm. -/
theorem erdos1179Size_asymptotic :
    Tendsto (fun N : ℕ ↦ (erdos1179Size N : ℝ) / Real.logb 2 N)
      atTop (nhds 1) := by
  have hprod := erdos1179Size_div_hallQ_tendsto_one.mul hallQ_div_logb_tendsto_one
  have hprod' : Tendsto
      (fun N : ℕ ↦ (erdos1179Size N : ℝ) / hallQ N *
        ((hallQ N : ℝ) / Real.logb 2 N)) atTop (nhds 1) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [hallQ_one_lt_eventually] with N hQ
  have hQ0 : (hallQ N : ℝ) ≠ 0 := by positivity
  field_simp

lemma hallM_div_hallBlock_tendsto_zero :
    Tendsto (fun N : ℕ ↦ (hallM N : ℝ) / hallBlock N) atTop (nhds 0) := by
  have hupper : Tendsto
      (fun N : ℕ ↦ 2 * ((hallM N : ℝ) ^ 2 /
        (2 : ℝ) ^ hallM N)) atTop (nhds 0) := by
    have hbase := (tendsto_pow_const_div_const_pow_of_one_lt 2
      (by norm_num : (1 : ℝ) < 2)).comp hallM_tendsto_atTop
    simpa only [Function.comp_apply, mul_zero] using hbase.const_mul 2
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) _ hupper
  filter_upwards [hallQ_one_lt_eventually, hallM_pos_eventually] with N hQ hM
  have hB : 0 < hallBlock N := hallBlock_pos (by omega) hM
  have hmul := hallBlock_mul_hallM (N := N) hM
  have hpowNat : (2 : ℕ) ^ hallM N < 2 * hallQ N := by
    have hp := (hallM_pow_bounds hQ).1
    calc
      (2 : ℕ) ^ hallM N = (2 : ℕ) ^ (hallM N - 1) * 2 := by
        rw [← pow_succ]
        congr 2
        omega
      _ = 2 * 2 ^ (hallM N - 1) := Nat.mul_comm _ _
      _ < 2 * hallQ N :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < (2 : ℕ))).2 hp
  have hpow : (2 : ℝ) ^ hallM N ≤ 2 * hallQ N := by
    exact_mod_cast hpowNat.le
  have hmul' : (4 : ℝ) * hallQ N ≤ hallBlock N * hallM N := by
    exact_mod_cast hmul
  have hM' : (0 : ℝ) < hallM N := by exact_mod_cast hM
  have hB' : (0 : ℝ) < hallBlock N := by exact_mod_cast hB
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ hallM N := by positivity
  rw [show 2 * ((hallM N : ℝ) ^ 2 / (2 : ℝ) ^ hallM N) =
    (2 * (hallM N : ℝ) ^ 2) / (2 : ℝ) ^ hallM N by ring]
  apply (div_le_div_iff₀ hB' hpowpos).2
  nlinarith

lemma hallRounds_div_hallBlock_tendsto_zero :
    Tendsto (fun N : ℕ ↦ (hallRounds N : ℝ) / hallBlock N) atTop (nhds 0) := by
  have hprod := hallRounds_div_hallM_tendsto_zero.mul hallM_div_hallBlock_tendsto_zero
  have hprod' : Tendsto
      (fun N : ℕ ↦ ((hallRounds N : ℝ) / hallM N) *
        ((hallM N : ℝ) / hallBlock N)) atTop (nhds 0) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [hallM_pos_eventually] with N hM
  field_simp

lemma hallRounds_le_hallBlock_eventually :
    ∀ᶠ N in atTop, hallRounds N ≤ hallBlock N := by
  have hlt := (tendsto_order.1 hallRounds_div_hallBlock_tendsto_zero).2 1 zero_lt_one
  filter_upwards [hlt, hallBlock_tendsto_atTop.eventually (eventually_gt_atTop 0)] with N hratio hB
  have hB' : (0 : ℝ) < hallBlock N := by exact_mod_cast hB
  have : (hallRounds N : ℝ) < hallBlock N := (div_lt_one hB').mp hratio
  exact_mod_cast this.le

lemma hallBlock_polynomial_error_tendsto_zero :
    Tendsto (fun N : ℕ ↦
      (hallBlock N + 1 : ℝ) ^ 2 / (4 : ℝ) ^ hallBlock N)
      atTop (nhds 0) := by
  have hbase : Tendsto (fun t : ℕ ↦
      (t + 1 : ℝ) ^ 2 / (4 : ℝ) ^ t) atTop (nhds 0) := by
    have hup := (tendsto_pow_const_div_const_pow_of_one_lt 2
      (by norm_num : (1 : ℝ) < 4)).const_mul 4
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) _ (by simpa using hup)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with t ht
    have ht' : (0 : ℝ) ≤ t := by positivity
    rw [show 4 * ((t : ℝ) ^ 2 / (4 : ℝ) ^ t) =
      (4 * (t : ℝ) ^ 2) / (4 : ℝ) ^ t by ring]
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ t)
    push_cast
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hprod : (0 : ℝ) ≤ ((t : ℝ) - 1) * (3 * t + 1) :=
      mul_nonneg (sub_nonneg.mpr htR) (by positivity)
    nlinarith
  have hcomp := hbase.comp hallBlock_tendsto_atTop
  convert hcomp using 1
  funext N
  simp

lemma hallBlock_linear_error_tendsto_zero :
    Tendsto (fun N : ℕ ↦
      (hallBlock N : ℝ) / (2 : ℝ) ^ hallBlock N)
      atTop (nhds 0) := by
  have hcomp := self_div_two_pow_tendsto_zero.comp hallBlock_tendsto_atTop
  convert hcomp using 1
  funext N
  rfl

lemma size_square_div_tendsto_zero :
    Tendsto (fun N : ℕ ↦ (erdos1179Size N : ℝ) ^ 2 / N)
      atTop (nhds 0) := by
  let L : ℕ → ℝ := fun N ↦ Real.logb 2 N
  have hsizeSq : Tendsto
      (fun N : ℕ ↦ ((erdos1179Size N : ℝ) / L N) ^ 2) atTop (nhds 1) := by
    simpa [L] using erdos1179Size_asymptotic.pow 2
  have hlogSq : Tendsto (fun N : ℕ ↦ L N ^ 2 / N) atTop (nhds 0) := by
    have hraw : Tendsto
        (fun N : ℕ ↦ Real.log (N : ℝ) ^ 2 / (N : ℝ)) atTop (nhds 0) :=
      by
        have hcomp := (isLittleO_log_rpow_rpow_atTop 2
          (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp
            tendsto_natCast_atTop_atTop
        convert hcomp using 1
        funext N
        simp
    have hc := hraw.const_mul ((Real.log 2) ^ 2)⁻¹
    have hc' : Tendsto
        (fun N : ℕ ↦ ((Real.log 2) ^ 2)⁻¹ *
          (Real.log (N : ℝ) ^ 2 / (N : ℝ))) atTop (nhds 0) := by
      simpa using hc
    apply hc'.congr'
    filter_upwards with N
    dsimp [L, Real.logb]
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
  have hprod := hsizeSq.mul hlogSq
  have hprod' : Tendsto
      (fun N : ℕ ↦ ((erdos1179Size N : ℝ) / L N) ^ 2 *
        (L N ^ 2 / (N : ℝ))) atTop (nhds 0) := by
    simpa using hprod
  have hLtop : Tendsto L atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      tendsto_natCast_atTop_atTop
  apply hprod'.congr'
  filter_upwards [hLtop.eventually (eventually_gt_atTop 0)] with N hL
  dsimp [L] at *
  field_simp

lemma prefixError_tendsto_zero :
    Tendsto (fun N : ℕ ↦
      (N : ℝ) * (2 : ℝ) ^ (2 ^ hallM N) /
        (2 : ℝ) ^ (hallBlock N * hallM N)) atTop (nhds 0) := by
  have hupper : Tendsto (fun N : ℕ ↦
      2 / (2 : ℝ) ^ hallQ N) atTop (nhds 0) := by
    have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).comp
        hallQ_tendsto_atTop
    have hc := hpow.const_mul 2
    have hc' : Tendsto (fun N : ℕ ↦
        2 * (1 / 2 : ℝ) ^ hallQ N) atTop (nhds 0) := by
      simpa using hc
    apply hc'.congr'
    filter_upwards with N
    rw [div_pow]
    norm_num
    ring
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) _ hupper
  filter_upwards [hallQ_one_lt_eventually, hallM_pos_eventually] with N hQ hM
  have hN : N ≤ 2 ^ (hallQ N + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N).le
  have hmPow : 2 ^ hallM N ≤ 2 * hallQ N := by
    have hp := (hallM_pow_bounds hQ).1
    calc
      2 ^ hallM N = 2 ^ (hallM N - 1) * 2 := by
        rw [← pow_succ]
        congr 2
        omega
      _ = 2 * 2 ^ (hallM N - 1) := Nat.mul_comm _ _
      _ ≤ 2 * hallQ N := Nat.mul_le_mul_left 2 hp.le
  have htm := hallBlock_mul_hallM (N := N) hM
  have hN' : (N : ℝ) ≤ (2 : ℝ) ^ (hallQ N + 1) := by exact_mod_cast hN
  have hmPow' : (2 : ℝ) ^ (2 ^ hallM N) ≤
      (2 : ℝ) ^ (2 * hallQ N) :=
    pow_le_pow_right₀ (by norm_num) hmPow
  have htm' : (2 : ℝ) ^ (4 * hallQ N) ≤
      (2 : ℝ) ^ (hallBlock N * hallM N) :=
    pow_le_pow_right₀ (by norm_num) htm
  have hden4 : (0 : ℝ) < (2 : ℝ) ^ (4 * hallQ N) := by positivity
  calc
    (N : ℝ) * (2 : ℝ) ^ (2 ^ hallM N) /
          (2 : ℝ) ^ (hallBlock N * hallM N) ≤
        ((2 : ℝ) ^ (hallQ N + 1) * (2 : ℝ) ^ (2 * hallQ N)) /
          (2 : ℝ) ^ (hallBlock N * hallM N) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hN' hmPow' (by positivity) (by positivity)
    _ ≤ (2 : ℝ) ^ (hallQ N + 1) * (2 : ℝ) ^ (2 * hallQ N) /
          (2 : ℝ) ^ (4 * hallQ N) := by
      exact div_le_div_of_nonneg_left (by positivity) hden4 htm'
    _ = 2 / (2 : ℝ) ^ hallQ N := by
      field_simp
      rw [← pow_add, ← pow_add,
        show hallQ N + 1 + 2 * hallQ N + hallQ N =
          4 * hallQ N + 1 by omega, pow_succ]

lemma smoothingError_tendsto_zero :
    Tendsto (fun N : ℕ ↦
      (hallRounds N : ℝ) / (2 : ℝ) ^ hallBlock N) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) _
    hallBlock_linear_error_tendsto_zero
  filter_upwards [hallRounds_le_hallBlock_eventually] with N hle
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (by positivity)

lemma dispersionError_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ ↦
      2 / (hallDelta ε N ^ 2 * (2 : ℝ) ^ (2 * hallBlock N)))
      atTop (nhds 0) := by
  have hconst := hallBlock_polynomial_error_tendsto_zero.const_mul (2 / ε ^ 2)
  have hconst' : Tendsto (fun N : ℕ ↦
      (2 / ε ^ 2) *
        ((hallBlock N + 1 : ℝ) ^ 2 / (4 : ℝ) ^ hallBlock N))
      atTop (nhds 0) := by simpa using hconst
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) _ hconst'
  filter_upwards [hallRounds_le_hallBlock_eventually] with N hle
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hpow : (2 : ℝ) ^ (2 * hallBlock N) = (4 : ℝ) ^ hallBlock N := by
    rw [pow_mul]
    norm_num
  rw [hallDelta, hpow]
  have hn : (0 : ℝ) < hallRounds N + 1 := by positivity
  have ht : (0 : ℝ) < (4 : ℝ) ^ hallBlock N := by positivity
  have hnum : (hallRounds N + 1 : ℝ) ^ 2 ≤
      (hallBlock N + 1 : ℝ) ^ 2 := by
    gcongr
  calc
    2 / ((ε / (hallRounds N + 1)) ^ 2 * (4 : ℝ) ^ hallBlock N) =
        (2 / ε ^ 2) *
          ((hallRounds N + 1 : ℝ) ^ 2 / (4 : ℝ) ^ hallBlock N) := by
      field_simp
    _ ≤ (2 / ε ^ 2) *
          ((hallBlock N + 1 : ℝ) ^ 2 / (4 : ℝ) ^ hallBlock N) := by
      gcongr

lemma hallFailureBound_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (hallFailureBound ε) atTop (nhds 0) := by
  unfold hallFailureBound
  simpa using (prefixError_tendsto_zero.add
    (dispersionError_tendsto_zero hε)).add smoothingError_tendsto_zero

lemma hallBlock_succ_div_pow_tendsto_zero :
    Tendsto (fun N : ℕ ↦
      (hallBlock N + 1 : ℝ) / (2 : ℝ) ^ hallBlock N)
      atTop (nhds 0) := by
  have hbase : Tendsto (fun t : ℕ ↦
      (t + 1 : ℝ) / (2 : ℝ) ^ t) atTop (nhds 0) := by
    have hup := self_div_two_pow_tendsto_zero.const_mul 2
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) _ (by simpa using hup)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with t ht
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    rw [show 2 * ((t : ℝ) / (2 : ℝ) ^ t) =
      (2 * (t : ℝ)) / (2 : ℝ) ^ t by ring]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hcomp := hbase.comp hallBlock_tendsto_atTop
  convert hcomp using 1
  funext N
  simp

lemma hallScale_tendsto_atTop {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ ↦ hallDelta ε N * (2 : ℝ) ^ hallBlock N)
      atTop atTop := by
  have hpos : ∀ᶠ N : ℕ in atTop,
      0 < (hallBlock N + 1 : ℝ) / (2 : ℝ) ^ hallBlock N := by
    filter_upwards with N
    positivity
  have hwithin : Tendsto (fun N : ℕ ↦
      (hallBlock N + 1 : ℝ) / (2 : ℝ) ^ hallBlock N)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hallBlock_succ_div_pow_tendsto_zero, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  have htarget : Tendsto (fun N : ℕ ↦
      ε * ((2 : ℝ) ^ hallBlock N / (hallBlock N + 1))) atTop atTop := by
    have hc := hinv.const_mul_atTop hε
    apply hc.congr'
    filter_upwards with N
    simp only [Pi.inv_apply, inv_div]
  refine tendsto_atTop_mono' _ ?_ htarget
  filter_upwards [hallRounds_le_hallBlock_eventually] with N hle
  have hn : (0 : ℝ) < hallRounds N + 1 := by positivity
  have ht : (0 : ℝ) < hallBlock N + 1 := by positivity
  unfold hallDelta
  have hle' : (hallRounds N + 1 : ℝ) ≤ hallBlock N + 1 := by
    exact_mod_cast Nat.add_le_add_right hle 1
  have hposnum : 0 ≤ ε * (2 : ℝ) ^ hallBlock N := by positivity
  calc
    ε * ((2 : ℝ) ^ hallBlock N / (hallBlock N + 1)) =
        (ε * (2 : ℝ) ^ hallBlock N) / (hallBlock N + 1) := by ring
    _ ≤ (ε * (2 : ℝ) ^ hallBlock N) / (hallRounds N + 1) :=
      div_le_div_of_nonneg_left hposnum hn hle'
    _ = ε / (hallRounds N + 1) * (2 : ℝ) ^ hallBlock N := by ring

lemma subsetFailureBound_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (subsetFailureBound ε) atTop (nhds 0) := by
  have hden : Tendsto (fun N : ℕ ↦
      1 - (erdos1179Size N : ℝ) ^ 2 / N) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub size_square_div_tendsto_zero
  have hquot := (hallFailureBound_tendsto_zero hε).div hden
    (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (hallFailureBound ε / fun N : ℕ ↦
    1 - (erdos1179Size N : ℝ) ^ 2 / N) atTop (nhds 0)
  simpa only [zero_div] using hquot

lemma hallBlock_one_le_eventually :
    ∀ᶠ N : ℕ in atTop, 1 ≤ hallBlock N :=
  hallBlock_tendsto_atTop.eventually_ge_atTop 1

lemma hallScale_two_le_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ hallDelta ε N * (2 : ℝ) ^ hallBlock N :=
  (hallScale_tendsto_atTop hε).eventually_ge_atTop 2

lemma hallSmallScale_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ hallDelta ε N * (2 : ℝ) ^ (2 * hallBlock N) := by
  filter_upwards [hallScale_two_le_eventually hε] with N hscale
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ hallBlock N := one_le_pow₀ (by norm_num)
  rw [show 2 * hallBlock N = hallBlock N + hallBlock N by omega, pow_add]
  nlinarith

lemma hall_finish_eventually :
    ∀ᶠ N : ℕ in atTop,
      N < 2 ^ hallExponent (hallBlock N) (hallRounds N) := by
  filter_upwards [hallQ_one_lt_eventually, hallM_pos_eventually] with N hQ hM
  have hN : N < 2 ^ (hallQ N + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N
  have hq : hallQ N + 1 ≤ 4 * hallQ N := by omega
  have hqm : 4 * hallQ N ≤ hallBlock N * hallM N :=
    hallBlock_mul_hallM hM
  have hmr : hallM N ≤ 2 ^ hallRounds N := hallRounds_finish_power N
  calc
    N < 2 ^ (hallQ N + 1) := hN
    _ ≤ 2 ^ (4 * hallQ N) := Nat.pow_le_pow_right (by norm_num) hq
    _ ≤ 2 ^ (hallBlock N * hallM N) :=
      Nat.pow_le_pow_right (by norm_num) hqm
    _ ≤ 2 ^ (hallBlock N * 2 ^ hallRounds N) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hmr)
    _ ≤ 2 ^ hallExponent (hallBlock N) (hallRounds N) := by
      apply Nat.pow_le_pow_right (by norm_num)
      calc
        hallBlock N * 2 ^ hallRounds N ≤
            hallBlock N * 2 ^ hallRounds N + 5 * hallBlock N :=
          Nat.le_add_right _ _
        _ = hallExponent (hallBlock N) (hallRounds N) := by
          simp [hallExponent]
          ring

end AsymptoticParameters

section LowerBound

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma card_group_pos : 0 < Fintype.card G := Fintype.card_pos

lemma mean_pos (A : Finset G) :
    0 < (2 : ℝ) ^ A.card / Fintype.card G := by
  positivity

lemma setRepCount_pos_of_balanced {ε : ℝ} (_hε0 : 0 < ε) (hε1 : ε < 1)
    {A : Finset G} (hA : SetBalanced ε A) (g : G) :
    0 < setRepCount A g := by
  have hm : 0 < (2 : ℝ) ^ A.card / Fintype.card G := mean_pos A
  have h := hA g
  have hlo :
      - (ε * ((2 : ℝ) ^ A.card / Fintype.card G)) ≤
        (setRepCount A g : ℝ) - (2 : ℝ) ^ A.card / Fintype.card G :=
    (abs_le.mp h).1
  have hpos : 0 < (setRepCount A g : ℝ) := by
    nlinarith
  exact_mod_cast hpos

/-- An `ε`-balanced set with `ε < 1` represents every group element. -/
lemma subsetSum_surjective_of_balanced {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {A : Finset G} (hA : SetBalanced ε A) :
    Function.Surjective (fun S : ↥A.powerset ↦ subsetSum S.1) := by
  classical
  intro g
  have hpos := setRepCount_pos_of_balanced hε0 hε1 hA g
  rw [setRepCount, Finset.card_pos] at hpos
  obtain ⟨S, hS⟩ := hpos
  have hSmem := Finset.mem_filter.mp hS
  exact ⟨⟨S, hSmem.1⟩, hSmem.2⟩

/-- The exact, pointwise lower bound behind `g_ε(n) ≥ log₂ n`. -/
theorem balanced_card_le_two_pow {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {A : Finset G} (hA : SetBalanced ε A) :
    Fintype.card G ≤ 2 ^ A.card := by
  classical
  let f : ↥A.powerset → G := fun S ↦ subsetSum S.1
  have hf : Function.Surjective f := subsetSum_surjective_of_balanced hε0 hε1 hA
  have hcard := Fintype.card_le_of_surjective f hf
  calc
    Fintype.card G ≤ Fintype.card (↥A.powerset) := hcard
    _ = A.powerset.card := Fintype.card_coe _
    _ = 2 ^ A.card := Finset.card_powerset A

end LowerBound

section FinalAssembly

/-- The quantitative Erdős--Hall estimate, uniformly for every finite abelian
group of order `N`, after conditioning independent samples to be distinct. -/
theorem finite_subset_success_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (G : Type u) [AddCommGroup G] [Fintype G], Fintype.card G = N →
        1 - subsetFailureBound ε N ≤
          subsetSuccessProbability (G := G) ε (erdos1179Size N) := by
  have hcollisionEventually : ∀ᶠ N : ℕ in atTop,
      (erdos1179Size N : ℝ) ^ 2 / N < 1 :=
    size_square_div_tendsto_zero.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hallQ_one_lt_eventually, hallBlock_one_le_eventually,
    hallScale_two_le_eventually hε0, hallSmallScale_eventually hε0,
    hall_finish_eventually, hcollisionEventually] with
      N hQ ht hscale hsmall hfinish hcollision
  intro G _ _ hcard
  let k := erdos1179Size N
  have hδ : 0 < hallDelta ε N := by
    unfold hallDelta
    positivity
  have herror : (hallRounds N + 1 : ℝ) * hallDelta ε N = ε := by
    unfold hallDelta
    field_simp
  have htuple := finite_tuple_success_lower_bound (G := G)
    (hallM N) (hallBlock N) (hallRounds N) ht hδ hsmall hscale herror
    hε1.le (by simpa [hcard] using hfinish)
  rw [hcard] at htuple
  have htupleSuccess :
      1 - hallFailureBound ε N ≤
        tupleSuccessProbability (G := G) ε k := by
    simpa [hallFailureBound, erdos1179Size, hallQ, k] using htuple
  have htupleFailure :
      uniformProbability
          (fun a : Fin k → G ↦ ¬ TupleBalanced ε a) ≤
        hallFailureBound ε N := by
    rw [uniformProbability_not]
    unfold tupleSuccessProbability at htupleSuccess
    linarith
  have hk1 : 1 ≤ k := by
    dsimp [k, erdos1179Size, hallLength]
    omega
  have hNpos : (0 : ℝ) < N := by
    rw [← hcard]
    positivity
  have hkG : k ≤ Fintype.card G := by
    rw [hcard]
    by_contra hnot
    have hNk : (N : ℝ) < k := by
      exact_mod_cast Nat.lt_of_not_ge hnot
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hNksq : (N : ℝ) < (k : ℝ) ^ 2 := by nlinarith
    have hone : (1 : ℝ) < (k : ℝ) ^ 2 / N :=
      (lt_div_iff₀ hNpos).2 (by simpa using hNksq)
    exact (not_lt_of_ge hcollision.le) hone
  have hsetFailure := subset_failure_le_tuple_failure (G := G)
    (ε := ε) hk1 hkG (by simpa [k, hcard] using hcollision)
  have hden : 0 ≤ 1 - (k : ℝ) ^ 2 / Fintype.card G := by
    rw [hcard]
    exact (sub_pos.mpr hcollision).le
  have hsetFailure' :
      uniformProbability
          (fun A : KSubsets G k ↦ ¬ SetBalanced ε A.1) ≤
        subsetFailureBound ε N := by
    calc
      uniformProbability
          (fun A : KSubsets G k ↦ ¬ SetBalanced ε A.1) ≤
          uniformProbability
              (fun a : Fin k → G ↦ ¬ TupleBalanced ε a) /
            (1 - (k : ℝ) ^ 2 / Fintype.card G) := hsetFailure
      _ ≤ hallFailureBound ε N /
            (1 - (k : ℝ) ^ 2 / Fintype.card G) :=
        div_le_div_of_nonneg_right htupleFailure hden
      _ = subsetFailureBound ε N := by
        unfold subsetFailureBound
        rw [hcard]
  letI : Nonempty (KSubsets G k) :=
    Fintype.card_pos_iff.mp (card_KSubsets_pos hkG)
  rw [uniformProbability_not] at hsetFailure'
  unfold subsetSuccessProbability
  linarith

lemma erdos1179Size_le_self_eventually :
    ∀ᶠ N : ℕ in atTop, erdos1179Size N ≤ N := by
  have hcollisionEventually : ∀ᶠ N : ℕ in atTop,
      (erdos1179Size N : ℝ) ^ 2 / N < 1 :=
    size_square_div_tendsto_zero.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hallQ_one_lt_eventually, hcollisionEventually] with
      N hQ hcollision
  have hk1 : 1 ≤ erdos1179Size N := by
    unfold erdos1179Size hallLength
    omega
  have hNpos : (0 : ℝ) < N := by
    have hNnat : 0 < N := by
      by_contra hN
      have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
      subst N
      norm_num [hallQ] at hQ
    exact_mod_cast hNnat
  by_contra hnot
  have hNk : (N : ℝ) < erdos1179Size N := by
    exact_mod_cast Nat.lt_of_not_ge hnot
  have hkR : (1 : ℝ) ≤ erdos1179Size N := by exact_mod_cast hk1
  have hNksq : (N : ℝ) < (erdos1179Size N : ℝ) ^ 2 := by nlinarith
  have hone : (1 : ℝ) < (erdos1179Size N : ℝ) ^ 2 / N :=
    (lt_div_iff₀ hNpos).2 (by simpa using hNksq)
  exact (not_lt_of_ge hcollision.le) hone

lemma subsetSuccessProbability_le_one_of_card {G : Type*}
    [AddCommGroup G] [Fintype G] {ε : ℝ} {k : ℕ}
    (hk : k ≤ Fintype.card G) :
    subsetSuccessProbability (G := G) ε k ≤ 1 := by
  letI : Nonempty (KSubsets G k) :=
    Fintype.card_pos_iff.mp (card_KSubsets_pos hk)
  unfold subsetSuccessProbability uniformProbability
  exact Erdos807.FiniteUniform.probability_le_one _

/-- Along every sequence of finite abelian groups whose orders tend to
infinity, the literal uniform `erdos1179Size |G|`-subset is balanced with
probability tending to one.  This is the probabilistic assertion in Problem
1179, with no restriction on the isomorphism types of the groups. -/
theorem subset_success_tendsto_one
    (G : ℕ → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hcard : Tendsto (fun i ↦ Fintype.card (G i)) atTop atTop) :
    Tendsto (fun i ↦ subsetSuccessProbability (G := G i) ε
      (erdos1179Size (Fintype.card (G i)))) atTop (nhds 1) := by
  have herr := (subsetFailureBound_tendsto_zero hε0).comp hcard
  have hlowerT : Tendsto (fun i ↦
      1 - subsetFailureBound ε (Fintype.card (G i))) atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [Function.comp_apply, sub_zero] using hone.sub herr
  have hlower := hcard.eventually
    (finite_subset_success_lower_bound hε0 hε1)
  have hsize := hcard.eventually erdos1179Size_le_self_eventually
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerT tendsto_const_nhds
    (by
      filter_upwards [hlower] with i hi
      exact hi (G i) rfl)
    (by
      filter_upwards [hsize] with i hi
      exact subsetSuccessProbability_le_one_of_card hi)

/-- **Resolution of Erdős Problem 1179.**

The first clause is the universal lower bound: every balanced set has at least
`log₂ |G|` elements.  The second clause says that the explicit Erdős--Hall
cardinality is `(1 + o(1)) log₂ N`.  The final clause says that this cardinality
works with probability tending to one, uniformly along every growing sequence
of finite abelian groups.  Thus the answer to the question in Problem 1179 is
affirmative. -/
theorem erdos_1179 :
    (∀ (G : Type u) [AddCommGroup G] [Fintype G] (ε : ℝ),
      0 < ε → ε < 1 → ∀ A : Finset G,
        SetBalanced ε A → Fintype.card G ≤ 2 ^ A.card) ∧
    Tendsto (fun N : ℕ ↦
      (erdos1179Size N : ℝ) / Real.logb 2 N) atTop (nhds 1) ∧
    ∀ (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (G : ℕ → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)],
        Tendsto (fun i ↦ Fintype.card (G i)) atTop atTop →
        Tendsto (fun i ↦ subsetSuccessProbability (G := G i) ε
          (erdos1179Size (Fintype.card (G i)))) atTop (nhds 1) := by
  refine ⟨?_, erdos1179Size_asymptotic, ?_⟩
  · intro G _ _ ε hε0 hε1 A hA
    exact balanced_card_le_two_pow hε0 hε1 hA
  · intro ε hε0 hε1 G _ _ hcard
    exact subset_success_tendsto_one G hε0 hε1 hcard

end FinalAssembly

end Erdos1179

#print axioms Erdos1179.erdos_1179

alias _root_.Erdos1179.erdos1179 := _root_.Erdos1179.erdos_1179
