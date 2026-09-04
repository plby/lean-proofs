/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.HostNested

/-!
# All-direction host preparation

This file carries out the second dependent-random-choice induction in Lee's
proof.  At a stage `i` a tuple is sampled from the `i`th set, every other set
is intersected with its common neighbourhood, and the `i`th set is fixed.
The elementary definitions and identities below keep that simultaneous
update literal; subsequent lemmas attach the cardinal and defect invariants.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace HostDirections

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Union of all members of a finite family except the indicated one. -/
def unionExcept {r : ℕ} (A : Fin r → Finset α) (j : Fin r) : Finset α :=
  Finset.univ.biUnion fun k => if k = j then ∅ else A k

@[simp] theorem mem_unionExcept {r : ℕ} (A : Fin r → Finset α)
    (j : Fin r) (x : α) :
    x ∈ unionExcept A j ↔ ∃ k : Fin r, k ≠ j ∧ x ∈ A k := by
  classical
  simp only [unionExcept, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hx⟩
    by_cases hkj : k = j
    · simp [hkj] at hx
    · exact ⟨k, hkj, by simpa [hkj] using hx⟩
  · rintro ⟨k, hkj, hx⟩
    exact ⟨k, by simpa [hkj] using hx⟩

theorem subset_unionExcept {r : ℕ} (A : Fin r → Finset α)
    {j k : Fin r} (hkj : k ≠ j) : A k ⊆ unionExcept A j := by
  intro x hx
  exact mem_unionExcept A j x |>.2 ⟨k, hkj, hx⟩

theorem unionExcept_subset_univ {r : ℕ} (A : Fin r → Finset α)
    (j : Fin r) : unionExcept A j ⊆ Finset.univ := by
  exact Finset.subset_univ _

theorem card_unionExcept_le {r : ℕ} (A : Fin r → Finset α)
    (j : Fin r) : (unionExcept A j).card ≤ Fintype.card α := by
  simpa using Finset.card_le_card (unionExcept_subset_univ A j)

/-- Keep one set and intersect every other set with the common neighbourhood
of the sampled tuple. -/
def intersectOthers (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i : Fin r) (x : Fin t → α) :
    Fin r → Finset α := fun j =>
  if j = i then A j else FiniteDefect.commonNeighbors G x (A j)

@[simp] theorem intersectOthers_self (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i : Fin r) (x : Fin t → α) :
    intersectOthers G A i x i = A i := by
  simp [intersectOthers]

theorem intersectOthers_of_ne (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i j : Fin r) (x : Fin t → α)
    (hji : j ≠ i) :
    intersectOthers G A i x j = FiniteDefect.commonNeighbors G x (A j) := by
  simp [intersectOthers, hji]

theorem intersectOthers_subset (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i j : Fin r) (x : Fin t → α) :
    intersectOthers G A i x j ⊆ A j := by
  by_cases hji : j = i
  · subst j
    simp
  · rw [intersectOthers_of_ne G A i j x hji]
    exact Defect.commonNeighbors_subset_target G x (A j)

/-- Common neighbourhood distributes over the finite union of all other
parts.  This identifies the raw reverse-direction defect supplied by DRC
with the new union-except product. -/
theorem unionExcept_intersectOthers_self
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i : Fin r) (x : Fin t → α) :
    unionExcept (intersectOthers G A i x) i =
      FiniteDefect.commonNeighbors G x (unionExcept A i) := by
  classical
  ext z
  simp only [mem_unionExcept, FiniteDefect.commonNeighbors,
    Defect.mem_commonNeighbors]
  constructor
  · rintro ⟨k, hki, hzk⟩
    rw [intersectOthers_of_ne G A i k x hki] at hzk
    change z ∈ Defect.commonNeighbors G x (A k) at hzk
    rw [Defect.mem_commonNeighbors] at hzk
    exact ⟨⟨k, hki, hzk.1⟩, hzk.2⟩
  · rintro ⟨hz, hx⟩
    obtain ⟨k, hki, hzk⟩ := hz
    refine ⟨k, hki, ?_⟩
    rw [intersectOthers_of_ne G A i k x hki,
      FiniteDefect.commonNeighbors, Defect.mem_commonNeighbors]
    exact ⟨hzk, hx⟩

theorem unionExcept_mono {r : ℕ} {A B : Fin r → Finset α}
    (hAB : ∀ j, A j ⊆ B j) (i : Fin r) :
    unionExcept A i ⊆ unionExcept B i := by
  intro z hz
  obtain ⟨j, hji, hzj⟩ := (mem_unionExcept A i z).1 hz
  exact (mem_unionExcept B i z).2 ⟨j, hji, hAB j hzj⟩

/-! ## The induction invariant -/

/-- Invariant after the indices `< stage` have been processed.  Future sets
retain the larger reserve `L`; processed sets retain the final reserve `τ`.
The tuple dimension decreases at each stage. -/
structure DirectionState
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (r stage L τ θ s dim : ℕ) (ε : ℝ) where
  sets : Fin r → Finset α
  future_card : ∀ j : Fin r, stage ≤ j.1 → L ≤ (sets j).card
  done_card : ∀ j : Fin r, j.1 < stage → τ ≤ (sets j).card
  future_nested : ∀ j : ℕ, stage ≤ j → ∀ hj : j + 1 < r,
    sets ⟨j, (Nat.lt_succ_self j).trans hj⟩ ⊆ sets ⟨j + 1, hj⟩
  future_moment : ∀ j : ℕ, stage ≤ j → ∀ hj : j + 1 < r,
    FiniteDefect.moment G L 0
      (fun _ : Fin dim => sets ⟨j, (Nat.lt_succ_self j).trans hj⟩)
      (sets ⟨j + 1, hj⟩) ≤ ε
  done_moment : ∀ j : Fin r, j.1 < stage →
    FiniteDefect.moment G θ s
      (fun _ : Fin dim => unionExcept sets j) (sets j) ≤ ε

theorem DirectionState.card_pos_of_future
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r stage L τ θ s dim : ℕ} {ε : ℝ}
    (S : DirectionState G r stage L τ θ s dim ε)
    (hL : 0 < L) (j : Fin r) (hj : stage ≤ j.1) :
    (S.sets j).Nonempty := by
  exact Finset.card_pos.mp (hL.trans_le (S.future_card j hj))

theorem DirectionState.card_pos_of_done
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r stage L τ θ s dim : ℕ} {ε : ℝ}
    (S : DirectionState G r stage L τ θ s dim ε)
    (hτ : 0 < τ) (j : Fin r) (hj : j.1 < stage) :
    (S.sets j).Nonempty := by
  exact Finset.card_pos.mp (hτ.trans_le (S.done_card j hj))

/-- Transitive form of the nesting invariant among unprocessed sets. -/
theorem DirectionState.future_subset
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r stage L τ θ s dim : ℕ} {ε : ℝ}
    (S : DirectionState G r stage L τ θ s dim ε)
    {a b : ℕ} (hstage : stage ≤ a) (hab : a ≤ b) (hb : b < r) :
    S.sets ⟨a, hab.trans_lt hb⟩ ⊆ S.sets ⟨b, hb⟩ := by
  induction b, hab using Nat.le_induction with
  | base => exact subset_rfl
  | succ b hab ih =>
      exact (ih (by omega)).trans (S.future_nested b (hstage.trans hab) hb)

theorem DirectionState.unionExcept_nonempty
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r stage L τ θ s dim : ℕ} {ε : ℝ}
    (S : DirectionState G r stage L τ θ s dim ε)
    (hr : 2 ≤ r) (hL : 0 < L) (hτ : 0 < τ)
    (i : Fin r) : (unionExcept S.sets i).Nonempty := by
  classical
  by_cases hi0 : i.1 = 0
  · let k : Fin r := ⟨1, hr⟩
    have hki : k ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp [k, hi0] at this
    have hkstage : stage ≤ k.1 ∨ k.1 < stage := by omega
    rcases hkstage with hk | hk
    · exact (S.card_pos_of_future G hL k hk).mono
        (subset_unionExcept S.sets hki)
    · exact (S.card_pos_of_done G hτ k hk).mono
        (subset_unionExcept S.sets hki)
  · let k : Fin r := ⟨0, by omega⟩
    have hki : k ≠ i := by
      intro h
      apply hi0
      exact (congrArg Fin.val h).symm
    have hkstage : stage ≤ k.1 ∨ k.1 < stage := by omega
    rcases hkstage with hk | hk
    · exact (S.card_pos_of_future G hL k hk).mono
        (subset_unionExcept S.sets hki)
    · exact (S.card_pos_of_done G hτ k hk).mono
        (subset_unionExcept S.sets hki)

/-- Package one sampled tuple once its cardinal and moment inequalities have
been established.  This lemma is deterministic; the next section obtains
the hypotheses by finite averaging. -/
def DirectionState.next_of_good_sample
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r i L τ θ s dim t : ℕ} {ε ε' : ℝ}
    (S : DirectionState G r i L τ θ s (dim + t) ε)
    (hi : i < r) (hτL : τ ≤ L) (x : Fin t → α)
    (hfutureCard : ∀ j : Fin r, i < j.1 →
      L ≤ (intersectOthers G S.sets ⟨i, hi⟩ x j).card)
    (hdoneCard : ∀ j : Fin r, j.1 < i →
      τ ≤ (intersectOthers G S.sets ⟨i, hi⟩ x j).card)
    (hfutureMoment : ∀ j : ℕ, i + 1 ≤ j → ∀ hj : j + 1 < r,
      FiniteDefect.moment G L 0
        (fun _ : Fin dim =>
          intersectOthers G S.sets ⟨i, hi⟩ x
            ⟨j, (Nat.lt_succ_self j).trans hj⟩)
        (intersectOthers G S.sets ⟨i, hi⟩ x ⟨j + 1, hj⟩) ≤ ε')
    (holdMoment : ∀ j : Fin r, j.1 < i →
      FiniteDefect.moment G θ s
        (fun _ : Fin dim =>
          unionExcept (intersectOthers G S.sets ⟨i, hi⟩ x) j)
        (intersectOthers G S.sets ⟨i, hi⟩ x j) ≤ ε')
    (hnewMoment : FiniteDefect.moment G θ s
      (fun _ : Fin dim =>
        unionExcept (intersectOthers G S.sets ⟨i, hi⟩ x) ⟨i, hi⟩)
      (intersectOthers G S.sets ⟨i, hi⟩ x ⟨i, hi⟩) ≤ ε') :
    DirectionState G r (i + 1) L τ θ s dim ε' := by
  let A := intersectOthers G S.sets ⟨i, hi⟩ x
  refine {
    sets := A
    future_card := ?_
    done_card := ?_
    future_nested := ?_
    future_moment := ?_
    done_moment := ?_ }
  · intro j hj
    exact hfutureCard j (by omega)
  · intro j hj
    by_cases hji : j.1 = i
    · subst i
      rw [show A j = S.sets j by simp [A]]
      exact hτL.trans (S.future_card j (by omega))
    · exact hdoneCard j (by omega)
  · intro j hj hjr
    have hji : (⟨j, (Nat.lt_succ_self j).trans hjr⟩ : Fin r) ≠ ⟨i, hi⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have hsucc : (⟨j + 1, hjr⟩ : Fin r) ≠ ⟨i, hi⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    rw [show A ⟨j, (Nat.lt_succ_self j).trans hjr⟩ =
        FiniteDefect.commonNeighbors G x
          (S.sets ⟨j, (Nat.lt_succ_self j).trans hjr⟩) by
      exact intersectOthers_of_ne G S.sets ⟨i, hi⟩ _ x hji,
      show A ⟨j + 1, hjr⟩ = FiniteDefect.commonNeighbors G x
          (S.sets ⟨j + 1, hjr⟩) by
        exact intersectOthers_of_ne G S.sets ⟨i, hi⟩ _ x hsucc]
    exact Defect.commonNeighbors_mono_target G x
      (S.future_nested j (by omega) hjr)
  · exact hfutureMoment
  · intro j hj
    by_cases hji : j.1 = i
    · have hjeq : j = ⟨i, hi⟩ := Fin.ext hji
      subst j
      exact hnewMoment
    · exact holdMoment j (by omega)

/-! ## A single simultaneous-selection objective -/

noncomputable def cardinalCost
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i : Fin r)
    (L τ : ℕ) (x : Fin t → α) (j : Fin r) : ℝ :=
  if j = i then 0 else if i.1 < j.1 then
    DRC.indicator ((intersectOthers G A i x j).card < L)
  else DRC.indicator ((intersectOthers G A i x j).card < τ)

noncomputable def futureRawCost
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i : Fin r)
    (L dim : ℕ) (ε' : ℝ) (x : Fin t → α) (j : Fin r) : ℝ :=
  if h : i.1 < j.1 ∧ j.1 + 1 < r then
    DRC.rawMoment G L 0 dim (intersectOthers G A i x j)
      (intersectOthers G A i x ⟨j.1 + 1, h.2⟩) /
        ((L : ℝ) ^ dim * ε')
  else 0

noncomputable def doneRawCost
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i : Fin r)
    (θ s dim τ : ℕ) (ε' : ℝ) (x : Fin t → α) (j : Fin r) : ℝ :=
  if j.1 ≤ i.1 then
    DRC.rawMoment G θ s dim
      (unionExcept (intersectOthers G A i x) j)
      (intersectOthers G A i x j) /
        ((τ : ℝ) ^ dim * ε')
  else 0

noncomputable def updateCost
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i : Fin r)
    (L τ θ s dim : ℕ) (ε' : ℝ) (x : Fin t → α) : ℝ :=
  ∑ j, (cardinalCost G A i L τ x j +
    futureRawCost G A i L dim ε' x j +
    doneRawCost G A i θ s dim τ ε' x j)

theorem cardinalCost_nonneg
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i : Fin r)
    (L τ : ℕ) (x : Fin t → α) (j : Fin r) :
    0 ≤ cardinalCost G A i L τ x j := by
  unfold cardinalCost
  split_ifs
  · exact le_rfl
  · exact DRC.indicator_nonneg _
  · exact DRC.indicator_nonneg _

theorem futureRawCost_nonneg
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i : Fin r)
    (L dim : ℕ) {ε' : ℝ} (hε' : 0 < ε')
    (x : Fin t → α) (j : Fin r) :
    0 ≤ futureRawCost G A i L dim ε' x j := by
  unfold futureRawCost
  split_ifs
  · exact div_nonneg (by
      unfold DRC.rawMoment
      exact Finset.sum_nonneg fun q _ =>
        FiniteDefect.defectPower_nonneg G L q _ 0)
      (mul_nonneg (by positivity) hε'.le)
  · exact le_rfl

theorem doneRawCost_nonneg
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i : Fin r)
    (θ s dim τ : ℕ) {ε' : ℝ} (hε' : 0 < ε')
    (x : Fin t → α) (j : Fin r) :
    0 ≤ doneRawCost G A i θ s dim τ ε' x j := by
  unfold doneRawCost
  split_ifs
  · exact div_nonneg (by
      unfold DRC.rawMoment
      exact Finset.sum_nonneg fun q _ =>
        FiniteDefect.defectPower_nonneg G θ q _ s)
      (mul_nonneg (by positivity) hε'.le)
  · exact le_rfl

theorem updateCost_nonneg
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r t : ℕ} (A : Fin r → Finset α) (i : Fin r)
    (L τ θ s dim : ℕ) {ε' : ℝ} (hε' : 0 < ε')
    (x : Fin t → α) :
    0 ≤ updateCost G A i L τ θ s dim ε' x := by
  unfold updateCost
  exact Finset.sum_nonneg fun j _ => add_nonneg
    (add_nonneg (cardinalCost_nonneg G A i L τ x j)
      (futureRawCost_nonneg G A i L dim hε' x j))
    (doneRawCost_nonneg G A i θ s dim τ hε' x j)

theorem expect_cardinalCost_le
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r i L τ s dim t K : ℕ} {ε : ℝ}
    (S : DirectionState G r i L τ τ s (dim + t) ε)
    (hi : i < r) (hτ : 0 < τ) (hτL : τ ≤ L) (hε : 0 ≤ ε)
    (hglobal : Fintype.card α ≤ K * τ) (j : Fin r) :
    (𝔼 x ∈ FiniteDefect.samples t (S.sets ⟨i, hi⟩),
      cardinalCost G S.sets ⟨i, hi⟩ L τ x j) ≤
        (K : ℝ) ^ t * ε := by
  classical
  let ii : Fin r := ⟨i, hi⟩
  by_cases hji : j = ii
  · subst j
    have hrhs : 0 ≤ (K : ℝ) ^ t * ε :=
      mul_nonneg (pow_nonneg (Nat.cast_nonneg K) t) hε
    simpa [ii, cardinalCost] using hrhs
  by_cases hfuture : i < j.1
  · have hjpos : 0 < j.1 := by omega
    let p : ℕ := j.1 - 1
    have hp : p + 1 = j.1 := by omega
    have hpi : i ≤ p := by omega
    have hpR : p + 1 < r := by simpa [hp] using j.2
    let prev : Fin r := ⟨p, (Nat.lt_succ_self p).trans hpR⟩
    have hsub : S.sets ii ⊆ S.sets prev := by
      exact S.future_subset G (a := i) (b := p) (by omega) hpi
        ((Nat.lt_succ_self p).trans hpR)
    have hBi : (S.sets ii).Nonempty := by
      exact Finset.card_pos.mp ((hτ.trans_le hτL).trans_le
        (S.future_card ii (by exact le_rfl)))
    have hcard : (S.sets prev).card ≤ K * (S.sets ii).card := by
      calc
        (S.sets prev).card ≤ Fintype.card α := by
          simpa using Finset.card_le_card (Finset.subset_univ _)
        _ ≤ K * τ := hglobal
        _ ≤ K * (S.sets ii).card :=
          Nat.mul_le_mul_left K (hτL.trans (S.future_card ii (by exact le_rfl)))
    have hmoment := HostTools.moment_subsample_dimension_le G hBi hsub L 0 K
      (d := t) (e := dim + t) (by omega) hcard (S.sets j)
    have hchain : FiniteDefect.moment G L 0
        (fun _ : Fin (dim + t) => S.sets prev) (S.sets j) ≤ ε := by
      have := S.future_moment p hpi hpR
      simpa [prev, hp, Fin.ext_iff] using this
    calc
      (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
          cardinalCost G S.sets ii L τ x j) =
          FiniteDefect.moment G L 0
            (fun _ : Fin t => S.sets ii) (S.sets j) := by
              rw [HostTools.moment_zero_eq_expect_indicator]
              apply Finset.expect_congr rfl
              intro x hx
              simp [cardinalCost, ii, hji, hfuture, intersectOthers]
      _ ≤ (K : ℝ) ^ t * FiniteDefect.moment G L 0
          (fun _ : Fin (dim + t) => S.sets prev) (S.sets j) := hmoment
      _ ≤ (K : ℝ) ^ t * ε :=
        mul_le_mul_of_nonneg_left hchain (pow_nonneg (by positivity) t)
  · have hjlt : j.1 < i := by
      have hne : j.1 ≠ i := by
        intro h
        apply hji
        exact Fin.ext (by simpa [ii] using h)
      omega
    have hsub : S.sets ii ⊆ unionExcept S.sets j :=
      subset_unionExcept S.sets (by
        intro h
        apply hji
        exact h.symm)
    have hBi : (S.sets ii).Nonempty := by
      exact Finset.card_pos.mp ((hτ.trans_le hτL).trans_le
        (S.future_card ii (by exact le_rfl)))
    have hcard : (unionExcept S.sets j).card ≤ K * (S.sets ii).card := by
      calc
        (unionExcept S.sets j).card ≤ Fintype.card α := card_unionExcept_le _ _
        _ ≤ K * τ := hglobal
        _ ≤ K * (S.sets ii).card :=
          Nat.mul_le_mul_left K (hτL.trans (S.future_card ii (by exact le_rfl)))
    have hdim := HostTools.moment_subsample_dimension_le G hBi hsub τ 0 K
      (d := t) (e := dim + t) (by omega) hcard (S.sets j)
    have hexp := FiniteDefect.moment_mono_exponent G τ
      (fun _ : Fin (dim + t) => unionExcept S.sets j) (S.sets j)
      (Nat.zero_le s)
    have hdone := S.done_moment j hjlt
    calc
      (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
          cardinalCost G S.sets ii L τ x j) =
          FiniteDefect.moment G τ 0
            (fun _ : Fin t => S.sets ii) (S.sets j) := by
              rw [HostTools.moment_zero_eq_expect_indicator]
              apply Finset.expect_congr rfl
              intro x hx
              simp [cardinalCost, ii, hji, hfuture, intersectOthers]
      _ ≤ (K : ℝ) ^ t * FiniteDefect.moment G τ 0
          (fun _ : Fin (dim + t) => unionExcept S.sets j) (S.sets j) := hdim
      _ ≤ (K : ℝ) ^ t * FiniteDefect.moment G τ s
          (fun _ : Fin (dim + t) => unionExcept S.sets j) (S.sets j) :=
        mul_le_mul_of_nonneg_left hexp (pow_nonneg (by positivity) t)
      _ ≤ (K : ℝ) ^ t * ε :=
        mul_le_mul_of_nonneg_left hdone (pow_nonneg (by positivity) t)

theorem expect_futureRawCost_le
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r i L τ s dim t K : ℕ} {ε ε' : ℝ}
    (S : DirectionState G r i L τ τ s (dim + t) ε)
    (hi : i < r) (hK : 1 ≤ K) (hτ : 0 < τ) (hτL : τ ≤ L)
    (hε : 0 ≤ ε) (hε' : 0 < ε')
    (hglobal : Fintype.card α ≤ K * τ) (j : Fin r) :
    (𝔼 x ∈ FiniteDefect.samples t (S.sets ⟨i, hi⟩),
      futureRawCost G S.sets ⟨i, hi⟩ L dim ε' x j) ≤
        (K : ℝ) ^ (dim + (dim + t)) * ε / ε' := by
  classical
  let ii : Fin r := ⟨i, hi⟩
  by_cases hcond : i < j.1 ∧ j.1 + 1 < r
  · let jn : Fin r := ⟨j.1 + 1, hcond.2⟩
    have hji : j ≠ ii := by
      intro h
      have hv := congrArg Fin.val h
      simp [ii] at hv
      omega
    have hjni : jn ≠ ii := by
      intro h
      have hv := congrArg Fin.val h
      simp [jn, ii] at hv
      omega
    have hBi : (S.sets ii).Nonempty := by
      exact Finset.card_pos.mp ((hτ.trans_le hτL).trans_le
        (S.future_card ii (by exact le_rfl)))
    have hBj : (S.sets j).Nonempty := by
      exact Finset.card_pos.mp ((hτ.trans_le hτL).trans_le
        (S.future_card j hcond.1.le))
    have hsubij : S.sets ii ⊆ S.sets j := by
      exact S.future_subset G (a := i) (b := j.1) (by exact le_rfl)
        hcond.1.le j.2
    have hcardij : (S.sets j).card ≤ K * (S.sets ii).card := by
      calc
        (S.sets j).card ≤ Fintype.card α := by
          simpa using Finset.card_le_card (Finset.subset_univ _)
        _ ≤ K * τ := hglobal
        _ ≤ K * (S.sets ii).card :=
          Nat.mul_le_mul_left K (hτL.trans (S.future_card ii le_rfl))
    let P : Fin (dim + t) → Finset α :=
      HostTools.appendTupleSets (D := dim) (t := t) (S.sets j) (S.sets ii)
    let Q : Fin (dim + t) → Finset α := fun _ => S.sets j
    have hP : ∀ k, (P k).Nonempty := by
      intro k
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) k
      · simpa [P, HostTools.appendTupleSets] using hBj
      · simpa [P, HostTools.appendTupleSets] using hBi
    have hPQ : ∀ k, P k ⊆ Q k := by
      intro k
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) k
      · simp [P, Q, HostTools.appendTupleSets]
      · simpa [P, Q, HostTools.appendTupleSets] using hsubij
    have hcardPQ : ∀ k, (Q k).card ≤ K * (P k).card := by
      intro k
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) k
      · simpa [P, Q, HostTools.appendTupleSets] using
          Nat.mul_le_mul_right (S.sets j).card hK
      · simpa [P, Q, HostTools.appendTupleSets] using hcardij
    have hfamily := HostTools.familyMoment_le_pow_mul_of_subset G L 0 K
      hP hPQ hcardPQ (S.sets jn)
    have happend : FiniteDefect.moment G L 0 P (S.sets jn) ≤
        (K : ℝ) ^ (dim + t) *
          FiniteDefect.moment G L 0 Q (S.sets jn) := by
      simpa [FiniteDefect.familyMoment_fin, P, Q] using hfamily
    have hchain : FiniteDefect.moment G L 0 Q (S.sets jn) ≤ ε := by
      have hc := S.future_moment j.1 hcond.1.le hcond.2
      simpa [Q, jn] using hc
    have hmomentAppend : FiniteDefect.moment G L 0 P (S.sets jn) ≤
        (K : ℝ) ^ (dim + t) * ε :=
      happend.trans (mul_le_mul_of_nonneg_left hchain
        (pow_nonneg (Nat.cast_nonneg K) _))
    have hpoint : ∀ x ∈ FiniteDefect.samples t (S.sets ii),
        DRC.rawMoment G L 0 dim
          (intersectOthers G S.sets ii x j)
          (intersectOthers G S.sets ii x jn) ≤
        DRC.rawMoment G L 0 dim (S.sets j)
          (FiniteDefect.commonNeighbors G x (S.sets jn)) := by
      intro x hx
      rw [intersectOthers_of_ne G S.sets ii jn x hjni]
      exact HostTools.rawMoment_mono_coordinates G L 0 dim
        (intersectOthers_subset G S.sets ii j x) _
    have hmeanRaw : (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
        DRC.rawMoment G L 0 dim
          (intersectOthers G S.sets ii x j)
          (intersectOthers G S.sets ii x jn)) ≤
        ((S.sets j).card : ℝ) ^ dim *
          ((K : ℝ) ^ (dim + t) * ε) := by
      calc
        (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
            DRC.rawMoment G L 0 dim
              (intersectOthers G S.sets ii x j)
              (intersectOthers G S.sets ii x jn)) ≤
            𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
              DRC.rawMoment G L 0 dim (S.sets j)
                (FiniteDefect.commonNeighbors G x (S.sets jn)) :=
          Finset.expect_le_expect hpoint
        _ = ((S.sets j).card : ℝ) ^ dim *
            (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
              FiniteDefect.moment G L 0 (fun _ : Fin dim => S.sets j)
                (FiniteDefect.commonNeighbors G x (S.sets jn))) := by
          simp_rw [DRC.rawMoment_eq_card_pow_mul_moment]
          exact HostTools.expect_const_mul _ _ _
        _ = ((S.sets j).card : ℝ) ^ dim *
            FiniteDefect.moment G L 0 P (S.sets jn) := by
          rw [HostTools.expect_moment_commonNeighbors]
        _ ≤ ((S.sets j).card : ℝ) ^ dim *
            ((K : ℝ) ^ (dim + t) * ε) :=
          mul_le_mul_of_nonneg_left hmomentAppend (pow_nonneg (by positivity) _)
    have hBjcard : (S.sets j).card ≤ K * L := by
      calc
        (S.sets j).card ≤ Fintype.card α := by
          simpa using Finset.card_le_card (Finset.subset_univ _)
        _ ≤ K * τ := hglobal
        _ ≤ K * L := Nat.mul_le_mul_left K hτL
    have hBjpow : ((S.sets j).card : ℝ) ^ dim ≤
        (K : ℝ) ^ dim * (L : ℝ) ^ dim := by
      have hn := Nat.pow_le_pow_left hBjcard dim
      have hc : ((S.sets j).card : ℝ) ^ dim ≤
          (((K * L : ℕ) : ℝ) ^ dim) := by exact_mod_cast hn
      simpa [Nat.cast_mul, mul_pow] using hc
    have hrawBound : (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
        DRC.rawMoment G L 0 dim
          (intersectOthers G S.sets ii x j)
          (intersectOthers G S.sets ii x jn)) ≤
        (L : ℝ) ^ dim * ((K : ℝ) ^ (dim + (dim + t)) * ε) := by
      calc
        _ ≤ ((S.sets j).card : ℝ) ^ dim *
            ((K : ℝ) ^ (dim + t) * ε) := hmeanRaw
        _ ≤ ((K : ℝ) ^ dim * (L : ℝ) ^ dim) *
            ((K : ℝ) ^ (dim + t) * ε) :=
          mul_le_mul_of_nonneg_right hBjpow
            (mul_nonneg (pow_nonneg (Nat.cast_nonneg K) _) hε)
        _ = (L : ℝ) ^ dim * ((K : ℝ) ^ (dim + (dim + t)) * ε) := by
          rw [pow_add]
          ring
    have hden : (0 : ℝ) < (L : ℝ) ^ dim * ε' := by
      have hL : 0 < L := hτ.trans_le hτL
      positivity
    calc
      (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
          futureRawCost G S.sets ii L dim ε' x j) =
          (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
            DRC.rawMoment G L 0 dim
              (intersectOthers G S.sets ii x j)
              (intersectOthers G S.sets ii x jn)) /
                ((L : ℝ) ^ dim * ε') := by
        rw [Finset.expect_div]
        apply Finset.expect_congr rfl
        intro x hx
        have hijFin : ii < j := by
          change i < j.1
          exact hcond.1
        simp [futureRawCost, hijFin, hcond.2, jn]
      _ ≤ ((L : ℝ) ^ dim *
          ((K : ℝ) ^ (dim + (dim + t)) * ε)) /
            ((L : ℝ) ^ dim * ε') :=
        div_le_div_of_nonneg_right hrawBound hden.le
      _ = (K : ℝ) ^ (dim + (dim + t)) * ε / ε' := by
        have hLpow : (L : ℝ) ^ dim ≠ 0 := by
          exact pow_ne_zero _ (Nat.cast_ne_zero.mpr
            (Nat.ne_of_gt (hτ.trans_le hτL)))
        field_simp
  · have hzero : ∀ x : Fin t → α,
        futureRawCost G S.sets ⟨i, hi⟩ L dim ε' x j = 0 := by
      intro x
      simp [futureRawCost, hcond]
    rw [show (𝔼 x ∈ FiniteDefect.samples t (S.sets ⟨i, hi⟩),
      futureRawCost G S.sets ⟨i, hi⟩ L dim ε' x j) = 0 by
        apply Finset.expect_eq_zero
        intro x hx
        exact hzero x]
    exact div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg K) _) hε)
      hε'.le

theorem expect_doneRawCost_le
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r i L τ s dim t K : ℕ} {ε ε' η : ℝ}
    (S : DirectionState G r i L τ τ s (dim + t) ε)
    (hi : i < r) (hK : 1 ≤ K) (hτ : 0 < τ) (hτL : τ ≤ L)
    (ht : 0 < t) (hst : s ≤ t) (hε : 0 ≤ ε) (hε' : 0 < ε')
    (hη : 0 ≤ η) (hglobal : Fintype.card α ≤ K * τ)
    (hthreshold : (τ : ℝ) ≤ η * (S.sets ⟨i, hi⟩).card)
    (j : Fin r) :
    (𝔼 x ∈ FiniteDefect.samples t (S.sets ⟨i, hi⟩),
      doneRawCost G S.sets ⟨i, hi⟩ τ s dim τ ε' x j) ≤
        (K : ℝ) ^ (dim + (dim + t)) * ε / ε' +
          (K : ℝ) ^ dim * η ^ t / ε' := by
  classical
  let ii : Fin r := ⟨i, hi⟩
  have hBi : (S.sets ii).Nonempty := by
    exact Finset.card_pos.mp ((hτ.trans_le hτL).trans_le
      (S.future_card ii le_rfl))
  by_cases hdone : j.1 ≤ i
  · by_cases hji : j = ii
    · subst j
      have hmeanRaw := DRC.expect_rawMoment_le G hBi ht hst hη
        (by norm_num : (0 : ℝ) ≤ 1) (by simpa [ii] using hthreshold)
        (B := unionExcept S.sets ii) (D := dim)
      have hident : ∀ x : Fin t → α,
          DRC.rawMoment G τ s dim
            (unionExcept (intersectOthers G S.sets ii x) ii)
            (intersectOthers G S.sets ii x ii) =
          DRC.rawMoment G τ s dim
            (FiniteDefect.commonNeighbors G x (unionExcept S.sets ii))
            (S.sets ii) := by
        intro x
        rw [unionExcept_intersectOthers_self, intersectOthers_self]
      have hUcard : (unionExcept S.sets ii).card ≤ K * τ := by
        exact (card_unionExcept_le _ _).trans hglobal
      have hUpow : ((unionExcept S.sets ii).card : ℝ) ^ dim ≤
          (K : ℝ) ^ dim * (τ : ℝ) ^ dim := by
        have hn := Nat.pow_le_pow_left hUcard dim
        have hc : ((unionExcept S.sets ii).card : ℝ) ^ dim ≤
            (((K * τ : ℕ) : ℝ) ^ dim) := by exact_mod_cast hn
        simpa [Nat.cast_mul, mul_pow] using hc
      have hrawBound : (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
          DRC.rawMoment G τ s dim
            (unionExcept (intersectOthers G S.sets ii x) ii)
            (intersectOthers G S.sets ii x ii)) ≤
          (τ : ℝ) ^ dim * ((K : ℝ) ^ dim * η ^ t) := by
        calc
          _ = 𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
              DRC.rawMoment G τ s dim
                (FiniteDefect.commonNeighbors G x (unionExcept S.sets ii))
                (S.sets ii) := by
            apply Finset.expect_congr rfl
            intro x hx
            exact hident x
          _ ≤ ((unionExcept S.sets ii).card : ℝ) ^ dim * η ^ t := by
            simpa using hmeanRaw
          _ ≤ ((K : ℝ) ^ dim * (τ : ℝ) ^ dim) * η ^ t :=
            mul_le_mul_of_nonneg_right hUpow (pow_nonneg hη t)
          _ = (τ : ℝ) ^ dim * ((K : ℝ) ^ dim * η ^ t) := by ring
      have hden : (0 : ℝ) < (τ : ℝ) ^ dim * ε' := by positivity
      have hnewBound : (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
          doneRawCost G S.sets ii τ s dim τ ε' x ii) ≤
          (K : ℝ) ^ dim * η ^ t / ε' := by
        calc
          _ = (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
              DRC.rawMoment G τ s dim
                (unionExcept (intersectOthers G S.sets ii x) ii)
                (intersectOthers G S.sets ii x ii)) /
                  ((τ : ℝ) ^ dim * ε') := by
            rw [Finset.expect_div]
            apply Finset.expect_congr rfl
            intro x hx
            simp [doneRawCost, ii]
          _ ≤ ((τ : ℝ) ^ dim * ((K : ℝ) ^ dim * η ^ t)) /
                ((τ : ℝ) ^ dim * ε') :=
            div_le_div_of_nonneg_right hrawBound hden.le
          _ = (K : ℝ) ^ dim * η ^ t / ε' := by
            have hτpow : (τ : ℝ) ^ dim ≠ 0 := pow_ne_zero _
              (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hτ))
            field_simp
      exact hnewBound.trans (le_add_of_nonneg_left
        (div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg K) _) hε)
          hε'.le))
    · have hjlt : j.1 < i := by
        have hne : j.1 ≠ i := by
          intro h
          apply hji
          exact Fin.ext (by simpa [ii] using h)
        omega
      let U := unionExcept S.sets j
      have hU : U.Nonempty := S.unionExcept_nonempty G (by omega) (hτ.trans_le hτL)
        hτ j
      have hsubi : S.sets ii ⊆ U := subset_unionExcept S.sets (by
        intro h
        apply hji
        exact h.symm)
      have hcardUi : U.card ≤ K * (S.sets ii).card := by
        calc
          U.card ≤ Fintype.card α := card_unionExcept_le _ _
          _ ≤ K * τ := hglobal
          _ ≤ K * (S.sets ii).card := Nat.mul_le_mul_left K
            (hτL.trans (S.future_card ii le_rfl))
      let P : Fin (dim + t) → Finset α :=
        HostTools.appendTupleSets (D := dim) (t := t) U (S.sets ii)
      let Q : Fin (dim + t) → Finset α := fun _ => U
      have hP : ∀ k, (P k).Nonempty := by
        intro k
        refine Fin.addCases (fun _ => ?_) (fun _ => ?_) k
        · simpa [P, HostTools.appendTupleSets] using hU
        · simpa [P, HostTools.appendTupleSets] using hBi
      have hPQ : ∀ k, P k ⊆ Q k := by
        intro k
        refine Fin.addCases (fun _ => ?_) (fun _ => ?_) k
        · simp [P, Q, HostTools.appendTupleSets]
        · simpa [P, Q, HostTools.appendTupleSets] using hsubi
      have hcardPQ : ∀ k, (Q k).card ≤ K * (P k).card := by
        intro k
        refine Fin.addCases (fun _ => ?_) (fun _ => ?_) k
        · simpa [P, Q, HostTools.appendTupleSets] using
            Nat.mul_le_mul_right U.card hK
        · simpa [P, Q, HostTools.appendTupleSets] using hcardUi
      have hfamily := HostTools.familyMoment_le_pow_mul_of_subset G τ s K
        hP hPQ hcardPQ (S.sets j)
      have happend : FiniteDefect.moment G τ s P (S.sets j) ≤
          (K : ℝ) ^ (dim + t) * FiniteDefect.moment G τ s Q (S.sets j) := by
        simpa [FiniteDefect.familyMoment_fin, P, Q] using hfamily
      have hdoneMoment : FiniteDefect.moment G τ s Q (S.sets j) ≤ ε := by
        simpa [Q, U] using S.done_moment j hjlt
      have hmomentAppend : FiniteDefect.moment G τ s P (S.sets j) ≤
          (K : ℝ) ^ (dim + t) * ε := happend.trans
        (mul_le_mul_of_nonneg_left hdoneMoment
          (pow_nonneg (Nat.cast_nonneg K) _))
      have hpoint : ∀ x ∈ FiniteDefect.samples t (S.sets ii),
          DRC.rawMoment G τ s dim
            (unionExcept (intersectOthers G S.sets ii x) j)
            (intersectOthers G S.sets ii x j) ≤
          DRC.rawMoment G τ s dim U
            (FiniteDefect.commonNeighbors G x (S.sets j)) := by
        intro x hx
        rw [intersectOthers_of_ne G S.sets ii j x (by
          intro h
          exact hji h)]
        exact HostTools.rawMoment_mono_coordinates G τ s dim
          (unionExcept_mono (fun k => intersectOthers_subset G S.sets ii k x) j) _
      have hmeanRaw : (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
          DRC.rawMoment G τ s dim
            (unionExcept (intersectOthers G S.sets ii x) j)
            (intersectOthers G S.sets ii x j)) ≤
          (U.card : ℝ) ^ dim * ((K : ℝ) ^ (dim + t) * ε) := by
        calc
          _ ≤ 𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
              DRC.rawMoment G τ s dim U
                (FiniteDefect.commonNeighbors G x (S.sets j)) :=
            Finset.expect_le_expect hpoint
          _ = (U.card : ℝ) ^ dim *
              (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
                FiniteDefect.moment G τ s (fun _ : Fin dim => U)
                  (FiniteDefect.commonNeighbors G x (S.sets j))) := by
            simp_rw [DRC.rawMoment_eq_card_pow_mul_moment]
            exact HostTools.expect_const_mul _ _ _
          _ = (U.card : ℝ) ^ dim * FiniteDefect.moment G τ s P (S.sets j) := by
            rw [HostTools.expect_moment_commonNeighbors]
          _ ≤ (U.card : ℝ) ^ dim * ((K : ℝ) ^ (dim + t) * ε) :=
            mul_le_mul_of_nonneg_left hmomentAppend (pow_nonneg (by positivity) _)
      have hUcard : U.card ≤ K * τ := (card_unionExcept_le _ _).trans hglobal
      have hUpow : (U.card : ℝ) ^ dim ≤ (K : ℝ) ^ dim * (τ : ℝ) ^ dim := by
        have hn := Nat.pow_le_pow_left hUcard dim
        have hc : (U.card : ℝ) ^ dim ≤ (((K * τ : ℕ) : ℝ) ^ dim) := by
          exact_mod_cast hn
        simpa [Nat.cast_mul, mul_pow] using hc
      have hrawBound : (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
          DRC.rawMoment G τ s dim
            (unionExcept (intersectOthers G S.sets ii x) j)
            (intersectOthers G S.sets ii x j)) ≤
          (τ : ℝ) ^ dim * ((K : ℝ) ^ (dim + (dim + t)) * ε) := by
        calc
          _ ≤ (U.card : ℝ) ^ dim * ((K : ℝ) ^ (dim + t) * ε) := hmeanRaw
          _ ≤ ((K : ℝ) ^ dim * (τ : ℝ) ^ dim) *
              ((K : ℝ) ^ (dim + t) * ε) :=
            mul_le_mul_of_nonneg_right hUpow
              (mul_nonneg (pow_nonneg (Nat.cast_nonneg K) _) hε)
          _ = (τ : ℝ) ^ dim * ((K : ℝ) ^ (dim + (dim + t)) * ε) := by
            rw [pow_add]
            ring
      have hden : (0 : ℝ) < (τ : ℝ) ^ dim * ε' := by positivity
      have holdBound : (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
          doneRawCost G S.sets ii τ s dim τ ε' x j) ≤
          (K : ℝ) ^ (dim + (dim + t)) * ε / ε' := by
        calc
          _ = (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
              DRC.rawMoment G τ s dim
                (unionExcept (intersectOthers G S.sets ii x) j)
                (intersectOthers G S.sets ii x j)) /
                  ((τ : ℝ) ^ dim * ε') := by
            rw [Finset.expect_div]
            apply Finset.expect_congr rfl
            intro x hx
            have hdoneFin : j ≤ ii := by
              change j.1 ≤ i
              exact hdone
            simp [doneRawCost, hdoneFin]
          _ ≤ ((τ : ℝ) ^ dim *
              ((K : ℝ) ^ (dim + (dim + t)) * ε)) /
                ((τ : ℝ) ^ dim * ε') :=
            div_le_div_of_nonneg_right hrawBound hden.le
          _ = (K : ℝ) ^ (dim + (dim + t)) * ε / ε' := by
            have hτpow : (τ : ℝ) ^ dim ≠ 0 := pow_ne_zero _
              (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hτ))
            field_simp
      exact holdBound.trans (le_add_of_nonneg_right
        (div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg K) _)
          (pow_nonneg hη t)) hε'.le))
  · have hzero : ∀ x : Fin t → α,
        doneRawCost G S.sets ii τ s dim τ ε' x j = 0 := by
      intro x
      have hnotFin : ¬j ≤ ii := by
        intro h
        apply hdone
        exact h
      simp [doneRawCost, hnotFin]
    rw [show (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
      doneRawCost G S.sets ii τ s dim τ ε' x j) = 0 by
        apply Finset.expect_eq_zero
        intro x hx
        exact hzero x]
    exact add_nonneg
      (div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg K) _) hε) hε'.le)
      (div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg K) _)
        (pow_nonneg hη t)) hε'.le)

/-- One quantitative all-direction step.  The displayed numerical
hypothesis is exactly the sum of the three normalized expectation bounds. -/
theorem expect_updateCost_lt_one
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r i L τ s dim t K : ℕ} {ε ε' η : ℝ}
    (S : DirectionState G r i L τ τ s (dim + t) ε)
    (hi : i < r) (hr : 2 ≤ r) (hK : 1 ≤ K)
    (hτ : 0 < τ) (hτL : τ ≤ L) (ht : 0 < t) (hst : s ≤ t)
    (hε : 0 ≤ ε) (hε' : 0 < ε') (hη : 0 ≤ η)
    (hglobal : Fintype.card α ≤ K * τ)
    (hthreshold : (τ : ℝ) ≤ η * (S.sets ⟨i, hi⟩).card)
    (hnum : (r : ℝ) *
      ((K : ℝ) ^ t * ε +
        (K : ℝ) ^ (dim + (dim + t)) * ε / ε' +
        ((K : ℝ) ^ (dim + (dim + t)) * ε / ε' +
          (K : ℝ) ^ dim * η ^ t / ε')) < 1) :
    (𝔼 x ∈ FiniteDefect.samples t (S.sets ⟨i, hi⟩),
      updateCost G S.sets ⟨i, hi⟩ L τ τ s dim ε' x) < 1 := by
  classical
  let ii : Fin r := ⟨i, hi⟩
  have hBi : (S.sets ii).Nonempty := by
    exact Finset.card_pos.mp ((hτ.trans_le hτL).trans_le
      (S.future_card ii le_rfl))
  have hsample : (FiniteDefect.samples t (S.sets ii)).Nonempty :=
    DRC.samples_nonempty t hBi
  let B : ℝ := (K : ℝ) ^ t * ε +
    (K : ℝ) ^ (dim + (dim + t)) * ε / ε' +
    ((K : ℝ) ^ (dim + (dim + t)) * ε / ε' +
      (K : ℝ) ^ dim * η ^ t / ε')
  have hj (j : Fin r) :
      (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
        (cardinalCost G S.sets ii L τ x j +
          futureRawCost G S.sets ii L dim ε' x j +
          doneRawCost G S.sets ii τ s dim τ ε' x j)) ≤ B := by
    rw [Finset.expect_add_distrib, Finset.expect_add_distrib]
    exact add_le_add
      (add_le_add
        (expect_cardinalCost_le G S hi hτ hτL hε hglobal j)
        (expect_futureRawCost_le G S hi hK hτ hτL hε hε' hglobal j))
      (expect_doneRawCost_le G S hi hK hτ hτL ht hst hε hε' hη
        hglobal hthreshold j)
  have hmean : (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
      updateCost G S.sets ii L τ τ s dim ε' x) < 1 := by
    have hle : (𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
        updateCost G S.sets ii L τ τ s dim ε' x) ≤ (r : ℝ) * B := by
      unfold updateCost
      rw [Finset.expect_sum_comm]
      calc
        (∑ j, 𝔼 x ∈ FiniteDefect.samples t (S.sets ii),
            (cardinalCost G S.sets ii L τ x j +
              futureRawCost G S.sets ii L dim ε' x j +
              doneRawCost G S.sets ii τ s dim τ ε' x j)) ≤
            ∑ _j : Fin r, B := Finset.sum_le_sum fun j _ => hj j
        _ = (r : ℝ) * B := by simp [mul_comm]
    exact hle.trans_lt (by simpa [B] using hnum)
  exact hmean

/-- If the combined normalized objective has expectation below one, one
sample advances the complete all-direction invariant. -/
theorem exists_next_of_expect_updateCost_lt_one
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r i L τ θ s dim t : ℕ} {ε ε' : ℝ}
    (S : DirectionState G r i L τ θ s (dim + t) ε)
    (hi : i < r) (hr : 2 ≤ r) (hL : 0 < L) (hτ : 0 < τ) (hτL : τ ≤ L)
    (hε' : 0 < ε')
    (hsample : (FiniteDefect.samples t (S.sets ⟨i, hi⟩)).Nonempty)
    (hmean : (𝔼 x ∈ FiniteDefect.samples t (S.sets ⟨i, hi⟩),
      updateCost G S.sets ⟨i, hi⟩ L τ θ s dim ε' x) < 1) :
    ∃ S' : DirectionState G r (i + 1) L τ θ s dim ε', True := by
  classical
  obtain ⟨x, hx, hcost⟩ := Finset.exists_lt_of_expect_lt hsample hmean
  have hterm (j : Fin r) :
      cardinalCost G S.sets ⟨i, hi⟩ L τ x j +
          futureRawCost G S.sets ⟨i, hi⟩ L dim ε' x j +
          doneRawCost G S.sets ⟨i, hi⟩ θ s dim τ ε' x j < 1 := by
    apply lt_of_le_of_lt _ hcost
    unfold updateCost
    exact Finset.single_le_sum
      (fun k _ => add_nonneg
        (add_nonneg (cardinalCost_nonneg G S.sets ⟨i, hi⟩ L τ x k)
          (futureRawCost_nonneg G S.sets ⟨i, hi⟩ L dim hε' x k))
        (doneRawCost_nonneg G S.sets ⟨i, hi⟩ θ s dim τ hε' x k))
      (Finset.mem_univ j)
  have hcardTerm (j : Fin r) :
      cardinalCost G S.sets ⟨i, hi⟩ L τ x j < 1 := by
    exact lt_of_le_of_lt (by
      have hfuture := futureRawCost_nonneg G S.sets ⟨i, hi⟩ L dim hε' x j
      have hdone := doneRawCost_nonneg G S.sets ⟨i, hi⟩ θ s dim τ hε' x j
      linarith) (hterm j)
  have hfutureTerm (j : Fin r) :
      futureRawCost G S.sets ⟨i, hi⟩ L dim ε' x j < 1 := by
    exact lt_of_le_of_lt (by
      have hcard := cardinalCost_nonneg G S.sets ⟨i, hi⟩ L τ x j
      have hdone := doneRawCost_nonneg G S.sets ⟨i, hi⟩ θ s dim τ hε' x j
      linarith) (hterm j)
  have hdoneTerm (j : Fin r) :
      doneRawCost G S.sets ⟨i, hi⟩ θ s dim τ ε' x j < 1 := by
    exact lt_of_le_of_lt (by
      have hcard := cardinalCost_nonneg G S.sets ⟨i, hi⟩ L τ x j
      have hfuture := futureRawCost_nonneg G S.sets ⟨i, hi⟩ L dim hε' x j
      linarith) (hterm j)
  let S' := S.next_of_good_sample G hi hτL x
    (fun j hj => by
      have hjne : j ≠ ⟨i, hi⟩ := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      have hc := hcardTerm j
      simp only [ge_iff_le] at hc
      by_contra hbad
      have hlt : (intersectOthers G S.sets ⟨i, hi⟩ x j).card < L :=
        Nat.lt_of_not_ge hbad
      rw [DRC.indicator_true hlt] at hc
      linarith)
    (fun j hj => by
      have hjne : j ≠ ⟨i, hi⟩ := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      have hnfuture : ¬i < j.1 := by omega
      have hc := hcardTerm j
      simp only [ge_iff_le] at hc
      by_contra hbad
      have hlt : (intersectOthers G S.sets ⟨i, hi⟩ x j).card < τ :=
        Nat.lt_of_not_ge hbad
      rw [DRC.indicator_true hlt] at hc
      linarith)
    (fun j hj hjr => by
      let jj : Fin r := ⟨j, (Nat.lt_succ_self j).trans hjr⟩
      have hcond : i < jj.1 ∧ jj.1 + 1 < r := by
        simpa [jj] using And.intro (by omega : i < j) hjr
      have hrawRatio := hfutureTerm jj
      simp only [ge_iff_le] at hrawRatio
      have hden : (0 : ℝ) < (L : ℝ) ^ dim * ε' := by positivity
      have hraw : DRC.rawMoment G L 0 dim
          (intersectOthers G S.sets ⟨i, hi⟩ x jj)
          (intersectOthers G S.sets ⟨i, hi⟩ x ⟨j + 1, hjr⟩) <
          (L : ℝ) ^ dim * ε' := by
        exact (div_lt_one hden).mp hrawRatio
      exact (HostTools.moment_lt_of_raw_lt_reserve G L 0 dim L hL
        (by
          have := hcardTerm jj
          have hjne : jj ≠ ⟨i, hi⟩ := by
            intro h
            have := congrArg Fin.val h
            simp [jj] at this
            omega
          simp only [ge_iff_le] at this
          by_contra hbad
          have hlt : (intersectOthers G S.sets ⟨i, hi⟩ x jj).card < L :=
            Nat.lt_of_not_ge hbad
          rw [DRC.indicator_true hlt] at this
          linarith)
        hε'.le hraw).le)
    (fun j hj => by
      have hcond : j.1 ≤ i := by omega
      have hrawRatio := hdoneTerm j
      simp only [ge_iff_le] at hrawRatio
      have hden : (0 : ℝ) < (τ : ℝ) ^ dim * ε' := by positivity
      have hraw : DRC.rawMoment G θ s dim
          (unionExcept (intersectOthers G S.sets ⟨i, hi⟩ x) j)
          (intersectOthers G S.sets ⟨i, hi⟩ x j) <
          (τ : ℝ) ^ dim * ε' := (div_lt_one hden).mp hrawRatio
      have hUcard : τ ≤
          (unionExcept (intersectOthers G S.sets ⟨i, hi⟩ x) j).card := by
        have hij : (⟨i, hi⟩ : Fin r) ≠ j := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        have hsub := subset_unionExcept
          (intersectOthers G S.sets ⟨i, hi⟩ x) hij
        exact hτL.trans ((S.future_card ⟨i, hi⟩ (by simp)).trans
          (Finset.card_le_card (by simpa [intersectOthers] using hsub))
          )
      exact (HostTools.moment_lt_of_raw_lt_reserve G θ s dim τ hτ hUcard
        hε'.le hraw).le)
    (by
      let ii : Fin r := ⟨i, hi⟩
      have hrawRatio := hdoneTerm ii
      simp only [intersectOthers_self, ge_iff_le] at hrawRatio
      have hden : (0 : ℝ) < (τ : ℝ) ^ dim * ε' := by positivity
      have hraw : DRC.rawMoment G θ s dim
          (unionExcept (intersectOthers G S.sets ii x) ii)
          (S.sets ii) <
          (τ : ℝ) ^ dim * ε' := (div_lt_one hden).mp hrawRatio
      have hUcard : τ ≤
          (unionExcept (intersectOthers G S.sets ii x) ii).card := by
        have hupdatedCard (k : Fin r) (hki : k ≠ ii) :
            τ ≤ (intersectOthers G S.sets ii x k).card := by
          by_cases hik : i < k.1
          · exact hτL.trans (by
              have := hcardTerm k
              simp only [ge_iff_le] at this
              by_contra hbad
              have hlt : (intersectOthers G S.sets ii x k).card < L :=
                Nat.lt_of_not_ge hbad
              rw [DRC.indicator_true hlt] at this
              linarith)
          · have hkiVal : k.1 < i := by
              have hne : k.1 ≠ i := by
                intro h
                apply hki
                exact Fin.ext h
              omega
            have := hcardTerm k
            simp only [ge_iff_le] at this
            by_contra hbad
            have hlt : (intersectOthers G S.sets ii x k).card < τ :=
              Nat.lt_of_not_ge hbad
            rw [DRC.indicator_true hlt] at this
            linarith
        by_cases hi0 : i = 0
        · let k : Fin r := ⟨1, hr⟩
          have hki : k ≠ ii := by
            intro h
            have hv := congrArg Fin.val h
            simp [k, ii, hi0] at hv
          exact (hupdatedCard k hki).trans (Finset.card_le_card
            (subset_unionExcept (intersectOthers G S.sets ii x) hki))
        · let k : Fin r := ⟨0, by omega⟩
          have hki : k ≠ ii := by
            intro h
            apply hi0
            have hv := congrArg Fin.val h
            simpa [k, ii] using hv.symm
          exact (hupdatedCard k hki).trans (Finset.card_le_card
            (subset_unionExcept (intersectOthers G S.sets ii x) hki))
      simpa [intersectOthers] using
        (HostTools.moment_lt_of_raw_lt_reserve G θ s dim τ hτ hUcard
          hε'.le hraw).le)
  exact ⟨S', trivial⟩

theorem exists_direction_step
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r i L τ s dim t K : ℕ} {ε ε' η : ℝ}
    (S : DirectionState G r i L τ τ s (dim + t) ε)
    (hi : i < r) (hr : 2 ≤ r) (hK : 1 ≤ K)
    (hτ : 0 < τ) (hτL : τ ≤ L) (ht : 0 < t) (hst : s ≤ t)
    (hε : 0 ≤ ε) (hε' : 0 < ε') (hη : 0 ≤ η)
    (hglobal : Fintype.card α ≤ K * τ)
    (hthreshold : (τ : ℝ) ≤ η * (S.sets ⟨i, hi⟩).card)
    (hnum : (r : ℝ) *
      ((K : ℝ) ^ t * ε +
        (K : ℝ) ^ (dim + (dim + t)) * ε / ε' +
        ((K : ℝ) ^ (dim + (dim + t)) * ε / ε' +
          (K : ℝ) ^ dim * η ^ t / ε')) < 1) :
    ∃ S' : DirectionState G r (i + 1) L τ τ s dim ε', True := by
  let ii : Fin r := ⟨i, hi⟩
  have hBi : (S.sets ii).Nonempty := by
    exact Finset.card_pos.mp ((hτ.trans_le hτL).trans_le
      (S.future_card ii le_rfl))
  have hsample : (FiniteDefect.samples t (S.sets ii)).Nonempty :=
    DRC.samples_nonempty t hBi
  exact exists_next_of_expect_updateCost_lt_one G S hi hr
    (hτ.trans_le hτL) hτ hτL hε' hsample
    (expect_updateCost_lt_one G S hi hr hK hτ hτL ht hst hε hε' hη
      hglobal hthreshold hnum)

theorem iterate_directions
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r stage L τ s dim t K m : ℕ} (err : ℕ → ℝ) {η : ℝ}
    (S : DirectionState G r stage L τ τ s (dim + m * t) (err 0))
    (hstage : stage + m ≤ r) (hr : 2 ≤ r) (hK : 1 ≤ K)
    (hτ : 0 < τ) (hτL : τ ≤ L) (ht : 0 < t) (hst : s ≤ t)
    (hη : 0 ≤ η) (hηL : (τ : ℝ) ≤ η * L)
    (hglobal : Fintype.card α ≤ K * τ)
    (herrpos : ∀ q, q ≤ m → 0 < err q)
    (hnum : ∀ q, q < m →
      let dnext := dim + (m - (q + 1)) * t
      (r : ℝ) *
        ((K : ℝ) ^ t * err q +
          (K : ℝ) ^ (dnext + (dnext + t)) * err q / err (q + 1) +
          ((K : ℝ) ^ (dnext + (dnext + t)) * err q / err (q + 1) +
            (K : ℝ) ^ dnext * η ^ t / err (q + 1))) < 1) :
    ∃ S' : DirectionState G r (stage + m) L τ τ s dim (err m), True := by
  induction m generalizing stage err with
  | zero =>
      let S0 : DirectionState G r stage L τ τ s dim (err 0) := by
        simpa using S
      simpa using (show ∃ S' : DirectionState G r stage L τ τ s dim (err 0), True
        from ⟨S0, trivial⟩)
  | succ m ih =>
      have hstageLt : stage < r := by omega
      let dnext := dim + m * t
      have hdim : dim + (m + 1) * t = dnext + t := by
        dsimp [dnext]
        rw [Nat.succ_mul]
        omega
      let S0 : DirectionState G r stage L τ τ s (dnext + t) (err 0) := by
        rw [← hdim]
        exact S
      have hthreshold : (τ : ℝ) ≤ η * (S0.sets ⟨stage, hstageLt⟩).card := by
        calc
          (τ : ℝ) ≤ η * L := hηL
          _ ≤ η * (S0.sets ⟨stage, hstageLt⟩).card :=
            mul_le_mul_of_nonneg_left (by
              exact_mod_cast S0.future_card ⟨stage, hstageLt⟩ le_rfl) hη
      have hnum0 : (r : ℝ) *
          ((K : ℝ) ^ t * err 0 +
            (K : ℝ) ^ (dnext + (dnext + t)) * err 0 / err 1 +
            ((K : ℝ) ^ (dnext + (dnext + t)) * err 0 / err 1 +
              (K : ℝ) ^ dnext * η ^ t / err 1)) < 1 := by
        have := hnum 0 (by omega)
        simpa [dnext] using this
      obtain ⟨S1, -⟩ := exists_direction_step G S0 hstageLt hr hK hτ hτL ht hst
        (herrpos 0 (by omega)).le (herrpos 1 (by omega)) hη hglobal
        hthreshold hnum0
      let err1 : ℕ → ℝ := fun q => err (q + 1)
      have hstage1 : (stage + 1) + m ≤ r := by omega
      have herrpos1 : ∀ q, q ≤ m → 0 < err1 q := by
        intro q hq
        exact herrpos (q + 1) (by omega)
      have hnum1 : ∀ q, q < m →
          let dn := dim + (m - (q + 1)) * t
          (r : ℝ) *
            ((K : ℝ) ^ t * err1 q +
              (K : ℝ) ^ (dn + (dn + t)) * err1 q / err1 (q + 1) +
              ((K : ℝ) ^ (dn + (dn + t)) * err1 q / err1 (q + 1) +
                (K : ℝ) ^ dn * η ^ t / err1 (q + 1))) < 1 := by
        intro q hq
        have hn := hnum (q + 1) (by omega)
        simpa [err1, Nat.add_assoc] using hn
      obtain ⟨S2, -⟩ := ih err1 S1 hstage1 herrpos1 hnum1
      have herr : err1 m = err (m + 1) := by simp [err1]
      rw [herr] at S2
      have hstageEq : (stage + 1) + m = stage + (m + 1) := by omega
      rw [hstageEq] at S2
      exact ⟨S2, trivial⟩

/-- Variable-length form used in Lee's geometric all-direction iteration. -/
theorem iterate_directions_list
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r stage L τ s dim K : ℕ} (widths : List ℕ) (err : ℕ → ℝ) {η : ℝ}
    (S : DirectionState G r stage L τ τ s (dim + widths.sum) (err 0))
    (hstage : stage + widths.length ≤ r) (hr : 2 ≤ r) (hK : 1 ≤ K)
    (hτ : 0 < τ) (hτL : τ ≤ L)
    (hwidth : ∀ w ∈ widths, 0 < w ∧ s ≤ w)
    (hη : 0 ≤ η) (hηL : (τ : ℝ) ≤ η * L)
    (hglobal : Fintype.card α ≤ K * τ)
    (herrpos : ∀ q, q ≤ widths.length → 0 < err q)
    (hnum : ∀ q, ∀ hq : q < widths.length,
      let w := widths.get ⟨q, hq⟩
      let dnext := dim + (widths.drop (q + 1)).sum
      (r : ℝ) *
        ((K : ℝ) ^ w * err q +
          (K : ℝ) ^ (dnext + (dnext + w)) * err q / err (q + 1) +
          ((K : ℝ) ^ (dnext + (dnext + w)) * err q / err (q + 1) +
            (K : ℝ) ^ dnext * η ^ w / err (q + 1))) < 1) :
    ∃ S' : DirectionState G r (stage + widths.length) L τ τ s dim
      (err widths.length), True := by
  induction widths generalizing stage err with
  | nil =>
      let S0 : DirectionState G r stage L τ τ s dim (err 0) := by
        simpa using S
      exact ⟨S0, trivial⟩
  | cons w ws ih =>
      have hwmem : w ∈ w :: ws := by simp
      have hw := hwidth w hwmem
      have hstageLt : stage < r := by simp only [List.length_cons] at hstage; omega
      let dnext := dim + ws.sum
      have hdim : dim + (w :: ws).sum = dnext + w := by
        simp [dnext, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      let S0 : DirectionState G r stage L τ τ s (dnext + w) (err 0) := by
        rw [← hdim]
        exact S
      have hthreshold : (τ : ℝ) ≤ η * (S0.sets ⟨stage, hstageLt⟩).card := by
        calc
          (τ : ℝ) ≤ η * L := hηL
          _ ≤ η * (S0.sets ⟨stage, hstageLt⟩).card :=
            mul_le_mul_of_nonneg_left (by
              exact_mod_cast S0.future_card ⟨stage, hstageLt⟩ le_rfl) hη
      have hnum0 : (r : ℝ) *
          ((K : ℝ) ^ w * err 0 +
            (K : ℝ) ^ (dnext + (dnext + w)) * err 0 / err 1 +
            ((K : ℝ) ^ (dnext + (dnext + w)) * err 0 / err 1 +
              (K : ℝ) ^ dnext * η ^ w / err 1)) < 1 := by
        have hn := hnum 0 (by simp)
        simpa [dnext] using hn
      obtain ⟨S1, -⟩ := exists_direction_step G S0 hstageLt hr hK hτ hτL
        hw.1 hw.2 (herrpos 0 (by simp)).le (herrpos 1 (by simp)) hη hglobal
        hthreshold hnum0
      let err1 : ℕ → ℝ := fun q => err (q + 1)
      have hstage1 : (stage + 1) + ws.length ≤ r := by
        simp only [List.length_cons] at hstage
        omega
      have hwidth1 : ∀ z ∈ ws, 0 < z ∧ s ≤ z := by
        intro z hz
        exact hwidth z (by simp [hz])
      have herrpos1 : ∀ q, q ≤ ws.length → 0 < err1 q := by
        intro q hq
        exact herrpos (q + 1) (by simp; omega)
      have hnum1 : ∀ q, ∀ hq : q < ws.length,
          let z := ws.get ⟨q, hq⟩
          let dn := dim + (ws.drop (q + 1)).sum
          (r : ℝ) *
            ((K : ℝ) ^ z * err1 q +
              (K : ℝ) ^ (dn + (dn + z)) * err1 q / err1 (q + 1) +
              ((K : ℝ) ^ (dn + (dn + z)) * err1 q / err1 (q + 1) +
                (K : ℝ) ^ dn * η ^ z / err1 (q + 1))) < 1 := by
        intro q hq
        have hn := hnum (q + 1) (by simp; omega)
        simpa [err1, Nat.add_assoc] using hn
      obtain ⟨S2, -⟩ := ih err1 S1 hstage1 hwidth1 herrpos1 hnum1
      have herr : err1 ws.length = err (List.length (w :: ws)) := by
        simp [err1]
      rw [herr] at S2
      have hstageEq : (stage + 1) + ws.length = stage + (w :: ws).length := by
        simp
        omega
      rw [hstageEq] at S2
      exact ⟨S2, trivial⟩

/-- Parameterized all-direction host theorem.  All numerical choices are
exposed; the final assembly instantiates them by powers of two. -/
theorem exists_all_directions_of_parameters
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r D s t t₀ L reserve₀ τ K : ℕ}
    (err : ℕ → ℝ) {η η₀ : ℝ}
    (hr : 2 ≤ r) (hD : 0 < D) (ht : 0 < t) (hst : s ≤ t)
    (ht₀ : 0 < t₀) (hL : 0 < L) (hLreserve : L ≤ reserve₀)
    (hτ : 0 < τ) (hτL : τ ≤ L) (hK : 1 ≤ K)
    (hη : 0 ≤ η) (hηL : (τ : ℝ) ≤ η * L)
    (hη₀ : 0 < η₀)
    (hnestedThreshold : (L : ℝ) ≤
      η₀ * (1 / 4 : ℝ) ^ (D + r * t) * reserve₀)
    (hnestedCard : HostNested.reserveFactor t₀ ^ (2 * (r - 1)) * reserve₀ ≤
      Fintype.card α)
    (hglobal : Fintype.card α ≤ K * τ)
    (herr0 : 2 * η₀ ^ t₀ ≤ err 0)
    (herrpos : ∀ q, q ≤ r → 0 < err q)
    (hnum : ∀ q, q < r →
      let dnext := D + (r - (q + 1)) * t
      (r : ℝ) *
        ((K : ℝ) ^ t * err q +
          (K : ℝ) ^ (dnext + (dnext + t)) * err q / err (q + 1) +
          ((K : ℝ) ^ (dnext + (dnext + t)) * err q / err (q + 1) +
            (K : ℝ) ^ dnext * η ^ t / err (q + 1))) < 1) :
    ∃ c : Bool, ∃ A : Fin r → Finset α,
      (∀ j, τ ≤ (A j).card) ∧
      (∀ j, FiniteDefect.moment (HostNested.colorGraph G c) τ s
        (fun _ : Fin D => unionExcept A j) (A j) ≤ err r) := by
  classical
  have hD0 : 0 < D + r * t := by omega
  obtain ⟨c, B, hBcard, hBnested, hBmoment⟩ :=
    HostNested.exists_nested_same_color G (r := r) (θ := L) (s := 0)
      (D := D + r * t) (t := t₀) (τ := reserve₀)
      (by omega) hD0 ht₀ (Nat.zero_le t₀) (hL.trans_le hLreserve)
      hη₀ hnestedThreshold hnestedCard
  let S0 : DirectionState (HostNested.colorGraph G c) r 0 L τ τ s
      (D + r * t) (err 0) := {
    sets := B
    future_card := fun j _ => hLreserve.trans (hBcard j)
    done_card := by intro j hj; omega
    future_nested := fun j _ hj => hBnested j hj
    future_moment := fun j _ hj => (hBmoment j hj).trans herr0
    done_moment := by intro j hj; omega }
  obtain ⟨Sf, -⟩ := iterate_directions (HostNested.colorGraph G c) err S0
    (by simp) hr hK hτ hτL ht hst hη hηL hglobal herrpos hnum
  refine ⟨c, Sf.sets, ?_, ?_⟩
  · intro j
    exact Sf.done_card j (by omega)
  · intro j
    exact Sf.done_moment j (by omega)

theorem exists_all_directions_of_list_parameters
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r D s t₀ L reserve₀ τ K : ℕ} (widths : List ℕ)
    (err : ℕ → ℝ) {η η₀ : ℝ}
    (hr : 2 ≤ r) (hlen : widths.length = r) (hD : 0 < D)
    (hwidth : ∀ w ∈ widths, 0 < w ∧ s ≤ w)
    (ht₀ : 0 < t₀) (hL : 0 < L) (hLreserve : L ≤ reserve₀)
    (hτ : 0 < τ) (hτL : τ ≤ L) (hK : 1 ≤ K)
    (hη : 0 ≤ η) (hηL : (τ : ℝ) ≤ η * L)
    (hη₀ : 0 < η₀)
    (hnestedThreshold : (L : ℝ) ≤
      η₀ * (1 / 4 : ℝ) ^ (D + widths.sum) * reserve₀)
    (hnestedCard : HostNested.reserveFactor t₀ ^ (2 * (r - 1)) * reserve₀ ≤
      Fintype.card α)
    (hglobal : Fintype.card α ≤ K * τ)
    (herr0 : 2 * η₀ ^ t₀ ≤ err 0)
    (herrpos : ∀ q, q ≤ widths.length → 0 < err q)
    (hnum : ∀ q, ∀ hq : q < widths.length,
      let w := widths.get ⟨q, hq⟩
      let dnext := D + (widths.drop (q + 1)).sum
      (r : ℝ) *
        ((K : ℝ) ^ w * err q +
          (K : ℝ) ^ (dnext + (dnext + w)) * err q / err (q + 1) +
          ((K : ℝ) ^ (dnext + (dnext + w)) * err q / err (q + 1) +
            (K : ℝ) ^ dnext * η ^ w / err (q + 1))) < 1) :
    ∃ c : Bool, ∃ A : Fin r → Finset α,
      (∀ j, τ ≤ (A j).card) ∧
      (∀ j, FiniteDefect.moment (HostNested.colorGraph G c) τ s
        (fun _ : Fin D => unionExcept A j) (A j) ≤ err r) := by
  classical
  have hD0 : 0 < D + widths.sum := by omega
  obtain ⟨c, B, hBcard, hBnested, hBmoment⟩ :=
    HostNested.exists_nested_same_color G (r := r) (θ := L) (s := 0)
      (D := D + widths.sum) (t := t₀) (τ := reserve₀)
      (by omega) hD0 ht₀ (Nat.zero_le t₀) (hL.trans_le hLreserve)
      hη₀ hnestedThreshold hnestedCard
  let S0 : DirectionState (HostNested.colorGraph G c) r 0 L τ τ s
      (D + widths.sum) (err 0) := {
    sets := B
    future_card := fun j _ => hLreserve.trans (hBcard j)
    done_card := by intro j hj; omega
    future_nested := fun j _ hj => hBnested j hj
    future_moment := fun j _ hj => (hBmoment j hj).trans herr0
    done_moment := by intro j hj; omega }
  obtain ⟨Sf, -⟩ := iterate_directions_list (HostNested.colorGraph G c)
    widths err S0 (by simp [hlen]) hr hK hτ hτL hwidth hη hηL hglobal
    herrpos hnum
  have hlen' : widths.length = r := hlen
  rw [hlen'] at Sf
  refine ⟨c, Sf.sets, ?_, ?_⟩
  · intro j
    exact Sf.done_card j (by omega)
  · intro j
    exact Sf.done_moment j (by omega)

end HostDirections
end Erdos163
