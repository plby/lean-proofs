import Mathlib

/-!
# A finite greedy sparse-selection lemma

This file isolates the counting argument used to choose a sparse family while successively
destroying all bad colourings.  It deliberately uses only natural-number cross multiplication.

`X j` is the `j`th stratum of candidates, `Hit x c` says that candidate `x` destroys colouring
`c`, and `Suitable S` is the sparsity condition imposed on a chosen family.  All strata have the
same cardinality `L`.  The two substantive hypotheses are:

* every colouring is hit by at least a `1 / A` fraction of one stratum;
* while fewer than `q` candidates have been selected, the non-addable candidates in every
  stratum form less than a `1 / (2A)` fraction.

Thus, among all `m` strata, averaging supplies an addable candidate hitting at least a
`1 / (2Am)` fraction of the currently bad colourings.
-/

namespace Erdos847SparseSelection

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

section Definitions

variable {Candidate Colour : Type*}

/-- The colourings not hit by any member of `S`. -/
def badColourings (colours : Finset Colour) (Hit : Candidate → Colour → Prop)
    (S : Finset Candidate) : Finset Colour := by
  classical
  exact colours.filter fun c ↦ ∀ x ∈ S, ¬ Hit x c

@[simp] lemma mem_badColourings {colours : Finset Colour} {Hit : Candidate → Colour → Prop}
    {S : Finset Candidate} {c : Colour} :
    c ∈ badColourings colours Hit S ↔ c ∈ colours ∧ ∀ x ∈ S, ¬ Hit x c := by
  classical
  simp [badColourings]

@[simp] lemma badColourings_empty (colours : Finset Colour) (Hit : Candidate → Colour → Prop) :
    badColourings colours Hit ∅ = colours := by
  classical
  ext c
  simp

lemma badColourings_insert (colours : Finset Colour) (Hit : Candidate → Colour → Prop)
    (x : Candidate) (S : Finset Candidate) :
    badColourings colours Hit (insert x S) =
      (badColourings colours Hit S).filter fun c ↦ ¬ Hit x c := by
  classical
  ext c
  simp [badColourings, and_assoc, and_left_comm, and_comm]

end Definitions

section Equalize

variable {Candidate : Type*}

/-- Positive finite strata can always be equalized by replication.  The weight of stratum `j`
is the product of the sizes of all the other strata. -/
theorem exists_equalizing_weights (X : Fin m → Finset Candidate)
    (hpos : ∀ j, 0 < (X j).card) :
    ∃ L : ℕ, 0 < L ∧ ∃ weight : Fin m → ℕ,
      ∀ j, weight j * (X j).card = L := by
  let L := ∏ j : Fin m, (X j).card
  let weight : Fin m → ℕ := fun j ↦ ∏ k ∈ (Finset.univ.erase j), (X k).card
  refine ⟨L, ?_, weight, ?_⟩
  · exact Finset.prod_pos fun j _ ↦ hpos j
  · intro j
    exact Finset.prod_erase_mul Finset.univ (fun k : Fin m ↦ (X k).card)
      (Finset.mem_univ j)

end Equalize

section Iteration

variable {Candidate Colour : Type*}

/-- Multiplicative decay propagates through any prescribed number of greedy steps. -/
theorem iterate_decay
    (colours : Finset Colour) (Hit : Candidate → Colour → Prop)
    (Suitable : Finset Candidate → Prop) {D q : ℕ} (hD : 0 < D)
    (hempty : Suitable ∅)
    (hstep : ∀ (S : Finset Candidate), Suitable S → S.card < q →
      (badColourings colours Hit S).Nonempty →
      ∃ x, Suitable (insert x S) ∧
        D * (badColourings colours Hit (insert x S)).card ≤
          (D - 1) * (badColourings colours Hit S).card)
    (t : ℕ) (ht : t ≤ q) :
    ∃ S : Finset Candidate, Suitable S ∧ S.card ≤ t ∧
      D ^ t * (badColourings colours Hit S).card ≤ (D - 1) ^ t * colours.card := by
  induction t with
  | zero =>
      refine ⟨∅, hempty, by simp, ?_⟩
      simp
  | succ t ih =>
      have htq : t ≤ q := t.le_succ.trans ht
      obtain ⟨S, hS, hSt, hdec⟩ := ih htq
      by_cases hbad : (badColourings colours Hit S).Nonempty
      · have hSq : S.card < q := hSt.trans_lt (Nat.lt_of_succ_le ht)
        obtain ⟨x, hxSuit, hxdec⟩ := hstep S hS hSq hbad
        refine ⟨insert x S, hxSuit, ?_, ?_⟩
        · exact (Finset.card_insert_le x S).trans (Nat.succ_le_succ hSt)
        · calc
            D ^ (t + 1) * (badColourings colours Hit (insert x S)).card =
                D ^ t * (D * (badColourings colours Hit (insert x S)).card) := by
                  rw [pow_succ]
                  ring
            _ ≤ D ^ t * ((D - 1) * (badColourings colours Hit S).card) :=
              Nat.mul_le_mul_left _ hxdec
            _ = (D - 1) * (D ^ t * (badColourings colours Hit S).card) := by ring
            _ ≤ (D - 1) * ((D - 1) ^ t * colours.card) :=
              Nat.mul_le_mul_left _ hdec
            _ = (D - 1) ^ (t + 1) * colours.card := by
              rw [pow_succ]
              ring
      · refine ⟨S, hS, hSt.trans (Nat.le_succ t), ?_⟩
        have hz : (badColourings colours Hit S).card = 0 := Finset.not_nonempty_iff_eq_empty.mp hbad ▸ rfl
        simp [hz]

end Iteration

section NumericalDecay

/-- The first two terms of the binomial expansion, in a form requiring no division. -/
lemma pow_add_one_lower (a n : ℕ) :
    a ^ (n + 1) + (n + 1) * a ^ n ≤ (a + 1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        a ^ (n + 1 + 1) + (n + 1 + 1) * a ^ (n + 1) ≤
            a ^ (n + 1 + 1) + (n + 1 + 1) * a ^ (n + 1) +
              (n + 1) * a ^ n := Nat.le_add_right _ _
        _ = (a ^ (n + 1) + (n + 1) * a ^ n) * (a + 1) := by
          rw [pow_succ, pow_succ]
          ring
        _ ≤ (a + 1) ^ (n + 1) * (a + 1) := Nat.mul_le_mul_right _ ih
        _ = (a + 1) ^ (n + 1 + 1) := by
          simp only [pow_succ]

/-- In a block of `D` steps, multiplying by `(D-1)/D` at each step loses at least a factor two. -/
lemma two_mul_pred_pow_le_pow {D : ℕ} (hD : 2 ≤ D) :
    2 * (D - 1) ^ D ≤ D ^ D := by
  have hDpos : 1 ≤ D := le_trans (by decide) hD
  have hdecomp : D - 1 + 1 = D := Nat.sub_add_cancel hDpos
  have hpow : (D - 1) ^ D ≤ D * (D - 1) ^ (D - 1) := by
    calc
      (D - 1) ^ D = (D - 1) ^ ((D - 1) + 1) :=
        congrArg (fun n : ℕ ↦ (D - 1) ^ n) hdecomp.symm
      _ = (D - 1) ^ (D - 1) * (D - 1) := by rw [pow_succ]
      _ ≤ (D - 1) ^ (D - 1) * D :=
        Nat.mul_le_mul_left _ (Nat.sub_le D 1)
      _ = D * (D - 1) ^ (D - 1) := Nat.mul_comm _ _
  calc
    2 * (D - 1) ^ D = (D - 1) ^ D + (D - 1) ^ D := by omega
    _ ≤ (D - 1) ^ D + D * (D - 1) ^ (D - 1) := Nat.add_le_add_left hpow _
    _ ≤ ((D - 1) + 1) ^ ((D - 1) + 1) := by
      simpa only [hdecomp] using pow_add_one_lower (D - 1) (D - 1)
    _ = D ^ D := by rw [hdecomp]

/-- `D*K` multiplicative-decay steps kill any family of fewer than `2^K` bad objects. -/
lemma decay_forces_zero {D K b₀ b : ℕ} (hD : 2 ≤ D) (hb₀ : b₀ < 2 ^ K)
    (hdec : D ^ (D * K) * b ≤ (D - 1) ^ (D * K) * b₀) : b = 0 := by
  have hpredpos : 0 < D - 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide) hD)
  have hstrict :
      (D - 1) ^ (D * K) * b₀ < (D - 1) ^ (D * K) * 2 ^ K := by
    exact (Nat.mul_lt_mul_left (pow_pos hpredpos _)).mpr hb₀
  have hblock := two_mul_pred_pow_le_pow hD
  have hupper : (D - 1) ^ (D * K) * 2 ^ K ≤ D ^ (D * K) := by
    calc
      (D - 1) ^ (D * K) * 2 ^ K = (2 * (D - 1) ^ D) ^ K := by
        rw [pow_mul, mul_pow]
        ring
      _ ≤ (D ^ D) ^ K := Nat.pow_le_pow_left hblock K
      _ = D ^ (D * K) := by rw [pow_mul]
  by_contra hb
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  have hself : D ^ (D * K) ≤ D ^ (D * K) * b := by
    calc
      D ^ (D * K) = D ^ (D * K) * 1 := by simp
      _ ≤ D ^ (D * K) * b := Nat.mul_le_mul_left _ hbpos
  have hlt : (D - 1) ^ (D * K) * b₀ < D ^ (D * K) := hstrict.trans_le hupper
  exact (not_lt_of_ge (hself.trans hdec)) hlt

end NumericalDecay

section OneStep

variable {Candidate Colour : Type*}
variable (X : Fin m → Finset Candidate) (colours : Finset Colour)
  (Hit : Candidate → Colour → Prop) (Suitable : Finset Candidate → Prop)

/-- The finite averaging step.  `weight` represents harmless replication of a stratum; the
identity `weight j * #(X j) = L` says that all replicated strata have the same size.  Thus this
statement applies directly when the unreplicated strata have different positive sizes.

`D = 2 * A * m` is kept explicit in the conclusion. -/
theorem exists_addable_hits_many
    (weight : Fin m → ℕ) {A L q : ℕ} (hA : 0 < A) (hL : 0 < L)
    (hcard : ∀ j, weight j * (X j).card = L)
    (hdense : ∀ c ∈ colours, ∃ j,
      (X j).card ≤ A * ((X j).filter fun x ↦ Hit x c).card)
    (hnonadd : ∀ (S : Finset Candidate), Suitable S → S.card < q → ∀ j,
      2 * A * ((X j).filter fun x ↦ ¬ Suitable (insert x S)).card < (X j).card)
    {S : Finset Candidate} (hS : Suitable S) (hSq : S.card < q)
    (hbad : (badColourings colours Hit S).Nonempty) :
    ∃ j x, x ∈ X j ∧ Suitable (insert x S) ∧
      (badColourings colours Hit S).card ≤
        (2 * A * m) * ((badColourings colours Hit S).filter fun c ↦ Hit x c).card := by
  classical
  let B := badColourings colours Hit S
  let goodCount : Fin m → Colour → ℕ := fun j c ↦
    weight j * ((X j).filter fun x ↦ Hit x c ∧ Suitable (insert x S)).card
  have hgood (c : Colour) (hc : c ∈ B) :
      L ≤ 2 * A * ∑ j, goodCount j c := by
    obtain ⟨j, hj⟩ := hdense c (mem_badColourings.mp hc).1
    let H := ((X j).filter fun x ↦ Hit x c).card
    let G := ((X j).filter fun x ↦ Hit x c ∧ Suitable (insert x S)).card
    let N := ((X j).filter fun x ↦ ¬ Suitable (insert x S)).card
    have hsplit : H ≤ G + N := by
      let Y := (X j).filter fun x ↦ Hit x c
      have hpart := Finset.card_filter_add_card_filter_not
        (s := Y) (fun x ↦ Suitable (insert x S))
      have hfirst : (Y.filter fun x ↦ Suitable (insert x S)).card = G := by
        congr 1
        ext x
        simp [Y, G, and_assoc, and_left_comm, and_comm]
      have hsecond : (Y.filter fun x ↦ ¬ Suitable (insert x S)).card ≤ N := by
        apply Finset.card_le_card
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        have hxY := Finset.mem_filter.mp hx'.1
        exact Finset.mem_filter.mpr ⟨hxY.1, hx'.2⟩
      dsimp [H]
      rw [← hpart, hfirst]
      exact Nat.add_le_add_left hsecond G
    have hd : (X j).card ≤ A * H := hj
    have hn : 2 * A * N < (X j).card := hnonadd S hS hSq j
    have hAG : (X j).card ≤ 2 * A * G := by
      let AG := A * G
      let AN := A * N
      have hAH : A * H ≤ AG + AN := by
        dsimp [AG, AN]
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left A hsplit
      have hn' : 2 * AN < (X j).card := by
        simpa [AN, Nat.mul_assoc] using hn
      have hd' : (X j).card ≤ AG + AN := hd.trans hAH
      have hAG' : (X j).card ≤ 2 * AG := by omega
      simpa [AG, Nat.mul_assoc] using hAG'
    have hweighted : L ≤ 2 * A * goodCount j c := by
      calc
        L = weight j * (X j).card := (hcard j).symm
        _ ≤ weight j * (2 * A * G) := Nat.mul_le_mul_left (weight j) hAG
        _ = 2 * A * goodCount j c := by
          simp [goodCount, G]
          ring
    calc
      L ≤ 2 * A * goodCount j c := hweighted
      _ ≤ 2 * A * ∑ k, goodCount k c := by
        exact Nat.mul_le_mul_left (2 * A)
          (Finset.single_le_sum (f := fun k : Fin m ↦ goodCount k c)
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))
  let incidence : Fin m → Candidate → ℕ := fun j x ↦
    weight j * (if Suitable (insert x S) then (B.filter fun c ↦ Hit x c).card else 0)
  have hincidence :
      (∑ c ∈ B, ∑ j, goodCount j c) = ∑ j, ∑ x ∈ X j, incidence j x := by
    rw [Finset.sum_comm]
    congr 1
    funext j
    simp_rw [goodCount, incidence]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hsx : Suitable (insert x S)
    · simp [hsx, B]
    · simp [hsx]
  have hlower : L * B.card ≤ 2 * A * ∑ j, ∑ x ∈ X j, incidence j x := by
    calc
      L * B.card = ∑ c ∈ B, L := by simp [Nat.mul_comm]
      _ ≤ ∑ c ∈ B, 2 * A * ∑ j, goodCount j c := by
        exact Finset.sum_le_sum fun c hc ↦ hgood c hc
      _ = 2 * A * ∑ j, ∑ x ∈ X j, incidence j x := by
        rw [← hincidence]
        simp only [Finset.mul_sum]
  by_contra! hno
  have hpoint (j : Fin m) (x : Candidate) (hx : x ∈ X j) :
      (2 * A * m) * incidence j x < weight j * B.card := by
    by_cases hsx : Suitable (insert x S)
    · have hw : 0 < weight j := by
        have hp : 0 < weight j * (X j).card := by rw [hcard j]; exact hL
        exact Nat.pos_of_mul_pos_right hp
      have := (Nat.mul_lt_mul_left hw).mpr (hno j x hx hsx)
      calc
        (2 * A * m) * incidence j x =
            weight j * ((2 * A * m) * (B.filter fun c ↦ Hit x c).card) := by
              simp [incidence, hsx]
              ring
        _ < weight j * B.card := by simpa [B] using this
    · have hw : 0 < weight j := by
        have hp : 0 < weight j * (X j).card := by rw [hcard j]; exact hL
        exact Nat.pos_of_mul_pos_right hp
      simp [incidence, hsx, B, hw, hbad.card_pos]
  have hm : 0 < m := by
    obtain ⟨c, hc⟩ := hbad
    obtain ⟨j, -⟩ := hdense c (mem_badColourings.mp hc).1
    exact Fin.pos_iff_nonempty.mpr ⟨j⟩
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hupper :
      (2 * A * m) * (∑ j, ∑ x ∈ X j, incidence j x) < m * (L * B.card) := by
    rw [Finset.mul_sum]
    calc
      ∑ j, (2 * A * m) * ∑ x ∈ X j, incidence j x =
          ∑ j, ∑ x ∈ X j, (2 * A * m) * incidence j x := by
            congr 1
            funext j
            rw [Finset.mul_sum]
      _ < ∑ j, ∑ _x ∈ X j, weight j * B.card := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro j _
        apply Finset.sum_lt_sum_of_nonempty
        · have : 0 < (X j).card := by
            have hp : 0 < weight j * (X j).card := by rw [hcard j]; exact hL
            exact Nat.pos_of_mul_pos_left hp
          exact Finset.card_pos.mp this
        · exact fun x hx ↦ hpoint j x hx
      _ = m * (L * B.card) := by
        calc
          ∑ j, ∑ _x ∈ X j, weight j * B.card = ∑ _j : Fin m, L * B.card := by
            apply Finset.sum_congr rfl
            intro j _
            simp only [Finset.sum_const, nsmul_eq_mul]
            calc
              (X j).card * (weight j * B.card) =
                  (weight j * (X j).card) * B.card := by ring
              _ = L * B.card := by rw [hcard j]
          _ = m * (L * B.card) := by simp
  have hlower' : m * (L * B.card) ≤ (2 * A * m) * (∑ j, ∑ x ∈ X j, incidence j x) := by
    calc
      m * (L * B.card) ≤ m * (2 * A * ∑ j, ∑ x ∈ X j, incidence j x) :=
        Nat.mul_le_mul_left m hlower
      _ = (2 * A * m) * (∑ j, ∑ x ∈ X j, incidence j x) := by ring
  exact (not_lt_of_ge hlower') hupper

end OneStep

section Compose

variable {Candidate Colour : Type*}

/-- Turning a lower bound for the newly covered bad objects into the standard decay inequality. -/
lemma badColourings_insert_decay (colours : Finset Colour) (Hit : Candidate → Colour → Prop)
    (S : Finset Candidate) (x : Candidate) {D : ℕ} (hD : 0 < D)
    (hcover : (badColourings colours Hit S).card ≤
      D * ((badColourings colours Hit S).filter fun c ↦ Hit x c).card) :
    D * (badColourings colours Hit (insert x S)).card ≤
      (D - 1) * (badColourings colours Hit S).card := by
  let B := badColourings colours Hit S
  let H := (B.filter fun c ↦ Hit x c).card
  let N := (B.filter fun c ↦ ¬ Hit x c).card
  have hpart : H + N = B.card := by
    exact Finset.card_filter_add_card_filter_not (s := B) (fun c ↦ Hit x c)
  have hdecomp : D - 1 + 1 = D := Nat.sub_add_cancel hD
  have hNH : N ≤ (D - 1) * H := by
    apply Nat.le_of_add_le_add_left (a := H)
    calc
      H + N = B.card := hpart
      _ ≤ D * H := hcover
      _ = (D - 1 + 1) * H := congrArg (fun d : ℕ ↦ d * H) hdecomp.symm
      _ = H + (D - 1) * H := by ring
  have hdec : D * N ≤ (D - 1) * B.card := by
    calc
      D * N = (D - 1 + 1) * N := congrArg (fun d : ℕ ↦ d * N) hdecomp.symm
      _ = N + (D - 1) * N := by ring
      _ ≤ (D - 1) * H + (D - 1) * N := Nat.add_le_add_right hNH _
      _ = (D - 1) * (H + N) := by ring
      _ = (D - 1) * B.card := by rw [hpart]
  rw [badColourings_insert]
  exact hdec

/--
The complete Nat-only sparse selection lemma.

There are `m` (not necessarily equally sized) positive strata.  Each colouring is hit on at least
a `1/A` fraction of one stratum.  Before `q = (2*A*m)*K` selections have been made, fewer than a
`1/(2A)` fraction of every stratum is non-addable.  If there are fewer than `2^K` colourings, a
suitable family of at most `q` candidates hits all of them.
-/
theorem exists_suitable_hitting_all
    (X : Fin m → Finset Candidate) (colours : Finset Colour)
    (Hit : Candidate → Colour → Prop) (Suitable : Finset Candidate → Prop)
    {A K : ℕ} (hA : 0 < A) (hm : 0 < m)
    (hpos : ∀ j, 0 < (X j).card)
    (hdense : ∀ c ∈ colours, ∃ j,
      (X j).card ≤ A * ((X j).filter fun x ↦ Hit x c).card)
    (hempty : Suitable ∅)
    (hnonadd : ∀ (S : Finset Candidate), Suitable S → S.card < (2 * A * m) * K → ∀ j,
      2 * A * ((X j).filter fun x ↦ ¬ Suitable (insert x S)).card < (X j).card)
    (hcolours : colours.card < 2 ^ K) :
    ∃ S : Finset Candidate, Suitable S ∧ S.card ≤ (2 * A * m) * K ∧
      ∀ c ∈ colours, ∃ x ∈ S, Hit x c := by
  classical
  let D := 2 * A * m
  have hDtwo : 2 ≤ D := by
    dsimp [D]
    simpa using Nat.mul_le_mul (Nat.mul_le_mul_left 2 hA) hm
  have hDpos : 0 < D := lt_of_lt_of_le (by decide) hDtwo
  obtain ⟨L, hL, weight, hweight⟩ := exists_equalizing_weights X hpos
  have hstep (S : Finset Candidate) (hS : Suitable S)
      (hSq : S.card < D * K) (hbad : (badColourings colours Hit S).Nonempty) :
      ∃ x, Suitable (insert x S) ∧
        D * (badColourings colours Hit (insert x S)).card ≤
          (D - 1) * (badColourings colours Hit S).card := by
    obtain ⟨j, x, hx, hxSuit, hxcover⟩ := exists_addable_hits_many
      X colours Hit Suitable weight hA hL hweight hdense (by
        intro T hT hTq
        exact hnonadd T hT (by simpa [D] using hTq)) hS (by simpa [D] using hSq) hbad
    refine ⟨x, hxSuit, ?_⟩
    apply badColourings_insert_decay colours Hit S x hDpos
    simpa [D] using hxcover
  obtain ⟨S, hS, hScard, hdec⟩ :=
    iterate_decay colours Hit Suitable hDpos hempty hstep (D * K) le_rfl
  have hz : (badColourings colours Hit S).card = 0 := by
    apply decay_forces_zero hDtwo hcolours
    simpa using hdec
  refine ⟨S, hS, by simpa [D] using hScard, ?_⟩
  intro c hc
  by_contra hnone
  have hall : ∀ x ∈ S, ¬ Hit x c := by
    intro x hx hxc
    exact hnone ⟨x, hx, hxc⟩
  have hmem : c ∈ badColourings colours Hit S := mem_badColourings.mpr ⟨hc, hall⟩
  have hemptyBad : badColourings colours Hit S = ∅ := Finset.card_eq_zero.mp hz
  rw [hemptyBad] at hmem
  simp at hmem

end Compose

end
end Erdos847SparseSelection
