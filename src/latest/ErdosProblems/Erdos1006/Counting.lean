/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle, Boris Alexeev
-/

import Mathlib

namespace Erdos1006NR5

/-- Functions satisfying all prescribed coordinate-identification events. -/
abbrev PairEqualityEvent {C A : Type*} {l : ℕ} (p q : Fin l → C) :=
  {f : C → A // ∀ t, f (p t) = f (q t)}

/-- Overwrite the pairwise-distinct `q`-coordinates.  The inverse records the
old `q`-values and normalizes each `q t` to the value at `p t`.

Only injectivity of `q` and disjointness of the ranges of `p` and `q` are
needed; the usual hypothesis that all `2*l` coordinates are distinct is
stronger. -/
noncomputable def pairEqualityEvent_mul_equiv {C A : Type*} {l : ℕ}
    (p q : Fin l → C) (hq : Function.Injective q)
    (hpq : ∀ i j, p i ≠ q j) :
    PairEqualityEvent (A := A) p q × (Fin l → A) ≃ (C → A) := by
  classical
  let encode : PairEqualityEvent (A := A) p q × (Fin l → A) → (C → A) :=
    fun z ↦ Function.extend q z.2 z.1.1
  refine Equiv.ofBijective encode ?_
  constructor
  · rintro ⟨⟨f, hf⟩, values⟩ ⟨⟨g, hg⟩, values'⟩ h
    have hvalues : values = values' := by
      funext t
      calc
        values t = encode (⟨f, hf⟩, values) (q t) :=
          (hq.extend_apply values f t).symm
        _ = encode (⟨g, hg⟩, values') (q t) := congrFun h (q t)
        _ = values' t := hq.extend_apply values' g t
    apply Prod.ext
    · apply Subtype.ext
      funext c
      by_cases hc : ∃ t, q t = c
      · obtain ⟨t, rfl⟩ := hc
        calc
          f (q t) = f (p t) := (hf t).symm
          _ = encode (⟨f, hf⟩, values) (p t) := by
            symm
            apply Function.extend_apply'
            rintro ⟨j, hj⟩
            exact hpq t j hj.symm
          _ = encode (⟨g, hg⟩, values') (p t) := congrFun h (p t)
          _ = g (p t) := by
            apply Function.extend_apply'
            rintro ⟨j, hj⟩
            exact hpq t j hj.symm
          _ = g (q t) := hg t
      · calc
          f c = encode (⟨f, hf⟩, values) c :=
            (Function.extend_apply' values f c hc).symm
          _ = encode (⟨g, hg⟩, values') c := congrFun h c
          _ = g c := Function.extend_apply' values' g c hc
    · exact hvalues
  · intro g
    let normalized : C → A := Function.extend q (fun t ↦ g (p t)) g
    have hnormalized : ∀ t, normalized (p t) = normalized (q t) := by
      intro t
      change Function.extend q (fun t ↦ g (p t)) g (p t) =
        Function.extend q (fun t ↦ g (p t)) g (q t)
      rw [hq.extend_apply]
      apply Function.extend_apply'
      rintro ⟨j, hj⟩
      exact hpq t j hj.symm
    refine ⟨(⟨normalized, hnormalized⟩, fun t ↦ g (q t)), ?_⟩
    funext c
    by_cases hc : ∃ t, q t = c
    · obtain ⟨t, rfl⟩ := hc
      exact hq.extend_apply (fun t ↦ g (q t)) normalized t
    · change Function.extend q (fun t ↦ g (q t)) normalized c = g c
      rw [Function.extend_apply' _ _ _ hc]
      exact Function.extend_apply' _ _ _ hc

/-- Exact finite count: imposing `l` independent coordinate equalities costs
one factor of `N` per equality.  The multiplicative form avoids subtraction
in exponents and remains valid for `N = 0`. -/
theorem pairEqualityEvent_card_mul_pow {C : Type*} [Fintype C]
    (N l : ℕ) (p q : Fin l → C) (hq : Function.Injective q)
    (hpq : ∀ i j, p i ≠ q j) :
    Nat.card (PairEqualityEvent (A := Fin N) p q) * N ^ l =
      N ^ Fintype.card C := by
  classical
  have hcard := Nat.card_congr
    (pairEqualityEvent_mul_equiv (A := Fin N) p q hq hpq)
  simpa [Nat.card_prod, Nat.card_fun] using hcard

/-- The exact count under the common hypothesis that all `2*l` displayed
coordinates are pairwise distinct. -/
theorem pairEqualityEvent_card_mul_pow_of_injective_sum {C : Type*} [Fintype C]
    (N l : ℕ) (p q : Fin l → C)
    (hpairs : Function.Injective (Sum.elim p q)) :
    Nat.card (PairEqualityEvent (A := Fin N) p q) * N ^ l =
      N ^ Fintype.card C := by
  apply pairEqualityEvent_card_mul_pow N l p q
  · intro i j hij
    have hs : (Sum.inr i : Fin l ⊕ Fin l) = Sum.inr j := hpairs hij
    exact Sum.inr.inj hs
  · intro i j hij
    have hs : (Sum.inl i : Fin l ⊕ Fin l) = Sum.inr j := hpairs hij
    exact Sum.inl_ne_inr hs

/-- Convenient event-finset spelling for union bounds. -/
theorem filter_pairEqual_card_mul_pow {C : Type*} [Fintype C]
    [DecidableEq C]
    (N l : ℕ) (p q : Fin l → C) (hq : Function.Injective q)
    (hpq : ∀ i j, p i ≠ q j) :
    (Finset.univ.filter fun f : C → Fin N ↦ ∀ t, f (p t) = f (q t)).card *
        N ^ l = N ^ Fintype.card C := by
  classical
  rw [← pairEqualityEvent_card_mul_pow N l p q hq hpq]
  congr 1
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype _).symm

/-- Event-finset version under pairwise distinctness of all displayed
coordinates. -/
theorem filter_pairEqual_card_mul_pow_of_injective_sum {C : Type*} [Fintype C]
    [DecidableEq C] (N l : ℕ) (p q : Fin l → C)
    (hpairs : Function.Injective (Sum.elim p q)) :
    (Finset.univ.filter fun f : C → Fin N ↦ ∀ t, f (p t) = f (q t)).card *
        N ^ l = N ^ Fintype.card C := by
  apply filter_pairEqual_card_mul_pow N l p q
  · intro i j hij
    have hs : (Sum.inr i : Fin l ⊕ Fin l) = Sum.inr j := hpairs hij
    exact Sum.inr.inj hs
  · intro i j hij
    have hs : (Sum.inl i : Fin l ⊕ Fin l) = Sum.inr j := hpairs hij
    exact Sum.inl_ne_inr hs

/-- Number of prescribed pair-collision witnesses present in one function. -/
noncomputable def pairBadCount {C W : Type*} [Fintype W] {N l : ℕ}
    (p q : W → Fin l → C) (f : C → Fin N) : ℕ :=
  (Finset.univ.filter fun w ↦ ∀ t, f (p w t) = f (q w t)).card

/-- Double-counting identity for a family of independent pair-collision
witnesses.  This is the numerator form of the expected-count calculation:
the sum of the numbers of bad witnesses, multiplied by `N^l`, is exactly the
number of witnesses times the size of the whole function space. -/
theorem sum_pairBadCount_mul_pow {C W : Type*} [Fintype C] [DecidableEq C]
    [Fintype W] (N l : ℕ) (p q : W → Fin l → C)
    (hpairs : ∀ w, Function.Injective (Sum.elim (p w) (q w))) :
    (∑ f : C → Fin N, pairBadCount p q f) * N ^ l =
      Fintype.card W * N ^ Fintype.card C := by
  classical
  rw [Finset.sum_mul]
  simp_rw [pairBadCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  calc
    (∑ w : W, ∑ f : C → Fin N,
        if ∀ t, f (p w t) = f (q w t) then N ^ l else 0) =
        ∑ w : W,
          (Finset.univ.filter fun f : C → Fin N ↦
            ∀ t, f (p w t) = f (q w t)).card * N ^ l := by
      congr 1
      funext w
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_mul]
      simp
    _ = ∑ _w : W, N ^ Fintype.card C := by
      apply Finset.sum_congr rfl
      intro w _
      exact filter_pairEqual_card_mul_pow_of_injective_sum
        N l (p w) (q w) (hpairs w)
    _ = Fintype.card W * N ^ Fintype.card C := by simp

end Erdos1006NR5

namespace Erdos1006NR5

open scoped BigOperators
open Finset

abbrev UnorderedSlotPair := {p : Fin 5 × Fin 5 // p.1 < p.2}
abbrev OrderedSlotPair := {p : Fin 5 × Fin 5 // p.1 ≠ p.2}

lemma card_unorderedSlotPair : Fintype.card UnorderedSlotPair = 10 := by
  decide

lemma card_orderedSlotPair : Fintype.card OrderedSlotPair = 20 := by
  decide

abbrev SampleAt (n m : ℕ) := (Fin m × Fin 5) → Fin n
abbrev DegWitness (m : ℕ) := Fin m × UnorderedSlotPair
abbrev CycleWitness (m l : ℕ) := (Fin l → Fin m) × (Fin l → OrderedSlotPair)

def degP {m : ℕ} (w : DegWitness m) (_ : Fin 1) : Fin m × Fin 5 :=
  (w.1, w.2.1.1)

def degQ {m : ℕ} (w : DegWitness m) (_ : Fin 1) : Fin m × Fin 5 :=
  (w.1, w.2.1.2)

def degEvent {n m : ℕ} (w : DegWitness m) (sigma : SampleAt n m) : Prop :=
  ∀ t, sigma (degP w t) = sigma (degQ w t)

def cycleP {m l : ℕ} (w : CycleWitness m l) (t : Fin l) : Fin m × Fin 5 :=
  (w.1 t, (w.2 t).1.2)

def cycleQ {m l : ℕ} (w : CycleWitness m l) (t : Fin l) : Fin m × Fin 5 :=
  (w.1 (finRotate l t), (w.2 (finRotate l t)).1.1)

def cycleEvent {n m l : ℕ} (w : CycleWitness m l) (sigma : SampleAt n m) : Prop :=
  Function.Injective w.1 ∧ ∀ t, sigma (cycleP w t) = sigma (cycleQ w t)

lemma cycleQ_injective {m l : ℕ} (w : CycleWitness m l)
    (he : Function.Injective w.1) : Function.Injective (cycleQ w) := by
  intro a b hab
  apply (finRotate l).injective
  apply he
  exact congrArg Prod.fst hab

lemma cycleP_ne_cycleQ {m l : ℕ} (w : CycleWitness m l)
    (he : Function.Injective w.1) (a b : Fin l) : cycleP w a ≠ cycleQ w b := by
  intro hab
  have hindex : a = finRotate l b := he (congrArg Prod.fst hab)
  have hslot := congrArg Prod.snd hab
  simp only [cycleP, cycleQ] at hslot
  rw [← hindex] at hslot
  exact (w.2 a).2 hslot.symm

noncomputable def degEventFinset {n m : ℕ} (w : DegWitness m) : Finset (SampleAt n m) :=
  by classical exact Finset.univ.filter (degEvent w)

noncomputable def cycleEventFinset {n m l : ℕ} (w : CycleWitness m l) :
    Finset (SampleAt n m) :=
  by classical exact Finset.univ.filter (cycleEvent w)

lemma degEventFinset_card_mul (n m : ℕ) (w : DegWitness m) :
    #(degEventFinset (n := n) w) * n = n ^ (m * 5) := by
  classical
  rw [show degEventFinset w =
    Finset.univ.filter (fun sigma : (Fin m × Fin 5) → Fin n ↦
      ∀ t, sigma (degP w t) = sigma (degQ w t)) from by
        ext sigma
        simp [degEventFinset, degEvent]]
  simpa only [pow_one, Fintype.card_prod, Fintype.card_fin] using
    (filter_pairEqual_card_mul_pow n 1 (degP w) (degQ w)
      (fun _ _ _ ↦ Subsingleton.elim _ _)
      (fun _ _ h ↦ (ne_of_lt w.2.2) (congrArg Prod.snd h)))

lemma cycleEventFinset_card_mul_le (n m l : ℕ) (w : CycleWitness m l) :
    #(cycleEventFinset (n := n) w) * n ^ l ≤
      n ^ (m * 5) := by
  classical
  by_cases he : Function.Injective w.1
  · have hcount := filter_pairEqual_card_mul_pow n l (cycleP w) (cycleQ w)
      (cycleQ_injective w he) (cycleP_ne_cycleQ w he)
    rw [show cycleEventFinset w =
      Finset.univ.filter (fun sigma : (Fin m × Fin 5) → Fin n ↦
        Function.Injective w.1 ∧ ∀ t, sigma (cycleP w t) = sigma (cycleQ w t)) from by
          ext sigma
          simp [cycleEventFinset, cycleEvent]]
    simpa only [he, true_and, Fintype.card_prod, Fintype.card_fin] using hcount.le
  · have hempty : cycleEventFinset (n := n) w = ∅ := by
      ext sigma
      simp [cycleEventFinset, cycleEvent, he]
    rw [hempty]
    simp

lemma card_degWitness (m : ℕ) : Fintype.card (DegWitness m) = m * 10 := by
  simp [card_unorderedSlotPair]

lemma card_cycleWitness (l : ℕ) :
    Fintype.card (CycleWitness m l) = (20 * m) ^ l := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    card_orderedSlotPair]
  simp [mul_pow, mul_comm]

lemma card_sampleAt (n m : ℕ) : Fintype.card (SampleAt n m) = n ^ (m * 5) := by
  simp only [SampleAt, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod]

def N : ℕ := 2 ^ 64
def K : ℕ := 8192 * N
def M : ℕ := 16384 * N

def budgetAt (c : ℕ) : ℕ :=
  10 * c + (20 * c) ^ 2 + (20 * c) ^ 3 + (20 * c) ^ 4

def badBudget : ℕ := budgetAt 16384

lemma N_pos : 0 < N := by norm_num [N]
lemma badBudget_lt_K : badBudget < K := by
  norm_num [badBudget, budgetAt, K, N]

lemma M_eq : M = 16384 * N := rfl

abbrev Sample := SampleAt N M

noncomputable instance : Nonempty Sample :=
  ⟨fun _ ↦ ⟨0, N_pos⟩⟩

noncomputable def degWitnessFinset {n m : ℕ} (sigma : SampleAt n m) :
    Finset (DegWitness m) := by
  classical
  exact Finset.univ.filter fun w ↦ degEvent w sigma

noncomputable def cycleWitnessFinset {n m l : ℕ} (sigma : SampleAt n m) :
    Finset (CycleWitness m l) := by
  classical
  exact Finset.univ.filter fun w ↦ cycleEvent w sigma

lemma sum_degWitnessFinset_card (n m : ℕ) :
    (∑ sigma : SampleAt n m, #(degWitnessFinset sigma)) =
      ∑ w : DegWitness m, #(degEventFinset (n := n) w) := by
  classical
  simp only [degWitnessFinset, degEventFinset, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]

lemma sum_cycleWitnessFinset_card (n m l : ℕ) :
    (∑ sigma : SampleAt n m, #(cycleWitnessFinset (l := l) sigma)) =
      ∑ w : CycleWitness m l, #(cycleEventFinset (n := n) w) := by
  classical
  simp only [cycleWitnessFinset, cycleEventFinset, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]

lemma sum_degEventFinset_card_mul (n m : ℕ) :
    (∑ w : DegWitness m, #(degEventFinset (n := n) w)) * n =
      Fintype.card (DegWitness m) * n ^ (m * 5) := by
  rw [Finset.sum_mul]
  calc
    ∑ w : DegWitness m, #(degEventFinset w) * n =
        ∑ _w : DegWitness m, n ^ (m * 5) := by
      apply Finset.sum_congr rfl
      intro w _
      exact degEventFinset_card_mul n m w
    _ = Fintype.card (DegWitness m) * n ^ (m * 5) := by simp

lemma sum_cycleEventFinset_card_mul_le (n m l : ℕ) :
    (∑ w : CycleWitness m l, #(cycleEventFinset (n := n) w)) * n ^ l ≤
      Fintype.card (CycleWitness m l) * n ^ (m * 5) := by
  rw [Finset.sum_mul]
  calc
    ∑ w : CycleWitness m l, #(cycleEventFinset w) * n ^ l ≤
        ∑ _w : CycleWitness m l, n ^ (m * 5) :=
      Finset.sum_le_sum fun w _ ↦ cycleEventFinset_card_mul_le n m l w
    _ = Fintype.card (CycleWitness m l) * n ^ (m * 5) := by simp

lemma sum_degWitnessFinset_card_le_scaled (n m c : ℕ) (hn : 0 < n)
    (hm : m = c * n) :
    (∑ sigma : SampleAt n m, #(degWitnessFinset sigma)) ≤
      (c * 10) * n ^ (m * 5) := by
  rw [sum_degWitnessFinset_card]
  apply Nat.le_of_mul_le_mul_right (c := n) _ hn
  rw [sum_degEventFinset_card_mul, card_degWitness, hm]
  ring_nf
  exact le_rfl

lemma sum_cycleWitnessFinset_card_le_scaled (n m c l : ℕ) (hn : 0 < n)
    (hm : m = c * n) :
    (∑ sigma : SampleAt n m, #(cycleWitnessFinset (l := l) sigma)) ≤
      (20 * c) ^ l * n ^ (m * 5) := by
  rw [sum_cycleWitnessFinset_card]
  apply Nat.le_of_mul_le_mul_right (c := n ^ l) _ (Nat.pow_pos hn)
  refine (sum_cycleEventFinset_card_mul_le n m l).trans_eq ?_
  rw [card_cycleWitness, hm]
  ring

noncomputable def badWitnessCountAt {n m : ℕ} (sigma : SampleAt n m) : ℕ :=
  #(degWitnessFinset sigma) + #(cycleWitnessFinset (l := 2) sigma) +
    #(cycleWitnessFinset (l := 3) sigma) + #(cycleWitnessFinset (l := 4) sigma)

lemma sum_badWitnessCountAt_le_scaled (n m c : ℕ) (hn : 0 < n)
    (hm : m = c * n) :
    (∑ sigma : SampleAt n m, badWitnessCountAt sigma) ≤
      Fintype.card (SampleAt n m) * budgetAt c := by
  have hd := sum_degWitnessFinset_card_le_scaled n m c hn hm
  have h2 := sum_cycleWitnessFinset_card_le_scaled n m c 2 hn hm
  have h3 := sum_cycleWitnessFinset_card_le_scaled n m c 3 hn hm
  have h4 := sum_cycleWitnessFinset_card_le_scaled n m c 4 hn hm
  rw [show (∑ sigma : SampleAt n m, badWitnessCountAt sigma) =
      (∑ sigma : SampleAt n m, #(degWitnessFinset sigma)) +
      (∑ sigma : SampleAt n m, #(cycleWitnessFinset (l := 2) sigma)) +
      (∑ sigma : SampleAt n m, #(cycleWitnessFinset (l := 3) sigma)) +
      (∑ sigma : SampleAt n m, #(cycleWitnessFinset (l := 4) sigma)) by
        simp [badWitnessCountAt, Finset.sum_add_distrib]]
  calc
    _ ≤ (c * 10) * n ^ (m * 5) + (20 * c) ^ 2 * n ^ (m * 5) +
        (20 * c) ^ 3 * n ^ (m * 5) + (20 * c) ^ 4 * n ^ (m * 5) :=
      add_le_add (add_le_add (add_le_add hd h2) h3) h4
    _ = Fintype.card (SampleAt n m) * budgetAt c := by
      rw [card_sampleAt]
      simp only [budgetAt]
      ring

noncomputable def badWitnessCount : Sample → ℕ :=
  badWitnessCountAt

lemma exists_le_average_bound {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (bad : Omega → ℕ) (B : ℕ)
    (h : ∑ omega, bad omega ≤ Fintype.card Omega * B) :
    ∃ omega, bad omega ≤ B := by
  by_contra! hcontra
  have hstrict : Fintype.card Omega * B < ∑ omega, bad omega := by
    calc
      Fintype.card Omega * B = ∑ _omega : Omega, B := by simp
      _ < ∑ omega : Omega, bad omega := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact Finset.univ_nonempty
        · intro i _
          exact hcontra i
  omega

lemma exists_sample_small_badWitnessCountAt (n m c : ℕ) (hn : 0 < n)
    (hm : m = c * n) :
    ∃ sigma : SampleAt n m, badWitnessCountAt sigma ≤ budgetAt c := by
  letI : Nonempty (SampleAt n m) := ⟨fun _ ↦ ⟨0, hn⟩⟩
  exact exists_le_average_bound (badWitnessCountAt (n := n) (m := m))
    (budgetAt c) (sum_badWitnessCountAt_le_scaled n m c hn hm)

lemma exists_sample_small_badWitnessCount :
    ∃ sigma : Sample, badWitnessCount sigma ≤ badBudget := by
  simpa only [badWitnessCount, badBudget] using
    exists_sample_small_badWitnessCountAt N M 16384 N_pos M_eq

def degRoot {m : ℕ} (w : DegWitness m) : Fin m := w.1

def cycleRoot {m l : ℕ} [NeZero l] (w : CycleWitness m l) : Fin m :=
  w.1 0

noncomputable def badRootsAt {n m : ℕ} (sigma : SampleAt n m) : Finset (Fin m) :=
  (degWitnessFinset sigma).image degRoot ∪
    (cycleWitnessFinset (l := 2) sigma).image cycleRoot ∪
    (cycleWitnessFinset (l := 3) sigma).image cycleRoot ∪
    (cycleWitnessFinset (l := 4) sigma).image cycleRoot

lemma badRootsAt_card_le_badWitnessCountAt {n m : ℕ} (sigma : SampleAt n m) :
    #(badRootsAt sigma) ≤ badWitnessCountAt sigma := by
  classical
  let A := (degWitnessFinset sigma).image degRoot
  let B := (cycleWitnessFinset (l := 2) sigma).image cycleRoot
  let C := (cycleWitnessFinset (l := 3) sigma).image cycleRoot
  let D := (cycleWitnessFinset (l := 4) sigma).image cycleRoot
  have hA : #A ≤ #(degWitnessFinset sigma) := Finset.card_image_le
  have hB : #B ≤ #(cycleWitnessFinset (l := 2) sigma) := Finset.card_image_le
  have hC : #C ≤ #(cycleWitnessFinset (l := 3) sigma) := Finset.card_image_le
  have hD : #D ≤ #(cycleWitnessFinset (l := 4) sigma) := Finset.card_image_le
  have hAB : #(A ∪ B) ≤ #A + #B := Finset.card_union_le A B
  have hABC : #((A ∪ B) ∪ C) ≤ #(A ∪ B) + #C := Finset.card_union_le (A ∪ B) C
  have hABCD : #(((A ∪ B) ∪ C) ∪ D) ≤ #((A ∪ B) ∪ C) + #D :=
    Finset.card_union_le ((A ∪ B) ∪ C) D
  change #(((A ∪ B) ∪ C) ∪ D) ≤
    #(degWitnessFinset sigma) + #(cycleWitnessFinset (l := 2) sigma) +
      #(cycleWitnessFinset (l := 3) sigma) +
      #(cycleWitnessFinset (l := 4) sigma)
  omega

lemma exists_kept_avoiding_badRootsAt (n m k c : ℕ) (hn : 0 < n)
    (hm : m = c * n) (hm2 : m = 2 * k) (hbudget : budgetAt c < k) :
    ∃ sigma : SampleAt n m, ∃ keep : Fin k ↪ Fin m,
      badWitnessCountAt sigma ≤ budgetAt c ∧
        ∀ q, keep q ∉ badRootsAt sigma := by
  classical
  obtain ⟨sigma, hsigma⟩ := exists_sample_small_badWitnessCountAt n m c hn hm
  have hroots : #(badRootsAt sigma) < k :=
    lt_of_le_of_lt (badRootsAt_card_le_badWitnessCountAt sigma)
      (lt_of_le_of_lt hsigma hbudget)
  let survivors : Finset (Fin m) := Finset.univ \ badRootsAt sigma
  have hsurvivors : k ≤ #survivors := by
    have hcard : #survivors = m - #(badRootsAt sigma) := by
      simpa [survivors] using
        (Finset.card_sdiff_of_subset
          (s := badRootsAt sigma) (t := (Finset.univ : Finset (Fin m)))
          (Finset.subset_univ _))
    rw [hcard]
    omega
  obtain ⟨kept, hkept_sub, hkept_card⟩ :=
    Finset.exists_subset_card_eq hsurvivors
  let e : Fin k ≃ kept := (kept.equivFinOfCardEq hkept_card).symm
  let keep : Fin k ↪ Fin m :=
    e.toEmbedding.trans (Function.Embedding.subtype (fun i ↦ i ∈ kept))
  refine ⟨sigma, keep, hsigma, fun q ↦ ?_⟩
  have hmem_kept : keep q ∈ kept := (e q).2
  have hmem_survivors : keep q ∈ survivors := hkept_sub hmem_kept
  exact (Finset.mem_sdiff.mp hmem_survivors).2

lemma kept_block_injective {n m k : ℕ} (sigma : SampleAt n m)
    (keep : Fin k ↪ Fin m) (hkeep : ∀ q, keep q ∉ badRootsAt sigma) (q : Fin k) :
    Function.Injective (fun a : Fin 5 ↦ sigma (keep q, a)) := by
  classical
  intro a b hab
  by_contra hne
  by_cases hlt : a < b
  · let w : DegWitness m := ⟨keep q, ⟨(a, b), hlt⟩⟩
    have hw : w ∈ degWitnessFinset sigma := by
      simp only [degWitnessFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      intro t
      fin_cases t
      exact hab
    apply hkeep q
    simp only [badRootsAt, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl (Or.inl ⟨w, hw, rfl⟩))
  · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hlt) (fun h ↦ hne h.symm)
    let w : DegWitness m := ⟨keep q, ⟨(b, a), hba⟩⟩
    have hw : w ∈ degWitnessFinset sigma := by
      simp only [degWitnessFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      intro t
      fin_cases t
      exact hab.symm
    apply hkeep q
    simp only [badRootsAt, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl (Or.inl ⟨w, hw, rfl⟩))

lemma no_kept_cycleEvent {n m k l : ℕ} [NeZero l]
    (sigma : SampleAt n m) (keep : Fin k ↪ Fin m)
    (hkeep : ∀ q, keep q ∉ badRootsAt sigma)
    (hl : l = 2 ∨ l = 3 ∨ l = 4) (w : CycleWitness m l)
    (hw : cycleEvent w sigma) :
    ¬ (∀ t, ∃ q, keep q = w.1 t) := by
  classical
  intro hsupported
  obtain ⟨q, hq⟩ := hsupported 0
  apply hkeep q
  rcases hl with rfl | rfl | rfl
  · simp only [badRootsAt, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl (Or.inr ⟨w, by simp [cycleWitnessFinset, hw], hq.symm⟩))
  · simp only [badRootsAt, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inr ⟨w, by simp [cycleWitnessFinset, hw], hq.symm⟩)
  · simp only [badRootsAt, Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨w, by simp [cycleWitnessFinset, hw], hq.symm⟩

def InBlock {X I : Type*} (block : I → Fin 5 → X) (i : I) (x : X) : Prop :=
  ∃ a, x = block i a

def NoBergeTwo {X I : Type*} (block : I → Fin 5 → X) : Prop :=
  ∀ {i j}, i ≠ j → ∀ {x y}, x ≠ y →
    InBlock block i x → InBlock block i y →
    InBlock block j x → InBlock block j y → False

def NoBergeThree {X I : Type*} (block : I → Fin 5 → X) : Prop :=
  ∀ {i j k}, i ≠ j → i ≠ k → j ≠ k →
    ∀ {x y z}, x ≠ y → x ≠ z → y ≠ z →
      InBlock block i x → InBlock block i y →
      InBlock block j y → InBlock block j z →
      InBlock block k z → InBlock block k x → False

def NoBergeFour {X I : Type*} (block : I → Fin 5 → X) : Prop :=
  ∀ {i j k l}, i ≠ j → i ≠ k → i ≠ l →
    j ≠ k → j ≠ l → k ≠ l →
    ∀ {w x y z}, w ≠ x → w ≠ y → w ≠ z →
      x ≠ y → x ≠ z → y ≠ z →
      InBlock block i w → InBlock block i x →
      InBlock block j x → InBlock block j y →
      InBlock block k y → InBlock block k z →
      InBlock block l z → InBlock block l w → False

lemma kept_noBergeTwo {n m k : ℕ} (sigma : SampleAt n m)
    (keep : Fin k ↪ Fin m) (hkeep : ∀ q, keep q ∉ badRootsAt sigma) :
    NoBergeTwo (fun q a ↦ sigma (keep q, a)) := by
  classical
  intro i j hij x y hxy
  rintro ⟨ai, hix⟩ ⟨bi, hiy⟩ ⟨aj, hjx⟩ ⟨bj, hjy⟩
  have hab_i : ai ≠ bi := by
    intro h
    apply hxy
    rw [hix, hiy, h]
  have hab_j : bj ≠ aj := by
    intro h
    apply hxy
    rw [hjx, hjy, h]
  let edge : Fin 2 → Fin k := ![i, j]
  have hedge : Function.Injective edge := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [edge]
  let slots : Fin 2 → OrderedSlotPair :=
    ![⟨(ai, bi), hab_i⟩, ⟨(bj, aj), hab_j⟩]
  let witness : CycleWitness m 2 := (fun t ↦ keep (edge t), slots)
  have hw : cycleEvent witness sigma := by
    refine ⟨keep.injective.comp hedge, ?_⟩
    intro t
    fin_cases t
    · simpa [witness, edge, slots, cycleP, cycleQ, finRotate_apply_zero,
        finRotate_last] using hiy.symm.trans hjy
    · simpa [witness, edge, slots, cycleP, cycleQ, finRotate_apply_zero,
        finRotate_last] using hjx.symm.trans hix
  apply no_kept_cycleEvent sigma keep hkeep (Or.inl rfl) witness hw
  intro t
  exact ⟨edge t, rfl⟩

lemma kept_noBergeThree {n m k : ℕ} (sigma : SampleAt n m)
    (keep : Fin k ↪ Fin m) (hkeep : ∀ q, keep q ∉ badRootsAt sigma) :
    NoBergeThree (fun q a ↦ sigma (keep q, a)) := by
  classical
  intro i j k' hij hik hjk x y z hxy hxz hyz
  rintro ⟨ai, hix⟩ ⟨bi, hiy⟩ ⟨aj, hjy⟩ ⟨bj, hjz⟩
    ⟨ak, hkz⟩ ⟨bk, hkx⟩
  have hab_i : ai ≠ bi := by
    intro h
    apply hxy
    rw [hix, hiy, h]
  have hab_j : aj ≠ bj := by
    intro h
    apply hyz
    rw [hjy, hjz, h]
  have hab_k : ak ≠ bk := by
    intro h
    apply hxz.symm
    rw [hkz, hkx, h]
  let edge : Fin 3 → Fin k := ![i, j, k']
  have hedge : Function.Injective edge := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [edge]
  let slots : Fin 3 → OrderedSlotPair :=
    ![⟨(ai, bi), hab_i⟩, ⟨(aj, bj), hab_j⟩, ⟨(ak, bk), hab_k⟩]
  let witness : CycleWitness m 3 := (fun t ↦ keep (edge t), slots)
  have hw : cycleEvent witness sigma := by
    refine ⟨keep.injective.comp hedge, ?_⟩
    intro t
    fin_cases t
    · simpa [witness, edge, slots, cycleP, cycleQ, finRotate_apply_zero,
        finRotate_last] using hiy.symm.trans hjy
    · simpa [witness, edge, slots, cycleP, cycleQ, finRotate_apply_zero,
        finRotate_of_lt, finRotate_last] using hjz.symm.trans hkz
    · simpa [witness, edge, slots, cycleP, cycleQ, finRotate_apply_zero,
        finRotate_last] using hkx.symm.trans hix
  apply no_kept_cycleEvent sigma keep hkeep (Or.inr (Or.inl rfl)) witness hw
  intro t
  exact ⟨edge t, rfl⟩

lemma kept_noBergeFour {n m k : ℕ} (sigma : SampleAt n m)
    (keep : Fin k ↪ Fin m) (hkeep : ∀ q, keep q ∉ badRootsAt sigma) :
    NoBergeFour (fun q a ↦ sigma (keep q, a)) := by
  classical
  intro i j k' l hij hik hil hjk hjl hkl w x y z hwx hwy hwz hxy hxz hyz
  rintro ⟨ai, hiw⟩ ⟨bi, hix⟩ ⟨aj, hjx⟩ ⟨bj, hjy⟩
    ⟨ak, hky⟩ ⟨bk, hkz⟩ ⟨al, hlz⟩ ⟨bl, hlw⟩
  have hab_i : ai ≠ bi := by
    intro h
    apply hwx
    rw [hiw, hix, h]
  have hab_j : aj ≠ bj := by
    intro h
    apply hxy
    rw [hjx, hjy, h]
  have hab_k : ak ≠ bk := by
    intro h
    apply hyz
    rw [hky, hkz, h]
  have hab_l : al ≠ bl := by
    intro h
    apply hwz.symm
    rw [hlz, hlw, h]
  let edge : Fin 4 → Fin k := ![i, j, k', l]
  have hedge : Function.Injective edge := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [edge]
  let slots : Fin 4 → OrderedSlotPair :=
    ![⟨(ai, bi), hab_i⟩, ⟨(aj, bj), hab_j⟩,
      ⟨(ak, bk), hab_k⟩, ⟨(al, bl), hab_l⟩]
  let witness : CycleWitness m 4 := (fun t ↦ keep (edge t), slots)
  have hevent : cycleEvent witness sigma := by
    refine ⟨keep.injective.comp hedge, ?_⟩
    intro t
    fin_cases t
    · simpa [witness, edge, slots, cycleP, cycleQ, finRotate_apply_zero,
        finRotate_last] using hix.symm.trans hjx
    · simpa [witness, edge, slots, cycleP, cycleQ, finRotate_apply_zero,
        finRotate_of_lt, finRotate_last] using hjy.symm.trans hky
    · simpa [witness, edge, slots, cycleP, cycleQ, finRotate_apply_zero,
        finRotate_of_lt, finRotate_last] using hkz.symm.trans hlz
    · simpa [witness, edge, slots, cycleP, cycleQ, finRotate_apply_zero,
        finRotate_last] using hlw.symm.trans hiw
  apply no_kept_cycleEvent sigma keep hkeep (Or.inr (Or.inr rfl)) witness hevent
  intro t
  exact ⟨edge t, rfl⟩

lemma M_eq_two_K : M = 2 * K := by
  simp only [M, K]
  ring

/-- The first, alteration stage of the specialized Nešetřil--Rödl
construction: `K` injective five-vertex carrier blocks with no Berge cycle
of length two, three, or four. -/
theorem exists_NR_carrier :
    ∃ block : Fin K → Fin 5 → Fin N,
      (∀ i, Function.Injective (block i)) ∧ NoBergeTwo block ∧
        NoBergeThree block ∧ NoBergeFour block := by
  have hbudget : budgetAt 16384 < K := by
    simpa only [badBudget] using badBudget_lt_K
  obtain ⟨sigma, keep, _hcount, hkeep⟩ :=
    exists_kept_avoiding_badRootsAt N M K 16384 N_pos M_eq M_eq_two_K hbudget
  let block : Fin K → Fin 5 → Fin N := fun q a ↦ sigma (keep q, a)
  refine ⟨block, fun i ↦ kept_block_injective sigma keep hkeep i,
    kept_noBergeTwo sigma keep hkeep, kept_noBergeThree sigma keep hkeep,
    kept_noBergeFour sigma keep hkeep⟩

end Erdos1006NR5


