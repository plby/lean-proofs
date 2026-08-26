import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Finset

namespace Erdos489

/-- Number of residues below `N` avoiding every modulus in a list. -/
def avoidCount (l : List ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => ∀ a ∈ l, ¬ a ∣ n).card

lemma periodic_filter_card_mul (f : ℕ → Prop) [DecidablePred f] {P : ℕ}
    (hf : Function.Periodic f P) (k : ℕ) :
    ((Finset.range (k * P)).filter f).card =
      k * ((Finset.range P).filter f).card := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Finset.card_filter, Finset.sum_range_add]
      rw [Finset.card_filter] at ih
      rw [ih]
      have hshift : ∀ i, (if f (k * P + i) then 1 else 0) =
          (if f i then 1 else 0) := by
        intro i
        have hi := hf.nat_mul k i
        simp only [Nat.cast_id] at hi
        rw [Nat.add_comm] at hi
        simpa only [hi]
      simp_rw [hshift]
      rw [← Finset.card_filter f (Finset.range P)]
      change k * ((Finset.range P).filter f).card +
          ((Finset.range P).filter f).card =
        (k + 1) * ((Finset.range P).filter f).card
      rw [Nat.add_mul]
      simp

/-- Avoiding a finite list of divisors is periodic with period the product of
that list.  The zero residue is intentionally included. -/
lemma avoidList_periodic (l : List ℕ) :
    Function.Periodic (fun n : ℕ => ∀ a ∈ l, ¬ a ∣ n) l.prod := by
  intro n
  apply propext
  constructor
  · intro hn a ha han
    apply hn a ha
    exact (Nat.dvd_add_iff_left (List.dvd_prod ha)).1 han
  · intro hn a ha han
    apply hn a ha
    exact (Nat.dvd_add_iff_left (List.dvd_prod ha)).2 han

lemma avoidCount_mul_prod (l : List ℕ) (k : ℕ) :
    avoidCount l (k * l.prod) = k * avoidCount l l.prod := by
  exact periodic_filter_card_mul (fun n => ∀ a ∈ l, ¬ a ∣ n)
    (avoidList_periodic l) k

/-- Adding one modulus `a` removes at most one old survivor per old period.
The injection sends an old survivor divisible by `a` to its quotient by `a`. -/
lemma sub_one_mul_avoidCount_le_cons (a : ℕ) (l : List ℕ) (ha : 0 < a) :
    (a - 1) * avoidCount l l.prod ≤ avoidCount (a :: l) (a * l.prod) := by
  let old : Finset ℕ :=
    (Finset.range (a * l.prod)).filter fun n => ∀ c ∈ l, ¬ c ∣ n
  let bad : Finset ℕ := old.filter fun n => a ∣ n
  let base : Finset ℕ :=
    (Finset.range l.prod).filter fun n => ∀ c ∈ l, ¬ c ∣ n
  have hbad : bad.card ≤ base.card := by
    apply Finset.card_le_card_of_injOn (fun n => n / a)
    · intro n hn
      have hnb : n ∈ bad := hn
      obtain ⟨hnold, hna⟩ := Finset.mem_filter.mp hnb
      obtain ⟨hnrange, hnl⟩ := Finset.mem_filter.mp hnold
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_⟩
      · apply (Nat.div_lt_iff_lt_mul ha).2
        simpa [Nat.mul_comm] using hnrange
      · intro c hc hcd
        apply hnl c hc
        rw [← Nat.div_mul_cancel hna]
        exact dvd_mul_of_dvd_left hcd a
    · intro n hn m hm hnm
      have hnb : n ∈ bad := hn
      have hmb : m ∈ bad := hm
      have hna : a ∣ n := (Finset.mem_filter.mp hnb).2
      have hma : a ∣ m := (Finset.mem_filter.mp hmb).2
      change n / a = m / a at hnm
      calc
        n = n / a * a := (Nat.div_mul_cancel hna).symm
        _ = m / a * a := by rw [hnm]
        _ = m := Nat.div_mul_cancel hma
  have hpartition :
      avoidCount (a :: l) (a * l.prod) + bad.card = old.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := old) (p := fun n => ¬ a ∣ n)
    have hnew : old.filter (fun n => ¬ a ∣ n) =
        (Finset.range (a * l.prod)).filter
          (fun n => ∀ c ∈ a :: l, ¬ c ∣ n) := by
      ext n
      simp only [old, Finset.mem_filter, Finset.mem_range, List.mem_cons]
      constructor
      · rintro ⟨⟨hn, hl⟩, hna⟩
        exact ⟨hn, fun c hc => hc.elim (fun hca => hca ▸ hna) (hl c)⟩
      · rintro ⟨hn, hall⟩
        exact ⟨⟨hn, fun c hc => hall c (Or.inr hc)⟩,
          hall a (Or.inl rfl)⟩
    have hbad' : old.filter (fun n => ¬ ¬ a ∣ n) = bad := by
      ext n
      simp [bad]
    rw [hbad'] at h
    rw [hnew] at h
    simpa only [avoidCount] using h
  have hold : old.card = a * base.card := by
    simpa only [old, base, avoidCount] using avoidCount_mul_prod l a
  have hbase : base.card = avoidCount l l.prod := by rfl
  rw [hold, hbase] at hpartition
  rw [hbase] at hbad
  have ha_split : a = (a - 1) + 1 := by omega
  have hnum : a * avoidCount l l.prod =
      (a - 1) * avoidCount l l.prod + avoidCount l l.prod := by
    calc
      a * avoidCount l l.prod = ((a - 1) + 1) * avoidCount l l.prod :=
        congrArg (fun z => z * avoidCount l l.prod) ha_split
      _ = (a - 1) * avoidCount l l.prod + avoidCount l l.prod := by
        rw [Nat.add_mul, one_mul]
  rw [hnum] at hpartition
  omega

/-- Finite Heilbronn--Rohrbach product-density inequality, in exact integral
form.  Over the product period, the number of residues avoiding every modulus
is at least the product of the individual survivor counts `a-1`. -/
theorem heilbronn_rohrbach_count (l : List ℕ) (hl : ∀ a ∈ l, 1 < a) :
    (l.map fun a => a - 1).prod ≤ avoidCount l l.prod := by
  induction l with
  | nil => simp [avoidCount]
  | cons a l ih =>
      have ha : 0 < a := (hl a (by simp)).trans' Nat.zero_lt_one
      have htail : ∀ c ∈ l, 1 < c := by
        intro c hc
        exact hl c (by simp [hc])
      have hrec := sub_one_mul_avoidCount_le_cons a l ha
      rw [List.map_cons, List.prod_cons, List.prod_cons]
      exact (Nat.mul_le_mul_left (a - 1) (ih htail)).trans hrec

end Erdos489
