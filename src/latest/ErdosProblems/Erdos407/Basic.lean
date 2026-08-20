/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Foundational definitions and elementary counting lemmas for Erdős Problem 407.
-/
import Mathlib

namespace Erdos407

open scoped BigOperators Matrix

/-- An ordered exponent quadruple occurring in Problem 407. -/
@[ext]
structure Rep where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq

/-- The integer represented by an ordered exponent quadruple. -/
def Rep.value (r : Rep) : ℕ :=
  2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d

/-- The set of ordered exponent quadruples representing `n`. -/
def solutions (n : ℕ) : Set Rep := {r | r.value = n}

/-- The literal representation-counting function from Problem 407. -/
noncomputable def w (n : ℕ) : ℕ := (solutions n).ncard

private theorem le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_two]
      have hk : 0 < 2 ^ k := pow_pos (by omega) _
      omega

private theorem le_three_pow (k : ℕ) : k ≤ 3 ^ k := by
  calc
    k ≤ 2 ^ k := le_two_pow k
    _ ≤ 3 ^ k := Nat.pow_le_pow_left (by omega) k

/-- Every exponent in a representation of `n` is at most `n`. -/
theorem Rep.coordinate_le {r : Rep} {n : ℕ} (hr : r ∈ solutions n) :
    r.a ≤ n ∧ r.b ≤ n ∧ r.c ≤ n ∧ r.d ≤ n := by
  change r.value = n at hr
  have ha_pow : 2 ^ r.a ≤ n := by
    calc
      2 ^ r.a ≤ 2 ^ r.a + 3 ^ r.b := Nat.le_add_right _ _
      _ ≤ 2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d := Nat.le_add_right _ _
      _ = n := hr
  have hb_pow : 3 ^ r.b ≤ n := by
    calc
      3 ^ r.b ≤ 2 ^ r.a + 3 ^ r.b := Nat.le_add_left _ _
      _ ≤ 2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d := Nat.le_add_right _ _
      _ = n := hr
  have hc_pow : 2 ^ r.c ≤ n := by
    calc
      2 ^ r.c ≤ 2 ^ r.c * 3 ^ r.d :=
        le_mul_of_one_le_right (Nat.zero_le _) (one_le_pow₀ (by omega))
      _ ≤ 2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d := Nat.le_add_left _ _
      _ = n := hr
  have hd_pow : 3 ^ r.d ≤ n := by
    calc
      3 ^ r.d ≤ 2 ^ r.c * 3 ^ r.d :=
        le_mul_of_one_le_left (Nat.zero_le _) (one_le_pow₀ (by omega))
      _ ≤ 2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d := Nat.le_add_left _ _
      _ = n := hr
  exact ⟨(le_two_pow r.a).trans ha_pow,
    (le_three_pow r.b).trans hb_pow,
    (le_two_pow r.c).trans hc_pow,
    (le_three_pow r.d).trans hd_pow⟩

/-- The solution set for each fixed right-hand side is finite. -/
theorem solutions_finite (n : ℕ) : (solutions n).Finite := by
  let box : Set (ℕ × ℕ × ℕ × ℕ) :=
    Set.Iic n ×ˢ (Set.Iic n ×ˢ (Set.Iic n ×ˢ Set.Iic n))
  apply Set.Finite.of_injOn (f := fun r : Rep => (r.a, r.b, r.c, r.d))
      (t := box)
  · intro r hr
    exact Rep.coordinate_le hr
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    exact Rep.ext hxy.1 hxy.2.1 hxy.2.2.1 hxy.2.2.2
  · exact Set.Finite.prod (Set.finite_Iic n)
      (Set.Finite.prod (Set.finite_Iic n)
        (Set.Finite.prod (Set.finite_Iic n) (Set.finite_Iic n)))

/-- `w n` really is the cardinality of the finite solution set. -/
theorem w_eq_card_toFinset (n : ℕ) :
    w n = (solutions_finite n).toFinset.card := by
  exact Set.ncard_eq_toFinset_card (solutions n) (solutions_finite n)

private theorem mixedPow_injective :
    Function.Injective (fun p : ℕ × ℕ => 2 ^ p.1 * 3 ^ p.2) := by
  rintro ⟨c, d⟩ ⟨c', d'⟩ h
  have htwo := congrArg (fun n : ℕ => n.factorization 2) h
  have hthree := congrArg (fun n : ℕ => n.factorization 3) h
  norm_num [Nat.factorization_mul, Nat.factorization_pow,
    Nat.Prime.factorization_self, Nat.factorization_eq_zero_of_not_dvd] at htwo hthree
  exact Prod.ext htwo hthree

/-- The three summands, with their roles retained. -/
def Rep.encodeNat (r : Rep) : Fin 3 → ℕ :=
  ![2 ^ r.a, 3 ^ r.b, 2 ^ r.c * 3 ^ r.d]

theorem Rep.encodeNat_injective : Function.Injective Rep.encodeNat := by
  intro r s hrs
  have ha : 2 ^ r.a = 2 ^ s.a := congrFun hrs 0
  have hb : 3 ^ r.b = 3 ^ s.b := congrFun hrs 1
  have hcd : 2 ^ r.c * 3 ^ r.d = 2 ^ s.c * 3 ^ s.d := congrFun hrs 2
  have ha' := Nat.pow_right_injective (by omega : 2 ≤ 2) ha
  have hb' := Nat.pow_right_injective (by omega : 2 ≤ 3) hb
  have hcd' : (r.c, r.d) = (s.c, s.d) := by
    apply mixedPow_injective
    exact hcd
  exact Rep.ext ha' hb' (congrArg Prod.fst hcd') (congrArg Prod.snd hcd')

/-!
## Ordered exponent tuples versus unordered summand multisets
-/

/-- The value of the mixed summand. -/
def Rep.mixed (r : Rep) : ℕ := 2 ^ r.c * 3 ^ r.d

/-- The unordered multiset convention used by Tijdeman--Wang and
Bajpai--Bennett.  The mixed term is placed first only to simplify cancellation
in the fibre proof; the result is a multiset, so this order is not observable. -/
def Rep.summands (r : Rep) : Multiset ℕ :=
  r.mixed ::ₘ {2 ^ r.a, 3 ^ r.b}

/-- Unordered summand classes representing `n`. -/
def classes (n : ℕ) : Set (Multiset ℕ) := Rep.summands '' solutions n

theorem classes_finite (n : ℕ) : (classes n).Finite :=
  (solutions_finite n).image Rep.summands

/-- The later papers' unordered representation count. -/
noncomputable def omega (n : ℕ) : ℕ := (classes n).ncard

private theorem two_pow_eq_three_pow {a b : ℕ} (h : 2 ^ a = 3 ^ b) :
    a = 0 ∧ b = 0 := by
  have htwo := congrArg (fun n : ℕ => n.factorization 2) h
  have hthree := congrArg (fun n : ℕ => n.factorization 3) h
  norm_num [Nat.factorization_pow, Nat.Prime.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd] at htwo hthree
  exact ⟨htwo, hthree.symm⟩

private theorem pair_multiset_eq {x y z w : ℕ}
    (h : ({x, y} : Multiset ℕ) = {z, w}) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  have h' : (x = z ∧ y = w) ∨ (x ≠ z ∧ y = z ∧ w = x) := by
    simpa [Multiset.cons_eq_cons] using h
  rcases h' with hdirect | ⟨_, hyz, hwx⟩
  · exact Or.inl hdirect
  · exact Or.inr ⟨hwx.symm, hyz⟩

private theorem Rep.eq_of_summands_eq_of_mixed_eq {r s : Rep}
    (hsum : r.summands = s.summands) (hmix : r.mixed = s.mixed) : r = s := by
  have hcd : (r.c, r.d) = (s.c, s.d) := by
    apply mixedPow_injective
    exact hmix
  have hpure : ({2 ^ r.a, 3 ^ r.b} : Multiset ℕ) = {2 ^ s.a, 3 ^ s.b} := by
    apply (Multiset.cons_inj_right s.mixed).mp
    simpa [Rep.summands, hmix] using hsum
  rcases pair_multiset_eq hpure with ⟨ha, hb⟩ | ⟨hab, hba⟩
  · exact Rep.ext
      (Nat.pow_right_injective (by omega) ha)
      (Nat.pow_right_injective (by omega) hb)
      (congrArg Prod.fst hcd) (congrArg Prod.snd hcd)
  · have hra : r.a = 0 := (two_pow_eq_three_pow hab).1
    have hsb : s.b = 0 := (two_pow_eq_three_pow hab).2
    have hsa : s.a = 0 := (two_pow_eq_three_pow hba.symm).1
    have hrb : r.b = 0 := (two_pow_eq_three_pow hba.symm).2
    exact Rep.ext (hra.trans hsa.symm) (hrb.trans hsb.symm)
      (congrArg Prod.fst hcd) (congrArg Prod.snd hcd)

private def classFiber (n : ℕ) (S : Multiset ℕ) : Set Rep :=
  {r | r ∈ solutions n ∧ r.summands = S}

private theorem classFiber_finite (n : ℕ) (S : Multiset ℕ) :
    (classFiber n S).Finite :=
  (solutions_finite n).subset fun _ hr => hr.1

/-- A fixed unordered summand multiset has at most three ordered exponent
quadruples above it. -/
theorem classFiber_ncard_le_three (n : ℕ) (S : Multiset ℕ) (hcard : S.card = 3) :
    (classFiber n S).ncard ≤ 3 := by
  have htarget : ((S.toFinset : Finset ℕ) : Set ℕ).Finite := S.toFinset.finite_toSet
  have hinj : Set.InjOn Rep.mixed (classFiber n S) := by
    intro r hr s hs hrs
    exact Rep.eq_of_summands_eq_of_mixed_eq (hr.2.trans hs.2.symm) hrs
  calc
    (classFiber n S).ncard ≤ ((S.toFinset : Finset ℕ) : Set ℕ).ncard :=
      Set.ncard_le_ncard_of_injOn Rep.mixed
        (fun (r : Rep) (hr : r ∈ classFiber n S) => by
          change r.mixed ∈ S.toFinset
          rw [Multiset.mem_toFinset, ← hr.2]
          change r.mixed ∈ r.mixed ::ₘ ({2 ^ r.a, 3 ^ r.b} : Multiset ℕ)
          exact Multiset.mem_cons_self r.mixed ({2 ^ r.a, 3 ^ r.b} : Multiset ℕ))
        hinj htarget
    _ = S.toFinset.card := Set.ncard_coe_finset S.toFinset
    _ ≤ S.card := Multiset.toFinset_card_le S
    _ = 3 := hcard

/-- The literal raw count is at most three times the unordered count used in
the effective theorem of Bajpai--Bennett. -/
theorem w_le_three_mul_omega (n : ℕ) : w n ≤ 3 * omega n := by
  let s : Finset Rep := (solutions_finite n).toFinset
  let t : Finset (Multiset ℕ) := s.image Rep.summands
  have hs_mem (r : Rep) : r ∈ s ↔ r ∈ solutions n := by
    simp [s]
  have ht_mem (S : Multiset ℕ) : S ∈ t ↔ S ∈ classes n := by
    simp only [t, Finset.mem_image, classes, Set.mem_image]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, (hs_mem r).mp hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, (hs_mem r).mpr hr, rfl⟩
  have homega : omega n = t.card := by
    rw [omega, Set.ncard_eq_toFinset_card (classes n) (classes_finite n)]
    congr 1
    ext S
    exact (classes_finite n).mem_toFinset.trans (ht_mem S).symm
  have hfiber (S : Multiset ℕ) (hS : S ∈ t) :
      (s.filter fun r => r.summands = S).card ≤ 3 := by
    have hScard : S.card = 3 := by
      rcases (ht_mem S).mp hS with ⟨r, _, rfl⟩
      simp [Rep.summands]
    have hset :
        ((s.filter fun r => r.summands = S : Finset Rep) : Set Rep) = classFiber n S := by
      ext r
      simp [classFiber, hs_mem]
    rw [← Set.ncard_coe_finset (s.filter fun r => r.summands = S), hset]
    exact classFiber_ncard_le_three n S hScard
  calc
    w n = s.card := w_eq_card_toFinset n
    _ = ∑ S ∈ t, (s.filter fun r => r.summands = S).card :=
      Finset.card_eq_sum_card_fiberwise fun r hr => Finset.mem_image_of_mem _ hr
    _ ≤ ∑ _S ∈ t, 3 := Finset.sum_le_sum fun S hS => hfiber S hS
    _ = 3 * t.card := by simp [Nat.mul_comm]
    _ = 3 * omega n := by rw [homega]

end Erdos407
