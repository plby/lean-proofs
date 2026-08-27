import ErdosProblems.Erdos4.FGKMTMixedDivisorMass
import ErdosProblems.Erdos4.FGKMTDivisorLabels
import Mathlib.Logic.Equiv.Option

/-! The two face completions of a common divisor core, with exact product cutoffs. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

variable {k R : ℕ}

abbrev SieveCore (j : Fin k) := {i : Fin k // i ≠ j}

def faceIndex (j : Fin k) (s : Fin 2) (i : Fin k) : SieveCore j ⊕ Fin 2 :=
  if hi : i = j then Sum.inr s else Sum.inl ⟨i, hi⟩

@[simp] theorem faceIndex_anchor (j : Fin k) (s : Fin 2) : faceIndex j s j = Sum.inr s := by
  simp [faceIndex]

@[simp] theorem faceIndex_core (j : Fin k) (s : Fin 2) (i : SieveCore j) :
    faceIndex j s i = Sum.inl i := by
  simp [faceIndex, i.property]

theorem faceIndex_injective (j : Fin k) (s : Fin 2) : Function.Injective (faceIndex j s) := by
  intro i l hil
  by_cases hi : i = j
  · subst i
    by_cases hl : l = j
    · exact hl.symm
    · simp [faceIndex, hl] at hil
  · by_cases hl : l = j
    · subst l
      simp [faceIndex, hi] at hil
    · simp only [faceIndex, dif_neg hi, dif_neg hl, Sum.inl.injEq] at hil
      exact congrArg Subtype.val hil

def faceTuple (j : Fin k) (s : Fin 2) (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1)) : Fin k → ℕ :=
  fun i => (a (faceIndex j s i) : ℕ)

@[simp] theorem faceTuple_anchor (j : Fin k) (s : Fin 2)
    (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1)) : faceTuple j s a j = (a (Sum.inr s) : ℕ) := by
  simp [faceTuple]

@[simp] theorem faceTuple_core (j : Fin k) (s : Fin 2)
    (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1)) (i : SieveCore j) :
    faceTuple j s a i = (a (Sum.inl i) : ℕ) := by
  simp [faceTuple]

theorem faceTuple_pairwise (j : Fin k) (s : Fin 2)
    (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1))
    (ha : Pairwise (fun i l => (a i : ℕ).Coprime (a l : ℕ))) :
    Pairwise (fun i l => (faceTuple j s a i).Coprime (faceTuple j s a l)) := by
  intro i l hil
  exact ha (fun heq => hil (faceIndex_injective j s heq))

theorem prod_faceTuple {M : Type*} [CommMonoid M] (f : ℕ → M) (j : Fin k) (s : Fin 2)
    (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1)) :
    (∏ i : Fin k, f (faceTuple j s a i)) =
      f (a (Sum.inr s)) * ∏ i : SieveCore j, f (a (Sum.inl i)) := by
  have hh := (Equiv.optionSubtypeNe j).prod_comp (fun i : Fin k => f (faceTuple j s a i))
  rw [Fintype.prod_option] at hh
  simpa only [Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some,
    faceTuple_anchor, faceTuple_core] using hh.symm

theorem sum_log_faceTuple (j : Fin k) (s : Fin 2)
    (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1)) :
    (∑ i : Fin k, Real.log (faceTuple j s a i : ℝ)) =
      Real.log (a (Sum.inr s) : ℕ) + mixedCoreLog (SieveCore j) a := by
  have hh := (Equiv.optionSubtypeNe j).sum_comp
    (fun i : Fin k => Real.log (faceTuple j s a i : ℝ))
  rw [Fintype.sum_option] at hh
  simpa only [Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some,
    faceTuple_anchor, faceTuple_core, mixedCoreLog] using hh.symm

theorem log_face_cutoff {T R : ℕ} (hT : 1 ≤ T) (hTR : T ^ 2 ≤ R)
    {n : ℕ} (hn : 0 < n) (hnT : n ≤ T) : Real.log (n : ℝ) ≤ Real.log (R : ℝ) / 2 := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (zero_lt_one.trans_le hT)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnTreal : (n : ℝ) ≤ T := by exact_mod_cast hnT
  have hsmall := Real.log_le_log hnpos hnTreal
  have hsquare : (T : ℝ) ^ 2 ≤ R := by exact_mod_cast hTR
  have hlarge := Real.log_le_log (pow_pos hTpos 2) hsquare
  rw [Real.log_pow] at hlarge
  norm_num only [Nat.cast_ofNat] at hlarge
  linarith

theorem faceTuple_product_le (j : Fin k) (s : Fin 2)
    {W T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ^ 2 ≤ R)
    (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1))
    (ha : MixedDivisorGood (SieveCore j) W T (Real.log (R : ℝ) / 2) a) :
    (∏ i : Fin k, faceTuple j s a i) ≤ R := by
  have hpos (i : Fin k) : 0 < faceTuple j s a i :=
    Nat.pos_of_ne_zero (ha.1 (faceIndex j s i)).1.ne_zero
  have hprod : (0 : ℝ) < (∏ i : Fin k, faceTuple j s a i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (zero_lt_one.trans_le hR)
  have hlogprod : Real.log (∏ i : Fin k, faceTuple j s a i : ℕ) =
      ∑ i : Fin k, Real.log (faceTuple j s a i : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro i _
    exact_mod_cast (hpos i).ne'
  have hface := log_face_cutoff hT hTR
    (Nat.pos_of_ne_zero (ha.1 (Sum.inr s)).1.ne_zero) (ha.2.1 s)
  have hlog : Real.log (∏ i : Fin k, faceTuple j s a i : ℕ) ≤ Real.log (R : ℝ) := by
    rw [hlogprod, sum_log_faceTuple]
    linarith [ha.2.2.1]
  exact_mod_cast (Real.log_le_log_iff hprod hRpos).mp hlog

end Erdos4.FGKMT
