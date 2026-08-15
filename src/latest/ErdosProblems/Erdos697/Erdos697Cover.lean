import Mathlib
import ErdosProblems.Erdos697.Erdos697CRTModel
import ErdosProblems.Erdos697.Erdos697WeightedSubset

/-!
# CRT cover events for the density-zero half of Erdős 697

This file conditions the independent prime-divisibility model on a fixed
small smooth factor.  Coprimality makes the extra coordinate independent,
so the resulting density is exactly `1/a` times the Bernoulli probability
of the large-prime event.
-/

open scoped BigOperators

namespace Erdos697.Cover

noncomputable section

open Erdos697

variable {I G : Type*} [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [CommGroup G]

/-- Large coordinates selected by divisibility. -/
def selected (q : I → ℕ) (n : ℕ) : Finset I :=
  Finset.univ.filter fun i => q i ∣ n

/-- A cover obtained by conditioning on one fixed factor and imposing an
arbitrary predicate on the remaining exact divisibility coordinates. -/
def eventSet (a : ℕ) (q : I → ℕ) (Good : Finset I → Prop) : Set ℕ :=
  {n | a ∣ n ∧ Good (selected q n)}

/-- The event used to cover an eligible divisor after its small part is
removed: either too many large primes divide `n`, or a nonempty selected
subproduct hits the required target set. -/
def set (a : ℕ) (q : I → ℕ) (f : I → G) (B : Finset G)
    (Kmax : ℕ) : Set ℕ :=
  {n | a ∣ n ∧
    (Kmax < (selected q n).card ∨
      WeightedSubset.hitsSet f B (selected q n))}

/-- All large-prime zero sets that are either above the cardinality cutoff
or hit the prescribed target. -/
noncomputable def goodSubsets (f : I → G) (B : Finset G) (Kmax : ℕ) :
    Finset (Finset I) := by
  classical
  exact Finset.univ.filter fun S =>
    Kmax < S.card ∨ WeightedSubset.hitsSet f B S

private theorem weight_insertNone
    (pa : ℝ) (p : I → ℝ) (S : Finset I) :
    Bernoulli.weight (Finset.univ : Finset (Option I))
        (fun o => o.elim pa p) S.insertNone =
      pa * Bernoulli.weight (Finset.univ : Finset I) p S := by
  classical
  unfold Bernoulli.weight
  rw [univ_option, Finset.prod_insertNone]
  have hdiff :
      (Finset.univ : Finset I).insertNone \ S.insertNone =
        ((Finset.univ : Finset I) \ S).map Function.Embedding.some := by
    ext (_ | i) <;> simp
  rw [hdiff, Finset.prod_map]
  simp only [Option.elim_none, Option.elim_some,
    Function.Embedding.some_apply]
  ring

private theorem sum_option_good_eq
    (pa : ℝ) (p : I → ℝ) (Good : Finset I → Prop)
    [DecidablePred Good] :
    (∑ T ∈ (Finset.univ : Finset (Finset (Option I))).filter
        (fun T => none ∈ T ∧ Good T.eraseNone),
      Bernoulli.weight Finset.univ (fun o => o.elim pa p) T) =
      pa * ∑ S ∈ (Finset.univ : Finset (Finset I)).filter Good,
        Bernoulli.weight Finset.univ p S := by
  classical
  have hreindex :
      (∑ T ∈ (Finset.univ : Finset (Finset (Option I))).filter
          (fun T => none ∈ T ∧ Good T.eraseNone),
        Bernoulli.weight Finset.univ (fun o => o.elim pa p) T) =
        ∑ S ∈ (Finset.univ : Finset (Finset I)).filter Good,
          Bernoulli.weight Finset.univ (fun o => o.elim pa p) S.insertNone := by
    apply Finset.sum_bij
      (fun T (_ : T ∈ (Finset.univ : Finset (Finset (Option I))).filter
        (fun T => none ∈ T ∧ Good T.eraseNone)) => T.eraseNone)
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      exact hT.2
    · intro T₁ hT₁ T₂ hT₂ hEq
      have hnone₁ : none ∈ T₁ := by
        exact (Finset.mem_filter.mp hT₁).2.1
      have hnone₂ : none ∈ T₂ := by
        exact (Finset.mem_filter.mp hT₂).2.1
      calc
        T₁ = T₁.eraseNone.insertNone := by
          rw [Finset.insertNone_eraseNone, Finset.insert_eq_self.mpr hnone₁]
        _ = T₂.eraseNone.insertNone := by rw [hEq]
        _ = T₂ := by
          rw [Finset.insertNone_eraseNone, Finset.insert_eq_self.mpr hnone₂]
    · intro S hS
      refine ⟨S.insertNone, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      exact ⟨Finset.none_mem_insertNone, by simpa using hS⟩
    · intro T hT
      have hnone : none ∈ T := by
        exact (Finset.mem_filter.mp hT).2.1
      have hTform : T = T.eraseNone.insertNone := by
        rw [Finset.insertNone_eraseNone, Finset.insert_eq_self.mpr hnone]
      rw [← hTform]
  rw [hreindex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  exact weight_insertNone pa p S

/-- Exact CRT density after conditioning on a fixed coprime factor, for an
arbitrary event on the remaining prime-divisibility coordinates. -/
theorem eventSet_hasDensity
    [LinearOrder I]
    (a : ℕ) (ha : 0 < a)
    (q : I → ℕ) (hq : ∀ i, 0 < q i)
    (hpair : Pairwise (Function.onFun Nat.Coprime q))
    (hacop : ∀ i, Nat.Coprime a (q i))
    (Good : Finset I → Prop) [DecidablePred Good] :
    (eventSet a q Good).HasDensity
      ((1 : ℝ) / a *
        ∑ S ∈ (Finset.univ : Finset (Finset I)).filter Good,
          Bernoulli.weight Finset.univ (fun i => 1 / (q i : ℝ)) S) := by
  classical
  let q' : Option I → ℕ := fun o => o.elim a q
  let Good' : Finset (Option I) → Prop := fun T =>
    none ∈ T ∧ Good T.eraseNone
  letI (o : Option I) : NeZero (q' o) := ⟨by
    cases o with
    | none => simpa [q'] using ha.ne'
    | some i => simpa [q'] using (hq i).ne'⟩
  have hpair' : Pairwise (Function.onFun Nat.Coprime q') := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => exact (hxy rfl).elim
        | some j =>
            change Nat.Coprime (q' none) (q' (some j))
            simpa [q'] using hacop j
    | some i =>
        cases y with
        | none =>
            change Nat.Coprime (q' (some i)) (q' none)
            simpa [q', Nat.coprime_comm] using hacop i
        | some j =>
            exact hpair (by intro h; apply hxy; simpa using h)
  let Q : ℕ := ∏ o, q' o
  letI : NeZero Q := ⟨by
    dsimp [Q]
    exact Finset.prod_ne_zero_iff.mpr fun o _ => NeZero.ne (q' o)⟩
  have hnone (n : ℕ) :
      none ∈ CRTModel.zeroSet q'
          (ZMod.prodEquivPi q' hpair' (n : ZMod Q)) ↔ a ∣ n := by
    rw [CRTModel.mem_zeroSet, ZMod.prodEquivPi_apply]
    rw [ZMod.castHom_apply,
      ZMod.cast_natCast
        (Finset.dvd_prod_of_mem q' (Finset.mem_univ none)) n]
    change (n : ZMod (q' none)) = 0 ↔ a ∣ n
    rw [ZMod.natCast_eq_zero_iff]
    rfl
  have herase (n : ℕ) :
      (CRTModel.zeroSet q'
          (ZMod.prodEquivPi q' hpair' (n : ZMod Q))).eraseNone =
        selected q n := by
    ext i
    rw [Finset.mem_eraseNone, CRTModel.mem_zeroSet,
      ZMod.prodEquivPi_apply]
    rw [ZMod.castHom_apply,
      ZMod.cast_natCast
        (Finset.dvd_prod_of_mem q' (Finset.mem_univ (some i))) n]
    simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
    change (n : ZMod (q' (some i))) = 0 ↔ q i ∣ n
    rw [ZMod.natCast_eq_zero_iff]
    rfl
  have hpFun : (fun o : Option I => 1 / (q' o : ℝ)) =
      (fun o => o.elim ((1 : ℝ) / a) (fun i => 1 / (q i : ℝ))) := by
    funext o
    cases o <;> rfl
  have hcrt := CRTModel.crt_zeroSet_good_hasDensity q' hpair' Good'
  convert hcrt using 1
  · ext n
    simp only [eventSet, Set.mem_setOf_eq, Good']
    rw [herase, hnone]
  · rw [hpFun]
    simpa [Good'] using
      (sum_option_good_eq (I := I) ((1 : ℝ) / a)
        (fun i => 1 / (q i : ℝ)) Good).symm

/-- Exact density of a fixed-small-factor cover event. -/
theorem set_hasDensity
    [LinearOrder I]
    (a : ℕ) (ha : 0 < a)
    (q : I → ℕ) (hq : ∀ i, 0 < q i)
    (hpair : Pairwise (Function.onFun Nat.Coprime q))
    (hacop : ∀ i, Nat.Coprime a (q i))
    (f : I → G) (B : Finset G) (Kmax : ℕ) :
    (set a q f B Kmax).HasDensity
      ((1 : ℝ) / a *
        ∑ S ∈ goodSubsets f B Kmax,
          Bernoulli.weight Finset.univ (fun i => 1 / (q i : ℝ)) S) := by
  classical
  let q' : Option I → ℕ := fun o => o.elim a q
  let Good : Finset (Option I) → Prop := fun T =>
    none ∈ T ∧
      (Kmax < T.eraseNone.card ∨
        WeightedSubset.hitsSet f B T.eraseNone)
  letI (o : Option I) : NeZero (q' o) := ⟨by
    cases o with
    | none => simpa [q'] using ha.ne'
    | some i => simpa [q'] using (hq i).ne'⟩
  have hpair' : Pairwise (Function.onFun Nat.Coprime q') := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => exact (hxy rfl).elim
        | some j =>
            change Nat.Coprime (q' none) (q' (some j))
            simpa [q'] using hacop j
    | some i =>
        cases y with
        | none =>
            change Nat.Coprime (q' (some i)) (q' none)
            simpa [q', Nat.coprime_comm] using hacop i
        | some j =>
            exact hpair (by intro h; apply hxy; simpa using h)
  let Q : ℕ := ∏ o, q' o
  letI : NeZero Q := ⟨by
    dsimp [Q]
    exact Finset.prod_ne_zero_iff.mpr fun o _ => NeZero.ne (q' o)⟩
  have hnone (n : ℕ) :
      none ∈ CRTModel.zeroSet q'
          (ZMod.prodEquivPi q' hpair' (n : ZMod Q)) ↔ a ∣ n := by
    rw [CRTModel.mem_zeroSet, ZMod.prodEquivPi_apply]
    rw [ZMod.castHom_apply,
      ZMod.cast_natCast
        (Finset.dvd_prod_of_mem q' (Finset.mem_univ none)) n]
    change (n : ZMod (q' none)) = 0 ↔ a ∣ n
    rw [ZMod.natCast_eq_zero_iff]
    rfl
  have herase (n : ℕ) :
      (CRTModel.zeroSet q'
          (ZMod.prodEquivPi q' hpair' (n : ZMod Q))).eraseNone =
        selected q n := by
    ext i
    rw [Finset.mem_eraseNone, CRTModel.mem_zeroSet,
      ZMod.prodEquivPi_apply]
    rw [ZMod.castHom_apply,
      ZMod.cast_natCast
        (Finset.dvd_prod_of_mem q' (Finset.mem_univ (some i))) n]
    simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
    change (n : ZMod (q' (some i))) = 0 ↔ q i ∣ n
    rw [ZMod.natCast_eq_zero_iff]
    rfl
  have hpFun : (fun o : Option I => 1 / (q' o : ℝ)) =
      (fun o => o.elim ((1 : ℝ) / a) (fun i => 1 / (q i : ℝ))) := by
    funext o
    cases o <;> rfl
  have hcrt := CRTModel.crt_zeroSet_good_hasDensity q' hpair' Good
  convert hcrt using 1
  · ext n
    simp only [set, Set.mem_setOf_eq, Good]
    rw [herase, hnone]
  · rw [hpFun]
    simpa [Good, goodSubsets] using
      (sum_option_good_eq (I := I) ((1 : ℝ) / a)
        (fun i => 1 / (q i : ℝ))
        (fun S => Kmax < S.card ∨ WeightedSubset.hitsSet f B S)).symm

end

end Erdos697.Cover
