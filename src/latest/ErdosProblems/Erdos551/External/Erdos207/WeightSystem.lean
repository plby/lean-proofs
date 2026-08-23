/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.FiniteProbability
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators

/-!
# Weight systems and moment expansion

This is the finite-sum core of KSSS Lemma 3.7.  It separates the exact
probability expansion from the later combinatorial estimate of the tuple
weight by the maximum extension weight.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Product weight of a finite subset of the ground set. -/
def setWeight {W : Type*} [DecidableEq W] (π : W → ℝ≥0) (S : Finset W) : ℝ≥0 :=
  ∏ x ∈ S, π x

/-- KSSS extension weight above a prescribed root `H`. -/
def extensionWeight {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (π : W → ℝ≥0) (H : Finset W) : ℝ≥0 :=
  ∑ i, if H ⊆ F i then setWeight π (F i \ H) else 0

/-- A common upper bound for every rooted extension weight. -/
def HasExtensionBound {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (π : W → ℝ≥0) (κ : ℝ≥0) : Prop :=
  ∀ H, extensionWeight F π H ≤ κ

/-- Weight of the configurations whose intersection with `U` is exactly
`H`. -/
def intersectionClassWeight {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (π : W → ℝ≥0) (U H : Finset W) : ℝ≥0 :=
  ∑ i, if F i ∩ U = H then setWeight π (F i \ H) else 0

lemma intersectionClassWeight_le_extensionWeight
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (π : W → ℝ≥0) (U H : Finset W) :
    intersectionClassWeight F π U H ≤ extensionWeight F π H := by
  classical
  unfold intersectionClassWeight extensionWeight
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : F i ∩ U = H
  · have hsub : H ⊆ F i := by
      rw [← hi]
      exact inter_subset_left
    simp [hi, hsub]
  · simp [hi]

/-- After a previously exposed union `U` is fixed, the total weight of all
possible next configurations is controlled by one extension bound for each
subset of `U`. -/
lemma sum_weight_sdiff_le_powerset_mul
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (π : W → ℝ≥0) (U : Finset W) {κ : ℝ≥0}
    (hκ : HasExtensionBound F π κ) :
    ∑ i, setWeight π (F i \ U) ≤ (2 : ℝ≥0) ^ U.card * κ := by
  classical
  have hpartition :
      (∑ i, setWeight π (F i \ U)) =
        ∑ H ∈ U.powerset, intersectionClassWeight F π U H := by
    calc
      (∑ i, setWeight π (F i \ U)) =
          ∑ i, ∑ H ∈ U.powerset,
            if F i ∩ U = H then setWeight π (F i \ H) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        have hmem : F i ∩ U ∈ U.powerset := mem_powerset.mpr inter_subset_right
        rw [Finset.sum_eq_single (F i ∩ U)]
        · simp only
          congr 1
          ext x
          simp
        · exact fun H hHU hne ↦ by simp [hne.symm]
        · exact fun hnot ↦ (hnot hmem).elim
      _ = ∑ H ∈ U.powerset, intersectionClassWeight F π U H := by
        unfold intersectionClassWeight
        rw [Finset.sum_comm]
  rw [hpartition]
  calc
    ∑ H ∈ U.powerset, intersectionClassWeight F π U H ≤
        ∑ _H ∈ U.powerset, κ := by
      apply Finset.sum_le_sum
      intro H _
      exact (intersectionClassWeight_le_extensionWeight F π U H).trans (hκ H)
    _ = (2 : ℝ≥0) ^ U.card * κ := by
      simp

lemma setWeight_union_eq_mul_sdiff
    {W : Type*} [DecidableEq W] (π : W → ℝ≥0) (U S : Finset W) :
    setWeight π (U ∪ S) = setWeight π U * setWeight π (S \ U) := by
  unfold setWeight
  rw [← union_sdiff_self_eq_union, Finset.prod_union disjoint_sdiff]

/-- One step of the tuple-weight recursion, with the deliberately coarse
`2 ^ |U|` count of possible intersections.  Since `d` and the moment order
are fixed in KSSS, this is as sufficient asymptotically as their sharper
`(dt)^d` count. -/
lemma sum_weight_union_le
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (π : W → ℝ≥0) (U : Finset W) {κ : ℝ≥0}
    (hκ : HasExtensionBound F π κ) :
    ∑ i, setWeight π (U ∪ F i) ≤
      setWeight π U * ((2 : ℝ≥0) ^ U.card * κ) := by
  calc
    ∑ i, setWeight π (U ∪ F i) =
        setWeight π U * ∑ i, setWeight π (F i \ U) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact setWeight_union_eq_mul_sdiff π U (F i)
    _ ≤ setWeight π U * ((2 : ℝ≥0) ^ U.card * κ) :=
      by
        simpa [mul_comm] using
          mul_le_mul_left (sum_weight_sdiff_le_powerset_mul F π U hκ) (setWeight π U)

/-- Union of the configurations in an ordered tuple. -/
def tupleUnion {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) {s : ℕ} (f : Fin s → I) : Finset W :=
  Finset.univ.biUnion fun t ↦ F (f t)

@[simp]
lemma tupleUnion_zero {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (f : Fin 0 → I) : tupleUnion F f = ∅ := by
  simp [tupleUnion]

lemma tupleUnion_cons {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) {s : ℕ} (i : I) (f : Fin s → I) :
    tupleUnion F (Fin.cons i f) = F i ∪ tupleUnion F f := by
  ext x
  simp [tupleUnion, Fin.exists_fin_succ]

/-- Split a sum over `(s+1)`-tuples into the first entry and the tail. -/
lemma sum_fin_succ_tuple {I M : Type*} [Fintype I] [AddCommMonoid M]
    {s : ℕ} (f : (Fin (s + 1) → I) → M) :
    ∑ x : Fin (s + 1) → I, f x = ∑ i : I, ∑ y : Fin s → I, f (Fin.cons i y) := by
  let e : I × (Fin s → I) ≃ (Fin (s + 1) → I) :=
    Fin.consEquiv (fun _ : Fin (s + 1) ↦ I)
  rw [← e.sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

/-- Nonnegative-real count of the configurations contained in `R`. -/
def selectedCount {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (R : Finset W) : ℝ≥0 :=
  ∑ i, if F i ⊆ R then 1 else 0

/-- A tuple of `s` configurations of size at most `d` has union size at most
`s*d`. -/
lemma card_tupleUnion_le {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) {d s : ℕ} (hcard : ∀ i, (F i).card ≤ d)
    (f : Fin s → I) : (tupleUnion F f).card ≤ s * d := by
  calc
    (tupleUnion F f).card ≤ ∑ t : Fin s, (F (f t)).card := card_biUnion_le
    _ ≤ ∑ _t : Fin s, d := Finset.sum_le_sum fun t _ ↦ hcard (f t)
    _ = s * d := by simp

/-- Coarse tuple-weight form of the combinatorial half of KSSS Lemma 3.7.
The sharper paper constant is unnecessary: for fixed `m,d`, this bound is
still an absolute constant times `κ^t`. -/
lemma sum_tupleWeight_le
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (π : W → ℝ≥0) {κ : ℝ≥0} {d m : ℕ}
    (hcard : ∀ i, (F i).card ≤ d) (hκ : HasExtensionBound F π κ) :
    ∀ t ≤ m, ∑ f : Fin t → I, setWeight π (tupleUnion F f) ≤
      ((2 : ℝ≥0) ^ (m * d) * κ) ^ t := by
  intro t htm
  induction t with
  | zero => simp [setWeight]
  | succ t ih =>
      have iht := ih (by omega)
      rw [sum_fin_succ_tuple, Finset.sum_comm]
      calc
        ∑ f : Fin t → I, ∑ i : I,
            setWeight π (tupleUnion F (Fin.cons i f)) ≤
            ∑ f : Fin t → I,
              setWeight π (tupleUnion F f) * ((2 : ℝ≥0) ^ (m * d) * κ) := by
          apply Finset.sum_le_sum
          intro f _
          simp only [tupleUnion_cons]
          have hstep := sum_weight_union_le F π (tupleUnion F f) hκ
          have hUcard := card_tupleUnion_le F hcard f
          have hUcard' : (tupleUnion F f).card ≤ m * d :=
            hUcard.trans (Nat.mul_le_mul_right d (by omega))
          calc
            ∑ i : I, setWeight π (F i ∪ tupleUnion F f) =
                ∑ i : I, setWeight π (tupleUnion F f ∪ F i) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [union_comm]
            _ ≤ setWeight π (tupleUnion F f) *
                ((2 : ℝ≥0) ^ (tupleUnion F f).card * κ) := hstep
            _ ≤ setWeight π (tupleUnion F f) *
                ((2 : ℝ≥0) ^ (m * d) * κ) := by
              gcongr
              norm_num
        _ = (∑ f : Fin t → I, setWeight π (tupleUnion F f)) *
              ((2 : ℝ≥0) ^ (m * d) * κ) := by
          rw [Finset.sum_mul]
        _ ≤ (((2 : ℝ≥0) ^ (m * d) * κ) ^ t) *
              ((2 : ℝ≥0) ^ (m * d) * κ) :=
          by
            simpa [mul_comm] using
              mul_le_mul_left iht ((2 : ℝ≥0) ^ (m * d) * κ)
        _ = ((2 : ℝ≥0) ^ (m * d) * κ) ^ (t + 1) := by
          rw [pow_succ]

/-- The `s`-th moment of a configuration count is the sum, over ordered
`s`-tuples, of their joint-inclusion probabilities. -/
lemma expectation_selectedCount_pow
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W) (s : ℕ) :
    L.expectation (fun ω ↦ (selectedCount F (R ω)) ^ s) =
      ∑ f : Fin s → I,
        L.probability (fun ω ↦ ∀ t, F (f t) ⊆ R ω) := by
  classical
  calc
    L.expectation (fun ω ↦ (selectedCount F (R ω)) ^ s) =
        ∑ ω, ∑ f : Fin s → I,
          L.mass ω * ∏ t, (if F (f t) ⊆ R ω then 1 else 0) := by
      unfold FiniteLaw.expectation selectedCount
      apply Finset.sum_congr rfl
      intro ω _
      change L.mass ω * (∑ i, if F i ⊆ R ω then 1 else 0) ^ s = _
      rw [Fintype.sum_pow, Finset.mul_sum]
    _ = ∑ f : Fin s → I, ∑ ω,
          L.mass ω * ∏ t, (if F (f t) ⊆ R ω then 1 else 0) := by
      exact Finset.sum_comm
    _ = ∑ f : Fin s → I,
        L.probability (fun ω ↦ ∀ t, F (f t) ⊆ R ω) := by
      apply Finset.sum_congr rfl
      intro f _
      unfold FiniteLaw.probability
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hall : ∀ t, F (f t) ⊆ R ω
      · simp [hall]
      · have hnotall : ¬ ∀ t, F (f t) ⊆ R ω := hall
        push Not at hall
        obtain ⟨t, ht⟩ := hall
        have hzero : ∏ t', (if F (f t') ⊆ R ω then (1 : ℝ≥0) else 0) = 0 := by
          apply Finset.prod_eq_zero (mem_univ t)
          simp [ht]
        simp [hnotall, hzero]

/-- Joint inclusion is equivalently inclusion of the tuple union. -/
lemma tuple_joint_iff_union_subset
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) {s : ℕ} (f : Fin s → I) (R : Finset W) :
    (∀ t, F (f t) ⊆ R) ↔ tupleUnion F f ⊆ R := by
  simp [tupleUnion]

/-- Applying a joint-inclusion hypothesis term by term after the exact
moment expansion. -/
lemma expectation_selectedCount_pow_le
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W)
    (π : W → ℝ≥0) (C : ℝ≥0) {d s : ℕ}
    (hcard : ∀ i, (F i).card ≤ d)
    (hjoint : ∀ T : Finset W, T.card ≤ s * d →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.expectation (fun ω ↦ (selectedCount F (R ω)) ^ s) ≤
      C * ∑ f : Fin s → I, setWeight π (tupleUnion F f) := by
  rw [expectation_selectedCount_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  have hevents : (fun ω ↦ ∀ t, F (f t) ⊆ R ω) =
      (fun ω ↦ tupleUnion F f ⊆ R ω) := by
    funext ω
    exact propext (tuple_joint_iff_union_subset F f (R ω))
  rw [hevents]
  exact hjoint (tupleUnion F f) (card_tupleUnion_le F hcard f)

/-- The first moment only uses the empty-root extension weight.  In
particular, unlike the higher-moment bound below, it does not require a
uniform extension estimate above every previously planted root. -/
theorem expectation_selectedCount_le_of_empty_extensionWeight
    {Omega W I : Type*} [Fintype Omega] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Omega) (F : I → Finset W) (R : Omega → Finset W)
    (pi : W → ℝ≥0) (C kappa : ℝ≥0) {d : ℕ}
    (hcard : ∀ i, (F i).card ≤ d)
    (hempty : extensionWeight F pi (∅ : Finset W) ≤ kappa)
    (hjoint : ∀ T : Finset W, T.card ≤ d →
      L.probability (fun omega ↦ T ⊆ R omega) ≤ C * setWeight pi T) :
    L.expectation (fun omega ↦ selectedCount F (R omega)) ≤ C * kappa := by
  calc
    L.expectation (fun omega ↦ selectedCount F (R omega)) =
        L.expectation (fun omega ↦ (selectedCount F (R omega)) ^ 1) := by simp
    _ ≤ C * ∑ f : Fin 1 → I, setWeight pi (tupleUnion F f) := by
      exact expectation_selectedCount_pow_le L F R pi C hcard (by
        intro T hT
        exact hjoint T (by simpa using hT))
    _ = C * extensionWeight F pi (∅ : Finset W) := by
      congr 1
      unfold extensionWeight
      simp only [if_pos (empty_subset _), sdiff_empty]
      apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) I)
      intro f
      simp [tupleUnion, Equiv.funUnique]
    _ ≤ C * kappa := by gcongr

/-- Complete finite moment estimate.  It has the same fixed-parameter
strength as KSSS Lemma 3.7; only the harmless constant is coarser. -/
theorem configurationMomentBound
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W)
    (π : W → ℝ≥0) (C κ : ℝ≥0) {d s : ℕ}
    (hcard : ∀ i, (F i).card ≤ d) (hκ : HasExtensionBound F π κ)
    (hjoint : ∀ T : Finset W, T.card ≤ s * d →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.expectation (fun ω ↦ (selectedCount F (R ω)) ^ s) ≤
      C * (((2 : ℝ≥0) ^ (s * d) * κ) ^ s) := by
  calc
    L.expectation (fun ω ↦ (selectedCount F (R ω)) ^ s) ≤
        C * ∑ f : Fin s → I, setWeight π (tupleUnion F f) :=
      expectation_selectedCount_pow_le L F R π C hcard hjoint
    _ ≤ C * (((2 : ℝ≥0) ^ (s * d) * κ) ^ s) := by
      gcongr
      exact sum_tupleWeight_le F π hcard hκ s le_rfl

/-- Specialization of the moment bound to an independently selected finite
subset.  Here the joint-inclusion hypothesis is an exact identity supplied by
`independentBits_probability_subset_selected`. -/
theorem independentBits_configurationMomentBound
    {W J : Type*} [Fintype W] [DecidableEq W] [Fintype J]
    (F : J → Finset W) (p : W → ℝ≥0) (hp : ∀ x, p x ≤ 1)
    (κ : ℝ≥0) {d s : ℕ}
    (hcard : ∀ j, (F j).card ≤ d) (hκ : HasExtensionBound F p κ) :
    (FiniteLaw.independentBits p hp).expectation
        (fun ω ↦ (selectedCount F (FiniteLaw.selectedByBits ω)) ^ s) ≤
      (((2 : ℝ≥0) ^ (s * d) * κ) ^ s) := by
  simpa using configurationMomentBound
    (FiniteLaw.independentBits p hp) F FiniteLaw.selectedByBits p 1 κ hcard hκ
    (fun T _ ↦ by
      rw [FiniteLaw.independentBits_probability_subset_selected]
      simp [setWeight])

end

end Erdos207
