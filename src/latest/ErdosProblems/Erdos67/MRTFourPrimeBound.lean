import ErdosProblems.Erdos67.PrimeFourier
import ErdosProblems.Erdos67.MRTSieveAdapter
import ErdosProblems.Erdos851.ConcreteBetaCardinality
import ErdosProblems.Erdos851.EulerMass
import ErdosProblems.Erdos851.SingularProductExpansion
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# The four-prime upper-bound-sieve estimate

This file develops the representation-count input in (3.3) of
Matomäki--Radziwiłł--Tao.  The first part is entirely finite: additive
quadruples are regrouped by their (unsigned) prime differences, and prime
pairs are embedded in the two-shift sieve from `Erdos851`.
-/

open Filter
open scoped BigOperators Topology Pointwise

namespace Erdos67

noncomputable section

/-! ## Difference fibres -/

/-- Ordered pairs from `A` whose second entry is the first plus `h`. -/
def forwardDifferencePairs (A : Finset ℕ) (h : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun x ↦ x.2 = x.1 + h

@[simp] theorem mem_forwardDifferencePairs {A : Finset ℕ} {h : ℕ}
    {x : ℕ × ℕ} :
    x ∈ forwardDifferencePairs A h ↔
      x.1 ∈ A ∧ x.2 ∈ A ∧ x.2 = x.1 + h := by
  simp [forwardDifferencePairs, and_assoc]

theorem card_forwardDifferencePairs_le_card (A : Finset ℕ) (h : ℕ) :
    (forwardDifferencePairs A h).card ≤ A.card := by
  let f : ℕ × ℕ → ℕ := fun x ↦ x.1
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    exact (mem_forwardDifferencePairs.mp hx).1
  · intro x hx z hz heq
    have hxdiff := (mem_forwardDifferencePairs.mp hx).2.2
    have hzdiff := (mem_forwardDifferencePairs.mp hz).2.2
    apply Prod.ext
    · exact heq
    · dsimp [f] at heq
      omega

theorem card_primesLE_le_succ (N : ℕ) : (Nat.primesLE N).card ≤ N + 1 := by
  calc
    (Nat.primesLE N).card ≤ (Finset.range (N + 1)).card := by
      apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.mem_primesLE.mp hp).1
    _ = N + 1 := by simp

/-- The signed difference of a pair, represented as an integer. -/
def pairDifference (x : ℕ × ℕ) : ℤ := (x.2 : ℤ) - x.1

/-- Fibres of the signed difference map. -/
def signedDifferencePairs (A : Finset ℕ) (d : ℤ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun x ↦ pairDifference x = d

@[simp] theorem mem_signedDifferencePairs {A : Finset ℕ} {d : ℤ}
    {x : ℕ × ℕ} :
    x ∈ signedDifferencePairs A d ↔
      x.1 ∈ A ∧ x.2 ∈ A ∧ pairDifference x = d := by
  simp [signedDifferencePairs, and_assoc]

theorem signedDifferencePairs_ofNat (A : Finset ℕ) (h : ℕ) :
    signedDifferencePairs A h = forwardDifferencePairs A h := by
  ext x
  simp only [mem_signedDifferencePairs, mem_forwardDifferencePairs, and_congr_right_iff]
  intro _ _
  simp only [pairDifference, Int.ofNat_eq_coe]
  omega

/-- Negating a signed difference just reverses every pair. -/
theorem card_signedDifferencePairs_neg (A : Finset ℕ) (d : ℤ) :
    (signedDifferencePairs A (-d)).card = (signedDifferencePairs A d).card := by
  let e : ℕ × ℕ ≃ ℕ × ℕ := Equiv.prodComm ℕ ℕ
  apply Finset.card_bij (fun x _ ↦ e x)
  · intro x hx
    rw [mem_signedDifferencePairs] at hx ⊢
    exact ⟨hx.2.1, hx.1, by
      dsimp [e, pairDifference] at hx ⊢
      omega⟩
  · intro x hx y hy hxy
    exact e.injective hxy
  · intro y hy
    refine ⟨e.symm y, ?_, ?_⟩
    · rw [mem_signedDifferencePairs] at hy ⊢
      exact ⟨hy.2.1, hy.1, by
        dsimp [e, pairDifference] at hy ⊢
        omega⟩
    · simp [e]

/-- The part of the additive-quadruple set whose first pair has signed
difference `d`. -/
def additiveQuadrupleDifferenceFiber (A : Finset ℕ) (d : ℤ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (additiveQuadruples A).filter fun x ↦ pairDifference x.1 = d

theorem additiveQuadrupleDifferenceFiber_eq (A : Finset ℕ) (d : ℤ) :
    additiveQuadrupleDifferenceFiber A d =
      signedDifferencePairs A d ×ˢ signedDifferencePairs A (-d) := by
  ext x
  simp only [additiveQuadrupleDifferenceFiber, Finset.mem_filter,
    mem_additiveQuadruples, Finset.mem_product, mem_signedDifferencePairs]
  constructor
  · rintro ⟨⟨ha₁, ha₂, hb₁, hb₂, hab⟩, hd⟩
    refine ⟨⟨ha₁, ha₂, hd⟩, hb₁, hb₂, ?_⟩
    dsimp [pairDifference] at hd ⊢
    omega
  · rintro ⟨⟨ha₁, ha₂, hd⟩, hb₁, hb₂, hneg⟩
    refine ⟨⟨ha₁, ha₂, hb₁, hb₂, ?_⟩, hd⟩
    dsimp [pairDifference] at hd hneg
    omega

theorem card_additiveQuadrupleDifferenceFiber (A : Finset ℕ) (d : ℤ) :
    (additiveQuadrupleDifferenceFiber A d).card =
      (signedDifferencePairs A d).card ^ 2 := by
  rw [additiveQuadrupleDifferenceFiber_eq, Finset.card_product,
    card_signedDifferencePairs_neg]
  ring

private def negativeSuccessorEmbedding : ℕ ↪ ℤ where
  toFun t := -(((t + 1 : ℕ) : ℤ))
  inj' := by
    intro a b h
    simp at h
    omega

@[simp] private theorem negativeSuccessorEmbedding_apply (t : ℕ) :
    negativeSuccessorEmbedding t = -(((t + 1 : ℕ) : ℤ)) := rfl

private theorem int_Icc_symmetric_eq_maps (N : ℕ) :
    Finset.Icc (-(N : ℤ)) (N : ℤ) =
      (Finset.range N).map negativeSuccessorEmbedding ∪
        (Finset.range (N + 1)).map Nat.castEmbedding := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_Icc] at hz
    rw [Finset.mem_union]
    by_cases hzneg : z < 0
    · left
      refine Finset.mem_map.mpr ⟨((-z - 1).toNat), ?_, ?_⟩
      · simp
        have hcast : ((-z).toNat : ℤ) = -z := by
          rw [Int.toNat_of_nonneg]
          omega
        omega
      · simp [negativeSuccessorEmbedding]
        have hcast : ((-z).toNat : ℤ) = -z := by
          rw [Int.toNat_of_nonneg]
          omega
        omega
    · right
      refine Finset.mem_map.mpr ⟨z.toNat, ?_, ?_⟩
      · simp
        omega
      · simp
        omega
  · intro hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · rcases Finset.mem_map.mp hz with ⟨t, ht, rfl⟩
      change -(((t + 1 : ℕ) : ℤ)) ∈
        Finset.Icc (-(N : ℤ)) (N : ℤ)
      rw [Finset.mem_Icc]
      have htN := Finset.mem_range.mp ht
      constructor <;> omega
    · rcases Finset.mem_map.mp hz with ⟨t, ht, rfl⟩
      change (t : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
      rw [Finset.mem_Icc]
      have htN := Finset.mem_range.mp ht
      constructor <;> omega

/-- Regrouping additive quadruples by signed difference, followed by the
symmetry `d ↔ -d`. -/
theorem additiveQuadruples_card_le_two_mul_difference_square_sum
    (A : Finset ℕ) (N : ℕ) (hA : ∀ a ∈ A, a ≤ N) :
    (additiveQuadruples A).card ≤
      2 * ∑ h ∈ Finset.range (N + 1),
        (forwardDifferencePairs A h).card ^ 2 := by
  classical
  let D : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hdiff : ∀ x ∈ additiveQuadruples A, pairDifference x.1 ∈ D := by
    intro x hx
    have hx' := mem_additiveQuadruples.mp hx
    have hx₁ := hA x.1.1 hx'.1
    have hx₂ := hA x.1.2 hx'.2.1
    rw [Finset.mem_Icc]
    dsimp [D, pairDifference]
    omega
  have hpartition :
      (additiveQuadruples A).card =
        ∑ d ∈ D, (signedDifferencePairs A d).card ^ 2 := by
    calc
      (additiveQuadruples A).card =
          ∑ d ∈ D, (additiveQuadrupleDifferenceFiber A d).card := by
        symm
        calc
          ∑ d ∈ D, (additiveQuadrupleDifferenceFiber A d).card =
              ((additiveQuadruples A).filter
                fun x ↦ pairDifference x.1 ∈ D).card := by
            simpa only [additiveQuadrupleDifferenceFiber] using
              (Finset.sum_card_fiberwise_eq_card_filter
                (additiveQuadruples A) D (fun x ↦ pairDifference x.1))
          _ = (additiveQuadruples A).card := by
            rw [Finset.filter_eq_self.2 hdiff]
      _ = ∑ d ∈ D, (signedDifferencePairs A d).card ^ 2 := by
        apply Finset.sum_congr rfl
        intro d hd
        exact card_additiveQuadrupleDifferenceFiber A d
  rw [hpartition]
  rw [show D =
      (Finset.range N).map negativeSuccessorEmbedding ∪
        (Finset.range (N + 1)).map Nat.castEmbedding by
    exact int_Icc_symmetric_eq_maps N]
  have hdisjoint :
      Disjoint ((Finset.range N).map negativeSuccessorEmbedding)
        ((Finset.range (N + 1)).map Nat.castEmbedding) := by
    rw [Finset.disjoint_left]
    intro z hzneg hzpos
    rcases Finset.mem_map.mp hzneg with ⟨t, ht, rfl⟩
    rcases Finset.mem_map.mp hzpos with ⟨u, hu, huz⟩
    simp only [negativeSuccessorEmbedding_apply, Nat.castEmbedding_apply] at huz
    omega
  rw [Finset.sum_union hdisjoint, Finset.sum_map, Finset.sum_map]
  simp_rw [negativeSuccessorEmbedding_apply, Nat.castEmbedding_apply,
    card_signedDifferencePairs_neg, signedDifferencePairs_ofNat]
  have hsub :
      ∑ t ∈ Finset.range N,
          (forwardDifferencePairs A (t + 1)).card ^ 2 ≤
        ∑ h ∈ Finset.range (N + 1),
          (forwardDifferencePairs A h).card ^ 2 := by
    have hreindex :
        ∑ t ∈ Finset.range N,
            (forwardDifferencePairs A (t + 1)).card ^ 2 =
          ∑ h ∈ Finset.Ioc 0 N,
            (forwardDifferencePairs A h).card ^ 2 := by
      apply Finset.sum_bij (fun t _ ↦ t + 1)
      · intro t ht
        rw [Finset.mem_Ioc]
        have ht' := Finset.mem_range.mp ht
        omega
      · intro a ha b hb hab
        omega
      · intro h hh
        rw [Finset.mem_Ioc] at hh
        refine ⟨h - 1, by simp; omega, by omega⟩
      · intro t ht
        rfl
    rw [hreindex]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro h hh
      rw [Finset.mem_Ioc] at hh
      rw [Finset.mem_range]
      omega
    · intros
      exact Nat.zero_le _
  omega

/-! ## A fixed signed four-prime difference is bounded by energy -/

/-- The signed combination which occurs in the fourth-moment expansion. -/
def fourPrimeDifference (x : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  (x.1.2 : ℤ) + x.2.2 - x.1.1 - x.2.1

/-- Four elements of `A` with prescribed signed difference of the two
crossed pair sums.  Its coordinate order agrees with the MRT fourth-moment
expansion. -/
def fourPrimeDifferenceFiber (A : Finset ℕ) (d : ℤ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter fun x ↦ fourPrimeDifference x = d

@[simp] theorem mem_fourPrimeDifferenceFiber {A : Finset ℕ} {d : ℤ}
    {x : (ℕ × ℕ) × (ℕ × ℕ)} :
    x ∈ fourPrimeDifferenceFiber A d ↔
      x.1.1 ∈ A ∧ x.1.2 ∈ A ∧ x.2.1 ∈ A ∧ x.2.2 ∈ A ∧
        fourPrimeDifference x = d := by
  simp only [fourPrimeDifferenceFiber, Finset.mem_filter, Finset.mem_product]
  aesop

/-- Ordered pairs from `A` with a prescribed (ordinary) sum. -/
def pairSumFiber (A : Finset ℕ) (s : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun x ↦ x.1 + x.2 = s

@[simp] theorem mem_pairSumFiber {A : Finset ℕ} {s : ℕ} {x : ℕ × ℕ} :
    x ∈ pairSumFiber A s ↔ x.1 ∈ A ∧ x.2 ∈ A ∧ x.1 + x.2 = s := by
  simp [pairSumFiber, and_assoc]

/-- The right-pair fiber whose sum differs from `s` by `d`. -/
def shiftedPairSumFiber (A : Finset ℕ) (d : ℤ) (s : ℕ) :
    Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun x ↦ (x.1 + x.2 : ℕ) = (s : ℤ) + d

@[simp] theorem mem_shiftedPairSumFiber {A : Finset ℕ} {d : ℤ} {s : ℕ}
    {x : ℕ × ℕ} :
    x ∈ shiftedPairSumFiber A d s ↔
      x.1 ∈ A ∧ x.2 ∈ A ∧ (x.1 + x.2 : ℕ) = (s : ℤ) + d := by
  simp [shiftedPairSumFiber, and_assoc]

/-- Refine a signed four-prime fiber by its left crossed-pair sum. -/
def fourPrimeLeftSumFiber (A : Finset ℕ) (d : ℤ) (s : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (fourPrimeDifferenceFiber A d).filter fun x ↦ x.1.1 + x.2.1 = s

theorem card_fourPrimeLeftSumFiber (A : Finset ℕ) (d : ℤ) (s : ℕ) :
    (fourPrimeLeftSumFiber A d s).card =
      (pairSumFiber A s).card * (shiftedPairSumFiber A d s).card := by
  let f : ((ℕ × ℕ) × (ℕ × ℕ)) → ((ℕ × ℕ) × (ℕ × ℕ)) :=
    fun x ↦ ((x.1.1, x.2.1), (x.1.2, x.2.2))
  rw [← Finset.card_product]
  apply Finset.card_bij (fun x _ ↦ f x)
  · intro x hx
    simp only [fourPrimeLeftSumFiber, Finset.mem_filter] at hx
    rw [Finset.mem_product, mem_pairSumFiber, mem_shiftedPairSumFiber]
    have hx' := mem_fourPrimeDifferenceFiber.mp hx.1
    refine ⟨⟨hx'.1, hx'.2.2.1, hx.2⟩,
      hx'.2.1, hx'.2.2.2.1, ?_⟩
    dsimp [f, fourPrimeDifference] at hx' ⊢
    omega
  · intro x hx y hy hxy
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z ↦ z.1.1) hxy
      · exact congrArg (fun z ↦ z.2.1) hxy
    · apply Prod.ext
      · exact congrArg (fun z ↦ z.1.2) hxy
      · exact congrArg (fun z ↦ z.2.2) hxy
  · intro y hy
    rw [Finset.mem_product, mem_pairSumFiber, mem_shiftedPairSumFiber] at hy
    let x : (ℕ × ℕ) × (ℕ × ℕ) :=
      ((y.1.1, y.2.1), (y.1.2, y.2.2))
    refine ⟨x, ?_, ?_⟩
    · simp only [fourPrimeLeftSumFiber, Finset.mem_filter]
      refine ⟨mem_fourPrimeDifferenceFiber.mpr
        ⟨hy.1.1, hy.2.1, hy.1.2.1, hy.2.2.1, ?_⟩, hy.1.2.2⟩
      dsimp [x, fourPrimeDifference]
      dsimp at hy
      omega
    · rfl

theorem card_fourPrimeDifferenceFiber_eq_sum (A : Finset ℕ) (d : ℤ) :
    (fourPrimeDifferenceFiber A d).card =
      ∑ s ∈ A + A,
        (pairSumFiber A s).card * (shiftedPairSumFiber A d s).card := by
  have hsum : ∀ x ∈ fourPrimeDifferenceFiber A d, x.1.1 + x.2.1 ∈ A + A := by
    intro x hx
    have hx' := mem_fourPrimeDifferenceFiber.mp hx
    exact Finset.mem_add.mpr ⟨x.1.1, hx'.1, x.2.1, hx'.2.2.1, rfl⟩
  calc
    (fourPrimeDifferenceFiber A d).card =
        ∑ s ∈ A + A, (fourPrimeLeftSumFiber A d s).card := by
      symm
      calc
        ∑ s ∈ A + A, (fourPrimeLeftSumFiber A d s).card =
            ((fourPrimeDifferenceFiber A d).filter
              fun x ↦ x.1.1 + x.2.1 ∈ A + A).card := by
          simpa only [fourPrimeLeftSumFiber] using
            (Finset.sum_card_fiberwise_eq_card_filter
              (fourPrimeDifferenceFiber A d) (A + A)
              (fun x ↦ x.1.1 + x.2.1))
        _ = (fourPrimeDifferenceFiber A d).card := by
          rw [Finset.filter_eq_self.2 hsum]
    _ = ∑ s ∈ A + A,
        (pairSumFiber A s).card * (shiftedPairSumFiber A d s).card := by
      apply Finset.sum_congr rfl
      intro s hs
      exact card_fourPrimeLeftSumFiber A d s

theorem card_additiveQuadruples_eq_sum_pairSumFiber_sq (A : Finset ℕ) :
    (additiveQuadruples A).card =
      ∑ s ∈ A + A, (pairSumFiber A s).card ^ 2 := by
  rw [card_additiveQuadruples, Finset.addEnergy_eq_sum_sq']
  rfl

/-- Natural target sum corresponding to translating a source sum by `d`. -/
def shiftTarget (d : ℤ) (s : ℕ) : ℕ := ((s : ℤ) + d).toNat

/-- Source sums for which translation by `d` is again a represented sum. -/
def validShiftSources (A : Finset ℕ) (d : ℤ) : Finset ℕ :=
  (A + A).filter fun s ↦ 0 ≤ (s : ℤ) + d ∧ shiftTarget d s ∈ A + A

theorem shiftedPairSumFiber_eq_pairSumFiber_of_mem_valid
    {A : Finset ℕ} {d : ℤ} {s : ℕ}
    (hs : s ∈ validShiftSources A d) :
    shiftedPairSumFiber A d s = pairSumFiber A (shiftTarget d s) := by
  have hs' := (Finset.mem_filter.mp hs).2
  have hcast : ((shiftTarget d s : ℕ) : ℤ) = (s : ℤ) + d := by
    exact Int.toNat_of_nonneg hs'.1
  ext x
  simp only [mem_shiftedPairSumFiber, mem_pairSumFiber]
  constructor
  · rintro ⟨hx₁, hx₂, hxsum⟩
    refine ⟨hx₁, hx₂, ?_⟩
    exact_mod_cast hxsum.trans hcast.symm
  · rintro ⟨hx₁, hx₂, hxsum⟩
    refine ⟨hx₁, hx₂, ?_⟩
    exact (congrArg (fun n : ℕ ↦ (n : ℤ)) hxsum).trans hcast

theorem shiftedPairSumFiber_eq_empty_of_not_mem_valid
    {A : Finset ℕ} {d : ℤ} {s : ℕ} (hsD : s ∈ A + A)
    (hs : s ∉ validShiftSources A d) :
    shiftedPairSumFiber A d s = ∅ := by
  ext x
  constructor
  · intro hx
    have hx' := mem_shiftedPairSumFiber.mp hx
    exfalso
    apply hs
    rw [validShiftSources, Finset.mem_filter]
    refine ⟨hsD, ?_⟩
    have hnonneg : 0 ≤ (s : ℤ) + d := by
      rw [← hx'.2.2]
      positivity
    refine ⟨hnonneg, ?_⟩
    have htarget : shiftTarget d s = x.1 + x.2 := by
      apply Int.ofNat_inj.mp
      change (((s : ℤ) + d).toNat : ℤ) = (x.1 + x.2 : ℕ)
      rw [Int.toNat_of_nonneg hnonneg]
      exact hx'.2.2.symm
    rw [htarget]
    exact Finset.mem_add.mpr ⟨x.1, hx'.1, x.2, hx'.2.1, rfl⟩
  · intro hx
    simp at hx

theorem shiftTarget_injective_on_valid (A : Finset ℕ) (d : ℤ) :
    Set.InjOn (shiftTarget d) (validShiftSources A d) := by
  intro s hs t ht heq
  have hs0 := (Finset.mem_filter.mp hs).2.1
  have ht0 := (Finset.mem_filter.mp ht).2.1
  have hsCast : ((shiftTarget d s : ℕ) : ℤ) = (s : ℤ) + d :=
    Int.toNat_of_nonneg hs0
  have htCast : ((shiftTarget d t : ℕ) : ℤ) = (t : ℤ) + d :=
    Int.toNat_of_nonneg ht0
  exact_mod_cast (show (s : ℤ) = t by
    rw [← add_left_cancel_iff (a := d)]
    omega)

theorem sum_shiftedPairSumFiber_sq_le (A : Finset ℕ) (d : ℤ) :
    (∑ s ∈ A + A, (shiftedPairSumFiber A d s).card ^ 2) ≤
      ∑ t ∈ A + A, (pairSumFiber A t).card ^ 2 := by
  let D := A + A
  let G := validShiftSources A d
  let f := shiftTarget d
  have hrestrict :
      (∑ s ∈ G, (shiftedPairSumFiber A d s).card ^ 2) =
        ∑ s ∈ D, (shiftedPairSumFiber A d s).card ^ 2 := by
    apply Finset.sum_subset
    · intro s hs
      exact (Finset.mem_filter.mp hs).1
    · intro s hsD hsG
      rw [shiftedPairSumFiber_eq_empty_of_not_mem_valid hsD hsG]
      simp
  have hfmem : ∀ s ∈ G, f s ∈ D := by
    intro s hs
    exact (Finset.mem_filter.mp hs).2.2
  have hfinj : Set.InjOn f G := by
    exact shiftTarget_injective_on_valid A d
  have himage : G.image f ⊆ D := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨s, hs, rfl⟩
    exact hfmem s hs
  have hreindex :
      (∑ s ∈ G, (shiftedPairSumFiber A d s).card ^ 2) =
        ∑ t ∈ G.image f, (pairSumFiber A t).card ^ 2 := by
    rw [Finset.sum_image hfinj]
    apply Finset.sum_congr rfl
    intro s hs
    rw [shiftedPairSumFiber_eq_pairSumFiber_of_mem_valid hs]
  rw [← hrestrict, hreindex]
  apply Finset.sum_le_sum_of_subset_of_nonneg himage
  intro t htD htImage
  exact Nat.zero_le _

/-- Every fixed translate of the two-prime sum correlation is at most its
zero translate, i.e. the additive energy. -/
theorem card_fourPrimeDifferenceFiber_le_additiveQuadruples
    (A : Finset ℕ) (d : ℤ) :
    (fourPrimeDifferenceFiber A d).card ≤ (additiveQuadruples A).card := by
  rw [card_fourPrimeDifferenceFiber_eq_sum,
    card_additiveQuadruples_eq_sum_pairSumFiber_sq]
  apply (Nat.pow_le_pow_iff_left (show (2 : ℕ) ≠ 0 by norm_num)).mp
  calc
    (∑ s ∈ A + A,
        (pairSumFiber A s).card * (shiftedPairSumFiber A d s).card) ^ 2 ≤
      (∑ s ∈ A + A, (pairSumFiber A s).card ^ 2) *
        (∑ s ∈ A + A, (shiftedPairSumFiber A d s).card ^ 2) := by
      exact Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) (A + A)
        (fun s ↦ (pairSumFiber A s).card)
        (fun s ↦ (shiftedPairSumFiber A d s).card)
    _ ≤ (∑ s ∈ A + A, (pairSumFiber A s).card ^ 2) *
        (∑ s ∈ A + A, (pairSumFiber A s).card ^ 2) := by
      exact Nat.mul_le_mul_left _ (sum_shiftedPairSumFiber_sq_le A d)
    _ = (∑ s ∈ A + A, (pairSumFiber A s).card ^ 2) ^ 2 := by ring

/-! ## Embedding a prime-pair fibre in the two-shift sieve -/

/-- The pairs of primes at distance `h` for which both primes exceed the
sieving endpoint. -/
def largeForwardPrimePairs (P h y : ℕ) : Finset (ℕ × ℕ) :=
  (forwardDifferencePairs (Nat.primesLE (2 * P)) h).filter fun x ↦
    y < x.1 ∧ y < x.2

theorem card_forwardDifferencePairs_le_large_add_small (P h y : ℕ) :
    ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ≤
      (largeForwardPrimePairs P h y).card + 2 * (y + 1) := by
  classical
  let F := forwardDifferencePairs (Nat.primesLE (2 * P)) h
  let L := largeForwardPrimePairs P h y
  let S := F.filter fun x ↦ x.1 ≤ y ∨ x.2 ≤ y
  have hcover : F ⊆ L ∪ S := by
    intro x hx
    by_cases hxlarge : y < x.1 ∧ y < x.2
    · exact Finset.mem_union_left _ (by simpa [L, largeForwardPrimePairs, F, hxlarge] using hx)
    · exact Finset.mem_union_right _ (by
        have : x.1 ≤ y ∨ x.2 ≤ y := by omega
        simp [S, hx, this])
  have hScard : S.card ≤ 2 * (y + 1) := by
    let T := Finset.range (y + 1)
    let f : ℕ × ℕ → ℕ := fun x ↦ x.1
    have hmaps : Set.MapsTo f S T := by
      intro x hx
      change x ∈ S at hx
      simp only [S, Finset.mem_filter] at hx
      have hxF : x ∈ F := hx.1
      have hxdiff : x.2 = x.1 + h :=
        (mem_forwardDifferencePairs.mp hxF).2.2
      have hx1 : x.1 ≤ y := by omega
      simpa [f, T] using hx1
    have hinj : Set.InjOn f S := by
      intro x hx z hz heq
      change x ∈ S at hx
      change z ∈ S at hz
      have hxF : x ∈ F := (Finset.mem_filter.mp hx).1
      have hzF : z ∈ F := (Finset.mem_filter.mp hz).1
      have hxdiff := (mem_forwardDifferencePairs.mp hxF).2.2
      have hzdiff := (mem_forwardDifferencePairs.mp hzF).2.2
      apply Prod.ext
      · exact heq
      · dsimp [f] at heq
        omega
    calc
      S.card ≤ T.card := Finset.card_le_card_of_injOn f hmaps hinj
      _ = y + 1 := by simp [T]
      _ ≤ 2 * (y + 1) := by omega
  have hcard : F.card ≤ L.card + S.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le L S)
  exact_mod_cast hcard.trans (Nat.add_le_add_left hScard L.card)

theorem prime_coprime_sievePrimeProduct_of_endpoint_lt
    {p y : ℕ} (hp : p.Prime) (hyp : y < p) :
    Nat.Coprime (Erdos387.sievePrimeProduct 2 (y + 1)) p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hpdiv
  have hmem := Erdos387.prime_mem_sievePrimes_of_dvd_product hp hpdiv
  have hpUpper := (Erdos387.mem_sievePrimes.mp hmem).2.2
  omega

theorem shiftedProduct_pair_eq {X p h : ℕ} (hh : h ≤ X) :
    Erdos851.ShiftSieve.shiftedProduct {X, X - h} (X + p) =
      if h = 0 then p else p * (p + h) := by
  by_cases h0 : h = 0
  · subst h
    simp [Erdos851.ShiftSieve.shiftedProduct]
  · simp only [Erdos851.ShiftSieve.shiftedProduct]
    have hshift : X - h ≠ X := by omega
    have hnot : X ∉ ({X - h} : Finset ℕ) := by
      simpa using hshift.symm
    rw [Finset.prod_insert hnot, Finset.prod_singleton, if_neg h0]
    congr 1 <;> omega

/-- A pair of primes larger than the sieving endpoint maps injectively to a
two-shift sifted candidate. -/
theorem card_largeForwardPrimePairs_le_sifted (P h y : ℕ) (hh : h ≤ 2 * P) :
    (largeForwardPrimePairs P h y).card ≤
      (Erdos851.ShiftSieve.siftedShiftCandidates
        {2 * P, 2 * P - h} (2 * P) 2 (y + 1)).card := by
  classical
  let S := largeForwardPrimePairs P h y
  let T := Erdos851.ShiftSieve.siftedShiftCandidates
    {2 * P, 2 * P - h} (2 * P) 2 (y + 1)
  let f : ℕ × ℕ → ℕ := fun x ↦ 2 * P + x.1
  have hmaps : Set.MapsTo f S T := by
    intro x hx
    change x ∈ S at hx
    have hxlarge := Finset.mem_filter.mp hx
    have hxpair := mem_forwardDifferencePairs.mp hxlarge.1
    have hp1le := (Nat.mem_primesLE.mp hxpair.1).1
    have hp2le := (Nat.mem_primesLE.mp hxpair.2.1).1
    have hp1 := (Nat.mem_primesLE.mp hxpair.1).2
    have hp2 := (Nat.mem_primesLE.mp hxpair.2.1).2
    have hcop1 := prime_coprime_sievePrimeProduct_of_endpoint_lt
      hp1 hxlarge.2.1
    have hcop2 := prime_coprime_sievePrimeProduct_of_endpoint_lt
      hp2 hxlarge.2.2
    change f x ∈ T
    change f x ∈ Erdos851.ShiftSieve.siftedShiftCandidates
      {2 * P, 2 * P - h} (2 * P) 2 (y + 1)
    simp only [Erdos851.ShiftSieve.siftedShiftCandidates,
      Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by
      dsimp [f]
      exact Nat.lt_add_of_pos_right hp1.pos,
      by dsimp [f]; omega⟩, ?_⟩
    rw [shiftedProduct_pair_eq hh]
    by_cases h0 : h = 0
    · rw [if_pos h0]
      exact hcop1
    · rw [if_neg h0]
      have hsum : x.1 + h = x.2 := hxpair.2.2.symm
      rw [hsum]
      exact hcop1.mul_right hcop2
  have hinj : Set.InjOn f S := by
    intro x hx z hz heq
    change x ∈ S at hx
    change z ∈ S at hz
    have hxpair := mem_forwardDifferencePairs.mp (Finset.mem_filter.mp hx).1
    have hzpair := mem_forwardDifferencePairs.mp (Finset.mem_filter.mp hz).1
    apply Prod.ext
    · dsimp [f] at heq
      omega
    · dsimp [f] at heq
      omega
  exact Finset.card_le_card_of_injOn f hmaps hinj

theorem forwardPrimeDifference_le_sifted_add_small
    (P h y : ℕ) (hh : h ≤ 2 * P) :
    ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ≤
      (Erdos851.ShiftSieve.siftedShiftCandidates
        {2 * P, 2 * P - h} (2 * P) 2 (y + 1)).card + 2 * (y + 1) := by
  calc
    ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ≤
        (largeForwardPrimePairs P h y).card + 2 * (y + 1) :=
      card_forwardDifferencePairs_le_large_add_small P h y
    _ ≤ (Erdos851.ShiftSieve.siftedShiftCandidates
          {2 * P, 2 * P - h} (2 * P) 2 (y + 1)).card + 2 * (y + 1) := by
      gcongr
      exact_mod_cast card_largeForwardPrimePairs_le_sifted P h y hh

/-! ## The analytic factors in the pair sieve -/

private theorem partial_euler_product_two : partial_euler_product 2 = 2 := by
  have hprimes : (Finset.Icc 1 2).filter Nat.Prime = {2} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_ho, hpTwo⟩, hp⟩
      have hpLower := hp.two_le
      omega
    · rintro rfl
      norm_num
  rw [partial_euler_product, hprimes]
  norm_num

theorem oneShift_localEulerProduct_two_eq (y : ℕ) (hy : 2 ≤ y) :
    Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y =
      2 / partial_euler_product y := by
  have hratio := Erdos851.oneShift_inverseLocalEulerProduct_eq hy
  rw [Erdos851.inverseLocalEulerProduct_eq_inv,
    partial_euler_product_two] at hratio
  have hpepPos : 0 < partial_euler_product y :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  calc
    Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y =
        (Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y)⁻¹⁻¹ := by rw [inv_inv]
    _ = (partial_euler_product y / 2)⁻¹ := by rw [hratio]
    _ = 2 / partial_euler_product y := by field_simp [hpepPos.ne']

theorem singularFactor_nonneg (h z y : ℕ) :
    0 ≤ Erdos851.singularFactor h z y := by
  unfold Erdos851.singularFactor
  exact Finset.prod_nonneg fun p hp ↦ by
    split_ifs
    · have hp' := Erdos851.mem_sievePrimes.mp hp
      exact div_nonneg (Nat.cast_nonneg p)
        (sub_nonneg.mpr (by exact_mod_cast hp'.2.2.one_le))
    · positivity

/-- Weak Mertens, in the direct-product direction needed by the upper
sieve. -/
theorem exists_oneShift_directMertens_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y ≤
        C / Real.log (y : ℝ) := by
  obtain ⟨Cl, hCl, hlower⟩ := weak_mertens_third_lower_all
  refine ⟨2 / Cl, by positivity, ?_⟩
  intro y hy
  have hyR : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos hyR
  have hpepPos : 0 < partial_euler_product y :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hlower' : Cl * Real.log (y : ℝ) ≤ partial_euler_product y := by
    simpa [Real.norm_of_nonneg hlog.le,
      Real.norm_of_nonneg (zero_le_one.trans
        (partial_euler_trivial_lower_bound (n := y)))]
      using hlower (y : ℝ) hyR.le
  rw [oneShift_localEulerProduct_two_eq y hy]
  calc
    2 / partial_euler_product y ≤ 2 / (Cl * Real.log (y : ℝ)) := by
      rw [div_le_div_iff₀ hpepPos (mul_pos hCl hlog)]
      nlinarith
    _ = (2 / Cl) / Real.log (y : ℝ) := by
      field_simp [hCl.ne', hlog.ne']

/-- Concrete two-shift beta-sieve bound, with the Euler product already
split into its Mertens part and its truncated singular factor. -/
theorem exists_forwardPrimeDifference_beta_bound :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ P h y S : ℕ, h ≤ 2 * P → 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ≤
          (2 * P : ℕ) *
              ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                ((C / Real.log (y : ℝ)) ^ 2 *
                  Erdos851.singularFactor h 2 y)) +
            ((y ^ S : ℕ) : ℝ) ^ 2 + 2 * (y + 1) := by
  obtain ⟨A, hA, hpair⟩ := Erdos851.exists_pairShift_concrete_cardinality_bounds
  obtain ⟨C, hC, hMertens⟩ := exists_oneShift_directMertens_bound
  refine ⟨A, C, hA, hC, ?_⟩
  intro P h y S hh hy hS hlog
  have hsieve := hpair (2 * P) (2 * P - h) (2 * P) 2 y S
    (by omega) (Nat.sub_le _ _) (by norm_num) (by omega) (by omega)
    hS hlog
  dsimp only at hsieve
  have hlocal := Erdos851.pairShift_localEulerProduct_le h
    (z := 2) (y := y) (by norm_num)
  have hdist : Nat.dist (2 * P) (2 * P - h) = h := by
    rw [Nat.dist_eq_sub_of_le_right (Nat.sub_le _ _), Nat.sub_sub_self hh]
  rw [hdist] at hsieve
  have hV := hMertens y hy
  have hVnonneg : 0 ≤ Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y :=
    Erdos851.oneShift_localEulerProduct_pos.le
  have hCdiv : 0 ≤ C / Real.log (y : ℝ) := by
    have : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    positivity
  have hVsq : Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y ^ 2 ≤
      (C / Real.log (y : ℝ)) ^ 2 :=
    (sq_le_sq₀ hVnonneg hCdiv).2 hV
  have hsingNonneg : 0 ≤ Erdos851.singularFactor h 2 y :=
    singularFactor_nonneg h 2 y
  have hpairProduct :
      Erdos851.localEulerProduct (Erdos851.pairShiftDensity h) 2 y ≤
        (C / Real.log (y : ℝ)) ^ 2 * Erdos851.singularFactor h 2 y :=
    hlocal.trans (mul_le_mul_of_nonneg_right hVsq hsingNonneg)
  have hcoeffNonneg :
      0 ≤ (2 * P : ℕ) *
        (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) := by
    have hA0 : 0 ≤ A := hA.trans' (by norm_num)
    positivity
  calc
    ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ≤
        (Erdos851.ShiftSieve.siftedShiftCandidates
          {2 * P, 2 * P - h} (2 * P) 2 (y + 1)).card + 2 * (y + 1) :=
      forwardPrimeDifference_le_sifted_add_small P h y hh
    _ ≤ (2 * P : ℕ) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            Erdos851.localEulerProduct (Erdos851.pairShiftDensity h) 2 y) +
          ((y ^ S : ℕ) : ℝ) ^ 2 + 2 * (y + 1) := by
      linarith [hsieve.2]
    _ ≤ (2 * P : ℕ) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            ((C / Real.log (y : ℝ)) ^ 2 *
              Erdos851.singularFactor h 2 y)) +
          ((y ^ S : ℕ) : ℝ) ^ 2 + 2 * (y + 1) := by
      gcongr

/-! ## Summing the pair bound -/

private theorem eventually_nthRoot_ge_local (k T : ℕ) (hk : k ≠ 0) :
    ∀ᶠ x : ℕ in atTop, T ≤ Nat.nthRoot k x := by
  filter_upwards [eventually_ge_atTop (T ^ k)] with x hx
  exact (Nat.le_nthRoot_iff hk).2 hx

private theorem nthRoot_pow_le_local {k x : ℕ} (hk : k ≠ 0) :
    Nat.nthRoot k x ^ k ≤ x :=
  (Nat.pow_nthRoot_le_iff).2 (Or.inl hk)

private theorem log_div_log_nthRoot_le
    {N S : ℕ} (hS : 0 < S)
    (hy : 2 ≤ Nat.nthRoot (4 * S) N) :
    Real.log (N : ℝ) /
        Real.log (Nat.nthRoot (4 * S) N : ℝ) ≤
      8 * (S : ℝ) := by
  let y := Nat.nthRoot (4 * S) N
  have hy2 : 2 ≤ y := by simpa [y] using hy
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hNat : N ≤ 2 ^ (4 * S) * y ^ (4 * S) := by
    have hxlt : N < (y + 1) ^ (4 * S) := by
      dsimp [y]
      exact Nat.lt_pow_nthRoot_add_one (by omega) N
    have hy_double : y + 1 ≤ 2 * y := by omega
    calc
      N ≤ (y + 1) ^ (4 * S) := hxlt.le
      _ ≤ (2 * y) ^ (4 * S) := Nat.pow_le_pow_left hy_double _
      _ = 2 ^ (4 * S) * y ^ (4 * S) := by ring
  have hNR : (0 : ℝ) < N := by
    have : 0 < N := by
      by_contra hn
      have hn0 : N = 0 := by omega
      rw [hn0, Nat.nthRoot_zero_right (by omega)] at hy
      omega
    exact_mod_cast this
  have hupperR :
      (0 : ℝ) < ((2 ^ (4 * S) * y ^ (4 * S) : ℕ) : ℝ) := by
    exact_mod_cast (by positivity : 0 < 2 ^ (4 * S) * y ^ (4 * S))
  have hlogmono : Real.log (N : ℝ) ≤
      Real.log (((2 ^ (4 * S) * y ^ (4 * S) : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa using hNR) (by simpa using hupperR) (by exact_mod_cast hNat)
  have hlogprod :
      Real.log (((2 ^ (4 * S) * y ^ (4 * S) : ℕ) : ℝ)) =
        (4 * (S : ℝ)) *
          (Real.log (2 : ℝ) + Real.log (y : ℝ)) := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog2le : Real.log (2 : ℝ) ≤ Real.log (y : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp) (by simp only [Set.mem_Ioi, Nat.cast_pos]; positivity) (by exact_mod_cast hy2)
  apply (div_le_iff₀ hlogy).2
  calc
    Real.log (N : ℝ) ≤
        Real.log (((2 ^ (4 * S) * y ^ (4 * S) : ℕ) : ℝ)) := hlogmono
    _ = (4 * (S : ℝ)) *
        (Real.log (2 : ℝ) + Real.log (y : ℝ)) := hlogprod
    _ ≤ (8 * (S : ℝ)) * Real.log (y : ℝ) := by
      have hS0 : (0 : ℝ) ≤ S := by positivity
      nlinarith

/-- Once the two fixed sieve constants and one admissible beta-sieve depth
are chosen, the consecutive singular-factor second moment gives the required
fourth-logarithm square-sum saving. -/
theorem forwardPrimeDifference_square_sum_eventually_of_parameters
    {A C : ℝ} (hA : 1 ≤ A) (hC : 0 < C) {S : ℕ}
    (hS : 101 ≤ S)
    (hlog : Real.log A ≤ 4 * (S - 100 : ℕ) / 99)
    (hpair : ∀ P h y : ℕ, h ≤ 2 * P → 2 ≤ y →
      ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ≤
        (2 * P : ℕ) *
            ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              ((C / Real.log (y : ℝ)) ^ 2 *
                Erdos851.singularFactor h 2 y)) +
          ((y ^ S : ℕ) : ℝ) ^ 2 + 2 * (y + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ P : ℕ in atTop,
      (∑ h ∈ Finset.range (2 * P + 1),
          ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ^ 2) ≤
        K * (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4 := by
  let B : ℝ := 1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let K₀ : ℝ := 2 * B * C ^ 2
  let L : ℝ := 8 * S
  let K : ℝ := 24 * K₀ ^ 2 * L ^ 4 + 111
  have hB : 0 < B := by
    dsimp [B]
    have hA0 : 0 ≤ A := zero_le_one.trans hA
    positivity
  have hK₀ : 0 < K₀ := by
    dsimp [K₀]
    positivity
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  have hlogdom : ∀ᶠ P : ℕ in atTop,
      Real.log (P : ℝ) ^ 4 ≤ (P : ℝ) := by
    have htend : Tendsto
        (fun P : ℕ ↦ Real.log (P : ℝ) ^ 4 / (P : ℝ))
        atTop (nhds 0) := by
      have ht :=
        (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
          (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero.comp
            tendsto_natCast_atTop_atTop
      convert ht using 1
      funext P
      dsimp only [Function.comp_apply]
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, Real.rpow_one]
    have hsmall := htend.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with P hsmall hP
    have hPR : (0 : ℝ) < P := by exact_mod_cast hP
    rw [div_lt_iff₀ hPR] at hsmall
    simpa only [one_mul] using hsmall.le
  filter_upwards [eventually_nthRoot_ge_local (4 * S) 2 (by omega),
    eventually_ge_atTop 2, hlogdom] with P hy hP hlogPdom
  let y := Nat.nthRoot (4 * S) P
  have hy' : 2 ≤ y := by simpa [y] using hy
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hscale : Real.log (P : ℝ) / Real.log (y : ℝ) ≤ L := by
    simpa [y, L] using
      (log_div_log_nthRoot_le
        (N := P) (S := S) (by omega) hy')
  have hlog_le : Real.log (P : ℝ) ≤ L * Real.log (y : ℝ) := by
    exact (div_le_iff₀ hlogy).mp hscale
  have hlog_pow : Real.log (P : ℝ) ^ 4 ≤
      L ^ 4 * Real.log (y : ℝ) ^ 4 := by
    calc
      Real.log (P : ℝ) ^ 4 ≤ (L * Real.log (y : ℝ)) ^ 4 := by
        gcongr
      _ = L ^ 4 * Real.log (y : ℝ) ^ 4 := by ring
  have hinvlog : 1 / Real.log (y : ℝ) ^ 4 ≤
      L ^ 4 / Real.log (P : ℝ) ^ 4 := by
    rw [div_le_div_iff₀ (pow_pos hlogy 4) (pow_pos hlogP 4)]
    simpa using hlog_pow
  have hroot : y ^ (4 * S) ≤ P := by
    dsimp [y]
    exact nthRoot_pow_le_local (by omega)
  have hy_sq : y ^ 2 ≤ P := by
    calc
      y ^ 2 ≤ y ^ (4 * S) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ P := hroot
  have herror : ((((y ^ S : ℕ) : ℝ) ^ 2) ^ 2) ≤ (P : ℝ) := by
    exact_mod_cast (show ((y ^ S) ^ 2) ^ 2 ≤ P by
      calc
        ((y ^ S) ^ 2) ^ 2 = y ^ (4 * S) := by ring
        _ ≤ P := hroot)
  have hyadd : (((y + 1 : ℕ) : ℝ) ^ 2) ≤ 4 * (P : ℝ) := by
    have hyaddNat : (y + 1) ^ 2 ≤ 4 * P := by
      calc
        (y + 1) ^ 2 ≤ (2 * y) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4 * y ^ 2 := by ring
        _ ≤ 4 * P := Nat.mul_le_mul_left 4 hy_sq
    exact_mod_cast hyaddNat
  have hyadd' : ((y : ℝ) + 1) ^ 2 ≤ 4 * (P : ℝ) := by
    norm_num [Nat.cast_add] at hyadd ⊢
    exact hyadd
  have hpoint (h : ℕ) (hh : h ∈ Finset.Ioc 0 (2 * P)) :
      ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ^ 2 ≤
        3 * ((K₀ * (P : ℝ) / Real.log (y : ℝ) ^ 2 *
                Erdos851.singularFactor h 2 y) ^ 2 +
          (((y ^ S : ℕ) : ℝ) ^ 2) ^ 2 +
          (2 * ((y : ℝ) + 1)) ^ 2) := by
    have hh' : h ≤ 2 * P := (Finset.mem_Ioc.mp hh).2
    have hp := hpair P h y hh' hy'
    have hmain :
        ((2 * P : ℕ) : ℝ) *
              (B * ((C / Real.log (y : ℝ)) ^ 2 *
                Erdos851.singularFactor h 2 y)) =
          K₀ * (P : ℝ) / Real.log (y : ℝ) ^ 2 *
            Erdos851.singularFactor h 2 y := by
      dsimp [K₀]
      push_cast
      field_simp [hlogy.ne']
    change _ ≤ ((2 * P : ℕ) : ℝ) *
        (B * ((C / Real.log (y : ℝ)) ^ 2 *
          Erdos851.singularFactor h 2 y)) +
        ((y ^ S : ℕ) : ℝ) ^ 2 + 2 * ((y : ℝ) + 1) at hp
    rw [hmain] at hp
    have hsing := singularFactor_nonneg h 2 y
    have hmain0 : 0 ≤ K₀ * (P : ℝ) / Real.log (y : ℝ) ^ 2 *
        Erdos851.singularFactor h 2 y := by positivity
    have hq0 : 0 ≤ ((forwardDifferencePairs
        (Nat.primesLE (2 * P)) h).card : ℝ) := Nat.cast_nonneg _
    have herr0 : 0 ≤ (((y ^ S : ℕ) : ℝ) ^ 2) := sq_nonneg _
    have hsmall0 : 0 ≤ 2 * ((y : ℝ) + 1) := by positivity
    nlinarith [sq_nonneg
      (K₀ * (P : ℝ) / Real.log (y : ℝ) ^ 2 *
          Erdos851.singularFactor h 2 y -
        (((y ^ S : ℕ) : ℝ) ^ 2)),
      sq_nonneg
        (K₀ * (P : ℝ) / Real.log (y : ℝ) ^ 2 *
          Erdos851.singularFactor h 2 y - 2 * ((y : ℝ) + 1)),
      sq_nonneg ((((y ^ S : ℕ) : ℝ) ^ 2) -
        2 * ((y : ℝ) + 1))]
  have hmainsum :
      (∑ h ∈ Finset.Ioc 0 (2 * P),
          (K₀ * (P : ℝ) / Real.log (y : ℝ) ^ 2 *
            Erdos851.singularFactor h 2 y) ^ 2) ≤
        8 * K₀ ^ 2 * L ^ 4 * (P : ℝ) ^ 3 /
          Real.log (P : ℝ) ^ 4 := by
    have hsingSum := sum_Ioc_singularFactor_sq_le 2 y (2 * P) (by norm_num)
    calc
      (∑ h ∈ Finset.Ioc 0 (2 * P),
          (K₀ * (P : ℝ) / Real.log (y : ℝ) ^ 2 *
            Erdos851.singularFactor h 2 y) ^ 2) =
          (K₀ * (P : ℝ) / Real.log (y : ℝ) ^ 2) ^ 2 *
            ∑ h ∈ Finset.Ioc 0 (2 * P),
              Erdos851.singularFactor h 2 y ^ 2 := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
      _ ≤ (K₀ * (P : ℝ) / Real.log (y : ℝ) ^ 2) ^ 2 *
            (4 * ((2 * P : ℕ) : ℝ)) := by
        gcongr
      _ = 8 * K₀ ^ 2 * (P : ℝ) ^ 3 *
            (1 / Real.log (y : ℝ) ^ 4) := by
        push_cast
        field_simp [hlogy.ne']
        ring
      _ ≤ 8 * K₀ ^ 2 * (P : ℝ) ^ 3 *
            (L ^ 4 / Real.log (P : ℝ) ^ 4) := by
        gcongr
      _ = 8 * K₀ ^ 2 * L ^ 4 * (P : ℝ) ^ 3 /
            Real.log (P : ℝ) ^ 4 := by ring
  have herrorsum :
      (∑ _h ∈ Finset.Ioc 0 (2 * P),
          ((((y ^ S : ℕ) : ℝ) ^ 2) ^ 2)) ≤
        2 * (P : ℝ) ^ 2 := by
    rw [Finset.sum_const, Nat.card_Ioc]
    simp only [nsmul_eq_mul]
    have hcard : ((2 * P - 0 : ℕ) : ℝ) = 2 * (P : ℝ) := by
      norm_num
    rw [hcard]
    nlinarith
  have hsmallsum :
      (∑ _h ∈ Finset.Ioc 0 (2 * P),
          (2 * ((y : ℝ) + 1)) ^ 2) ≤
        32 * (P : ℝ) ^ 2 := by
    rw [Finset.sum_const, Nat.card_Ioc]
    simp only [nsmul_eq_mul]
    have hcard : ((2 * P - 0 : ℕ) : ℝ) = 2 * (P : ℝ) := by
      norm_num
    rw [hcard]
    nlinarith [hyadd']
  have hpositiveSum :
      (∑ h ∈ Finset.Ioc 0 (2 * P),
          ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ^ 2) ≤
        24 * K₀ ^ 2 * L ^ 4 * (P : ℝ) ^ 3 /
            Real.log (P : ℝ) ^ 4 + 102 * (P : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ h ∈ Finset.Ioc 0 (2 * P),
          3 * ((K₀ * (P : ℝ) / Real.log (y : ℝ) ^ 2 *
                Erdos851.singularFactor h 2 y) ^ 2 +
            (((y ^ S : ℕ) : ℝ) ^ 2) ^ 2 +
            (2 * ((y : ℝ) + 1)) ^ 2) := by
        exact Finset.sum_le_sum fun h hh ↦ hpoint h hh
      _ = 3 * ((∑ h ∈ Finset.Ioc 0 (2 * P),
              (K₀ * (P : ℝ) / Real.log (y : ℝ) ^ 2 *
                Erdos851.singularFactor h 2 y) ^ 2) +
            (∑ _h ∈ Finset.Ioc 0 (2 * P),
              (((y ^ S : ℕ) : ℝ) ^ 2) ^ 2) +
            (∑ _h ∈ Finset.Ioc 0 (2 * P),
              (2 * ((y : ℝ) + 1)) ^ 2)) := by
        symm
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.mul_sum _ _ _
      _ ≤ 3 * ((8 * K₀ ^ 2 * L ^ 4 * (P : ℝ) ^ 3 /
              Real.log (P : ℝ) ^ 4) +
            (2 * (P : ℝ) ^ 2) + 32 * (P : ℝ) ^ 2) := by
        gcongr
      _ = 24 * K₀ ^ 2 * L ^ 4 * (P : ℝ) ^ 3 /
            Real.log (P : ℝ) ^ 4 + 102 * (P : ℝ) ^ 2 := by ring
  have hzero :
      ((forwardDifferencePairs (Nat.primesLE (2 * P)) 0).card : ℝ) ^ 2 ≤
        9 * (P : ℝ) ^ 2 := by
    have hc : (forwardDifferencePairs (Nat.primesLE (2 * P)) 0).card ≤
        2 * P + 1 :=
      (card_forwardDifferencePairs_le_card _ _).trans
        (card_primesLE_le_succ (2 * P))
    have hcR : ((forwardDifferencePairs
        (Nat.primesLE (2 * P)) 0).card : ℝ) ≤ 3 * (P : ℝ) := by
      exact_mod_cast (hc.trans (by omega : 2 * P + 1 ≤ 3 * P))
    nlinarith [sq_nonneg
      (((forwardDifferencePairs (Nat.primesLE (2 * P)) 0).card : ℝ))]
  have hfull :
      (∑ h ∈ Finset.range (2 * P + 1),
          ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ^ 2) ≤
        24 * K₀ ^ 2 * L ^ 4 * (P : ℝ) ^ 3 /
            Real.log (P : ℝ) ^ 4 + 111 * (P : ℝ) ^ 2 := by
    have hrange : Finset.range (2 * P + 1) =
        insert 0 (Finset.Ioc 0 (2 * P)) := by
      ext h
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [hrange, Finset.sum_insert (by simp)]
    linarith
  have herrabsorb : (P : ℝ) ^ 2 ≤
      (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4 := by
    rw [le_div_iff₀ (pow_pos hlogP 4)]
    calc
      (P : ℝ) ^ 2 * Real.log (P : ℝ) ^ 4 ≤
          (P : ℝ) ^ 2 * (P : ℝ) :=
        mul_le_mul_of_nonneg_left hlogPdom (sq_nonneg (P : ℝ))
      _ = (P : ℝ) ^ 3 := by ring
  let X : ℝ := (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4
  have hfullX :
      (∑ h ∈ Finset.range (2 * P + 1),
          ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ^ 2) ≤
        (24 * K₀ ^ 2 * L ^ 4) * X + 111 * (P : ℝ) ^ 2 := by
    simpa only [X, mul_div_assoc] using hfull
  have herrabsorbX : (P : ℝ) ^ 2 ≤ X := by
    simpa only [X] using herrabsorb
  rw [show K = 24 * K₀ ^ 2 * L ^ 4 + 111 by rfl]
  rw [mul_div_assoc]
  change (∑ h ∈ Finset.range (2 * P + 1),
      ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ^ 2) ≤
    (24 * K₀ ^ 2 * L ^ 4 + 111) * X
  calc
    (∑ h ∈ Finset.range (2 * P + 1),
        ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ^ 2) ≤
      (24 * K₀ ^ 2 * L ^ 4) * X + 111 * (P : ℝ) ^ 2 := hfullX
    _ ≤ (24 * K₀ ^ 2 * L ^ 4) * X + 111 * X := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left herrabsorbX
          (show (0 : ℝ) ≤ 111 by norm_num)) _
    _ = (24 * K₀ ^ 2 * L ^ 4 + 111) * X := by ring

/-- The pair-difference square sum for primes up to `2P` has the fourth
logarithmic saving required in the MRT minor-arc argument. -/
theorem exists_forwardPrimeDifference_square_sum_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ P : ℕ in atTop,
      (∑ h ∈ Finset.range (2 * P + 1),
          ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ^ 2) ≤
        K * (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4 := by
  obtain ⟨A, C, hA, hC, hbeta⟩ := exists_forwardPrimeDifference_beta_bound
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt (99 * Real.log A / 4)
  let S : ℕ := max 101 (T + 100)
  have hS : 101 ≤ S := by
    dsimp [S]
    exact le_max_left _ _
  have hTS : T ≤ S - 100 := by
    dsimp [S]
    omega
  have hlog : Real.log A ≤ 4 * (S - 100 : ℕ) / 99 := by
    have hTSR : (T : ℝ) ≤ (S - 100 : ℕ) := by exact_mod_cast hTS
    have hT' : 99 * Real.log A < (T : ℝ) * 4 :=
      (div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hT
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 99)).2
    calc
      Real.log A * 99 ≤ (T : ℝ) * 4 := by
        simpa only [mul_comm] using hT'.le
      _ ≤ (S - 100 : ℕ) * 4 :=
        mul_le_mul_of_nonneg_right hTSR (by norm_num)
      _ = 4 * (S - 100 : ℕ) := by ring
  exact forwardPrimeDifference_square_sum_eventually_of_parameters hA hC hS hlog
    (fun P h y hh hy ↦ hbeta P h y S hh hy hS hlog)

/-- Additive energy of the primes up to `2P`, in its explicit quadruple
model, inherits the same logarithmic saving. -/
theorem exists_primesLE_additiveQuadruples_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ P : ℕ in atTop,
      ((additiveQuadruples (Nat.primesLE (2 * P))).card : ℝ) ≤
        K * (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4 := by
  obtain ⟨K, hK, hsum⟩ := exists_forwardPrimeDifference_square_sum_bound
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [hsum] with P hsumP
  have hcomb := additiveQuadruples_card_le_two_mul_difference_square_sum
    (Nat.primesLE (2 * P)) (2 * P)
    (fun p hp ↦ (Nat.mem_primesLE.mp hp).1)
  have hcombR :
      ((additiveQuadruples (Nat.primesLE (2 * P))).card : ℝ) ≤
        2 * ∑ h ∈ Finset.range (2 * P + 1),
          ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ^ 2 := by
    exact_mod_cast hcomb
  calc
    ((additiveQuadruples (Nat.primesLE (2 * P))).card : ℝ) ≤
        2 * ∑ h ∈ Finset.range (2 * P + 1),
          ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ^ 2 := hcombR
    _ ≤ 2 * (K * (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4) := by
      gcongr
    _ = (2 * K) * (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4 := by ring

/-- Eventual uniform bound for every signed four-prime difference fiber. -/
theorem exists_eventually_primesLE_fourPrimeDifferenceFiber_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ P : ℕ in atTop,
      ∀ d : ℤ,
        ((fourPrimeDifferenceFiber (Nat.primesLE (2 * P)) d).card : ℝ) ≤
          K * (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4 := by
  obtain ⟨K, hK, henergy⟩ := exists_primesLE_additiveQuadruples_bound
  refine ⟨K, hK, ?_⟩
  filter_upwards [henergy] with P hP
  intro d
  calc
    ((fourPrimeDifferenceFiber (Nat.primesLE (2 * P)) d).card : ℝ) ≤
        ((additiveQuadruples (Nat.primesLE (2 * P))).card : ℝ) := by
      exact_mod_cast card_fourPrimeDifferenceFiber_le_additiveQuadruples
        (Nat.primesLE (2 * P)) d
    _ ≤ K * (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4 := hP

theorem card_fourPrimeDifferenceFiber_le_fourth_power (A : Finset ℕ) (d : ℤ) :
    (fourPrimeDifferenceFiber A d).card ≤ A.card ^ 4 := by
  calc
    (fourPrimeDifferenceFiber A d).card ≤
        (((A ×ˢ A) ×ˢ (A ×ˢ A))).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = A.card ^ 4 := by
      simp only [Finset.card_product]
      ring


end

end Erdos67
