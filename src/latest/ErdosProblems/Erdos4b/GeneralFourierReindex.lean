/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierFiniteIntegral
import ErdosProblems.Erdos4b.GeneralFourierAffineEdges
import ErdosProblems.Erdos4b.GeneralFourierCoefficientSquare

/-!
# Reindexing the finite doubled divisor sum

The finite Fourier coefficient sum is invariant under an equivalence
of the shift index sets. This connects the fixed analytic `Fin K`
index to the cutoff-dependent arithmetic primorial tuple.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def reindexDoubledDivisors {ι κ : Type*} (e : ι ≃ κ) :
    ((κ ⊕ κ) → Bool → ℕ) ≃ ((ι ⊕ ι) → Bool → ℕ) :=
  Equiv.arrowCongr (e.sumCongr e).symm (Equiv.refl _)

@[simp] theorem reindexDoubledDivisors_apply {ι κ : Type*} (e : ι ≃ κ)
    (d : (κ ⊕ κ) → Bool → ℕ) (i : ι ⊕ ι) (b : Bool) :
    reindexDoubledDivisors e d i b = d ((e.sumCongr e) i) b := rfl

theorem withinFamilyDivisorCoprime_reindex_iff {ι κ : Type*} (e : ι ≃ κ)
    (d : (κ ⊕ κ) → Bool → ℕ) :
    WithinFamilyDivisorCoprime (reindexDoubledDivisors e d) ↔ WithinFamilyDivisorCoprime d := by
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · intro i j hij a b
      simpa using hleft (e.symm i) (e.symm j)
        (fun h ↦ hij (e.symm.injective h)) a b
    · intro i j hij a b
      simpa using hright (e.symm i) (e.symm j)
        (fun h ↦ hij (e.symm.injective h)) a b
  · rintro ⟨hleft, hright⟩
    exact ⟨fun i j hij a b ↦ hleft (e i) (e j) (fun h ↦ hij (e.injective h)) a b,
      fun i j hij a b ↦ hright (e i) (e j) (fun h ↦ hij (e.injective h)) a b⟩

theorem mem_doubledCutoffDivisorTuples_reindex_iff
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (d : (κ ⊕ κ) → Bool → ℕ) :
    reindexDoubledDivisors e d ∈ doubledCutoffDivisorTuples ι P ↔
      d ∈ doubledCutoffDivisorTuples κ P := by
  rw [mem_doubledCutoffDivisorTuples P hP, mem_doubledCutoffDivisorTuples P hP,
    withinFamilyDivisorCoprime_reindex_iff]
  apply and_congr_left
  intro hcop
  constructor
  · intro h i b
    obtain ⟨j, rfl⟩ := (e.sumCongr e).surjective i
    exact h j b
  · exact fun h i b ↦ h ((e.sumCongr e) i) b

def reindexFourierEdges {ι κ : Type*} (e : ι ≃ κ)
    (edges : ℕ → Finset (κ × κ)) (p : ℕ) : Finset (ι × ι) :=
  (edges p).map (e.symm.prodCongr e.symm).toEmbedding

@[simp] theorem mem_reindexFourierEdges {ι κ : Type*} (e : ι ≃ κ)
    (edges : ℕ → Finset (κ × κ)) (p : ℕ) (i j : ι) :
    (i, j) ∈ reindexFourierEdges e edges p ↔ (e i, e j) ∈ edges p := by
  simp [reindexFourierEdges, Finset.mem_map_equiv]

theorem doubledDivisorPrimeCompatible_reindex_iff {ι κ : Type*} (e : ι ≃ κ)
    (P : Finset ℕ) (edges : ℕ → Finset (κ × κ)) (companion : ℕ → Bool)
    (d : (κ ⊕ κ) → Bool → ℕ) :
    DoubledDivisorPrimeCompatible P (reindexFourierEdges e edges) companion
        (reindexDoubledDivisors e d) ↔
      DoubledDivisorPrimeCompatible P edges companion d := by
  constructor
  · intro h p
    constructor
    · intro j hj
      simpa using (h p).1 (e.symm j) (by simpa using hj)
    · intro i j hi hj
      simpa using (h p).2 (e.symm i) (e.symm j) (by simpa using hi) (by simpa using hj)
  · intro h p
    constructor
    · exact fun j hj ↦ (h p).1 (e j) hj
    · intro i j hi hj
      exact (mem_reindexFourierEdges e edges p i j).mpr ((h p).2 (e i) (e j) hi hj)

theorem flatDoubledDivisorLcm_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (d : (κ ⊕ κ) → Bool → ℕ) :
    (Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
        (fun ib ↦ reindexDoubledDivisors e d ib.1 ib.2) =
      (Finset.univ : Finset ((κ ⊕ κ) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro ib hib
    exact Finset.dvd_lcm (Finset.mem_univ ((e.sumCongr e) ib.1, ib.2))
  · apply Finset.lcm_dvd
    rintro ⟨i, b⟩ hib
    obtain ⟨j, rfl⟩ := (e.sumCongr e).surjective i
    exact Finset.dvd_lcm (Finset.mem_univ (j, b))

theorem doubledSelbergProfileTensor_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (F : ((κ ⊕ κ) × Bool) → ℝ → ℂ) (L : (κ ⊕ κ) → Bool → ℝ)
    (d : (κ ⊕ κ) → Bool → ℕ) :
    doubledSelbergProfileTensor (fun ib ↦ F ((e.sumCongr e) ib.1, ib.2))
        (fun i b ↦ L ((e.sumCongr e) i) b) (reindexDoubledDivisors e d) =
      doubledSelbergProfileTensor F L d := by
  unfold doubledSelbergProfileTensor
  exact ((e.sumCongr e).prodCongr (Equiv.refl Bool)).prod_comp
    (fun ib ↦ (ArithmeticFunction.moebius (d ib.1 ib.2) : ℂ) *
      F ib (Real.log (d ib.1 ib.2) / L ib.1 ib.2))

theorem cutoffSelbergProfileTensorSum_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (κ × κ)) (companion : ℕ → Bool)
    (F : ((κ ⊕ κ) × Bool) → ℝ → ℂ) (L : (κ ⊕ κ) → Bool → ℝ) :
    cutoffSelbergProfileTensorSum P (reindexFourierEdges e edges) companion
        (fun ib ↦ F ((e.sumCongr e) ib.1, ib.2)) (fun i b ↦ L ((e.sumCongr e) i) b) =
      cutoffSelbergProfileTensorSum P edges companion F L := by
  classical
  unfold cutoffSelbergProfileTensorSum
  symm
  apply Finset.sum_bij (fun d hd ↦ reindexDoubledDivisors e d)
  · intro d hd
    exact (mem_doubledCutoffDivisorTuples_reindex_iff e P hP d).mpr hd
  · intro d hd d' hd' heq
    exact (reindexDoubledDivisors e).injective heq
  · intro d hd
    refine ⟨(reindexDoubledDivisors e).symm d, ?_, (reindexDoubledDivisors e).apply_symm_apply d⟩
    apply (mem_doubledCutoffDivisorTuples_reindex_iff e P hP _).mp
    simpa only [Equiv.apply_symm_apply] using hd
  · intro d hd
    rw [doubledDivisorPrimeCompatible_reindex_iff,
      doubledSelbergProfileTensor_reindex, flatDoubledDivisorLcm_reindex]

theorem cutoffSelbergBilinearSum_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (κ × κ)) (companion : ℕ → Bool)
    (a b : ((κ ⊕ κ) → ℕ) → ℂ) :
    cutoffSelbergBilinearSum P (reindexFourierEdges e edges) companion
        (fun d ↦ a (fun j ↦ d ((e.sumCongr e).symm j)))
        (fun d ↦ b (fun j ↦ d ((e.sumCongr e).symm j))) =
      cutoffSelbergBilinearSum P edges companion a b := by
  classical
  unfold cutoffSelbergBilinearSum
  symm
  apply Finset.sum_bij (fun d hd ↦ reindexDoubledDivisors e d)
  · intro d hd
    exact (mem_doubledCutoffDivisorTuples_reindex_iff e P hP d).mpr hd
  · intro d hd d' hd' heq
    exact (reindexDoubledDivisors e).injective heq
  · intro d hd
    refine ⟨(reindexDoubledDivisors e).symm d, ?_, (reindexDoubledDivisors e).apply_symm_apply d⟩
    apply (mem_doubledCutoffDivisorTuples_reindex_iff e P hP _).mp
    simpa only [Equiv.apply_symm_apply] using hd
  · intro d hd
    rw [doubledDivisorPrimeCompatible_reindex_iff, flatDoubledDivisorLcm_reindex]
    simp only [reindexDoubledDivisors_apply, Equiv.apply_symm_apply]

theorem selbergTensorCoefficient_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (F : (κ ⊕ κ) → ℝ → ℂ) (L : (κ ⊕ κ) → ℝ) (d : (κ ⊕ κ) → ℕ) :
    selbergTensorCoefficient (fun i ↦ F ((e.sumCongr e) i))
      (fun i ↦ L ((e.sumCongr e) i)) (fun i ↦ d ((e.sumCongr e) i)) =
        selbergTensorCoefficient F L d := by
  exact (e.sumCongr e).prod_comp
    (fun i ↦ (ArithmeticFunction.moebius (d i) : ℂ) * F i (Real.log (d i) / L i))

end

end Erdos4b
