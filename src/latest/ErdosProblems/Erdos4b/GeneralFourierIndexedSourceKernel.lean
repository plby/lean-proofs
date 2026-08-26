/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierReindex
import ErdosProblems.Erdos4b.GeneralFourierSourceCoefficient
import ErdosProblems.Erdos4b.GeneralFourierTensorSquareAsymptotic

/-!
# The fixed-index Fourier square and the original source kernel

The source profiles are transported to the primorial tuple through its
explicit equivalence with `Fin K`. The coefficient and kernel identities
are exact at the same prime cutoff on both sides.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem twoFamilySelbergProfiles_transport_pullback
    {ι κ : Type*} (e : ι ≃ κ) (F : ι → ℝ → ℝ) (G : ℝ → ℝ) :
    (fun i ↦ twoFamilySelbergProfiles (fun j ↦ F (e.symm j)) G ((e.sumCongr e) i)) =
      twoFamilySelbergProfiles F G := by
  funext i t
  cases i <;> simp [twoFamilySelbergProfiles]

theorem twoFamilySelbergScales_pullback
    {ι κ : Type*} (e : ι ≃ κ) (LD LE : ℝ) :
    (fun i ↦ twoFamilySelbergScales LD LE ((e.sumCongr e) i)) =
      twoFamilySelbergScales LD LE := by
  funext i
  cases i <;> rfl

theorem sourceAnalyticSelbergCoefficient_transport
    {ι κ J : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ) (LD LE : ℝ)
    (d : (ι ⊕ ι) → ℕ) :
    (sourceAnalyticSelbergCoefficient S (fun j i ↦ F j (e.symm i)) G LD LE
        (fun i ↦ d (.inl (e.symm i))) (fun i ↦ d (.inr (e.symm i))) : ℂ) =
      ∑ j ∈ S, selbergTensorCoefficient (twoFamilySelbergProfiles (F j) G)
        (twoFamilySelbergScales LD LE) d := by
  have hcoef := sourceAnalyticSelbergCoefficient_eq_tensor_sum_of_flat S
    (fun j i ↦ F j (e.symm i)) G LD LE (fun i ↦ d ((e.sumCongr e).symm i))
  simp only [Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr] at hcoef
  rw [hcoef]
  apply Finset.sum_congr rfl
  intro j hj
  have h := selbergTensorCoefficient_reindex e
    (twoFamilySelbergProfiles (fun i ↦ F j (e.symm i)) G) (twoFamilySelbergScales LD LE)
    (fun i ↦ d ((e.sumCongr e).symm i))
  rw [twoFamilySelbergProfiles_transport_pullback, twoFamilySelbergScales_pullback] at h
  simp only [Equiv.symm_apply_apply] at h
  simpa only [Equiv.sumCongr_symm, Equiv.sumCongr_apply] using h.symm

theorem indexed_cutoffTensorSquare_eq_sourceCoordinateKernel
    {K w m q : ℕ} {J : Type*} (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hm : 0 < m) (hq : q.Prime) (hKw : K ≤ w)
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (LD LE : ℝ) (A : (preSievedShifts K w ⊕ preSievedShifts K w) → ℝ)
    (hLD : 0 < LD) (hLE : 0 < LE)
    (hsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t →
      twoFamilySelbergProfiles (fun h ↦ F j ((preSievedShiftEquiv K w).symm h)) G i t ≠ 0 → t ≤ A i)
    (hAq : ∀ i, A i * twoFamilySelbergScales LD LE i < Real.log q) :
    cutoffSelbergBilinearSum P (indexedPreSievedFourierEdges K w m q)
        (affineFourierCompanionSwitch m)
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (twoFamilySelbergProfiles (F j) G)
          (twoFamilySelbergScales LD LE) d)
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (twoFamilySelbergProfiles (F j) G)
          (twoFamilySelbergScales LD LE) d) =
      (doubledSelbergCoordinateLcmKernel (preSievedShifts K w)
        (cutoffDivisorTupleSupport (preSievedShifts K w) P)
        (cutoffCompanionDivisorTupleSupport (preSievedShifts K w) P m)
        (sourceAnalyticSelbergCoefficient S
          (fun j h ↦ F j ((preSievedShiftEquiv K w).symm h)) G LD LE) m q : ℂ) := by
  let e := preSievedShiftEquiv K w
  let a (d : (preSievedShifts K w ⊕ preSievedShifts K w) → ℕ) : ℂ :=
    sourceAnalyticSelbergCoefficient S (fun j i ↦ F j (e.symm i)) G LD LE
      (fun i ↦ d (.inl i)) (fun i ↦ d (.inr i))
  have htransport (d : (Fin K ⊕ Fin K) → ℕ) :
      a (fun i ↦ d ((e.sumCongr e).symm i)) =
        ∑ j ∈ S, selbergTensorCoefficient (twoFamilySelbergProfiles (F j) G)
          (twoFamilySelbergScales LD LE) d :=
    sourceAnalyticSelbergCoefficient_transport e S F G LD LE d
  have hindex := cutoffSelbergBilinearSum_reindex e P hP
    (affineFourierCollisionEdges (preSievedShifts K w) m q) (affineFourierCompanionSwitch m) a a
  simp only [htransport] at hindex
  change cutoffSelbergBilinearSum P (indexedPreSievedFourierEdges K w m q)
      (affineFourierCompanionSwitch m) _ _ = _ at hindex
  rw [hindex]
  have hsource := sourceAnalyticSelbergCoordinateKernel_eq_cutoffTensorSquare P hP hrough hm hq hKw
    S (fun j h ↦ F j (e.symm h)) G LD LE A hLD hLE hsupport hAq
  rw [hsource]
  congr 1 <;> funext d
  · exact sourceAnalyticSelbergCoefficient_eq_tensor_sum_of_flat S
      (fun j h ↦ F j (e.symm h)) G LD LE d
  · exact sourceAnalyticSelbergCoefficient_eq_tensor_sum_of_flat S
      (fun j h ↦ F j (e.symm h)) G LD LE d

end

end Erdos4b
