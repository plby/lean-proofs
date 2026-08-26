/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceTensorVariational

/-!
# Finite tensor energies reduced to one-dimensional pair integrals

The factors need not be smooth. The identities therefore apply both to
rectangle indicators and to their smooth approximations.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

theorem integral_weighted_real_tensor_square {ι J : Type*} [Fintype ι]
    (S : Finset J) (c : J → ℝ) (ψ : J → ι → ℝ → ℝ)
    (hint : ∀ j ∈ S, ∀ k ∈ S, ∀ i,
      IntegrableOn (fun t ↦ ψ j i t * ψ k i t) (Set.Ioi 0)) :
    (∫ t : ι → ℝ in Set.univ.pi (fun _ ↦ Set.Ioi 0),
      (∑ j ∈ S, c j * ∏ i, ψ j i (t i)) ^ 2) =
      ∑ j ∈ S, ∑ k ∈ S, (c j * c k) * ∏ i,
        ∫ t : ℝ in Set.Ioi 0, ψ j i t * ψ k i t := by
  have hi (j : J) (hj : j ∈ S) (k : J) (hk : k ∈ S) :
      Integrable (fun t : ι → ℝ ↦ (c j * c k) * ∏ i, ψ j i (t i) * ψ k i (t i))
        (Measure.pi (fun _ : ι ↦ volume.restrict (Set.Ioi 0 : Set ℝ))) :=
    (Integrable.fintype_prod fun i ↦ hint j hj k hk i).const_mul (c j * c k)
  have hid (t : ι → ℝ) : (∑ j ∈ S, c j * ∏ i, ψ j i (t i)) ^ 2 =
      ∑ j ∈ S, ∑ k ∈ S, (c j * c k) * ∏ i, ψ j i (t i) * ψ k i (t i) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.prod_mul_distrib]
    ring
  change (∫ t : ι → ℝ, _ ∂((Measure.pi fun _ : ι ↦ (volume : Measure ℝ)).restrict
    (Set.univ.pi (fun _ ↦ Set.Ioi 0)))) = _
  rw [Measure.restrict_pi_pi]
  simp_rw [hid]
  rw [integral_finsetSum S (fun j hj ↦ integrable_finsetSum S fun k hk ↦ hi j hj k hk)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum S (fun k hk ↦ hi j hj k hk)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (fun i t ↦ ψ j i t * ψ k i t)

theorem sourceTensorEnergy_eq_pair_sum {ι J : Type*} [Fintype ι]
    (S : Finset J) (ψ : J → ι → ℝ → ℝ)
    (hint : ∀ j ∈ S, ∀ k ∈ S, ∀ i,
      IntegrableOn (fun t ↦ ψ j i t * ψ k i t) (Set.Ioi 0)) :
    sourceTensorEnergy S ψ = ∑ j ∈ S, ∑ k ∈ S, ∏ i,
      ∫ t : ℝ in Set.Ioi 0, ψ j i t * ψ k i t := by
  simpa only [sourceTensorEnergy, sourceTensorValue, one_mul] using
    integral_weighted_real_tensor_square S (fun _ ↦ 1) ψ hint

theorem sourceTensorFaceEnergy_eq_pair_sum {K : ℕ} {J : Type*}
    (S : Finset J) (ψ : J → Fin K → ℝ → ℝ)
    (hint : ∀ j ∈ S, ∀ k ∈ S, ∀ i,
      IntegrableOn (fun t ↦ ψ j i t * ψ k i t) (Set.Ioi 0)) (h : Fin K) :
    sourceTensorFaceEnergy S ψ h = ∑ j ∈ S, ∑ k ∈ S,
      ((∫ t : ℝ in Set.Ioi 0, ψ j h t) * (∫ t : ℝ in Set.Ioi 0, ψ k h t)) *
        ∏ i : PinnedShiftIndex h, ∫ t : ℝ in Set.Ioi 0, ψ j i.val t * ψ k i.val t :=
  integral_weighted_real_tensor_square S (fun j ↦ ∫ t : ℝ in Set.Ioi 0, ψ j h t)
    (fun j (i : PinnedShiftIndex h) ↦ ψ j i.val) (fun j hj k hk i ↦ hint j hj k hk i.val)

theorem tendsto_sourceTensorEnergy_of_pair {ι J : Type*} [Fintype ι]
    (S : Finset J) (ψ : ℕ → J → ι → ℝ → ℝ) (φ : J → ι → ℝ → ℝ)
    (hψ : ∀ n j, j ∈ S → ∀ k ∈ S, ∀ i,
      IntegrableOn (fun t ↦ ψ n j i t * ψ n k i t) (Set.Ioi 0))
    (hφ : ∀ j ∈ S, ∀ k ∈ S, ∀ i,
      IntegrableOn (fun t ↦ φ j i t * φ k i t) (Set.Ioi 0))
    (hlim : ∀ j ∈ S, ∀ k ∈ S, ∀ i,
      Tendsto (fun n ↦ ∫ t : ℝ in Set.Ioi 0, ψ n j i t * ψ n k i t) atTop
        (𝓝 (∫ t : ℝ in Set.Ioi 0, φ j i t * φ k i t))) :
    Tendsto (fun n ↦ sourceTensorEnergy S (ψ n)) atTop (𝓝 (sourceTensorEnergy S φ)) := by
  simp_rw [sourceTensorEnergy_eq_pair_sum S _ (hψ _), sourceTensorEnergy_eq_pair_sum S φ hφ]
  apply tendsto_finsetSum S
  intro j hj
  apply tendsto_finsetSum S
  intro k hk
  exact tendsto_finsetProd _ fun i _ ↦ hlim j hj k hk i

theorem tendsto_sourceTensorFaceEnergy_of_pair {K : ℕ} {J : Type*}
    (S : Finset J) (ψ : ℕ → J → Fin K → ℝ → ℝ) (φ : J → Fin K → ℝ → ℝ)
    (hψ : ∀ n j, j ∈ S → ∀ k ∈ S, ∀ i,
      IntegrableOn (fun t ↦ ψ n j i t * ψ n k i t) (Set.Ioi 0))
    (hφ : ∀ j ∈ S, ∀ k ∈ S, ∀ i,
      IntegrableOn (fun t ↦ φ j i t * φ k i t) (Set.Ioi 0))
    (hlim : ∀ j ∈ S, ∀ k ∈ S, ∀ i,
      Tendsto (fun n ↦ ∫ t : ℝ in Set.Ioi 0, ψ n j i t * ψ n k i t) atTop
        (𝓝 (∫ t : ℝ in Set.Ioi 0, φ j i t * φ k i t)))
    (hmass : ∀ j ∈ S, ∀ i,
      Tendsto (fun n ↦ ∫ t : ℝ in Set.Ioi 0, ψ n j i t) atTop
        (𝓝 (∫ t : ℝ in Set.Ioi 0, φ j i t))) (h : Fin K) :
    Tendsto (fun n ↦ sourceTensorFaceEnergy S (ψ n) h) atTop
      (𝓝 (sourceTensorFaceEnergy S φ h)) := by
  simp_rw [sourceTensorFaceEnergy_eq_pair_sum S _ (hψ _) h,
    sourceTensorFaceEnergy_eq_pair_sum S φ hφ h]
  apply tendsto_finsetSum S
  intro j hj
  apply tendsto_finsetSum S
  intro k hk
  exact ((hmass j hj h).mul (hmass k hk h)).mul
    (tendsto_finsetProd _ fun i _ ↦ hlim j hj k hk i.val)

end

end Erdos4b
