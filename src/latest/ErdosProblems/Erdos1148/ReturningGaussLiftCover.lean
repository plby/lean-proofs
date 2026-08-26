import ErdosProblems.Erdos1148.ReturningGaussGrid
import ErdosProblems.Erdos1148.GaussLiftBoxes

/-! # Returning frames have compact forward lift covers of size exp(S/2) -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_returningGauss_lift_cover {A c δ : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : SL(2, ℝ)), (∀ i j : Fin 2, |g i j| ≤ A) →
      ∀ S : ℝ, 0 ≤ S → 96 * Real.exp (-S) ≤ c →
        ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
          (N : ℝ) ≤ K * Real.exp (S / 2) ∧ (∀ i, IsCompact (B i)) ∧
          gaussParameterFrame g '' ReturningGaussParameters g S c ⊆ ⋃ i, B i ∧
          ∀ i, LiftForwardClose (8 * δ) S (B i) := by
  obtain ⟨K, hK, hgrid⟩ := exists_returningGauss_unstable_grid hA hc hδ
  obtain ⟨Nx, b, _, _, hxcov⟩ := exists_real_interval_grid
    (a := (-1 : ℝ)) (b := 1) (by norm_num) hδ
  obtain ⟨Nh, c₀, _, _, hhcov⟩ := exists_real_interval_grid
    (a := (1 / 2 : ℝ)) (b := 2) (by norm_num) hδ
  refine ⟨K * ((Nx : ℝ) + 1) * ((Nh : ℝ) + 1), by positivity, ?_⟩
  intro g hg S hS hsmall
  obtain ⟨Nr, a, hNr, hrcov⟩ := hgrid g hg S hS hsmall
  let ι := Fin Nr × Fin Nx × Fin Nh
  let B : ι → Set SL(2, ℝ) := fun i =>
    gaussLiftBox g (a i.1) (b i.2.1) (c₀ i.2.2) (δ * Real.exp (-S)) δ δ
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => B (e.symm i), ?_, ?_, ?_, ?_⟩
  · have hprod : (Nx : ℝ) * Nh ≤ ((Nx : ℝ) + 1) * ((Nh : ℝ) + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) Nx, Nat.cast_nonneg (α := ℝ) Nh]
    have hbound := mul_le_mul hNr hprod
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity)
    change (Fintype.card (Fin Nr × Fin Nx × Fin Nh) : ℝ) ≤ _
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ (K * Real.exp (S / 2)) * (((Nx : ℝ) + 1) * ((Nh : ℝ) + 1)) := hbound
      _ = _ := by ring
  · intro i
    exact isCompact_gaussLiftBox _ _ _ _ _ _ _
  · rintro x ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := hrcov p hp
    obtain ⟨j, hj⟩ := hxcov p.val.2.1 (abs_le.mp p.property.2.1)
    obtain ⟨k, hk⟩ := hhcov p.val.2.2 ⟨p.property.2.2.1, p.property.2.2.2⟩
    refine Set.mem_iUnion.mpr ⟨e (i, j, k), ?_⟩
    have he : e.symm (e (i, j, k)) = (i, j, k) := e.symm_apply_apply _
    rw [he]
    exact ⟨p, ⟨hi, hj, hk⟩, rfl⟩
  · intro i
    exact gaussLiftBox_forward_close g _ _ _ hδ.le hS

end Erdos1148.DukeArithmetic
