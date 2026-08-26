import ErdosProblems.Erdos1148.ReturningGaussParameters
import ErdosProblems.Erdos1148.DiameterIntervalGrid

/-! # An exp(S/2) interval cover of the unstable parameters of returning vectors -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma returning_grid_count_bound {c δ S : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hS : 0 ≤ S) :
    2 * ((16 / Real.sqrt c) * Real.exp (-(S / 2))) / (δ * Real.exp (-S)) + 1 ≤
      (32 / (Real.sqrt c * δ) + 1) * Real.exp (S / 2) := by
  have hexp : Real.exp (-(S / 2)) = Real.exp (S / 2) * Real.exp (-S) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heq : 2 * ((16 / Real.sqrt c) * Real.exp (-(S / 2))) / (δ * Real.exp (-S)) =
      (32 / (Real.sqrt c * δ)) * Real.exp (S / 2) := by
    rw [hexp]
    field_simp
    <;> ring
  rw [heq]
  have h1 : 1 ≤ Real.exp (S / 2) := Real.one_le_exp_iff.mpr (by linarith)
  nlinarith

theorem exists_returningGauss_unstable_grid_from_candidates {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (V : Finset (ℤ × ℤ)) (g : SL(2, ℝ))
    (hV : ∀ (S c : ℝ) (p : BoundedGaussParameters) (q : ℤ × ℤ),
      GaussVectorReturns g S c q p → q ∈ V) {S : ℝ}
    (hS : 0 ≤ S) (hsmall : 96 * Real.exp (-S) ≤ c) :
    ∃ (N : ℕ) (a : Fin N → ℝ),
      (N : ℝ) ≤ ((V.card : ℝ) + 1) * (32 / (Real.sqrt c * δ) + 1) * Real.exp (S / 2) ∧
      ∀ p ∈ ReturningGaussParameters g S c, ∃ i : Fin N,
        p.val.1 ∈ Set.Icc (a i) (a i + δ * Real.exp (-S)) := by
  classical
  let F : ℝ := 32 / (Real.sqrt c * δ) + 1
  have hF : 0 < F := by dsimp [F]; positivity
  let E : V → Set ℝ := fun q => {r | ∃ p : BoundedGaussParameters,
    p.val.1 = r ∧ GaussVectorReturns g S c q.val p}
  have hgrid (q : V) : ∃ (N : ℕ) (a : Fin N → ℝ),
      (N : ℝ) ≤ F * Real.exp (S / 2) ∧ ∀ r ∈ E q,
        ∃ i : Fin N, r ∈ Set.Icc (a i) (a i + δ * Real.exp (-S)) := by
    have hdiam : ∀ r ∈ E q, ∀ s ∈ E q,
        |r - s| ≤ (16 / Real.sqrt c) * Real.exp (-(S / 2)) := by
      rintro r ⟨p, rfl, hp⟩ s ⟨p', rfl, hp'⟩
      exact returningGauss_parameter_diameter g hc hsmall q.val hp hp'
    obtain ⟨N, a, hN, hcover⟩ := exists_diameter_interval_grid
      (by positivity : 0 ≤ (16 / Real.sqrt c) * Real.exp (-(S / 2)))
      (mul_pos hδ (Real.exp_pos (-S))) hdiam
    exact ⟨N, a, hN.trans (returning_grid_count_bound hc hδ hS), hcover⟩
  choose N a hN hcover using hgrid
  let ι := (q : V) × Fin (N q)
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => a (e.symm i).1 (e.symm i).2, ?_, ?_⟩
  · have hcard : (Fintype.card ι : ℝ) = ∑ q : V, (N q : ℝ) := by
      simp only [ι, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    rw [hcard]
    calc
      _ ≤ ∑ _q : V, F * Real.exp (S / 2) := Finset.sum_le_sum (fun q _ => hN q)
      _ = (V.card : ℝ) * (F * Real.exp (S / 2)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ _ := by nlinarith [mul_pos hF (Real.exp_pos (S / 2))]
  · rintro p ⟨q, hq⟩
    let q' : V := ⟨q, hV S c p q hq⟩
    obtain ⟨i, hi⟩ := hcover q' p.val.1 ⟨p, rfl, hq⟩
    refine ⟨e ⟨q', i⟩, ?_⟩
    have he : e.symm (e ⟨q', i⟩) = ⟨q', i⟩ := e.symm_apply_apply _
    dsimp only
    rw [he]
    exact hi

theorem exists_returningGauss_unstable_grid {A c δ : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : SL(2, ℝ)), (∀ i j : Fin 2, |g i j| ≤ A) →
      ∀ S : ℝ, 0 ≤ S → 96 * Real.exp (-S) ≤ c →
        ∃ (N : ℕ) (a : Fin N → ℝ), (N : ℝ) ≤ K * Real.exp (S / 2) ∧
          ∀ p ∈ ReturningGaussParameters g S c, ∃ i : Fin N,
            p.val.1 ∈ Set.Icc (a i) (a i + δ * Real.exp (-S)) := by
  obtain ⟨V, hV⟩ := exists_uniform_returningGauss_candidates hA
  refine ⟨((V.card : ℝ) + 1) * (32 / (Real.sqrt c * δ) + 1), by positivity, ?_⟩
  intro g hg S hS hsmall
  exact exists_returningGauss_unstable_grid_from_candidates hc hδ V g (hV g hg) hS hsmall

end Erdos1148.DukeArithmetic
