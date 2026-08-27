import ErdosProblems.Erdos587.HooleyHyperplaneCount

/-! # A finite box-density criterion for full real linear span -/

open scoped BigOperators
open Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem delta_span_eq_top_of_box_density {d : ℕ} (A : Finset (Fin d → ℤ))
    (R : Fin d → ℕ) (W : ℕ) (hW : ∀ i, W ≤ 2 * R i + 1)
    (hbox : ∀ v ∈ A, ∀ i, (v i).natAbs ≤ R i)
    (hdense : (∏ i, (2 * R i + 1)) < W * A.card) :
    Submodule.span ℝ (intCastVec '' (A : Set (Fin d → ℤ))) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨ℓ, hℓ, hker⟩ :=
    (Submodule.span ℝ (intCastVec '' (A : Set (Fin d → ℤ)))).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hspan)
  let a : Fin d → ℝ := fun i => ℓ (Pi.single i 1)
  have heval (x : Fin d → ℝ) : ℓ x = ∑ i, a i * x i := by
    calc
      _ = ℓ (∑ i, x i • Pi.single i (1 : ℝ)) := congrArg ℓ (pi_eq_sum_univ' x)
      _ = ∑ i, x i * ℓ (Pi.single i 1) := by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
  have hane : ∃ j, a j ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hℓ
    apply LinearMap.ext
    intro x
    change ℓ x = 0
    rw [heval]
    simp only [hn, zero_mul, Finset.sum_const_zero]
  obtain ⟨j, haj⟩ := hane
  have hplane : ∀ v ∈ A, (∑ i, a i * (v i : ℝ)) = 0 := by
    intro v hv
    have hmem : intCastVec v ∈ Submodule.span ℝ (intCastVec '' (A : Set (Fin d → ℤ))) :=
      Submodule.subset_span ⟨v, hv, rfl⟩
    have hz : ℓ (intCastVec v) = 0 := hker hmem
    rw [heval] at hz
    exact hz
  have hcount := delta_hyperplane_card_bound A R a j haj hbox hplane
  have hh := (Nat.mul_le_mul_right A.card (hW j)).trans hcount
  exact (not_lt_of_ge hh) hdense

end Erdos587.CFP
