/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTNormalizerMoments

/-! # Explicit normalizer moment and tail bounds for the covering induction -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ] [DecidableEq α]

theorem reweightNormalizer_mean_error (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    (hP : ∀ v ∈ F.vertices, 0 < P v) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (i : I) {η : ℝ}
    (hcont : ∀ w, |containmentMass ρ W (F.edge i w) - survivalProduct P (F.edge i w)| ≤
      η * survivalProduct P (F.edge i w)) :
    |(∑ s, ρ s * F.reweightNormalizer P (W s) i) - 1| ≤ η := by
  have hrel (w : Ω) :
      |containmentMass ρ W (F.edge i w) / survivalProduct P (F.edge i w) - 1| ≤ η := by
    have hp := survivalProduct_pos (fun v hv => hP v (F.edge_subset i w hv))
    rw [div_sub_one hp.ne', abs_div, abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr (hcont w)
  have heq : (∑ s, ρ s * F.reweightNormalizer P (W s) i) - 1 =
      ∑ w, F.mass i w *
        (containmentMass ρ W (F.edge i w) / survivalProduct P (F.edge i w) - 1) := by
    conv_lhs => rw [F.reweightNormalizer_mean, ← F.mass_sum_one i, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _hw => by ring
  rw [heq]
  calc
    _ ≤ ∑ w, |F.mass i w *
        (containmentMass ρ W (F.edge i w) / survivalProduct P (F.edge i w) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w, F.mass i w * η := by
      apply Finset.sum_le_sum
      intro w _hw
      rw [abs_mul, abs_of_nonneg (F.mass_nonneg i w)]
      exact mul_le_mul_of_nonneg_left (hrel w) (F.mass_nonneg i w)
    _ = η := by rw [← Finset.sum_mul, F.mass_sum_one, one_mul]

theorem reweightNormalizer_second_le_intersection (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} (hP : ∀ v ∈ F.vertices, 0 < P v)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (i : I) {η : ℝ}
    (hcont : ∀ w z, containmentMass ρ W (F.edge i w ∪ F.edge i z) ≤
      (1 + η) * survivalProduct P (F.edge i w ∪ F.edge i z)) :
    (∑ s, ρ s * F.reweightNormalizer P (W s) i ^ 2) ≤
      (1 + η) * ∑ w, ∑ z,
        F.mass i w * F.mass i z / survivalProduct P (F.edge i w ∩ F.edge i z) := by
  rw [F.reweightNormalizer_second_moment]
  calc
    _ ≤ ∑ w, ∑ z, F.mass i w * F.mass i z /
        (survivalProduct P (F.edge i w) * survivalProduct P (F.edge i z)) *
        ((1 + η) * survivalProduct P (F.edge i w ∪ F.edge i z)) := by
      apply Finset.sum_le_sum
      intro w _hw
      apply Finset.sum_le_sum
      intro z _hz
      have hw := survivalProduct_pos (fun v hv => hP v (F.edge_subset i w hv))
      have hz := survivalProduct_pos (fun v hv => hP v (F.edge_subset i z hv))
      exact mul_le_mul_of_nonneg_left (hcont w z)
        (div_nonneg (mul_nonneg (F.mass_nonneg i w) (F.mass_nonneg i z))
          (mul_pos hw hz).le)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _hw
      apply Finset.sum_congr rfl
      intro z _hz
      have hratio := survivalProduct_union_ratio hP (F.edge_subset i w) (F.edge_subset i z)
      calc
        _ = (1 + η) * (F.mass i w * F.mass i z) *
            (survivalProduct P (F.edge i w ∪ F.edge i z) /
              (survivalProduct P (F.edge i w) * survivalProduct P (F.edge i z))) := by ring
        _ = _ := by rw [hratio]; ring

omit [Fintype Ξ] in
theorem independent_inverse_intersection_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ b : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (i : I) (hb : 0 ≤ b)
    (hcap : ∀ v ∈ F.vertices, F.vertexMass i v ≤ b) :
    (∑ w, ∑ z, F.mass i w * F.mass i z /
      survivalProduct P (F.edge i w ∩ F.edge i z)) ≤
      1 + (1 / κ ^ F.rank) * ((F.rank : ℝ) * b) := by
  have hcoef (w z : Ω) : 0 ≤ F.mass i w * F.mass i z :=
    mul_nonneg (F.mass_nonneg i w) (F.mass_nonneg i z)
  calc
    _ ≤ ∑ w, ∑ z, (F.mass i w * F.mass i z) *
        (1 + if (F.edge i w ∩ F.edge i z).Nonempty then 1 / κ ^ F.rank else 0) := by
      apply Finset.sum_le_sum
      intro w _hw
      apply Finset.sum_le_sum
      intro z _hz
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (survivalProduct_inter_inv_le (B := F.edge i z) hκ0 hκ1 hP
          (F.edge_subset i w) (F.edge_card_le i w)) (hcoef w z)
    _ = 1 + (1 / κ ^ F.rank) * F.independentIntersectionMass i i := by
      rw [F.independentIntersectionMass_eq]
      simp only [mul_add, mul_one, mul_ite, mul_zero, Finset.sum_add_distrib]
      rw [F.independent_pair_mass_sum]
      congr 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _hw
      apply Finset.sum_congr rfl
      intro z _hz
      split_ifs <;> ring
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (F.independentIntersectionMass_le_rank_mul i i hb hcap)
        (one_div_nonneg.mpr (pow_pos hκ0 F.rank).le))

theorem reweightNormalizer_second_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ b η : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (i : I) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hcap : ∀ v ∈ F.vertices, F.vertexMass i v ≤ b)
    (hcont : ∀ w z, containmentMass ρ W (F.edge i w ∪ F.edge i z) ≤
      (1 + η) * survivalProduct P (F.edge i w ∪ F.edge i z)) :
    (∑ s, ρ s * F.reweightNormalizer P (W s) i ^ 2) ≤
      (1 + η) * (1 + (1 / κ ^ F.rank) * ((F.rank : ℝ) * b)) := by
  exact (F.reweightNormalizer_second_le_intersection
    (fun v hv => hκ0.trans_le (hP v hv)) ρ W i hcont).trans
    (mul_le_mul_of_nonneg_left (F.independent_inverse_intersection_le hκ0 hκ1 hP i hb hcap)
      (by linarith))

theorem reweightNormalizer_centered_second_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ b η : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (hρsum : ∑ s, ρ s = 1) (i : I) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hcap : ∀ v ∈ F.vertices, F.vertexMass i v ≤ b)
    (hfirst : ∀ w, |containmentMass ρ W (F.edge i w) - survivalProduct P (F.edge i w)| ≤
      η * survivalProduct P (F.edge i w))
    (hsecond : ∀ w z, containmentMass ρ W (F.edge i w ∪ F.edge i z) ≤
      (1 + η) * survivalProduct P (F.edge i w ∪ F.edge i z)) :
    (∑ s, ρ s * (F.reweightNormalizer P (W s) i - 1) ^ 2) ≤
      3 * η + (1 + η) * (1 / κ ^ F.rank) * ((F.rank : ℝ) * b) := by
  have hm := F.reweightNormalizer_mean_error
    (fun v hv => hκ0.trans_le (hP v hv)) ρ W i hfirst
  have hs := F.reweightNormalizer_second_le hκ0 hκ1 hP ρ W i hb hη hcap hsecond
  have h := finite_approx_mean_variance_bound ρ
    (fun s => F.reweightNormalizer P (W s) i) hρsum (s := 1) (by norm_num)
    (e := η) (d := (1 + η) * (1 / κ ^ F.rank) * ((F.rank : ℝ) * b))
    (by simpa only [mul_one] using hm) (by nlinarith [hs])
  simpa only [one_pow, mul_one] using h

theorem reweightNormalizer_tail_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ b η τ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (hρ0 : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (i : I) (hb : 0 ≤ b) (hη : 0 ≤ η) (hτ : 0 < τ)
    (hcap : ∀ v ∈ F.vertices, F.vertexMass i v ≤ b)
    (hfirst : ∀ w, |containmentMass ρ W (F.edge i w) - survivalProduct P (F.edge i w)| ≤
      η * survivalProduct P (F.edge i w))
    (hsecond : ∀ w z, containmentMass ρ W (F.edge i w ∪ F.edge i z) ≤
      (1 + η) * survivalProduct P (F.edge i w ∪ F.edge i z)) :
    (∑ s, if τ ≤ |F.reweightNormalizer P (W s) i - 1| then ρ s else 0) ≤
      (3 * η + (1 + η) * (1 / κ ^ F.rank) * ((F.rank : ℝ) * b)) / τ ^ 2 := by
  exact (finite_square_tail_le ρ (fun s => F.reweightNormalizer P (W s) i) hρ0 1 hτ).trans
    (div_le_div_of_nonneg_right
      (F.reweightNormalizer_centered_second_le hκ0 hκ1 hP ρ W hρsum i hb hη hcap hfirst hsecond)
      (sq_nonneg _))

end

end Erdos4b.FGKMT.FiniteEdgeFamily
