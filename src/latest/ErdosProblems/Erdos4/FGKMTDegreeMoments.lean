import ErdosProblems.Erdos4.FGKMTRawDegree

/-!
# Degree concentration from the aggregate incidence law

The first absolute moment is estimated before conditioning. Conditioning
on a test set then costs only the reciprocal of its survival probability.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

noncomputable def degreeVariance (r : ℕ) (κ δ ε D : ℝ) : ℝ :=
  3 * D ^ 2 * ε + (1 + ε) * (r : ℝ) * δ * D / κ ^ (r + 1)

theorem degreeVariance_nonneg (r : ℕ) {κ δ ε D : ℝ}
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hD : 0 ≤ D) :
    0 ≤ degreeVariance r κ δ ε D := by
  unfold degreeVariance
  positivity

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

theorem scaled_incidence_variance (ν : FiniteLaw (Finset V))
    (μ : I → FiniteLaw (Finset V)) (p : V → ℝ) (v : V)
    {r : ℕ} {κ δ ε D : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hp : ∀ v, κ ≤ p v) (hsize : ∀ i e, 0 < (μ i).weight e → e.card ≤ r)
    (hd : 0 < vertexDegree μ v) (hD : vertexDegree μ v / p v ≤ D)
    (hpair : ∀ w, w ≠ v → pairDegree μ v w ≤ δ)
    (hacc : SurvivalAccurate ν p (2 * r) ε) :
    ν.mean (fun W => ((vertexDegree μ v / p v) *
        (normalizer (erasedIncidence μ v) p W - 1)) ^ 2) ≤ degreeVariance r κ δ ε D := by
  have hpv : 0 < p v := hκ0.trans_le (hp v)
  have hm0 : 0 ≤ vertexDegree μ v / p v := div_nonneg hd.le hpv.le
  have hD0 : 0 ≤ D := hm0.trans hD
  have hmoment := normalizer_mean_sq_error ν (erasedIncidence μ v) p hκ0 hκ1
    (div_nonneg hδ hd.le) hε hp (erasedIncidence_size μ v hd hsize)
    (erasedIncidence_sparse μ v hd hδ hpair) hacc
  have hscalar :
      (vertexDegree μ v / p v) ^ 2 *
        (3 * ε + (1 + ε) * (r : ℝ) * (δ / vertexDegree μ v) / κ ^ r) =
      3 * (vertexDegree μ v / p v) ^ 2 * ε +
        (1 + ε) * (r : ℝ) * δ * (vertexDegree μ v / p v) / (p v * κ ^ r) := by
    field_simp
    <;> ring
  have hfirst : 3 * (vertexDegree μ v / p v) ^ 2 * ε ≤ 3 * D ^ 2 * ε := by
    have hh := pow_le_pow_left₀ hm0 hD 2
    nlinarith
  have hsecond :
      (1 + ε) * (r : ℝ) * δ * (vertexDegree μ v / p v) / (p v * κ ^ r) ≤
        (1 + ε) * (r : ℝ) * δ * D / κ ^ (r + 1) := by
    calc
      _ ≤ (1 + ε) * (r : ℝ) * δ * D / (p v * κ ^ r) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hD (by positivity)) (by positivity)
      _ ≤ (1 + ε) * (r : ℝ) * δ * D / (κ * κ ^ r) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right (hp v) (pow_pos hκ0 r).le)
      _ = _ := by rw [pow_succ]; ring
  calc
    _ = (vertexDegree μ v / p v) ^ 2 *
        ν.mean (fun W => (normalizer (erasedIncidence μ v) p W - 1) ^ 2) := by
      simp only [mul_pow, FiniteLaw.mean_const_mul]
    _ ≤ (vertexDegree μ v / p v) ^ 2 *
        (3 * ε + (1 + ε) * (r : ℝ) * (δ / vertexDegree μ v) / κ ^ r) :=
      mul_le_mul_of_nonneg_left hmoment (sq_nonneg _)
    _ = _ := hscalar
    _ ≤ degreeVariance r κ δ ε D := add_le_add hfirst hsecond

theorem conditioned_degree_error (ν : FiniteLaw (Finset V))
    (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    {r A : ℕ} {κ δ ε D : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hδ : 0 ≤ δ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (hD0 : 0 ≤ D)
    (hp : ∀ v, κ ≤ p v) (hsize : ∀ i e, 0 < (μ i).weight e → e.card ≤ r)
    (hacc : SurvivalAccurate ν p A ε) (hrA : 2 * r ≤ A)
    (T : Finset V) (hT : T.card ≤ A) (v : V) (hvT : v ∈ T)
    (hD : vertexDegree μ v / p v ≤ D)
    (hpair : ∀ w, w ≠ v → pairDegree μ v w ≤ δ) :
    (conditionSurvival ν T).mean (fun W => |rawDegree μ p W v - vertexDegree μ v / p v|) ≤
      2 * Real.sqrt (degreeVariance r κ δ ε D) / κ ^ A := by
  have hp0 : ∀ v, 0 < p v := fun v => hκ0.trans_le (hp v)
  by_cases hd0 : vertexDegree μ v = 0
  · have hz : (conditionSurvival ν T).mean
        (fun W => |rawDegree μ p W v - vertexDegree μ v / p v|) = 0 := by
      simp only [rawDegree_zero μ p hκ0 hκ1 hp hsize v hd0, hd0, zero_div,
        sub_self, abs_zero, FiniteLaw.mean_const]
    rw [hz]
    positivity
  · have hd : 0 < vertexDegree μ v :=
      lt_of_le_of_ne (vertexDegree_nonneg μ v) (Ne.symm hd0)
    have hvar := scaled_incidence_variance ν μ p v hκ0 hκ1 hδ hε0 hp hsize hd hD hpair
      (fun e he => hacc e (he.trans hrA))
    have habs := ν.mean_abs_le_sqrt
      (fun W => (vertexDegree μ v / p v) * (normalizer (erasedIncidence μ v) p W - 1)) hvar
    have hbound := conditioned_error_le ν p hκ0 hκ1 hε1 hp hacc T hT
      (fun W => |(vertexDegree μ v / p v) * (normalizer (erasedIncidence μ v) p W - 1)|)
      (fun W => abs_nonneg _) habs
    have hTpos := survival_pos_of_accurate ν p hp0 (by linarith : ε < 1) hacc hT
    have heq : (conditionSurvival ν T).mean
        (fun W => |rawDegree μ p W v - vertexDegree μ v / p v|) =
        (conditionSurvival ν T).mean (fun W =>
          |(vertexDegree μ v / p v) * (normalizer (erasedIncidence μ v) p W - 1)|) := by
      apply (conditionSurvival ν T).mean_congr_support
      intro W hW
      have hvW := conditionSurvival_support ν T W (ne_of_gt hTpos) hW hvT
      rw [rawDegree_eq_incidence μ p hp0 W v hvW hd0]
      congr 1
      ring
    rw [heq]
    exact hbound

end Erdos4.FGKMT
