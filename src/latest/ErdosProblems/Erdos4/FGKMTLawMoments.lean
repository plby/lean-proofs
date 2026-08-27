import ErdosProblems.Erdos4.FGKMTNormalizerMoments

/-! Finite first-absolute-moment estimates, with no measure-theoretic input. -/

namespace Erdos4.FGKMT.FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem mean_sq_sub (ν : FiniteLaw Ω) (f : Ω → ℝ) (a : ℝ) :
    ν.mean (fun o => (f o - a) ^ 2) =
      ν.mean (fun o => f o ^ 2) - 2 * a * ν.mean f + a ^ 2 := by
  have heq : (fun o => (f o - a) ^ 2) =
      (fun o => (f o ^ 2 - (2 * a) * f o) + a ^ 2) := by
    funext o
    ring
  rw [heq, mean_add, mean_sub, mean_const_mul, mean_const]

theorem mean_sq_ge_sq_mean (ν : FiniteLaw Ω) (f : Ω → ℝ) :
    ν.mean f ^ 2 ≤ ν.mean (fun o => f o ^ 2) := by
  have hh := ν.mean_nonneg (fun o => sq_nonneg (f o - ν.mean f))
  rw [mean_sq_sub] at hh
  nlinarith

theorem mean_abs_sq_le (ν : FiniteLaw Ω) (f : Ω → ℝ) :
    ν.mean (fun o => |f o|) ^ 2 ≤ ν.mean (fun o => f o ^ 2) := by
  simpa only [sq_abs] using ν.mean_sq_ge_sq_mean (fun o => |f o|)

theorem mean_abs_le_of_sq (ν : FiniteLaw Ω) (f : Ω → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hsq : ν.mean (fun o => f o ^ 2) ≤ b ^ 2) : ν.mean (fun o => |f o|) ≤ b := by
  have hsq' := (ν.mean_abs_sq_le f).trans hsq
  have hn := ν.mean_nonneg (fun o => abs_nonneg (f o))
  nlinarith

theorem mean_abs_le_sqrt (ν : FiniteLaw Ω) (f : Ω → ℝ) {b : ℝ}
    (hsq : ν.mean (fun o => f o ^ 2) ≤ b) : ν.mean (fun o => |f o|) ≤ Real.sqrt b := by
  have hb : 0 ≤ b := (ν.mean_nonneg (fun o => sq_nonneg (f o))).trans hsq
  apply ν.mean_abs_le_of_sq f (Real.sqrt_nonneg b)
  simpa only [Real.sq_sqrt hb] using hsq

end Erdos4.FGKMT.FiniteLaw

namespace Erdos4.FGKMT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem normalizer_mean_sq_error (ν μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {r : ℕ} {κ δ ε : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hp : ∀ v, κ ≤ p v) (hsize : ∀ e, 0 < μ.weight e → e.card ≤ r)
    (hsparse : ∀ v : V, μ.prob (fun f => v ∈ f) ≤ δ)
    (hacc : SurvivalAccurate ν p (2 * r) ε) :
    ν.mean (fun W => (normalizer μ p W - 1) ^ 2) ≤
      3 * ε + (1 + ε) * (r : ℝ) * δ / κ ^ r := by
  rw [FiniteLaw.mean_sq_sub_one]
  have hfirst := normalizer_first_moment ν μ p hsize
    (fun e he => hacc e (by omega))
  have hsecond := normalizer_second_moment ν μ p hκ0 hκ1 hδ hε hp hsize hsparse hacc
  have hsecond' := hsecond.trans_eq
    (show (1 + ε) * (1 + (r : ℝ) * δ / κ ^ r) =
      1 + ε + (1 + ε) * (r : ℝ) * δ / κ ^ r by ring)
  have hh := (abs_le.mp hfirst).1
  linarith

end Erdos4.FGKMT
