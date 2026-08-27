import ErdosProblems.Erdos4.FGKMTReweighting

/-!
# Concentration of the reweighting normalizer

Joint survival accuracy up to twice the maximum edge size controls the
first moment. A sparse vertex marginal bounds the contribution of
intersecting edge pairs to the second moment. No uniform edge-size
hypothesis is imposed.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem meeting_prob_le (μ : FiniteLaw (Finset V)) (e : Finset V) {δ : ℝ}
    (hsparse : ∀ v : V, μ.prob (fun f => v ∈ f) ≤ δ) :
    μ.prob (fun f => ¬Disjoint e f) ≤ (e.card : ℝ) * δ := by
  calc
    _ ≤ μ.prob (fun f => ∃ v ∈ e, v ∈ f) := μ.prob_mono (fun f hf => by
      obtain ⟨v, hv, hvf⟩ := Finset.not_disjoint_iff.mp hf
      exact ⟨v, hv, hvf⟩)
    _ ≤ ∑ v ∈ e, μ.prob (fun f => v ∈ f) := μ.prob_exists_finset_le e (fun v f => v ∈ f)
    _ ≤ ∑ _v ∈ e, δ := Finset.sum_le_sum (fun v _hv => hsparse v)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

open Classical in
theorem inverse_intersection_le (p : V → ℝ) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hp : ∀ v, κ ≤ p v) {e f : Finset V} {r : ℕ} (he : e.card ≤ r) :
    1 / setProduct p (e ∩ f) ≤
      1 + (1 / κ ^ r) * (if ¬Disjoint e f then 1 else 0) := by
  by_cases hd : Disjoint e f
  · rw [Finset.disjoint_iff_inter_eq_empty.mp hd, setProduct_empty]
    simp [hd]
  · rw [if_pos hd, mul_one]
    have hcard : (e ∩ f).card ≤ r := (Finset.card_le_card Finset.inter_subset_left).trans he
    have hh := setProduct_lower p hκ0.le hκ1 hp hcard
    exact (one_div_le_one_div_of_le (pow_pos hκ0 r) hh).trans (by linarith)

theorem mean_inverse_intersection_le (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {κ δ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    (hp : ∀ v, κ ≤ p v) (hsize : ∀ e, 0 < μ.weight e → e.card ≤ r)
    (hsparse : ∀ v : V, μ.prob (fun f => v ∈ f) ≤ δ) :
    μ.mean (fun e => μ.mean (fun f => 1 / setProduct p (e ∩ f))) ≤
      1 + (r : ℝ) * δ / κ ^ r := by
  classical
  calc
    _ ≤ μ.mean (fun _ => 1 + (r : ℝ) * δ / κ ^ r) := by
      apply μ.mean_mono_support
      intro e he
      have hcard := hsize e he
      have hmeeting : μ.prob (fun f => ¬Disjoint e f) ≤ (r : ℝ) * δ :=
        (meeting_prob_le μ e hsparse).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hδ)
      calc
        _ ≤ μ.mean (fun f => 1 + (1 / κ ^ r) * (if ¬Disjoint e f then 1 else 0)) :=
          μ.mean_mono (fun f => inverse_intersection_le p hκ0 hκ1 hp hcard)
        _ = 1 + (1 / κ ^ r) * μ.prob (fun f => ¬Disjoint e f) := by
          rw [FiniteLaw.mean_add, FiniteLaw.mean_const, FiniteLaw.mean_const_mul,
            ← FiniteLaw.prob_eq_mean]
        _ ≤ 1 + (1 / κ ^ r) * ((r : ℝ) * δ) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hmeeting (by positivity))
        _ = _ := by ring
    _ = _ := μ.mean_const _

theorem normalizer_first_moment (ν μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {r : ℕ} {ε : ℝ} (hsize : ∀ e, 0 < μ.weight e → e.card ≤ r)
    (hacc : SurvivalAccurate ν p r ε) : |ν.mean (normalizer μ p) - 1| ≤ ε := by
  rw [mean_normalizer]
  have heq : μ.mean (fun e => survival ν e / setProduct p e) - 1 =
      μ.mean (fun e => survival ν e / setProduct p e - 1) := by
    rw [FiniteLaw.mean_sub, FiniteLaw.mean_const]
  rw [heq]
  calc
    _ ≤ μ.mean (fun e => |survival ν e / setProduct p e - 1|) := μ.abs_mean_le _
    _ ≤ μ.mean (fun _ => ε) := μ.mean_mono_support (fun e he => hacc e (hsize e he))
    _ = _ := μ.mean_const ε

theorem normalizer_second_moment (ν μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {r : ℕ} {κ δ ε : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hp : ∀ v, κ ≤ p v) (hsize : ∀ e, 0 < μ.weight e → e.card ≤ r)
    (hsparse : ∀ v : V, μ.prob (fun f => v ∈ f) ≤ δ)
    (hacc : SurvivalAccurate ν p (2 * r) ε) :
    ν.mean (fun W => normalizer μ p W ^ 2) ≤ (1 + ε) * (1 + (r : ℝ) * δ / κ ^ r) := by
  have hp0 : ∀ v, 0 < p v := fun v => hκ0.trans_le (hp v)
  rw [mean_normalizer_sq]
  calc
    _ ≤ μ.mean (fun e => μ.mean (fun f => (1 + ε) / setProduct p (e ∩ f))) := by
      apply μ.mean_mono_support
      intro e he
      apply μ.mean_mono_support
      intro f hf
      have hcard : (e ∪ f).card ≤ 2 * r := by
        have hh := Finset.card_union_le e f
        have h₁ := hsize e he
        have h₂ := hsize f hf
        omega
      have hh := (abs_le.mp (hacc (e ∪ f) hcard)).2
      have hupper : survival ν (e ∪ f) / setProduct p (e ∪ f) ≤ 1 + ε := by linarith
      rw [union_denominator]
      exact div_le_div_of_nonneg_right hupper (setProduct_pos p hp0 (e ∩ f)).le
    _ = (1 + ε) * μ.mean (fun e => μ.mean (fun f => 1 / setProduct p (e ∩ f))) := by
      simp only [div_eq_mul_inv, one_mul, FiniteLaw.mean_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mean_inverse_intersection_le μ p hκ0 hκ1 hδ hp hsize hsparse) (by linarith)

/-- The finite quantitative form of the normalizer concentration step.
The threshold is arbitrary and positive; the covering induction will
choose it as a suitable fractional power of its error parameter. -/
theorem normalizer_concentration (ν μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {r : ℕ} {κ δ ε t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (ht : 0 < t) (hp : ∀ v, κ ≤ p v)
    (hsize : ∀ e, 0 < μ.weight e → e.card ≤ r)
    (hsparse : ∀ v : V, μ.prob (fun f => v ∈ f) ≤ δ)
    (hacc : SurvivalAccurate ν p (2 * r) ε) :
    ν.prob (fun W => t ≤ |normalizer μ p W - 1|) ≤
      (3 * ε + (1 + ε) * (r : ℝ) * δ / κ ^ r) / t ^ 2 := by
  have hfirst := normalizer_first_moment ν μ p hsize
    (fun e he => hacc e (by omega))
  have hsecond := normalizer_second_moment ν μ p hκ0 hκ1 hδ hε hp hsize hsparse hacc
  exact ν.normalizer_bad_mass_le (normalizer μ p) ht hfirst (hsecond.trans_eq (by ring))

end Erdos4.FGKMT
