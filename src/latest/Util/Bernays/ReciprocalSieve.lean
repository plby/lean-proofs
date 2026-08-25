import Util.Bernays.SquareEulerCorrection
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Finite-product and tail estimates for a convergent reciprocal sieve
-/

open Filter Topology

namespace Bernays

theorem exp_neg_two_sum_le_prod_one_sub {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha₀ : ∀ i ∈ S, 0 ≤ a i) (ha₁ : ∀ i ∈ S, a i ≤ 1 / 2) :
    Real.exp (-2 * ∑ i ∈ S, a i) ≤ ∏ i ∈ S, (1 - a i) := by
  have hpos : ∀ i ∈ S, 0 < 1 - a i := fun i hi => by linarith [ha₁ i hi]
  have hlog : -2 * ∑ i ∈ S, a i ≤ ∑ i ∈ S, Real.log (1 - a i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      linarith [(neg_log_one_sub_bound (ha₀ i hi) (ha₁ i hi)).2]
  calc
    _ ≤ Real.exp (∑ i ∈ S, Real.log (1 - a i)) := Real.exp_le_exp.mpr hlog
    _ = Real.exp (Real.log (∏ i ∈ S, (1 - a i))) := by
      rw [Real.log_prod]
      exact fun i hi => (hpos i hi).ne'
    _ = _ := Real.exp_log (Finset.prod_pos hpos)

theorem exp_neg_two_tsum_le_prod_one_sub {ι : Type*} (a : ι → ℝ)
    (ha₀ : ∀ i, 0 ≤ a i) (ha₁ : ∀ i, a i ≤ 1 / 2) (hsum : Summable a) (S : Finset ι) :
    Real.exp (-2 * ∑' i, a i) ≤ ∏ i ∈ S, (1 - a i) := by
  have hsumLe := hsum.sum_le_tsum S (fun i _ => ha₀ i)
  exact (Real.exp_le_exp.mpr (by linarith)).trans
    (exp_neg_two_sum_le_prod_one_sub S a (fun i _ => ha₀ i) (fun i _ => ha₁ i))

theorem summable_nonneg_finite_tail {ι : Type*} (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : Summable a) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ι, ∀ T : Finset ι, Disjoint T F → ∑ i ∈ T, a i < ε := by
  classical
  have hev : ∀ᶠ F : Finset ι in atTop, (∑' i : {i // i ∉ F}, a i) < ε :=
    (tendsto_tsum_compl_atTop_zero a).eventually (Iio_mem_nhds hε)
  obtain ⟨F, hF⟩ := hev.exists
  refine ⟨F, ?_⟩
  intro T hTF
  let e : {i // i ∈ T} ↪ {i // i ∉ F} :=
    ⟨fun i => ⟨i.1, fun hi => Finset.disjoint_left.mp hTF i.2 hi⟩,
      fun _ _ h => Subtype.ext (congrArg (fun i : {i // i ∉ F} => i.1) h)⟩
  let U := Finset.univ.map e
  have hs : Summable (fun i : {i // i ∉ F} => a i) := (Finset.summable_compl_iff F).mpr hsum
  have heq : ∑ i ∈ T, a i = ∑ i ∈ U, a i := by
    dsimp only [U]
    rw [Finset.sum_map]
    exact (T.sum_attach a).symm
  rw [heq]
  exact (hs.sum_le_tsum U (fun i _ => ha i)).trans_lt hF

end Bernays
