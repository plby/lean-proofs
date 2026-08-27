import ErdosProblems.Erdos587.HooleyQuotientTransfer
import ErdosProblems.Erdos587.HooleyConvexExtraction

/-! # Full-width GAP extraction, including inner proper rank reduction -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

theorem delta_robust_convex_extraction (X : ConvexProgression) {d : ℕ}
    (p : (Fin d → ℤ) →ₗ[ℤ] (Fin X.rank → ℤ)) (hp : Function.Surjective p)
    (hcube : ∀ e : Fin d → ℝ, (∀ i, |e i| ≤ (1 / 2 : ℝ)) →
      intLinearMapRealExtension p e ∈ bodyDilate (1 / 4 ^ (X.rank + 2)) X.body)
    (U : Finset (Fin X.rank → ℤ)) (hU : 0 < U.card) (hinj : Set.InjOn X.eval U)
    (hnonzero : ∃ u, X.eval u ≠ 0) (k : ℕ) (hk : 2 * k ≤ U.card)
    (hspan : ∀ V ⊆ U, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin X.rank → ℤ))) = ⊤)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hsub : ∀ x ∈ CFP.deltaZonotope (fun u : U => intCastVec (u : Fin X.rank → ℤ)),
      δ • x ∈ X.body)
    (hbase : ∃ c : Fin X.rank → ℤ, X.eval c = X.base)
    (hbaseMass : (X.base : ℝ) ≤ C * ∑ u ∈ U, (X.eval u : ℝ))
    (hlarge : 16 * ((4 ^ X.rank : ℕ) : ℝ) ≤
      (δ / ((4 ^ (X.rank + 1) : ℕ) : ℝ)) * U.card) :
    let K := ⌈32 * ((4 ^ X.rank : ℕ) : ℝ) / (δ / ((4 ^ (X.rank + 1) : ℕ) : ℝ))⌉₊
    let F := 9 * X.rank * K
    0 < F ∧ ∃ Q : GeneralizedAP, 0 < Q.rank ∧ Q.rank ≤ X.rank ∧
      Q.Proper ∧ Q.HasHomogeneousBase ∧ (Q.carrier : Set ℤ) ⊆ X.carrier ∧
      (∀ i, U.card ≤ F * Q.length i) ∧
      U.card ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card ∧
      (Q.upperEndpoint : ℝ) ≤ (C * K + 1) * Q.coefficientSpan := by
  classical
  obtain ⟨D⟩ := delta_exists_inner_proper_quotient X p hp hcube
  let Y := D.progression
  let V := U.image D.projection
  let δ₀ := δ / ((4 ^ (X.rank + 1) : ℕ) : ℝ)
  let K := ⌈32 * ((4 ^ X.rank : ℕ) : ℝ) / δ₀⌉₊
  let K' := ⌈32 * ((4 ^ Y.rank : ℕ) : ℝ) / (D.factor * δ)⌉₊
  have hinj' := D.injOn X hinj
  have hcard : V.card = U.card := Finset.card_image_of_injOn hinj'
  have hY : 0 < Y.rank := D.rank_pos X hnonzero
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδlo : δ₀ ≤ D.factor * δ := by
    have hh := mul_le_mul_of_nonneg_right D.factor_lower hδ.le
    simpa only [δ₀, Nat.cast_pow, Nat.cast_ofNat, one_div, div_eq_mul_inv,
      one_mul, mul_comm] using hh
  have hscale : ((4 ^ Y.rank : ℕ) : ℝ) ≤ ((4 ^ X.rank : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 4) D.rank_le
  have hlargeY : 16 * ((4 ^ Y.rank : ℕ) : ℝ) ≤ (D.factor * δ) * V.card := by
    rw [hcard]
    calc
      _ ≤ 16 * ((4 ^ X.rank : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ ≤ δ₀ * U.card := hlarge
      _ ≤ (D.factor * δ) * U.card := mul_le_mul_of_nonneg_right hδlo (Nat.cast_nonneg _)
  have hsum : (∑ u ∈ V, (Y.eval u : ℝ)) = ∑ u ∈ U, (X.eval u : ℝ) := by
    dsimp only [V]
    rw [Finset.sum_image (fun u hu v hv h => hinj' hu hv h)]
    simp only [Y, D.eval_projection]
  have hbaseY : (Y.base : ℝ) ≤ C * ∑ u ∈ V, (Y.eval u : ℝ) := by
    rw [hsum]
    change (D.progression.base : ℝ) ≤ _
    rw [D.base_eq]
    exact hbaseMass
  obtain ⟨hF', Q, hQrank, hQproper, hQhom, hQsub, hside, hQcard, hheight⟩ :=
    delta_full_width_convex_extraction Y hY V (by rwa [hcard]) k (by rwa [hcard])
      (delta_finset_robust_spanning_image U k hspan D.projection D.surjective)
      (mul_pos D.factor_pos hδ) hC (D.zonotope X U hinj δ hsub) D.rounding
      D.proper (D.homogeneous X hbase) hbaseY hlargeY
  have hK : K' ≤ K := by
    apply Nat.ceil_mono
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hscale (by norm_num))
      hδ₀ hδlo
  have hF : 9 * Y.rank * K' ≤ 9 * X.rank * K :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 9 D.rank_le) hK
  refine ⟨hF'.trans_le hF, Q, hQrank ▸ hY, hQrank ▸ D.rank_le, hQproper, hQhom,
    hQsub.trans D.carrier_subset, ?_, ?_, ?_⟩
  · intro i
    have hs := hside i
    rw [hcard] at hs
    exact hs.trans (Nat.mul_le_mul_right (Q.length i) hF)
  · rw [hcard] at hQcard
    exact hQcard.trans (Nat.mul_le_mul_right Q.carrier.card
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hF Q.rank)))
  · have hKreal : (K' : ℝ) ≤ K := by exact_mod_cast hK
    have hspan0 : (0 : ℝ) ≤ Q.coefficientSpan := by
      change (0 : ℝ) ≤ ((∑ i, (Q.length i : ℤ) * |Q.step i| : ℤ) : ℝ)
      positivity
    exact hheight.trans (mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left hKreal hC) le_rfl) hspan0)

end Erdos587.GeneralizedAP
