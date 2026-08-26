import ErdosProblems.Erdos1038.TaoUpperClosedTarget
import ErdosProblems.Erdos1038.EndpointEquality

/-!
# Algebraic equality case for the sharp upper bound

If the two extreme points of the closed unit sublevel set are exactly
`-sqrt 2` and `sqrt 2`, evaluating the polynomial at those two points
classifies its roots.  For every root `r ∈ [-1,1]`, the product of the two
corresponding distances is `2 - r^2 ≥ 1`.  Both endpoint evaluations have
absolute value at most one, so every such factor is one.  Thus all roots are
endpoints, and the two endpoint evaluations force the multiplicities at
`-1` and `1` to agree.
-/

open scoped BigOperators
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

private theorem one_le_multiset_map_prod
    {α : Type*} (s : Multiset α) (g : α → ℝ)
    (hg : ∀ x ∈ s, 1 ≤ g x) :
    1 ≤ (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact one_le_mul_of_one_le_of_one_le (hg x (by simp))
        (ih fun y hy ↦ hg y (by simp [hy]))

private theorem multiset_factor_eq_one_of_prod_le_one
    {α : Type*} [DecidableEq α] (s : Multiset α) (g : α → ℝ)
    (hg : ∀ x ∈ s, 1 ≤ g x)
    (hprod : (s.map g).prod ≤ 1) :
    ∀ x ∈ s, g x = 1 := by
  intro x hx
  have hrest : 1 ≤ ((s.erase x).map g).prod :=
    one_le_multiset_map_prod (s.erase x) g fun y hy ↦
      hg y (Multiset.mem_of_mem_erase hy)
  have hfactor :
      (s.map g).prod = g x * ((s.erase x).map g).prod := by
    conv_lhs => rw [← Multiset.cons_erase hx]
    simp
  have hxone : 1 ≤ g x := hg x hx
  have hxnonneg : 0 ≤ g x := zero_le_one.trans hxone
  rw [hfactor] at hprod
  nlinarith [mul_nonneg hxnonneg (sub_nonneg.mpr hrest)]

private theorem root_endpoint_distance_product
    {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    |Real.sqrt 2 - r| * |-Real.sqrt 2 - r| = 2 - r ^ 2 := by
  rw [abs_of_nonneg (by linarith [one_lt_sqrt_two, hr.2]),
    abs_of_nonpos (by linarith [one_lt_sqrt_two, hr.1])]
  nlinarith [sqrt_two_sq]

private theorem roots_eq_replicate_endpoints_of_subset
    {f : Polynomial ℝ}
    (hroot : ∀ r ∈ f.roots, r = -1 ∨ r = 1) :
    f.roots = Multiset.replicate (f.roots.count (-1)) (-1) +
      Multiset.replicate (f.roots.count 1) 1 := by
  classical
  rw [Multiset.ext]
  intro r
  by_cases hrn : r = -1
  · subst r
    simp only [Multiset.count_add, Multiset.count_replicate]
    norm_num
  by_cases hrp : r = 1
  · subst r
    simp only [Multiset.count_add, Multiset.count_replicate]
    norm_num
  have hrnot : r ∉ f.roots := by
    intro hr
    exact (hroot r hr).elim hrn hrp
  rw [Multiset.count_eq_zero.mpr hrnot, Multiset.count_add,
    Multiset.count_replicate, Multiset.count_replicate]
  simp [Ne.symm hrn, Ne.symm hrp]

/-- If the closed unit sublevel set has the two sharp extreme points, the
polynomial is one of the claimed equality examples. -/
theorem extremal_of_closedUnitSublevel_endpoints
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hleft : closedUnitSublevelLeft f hf = -Real.sqrt 2)
    (hright : closedUnitSublevelRight f hf = Real.sqrt 2) :
    ∃ m : ℕ, 0 < m ∧ f = (Polynomial.X ^ 2 - 1) ^ m := by
  let s : ℝ := Real.sqrt 2
  have hs : s ^ 2 = 2 := sqrt_two_sq
  have hsone : 1 < s := one_lt_sqrt_two
  have hspos : 0 < s + 1 := by linarith
  have hsne : s + 1 ≠ 1 := by linarith
  have hleftMem : -s ∈ closedUnitSublevelSet f := by
    simpa [s, hleft] using! (closedUnitSublevelLeft_isLeast hf).1
  have hrightMem : s ∈ closedUnitSublevelSet f := by
    simpa [s, hright] using! (closedUnitSublevelRight_isGreatest hf).1
  have hevalLeft : |f.eval (-s)| ≤ 1 := hleftMem
  have hevalRight : |f.eval s| ≤ 1 := hrightMem
  have hprodEval :
      |f.eval s| * |f.eval (-s)| =
        (f.roots.map fun r ↦ 2 - r ^ 2).prod := by
    rw [hf.abs_eval_eq_prod_abs_roots,
      hf.abs_eval_eq_prod_abs_roots, ← Multiset.prod_map_mul]
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro r hr
    simpa [s] using! root_endpoint_distance_product (hf.root_mem_Icc hr)
  have hfactorOne : ∀ r ∈ f.roots, 2 - r ^ 2 = 1 := by
    apply multiset_factor_eq_one_of_prod_le_one f.roots
        (fun r ↦ 2 - r ^ 2)
    · intro r hr
      have hrsq : r ^ 2 ≤ 1 :=
        (sq_le_one_iff_abs_le_one r).2 ((abs_le).2 (hf.root_mem_Icc hr))
      linarith
    · rw [← hprodEval]
      nlinarith [abs_nonneg (f.eval s), abs_nonneg (f.eval (-s)),
        mul_nonneg (sub_nonneg.mpr hevalRight) (sub_nonneg.mpr hevalLeft)]
  have hrootEndpoints : ∀ r ∈ f.roots, r = -1 ∨ r = 1 := by
    intro r hr
    have hsq : r ^ 2 = 1 := by linarith [hfactorOne r hr]
    have hmul : (r - 1) * (r + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hmul with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  have hroots := roots_eq_replicate_endpoints_of_subset hrootEndpoints
  let a := f.roots.count (-1)
  let b := f.roots.count 1
  have hevalRightFormula : |f.eval s| = (s + 1) ^ a * (s - 1) ^ b := by
    rw [hf.abs_eval_eq_prod_abs_roots, hroots]
    simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
      Multiset.prod_replicate]
    simp only [sub_neg_eq_add]
    change |s + 1| ^ a * |s - 1| ^ b =
      (s + 1) ^ a * (s - 1) ^ b
    rw [abs_of_pos hspos, abs_of_pos (sub_pos.mpr hsone)]
  have hprodFactors : (f.roots.map fun r ↦ 2 - r ^ 2).prod = 1 := by
    apply le_antisymm
    · rw [← hprodEval]
      nlinarith [abs_nonneg (f.eval s), abs_nonneg (f.eval (-s)),
        mul_nonneg (sub_nonneg.mpr hevalRight) (sub_nonneg.mpr hevalLeft)]
    · apply one_le_multiset_map_prod
      intro r hr
      have hrsq : r ^ 2 ≤ 1 :=
        (sq_le_one_iff_abs_le_one r).2 ((abs_le).2 (hf.root_mem_Icc hr))
      linarith
  have hprodEvalOne : |f.eval s| * |f.eval (-s)| = 1 := by
    rw [hprodEval, hprodFactors]
  have hevalRightOne : |f.eval s| = 1 := by
    apply le_antisymm hevalRight
    nlinarith [abs_nonneg (f.eval s), abs_nonneg (f.eval (-s)),
      mul_nonneg (abs_nonneg (f.eval s)) (sub_nonneg.mpr hevalLeft)]
  have heqPowers : (s + 1) ^ a = (s + 1) ^ b := by
    have hpair : (s - 1) * (s + 1) = 1 := by nlinarith [hs]
    have hpairPow : (s - 1) ^ b * (s + 1) ^ b = 1 := by
      rw [← mul_pow, hpair, one_pow]
    calc
      (s + 1) ^ a = (s + 1) ^ a * 1 := by ring
      _ = (s + 1) ^ a * ((s - 1) ^ b * (s + 1) ^ b) := by rw [hpairPow]
      _ = ((s + 1) ^ a * (s - 1) ^ b) * (s + 1) ^ b := by ring
      _ = (s + 1) ^ b := by rw [← hevalRightFormula, hevalRightOne, one_mul]
  have hab : a = b := pow_right_injective₀ hspos hsne heqPowers
  let m := a
  have hroots' : f.roots = Multiset.replicate m (-1) +
      Multiset.replicate m 1 := by
    change f.roots = Multiset.replicate a (-1) +
      Multiset.replicate b 1 at hroots
    rw [← hab] at hroots
    simpa [m] using! hroots
  have hmpos : 0 < m := by
    have hcard : 0 < f.roots.card := Multiset.card_pos.mpr (roots_ne_zero hf)
    rw [hroots'] at hcard
    simpa [m] using! hcard
  refine ⟨m, hmpos, ?_⟩
  rw [hf.splits.eq_prod_roots_of_monic hf.monic, hroots']
  simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
    Multiset.prod_replicate]
  change (X - C (-1 : ℝ)) ^ m * (X - C (1 : ℝ)) ^ m =
    (X ^ 2 - 1) ^ m
  rw [← mul_pow]
  congr 1
  simp only [map_neg, map_one]
  ring

/-- Endpoint bounds plus equality of the sublevel volume force both endpoint
bounds to be equalities, so the algebraic classification above applies. -/
theorem extremal_of_sublevelVolume_eq_of_endpoint_bounds
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hleft : -Real.sqrt 2 ≤ closedUnitSublevelLeft f hf)
    (hright : closedUnitSublevelRight f hf ≤ Real.sqrt 2)
    (hvolume : sublevelVolume f =
      ENNReal.ofReal (2 * Real.sqrt 2)) :
    ∃ m : ℕ, 0 < m ∧ f = (Polynomial.X ^ 2 - 1) ^ m := by
  let l := closedUnitSublevelLeft f hf
  let r := closedUnitSublevelRight f hf
  have hlmem : l ∈ closedUnitSublevelSet f :=
    (closedUnitSublevelLeft_isLeast hf).1
  have hrmem : r ∈ closedUnitSublevelSet f :=
    (closedUnitSublevelRight_isGreatest hf).1
  have hlr : l ≤ r := (closedUnitSublevelLeft_isLeast hf).2 hrmem
  have hmeasure := measure_mono (μ := volume)
    (closedUnitSublevelSet_subset_endpoints hf)
  rw [volume_closedUnitSublevelSet hf, hvolume, Real.volume_Icc] at hmeasure
  have hdiam : 2 * Real.sqrt 2 ≤ r - l := by
    exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hlr)).mp hmeasure
  have hlefteq : l = -Real.sqrt 2 := by
    dsimp [l, r] at hleft hright ⊢
    dsimp [l, r] at hdiam
    linarith
  have hrighteq : r = Real.sqrt 2 := by
    dsimp [l, r] at hleft hright ⊢
    dsimp [l, r] at hdiam
    linarith
  exact extremal_of_closedUnitSublevel_endpoints hf hlefteq hrighteq

end

end Erdos1038
