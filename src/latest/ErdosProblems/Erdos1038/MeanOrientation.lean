import ErdosProblems.Erdos1038.PolynomialBridge
import Mathlib.Analysis.MeanInequalities

/-!
# Mean orientation for Erdős problem 1038

This file formalizes the elementary orientation argument from the manuscript.
For an admissible polynomial, the empirical root mean is the arithmetic mean
of its roots, counted with multiplicity.  If that mean is nonpositive, then
the whole interval `(-1, 0)` lies in the strict unit sublevel set.

The proof is deliberately finite.  For `-1 < x < 0` and a root
`r ∈ [-1, 1]`, one has

`|x - r| ≤ 1 - x * r`.

Strict finite AM--GM handles a nonconstant root configuration.  If all roots
are equal, their common value is nonpositive, and every root distance is
already strictly less than one.  Thus the boundary case where the empirical
mean is exactly zero is included without an additional hypothesis.
-/

open scoped BigOperators
open Set Polynomial
open MeasureTheory

namespace Erdos1038

noncomputable section

/-- The arithmetic mean of the roots of a polynomial, counted with
multiplicity.  For an admissible polynomial the denominator is positive. -/
def empiricalRootMean (f : Polynomial ℝ) : ℝ :=
  f.roots.sum / (f.natDegree : ℝ)

/-- Reflection of all roots through the origin, normalized so that a monic
polynomial remains monic. -/
def rootReflection (f : Polynomial ℝ) : Polynomial ℝ :=
  (-1) ^ f.natDegree * f.comp (-X)

/-- Evaluation of the reflected polynomial. -/
lemma eval_rootReflection (f : Polynomial ℝ) (x : ℝ) :
    (rootReflection f).eval x = (-1 : ℝ) ^ f.natDegree * f.eval (-x) := by
  simp [rootReflection, Polynomial.eval_comp]

/-- Root reflection preserves the absolute value after reflecting the
variable. -/
lemma abs_eval_rootReflection (f : Polynomial ℝ) (x : ℝ) :
    |(rootReflection f).eval x| = |f.eval (-x)| := by
  rw [eval_rootReflection, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- The sublevel set of the root reflection is the preimage of the original
sublevel set under negation. -/
lemma sublevelSet_rootReflection (f : Polynomial ℝ) :
    sublevelSet (rootReflection f) = (fun x : ℝ ↦ -x) ⁻¹' sublevelSet f := by
  ext x
  simp only [sublevelSet, Set.mem_ofPred_eq, Set.mem_preimage]
  rw [abs_eval_rootReflection]

/-- Reflection of the roots preserves the Lebesgue length of the strict unit
sublevel set. -/
lemma sublevelVolume_rootReflection (f : Polynomial ℝ) :
    sublevelVolume (rootReflection f) = sublevelVolume f := by
  rw [sublevelVolume, sublevelVolume, sublevelSet_rootReflection]
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).measure_preimage
    (measurableSet_sublevelSet f).nullMeasurableSet

/-- The normalization in `rootReflection` preserves monicity. -/
lemma IsAdmissible.monic_rootReflection {f : Polynomial ℝ} (hf : IsAdmissible f) :
    (rootReflection f).Monic := by
  exact hf.monic.neg_one_pow_natDegree_mul_comp_neg_X

/-- For a split monic polynomial, reflection negates its root multiset. -/
lemma IsAdmissible.rootReflection_eq_prod_neg_roots {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    rootReflection f =
      (f.roots.map fun r ↦ X - C (-r)).prod := by
  rw [rootReflection, ← hf.card_roots_eq_natDegree]
  have hcomp := congrArg (fun p : Polynomial ℝ ↦ p.comp (-X))
    (hf.splits.eq_prod_roots_of_monic hf.monic)
  change f.comp (-X) =
    ((f.roots.map fun r ↦ X - C r).prod).comp (-X) at hcomp
  rw [hcomp]
  rw [Polynomial.multiset_prod_comp]
  simp only [Multiset.map_map, Function.comp_apply, sub_comp, X_comp, C_comp,
    map_neg]
  have hfactor (r : ℝ) :
      -(X : Polynomial ℝ) - C r = -(X + C r) := by ring
  simp_rw [hfactor]
  simp only [sub_neg_eq_add]
  have hmap :
      (f.roots.map fun r ↦ -(X + C r)) =
        (f.roots.map fun r ↦ X + C r).map Neg.neg := by
    simp [Multiset.map_map]
  rw [hmap]
  rw [Multiset.prod_map_neg, ← mul_assoc, ← pow_add]
  simp

/-- Reflection negates every root, preserving multiplicities. -/
lemma IsAdmissible.roots_rootReflection {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    (rootReflection f).roots = f.roots.map fun r ↦ -r := by
  rw [hf.rootReflection_eq_prod_neg_roots]
  simpa only [Multiset.map_map, Function.comp_apply] using!
    Polynomial.roots_multiset_prod_X_sub_C (f.roots.map fun r ↦ -r)

/-- Reflection preserves the degree of an admissible polynomial. -/
lemma IsAdmissible.natDegree_rootReflection {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    (rootReflection f).natDegree = f.natDegree := by
  rw [hf.rootReflection_eq_prod_neg_roots]
  have hmap :
      (f.roots.map fun r ↦ X - C (-r)) =
        (f.roots.map fun r ↦ -r).map fun r ↦ X - C r := by
    simp [Multiset.map_map]
  rw [hmap,
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card,
    Multiset.card_map, hf.card_roots_eq_natDegree]

/-- Root reflection preserves admissibility, including the exact filtered
root-card condition in `IsAdmissible`. -/
lemma IsAdmissible.reflection {f : Polynomial ℝ}
    (hf : IsAdmissible f) : IsAdmissible (rootReflection f) := by
  refine ⟨hf.monic_rootReflection, ?_, ?_⟩
  · intro heq
    have hdegree : 0 < f.natDegree :=
      hf.monic.natDegree_pos.mpr hf.ne_one
    have : (rootReflection f).natDegree = 0 := by simp [heq]
    rw [hf.natDegree_rootReflection] at this
    omega
  · have hall : ∀ r ∈ (rootReflection f).roots,
        r ∈ Set.Icc (-1 : ℝ) 1 := by
      intro r hr
      rw [hf.roots_rootReflection] at hr
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hr
      have htIcc := hf.root_mem_Icc ht
      constructor <;> linarith [htIcc.1, htIcc.2]
    rw [Multiset.filter_eq_self.mpr hall, hf.roots_rootReflection,
      Multiset.card_map, hf.card_roots_eq_natDegree,
      hf.natDegree_rootReflection]

/-- Reflection reverses the empirical root mean. -/
lemma IsAdmissible.empiricalRootMean_rootReflection {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    empiricalRootMean (rootReflection f) = -empiricalRootMean f := by
  rw [empiricalRootMean, empiricalRootMean, hf.roots_rootReflection,
    hf.natDegree_rootReflection]
  simp [Multiset.sum_map_neg']
  ring

/-- A pointwise comparison used in the mean-orientation argument. -/
lemma abs_sub_le_one_sub_mul {x r : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 0)
    (hr : r ∈ Set.Icc (-1 : ℝ) 1) :
    |x - r| ≤ 1 - x * r := by
  have hxabs : |x| < 1 := by
    rw [abs_of_neg hx.2]
    linarith [hx.1]
  have hrabs : |r| ≤ 1 := (abs_le).2 hr
  have hxr : x * r < 1 := calc
    x * r ≤ |x * r| := le_abs_self _
    _ = |x| * |r| := abs_mul x r
    _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left hrabs (abs_nonneg x)
    _ < 1 * 1 := mul_lt_mul_of_pos_right hxabs zero_lt_one
    _ = 1 := one_mul 1
  have hz : 0 ≤ 1 - x * r := by linarith
  have hx_sq : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hxabs
  have hr_sq : r ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one r).2 hrabs
  have hfactor : 0 ≤ (1 - x ^ 2) * (1 - r ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hsq : |x - r| ^ 2 ≤ (1 - x * r) ^ 2 := by
    rw [sq_abs]
    nlinarith
  nlinarith [sq_nonneg (|x - r| - (1 - x * r))]

/-- Finite mean-orientation inequality.  This is the AM--GM core of the
polynomial statement, with roots represented by an arbitrary finite family. -/
lemma prod_abs_sub_lt_one_of_mean_nonpos {n : ℕ} (hn : 0 < n)
    (r : Fin n → ℝ) (hr : ∀ i, r i ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : (∑ i, r i) / (n : ℝ) ≤ 0)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 0) :
    ∏ i, |x - r i| < 1 := by
  let i₀ : Fin n := ⟨0, hn⟩
  let w : Fin n → ℝ := fun _ ↦ (n : ℝ)⁻¹
  let z : Fin n → ℝ := fun i ↦ 1 - x * r i
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hwpos : ∀ i, 0 < w i := fun _ ↦ inv_pos.mpr hnreal
  have hwsum : ∑ i, w i = 1 := by
    simp [w, hn.ne']
  have hzpos : ∀ i, 0 < z i := by
    intro i
    have hxabs : |x| < 1 := by
      rw [abs_of_neg hx.2]
      linarith [hx.1]
    have hrabs : |r i| ≤ 1 := (abs_le).2 (hr i)
    have hxr : x * r i < 1 := calc
      x * r i ≤ |x * r i| := le_abs_self _
      _ = |x| * |r i| := abs_mul x (r i)
      _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left hrabs (abs_nonneg x)
      _ < 1 * 1 := mul_lt_mul_of_pos_right hxabs zero_lt_one
      _ = 1 := one_mul 1
    dsimp [z]
    linarith
  have harith : ∑ i, w i * z i = 1 - x * ((∑ i, r i) / (n : ℝ)) := by
    simp only [w, z]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    field_simp
  have harith_le : ∑ i, w i * z i ≤ 1 := by
    rw [harith]
    have hxnonpos : x ≤ 0 := hx.2.le
    have := mul_nonneg_of_nonpos_of_nonpos hxnonpos hmean
    linarith
  have hdist : ∀ i, |x - r i| ≤ z i := by
    intro i
    exact abs_sub_le_one_sub_mul hx (hr i)
  have hprod_dist_le :
      ∏ i, |x - r i| ≤ ∏ i, z i := by
    exact Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) (fun i _ ↦ hdist i)
  by_cases hconstant : ∀ i, r i = r i₀
  · have hmean_eq : (∑ i, r i) / (n : ℝ) = r i₀ := by
      simp_rw [hconstant]
      simp [hn.ne']
    have hr₀_nonpos : r i₀ ≤ 0 := by
      rw [hmean_eq] at hmean
      exact hmean
    have hdist_lt : |x - r i₀| < 1 := by
      have hr₀ := hr i₀
      have hxlow : -1 < x := hx.1
      have hxneg : x < 0 := hx.2
      have hr₀_low : -1 ≤ r i₀ := hr₀.1
      rw [abs_lt]
      constructor <;> linarith
    simp_rw [hconstant]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_lt_one₀ (abs_nonneg _) hdist_lt hn.ne'
  · have hvary : ∃ j ∈ (Finset.univ : Finset (Fin n)),
        ∃ k ∈ (Finset.univ : Finset (Fin n)), z j ≠ z k := by
      push_neg at hconstant
      obtain ⟨j, hj⟩ := hconstant
      refine ⟨j, Finset.mem_univ _, i₀, Finset.mem_univ _, ?_⟩
      dsimp [z]
      intro heq
      apply hj
      have hxne : x ≠ 0 := ne_of_lt hx.2
      apply (mul_left_cancel₀ hxne)
      linarith
    have hamgm :
        ∏ i, z i ^ w i < ∑ i, w i * z i :=
      (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos
        Finset.univ w z (fun i _ ↦ hwpos i) hwsum
        (fun i _ ↦ (hzpos i).le)).2 hvary
    have hroot_lt_one : (∏ i, z i) ^ (n : ℝ)⁻¹ < 1 := by
      rw [← Real.finsetProd_rpow Finset.univ z (fun i _ ↦ (hzpos i).le)]
      exact hamgm.trans_le harith_le
    have hprod_z_nonneg : 0 ≤ ∏ i, z i :=
      Finset.prod_nonneg fun i _ ↦ (hzpos i).le
    have hinvpos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnreal
    have hprod_z_lt : ∏ i, z i < 1 :=
      (Real.rpow_lt_one_iff' hprod_z_nonneg hinvpos).mp hroot_lt_one
    exact hprod_dist_le.trans_lt hprod_z_lt

/-- **Mean orientation lemma.**  If the empirical root mean of an admissible
polynomial is nonpositive, its strict unit sublevel set contains `(-1, 0)`. -/
theorem Ioo_neg_one_zero_subset_sublevelSet_of_empiricalRootMean_nonpos
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hmean : empiricalRootMean f ≤ 0) :
    Set.Ioo (-1 : ℝ) 0 ⊆ sublevelSet f := by
  intro x hx
  let l : List ℝ := f.roots.toList
  have hlength : l.length = f.natDegree := by
    simp [l, hf.card_roots_eq_natDegree]
  have hlength_pos : 0 < l.length := by
    rw [hlength]
    exact hf.monic.natDegree_pos.mpr hf.ne_one
  have hroots : ∀ i : Fin l.length,
      l[i.1] ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i
    apply hf.root_mem_Icc
    rw [← Multiset.mem_toList]
    change l[i.1] ∈ l
    exact List.getElem_mem i.isLt
  have hmean' :
      (∑ i : Fin l.length, l[i.1]) / (l.length : ℝ) ≤ 0 := by
    simpa [empiricalRootMean, l, hf.card_roots_eq_natDegree] using! hmean
  have hprod := prod_abs_sub_lt_one_of_mean_nonpos hlength_pos
    (fun i : Fin l.length ↦ l[i.1]) hroots hmean' hx
  change |f.eval x| < 1
  rw [hf.abs_eval_eq_prod_abs_roots]
  change (∏ i : Fin l.length, |x - l[i.1]|) < 1 at hprod
  have hprod_eq :
      (∏ i : Fin l.length, |x - l[i.1]|) =
        (l.map fun r ↦ |x - r|).prod := by
    simpa using! Fin.prod_univ_fun_getElem l (fun r : ℝ ↦ |x - r|)
  rw [hprod_eq] at hprod
  have hlcoe : (l : Multiset ℝ) = f.roots := by simp [l]
  rw [← hlcoe]
  simpa using! hprod

/-- Every admissible polynomial admits one of the two reflected orientations:
either it already has nonpositive empirical root mean, or its root reflection
does.  In both branches the chosen polynomial is admissible and has the same
sublevel volume as the original polynomial. -/
theorem reflection_orientation_dichotomy {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    (IsAdmissible f ∧ empiricalRootMean f ≤ 0 ∧
        sublevelVolume f = sublevelVolume f) ∨
      (IsAdmissible (rootReflection f) ∧
        empiricalRootMean (rootReflection f) ≤ 0 ∧
        sublevelVolume (rootReflection f) = sublevelVolume f) := by
  rcases le_total (empiricalRootMean f) 0 with hmean | hmean
  · exact Or.inl ⟨hf, hmean, rfl⟩
  · refine Or.inr ⟨hf.reflection, ?_, sublevelVolume_rootReflection f⟩
    rw [hf.empiricalRootMean_rootReflection]
    exact neg_nonpos.mpr hmean

/-- A uniform representative form of `reflection_orientation_dichotomy`.
The selected polynomial is either `f` or its root reflection, is admissible,
has nonpositive empirical root mean, has the same sublevel volume as `f`, and
therefore contains `(-1, 0)` in its strict unit sublevel set. -/
theorem exists_oriented_admissible_same_sublevelVolume {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    ∃ g : Polynomial ℝ,
      (g = f ∨ g = rootReflection f) ∧
      IsAdmissible g ∧
      empiricalRootMean g ≤ 0 ∧
      sublevelVolume g = sublevelVolume f ∧
      Set.Ioo (-1 : ℝ) 0 ⊆ sublevelSet g := by
  rcases reflection_orientation_dichotomy hf with h | h
  · refine ⟨f, Or.inl rfl, h.1, h.2.1, h.2.2, ?_⟩
    exact Ioo_neg_one_zero_subset_sublevelSet_of_empiricalRootMean_nonpos
      h.1 h.2.1
  · refine ⟨rootReflection f, Or.inr rfl, h.1, h.2.1, h.2.2, ?_⟩
    exact Ioo_neg_one_zero_subset_sublevelSet_of_empiricalRootMean_nonpos
      h.1 h.2.1

end

end Erdos1038
