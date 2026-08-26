import ErdosProblems.Erdos1038.PolynomialBridge

/-!
# Translation invariance for Erdős problem 1038

We use the convention

`translatePolynomial f c = f.comp (X + C c)`.

Thus `translatePolynomial f c` evaluates at `x` as `f` evaluates at
`x + c`, and a root `r` of `f` is moved to `r - c`.  This is the convention
needed when a root cluster at `c₀` is moved to `-1`: one takes translation
parameter `c₀ + 1`.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- Translate the variable by `c`.  The convention is
`(translatePolynomial f c)(x) = f(x + c)`. -/
def translatePolynomial (f : Polynomial ℝ) (c : ℝ) : Polynomial ℝ :=
  f.comp (X + C c)

/-- Evaluation under our translation convention. -/
@[simp]
lemma eval_translatePolynomial (f : Polynomial ℝ) (c x : ℝ) :
    (translatePolynomial f c).eval x = f.eval (x + c) := by
  simp [translatePolynomial, Polynomial.eval_comp]

/-- Translation preserves monicity. -/
lemma IsAdmissible.monic_translatePolynomial {f : Polynomial ℝ}
    (hf : IsAdmissible f) (c : ℝ) :
    (translatePolynomial f c).Monic :=
  hf.monic.comp_X_add_C c

/-- Translation preserves the natural degree. -/
lemma natDegree_translatePolynomial (f : Polynomial ℝ) (c : ℝ) :
    (translatePolynomial f c).natDegree = f.natDegree := by
  simp [translatePolynomial, Polynomial.natDegree_comp]

/-- Translation preserves splitting over the reals. -/
lemma IsAdmissible.splits_translatePolynomial {f : Polynomial ℝ}
    (hf : IsAdmissible f) (c : ℝ) :
    (translatePolynomial f c).Splits :=
  hf.splits.comp_X_add_C c

/-- Exact factorization of a translated admissible polynomial.  Every root
`r` is replaced by `r - c`, with multiplicity unchanged. -/
lemma IsAdmissible.translatePolynomial_eq_prod_translated_roots
    {f : Polynomial ℝ} (hf : IsAdmissible f) (c : ℝ) :
    translatePolynomial f c =
      (f.roots.map fun r ↦ X - C (r - c)).prod := by
  rw [translatePolynomial]
  have hcomp := congrArg (fun p : Polynomial ℝ ↦ p.comp (X + C c))
    (hf.splits.eq_prod_roots_of_monic hf.monic)
  change f.comp (X + C c) =
    ((f.roots.map fun r ↦ X - C r).prod).comp (X + C c) at hcomp
  rw [hcomp, Polynomial.multiset_prod_comp]
  simp only [Multiset.map_map, Function.comp_apply]
  have hfactor (r : ℝ) :
      (X - C r).comp (X + C c) = X - C (r - c) := by
    simp only [sub_comp, X_comp, C_comp]
    rw [map_sub]
    ring
  simp_rw [hfactor]

/-- The root multiset is translated by `r ↦ r - c`; this equality records
multiplicities, not merely the underlying root set. -/
lemma IsAdmissible.roots_translatePolynomial {f : Polynomial ℝ}
    (hf : IsAdmissible f) (c : ℝ) :
    (translatePolynomial f c).roots = f.roots.map fun r ↦ r - c := by
  rw [hf.translatePolynomial_eq_prod_translated_roots c]
  simpa only [Multiset.map_map, Function.comp_apply] using!
    Polynomial.roots_multiset_prod_X_sub_C (f.roots.map fun r ↦ r - c)

/-- Root multiplicities transform by the same translation convention:
the multiplicity at `x` after translation is the original multiplicity at
`x + c`. -/
lemma rootMultiplicity_translatePolynomial (f : Polynomial ℝ) (c x : ℝ) :
    (translatePolynomial f c).rootMultiplicity x =
      f.rootMultiplicity (x + c) := by
  calc
    (translatePolynomial f c).rootMultiplicity x =
        ((translatePolynomial f c).comp (X + C x)).rootMultiplicity 0 :=
      Polynomial.rootMultiplicity_eq_rootMultiplicity
    _ = (f.comp (X + C (x + c))).rootMultiplicity 0 := by
      congr 1
      simp only [translatePolynomial, comp_assoc, add_comp, X_comp, C_comp]
      apply congrArg (fun q : Polynomial ℝ ↦ f.comp q)
      rw [map_add]
      ring
    _ = f.rootMultiplicity (x + c) :=
      Polynomial.rootMultiplicity_eq_rootMultiplicity.symm

/-- An admissible polynomial remains admissible after translation provided
all translated roots still lie in `[-1, 1]`. -/
lemma IsAdmissible.translated {f : Polynomial ℝ}
    (hf : IsAdmissible f) (c : ℝ)
    (hroots : ∀ r ∈ f.roots, r - c ∈ Set.Icc (-1 : ℝ) 1) :
    IsAdmissible (translatePolynomial f c) := by
  refine ⟨hf.monic_translatePolynomial c, ?_, ?_⟩
  · intro heq
    have hdegree : 0 < f.natDegree :=
      hf.monic.natDegree_pos.mpr hf.ne_one
    have hzero : (translatePolynomial f c).natDegree = 0 := by
      simp [heq]
    rw [natDegree_translatePolynomial f c] at hzero
    omega
  · have hall : ∀ r ∈ (translatePolynomial f c).roots,
        r ∈ Set.Icc (-1 : ℝ) 1 := by
      intro r hr
      rw [hf.roots_translatePolynomial c] at hr
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hr
      exact hroots t ht
    rw [Multiset.filter_eq_self.mpr hall,
      hf.roots_translatePolynomial c, Multiset.card_map,
      hf.card_roots_eq_natDegree, natDegree_translatePolynomial f c]

/-- Exact sublevel-set identity under translation. -/
lemma sublevelSet_translatePolynomial (f : Polynomial ℝ) (c : ℝ) :
    sublevelSet (translatePolynomial f c) =
      (fun x : ℝ ↦ x + c) ⁻¹' sublevelSet f := by
  ext x
  simp [sublevelSet]

/-- Translation preserves the Lebesgue volume of the strict unit sublevel
set. -/
lemma sublevelVolume_translatePolynomial (f : Polynomial ℝ) (c : ℝ) :
    sublevelVolume (translatePolynomial f c) = sublevelVolume f := by
  rw [sublevelVolume, sublevelVolume, sublevelSet_translatePolynomial]
  exact measure_preimage_add_right (volume : Measure ℝ) c (sublevelSet f)

end

end Erdos1038
