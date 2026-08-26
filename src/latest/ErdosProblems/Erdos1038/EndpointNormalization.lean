import ErdosProblems.Erdos1038.Atomization
import ErdosProblems.Erdos1038.MeanOrientation
import ErdosProblems.Erdos1038.TranslationInvariance
import ErdosProblems.Erdos1038.SublevelComponents

/-!
# Endpoint normalization after component atomization

This file packages the finite reduction which follows simultaneous
atomization and mean orientation.  A component-atomized polynomial has at
most one distinct root value in each strict unit sublevel component.  In the
nonpositive-mean orientation, the component containing `(-1, 0)` determines
a distinguished, leftmost root cluster.  Translating that cluster to `-1`
preserves admissibility, volume, component atomization, and the mean
orientation.
-/

open scoped BigOperators ENNReal Real
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- There is at most one distinct root location in each strict unit
sublevel component.  Multiplicity at that location is unrestricted. -/
def IsComponentAtomized (f : Polynomial ℝ) : Prop :=
  ∀ ⦃r s : ℝ⦄, r ∈ f.roots → s ∈ f.roots →
    sublevelComponent f r = sublevelComponent f s → r = s

/-- Translating a set by `x ↦ x - c` gives the translated polynomial's
sublevel set. -/
lemma image_sublevelSet_subRight (f : Polynomial ℝ) (c : ℝ) :
    (Homeomorph.subRight c) '' sublevelSet f =
      sublevelSet (translatePolynomial f c) := by
  ext x
  simp [sublevelSet_translatePolynomial, sub_eq_iff_eq_add]

/-- Exact covariance of sublevel components under translation. -/
lemma sublevelComponent_translatePolynomial {f : Polynomial ℝ}
    {x c : ℝ} (hx : x ∈ sublevelSet f) :
    sublevelComponent (translatePolynomial f c) (x - c) =
      (Homeomorph.subRight c) '' sublevelComponent f x := by
  have hcomponent :=
    (Homeomorph.subRight c).image_connectedComponentIn hx
  rw [image_sublevelSet_subRight] at hcomponent
  simpa [sublevelComponent] using! hcomponent.symm

/-- Component atomization is invariant under translating all roots. -/
lemma IsComponentAtomized.translatePolynomial {f : Polynomial ℝ}
    (ha : IsComponentAtomized f) (hf : IsAdmissible f) (c : ℝ) :
    IsComponentAtomized (translatePolynomial f c) := by
  intro x y hx hy hxy
  rw [hf.roots_translatePolynomial c] at hx hy
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hy
  have hrC := sublevelComponent_translatePolynomial
    (c := c) (root_mem_sublevelSet hr)
  have hsC := sublevelComponent_translatePolynomial
    (c := c) (root_mem_sublevelSet hs)
  have himage :
      (Homeomorph.subRight c) '' sublevelComponent f r =
        (Homeomorph.subRight c) '' sublevelComponent f s := by
    rw [← hrC, ← hsC]
    exact hxy
  have hold : sublevelComponent f r = sublevelComponent f s :=
    (Homeomorph.subRight c).injective.image_injective himage
  rw [ha hr hs hold]

/-- Sum after subtracting a common constant from every multiset entry. -/
private lemma sum_map_sub_const (s : Multiset ℝ) (c : ℝ) :
    (s.map fun r ↦ r - c).sum = s.sum - (s.card : ℝ) * c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
        Nat.cast_add, Nat.cast_one, ih]
      ring

/-- Equality case for a product of numbers in `[0,1]`. -/
private lemma multiset_eq_replicate_one_of_mem_Icc_of_prod_eq_one
    {s : Multiset ℝ} (hmem : ∀ x ∈ s, x ∈ Icc (0 : ℝ) 1)
    (hprod : s.prod = 1) :
    s = Multiset.replicate s.card (1 : ℝ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha : a ∈ Icc (0 : ℝ) 1 := hmem a (by simp)
      have hs : ∀ x ∈ s, x ∈ Icc (0 : ℝ) 1 := by
        intro x hx
        exact hmem x (by simp [hx])
      have hs_nonneg : 0 ≤ s.prod :=
        Multiset.prod_nonneg (fun x hx ↦ (hs x hx).1)
      have hs_le : s.prod ≤ 1 := by
        have hmaps := Multiset.prod_map_le_prod_map₀
          (s := s) (fun x : ℝ ↦ x) (fun _ ↦ (1 : ℝ))
          (fun x hx ↦ (hs x hx).1) (fun x hx ↦ (hs x hx).2)
        simpa using! hmaps
      have haprod : a * s.prod = 1 := by simpa using! hprod
      have hone_le_a : 1 ≤ a := by
        rw [← haprod]
        exact mul_le_of_le_one_right ha.1 hs_le
      have haone : a = 1 := le_antisymm ha.2 hone_le_a
      have hsprod : s.prod = 1 := by
        rw [haone] at haprod
        simpa using! haprod
      have ih' := ih hs hsprod
      rw [haone, ih']
      simp [Multiset.replicate_succ]

/-- Translation subtracts its parameter from the empirical root mean. -/
lemma IsAdmissible.empiricalRootMean_translatePolynomial
    {f : Polynomial ℝ} (hf : IsAdmissible f) (c : ℝ) :
    empiricalRootMean (translatePolynomial f c) =
      empiricalRootMean f - c := by
  rw [empiricalRootMean, empiricalRootMean, hf.roots_translatePolynomial,
    natDegree_translatePolynomial, sum_map_sub_const,
    hf.card_roots_eq_natDegree]
  have hdegree : (f.natDegree : ℝ) ≠ 0 := by
    exact_mod_cast (hf.monic.natDegree_pos.mpr hf.ne_one).ne'
  field_simp [hdegree]

/-- The hypotheses needed for endpoint normalization. -/
structure EndpointNormalizationHypotheses (f : Polynomial ℝ) where
  admissible : IsAdmissible f
  componentAtomized : IsComponentAtomized f
  mean_nonpos : empiricalRootMean f ≤ 0

/-- Build the normalization hypotheses directly for the output of
simultaneous empirical atomization.  The remaining two assumptions are the
explicit one-cluster-per-new-component and orientation hypotheses. -/
def EndpointNormalizationHypotheses.ofAtomized {f : Polynomial ℝ}
    (hf : IsAdmissible f)
    (hclusters : IsComponentAtomized (atomizedPolynomial f))
    (hmean : empiricalRootMean (atomizedPolynomial f) ≤ 0) :
    EndpointNormalizationHypotheses (atomizedPolynomial f) where
  admissible := isAdmissible_atomizedPolynomial hf
  componentAtomized := hclusters
  mean_nonpos := hmean

/-- Multiplicity of the endpoint root `-1`. -/
def endpointMultiplicity (f : Polynomial ℝ) : ℕ := by
  classical
  exact f.roots.count (-1)

/-- Root occurrences away from the normalized endpoint `-1`. -/
def endpointResidualRoots (f : Polynomial ℝ) : Multiset ℝ := by
  classical
  exact f.roots.filter fun r ↦ r ≠ -1

/-- Relative endpoint multiplicity. -/
def endpointMultiplicityFraction (f : Polynomial ℝ) : ℝ :=
  (endpointMultiplicity f : ℝ) / (f.natDegree : ℝ)

@[simp]
lemma mem_endpointResidualRoots {f : Polynomial ℝ} {r : ℝ} :
    r ∈ endpointResidualRoots f ↔ r ∈ f.roots ∧ r ≠ -1 := by
  classical
  simp [endpointResidualRoots]

/-- The endpoint copies and residual root occurrences partition the full
root multiset. -/
lemma replicate_endpoint_add_residual (f : Polynomial ℝ) :
    Multiset.replicate (endpointMultiplicity f) (-1 : ℝ) +
      endpointResidualRoots f = f.roots := by
  classical
  rw [endpointMultiplicity, endpointResidualRoots,
    ← Multiset.filter_eq' f.roots (-1)]
  exact Multiset.filter_add_not (fun r : ℝ ↦ r = -1) f.roots

/-- A fixed point used to name the component containing `(-1, 0)`. -/
def leftOrientationPoint : ℝ := -(1 / 2 : ℝ)

@[simp]
lemma leftOrientationPoint_mem_Ioo :
    leftOrientationPoint ∈ Ioo (-1 : ℝ) 0 := by
  norm_num [leftOrientationPoint]

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)
include h

lemma Ioo_neg_one_zero_subset_sublevelSet :
    Ioo (-1 : ℝ) 0 ⊆ sublevelSet f :=
  Ioo_neg_one_zero_subset_sublevelSet_of_empiricalRootMean_nonpos
    h.admissible h.mean_nonpos

lemma leftOrientationPoint_mem_sublevelSet :
    leftOrientationPoint ∈ sublevelSet f :=
  h.Ioo_neg_one_zero_subset_sublevelSet leftOrientationPoint_mem_Ioo

/-- Every point of `(-1, 0)` lies in the component named by the fixed
orientation point. -/
lemma Ioo_neg_one_zero_subset_component :
    Ioo (-1 : ℝ) 0 ⊆ sublevelComponent f leftOrientationPoint := by
  exact isPreconnected_Ioo.subset_connectedComponentIn
    leftOrientationPoint_mem_Ioo h.Ioo_neg_one_zero_subset_sublevelSet

lemma exists_distinguishedCluster :
    ∃ r ∈ f.roots, r ∈ sublevelComponent f leftOrientationPoint :=
  sublevelComponent_contains_root h.admissible
    h.leftOrientationPoint_mem_sublevelSet

/-- The unique root location in the component containing `(-1, 0)`. -/
def distinguishedCluster : ℝ :=
  Classical.choose h.exists_distinguishedCluster

lemma distinguishedCluster_mem_roots :
    h.distinguishedCluster ∈ f.roots :=
  (Classical.choose_spec h.exists_distinguishedCluster).1

lemma distinguishedCluster_mem_component :
    h.distinguishedCluster ∈
      sublevelComponent f leftOrientationPoint :=
  (Classical.choose_spec h.exists_distinguishedCluster).2

/-- Any root in the distinguished component is its unique cluster. -/
lemma root_eq_distinguishedCluster_of_mem_component {r : ℝ}
    (hr : r ∈ f.roots)
    (hrC : r ∈ sublevelComponent f leftOrientationPoint) :
    r = h.distinguishedCluster := by
  apply h.componentAtomized hr h.distinguishedCluster_mem_roots
  have hrEq : sublevelComponent f leftOrientationPoint =
      sublevelComponent f r := connectedComponentIn_eq hrC
  have hcEq : sublevelComponent f leftOrientationPoint =
      sublevelComponent f h.distinguishedCluster :=
    connectedComponentIn_eq h.distinguishedCluster_mem_component
  exact hrEq.symm.trans hcEq

/-- A root in `[-1, 0]` is connected to the orientation point through the
sublevel set, including the endpoint cases `r = -1` and `r = 0`. -/
lemma root_mem_distinguishedComponent_of_nonpos {r : ℝ}
    (hr : r ∈ f.roots) (hr0 : r ≤ 0) :
    r ∈ sublevelComponent f leftOrientationPoint := by
  have hrIcc := h.admissible.root_mem_Icc hr
  have hsegment : Set.uIcc r leftOrientationPoint ⊆ sublevelSet f := by
    intro y hy
    by_cases hyr : y = r
    · rw [hyr]
      exact root_mem_sublevelSet hr
    · apply h.Ioo_neg_one_zero_subset_sublevelSet
      rw [mem_uIcc] at hy
      rcases hy with hy | hy
      · have hry : r < y := lt_of_le_of_ne hy.1 (Ne.symm hyr)
        constructor
        · linarith [hrIcc.1, hry]
        · norm_num [leftOrientationPoint] at hy
          linarith [hy.2]
      · have hyr' : y < r := lt_of_le_of_ne hy.2 hyr
        norm_num [leftOrientationPoint] at hy
        constructor <;> linarith [hy.1, hyr', hr0]
  have hconnected := isPreconnected_uIcc.subset_connectedComponentIn
    (show leftOrientationPoint ∈ Set.uIcc r leftOrientationPoint by
      exact right_mem_uIcc) hsegment
  exact hconnected left_mem_uIcc

/-- A nonpositive empirical mean forces at least one nonpositive root. -/
lemma exists_nonpositive_root : ∃ r ∈ f.roots, r ≤ 0 := by
  have hdegree_nat : 0 < f.natDegree :=
    h.admissible.monic.natDegree_pos.mpr h.admissible.ne_one
  have hdegree : 0 < (f.natDegree : ℝ) := by exact_mod_cast hdegree_nat
  have hsum : f.roots.sum ≤ 0 := by
    have hm := h.mean_nonpos
    rw [empiricalRootMean, div_le_iff₀ hdegree] at hm
    simpa using! hm
  by_contra hexists
  push_neg at hexists
  have hroots : f.roots ≠ 0 := by
    apply Multiset.card_pos.mp
    rw [h.admissible.card_roots_eq_natDegree]
    exact hdegree_nat
  have hsumpos := Multiset.sum_lt_sum_of_nonempty hroots
    (fun r hr ↦ hexists r hr)
  have : 0 < f.roots.sum := by simpa using! hsumpos
  exact (not_lt_of_ge hsum) this

/-- The distinguished cluster is nonpositive. -/
lemma distinguishedCluster_nonpos : h.distinguishedCluster ≤ 0 := by
  obtain ⟨r, hr, hr0⟩ := h.exists_nonpositive_root
  rw [← h.root_eq_distinguishedCluster_of_mem_component hr
    (h.root_mem_distinguishedComponent_of_nonpos hr hr0)]
  exact hr0

/-- The cluster in the component containing `(-1, 0)` is the leftmost root
cluster. -/
lemma distinguishedCluster_le_root {r : ℝ} (hr : r ∈ f.roots) :
    h.distinguishedCluster ≤ r := by
  rcases le_total r 0 with hr0 | h0r
  · rw [h.root_eq_distinguishedCluster_of_mem_component hr
      (h.root_mem_distinguishedComponent_of_nonpos hr hr0)]
  · exact h.distinguishedCluster_nonpos.trans h0r

/-- Translation parameter which moves the distinguished cluster to `-1`. -/
def endpointTranslation : ℝ := h.distinguishedCluster + 1

/-- The endpoint-normalized polynomial. -/
def normalizedPolynomial : Polynomial ℝ :=
  translatePolynomial f h.endpointTranslation

lemma endpointTranslation_nonneg : 0 ≤ h.endpointTranslation := by
  have hc := h.admissible.root_mem_Icc h.distinguishedCluster_mem_roots
  dsimp [endpointTranslation]
  linarith [hc.1]

lemma translated_root_mem_Icc {r : ℝ} (hr : r ∈ f.roots) :
    r - h.endpointTranslation ∈ Icc (-1 : ℝ) 1 := by
  have hrIcc := h.admissible.root_mem_Icc hr
  constructor
  · dsimp [endpointTranslation]
    linarith [h.distinguishedCluster_le_root hr]
  · linarith [hrIcc.2, h.endpointTranslation_nonneg]

lemma normalized_admissible : IsAdmissible h.normalizedPolynomial := by
  exact h.admissible.translated h.endpointTranslation
    (fun r hr ↦ h.translated_root_mem_Icc hr)

lemma normalized_componentAtomized :
    IsComponentAtomized h.normalizedPolynomial :=
  h.componentAtomized.translatePolynomial h.admissible h.endpointTranslation

lemma normalized_sublevelVolume :
    sublevelVolume h.normalizedPolynomial = sublevelVolume f :=
  sublevelVolume_translatePolynomial f h.endpointTranslation

lemma normalized_mean :
    empiricalRootMean h.normalizedPolynomial =
      empiricalRootMean f - h.endpointTranslation :=
  h.admissible.empiricalRootMean_translatePolynomial h.endpointTranslation

lemma normalized_mean_nonpos :
    empiricalRootMean h.normalizedPolynomial ≤ 0 := by
  rw [h.normalized_mean]
  linarith [h.mean_nonpos, h.endpointTranslation_nonneg]

/-- The distinguished cluster is moved exactly to `-1`. -/
lemma neg_one_mem_normalized_roots :
    (-1 : ℝ) ∈ h.normalizedPolynomial.roots := by
  rw [normalizedPolynomial,
    h.admissible.roots_translatePolynomial h.endpointTranslation]
  apply Multiset.mem_map.mpr
  refine ⟨h.distinguishedCluster, h.distinguishedCluster_mem_roots, ?_⟩
  simp [endpointTranslation]

/-- Right boundary of the translated component containing the endpoint
root `-1`. -/
def normalizedRightBoundary : ℝ :=
  sSup (sublevelComponent h.normalizedPolynomial (-1))

lemma normalized_Ioo_neg_one_zero_subset_sublevelSet :
    Ioo (-1 : ℝ) 0 ⊆ sublevelSet h.normalizedPolynomial :=
  Ioo_neg_one_zero_subset_sublevelSet_of_empiricalRootMean_nonpos
    h.normalized_admissible h.normalized_mean_nonpos

/-- The full interval `(-1,0)` belongs to the translated endpoint
component. -/
lemma normalized_Ioo_neg_one_zero_subset_component :
    Ioo (-1 : ℝ) 0 ⊆
      sublevelComponent h.normalizedPolynomial (-1) := by
  intro x hx
  have hsegment : Icc (-1 : ℝ) x ⊆
      sublevelSet h.normalizedPolynomial := by
    intro y hy
    rcases hy.1.eq_or_lt with rfl | hyneg
    · exact root_mem_sublevelSet h.neg_one_mem_normalized_roots
    · apply h.normalized_Ioo_neg_one_zero_subset_sublevelSet
      exact ⟨hyneg, hy.2.trans_lt hx.2⟩
  have hconnected := isPreconnected_Icc.subset_connectedComponentIn
    (show (-1 : ℝ) ∈ Icc (-1 : ℝ) x by exact ⟨le_rfl, hx.1.le⟩)
    hsegment
  exact hconnected ⟨hx.1.le, le_rfl⟩

lemma normalized_endpoint_component_eq_Ioo :
    sublevelComponent h.normalizedPolynomial (-1) =
      Ioo (sInf (sublevelComponent h.normalizedPolynomial (-1)))
        h.normalizedRightBoundary := by
  simpa [normalizedRightBoundary] using!
    sublevelComponent_eq_Ioo h.normalized_admissible
      (root_mem_sublevelSet h.neg_one_mem_normalized_roots)

/-- The translated endpoint component reaches at least the origin. -/
lemma normalizedRightBoundary_nonneg : 0 ≤ h.normalizedRightBoundary := by
  have hhalf : leftOrientationPoint ∈
      sublevelComponent h.normalizedPolynomial (-1) :=
    h.normalized_Ioo_neg_one_zero_subset_component
      leftOrientationPoint_mem_Ioo
  rw [h.normalized_endpoint_component_eq_Ioo] at hhalf
  by_contra hbeta
  have hbeta_neg : h.normalizedRightBoundary < 0 := lt_of_not_ge hbeta
  let x := h.normalizedRightBoundary / 2
  have hx : x ∈ Ioo (-1 : ℝ) 0 := by
    dsimp [x]
    norm_num [leftOrientationPoint] at hhalf
    constructor <;> linarith [hhalf.2, hbeta_neg]
  have hxC := h.normalized_Ioo_neg_one_zero_subset_component hx
  rw [h.normalized_endpoint_component_eq_Ioo] at hxC
  dsimp [x] at hxC
  linarith [hxC.2, hbeta_neg]

/-- Every non-endpoint root lies to the right of the endpoint component's
right boundary and remains at most `1`. -/
lemma normalized_residual_root_mem_Icc {r : ℝ}
    (hr : r ∈ endpointResidualRoots h.normalizedPolynomial) :
    r ∈ Icc h.normalizedRightBoundary 1 := by
  have hr' := mem_endpointResidualRoots.mp hr
  have hrIcc := h.normalized_admissible.root_mem_Icc hr'.1
  let a := sInf (sublevelComponent h.normalizedPolynomial (-1))
  have hcomponent : sublevelComponent h.normalizedPolynomial (-1) =
      Ioo a h.normalizedRightBoundary := by
    simpa only [a] using! h.normalized_endpoint_component_eq_Ioo
  have hnegoneC : (-1 : ℝ) ∈
      sublevelComponent h.normalizedPolynomial (-1) :=
    mem_connectedComponentIn
      (root_mem_sublevelSet h.neg_one_mem_normalized_roots)
  have ha : a < -1 := by
    rw [hcomponent] at hnegoneC
    exact hnegoneC.1
  have hrnotC : r ∉ sublevelComponent h.normalizedPolynomial (-1) := by
    intro hrC
    have hcomponents :
        sublevelComponent h.normalizedPolynomial r =
          sublevelComponent h.normalizedPolynomial (-1) :=
      (connectedComponentIn_eq hrC).symm
    exact hr'.2 (h.normalized_componentAtomized hr'.1
      h.neg_one_mem_normalized_roots hcomponents)
  have hrnotI : r ∉ Ioo a h.normalizedRightBoundary := by
    rwa [← hcomponent]
  change ¬(a < r ∧ r < h.normalizedRightBoundary) at hrnotI
  rcases not_and_or.mp hrnotI with hleft | hright
  · exact False.elim (hleft (ha.trans_le hrIcc.1))
  · exact ⟨le_of_not_gt hright, hrIcc.2⟩

lemma normalizedRightBoundary_abs_eval_eq_one :
    |h.normalizedPolynomial.eval h.normalizedRightBoundary| = 1 := by
  have hend := sublevelComponent_endpoints_frontier
    h.normalized_admissible
    (root_mem_sublevelSet h.neg_one_mem_normalized_roots)
  exact frontier_sublevelSet_abs_eval_eq_one h.normalizedPolynomial hend.2

lemma endpointMultiplicity_add_residual_card :
    endpointMultiplicity h.normalizedPolynomial +
        (endpointResidualRoots h.normalizedPolynomial).card =
      h.normalizedPolynomial.natDegree := by
  have hcard := congrArg Multiset.card
    (replicate_endpoint_add_residual h.normalizedPolynomial)
  rw [Multiset.card_add, Multiset.card_replicate,
    h.normalized_admissible.card_roots_eq_natDegree] at hcard
  exact hcard

lemma endpointMultiplicity_pos :
    0 < endpointMultiplicity h.normalizedPolynomial := by
  classical
  rw [endpointMultiplicity]
  exact Multiset.count_pos.mpr h.neg_one_mem_normalized_roots

lemma normalized_roots_sum_eq_endpoint_add_residual :
    h.normalizedPolynomial.roots.sum =
      -(endpointMultiplicity h.normalizedPolynomial : ℝ) +
        (endpointResidualRoots h.normalizedPolynomial).sum := by
  rw [← replicate_endpoint_add_residual h.normalizedPolynomial]
  simp

lemma normalized_roots_sum_nonpos :
    h.normalizedPolynomial.roots.sum ≤ 0 := by
  have hdegree : 0 < (h.normalizedPolynomial.natDegree : ℝ) := by
    exact_mod_cast (h.normalized_admissible.monic.natDegree_pos.mpr
      h.normalized_admissible.ne_one)
  have hm := h.normalized_mean_nonpos
  rw [empiricalRootMean, div_le_iff₀ hdegree] at hm
  simpa using! hm

/-- Root-product factorization into endpoint copies and residual roots. -/
lemma normalized_abs_eval_eq_endpoint_mul_residual (x : ℝ) :
    |h.normalizedPolynomial.eval x| =
      |x + 1| ^ endpointMultiplicity h.normalizedPolynomial *
        ((endpointResidualRoots h.normalizedPolynomial).map
          fun r ↦ |x - r|).prod := by
  rw [h.normalized_admissible.abs_eval_eq_prod_abs_roots,
    ← replicate_endpoint_add_residual h.normalizedPolynomial]
  simp [sub_neg_eq_add]

lemma normalized_boundary_product_identity :
    1 = (1 + h.normalizedRightBoundary) ^
          endpointMultiplicity h.normalizedPolynomial *
        ((endpointResidualRoots h.normalizedPolynomial).map
          fun r ↦ |h.normalizedRightBoundary - r|).prod := by
  calc
    1 = |h.normalizedPolynomial.eval h.normalizedRightBoundary| :=
      h.normalizedRightBoundary_abs_eval_eq_one.symm
    _ = |h.normalizedRightBoundary + 1| ^
          endpointMultiplicity h.normalizedPolynomial *
        ((endpointResidualRoots h.normalizedPolynomial).map
          fun r ↦ |h.normalizedRightBoundary - r|).prod :=
      h.normalized_abs_eval_eq_endpoint_mul_residual _
    _ = (1 + h.normalizedRightBoundary) ^
          endpointMultiplicity h.normalizedPolynomial *
        ((endpointResidualRoots h.normalizedPolynomial).map
          fun r ↦ |h.normalizedRightBoundary - r|).prod := by
      rw [abs_of_nonneg]
      · ring
      · linarith [h.normalizedRightBoundary_nonneg]

/-- Boundary-product upper bound obtained from residual support in
`[β,1]`. -/
lemma one_le_endpoint_pow_mul_one_sub_boundary_pow :
    1 ≤ (1 + h.normalizedRightBoundary) ^
          endpointMultiplicity h.normalizedPolynomial *
        (1 - h.normalizedRightBoundary) ^
          (endpointResidualRoots h.normalizedPolynomial).card := by
  have hprod :
      ((endpointResidualRoots h.normalizedPolynomial).map
        fun r ↦ |h.normalizedRightBoundary - r|).prod ≤
        (1 - h.normalizedRightBoundary) ^
          (endpointResidualRoots h.normalizedPolynomial).card := by
    have hmap := Multiset.prod_map_le_prod_map₀
      (s := endpointResidualRoots h.normalizedPolynomial)
      (fun r ↦ |h.normalizedRightBoundary - r|)
      (fun _ ↦ 1 - h.normalizedRightBoundary)
      (fun r hr ↦ abs_nonneg _)
      (fun r hr ↦ by
        change |h.normalizedRightBoundary - r| ≤
          1 - h.normalizedRightBoundary
        have hrIcc := h.normalized_residual_root_mem_Icc hr
        rw [abs_of_nonpos (sub_nonpos.mpr hrIcc.1)]
        linarith [hrIcc.2])
    simpa using! hmap
  calc
    1 = (1 + h.normalizedRightBoundary) ^
          endpointMultiplicity h.normalizedPolynomial *
        ((endpointResidualRoots h.normalizedPolynomial).map
          fun r ↦ |h.normalizedRightBoundary - r|).prod :=
      h.normalized_boundary_product_identity
    _ ≤ (1 + h.normalizedRightBoundary) ^
          endpointMultiplicity h.normalizedPolynomial *
        (1 - h.normalizedRightBoundary) ^
          (endpointResidualRoots h.normalizedPolynomial).card :=
      mul_le_mul_of_nonneg_left hprod
        (pow_nonneg (by linarith [h.normalizedRightBoundary_nonneg]) _)

lemma normalizedRightBoundary_le_one_of_residual_ne_zero
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    h.normalizedRightBoundary ≤ 1 := by
  have hcard : 0 < (endpointResidualRoots h.normalizedPolynomial).card :=
    Multiset.card_pos.mpr hres
  obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
  have hrIcc := h.normalized_residual_root_mem_Icc hr
  exact hrIcc.1.trans hrIcc.2

/-- The degenerate boundary case `β = 0`: the boundary product forces
every residual root to equal `1`, and the nonpositive mean then gives at
least half of the roots at `-1`. -/
lemma natDegree_le_twice_endpointMultiplicity_of_boundary_eq_zero
    (hbeta : h.normalizedRightBoundary = 0) :
    h.normalizedPolynomial.natDegree ≤
      2 * endpointMultiplicity h.normalizedPolynomial := by
  let s := endpointResidualRoots h.normalizedPolynomial
  have hprod_abs : (s.map fun r ↦ |r|).prod = 1 := by
    simpa [s, hbeta, abs_neg] using!
      h.normalized_boundary_product_identity.symm
  have hmap : (s.map fun r ↦ |r|) = s := by
    calc
      (s.map fun r ↦ |r|) = s.map id := by
        apply Multiset.map_congr rfl
        intro r hr
        change |r| = id r
        have hrIcc := h.normalized_residual_root_mem_Icc
          (by simpa [s] using! hr)
        have hr0 : 0 ≤ r := by
          rw [← hbeta]
          exact hrIcc.1
        simp [id, abs_of_nonneg hr0]
      _ = s := Multiset.map_id s
  rw [hmap] at hprod_abs
  have hs : s = Multiset.replicate s.card (1 : ℝ) :=
    multiset_eq_replicate_one_of_mem_Icc_of_prod_eq_one
      (fun r hr ↦ by
        have hrIcc := h.normalized_residual_root_mem_Icc
          (by simpa [s] using! hr)
        exact ⟨by linarith [hrIcc.1, hbeta], hrIcc.2⟩)
      hprod_abs
  have hs_sum : s.sum = (s.card : ℝ) := by
    rw [hs]
    simp
  have hcard_real : (s.card : ℝ) ≤
      (endpointMultiplicity h.normalizedPolynomial : ℝ) := by
    have hsum := h.normalized_roots_sum_nonpos
    rw [h.normalized_roots_sum_eq_endpoint_add_residual] at hsum
    change -(endpointMultiplicity h.normalizedPolynomial : ℝ) + s.sum ≤ 0 at hsum
    linarith [hs_sum]
  have hcard_nat : s.card ≤ endpointMultiplicity h.normalizedPolynomial := by
    exact_mod_cast hcard_real
  have htotal := h.endpointMultiplicity_add_residual_card
  change endpointMultiplicity h.normalizedPolynomial + s.card =
    h.normalizedPolynomial.natDegree at htotal
  omega

/-- For a positive right boundary, the boundary product itself rules out
endpoint multiplicity below one half. -/
lemma natDegree_le_twice_endpointMultiplicity_of_boundary_pos
    (hbeta : 0 < h.normalizedRightBoundary) :
    h.normalizedPolynomial.natDegree ≤
      2 * endpointMultiplicity h.normalizedPolynomial := by
  by_cases hres : endpointResidualRoots h.normalizedPolynomial = 0
  · have htotal := h.endpointMultiplicity_add_residual_card
    rw [hres, Multiset.card_zero, add_zero] at htotal
    omega
  · have hbeta_le := h.normalizedRightBoundary_le_one_of_residual_ne_zero hres
    by_contra hdegree
    have htotal := h.endpointMultiplicity_add_residual_card
    have hklt : endpointMultiplicity h.normalizedPolynomial <
        (endpointResidualRoots h.normalizedPolynomial).card := by
      omega
    have hdiff : 0 <
        (endpointResidualRoots h.normalizedPolynomial).card -
          endpointMultiplicity h.normalizedPolynomial :=
      Nat.sub_pos_iff_lt.mpr hklt
    have hq0 : 0 ≤ 1 - h.normalizedRightBoundary := by linarith
    have hq1 : 1 - h.normalizedRightBoundary < 1 := by linarith
    have hqpow :
        (1 - h.normalizedRightBoundary) ^
            ((endpointResidualRoots h.normalizedPolynomial).card -
              endpointMultiplicity h.normalizedPolynomial) < 1 :=
      pow_lt_one₀ hq0 hq1 hdiff.ne'
    have hp0 : 0 ≤
        (1 + h.normalizedRightBoundary) *
          (1 - h.normalizedRightBoundary) :=
      mul_nonneg (by linarith) hq0
    have hp1 :
        (1 + h.normalizedRightBoundary) *
            (1 - h.normalizedRightBoundary) ≤ 1 := by
      nlinarith [sq_nonneg h.normalizedRightBoundary]
    have hppow :
        ((1 + h.normalizedRightBoundary) *
          (1 - h.normalizedRightBoundary)) ^
            endpointMultiplicity h.normalizedPolynomial ≤ 1 :=
      pow_le_one₀ hp0 hp1
    have hrearrange :
        (1 + h.normalizedRightBoundary) ^
              endpointMultiplicity h.normalizedPolynomial *
            (1 - h.normalizedRightBoundary) ^
              (endpointResidualRoots h.normalizedPolynomial).card =
          ((1 + h.normalizedRightBoundary) *
              (1 - h.normalizedRightBoundary)) ^
                endpointMultiplicity h.normalizedPolynomial *
            (1 - h.normalizedRightBoundary) ^
              ((endpointResidualRoots h.normalizedPolynomial).card -
                endpointMultiplicity h.normalizedPolynomial) := by
      have hm : (endpointResidualRoots h.normalizedPolynomial).card =
          endpointMultiplicity h.normalizedPolynomial +
            ((endpointResidualRoots h.normalizedPolynomial).card -
              endpointMultiplicity h.normalizedPolynomial) := by omega
      conv_lhs =>
        rw [hm, pow_add]
      conv_rhs =>
        rw [mul_pow]
      ring
    have hrhs_lt :
        (1 + h.normalizedRightBoundary) ^
              endpointMultiplicity h.normalizedPolynomial *
            (1 - h.normalizedRightBoundary) ^
              (endpointResidualRoots h.normalizedPolynomial).card < 1 := by
      rw [hrearrange]
      calc
        ((1 + h.normalizedRightBoundary) *
              (1 - h.normalizedRightBoundary)) ^
                endpointMultiplicity h.normalizedPolynomial *
            (1 - h.normalizedRightBoundary) ^
              ((endpointResidualRoots h.normalizedPolynomial).card -
                endpointMultiplicity h.normalizedPolynomial) ≤
            1 * (1 - h.normalizedRightBoundary) ^
              ((endpointResidualRoots h.normalizedPolynomial).card -
                endpointMultiplicity h.normalizedPolynomial) :=
          mul_le_mul_of_nonneg_right hppow (pow_nonneg hq0 _)
        _ < 1 := by simpa using! hqpow
    exact (not_lt_of_ge
      h.one_le_endpoint_pow_mul_one_sub_boundary_pow) hrhs_lt

/-- The endpoint cluster contains at least half of all root occurrences,
with the `β = 0` boundary case handled separately above. -/
theorem natDegree_le_twice_endpointMultiplicity :
    h.normalizedPolynomial.natDegree ≤
      2 * endpointMultiplicity h.normalizedPolynomial := by
  rcases h.normalizedRightBoundary_nonneg.eq_or_lt with hbeta | hbeta
  · exact h.natDegree_le_twice_endpointMultiplicity_of_boundary_eq_zero
      hbeta.symm
  · exact h.natDegree_le_twice_endpointMultiplicity_of_boundary_pos hbeta

/-- Endpoint multiplicity fraction `A` is at least `1/2`. -/
theorem endpointMultiplicityFraction_ge_half :
    (1 / 2 : ℝ) ≤ endpointMultiplicityFraction h.normalizedPolynomial := by
  have hdegree : 0 < (h.normalizedPolynomial.natDegree : ℝ) := by
    exact_mod_cast (h.normalized_admissible.monic.natDegree_pos.mpr
      h.normalized_admissible.ne_one)
  rw [endpointMultiplicityFraction, le_div_iff₀ hdegree]
  have hcast : (h.normalizedPolynomial.natDegree : ℝ) ≤
      2 * (endpointMultiplicity h.normalizedPolynomial : ℝ) := by
    exact_mod_cast h.natDegree_le_twice_endpointMultiplicity
  norm_num
  linarith

end EndpointNormalizationHypotheses

end

end Erdos1038
