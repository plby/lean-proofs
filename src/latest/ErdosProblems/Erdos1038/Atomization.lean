import ErdosProblems.Erdos1038.SublevelComponents
import ErdosProblems.Erdos1038.BarycentricCollapse

/-!
# Simultaneous empirical atomization

For every occurrence of a root of an admissible polynomial, we look at the
connected component of the strict unit sublevel set containing that root.
All occurrences in one component are replaced simultaneously by the
barycenter of the roots in that component.  Multiplicities are retained.

The main result is that this operation can only shrink the strict unit
sublevel set.  Its proof partitions the root multiset by old sublevel
components and applies the local Jensen inequality from
`BarycentricCollapse.lean` on every fiber.
-/

open scoped BigOperators ENNReal Real
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- The root occurrences lying in the same old sublevel component as `r`.
The definition retains multiplicities. -/
def componentRootMultiset (f : Polynomial ℝ) (r : ℝ) : Multiset ℝ :=
  by
    classical
    exact f.roots.filter fun t ↦ sublevelComponent f t = sublevelComponent f r

/-- The empirical barycenter of the roots in the old component of `r`. -/
def componentBarycenter (f : Polynomial ℝ) (r : ℝ) : ℝ :=
  multisetBarycenter (componentRootMultiset f r)

/-- The root multiset after replacing each occurrence by the barycenter of
its old sublevel component. -/
def atomizedRootMultiset (f : Polynomial ℝ) : Multiset ℝ :=
  f.roots.map (componentBarycenter f)

/-- The monic polynomial having the simultaneously atomized root multiset. -/
def atomizedPolynomial (f : Polynomial ℝ) : Polynomial ℝ :=
  ((atomizedRootMultiset f).map fun c ↦ X - C c).prod

/-- The finite set of old sublevel components which contain a root.  For an
admissible polynomial this represents the full component family. -/
def rootComponentFinset (f : Polynomial ℝ) : Finset (Set ℝ) := by
  classical
  exact (f.roots.map (sublevelComponent f)).toFinset

/-- Root occurrences in a specified old component, retaining
multiplicities. -/
def rootsInOldComponent (f : Polynomial ℝ) (D : Set ℝ) : Multiset ℝ := by
  classical
  exact f.roots.filter fun r ↦ sublevelComponent f r = D

@[simp]
lemma mem_rootComponentFinset {f : Polynomial ℝ} {D : Set ℝ} :
    D ∈ rootComponentFinset f ↔
      ∃ r ∈ f.roots, sublevelComponent f r = D := by
  classical
  simp [rootComponentFinset]

/-- For an admissible polynomial, the finite component index used by the
atomization is exactly the full old sublevel-component family. -/
theorem coe_rootComponentFinset {f : Polynomial ℝ} (hf : IsAdmissible f) :
    (rootComponentFinset f : Set (Set ℝ)) = sublevelComponentFamily f := by
  rw [sublevelComponentFamily_eq_image_rootSet hf]
  ext D
  simp [mem_rootSet_iff]

@[simp]
lemma mem_componentRootMultiset {f : Polynomial ℝ} {r t : ℝ} :
    t ∈ componentRootMultiset f r ↔
      t ∈ f.roots ∧ sublevelComponent f t = sublevelComponent f r := by
  classical
  simp [componentRootMultiset]

lemma componentRootMultiset_ne_zero {f : Polynomial ℝ} {r : ℝ}
    (hr : r ∈ f.roots) : componentRootMultiset f r ≠ 0 := by
  intro hzero
  have hr' : r ∈ componentRootMultiset f r :=
    mem_componentRootMultiset.mpr ⟨hr, rfl⟩
  rw [hzero] at hr'
  simp at hr'

/-- Every root selected into the fiber of `r` really lies in the old
component of `r`. -/
lemma componentRootMultiset_mem_component {f : Polynomial ℝ} {r t : ℝ}
    (ht : t ∈ componentRootMultiset f r) : t ∈ sublevelComponent f r := by
  have ht' := mem_componentRootMultiset.mp ht
  have hself : t ∈ sublevelComponent f t :=
    mem_connectedComponentIn (root_mem_sublevelSet ht'.1)
  rw [ht'.2] at hself
  exact hself

/-- The barycenter assigned to a root remains in that root's old sublevel
component. -/
lemma componentBarycenter_mem_component {f : Polynomial ℝ}
    (hf : IsAdmissible f) {r : ℝ} (hr : r ∈ f.roots) :
    componentBarycenter f r ∈ sublevelComponent f r := by
  have hrE := root_mem_sublevelSet hr
  rw [sublevelComponent_eq_Ioo hf hrE]
  exact multisetBarycenter_mem_Ioo (componentRootMultiset_ne_zero hr) fun t ht ↦ by
    rw [← sublevelComponent_eq_Ioo hf hrE]
    exact componentRootMultiset_mem_component ht

lemma componentBarycenter_mem_sublevelSet {f : Polynomial ℝ}
    (hf : IsAdmissible f) {r : ℝ} (hr : r ∈ f.roots) :
    componentBarycenter f r ∈ sublevelSet f :=
  connectedComponentIn_subset _ _ (componentBarycenter_mem_component hf hr)

/-- A closed-interval version of the elementary barycenter containment
fact. -/
lemma multisetBarycenter_mem_Icc {s : Multiset ℝ} {a b : ℝ}
    (hs : s ≠ 0) (hmem : ∀ r ∈ s, r ∈ Icc a b) :
    multisetBarycenter s ∈ Icc a b := by
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast (Multiset.card_pos.mpr hs)
  constructor
  · rw [multisetBarycenter, le_div_iff₀ hcard]
    have hlo := Multiset.card_nsmul_le_sum
      (s := s) (a := a) (fun r hr ↦ (hmem r hr).1)
    simpa [nsmul_eq_mul, mul_comm] using! hlo
  · rw [multisetBarycenter, div_le_iff₀ hcard]
    have hhi := Multiset.sum_le_card_nsmul s b
      (fun r hr ↦ (hmem r hr).2)
    simpa [nsmul_eq_mul, mul_comm] using! hhi

/-- Atomization preserves the stipulated root-support interval. -/
lemma componentBarycenter_mem_Icc {f : Polynomial ℝ}
    (hf : IsAdmissible f) {r : ℝ} (hr : r ∈ f.roots) :
    componentBarycenter f r ∈ Icc (-1 : ℝ) 1 := by
  apply multisetBarycenter_mem_Icc (componentRootMultiset_ne_zero hr)
  intro t ht
  exact hf.root_mem_Icc (mem_componentRootMultiset.mp ht).1

lemma componentRootMultiset_eq_of_component_eq {f : Polynomial ℝ}
    {r s : ℝ} (h : sublevelComponent f r = sublevelComponent f s) :
    componentRootMultiset f r = componentRootMultiset f s := by
  classical
  simp [componentRootMultiset, h]

/-- All roots in one old component are sent to exactly the same atom. -/
lemma componentBarycenter_eq_of_component_eq {f : Polynomial ℝ}
    {r s : ℝ} (h : sublevelComponent f r = sublevelComponent f s) :
    componentBarycenter f r = componentBarycenter f s := by
  rw [componentBarycenter, componentBarycenter,
    componentRootMultiset_eq_of_component_eq h]

lemma componentBarycenter_eq_of_mem_component {f : Polynomial ℝ}
    {r s : ℝ} (hs : s ∈ sublevelComponent f r) :
    componentBarycenter f r = componentBarycenter f s :=
  componentBarycenter_eq_of_component_eq (connectedComponentIn_eq hs)

/-- The atom assigned to `r` represents the same old component as `r`. -/
lemma sublevelComponent_componentBarycenter {f : Polynomial ℝ}
    (hf : IsAdmissible f) {r : ℝ} (hr : r ∈ f.roots) :
    sublevelComponent f (componentBarycenter f r) = sublevelComponent f r := by
  exact (connectedComponentIn_eq (componentBarycenter_mem_component hf hr)).symm

/-- Atoms belonging to distinct old components are distinct. -/
lemma componentBarycenter_ne_of_component_ne {f : Polynomial ℝ}
    (hf : IsAdmissible f) {r s : ℝ} (hr : r ∈ f.roots)
    (hs : s ∈ f.roots)
    (h : sublevelComponent f r ≠ sublevelComponent f s) :
    componentBarycenter f r ≠ componentBarycenter f s := by
  intro heq
  apply h
  rw [← sublevelComponent_componentBarycenter hf hr,
    ← sublevelComponent_componentBarycenter hf hs, heq]

lemma componentBarycenter_mem_component_iff {f : Polynomial ℝ}
    (hf : IsAdmissible f) {r s : ℝ} (hs : s ∈ f.roots) :
    componentBarycenter f s ∈ sublevelComponent f r ↔
      sublevelComponent f s = sublevelComponent f r := by
  constructor
  · intro hmem
    have hrc : sublevelComponent f r =
        sublevelComponent f (componentBarycenter f s) :=
      connectedComponentIn_eq hmem
    rw [sublevelComponent_componentBarycenter hf hs] at hrc
    exact hrc.symm
  · intro hcomp
    rw [← hcomp]
    exact componentBarycenter_mem_component hf hs

/-- The atomized root occurrences which lie in the old component of `r`. -/
def atomizedRootsInComponent (f : Polynomial ℝ) (r : ℝ) : Multiset ℝ := by
  classical
  exact (atomizedRootMultiset f).filter
    (fun c ↦ c ∈ sublevelComponent f r)

/-- In each old component, the atomized multiset has exactly the old total
multiplicity, concentrated at that component's barycenter. -/
theorem atomizedRootMultiset_filter_component {f : Polynomial ℝ}
    (hf : IsAdmissible f) (r : ℝ) :
    atomizedRootsInComponent f r =
      Multiset.replicate (componentRootMultiset f r).card
        (componentBarycenter f r) := by
  classical
  rw [atomizedRootsInComponent, atomizedRootMultiset, Multiset.filter_map]
  have hfilter :
      f.roots.filter
          ((fun c ↦ c ∈ sublevelComponent f r) ∘ componentBarycenter f) =
        componentRootMultiset f r := by
    apply Multiset.filter_congr
    intro s hs
    exact componentBarycenter_mem_component_iff hf hs
  rw [hfilter, Multiset.eq_replicate]
  constructor
  · simp
  · intro c hc
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hc
    exact componentBarycenter_eq_of_component_eq
      (mem_componentRootMultiset.mp hs).2

@[simp]
theorem roots_atomizedPolynomial (f : Polynomial ℝ) :
    (atomizedPolynomial f).roots = atomizedRootMultiset f := by
  simp [atomizedPolynomial]

theorem atomizedPolynomial_monic (f : Polynomial ℝ) :
    (atomizedPolynomial f).Monic := by
  exact Polynomial.monic_multisetProd_X_sub_C (atomizedRootMultiset f)

@[simp]
lemma card_atomizedRootMultiset (f : Polynomial ℝ) :
    (atomizedRootMultiset f).card = f.roots.card := by
  simp [atomizedRootMultiset]

@[simp]
theorem natDegree_atomizedPolynomial (f : Polynomial ℝ) :
    (atomizedPolynomial f).natDegree = f.roots.card := by
  simp [atomizedPolynomial]

theorem natDegree_atomizedPolynomial_eq {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    (atomizedPolynomial f).natDegree = f.natDegree := by
  rw [natDegree_atomizedPolynomial, hf.card_roots_eq_natDegree]

/-- Simultaneous atomization remains in the admissible class. -/
theorem isAdmissible_atomizedPolynomial {f : Polynomial ℝ}
    (hf : IsAdmissible f) : IsAdmissible (atomizedPolynomial f) := by
  refine ⟨atomizedPolynomial_monic f, ?_, ?_⟩
  · intro hone
    have hzero : (atomizedPolynomial f).natDegree = 0 :=
      (atomizedPolynomial_monic f).natDegree_eq_zero.mpr hone
    rw [natDegree_atomizedPolynomial_eq hf] at hzero
    exact (hf.monic.natDegree_eq_zero.not.mpr hf.ne_one) hzero
  · rw [roots_atomizedPolynomial, natDegree_atomizedPolynomial_eq hf]
    have hfilter :
        (atomizedRootMultiset f).filter (fun x ↦ x ∈ Icc (-1 : ℝ) 1) =
          atomizedRootMultiset f := by
      apply Multiset.filter_eq_self.mpr
      intro c hc
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hc
      exact componentBarycenter_mem_Icc hf hr
    rw [hfilter, card_atomizedRootMultiset, hf.card_roots_eq_natDegree]

/-- Summing over all fibers of a finite multiset recovers the original
sum.  This formulation is useful because the fiber labels need not form a
pre-existing finite type. -/
private lemma multiset_sum_fibers {α β : Type*} [DecidableEq β]
    (s : Multiset α)
    (κ : α → β) (w : α → ℝ) :
    ∑ c ∈ (s.map κ).toFinset,
        ((s.filter fun a ↦ κ a = c).map w).sum =
      (s.map w).sum := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have hfiber (c : β) :
          (((a ::ₘ s).filter fun x ↦ κ x = c).map w).sum =
            (if κ a = c then w a else 0) +
              ((s.filter fun x ↦ κ x = c).map w).sum := by
        by_cases h : κ a = c <;> simp [h]
      simp only [Multiset.map_cons, Multiset.toFinset_cons, Multiset.sum_cons]
      calc
        ∑ c ∈ insert (κ a) (s.map κ).toFinset,
              (((a ::ₘ s).filter fun x ↦ κ x = c).map w).sum =
            ∑ c ∈ insert (κ a) (s.map κ).toFinset,
              ((if κ a = c then w a else 0) +
                ((s.filter fun x ↦ κ x = c).map w).sum) := by
          apply Finset.sum_congr rfl
          intro c hc
          exact hfiber c
        _ = w a + (s.map w).sum := by
          by_cases ha : κ a ∈ (s.map κ).toFinset
          · simp [Finset.sum_add_distrib, ha, ih]
          · have hnot : ∀ x ∈ s, κ x ≠ κ a := by
              intro x hx hxa
              apply ha
              have hxmap : κ x ∈ s.map κ :=
                Multiset.mem_map.mpr ⟨x, hx, rfl⟩
              have hxfin : κ x ∈ (s.map κ).toFinset := by
                simpa using! hxmap
              rwa [hxa] at hxfin
            have hzero : s.filter (fun x ↦ κ x = κ a) = 0 := by
              rw [Multiset.eq_zero_iff_forall_notMem]
              intro x hx
              exact hnot x (Multiset.mem_filter.mp hx).1
                (Multiset.mem_filter.mp hx).2
            simp [Finset.sum_add_distrib, ha, hzero, ih]

private lemma sum_root_component_fibers (f : Polynomial ℝ) (w : ℝ → ℝ) :
    ∑ D ∈ rootComponentFinset f,
        ((rootsInOldComponent f D).map w).sum = (f.roots.map w).sum := by
  classical
  simpa [rootComponentFinset, rootsInOldComponent] using!
    multiset_sum_fibers f.roots (sublevelComponent f) w

/-- Jensen's inequality on one fiber of the partition by old sublevel
components. -/
private lemma component_fiber_log_inequality {f : Polynomial ℝ}
    (hf : IsAdmissible f) {x : ℝ}
    (hx : x ∉ sublevelSet f) {D : Set ℝ}
    (hD : D ∈ rootComponentFinset f) :
    ((rootsInOldComponent f D).map fun r ↦ Real.log |x - r|).sum ≤
      ((rootsInOldComponent f D).map fun r ↦
        Real.log |x - componentBarycenter f r|).sum := by
  classical
  have hD' : D ∈ f.roots.map (sublevelComponent f) := by
    simpa [rootComponentFinset] using! hD
  obtain ⟨r, hr, hrD⟩ := Multiset.mem_map.mp hD'
  have hfiber :
      rootsInOldComponent f D = componentRootMultiset f r := by
    rw [rootsInOldComponent, componentRootMultiset]
    apply Multiset.filter_congr
    intro t ht
    rw [hrD]
  let a := sInf (sublevelComponent f r)
  let b := sSup (sublevelComponent f r)
  have hrE := root_mem_sublevelSet hr
  have hcomponent : sublevelComponent f r = Ioo a b := by
    simpa only [a, b] using! sublevelComponent_eq_Ioo hf hrE
  have hmem : ∀ t ∈ componentRootMultiset f r, t ∈ Ioo a b := by
    intro t ht
    rw [← hcomponent]
    exact componentRootMultiset_mem_component ht
  have hxnotI : x ∉ Ioo a b := by
    intro hxI
    apply hx
    have hxcomp : x ∈ sublevelComponent f r :=
      (Set.ext_iff.mp hcomponent x).mpr hxI
    exact connectedComponentIn_subset (sublevelSet f) r hxcomp
  have hxext : x ≤ a ∨ b ≤ x := by
    rcases not_and_or.mp hxnotI with hleft | hright
    · exact Or.inl (le_of_not_gt hleft)
    · exact Or.inr (le_of_not_gt hright)
  have hlocal := sum_log_abs_sub_le_card_mul_log_abs_sub_barycenter
    (componentRootMultiset_ne_zero hr) hmem hxext
  have hconstant :
      ((componentRootMultiset f r).map
          fun t ↦ Real.log |x - componentBarycenter f t|).sum =
        (componentRootMultiset f r).card *
          Real.log |x - componentBarycenter f r| := by
    have hmap :
        (componentRootMultiset f r).map
            (fun t ↦ Real.log |x - componentBarycenter f t|) =
          (componentRootMultiset f r).map
            (fun _ ↦ Real.log |x - componentBarycenter f r|) := by
      apply Multiset.map_congr rfl
      intro t ht
      rw [componentBarycenter_eq_of_component_eq
        (mem_componentRootMultiset.mp ht).2]
    rw [hmap]
    simp [nsmul_eq_mul]
  calc
    ((rootsInOldComponent f D).map fun t ↦ Real.log |x - t|).sum =
        ((componentRootMultiset f r).map
          fun t ↦ Real.log |x - t|).sum := by rw [hfiber]
    _ ≤ (componentRootMultiset f r).card *
        Real.log |x - componentBarycenter f r| := hlocal
    _ = ((componentRootMultiset f r).map
        fun t ↦ Real.log |x - componentBarycenter f t|).sum :=
      hconstant.symm
    _ = ((rootsInOldComponent f D).map fun t ↦
        Real.log |x - componentBarycenter f t|).sum := by rw [hfiber]

/-- Outside the old strict unit sublevel set, simultaneous atomization
weakly raises the total logarithmic potential of the roots. -/
theorem sum_log_abs_sub_roots_le_atomized {f : Polynomial ℝ}
    (hf : IsAdmissible f) {x : ℝ} (hx : x ∉ sublevelSet f) :
    (f.roots.map fun r ↦ Real.log |x - r|).sum ≤
      (f.roots.map fun r ↦
        Real.log |x - componentBarycenter f r|).sum := by
  classical
  rw [← sum_root_component_fibers f
      (fun r ↦ Real.log |x - r|),
    ← sum_root_component_fibers f
      (fun r ↦ Real.log |x - componentBarycenter f r|)]
  apply Finset.sum_le_sum
  intro D hD
  exact component_fiber_log_inequality hf hx hD

/-- Pointwise polynomial form of the simultaneous Jensen inequality.  At
every point outside the old sublevel set, the atomized polynomial has at
least as large an absolute value. -/
theorem abs_eval_le_atomized_of_not_mem {f : Polynomial ℝ}
    (hf : IsAdmissible f) {x : ℝ} (hx : x ∉ sublevelSet f) :
    |f.eval x| ≤ |(atomizedPolynomial f).eval x| := by
  have hxroot : ∀ r ∈ f.roots, x ≠ r := by
    intro r hr hxr
    apply hx
    rw [hxr]
    exact root_mem_sublevelSet hr
  have hxatom : ∀ r ∈ f.roots, x ≠ componentBarycenter f r := by
    intro r hr hxr
    apply hx
    rw [hxr]
    exact componentBarycenter_mem_sublevelSet hf hr
  have horig_ne :
      ∀ y ∈ f.roots.map (fun r ↦ |x - r|), y ≠ 0 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
    exact abs_ne_zero.mpr (sub_ne_zero.mpr (hxroot r hr))
  have hatom_ne :
      ∀ y ∈ f.roots.map
        (fun r ↦ |x - componentBarycenter f r|), y ≠ 0 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
    exact abs_ne_zero.mpr (sub_ne_zero.mpr (hxatom r hr))
  have hsum :
      ((f.roots.map fun r ↦ |x - r|).map Real.log).sum ≤
        ((f.roots.map fun r ↦
          |x - componentBarycenter f r|).map Real.log).sum := by
    simpa only [Multiset.map_map, Function.comp_apply] using!
      sum_log_abs_sub_roots_le_atomized hf hx
  have hlogprod :
      Real.log (f.roots.map (fun r ↦ |x - r|)).prod ≤
        Real.log (f.roots.map
          (fun r ↦ |x - componentBarycenter f r|)).prod := by
    calc
      Real.log (f.roots.map (fun r ↦ |x - r|)).prod =
          ((f.roots.map fun r ↦ |x - r|).map Real.log).sum :=
        Real.log_multiset_prod horig_ne
      _ ≤ ((f.roots.map fun r ↦
          |x - componentBarycenter f r|).map Real.log).sum := hsum
      _ = Real.log (f.roots.map
          (fun r ↦ |x - componentBarycenter f r|)).prod :=
        (Real.log_multiset_prod hatom_ne).symm
  have horig_pos :
      0 < (f.roots.map (fun r ↦ |x - r|)).prod := by
    apply Multiset.prod_pos
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
    exact abs_pos.mpr (sub_ne_zero.mpr (hxroot r hr))
  have hatom_pos :
      0 < (f.roots.map
        (fun r ↦ |x - componentBarycenter f r|)).prod := by
    apply Multiset.prod_pos
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
    exact abs_pos.mpr (sub_ne_zero.mpr (hxatom r hr))
  have hprod := Real.exp_le_exp.mpr hlogprod
  rw [Real.exp_log horig_pos, Real.exp_log hatom_pos] at hprod
  calc
    |f.eval x| = (f.roots.map fun r ↦ |x - r|).prod :=
      hf.abs_eval_eq_prod_abs_roots x
    _ ≤ (f.roots.map
        (fun r ↦ |x - componentBarycenter f r|)).prod := hprod
    _ = |(atomizedPolynomial f).eval x| := by
      rw [(isAdmissible_atomizedPolynomial hf).abs_eval_eq_prod_abs_roots]
      simp only [roots_atomizedPolynomial, atomizedRootMultiset,
        Multiset.map_map, Function.comp_apply]

/-- Simultaneous empirical atomization can only shrink the strict unit
sublevel set. -/
theorem sublevelSet_atomized_subset {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    sublevelSet (atomizedPolynomial f) ⊆ sublevelSet f := by
  intro x hxatom
  by_contra hxold
  apply hxold
  change |f.eval x| < 1
  exact (abs_eval_le_atomized_of_not_mem hf hxold).trans_lt hxatom

/-- Consequently, simultaneous atomization does not increase sublevel
volume. -/
theorem sublevelVolume_atomized_le {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    sublevelVolume (atomizedPolynomial f) ≤ sublevelVolume f := by
  exact measure_mono (sublevelSet_atomized_subset hf)

/-- Replacing every component's root occurrences by their barycenter
preserves the total sum of the root multiset. -/
theorem sum_atomizedRootMultiset (f : Polynomial ℝ) :
    (atomizedRootMultiset f).sum = f.roots.sum := by
  classical
  rw [atomizedRootMultiset]
  rw [← sum_root_component_fibers f (componentBarycenter f)]
  have hid :
      ∑ D ∈ rootComponentFinset f,
          ((rootsInOldComponent f D).map id).sum = f.roots.sum := by
    simpa using! sum_root_component_fibers f id
  rw [← hid]
  apply Finset.sum_congr rfl
  intro D hD
  obtain ⟨r, hr, hrD⟩ := mem_rootComponentFinset.mp hD
  have hfiber : rootsInOldComponent f D = componentRootMultiset f r := by
    rw [rootsInOldComponent, componentRootMultiset]
    apply Multiset.filter_congr
    intro t ht
    rw [hrD]
  rw [hfiber]
  have hmap :
      (componentRootMultiset f r).map (componentBarycenter f) =
        (componentRootMultiset f r).map
          (fun _ ↦ componentBarycenter f r) := by
    apply Multiset.map_congr rfl
    intro t ht
    exact componentBarycenter_eq_of_component_eq
      (mem_componentRootMultiset.mp ht).2
  rw [hmap]
  have hcard : ((componentRootMultiset f r).card : ℝ) ≠ 0 := by
    exact_mod_cast (Multiset.card_pos.mpr
      (componentRootMultiset_ne_zero hr)).ne'
  simp [componentBarycenter, multisetBarycenter, nsmul_eq_mul]
  field_simp [hcard]

end

end Erdos1038
