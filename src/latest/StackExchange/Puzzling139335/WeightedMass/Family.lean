import StackExchange.Puzzling139335.WeightedMass.Basic

/-!
# Weighted mass of a finite regular-closed dissection

Triple-contact finiteness is an explicit hypothesis of these measure-theoretic
helpers. The geometric Jordan argument supplying it is separate.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335

noncomputable section

variable {X ι : Type*} [TopologicalSpace X]

/-- Points belonging to three distinct members of a family of regions. -/
def tripleContactSet (P : ι → Set X) : Set X :=
  {x | ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ x ∈ P i ∧ x ∈ P j ∧ x ∈ P k}

/-- Disjoint interiors of regular-closed regions also separate each interior
from the entire other region. -/
theorem disjoint_interior_piece_of_regular
    (P : ι → Set X) (hreg : ∀ i, closure (interior (P i)) = P i)
    (hdisj : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {i j : ι} (hij : i ≠ j) : Disjoint (interior (P i)) (P j) := by
  have h := (hdisj hij).closure_right isOpen_interior
  simpa only [hreg j] using h

/-- A point of the ambient interior belonging to only one closed piece is
in that piece's interior. -/
theorem mem_interior_of_unique_piece [Finite ι]
    (P : ι → Set X) {S : Set X} (hclosed : ∀ i, IsClosed (P i))
    (hcover : (⋃ i, P i) = S) {x : X} (hx : x ∈ interior S)
    {i : ι} (hunique : ∀ j, x ∈ P j → j = i) : x ∈ interior (P i) := by
  classical
  let V : Set X := ⋃ j : {j : ι // j ≠ i}, P j.val
  have hV : IsClosed V :=
    isClosed_iUnion_of_finite (fun j : {j : ι // j ≠ i} => hclosed j.val)
  have hxV : x ∉ V := by
    intro hxV
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxV
    exact j.property (hunique j.val hj)
  have hopen : IsOpen (interior S ∩ Vᶜ) := isOpen_interior.inter hV.isOpen_compl
  refine mem_interior.mpr ⟨interior S ∩ Vᶜ, ?_, hopen, ⟨hx, hxV⟩⟩
  intro y hy
  have hyS : y ∈ ⋃ j, P j := by
    rw [hcover]
    exact interior_subset hy.1
  obtain ⟨j, hj⟩ := mem_iUnion.mp hyS
  by_cases hji : j = i
  · simpa only [hji] using hj
  · exact False.elim (hy.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩))

theorem exists_other_piece_at_frontier [Finite ι]
    (P : ι → Set X) {S : Set X} (hclosed : ∀ i, IsClosed (P i))
    (hcover : (⋃ i, P i) = S) {x : X} (hxS : x ∈ interior S)
    {i : ι} (hx : x ∈ frontier (P i)) : ∃ j, j ≠ i ∧ x ∈ P j := by
  by_contra h
  have huniq : ∀ j, x ∈ P j → j = i := by
    intro j hj
    by_contra hji
    exact h ⟨j, hji, hj⟩
  exact hx.2 (mem_interior_of_unique_piece P hclosed hcover hxS huniq)

variable [Fintype ι]

/-- At an interior point outside the triple-contact set, the densities add
to one, without any boundary regularity or measure hypothesis. -/
theorem sum_weightedDensity_eq_one
    (P : ι → Set X) {S : Set X} (hclosed : ∀ i, IsClosed (P i))
    (hreg : ∀ i, closure (interior (P i)) = P i)
    (hdisj : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (hcover : (⋃ i, P i) = S) {x : X} (hxS : x ∈ interior S)
    (hxtriple : x ∉ tripleContactSet P) :
    ∑ i, weightedDensity (P i) x = 1 := by
  classical
  by_cases hint : ∃ i, x ∈ interior (P i)
  · obtain ⟨i, hi⟩ := hint
    rw [Finset.sum_eq_single i]
    · exact weightedDensity_of_mem_interior hi
    · intro j _ hji
      apply weightedDensity_of_not_mem (hclosed j)
      intro hj
      exact (disjoint_left.mp
        (disjoint_interior_piece_of_regular P hreg hdisj hji.symm)) hi hj
    · simp
  · have hnotint : ∀ i, x ∉ interior (P i) := by
      intro i hi
      exact hint ⟨i, hi⟩
    have hxcover : x ∈ ⋃ i, P i := by
      rw [hcover]
      exact interior_subset hxS
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxcover
    have hif : x ∈ frontier (P i) :=
      (mem_frontier_iff_notMem_interior hi).mpr (hnotint i)
    obtain ⟨j, hji, hj⟩ := exists_other_piece_at_frontier P hclosed hcover hxS hif
    have hjf : x ∈ frontier (P j) :=
      (mem_frontier_iff_notMem_interior hj).mpr (hnotint j)
    have hothers : ∀ k, k ≠ i → k ≠ j → x ∉ P k := by
      intro k hki hkj hk
      exact hxtriple ⟨i, j, k, hji.symm, hki.symm, hkj.symm, hi, hj, hk⟩
    calc
      ∑ k, weightedDensity (P k) x =
          ∑ k : ι, ((if k = i then (2 : ℝ≥0∞)⁻¹ else 0) +
            (if k = j then (2 : ℝ≥0∞)⁻¹ else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hki : k = i
        · subst k
          simp [weightedDensity_of_mem_frontier hif, hji.symm]
        by_cases hkj : k = j
        · subst k
          simp [weightedDensity_of_mem_frontier hjf, hji]
        · simp [hki, hkj, weightedDensity_of_not_mem (hclosed k) (hothers k hki hkj)]
      _ = 1 := by
        rw [Finset.sum_add_distrib]
        simp [ENNReal.inv_two_add_inv_two]

variable [MeasurableSpace X]

/-- The finite dissection density is the ambient indicator almost everywhere.
The only exceptional sets are the ambient frontier and triple contacts. -/
theorem sum_weightedDensity_ae_eq_indicator
    (P : ι → Set X) {S : Set X} (hclosed : ∀ i, IsClosed (P i))
    (hreg : ∀ i, closure (interior (P i)) = P i)
    (hdisj : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (hcover : (⋃ i, P i) = S) (μ : Measure X)
    (hfront : μ (frontier S) = 0) (htriple : μ (tripleContactSet P) = 0) :
    (fun x => ∑ i, weightedDensity (P i) x) =ᵐ[μ] S.indicator (fun _ => 1) := by
  classical
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hfront,
    measure_eq_zero_iff_ae_notMem.mp htriple] with x hxfront hxtriple
  by_cases hxS : x ∈ S
  · rw [indicator_of_mem hxS]
    exact sum_weightedDensity_eq_one P hclosed hreg hdisj hcover
      ((mem_interior_iff_notMem_frontier hxS).mpr hxfront) hxtriple
  · rw [indicator_of_notMem hxS]
    apply Finset.sum_eq_zero
    intro i _
    apply weightedDensity_of_not_mem (hclosed i)
    intro hi
    apply hxS
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hi⟩

variable [BorelSpace X]

/-- Weighted masses add to the ambient measure, including when pairwise
common boundaries have positive measure. -/
theorem sum_weightedMass_eq_measure
    (P : ι → Set X) {S : Set X} (hclosed : ∀ i, IsClosed (P i))
    (hreg : ∀ i, closure (interior (P i)) = P i)
    (hdisj : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (hcover : (⋃ i, P i) = S) (μ : Measure X)
    (hfront : μ (frontier S) = 0) (htriple : μ (tripleContactSet P) = 0) :
    ∑ i, weightedMass μ (P i) = μ S := by
  have hS : MeasurableSet S := by
    rw [← hcover]
    exact (isClosed_iUnion_of_finite hclosed).measurableSet
  calc
    ∑ i, weightedMass μ (P i) = ∫⁻ x, ∑ i, weightedDensity (P i) x ∂μ :=
      (lintegral_finsetSum Finset.univ
        (fun i _ => measurable_weightedDensity (P i))).symm
    _ = ∫⁻ x, S.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
      lintegral_congr_ae
        (sum_weightedDensity_ae_eq_indicator P hclosed hreg hdisj hcover μ hfront htriple)
    _ = μ S := by rw [lintegral_indicator_const hS, one_mul]

/-- Finitely many triple contacts suffice for any measure without atoms. -/
theorem sum_weightedMass_eq_measure_of_finite_triple
    (P : ι → Set X) {S : Set X} (hclosed : ∀ i, IsClosed (P i))
    (hreg : ∀ i, closure (interior (P i)) = P i)
    (hdisj : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (hcover : (⋃ i, P i) = S) (μ : Measure X) [NullSingletonClass μ]
    (hfront : μ (frontier S) = 0) (htriple : (tripleContactSet P).Finite) :
    ∑ i, weightedMass μ (P i) = μ S :=
  sum_weightedMass_eq_measure P hclosed hreg hdisj hcover μ hfront
    (htriple.measure_zero μ)

end

end Puzzling139335
