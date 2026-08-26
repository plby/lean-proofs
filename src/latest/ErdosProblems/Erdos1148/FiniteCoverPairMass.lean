import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.Disjointed

/-! # Finite covers turn a pair-mass bound into a mass bound -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Set Function

theorem sum_sq_measureReal_le_pair_mass {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (s : ι → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hdisj : Pairwise (Disjoint on s))
    {R : Set (X × X)} (hpair : ∀ i, s i ×ˢ s i ⊆ R) :
    (∑ i, μ.real (s i) ^ 2) ≤ (μ.prod μ).real R := by
  have hpdisj : Pairwise (Disjoint on fun i => s i ×ˢ s i) :=
    fun i j hij => (hdisj hij).set_prod_left _ _
  have heq : (∑ i, μ.real (s i) ^ 2) = (μ.prod μ).real (⋃ i, s i ×ˢ s i) := by
    rw [measureReal_iUnion_fintype hpdisj (fun i => (hs i).prod (hs i))]
    simp only [measureReal_prod_prod, pow_two]
  rw [heq]
  exact measureReal_mono (iUnion_subset hpair) (measure_ne_top _ _)

theorem finite_cover_mass_sq_le_pair_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {N : ℕ} (s : Fin N → Set X)
    (hs : ∀ i, MeasurableSet (s i)) {E : Set X} (hcover : E ⊆ ⋃ i, s i)
    {R : Set (X × X)} (hpair : ∀ i, s i ×ˢ s i ⊆ R) :
    μ.real E ^ 2 ≤ (N : ℝ) * (μ.prod μ).real R := by
  classical
  let t := disjointed s
  have ht (i : Fin N) : t i ⊆ s i := disjointed_le s i
  have htm (i : Fin N) : MeasurableSet (t i) :=
    disjointedRec (fun {_ j} h => h.diff (hs j)) (hs i)
  have htd : Pairwise (Disjoint on t) := disjoint_disjointed s
  have htunion : (⋃ i, t i) = ⋃ i, s i := iUnion_disjointed
  have hsum : μ.real E ≤ ∑ i, μ.real (t i) := by
    rw [← measureReal_iUnion_fintype htd htm, htunion]
    exact measureReal_mono hcover
  have hprod : (∑ i, μ.real (t i) ^ 2) ≤ (μ.prod μ).real R :=
    sum_sq_measureReal_le_pair_mass μ t htm htd
      (fun i => (prod_mono (ht i) (ht i)).trans (hpair i))
  calc
    μ.real E ^ 2 ≤ (∑ i, μ.real (t i)) ^ 2 :=
      pow_le_pow_left₀ measureReal_nonneg hsum 2
    _ ≤ (N : ℝ) * ∑ i, μ.real (t i) ^ 2 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => μ.real (t i)))
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)

theorem fintype_cover_mass_sq_le_pair_mass {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (s : ι → Set X)
    (hs : ∀ i, MeasurableSet (s i)) {E : Set X} (hcover : E ⊆ ⋃ i, s i)
    {R : Set (X × X)} (hpair : ∀ i, s i ×ˢ s i ⊆ R) :
    μ.real E ^ 2 ≤ (Fintype.card ι : ℝ) * (μ.prod μ).real R := by
  classical
  let e := Fintype.equivFin ι
  apply finite_cover_mass_sq_le_pair_mass μ (fun i => s (e.symm i)) (fun i => hs (e.symm i))
    (hpair := fun i => hpair (e.symm i))
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  exact mem_iUnion.mpr ⟨e i, by simpa only [Equiv.symm_apply_apply] using hi⟩

end Erdos1148.DukeArithmetic
