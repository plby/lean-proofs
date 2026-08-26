import ErdosProblems.Erdos1148.ExceptionalVisitCount

/-! # Most mass lies in words with few exceptional visits -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Function

def goodOrbitSet (P : FineModularPartition) (κ : ℝ) (n : ℕ) : Set ModularOrbitSpace :=
  ⋃ w : {w : Fin (n + 1) → Option (Fin P.size) // GoodOrbitWord κ w},
    P.partition.orbitAtom modularTimeOne (n + 1) w.val

lemma measurableSet_goodOrbitSet (P : FineModularPartition) (κ : ℝ) (n : ℕ) :
    MeasurableSet (goodOrbitSet P κ n) :=
  MeasurableSet.iUnion (fun w => P.partition.measurableSet_orbitAtom
    continuous_modularTimeOne.measurable _ w.val)

lemma mem_goodOrbitSet_of_count_le (P : FineModularPartition) {κ : ℝ} {n : ℕ}
    {x : ModularOrbitSpace} (hx : x ∉ P.partition.atom none)
    (hcount : exceptionalVisitCount P n x ≤ κ * (n + 1)) : x ∈ goodOrbitSet P κ n := by
  have hcover : x ∈ ⋃ w : Fin (n + 1) → Option (Fin P.size),
      P.partition.orbitAtom modularTimeOne (n + 1) w := by
    rw [P.partition.iUnion_orbitAtom]
    exact Set.mem_univ _
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hcover
  have hfirst : w 0 ≠ none := by
    intro h
    have hx0 := hw (0 : Fin (n + 1))
    apply hx
    simpa only [Fin.val_zero, Function.iterate_zero_apply, h] using hx0
  have hgood : GoodOrbitWord κ w := ⟨hfirst, by
    rwa [exceptionalVisitCount_of_mem_orbitAtom P hw] at hcount⟩
  exact Set.mem_iUnion.mpr ⟨⟨w, hgood⟩, hw⟩

lemma goodOrbitSet_compl_subset (P : FineModularPartition) (κ : ℝ) (n : ℕ) :
    (goodOrbitSet P κ n)ᶜ ⊆ P.partition.atom none ∪
      {x | κ * (n + 1) ≤ exceptionalVisitCount P n x} := by
  intro x hx
  by_cases hbad : x ∈ P.partition.atom none
  · exact Or.inl hbad
  · right
    by_contra hnot
    exact hx (mem_goodOrbitSet_of_count_le P hbad (lt_of_not_ge hnot).le)

theorem exceptionalVisitCount_exceedance_mass_le (P : FineModularPartition)
    (μ : Measure ModularOrbitSpace) [IsFiniteMeasure μ]
    (hinv : ∀ t : ℝ, Measure.map (modularRightTranslate (diagonalFlow t)) μ = μ)
    {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    μ.real {x | κ * (n + 1) ≤ exceptionalVisitCount P n x} ≤ μ.real (P.partition.atom none) / κ := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (exceptionalVisitCount_nonneg P n))
    (integrable_exceptionalVisitCount P μ n) (κ * (n + 1))
  rw [integral_exceptionalVisitCount P μ hinv] at hmarkov
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hscaled : ((n : ℝ) + 1) *
      (κ * μ.real {x | κ * (n + 1) ≤ exceptionalVisitCount P n x}) ≤
      ((n : ℝ) + 1) * μ.real (P.partition.atom none) := by
    nlinarith [measureReal_nonneg (μ := μ) (s := P.partition.atom none)]
  have hbound := (mul_le_mul_iff_right₀ hn).mp hscaled
  apply (le_div_iff₀ hκ).mpr
  nlinarith

theorem goodOrbitSet_mass_lower (P : FineModularPartition)
    (μ : Measure ModularOrbitSpace) [IsProbabilityMeasure μ]
    (hinv : ∀ t : ℝ, Measure.map (modularRightTranslate (diagonalFlow t)) μ = μ)
    {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    1 - (1 + κ⁻¹) * μ.real (P.partition.atom none) ≤ μ.real (goodOrbitSet P κ n) := by
  have hcomp := (measureReal_mono (μ := μ) (goodOrbitSet_compl_subset P κ n)).trans
    (measureReal_union_le _ _)
  have htail := exceptionalVisitCount_exceedance_mass_le P μ hinv hκ n
  rw [measureReal_compl (measurableSet_goodOrbitSet P κ n), probReal_univ] at hcomp
  rw [div_eq_mul_inv] at htail
  nlinarith

theorem sum_goodOrbitWord_mass (P : FineModularPartition)
    (μ : Measure ModularOrbitSpace) [IsFiniteMeasure μ] (κ : ℝ) (n : ℕ) :
    (∑ w : {w : Fin (n + 1) → Option (Fin P.size) // GoodOrbitWord κ w},
      μ.real (P.partition.orbitAtom modularTimeOne (n + 1) w.val)) =
      μ.real (goodOrbitSet P κ n) := by
  apply (measureReal_iUnion_fintype _ _).symm
  · intro v w hvw
    exact P.partition.pairwise_disjoint_orbitAtom modularTimeOne _
      (fun h => hvw (Subtype.ext h))
  · intro w
    exact P.partition.measurableSet_orbitAtom continuous_modularTimeOne.measurable _ w.val

end Erdos1148.DukeArithmetic
