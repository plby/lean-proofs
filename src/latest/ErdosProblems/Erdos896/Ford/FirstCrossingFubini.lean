/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.OrderQ

/-!
# Fubini decomposition at an order statistic

This file splits a tuple immediately before and after a distinguished
coordinate.  It also packages the sectionwise comparison used in Ford's
first-crossing argument.
-/

namespace Erdos896.Ford

open MeasureTheory Set
open scoped ENNReal

/-- Split a tuple into its first `m` and last `n` coordinates. -/
noncomputable def restSplit (m n : ℕ) :
    (Fin (m + n) → ℝ) ≃ᵐ ((Fin m → ℝ) × (Fin n → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) ↦ ℝ)
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n ↦ ℝ))

theorem restSplit_measurePreserving (m n : ℕ) :
    MeasurePreserving (restSplit m n) volume volume := by
  have h₂ := (volume_measurePreserving_piCongrLeft
    (fun _ : Fin (m + n) ↦ ℝ)
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))).symm
  have h₃ := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin m ⊕ Fin n ↦ ℝ)
  simpa only [restSplit, MeasurableEquiv.coe_trans] using h₃.comp h₂

/-- Split a tuple at coordinate `m`, retaining the distinguished coordinate
as the first component. -/
noncomputable def splitAt (m n : ℕ) :
    (Fin (m + n + 1) → ℝ) ≃ᵐ
      (ℝ × ((Fin m → ℝ) × (Fin n → ℝ))) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + n + 1) ↦ ℝ)
      ⟨m, by omega⟩).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (restSplit m n))

theorem splitAt_measurePreserving (m n : ℕ) :
    MeasurePreserving (splitAt m n) volume volume := by
  let : MeasurableSpace (Fin (m + n + 1) → ℝ) := MeasurableSpace.pi
  let : MeasurableSpace (Fin (m + n) → ℝ) := MeasurableSpace.pi
  let : MeasurableSpace (Fin m → ℝ) := MeasurableSpace.pi
  let : MeasurableSpace (Fin n → ℝ) := MeasurableSpace.pi
  have h₁ := volume_preserving_piFinSuccAbove
    (fun _ : Fin (m + n + 1) ↦ ℝ) ⟨m, by omega⟩
  have hprod := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (restSplit_measurePreserving m n)
  rw [← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at hprod
  exact hprod.comp h₁

/-- Pointwise comparison of all vertical sections implies comparison of
their product measures. -/
theorem Measure.prod_mono_of_section_mono
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    {S T : Set (α × β)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (C : ℝ≥0∞)
    (hsection : ∀ a, C * ν (Prod.mk a ⁻¹' S) ≤ ν (Prod.mk a ⁻¹' T)) :
    C * (μ.prod ν) S ≤ (μ.prod ν) T := by
  rw [Measure.prod_apply hS, Measure.prod_apply hT,
    ← lintegral_const_mul C (measurable_measure_prodMk_left hS)]
  exact lintegral_mono fun a ↦ hsection a

/-- The split at coordinate `m`, associated so the distinguished coordinate
and the prefix form the base of the Fubini integral. -/
noncomputable def splitAtFubini (m n : ℕ) :
    (Fin (m + n + 1) → ℝ) ≃ᵐ
      ((ℝ × (Fin m → ℝ)) × (Fin n → ℝ)) :=
  (splitAt m n).trans MeasurableEquiv.prodAssoc.symm

theorem splitAtFubini_measurePreserving (m n : ℕ) :
    MeasurePreserving (splitAtFubini m n) volume volume := by
  let : MeasurableSpace (Fin (m + n + 1) → ℝ) := MeasurableSpace.pi
  let : MeasurableSpace (Fin (m + n) → ℝ) := MeasurableSpace.pi
  let : MeasurableSpace (Fin m → ℝ) := MeasurableSpace.pi
  let : MeasurableSpace (Fin n → ℝ) := MeasurableSpace.pi
  exact volume_preserving_prodAssoc.symm.comp (splitAt_measurePreserving m n)

@[simp]
theorem splitAtFubini_pivot (m n : ℕ) (x : Fin (m + n + 1) → ℝ) :
    (splitAtFubini m n x).1.1 = x ⟨m, by omega⟩ := by
  rfl

@[simp]
theorem splitAtFubini_prefix (m n : ℕ) (x : Fin (m + n + 1) → ℝ)
    (i : Fin m) :
    (splitAtFubini m n x).1.2 i = x (Fin.castAdd (n + 1) i) := by
  change x ((⟨m, by omega⟩ : Fin (m + n + 1)).succAbove
    (Fin.castAdd n i)) = _
  rw [Fin.succAbove_of_castSucc_lt _ _ (by exact_mod_cast i.isLt)]
  rfl

@[simp]
theorem splitAtFubini_suffix (m n : ℕ) (x : Fin (m + n + 1) → ℝ)
    (i : Fin n) :
    (splitAtFubini m n x).2 i = x ⟨m + 1 + i, by omega⟩ := by
  change x ((⟨m, by omega⟩ : Fin (m + n + 1)).succAbove
    (Fin.natAdd m i)) = _
  rw [Fin.succAbove_of_le_castSucc _ _ (by
    change m ≤ m + i
    omega)]
  congr 1
  apply Fin.ext
  simp
  omega

/-- A base condition together with an ordered suffix from the distinguished
coordinate up to `b`. -/
def orderedSuffixCell (m n : ℕ) (b : ℝ)
    (P : Set (ℝ × (Fin m → ℝ))) :
    Set ((ℝ × (Fin m → ℝ)) × (Fin n → ℝ)) :=
  {q | q.1 ∈ P ∧ q.2 ∈ orderedSimplex n q.1.1 b}

theorem measurableSet_orderedSuffixCell {m n : ℕ} {b : ℝ}
    {P : Set (ℝ × (Fin m → ℝ))} (hP : MeasurableSet P) :
    MeasurableSet (orderedSuffixCell m n b P) := by
  have hbounds : MeasurableSet
      {q : (ℝ × (Fin m → ℝ)) × (Fin n → ℝ) |
        ∀ i, q.1.1 ≤ q.2 i ∧ q.2 i ≤ b} := by
    rw [show {q : (ℝ × (Fin m → ℝ)) × (Fin n → ℝ) |
        ∀ i, q.1.1 ≤ q.2 i ∧ q.2 i ≤ b} =
        ⋂ i, {q | q.1.1 ≤ q.2 i ∧ q.2 i ≤ b} by ext; simp]
    apply MeasurableSet.iInter
    intro i
    have hlo : MeasurableSet
        {q : (ℝ × (Fin m → ℝ)) × (Fin n → ℝ) | q.1.1 ≤ q.2 i} :=
      measurableSet_le measurable_fst.fst
        ((measurable_pi_apply i).comp measurable_snd)
    have hhi : MeasurableSet
        {q : (ℝ × (Fin m → ℝ)) × (Fin n → ℝ) | q.2 i ≤ b} :=
      measurableSet_le ((measurable_pi_apply i).comp measurable_snd) measurable_const
    exact hlo.inter hhi
  have hmono : MeasurableSet
      {q : (ℝ × (Fin m → ℝ)) × (Fin n → ℝ) | Monotone q.2} := by
    rw [show {q : (ℝ × (Fin m → ℝ)) × (Fin n → ℝ) | Monotone q.2} =
        ⋂ i, ⋂ j, ⋂ (_h : i ≤ j), {q | q.2 i ≤ q.2 j} by
          ext q
          simp only [mem_ofPred_eq, mem_iInter]
          exact Iff.rfl]
    exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun _ ↦
        measurableSet_le ((measurable_pi_apply i).comp measurable_snd)
          ((measurable_pi_apply j).comp measurable_snd)
  rw [show orderedSuffixCell m n b P =
      (P ×ˢ (Set.univ : Set (Fin n → ℝ))) ∩
        ({q | ∀ i, q.1.1 ≤ q.2 i ∧ q.2 i ≤ b} ∩ {q | Monotone q.2}) by
        ext q
        simp [orderedSuffixCell, orderedSimplex]]
  exact (hP.prod MeasurableSet.univ).inter (hbounds.inter hmono)

/-- Pull an ordered suffix cell back to the original tuple coordinates. -/
def splitOrderedCell (m n : ℕ) (b : ℝ)
    (P : Set (ℝ × (Fin m → ℝ))) : Set (Fin (m + n + 1) → ℝ) :=
  splitAtFubini m n ⁻¹' orderedSuffixCell m n b P

theorem measurableSet_splitOrderedCell {m n : ℕ} {b : ℝ}
    {P : Set (ℝ × (Fin m → ℝ))} (hP : MeasurableSet P) :
    MeasurableSet (splitOrderedCell m n b P) :=
  (splitAtFubini m n).measurable (measurableSet_orderedSuffixCell hP)

theorem volume_splitOrderedCell {m n : ℕ} {b : ℝ}
    {P : Set (ℝ × (Fin m → ℝ))} (hP : MeasurableSet P) :
    volume (splitOrderedCell m n b P) = volume (orderedSuffixCell m n b P) :=
  (splitAtFubini_measurePreserving m n).measure_preimage
    (measurableSet_orderedSuffixCell hP).nullMeasurableSet

theorem orderedSuffixCell_section_of_mem {m n : ℕ} {b : ℝ}
    {P : Set (ℝ × (Fin m → ℝ))} {q : ℝ × (Fin m → ℝ)} (hq : q ∈ P) :
    Prod.mk q ⁻¹' orderedSuffixCell m n b P = orderedSimplex n q.1 b := by
  ext x
  simp [orderedSuffixCell, hq]

theorem orderedSuffixCell_section_of_not_mem {m n : ℕ} {b : ℝ}
    {P : Set (ℝ × (Fin m → ℝ))} {q : ℝ × (Fin m → ℝ)} (hq : q ∉ P) :
    Prod.mk q ⁻¹' orderedSuffixCell m n b P = ∅ := by
  ext x
  simp [orderedSuffixCell, hq]

/-- A sectionwise comparison of the ordered suffixes compares the full
first-crossing cells after splitting at the crossing coordinate. -/
theorem mul_volume_splitOrderedCell_le {m n : ℕ} {c d : ℝ}
    {P : Set (ℝ × (Fin m → ℝ))} (hP : MeasurableSet P) (C : ℝ≥0∞)
    (hsection : ∀ q ∈ P,
      C * volume (orderedSimplex n q.1 c) ≤
        volume (orderedSimplex n q.1 d)) :
    C * volume (splitOrderedCell m n c P) ≤
      volume (splitOrderedCell m n d P) := by
  rw [volume_splitOrderedCell hP, volume_splitOrderedCell hP,
    Measure.volume_eq_prod, Measure.volume_eq_prod]
  apply Measure.prod_mono_of_section_mono
      (measurableSet_orderedSuffixCell hP)
      (measurableSet_orderedSuffixCell hP)
  intro q
  by_cases hq : q ∈ P
  · rw [orderedSuffixCell_section_of_mem hq,
      orderedSuffixCell_section_of_mem hq]
    exact hsection q hq
  · rw [orderedSuffixCell_section_of_not_mem hq,
      orderedSuffixCell_section_of_not_mem hq]
    simp

end Erdos896.Ford
