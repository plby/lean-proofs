import Arxiv.Arxiv2411_18291.UniformCliqueEnlargement

/-! # Face probabilities with prescribed clique candidates -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q d : ℕ}

theorem cliqueEnlargements_face_card_zero (Q : Block V q) (S : Finset V)
    (hj : d < (S \ Q.val).card) :
    ((cliqueEnlargements Q d).filter fun Z => S ⊆ Z.val).card = 0 := by
  rw [card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro Z hZ
  have hQZ := (mem_filter.mp (mem_filter.mp hZ).1).2
  have hSZ := (mem_filter.mp hZ).2
  have hc := card_le_card (union_subset hQZ hSZ)
  have h := card_sdiff_add_card S Q.val
  rw [union_comm] at h
  rw [Z.property] at hc
  have hQ := Q.property
  omega

theorem uniform_prescribed_clique_face_probability_le (Q : Block V q)
    [MeasurableSpace (Block V (q + d))] [MeasurableSingletonClass (Block V (q + d))]
    (C : Finset (Block V (q + d))) (hC : C.Nonempty)
    (hCQ : C ⊆ cliqueEnlargements Q d) {η : ℝ} (hη : 0 < η)
    (hcount : η * (Fintype.card V : ℝ) ^ d ≤ C.card)
    (hn : 0 < Fintype.card V) (S : Finset V) :
    (PMF.uniformOfFinset C hC).toMeasure.real {Z | S ⊆ Z.val} ≤
      (1 / (Fintype.card V : ℝ) ^ (S \ Q.val).card) / η := by
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  rw [measureReal_def, PMF.toMeasure_uniformOfFinset_apply _ _
    (Set.toFinite _).measurableSet, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  simp only [Set.mem_ofPred_eq]
  have hsub : (C.filter fun Z => S ⊆ Z.val).card ≤
      ((cliqueEnlargements Q d).filter fun Z => S ⊆ Z.val).card :=
    card_le_card (filter_subset_filter _ hCQ)
  by_cases hj : (S \ Q.val).card ≤ d
  · have hnum : ((C.filter fun Z => S ⊆ Z.val).card : ℝ) ≤
        (Fintype.card V : ℝ) ^ (d - (S \ Q.val).card) := by
      exact_mod_cast hsub.trans (cliqueEnlargements_face_card_le Q S hj)
    calc
      _ ≤ (Fintype.card V : ℝ) ^ (d - (S \ Q.val).card) /
          (η * (Fintype.card V : ℝ) ^ d) :=
        div_le_div₀ (by positivity) hnum (by positivity) hcount
      _ = _ := by rw [pow_sub₀ _ hN.ne' hj]; field_simp
  · have hz := cliqueEnlargements_face_card_zero (d := d) Q S (by omega)
    have hzero : (C.filter fun Z => S ⊆ Z.val).card = 0 := by omega
    rw [hzero, Nat.cast_zero, zero_div]
    positivity

end Arxiv2411_18291
