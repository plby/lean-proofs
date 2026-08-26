import Mathlib.NumberTheory.NumberField.Units.Regulator

/-! # A regulator bound from one real unit when there are two infinite places -/

namespace Erdos1148.DukeArithmetic

open NumberField NumberField.Units

theorem regOfFamily_const_eq_abs_log {K : Type*} [Field K] [NumberField K]
    (hcard : Fintype.card (InfinitePlace K) = 2) (w : InfinitePlace K)
    (hw : InfinitePlace.IsReal w) (u : (𝓞 K)ˣ) :
    regOfFamily (fun _ : Fin (NumberField.Units.rank K) => u) = |Real.log (w (u : K))| := by
  classical
  have hrank : NumberField.Units.rank K = 1 := by rw [NumberField.Units.rank, hcard]
  let : Nontrivial (InfinitePlace K) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, hv⟩ := exists_ne w
  have hJ : Fintype.card {p : InfinitePlace K // p ≠ v} = 1 := by
    simp [Fintype.card_subtype_compl, hcard]
  let : Subsingleton {p : InfinitePlace K // p ≠ v} :=
    Fintype.card_le_one_iff_subsingleton.mp hJ.le
  let e : {p : InfinitePlace K // p ≠ v} ≃ Fin (NumberField.Units.rank K) :=
    Fintype.equivOfCardEq (by simp [hJ, hrank])
  rw [regOfFamily_eq_det _ v e,
    Matrix.det_eq_elem_of_subsingleton _ (⟨w, Ne.symm hv⟩ : {p : InfinitePlace K // p ≠ v})]
  simp [hw.mult_eq_one]

theorem regulator_le_abs_log_of_two_places {K : Type*} [Field K] [NumberField K]
    (hcard : Fintype.card (InfinitePlace K) = 2) (w : InfinitePlace K)
    (hw : InfinitePlace.IsReal w) (u : (𝓞 K)ˣ) (hu : Real.log (w (u : K)) ≠ 0) :
    regulator K ≤ |Real.log (w (u : K))| := by
  let f : Fin (NumberField.Units.rank K) → (𝓞 K)ˣ := fun _ => u
  have hf : regOfFamily f = |Real.log (w (u : K))| := regOfFamily_const_eq_abs_log hcard w hw u
  have hidx := regOfFamily_div_regulator f
  rw [hf] at hidx
  have hpos : 0 < ((Subgroup.closure (Set.range f) ⊔ torsion K).index : ℝ) := by
    rw [← hidx]
    exact div_pos (abs_pos.mpr hu) (regulator_pos K)
  have hnat : 1 ≤ (Subgroup.closure (Set.range f) ⊔ torsion K).index := by
    have hn : 0 < (Subgroup.closure (Set.range f) ⊔ torsion K).index := by exact_mod_cast hpos
    omega
  have hge : (1 : ℝ) ≤ |Real.log (w (u : K))| / regulator K := by
    rw [hidx]
    exact_mod_cast hnat
  simpa only [one_mul] using (le_div_iff₀ (regulator_pos K)).mp hge

end Erdos1148.DukeArithmetic
