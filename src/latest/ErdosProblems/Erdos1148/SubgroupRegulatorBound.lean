import ErdosProblems.Erdos1148.RankOneRegulator

/-! # Retaining the unit-subgroup index in the regulator bound -/

namespace Erdos1148.DukeArithmetic

open NumberField NumberField.Units

theorem unitFamily_index_mul_regulator {K : Type*} [Field K] [NumberField K]
    (hcard : Fintype.card (InfinitePlace K) = 2) (w : InfinitePlace K)
    (hw : InfinitePlace.IsReal w) (u : (𝓞 K)ˣ) :
    ((Subgroup.closure (Set.range (fun _ : Fin (NumberField.Units.rank K) => u)) ⊔
      torsion K).index : ℝ) * regulator K = |Real.log (w (u : K))| := by
  have h := regOfFamily_div_regulator (fun _ : Fin (NumberField.Units.rank K) => u)
  rw [regOfFamily_const_eq_abs_log hcard w hw u] at h
  exact (eq_div_iff (regulator_ne_zero K)).mp h.symm

lemma unitFamily_finiteIndex {K : Type*} [Field K] [NumberField K]
    (hcard : Fintype.card (InfinitePlace K) = 2) (w : InfinitePlace K)
    (hw : InfinitePlace.IsReal w) (u : (𝓞 K)ˣ) (hu : Real.log (w (u : K)) ≠ 0) :
    (Subgroup.closure (Set.range (fun _ : Fin (NumberField.Units.rank K) => u)) ⊔
      torsion K).FiniteIndex := by
  constructor
  intro hzero
  have h := unitFamily_index_mul_regulator hcard w hw u
  rw [hzero, Nat.cast_zero, zero_mul] at h
  exact (abs_ne_zero.mpr hu) h.symm

lemma unitFamily_le_subgroup {K : Type*} [Field K] [NumberField K]
    (S : Subgroup (𝓞 K)ˣ) (hS : torsion K ≤ S) {u : (𝓞 K)ˣ} (hu : u ∈ S) :
    Subgroup.closure (Set.range (fun _ : Fin (NumberField.Units.rank K) => u)) ⊔ torsion K ≤ S := by
  apply sup_le _ hS
  apply (Subgroup.closure_le S).mpr
  rintro _ ⟨_, rfl⟩
  exact hu

theorem unitSubgroup_finiteIndex {K : Type*} [Field K] [NumberField K]
    (hcard : Fintype.card (InfinitePlace K) = 2) (w : InfinitePlace K)
    (hw : InfinitePlace.IsReal w) (S : Subgroup (𝓞 K)ˣ) (hS : torsion K ≤ S)
    (u : (𝓞 K)ˣ) (hu : u ∈ S) (hlog : Real.log (w (u : K)) ≠ 0) : S.FiniteIndex := by
  let := unitFamily_finiteIndex hcard w hw u hlog
  exact Subgroup.finiteIndex_of_le (unitFamily_le_subgroup S hS hu)

theorem unitSubgroup_index_mul_regulator_le {K : Type*} [Field K] [NumberField K]
    (hcard : Fintype.card (InfinitePlace K) = 2) (w : InfinitePlace K)
    (hw : InfinitePlace.IsReal w) (S : Subgroup (𝓞 K)ˣ) (hS : torsion K ≤ S)
    (u : (𝓞 K)ˣ) (hu : u ∈ S) (hlog : Real.log (w (u : K)) ≠ 0) :
    (S.index : ℝ) * regulator K ≤ |Real.log (w (u : K))| := by
  let := unitFamily_finiteIndex hcard w hw u hlog
  have hi := Subgroup.index_antitone (unitFamily_le_subgroup S hS hu)
  have hiR : (S.index : ℝ) ≤
      ((Subgroup.closure (Set.range (fun _ : Fin (NumberField.Units.rank K) => u)) ⊔
        torsion K).index : ℝ) := by exact_mod_cast hi
  exact (mul_le_mul_of_nonneg_right hiR (regulator_pos K).le).trans_eq
    (unitFamily_index_mul_regulator hcard w hw u)

end Erdos1148.DukeArithmetic
