/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Transfer the cone-record theorem to the original iid coefficient sequence.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Model
import ErdosProblems.Erdos521.ConeSurvival

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem signLaw_eq_diracs : signLaw =
    (1 / 2 : ℝ≥0) • Measure.dirac (1 : ℝ) + (1 / 2 : ℝ≥0) • Measure.dirac (-1 : ℝ) := by
  norm_num [signLaw, bernoulliMeasure_def, unitInterval.toNNReal, unitInterval.symm]
  rfl

theorem pairedDirectionLaw_eq_prod : Pitman.pairedDirectionLaw = signLaw.prod signLaw := by
  classical
  ext s hs
  rw [Pitman.pairedDirectionLaw, Measure.map_apply Pitman.measurable_signPair hs]
  rw [Pitman.directionLaw, PMF.toMeasure_apply_fintype]
  rw [signLaw_eq_diracs]
  simp only [Measure.add_prod, Measure.prod_add, Measure.prod_smul_left,
    Measure.prod_smul_right, Measure.dirac_prod_dirac, Measure.add_apply,
    Measure.smul_apply]
  simp [PMF.uniformOfFintype_apply, Fin.sum_univ_succ, Pitman.signPair, Pitman.step,
    Set.indicator, Measure.dirac_apply' _ hs]
  norm_num [ENNReal.smul_def]
  have hquarter : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ = 4⁻¹ := by
    rw [← ENNReal.mul_inv] <;> norm_num
  rw [hquarter]
  ring

def coefficientPairs (ε : ℕ → ℝ) : ℕ → ℝ × ℝ := fun i ↦ (ε (2 * i + 1), ε (2 * i))

theorem measurable_coefficientPairs : Measurable coefficientPairs := by
  fun_prop [coefficientPairs]

def pairIndex (p : ℕ × Fin 2) : ℕ := 2 * p.1 + p.2

theorem pairIndex_injective : Function.Injective pairIndex := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  have hi := i.isLt
  have hj := j.isLt
  dsimp [pairIndex] at h
  have hab : a = b := by omega
  have hij : i = j := Fin.ext (by omega)
  exact Prod.ext hab hij

theorem coefficientPairs_map : sequenceLaw.map coefficientPairs =
    Measure.infinitePi fun _ : ℕ ↦ signLaw.prod signLaw := by
  have hreindex : sequenceLaw.map (fun ε (p : ℕ × Fin 2) ↦ ε (pairIndex p)) =
      Measure.infinitePi (fun _ : ℕ × Fin 2 ↦ signLaw) :=
    Measure.map_infinitePi_infinitePi_of_inj pairIndex_injective
  have hcurry : sequenceLaw.map (fun ε (i : ℕ) (j : Fin 2) ↦ ε (2 * i + j)) =
      Measure.infinitePi (fun _ : ℕ ↦ Measure.infinitePi (fun _ : Fin 2 ↦ signLaw)) := by
    have h := congrArg (fun μ : Measure (ℕ × Fin 2 → ℝ) ↦
      μ.map (MeasurableEquiv.curry ℕ (Fin 2) ℝ)) hreindex
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin 2) ↦ signLaw)] at h
    exact h
  have hmap := congrArg (fun μ : Measure (ℕ → Fin 2 → ℝ) ↦
    μ.map (fun ω i ↦ (ω i 1, ω i 0))) hcurry
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hmap
  rw [Measure.infinitePi_map_pi
    (f := fun (_ : ℕ) (w : Fin 2 → ℝ) ↦ (w 1, w 0)) _ (fun _ ↦ by fun_prop)] at hmap
  have hpair : (Measure.infinitePi (fun _ : Fin 2 ↦ signLaw)).map
      (fun w ↦ (w 1, w 0)) = signLaw.prod signLaw :=
    Measure.infinitePi_map_eval_prod (by decide : (1 : Fin 2) ≠ 0)
  change sequenceLaw.map (fun ε i ↦ (ε (2 * i + 1), ε (2 * i))) = _
  simpa only [hpair, Function.comp_def, Fin.val_one, Fin.val_zero, Nat.add_zero] using hmap

theorem measurePreserving_coefficientPairs :
    MeasurePreserving coefficientPairs sequenceLaw
      (Measure.infinitePi fun _ : ℕ ↦ Pitman.pairedDirectionLaw) := by
  rw [pairedDirectionLaw_eq_prod]
  exact ⟨measurable_coefficientPairs, coefficientPairs_map⟩

/-- Infinitely many cone records occur for the one infinite iid sign sequence. -/
theorem ae_infinite_coefficientRecords :
    ∀ᵐ ε ∂sequenceLaw, ∀ N, ∃ m, N ≤ m ∧ CoefficientRecord ε m := by
  have hpair : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ ↦ Pitman.pairedDirectionLaw),
      ω ∈ pairInfiniteRecords := by
    exact (mem_ae_iff_prob_eq_one measurableSet_pairInfiniteRecords).mpr
      Pitman.pairedDirection_infiniteRecords_measure_one
  exact measurePreserving_coefficientPairs.quasiMeasurePreserving.ae hpair

/-- Almost surely there are arbitrarily large odd degrees with no exterior real zeros. -/
theorem ae_infinite_no_exterior_roots :
    ∀ᵐ ε ∂sequenceLaw, ∀ N, ∃ m, N ≤ m ∧
      ∀ x : ℝ, 1 < |x| → powerSum ε (2 * m + 2) x ≠ 0 := by
  filter_upwards [ae_infinite_coefficientRecords, ae_sequence_signs] with ε hrecord hsign
  intro N
  obtain ⟨m, hm, hrec⟩ := hrecord N
  refine ⟨m, hm, fun x hx ↦ coefficientRecord_no_exterior_root ε m hrec ?_ x hx⟩
  rcases hsign (2 * m + 1) with h | h <;> simp [h]

/-- On infinitely many odd degrees the total and interior root counts coincide. -/
theorem ae_infinite_rootCount_eq_interior :
    ∀ᵐ ε ∂sequenceLaw, ∀ N, ∃ m, N ≤ m ∧
      rootCount ε (2 * m + 1) = interiorRootCount ε (2 * m + 1) := by
  filter_upwards [ae_infinite_coefficientRecords, ae_record_rootCount_eq] with ε hrecord heq
  intro N
  obtain ⟨m, hm, hrec⟩ := hrecord N
  exact ⟨m, hm, heq m hrec⟩

end Erdos521
