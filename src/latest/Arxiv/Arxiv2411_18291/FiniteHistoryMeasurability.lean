import Arxiv.Arxiv2411_18291.FiniteHistoryStep

/-! # Adaptation and integrability of finite-history statistics -/

open MeasureTheory ProbabilityTheory Finset Preorder

noncomputable section

namespace Arxiv2411_18291.FiniteHistoryProcess

variable {S : Type*} [Finite S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem stronglyMeasurable_history (n : ℕ) (f : History S n → ℝ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => S) n]
      (fun ω => f (frestrictLe n ω)) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  change StronglyMeasurable[MeasurableSpace.comap (frestrictLe (π := fun _ => S) n) inferInstance]
    (f ∘ frestrictLe (π := fun _ => S) n)
  exact ((measurable_of_finite f).comp (comap_measurable _)).stronglyMeasurable

theorem measurableSet_history (n : ℕ) (Q : History S n → Prop) :
    MeasurableSet[Filtration.piLE (X := fun _ => S) n] {ω | Q (frestrictLe n ω)} := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact comap_measurable (frestrictLe (π := fun _ => S) n)
    ((Set.toFinite {h | Q h}).measurableSet)

theorem stronglyMeasurable_step (n : ℕ) (f : History S n → S → ℝ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => S) (n + 1)]
      (fun ω => f (frestrictLe n ω) (ω (n + 1))) := by
  let g : History S (n + 1) → ℝ := fun h =>
    f (frestrictLe₂ (π := fun _ => S) (Nat.le_succ n) h) (h ⟨n + 1, mem_Iic.mpr le_rfl⟩)
  exact stronglyMeasurable_history (n + 1) g

omit [Finite S] in
theorem integrable_history [Fintype S] (start : S) (p : (n : ℕ) → History S n → PMF S)
    (n : ℕ) (f : History S n → ℝ) :
    Integrable (fun ω => f (frestrictLe n ω)) (probability start p) := by
  have hi : Integrable f ((probability start p).map (frestrictLe n)) := .of_finite
  exact hi.comp_measurable (measurable_frestrictLe n)

end Arxiv2411_18291.FiniteHistoryProcess
