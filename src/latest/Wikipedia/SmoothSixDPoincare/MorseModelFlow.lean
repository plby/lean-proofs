import Wikipedia.SmoothSixDPoincare.MorseHandleAmbient
import Wikipedia.SmoothSixDPoincare.MorseDescentModel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Dynamics.Flow

/-!
# The exact descending flow of the quadratic Morse model

Negative coordinates expand and positive coordinates contract. The union
of the lower quadratic sublevel and the curved handle is forward invariant.
These model results still require transport to the original manifold flow.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The complete linear flow of `(u, -v)`. -/
def descentFlow : Flow ℝ (N × P) where
  toFun t z := (Real.exp t • z.1, Real.exp (-t) • z.2)
  cont' := ((Real.continuous_exp.comp continuous_fst).smul continuous_snd.fst).prodMk
    ((Real.continuous_exp.comp continuous_fst.neg).smul continuous_snd.snd)
  map_add' s t z := by
    simp only [Real.exp_add, neg_add, smul_smul]
  map_zero' z := by simp

/-- Its trajectories solve the actual linear differential equation. -/
theorem hasDerivAt_descentFlow (z : N × P) (t : ℝ) :
    HasDerivAt (fun s => descentFlow s z) (descent (descentFlow t z)) t := by
  have h₁ := (Real.hasDerivAt_exp t).smul_const z.1
  have h₂ := ((hasDerivAt_id t).neg.exp).smul_const z.2
  simpa only [descentFlow, descent, id_eq, Pi.neg_apply, mul_neg, mul_one, neg_smul]
    using h₁.prodMk h₂

theorem norm_descentFlow_fst (t : ℝ) (z : N × P) :
    ‖(descentFlow t z).1‖ = Real.exp t * ‖z.1‖ := by
  change ‖Real.exp t • z.1‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]

theorem norm_descentFlow_snd (t : ℝ) (z : N × P) :
    ‖(descentFlow t z).2‖ = Real.exp (-t) * ‖z.2‖ := by
  change ‖Real.exp (-t) • z.2‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-t))]

theorem norm_fst_le_descentFlow {t : ℝ} (ht : 0 ≤ t) (z : N × P) :
    ‖z.1‖ ≤ ‖(descentFlow t z).1‖ := by
  rw [norm_descentFlow_fst]
  exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr ht)

theorem norm_snd_descentFlow_le {t : ℝ} (ht : 0 ≤ t) (z : N × P) :
    ‖(descentFlow t z).2‖ ≤ ‖z.2‖ := by
  rw [norm_descentFlow_snd]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))

/-- The quadratic height is nonincreasing in forward time. -/
theorem quadratic_descentFlow_le {t : ℝ} (ht : 0 ≤ t) (z : N × P) :
    quadratic (descentFlow t z) ≤ quadratic z := by
  have h₁ := (sq_le_sq₀ (norm_nonneg z.1) (norm_nonneg (descentFlow t z).1)).mpr
    (norm_fst_le_descentFlow ht z)
  have h₂ := (sq_le_sq₀ (norm_nonneg (descentFlow t z).2) (norm_nonneg z.2)).mpr
    (norm_snd_descentFlow_le ht z)
  exact add_le_add (neg_le_neg h₁) h₂

/-- A useful description of the lower sublevel with the model handle adjoined. -/
theorem mem_lower_union_handle_iff {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ {w | quadratic w ≤ -(ρ ^ 2)} ∪ range (modelMap ρ) ↔
      quadratic z ≤ -(ρ ^ 2) ∨ ‖z.2‖ ≤ ρ := by
  rw [mem_union, mem_ofPred_eq, mem_range_modelMap_iff hρ]
  change quadratic z ≤ -(ρ ^ 2) ∨ (‖z.2‖ ≤ ρ ∧ -(ρ ^ 2) ≤ quadratic z) ↔ _
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.1
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hq : quadratic z ≤ -(ρ ^ 2)
      · exact Or.inl hq
      · exact Or.inr ⟨h, le_of_not_ge hq⟩

/-- Every forward trajectory stays in the lower sublevel with its handle adjoined. -/
theorem descentFlow_mem_lower_union_handle {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 ≤ t)
    {z : N × P} (hz : z ∈ {w | quadratic w ≤ -(ρ ^ 2)} ∪ range (modelMap ρ)) :
    descentFlow t z ∈ {w | quadratic w ≤ -(ρ ^ 2)} ∪ range (modelMap ρ) := by
  rw [mem_lower_union_handle_iff hρ] at hz ⊢
  rcases hz with hq | hv
  · exact Or.inl ((quadratic_descentFlow_le ht z).trans hq)
  · exact Or.inr ((norm_snd_descentFlow_le ht z).trans hv)

end Wikipedia.SmoothSixDPoincare.MorseHandle
