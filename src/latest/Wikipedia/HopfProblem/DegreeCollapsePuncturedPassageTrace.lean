import Wikipedia.HopfProblem.DegreeCollapseCylinderMeridianRelation

/-!
# The actual single-passage trace on the punctured parameter cylinder

Clamp the time coordinate to the original unit interval. Its unique
interior crossing has exactly one preimage under clamping. Thus the actual
trace on the cylinder with that point removed lands in the full obstacle
complement and agrees with the original family on the entire unit interval.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.PassageHomology

def clampTime : C(ℝ, ℝ) :=
  ⟨fun t => max 0 (min 1 t), continuous_const.max (continuous_const.min continuous_id)⟩

theorem clampTime_mem (t : ℝ) : clampTime t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clampTime_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clampTime t = t := by
  change max 0 (min 1 t) = t
  rw [min_eq_right ht.2, max_eq_right ht.1]

theorem clampTime_eq_interior_iff {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    clampTime t = τ ↔ t = τ := by
  constructor
  · intro he
    by_cases ht0 : t ≤ 0
    · have hc : clampTime t = 0 := by
        change max 0 (min 1 t) = 0
        rw [min_eq_right (ht0.trans zero_le_one), max_eq_left ht0]
      exact (hτ.1.ne (hc.symm.trans he)).elim
    by_cases ht1 : 1 ≤ t
    · have hc : clampTime t = 1 := by
        change max 0 (min 1 t) = 1
        rw [min_eq_left ht1, max_eq_right zero_le_one]
      exact (hτ.2.ne' (hc.symm.trans he)).elim
    exact (clampTime_of_mem ⟨(lt_of_not_ge ht0).le, (lt_of_not_ge ht1).le⟩).symm.trans he
  · intro he
    subst t
    exact clampTime_of_mem ⟨hτ.1.le, hτ.2.le⟩

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

def puncturedPassageTrace (H : C(ℝ × sphere (0 : E) 1, X)) (S : Set X)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (u : sphere (0 : E) 1)
    (hcross : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : sphere (0 : E) 1,
      H (t, v) ∈ S ↔ t = τ ∧ v = u) :
    C(({(τ, u)}ᶜ : Set (ℝ × sphere (0 : E) 1)), (Sᶜ : Set X)) where
  toFun p := ⟨H (clampTime p.val.1, p.val.2), by
    intro hp
    have he := (hcross _ (clampTime_mem _) p.val.2).mp hp
    exact p.property (Prod.ext ((clampTime_eq_interior_iff hτ _).mp he.1) he.2)⟩
  continuous_toFun := by
    have ht : Continuous (fun p : ({(τ, u)}ᶜ : Set (ℝ × sphere (0 : E) 1)) =>
        clampTime p.val.1) :=
      clampTime.continuous.comp (continuous_fst.comp continuous_subtype_val)
    have hv : Continuous (fun p : ({(τ, u)}ᶜ : Set (ℝ × sphere (0 : E) 1)) => p.val.2) :=
      continuous_snd.comp continuous_subtype_val
    exact (H.continuous.comp (ht.prodMk hv)).subtype_mk _

theorem puncturedPassageTrace_on_interval
    (H : C(ℝ × sphere (0 : E) 1, X)) (S : Set X)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (u : sphere (0 : E) 1)
    (hcross : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : sphere (0 : E) 1,
      H (t, v) ∈ S ↔ t = τ ∧ v = u)
    (p : ({(τ, u)}ᶜ : Set (ℝ × sphere (0 : E) 1)))
    (hp : p.val.1 ∈ Icc (0 : ℝ) 1) :
    (puncturedPassageTrace H S hτ u hcross p).val = H p.val := by
  change H (clampTime p.val.1, p.val.2) = H p.val
  rw [clampTime_of_mem hp]

end Wikipedia.HopfProblem.DegreeCollapse.PassageHomology
