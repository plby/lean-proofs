import Wikipedia.HopfProblem.DegreeCollapseBirthLevelPreservation
import Wikipedia.SmoothSixDPoincare.RegularLevelSmoothMaps

/-!
# Identifying equal regular level sets in their original native atlases

The identity on ambient points is a genuine native diffeomorphism even when
the two defining functions differ away from the level. Smoothness in both
directions follows from the proved inclusion criterion for regular levels.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f g : M → ℝ} {a : ℝ}

def equalFiberDiffeomorph {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = b → y ∉ criticalPoints E g) (heq : ∀ y, g y = b ↔ f y = a) :
    let _ := RegularLevel.chartedSpace hf hfr
    let _ := RegularLevel.chartedSpace hg hgr
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      {y : M // f y = a} {y : M // g y = b} ∞ := by
  let _ := RegularLevel.chartedSpace hf hfr
  let _ := RegularLevel.chartedSpace hg hgr
  let F : {y : M // f y = a} → {y : M // g y = b} := fun y => ⟨y, (heq y).mpr y.property⟩
  let G : {y : M // g y = b} → {y : M // f y = a} := fun y => ⟨y, (heq y).mp y.property⟩
  exact {
    toFun := F
    invFun := G
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    contMDiff_toFun := (RegularLevel.contMDiff_iff_inclusion hg hgr
      𝓘(ℝ, RegularLevel.Model E) F).mpr (RegularLevel.contMDiff_inclusion hf hfr)
    contMDiff_invFun := (RegularLevel.contMDiff_iff_inclusion hf hfr
      𝓘(ℝ, RegularLevel.Model E) G).mpr (RegularLevel.contMDiff_inclusion hg hgr) }

def equalLevelDiffeomorph
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g) (heq : ∀ y, g y = a ↔ f y = a) :
    let _ := RegularLevel.chartedSpace hf hfr
    let _ := RegularLevel.chartedSpace hg hgr
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      {y : M // f y = a} {y : M // g y = a} ∞ :=
  equalFiberDiffeomorph hf hg hfr hgr heq

theorem equalLevelDiffeomorph_val
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g) (heq : ∀ y, g y = a ↔ f y = a)
    (y : {z : M // f z = a}) : (equalLevelDiffeomorph hf hg hfr hgr heq y).val = y.val := rfl

theorem equalLevelDiffeomorph_symm_val
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g) (heq : ∀ y, g y = a ↔ f y = a)
    (y : {z : M // g z = a}) :
    let _ := RegularLevel.chartedSpace hf hfr
    let _ := RegularLevel.chartedSpace hg hgr
    ((equalLevelDiffeomorph hf hg hfr hgr heq).symm y).val = y.val := by
  let _ := RegularLevel.chartedSpace hf hfr
  let _ := RegularLevel.chartedSpace hg hgr
  rfl

theorem regular_level_of_retained_critical_germs
    (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    {p q : M} (hcrit : ∀ y ∈ criticalPoints E g, y ∈ criticalPoints E f ∨ y = p ∨ y = q)
    (hkeep : ∀ y ∈ criticalPoints E f, g =ᶠ[𝓝 y] f)
    (hp : a < g p) (hq : a < g q) : ∀ y, g y = a → y ∉ criticalPoints E g := by
  intro y hy hcy
  rcases hcrit y hcy with hold | rfl | rfl
  · exact hfr y (((hkeep y hold).self_of_nhds).symm.trans hy) hold
  · exact hp.ne' hy
  · exact hq.ne' hy

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
