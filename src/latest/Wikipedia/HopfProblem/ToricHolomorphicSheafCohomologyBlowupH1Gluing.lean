import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Charts

/-!
# Local holomorphic gluing on the actual incidence blowup

The chart functions need agree only over the specified open subset, not
outside it. Their common function is proved holomorphic by agreement on
an actual neighborhood with a fixed chart representative.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1

open AffineBlowup ToricCharts

def CompatibleOn (U : Set Space) (a : Bool → ℂ × ℂ → ℂ) : Prop :=
  ∀ b c q p, chartMap b q = chartMap c p → chartMap b q ∈ U → a b q = a c p

theorem compatibleOn_of_cross {U : Set Space} {a : Bool → ℂ × ℂ → ℂ}
    (ha : ∀ q, q.2 ≠ 0 → chartMap false q ∈ U → a false q = a true (cross q)) :
    CompatibleOn U a := by
  intro b c q p he hU
  by_cases hbc : b = c
  · subst c
    rw [(chartMap_isOpenEmbedding b).injective he]
  · have hc : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    obtain ⟨hq, hp⟩ := (chartMap_cross_eq_iff b q p).mp he
    subst p
    cases b
    · exact ha q hq hU
    · have hm : chartMap false (cross q) ∈ U := by
        change chartMap (!true) (cross q) ∈ U
        rw [chartMap_cross true q hq]
        exact hU
      have h := ha (cross q) (inv_ne_zero hq) hm
      rw [cross_cross q hq] at h
      exact h.symm

def chartGlue (a : Bool → ℂ × ℂ → ℂ) (x : Space) : ℂ :=
  a (preferredChart x) (chartCoords (preferredChart x) x)

theorem chartGlue_eq_on_target {U : Set Space} (a : Bool → ℂ × ℂ → ℂ)
    (ha : CompatibleOn U a) (b : Bool) (x : Space) (hx : x ∈ U)
    (hxb : x ∈ affineTarget b) : chartGlue a x = a b (chartCoords b x) := by
  apply ha (preferredChart x) b
  · exact (chartMap_chartCoords _ x (preferred_mem x)).trans
      (chartMap_chartCoords b x hxb).symm
  · rwa [chartMap_chartCoords _ x (preferred_mem x)]

theorem chartGlue_chartMap {U : Set Space} (a : Bool → ℂ × ℂ → ℂ)
    (ha : CompatibleOn U a) (b : Bool) (q : ℂ × ℂ) (hq : chartMap b q ∈ U) :
    chartGlue a (chartMap b q) = a b q := by
  rw [chartGlue_eq_on_target a ha b _ hq (chartMap_mem_target b q), chartCoords_chartMap]

theorem chartGlue_contMDiffOn {U : Set Space} (hU : IsOpen U)
    (a : Bool → ℂ × ℂ → ℂ) (ha : CompatibleOn U a)
    (hhol : ∀ b, AnalyticOnNhd ℂ (a b) (chartMap b ⁻¹' U)) :
    ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω (chartGlue a) U := by
  intro x hx
  let b := preferredChart x
  have hxb : x ∈ affineTarget b := preferred_mem x
  have hcoords : chartCoords b x ∈ chartMap b ⁻¹' U := by
    change chartMap b (chartCoords b x) ∈ U
    rwa [chartMap_chartCoords b x hxb]
  have hg : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) ω (a b) (chartCoords b x) :=
    (hhol b _ hcoords).contDiffAt.contMDiffAt
  have hc := (chartCoords_holomorphicOn b).contMDiffAt
    ((affineTarget_isOpen b).mem_nhds hxb)
  have hcomp : ContMDiffAt 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω
      (fun y => a b (chartCoords b y)) x := hg.comp x hc
  apply (hcomp.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hU.mem_nhds hx, (affineTarget_isOpen b).mem_nhds hxb] with y hy hyb
  exact chartGlue_eq_on_target a ha b y hy hyb

theorem analyticOnNhd_comp_chartMap {U : Set Space} (hU : IsOpen U)
    {f : Space → ℂ} (hf : ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω f U) (b : Bool) :
    AnalyticOnNhd ℂ (f ∘ chartMap b) (chartMap b ⁻¹' U) := by
  intro q hq
  have hg := hf.contMDiffAt (hU.mem_nhds hq)
  exact (hg.comp q (chartMap_holomorphic b q)).contDiffAt.analyticAt

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1
