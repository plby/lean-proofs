import Wikipedia.HopfProblem.SpecialPeriodsModularCoverDegree
import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftAction
import Mathlib.Data.Countable.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

/-!
# Alignment of analytic lifts of the modular j-function

A countable family of analytic functions cannot cover another analytic
function pointwise on a connected open domain without one family member
agreeing everywhere. Baire's theorem supplies a genuine open agreement set,
and the analytic identity principle propagates the agreement. Applied to
the modular orbit theorem, this fixes a single modular transformation for
two lifts, including across elliptic values.
-/

noncomputable section

open Filter Function Metric Set UpperHalfPlane
open scoped Topology MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift

/-- Integer modular matrices form a countable group. -/
theorem modularGroup_countable : Countable SL(2, ℤ) := by
  unfold Matrix.SpecialLinearGroup Matrix
  infer_instance

/-- Countably many analytic candidate functions cannot require genuinely
different pointwise choices throughout a connected open domain. -/
theorem exists_eqOn_of_countable_analytic_cover {ι : Type*} [Countable ι]
    {U : Set ℂ} {f : ℂ → ℂ} {g : ι → ℂ → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUn : U.Nonempty)
    (hf : AnalyticOnNhd ℂ f U) (hg : ∀ i, AnalyticOnNhd ℂ (g i) U)
    (hcover : ∀ z ∈ U, ∃ i, f z = g i z) :
    ∃ i, EqOn f (g i) U := by
  let : BaireSpace U := hU.baireSpace
  obtain ⟨a, ha⟩ := hUn
  let : Nonempty U := ⟨⟨a, ha⟩⟩
  let C : ι → Set U := fun i => {z | f z = g i z}
  have hC (i : ι) : IsClosed (C i) :=
    isClosed_eq hf.continuousOn.domRestrict (hg i).continuousOn.domRestrict
  have hCU : ⋃ i, C i = univ := by
    ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hcover z z.2
  obtain ⟨i, z, hz⟩ := nonempty_interior_of_iUnion_of_closed hC hCU
  let V : Set ℂ := Subtype.val '' interior (C i)
  have hV : IsOpen V := hU.isOpenMap_subtype_val _ isOpen_interior
  have hzV : (z : ℂ) ∈ V := mem_image_of_mem Subtype.val hz
  have heq : f =ᶠ[𝓝 (z : ℂ)] g i := by
    filter_upwards [hV.mem_nhds hzV] with w hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hvC : v ∈ C i := interior_subset hv
    exact hvC
  exact ⟨i, hf.eqOn_of_preconnected_of_eventuallyEq (hg i) hUc z.2 heq⟩

/-- Two analytic representatives of the same modular function on a
connected open domain differ by one fixed modular transformation. -/
theorem exists_modular_alignment {U : Set ℂ} {τ σ : ℂ → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUn : U.Nonempty)
    (hτ : AnalyticOnNhd ℂ τ U) (hσ : AnalyticOnNhd ℂ σ U)
    (hτU : MapsTo τ U upperHalfPlaneSet) (hσU : MapsTo σ U upperHalfPlaneSet)
    (hJ : EqOn (fun z => modularJ (ofComplex (τ z)))
      (fun z => modularJ (ofComplex (σ z))) U) :
    ∃ γ : SL(2, ℤ), EqOn τ (fun z => ((γ • ofComplex (σ z) : ℍ) : ℂ)) U := by
  let : Countable SL(2, ℤ) := modularGroup_countable
  apply exists_eqOn_of_countable_analytic_cover hU hUc hUn hτ
    (fun γ => analyticOnNhd_modular_smul γ hσ hσU)
  intro z hz
  obtain ⟨γ, hγ⟩ :=
    (modularJ_eq_iff_exists_smul (ofComplex (τ z)) (ofComplex (σ z))).mp (hJ hz)
  refine ⟨γ, ?_⟩
  have hc := congrArg (fun w : ℍ => (w : ℂ)) hγ
  rw [ofComplex_apply_of_im_pos (hτU hz)] at hc
  exact hc.symm

/-- The same alignment stated in the actual upper half-plane. -/
theorem exists_modular_alignment_ofComplex {U : Set ℂ} {τ σ : ℂ → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUn : U.Nonempty)
    (hτ : AnalyticOnNhd ℂ τ U) (hσ : AnalyticOnNhd ℂ σ U)
    (hτU : MapsTo τ U upperHalfPlaneSet) (hσU : MapsTo σ U upperHalfPlaneSet)
    (hJ : EqOn (fun z => modularJ (ofComplex (τ z)))
      (fun z => modularJ (ofComplex (σ z))) U) :
    ∃ γ : SL(2, ℤ), ∀ z ∈ U, ofComplex (τ z) = γ • ofComplex (σ z) := by
  obtain ⟨γ, hγ⟩ := exists_modular_alignment hU hUc hUn hτ hσ hτU hσU hJ
  refine ⟨γ, ?_⟩
  intro z hz
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos (hτU hz)]
  exact hγ hz

/-- Analytic lift germs with equal modular values differ by a fixed
modular transformation on an actual neighborhood of their center. -/
theorem exists_modular_alignment_germ {τ σ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hσ : AnalyticAt ℂ σ a)
    (hτa : 0 < (τ a).im) (hσa : 0 < (σ a).im)
    (hJ : (fun z => modularJ (ofComplex (τ z))) =ᶠ[𝓝 a]
      (fun z => modularJ (ofComplex (σ z)))) :
    ∃ γ : SL(2, ℤ), τ =ᶠ[𝓝 a] (fun z => ((γ • ofComplex (σ z) : ℍ) : ℂ)) := by
  have hpτ : ∀ᶠ z in 𝓝 a, τ z ∈ upperHalfPlaneSet :=
    hτ.continuousAt.preimage_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds hτa)
  have hpσ : ∀ᶠ z in 𝓝 a, σ z ∈ upperHalfPlaneSet :=
    hσ.continuousAt.preimage_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds hσa)
  have hn : {z | AnalyticAt ℂ τ z ∧ AnalyticAt ℂ σ z ∧
      τ z ∈ upperHalfPlaneSet ∧ σ z ∈ upperHalfPlaneSet ∧
      modularJ (ofComplex (τ z)) = modularJ (ofComplex (σ z))} ∈ 𝓝 a :=
    hτ.eventually_analyticAt.and (hσ.eventually_analyticAt.and (hpτ.and (hpσ.and hJ)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨γ, hγ⟩ := exists_modular_alignment isOpen_ball
    (convex_ball a ε).isPreconnected ⟨a, mem_ball_self hε⟩
    (fun z hz => (hball hz).1) (fun z hz => (hball hz).2.1)
    (fun z hz => (hball hz).2.2.1) (fun z hz => (hball hz).2.2.2.1)
    (fun z hz => (hball hz).2.2.2.2)
  exact ⟨γ, eventually_of_mem (ball_mem_nhds a hε) (fun _ hz => hγ hz)⟩

end Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift
