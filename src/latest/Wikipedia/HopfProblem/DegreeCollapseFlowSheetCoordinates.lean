import Wikipedia.HopfProblem.DegreeCollapseNativeVerticalCylinderFlow

/-!
# Actual endpoint flow sheets have their prescribed cylinder labels

An original endpoint phase equation propagates under the complete native
flow to all times. The genuine inverse cylinder recovers the exact label.
The resulting actual flow sheet is smooth at the reference point using
only the original coordinate germs.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {D Z E M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem phase_slice_flow_coordinates
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : A.source = U ×ˢ univ)
    (F : Flow ℝ M)
    (hflow : ∀ z ∈ U, ∀ s t : ℝ, F t (A (z, s)) = A (z, s + t))
    (Q : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞) (hQU : Q.target ⊆ U)
    (S : D → M) (v : D → ℝ) (T : ℝ)
    (hphase : ∀ u ∈ Q.source, S u = A (Q u, T + v u)) :
    ∀ u ∈ Q.source, ∀ t : ℝ,
      F (t - T) (S u) = A (Q u, t + v u) ∧
      A.symm (F (t - T) (S u)) = (Q u, t + v u) := by
  intro u hu t
  have hq := hQU (Q.map_source' hu)
  have hh : F (t - T) (S u) = A (Q u, t + v u) := by
    rw [hphase u hu, hflow (Q u) hq]
    exact congrArg (fun s : ℝ => A (Q u, s)) (by ring)
  refine ⟨hh, ?_⟩
  rw [hh]
  apply A.left_inv'
  rw [hsource]
  exact ⟨hq, mem_univ _⟩

theorem phase_flow_sheet_contMDiffAt
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : A.source = U ×ˢ univ)
    (F : Flow ℝ M)
    (hflow : ∀ z ∈ U, ∀ s t : ℝ, F t (A (z, s)) = A (z, s + t))
    (Q : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞) (hQU : Q.target ⊆ U)
    (h0 : (0 : D) ∈ Q.source) (hQ0 : Q 0 = 0)
    (S : D → M) (v : D → ℝ) (T : ℝ)
    (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    (hphase : ∀ u ∈ Q.source, S u = A (Q u, T + v u)) :
    ContMDiffAt 𝓘(ℝ, ℝ × D) 𝓘(ℝ, E) ∞
      (fun w : ℝ × D => F (w.1 - T) (S w.2)) 0 := by
  have h0U : (0 : Z) ∈ U := hQ0 ▸ hQU (Q.map_source' h0)
  have h0A : ((0 : Z), (0 : ℝ)) ∈ A.source := by
    rw [hsource]
    exact ⟨h0U, mem_univ _⟩
  have hQ : ContDiffAt ℝ ∞ Q (0 : D) :=
    Q.contMDiffOn_toFun.contDiffOn.contDiffAt (Q.open_source.mem_nhds h0)
  have hparam : ContDiffAt ℝ ∞
      (fun w : ℝ × D => (Q w.2, w.1 + v w.2)) 0 :=
    (hQ.comp (f := fun w : ℝ × D => w.2) 0 contDiffAt_snd).prodMk
      (contDiffAt_fst.add (hv.contDiffAt.comp (f := fun w : ℝ × D => w.2) 0 contDiffAt_snd))
  have hAparam : (Q ((0 : ℝ × D).2), (0 : ℝ × D).1 + v (0 : ℝ × D).2) ∈ A.source := by
    simpa only [Prod.fst_zero, Prod.snd_zero, hQ0, hv0, add_zero] using h0A
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ × D) 𝓘(ℝ, E) ∞
      (fun w : ℝ × D => A (Q w.2, w.1 + v w.2)) 0 :=
    (A.contMDiffOn_toFun.contMDiffAt (A.open_source.mem_nhds hAparam)).comp
      (f := fun w : ℝ × D => (Q w.2, w.1 + v w.2)) 0 hparam.contMDiffAt
  have hnear : ∀ᶠ w : ℝ × D in 𝓝 0, w.2 ∈ Q.source :=
    continuous_snd.continuousAt.eventually (Q.open_source.mem_nhds h0)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnear] with w hw
  exact (phase_slice_flow_coordinates A hsource F hflow Q hQU S v T hphase w.2 hw w.1).1

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem phase_flow_subsheet_properties
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : A.source = U ×ˢ univ)
    (F : Flow ℝ M)
    (hflow : ∀ z ∈ U, ∀ s t : ℝ, F t (A (z, s)) = A (z, s + t))
    (Q : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞) (hQU : Q.target ⊆ U)
    (h0 : (0 : D) ∈ Q.source) (hQ0 : Q 0 = 0)
    (S : D → M) (v : D → ℝ) (T : ℝ)
    (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    (hphase : ∀ u ∈ Q.source, S u = A (Q u, T + v u)) (L : B →L[ℝ] D) :
    ContMDiffAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) ∞
      (fun w : ℝ × B => F (w.1 - T) (S (L w.2))) 0 ∧
      F (-T) (S (L 0)) = A 0 ∧
      (fun w : ℝ × B => (A.symm (F (w.1 - T) (S (L w.2)))).1) =ᶠ[𝓝 0]
        (fun w : ℝ × B => Q (L w.2)) := by
  have hbase := phase_flow_sheet_contMDiffAt A hsource F hflow Q hQU h0 hQ0 S v T hv hv0 hphase
  have hparam : ContDiff ℝ ∞ (fun w : ℝ × B => (w.1, L w.2)) :=
    contDiff_fst.prodMk (L.contDiff.comp contDiff_snd)
  have hparam0 : ((0 : ℝ × B).1, L (0 : ℝ × B).2) = (0 : ℝ × D) := by simp
  have hbase' : ContMDiffAt 𝓘(ℝ, ℝ × D) 𝓘(ℝ, E) ∞
      (fun w : ℝ × D => F (w.1 - T) (S w.2)) ((0 : ℝ × B).1, L (0 : ℝ × B).2) := by
    rw [hparam0]
    exact hbase
  refine ⟨hbase'.comp (f := fun w : ℝ × B => (w.1, L w.2)) 0 hparam.contMDiff.contMDiffAt,
    ?_, ?_⟩
  · have hh := (phase_slice_flow_coordinates A hsource F hflow Q hQU S v T hphase 0 h0 0).1
    change F (-T) (S (L 0)) = A ((0 : Z), (0 : ℝ))
    simpa only [map_zero, zero_sub, zero_add, hQ0, hv0] using hh
  · have hnear : ∀ᶠ w : ℝ × B in 𝓝 0, L w.2 ∈ Q.source :=
      (L.continuous.comp continuous_snd).continuousAt.eventually
        (Q.open_source.mem_nhds (by simpa using h0))
    filter_upwards [hnear] with w hw
    exact congrArg Prod.fst
      (phase_slice_flow_coordinates A hsource F hflow Q hQU S v T hphase (L w.2) hw w.1).2

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
