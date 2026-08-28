import Wikipedia.SmoothSixDPoincare.LocalCurveEndpointGerms

/-!
# Smooth joins of local endpoint germs inside an actual open model

Extend each local curve into the open target without changing its germ.
An actual path in that open target then gives a globally smooth joining by
the proved relative curve-smoothing theorem. The resulting curve stays in
the target everywhere, not merely at the endpoints.
-/

noncomputable section

open Set Function Filter ContinuousMap Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  (S : TopologicalSpace.Opens B)

/-- Globalize a local smooth curve into the actual open model, retaining its full germ. -/
theorem exists_smooth_open_curve_with_germ {a : ℝ → B} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ∈ S) :
    ∃ f : C(ℝ, S), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ f ∧
      (fun t => (f t : B)) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → S := fun t => if h : a t ∈ S then ⟨a t, h⟩ else ⟨a t₀, ha0⟩
  let V := U ∩ a ⁻¹' (S : Set B)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU S.isOpen
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) : (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hsS : a s ∈ S := hs.2
    simp only [Function.comp_apply, A, dif_pos hsS]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ A V := by
    intro t ht
    have haAt := (ha.contDiffAt (hU.mem_nhds ht.1)).contMDiffAt
    have hvalAt := haAt.congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff S A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨f, hf, heq⟩ := exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨f, hf, ?_⟩
  filter_upwards [heq, hval htV] with t ht hta
  exact (congrArg Subtype.val ht).trans hta

/-- An actual path inside the open target joins both full local germs by a globally smooth curve. -/
theorem exists_smooth_open_curve_with_endpoint_germs {a b : ℝ → B} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V)
    (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (ha0 : a 0 ∈ S) (hb1 : b 1 ∈ S)
    (γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S)) :
    ∃ f : ℝ → B, ContDiff ℝ ∞ f ∧ (∀ t, f t ∈ S) ∧
      (f =ᶠ[𝓝 (0 : ℝ)] a) ∧ (f =ᶠ[𝓝 (1 : ℝ)] b) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_open_curve_with_germ S ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_smooth_open_curve_with_germ S hb hV h1V hb1
  have hstart : a' 0 = (⟨a 0, ha0⟩ : S) := Subtype.ext heqa.eq_of_nhds
  have hend : b' 1 = (⟨b 1, hb1⟩ : S) := Subtype.ext heqb.eq_of_nhds
  obtain ⟨f, hf, hfa, hfb⟩ := exists_smooth_curve_with_endpoint_germs a' b' ha' hb'
    (γ.cast hstart hend)
  refine ⟨fun t => (f t : B),
    ((contMDiff_subtype_val (I := 𝓘(ℝ, B)) (U := S)).comp hf).contDiff,
    fun t => (f t).property, ?_, ?_⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num), heqa] with t ht hta
    change t < 1 / 8 at ht
    exact (congrArg Subtype.val (hfa ht.le)).trans hta
  · filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num), heqb] with t ht htb
    change 7 / 8 < t at ht
    exact (congrArg Subtype.val (hfb ht.le)).trans htb

end Wikipedia.SmoothSixDPoincare
