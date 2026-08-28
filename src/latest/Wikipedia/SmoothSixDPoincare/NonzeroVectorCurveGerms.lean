import Wikipedia.SmoothSixDPoincare.LocalCurveEndpointGerms
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Smooth nonzero vector curves with prescribed endpoint germs

Use the actual open complement of zero in the normal model, with its inherited
smooth atlas. Local nonzero vector germs extend to this open manifold. Its
path connectedness in dimension at least two and relative smoothing then give
a globally nonzero smooth vector curve retaining both endpoint germs.
-/

noncomputable section

open Set Function Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.DiskFraming

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The genuine open complement of the zero vector, with the inherited manifold structure. -/
def puncturedModel : TopologicalSpace.Opens B := ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩

variable {B}

/-- A locally nonzero smooth vector germ extends into the actual punctured model. -/
theorem exists_smooth_punctured_curve_with_germ {a : ℝ → B} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ≠ 0) :
    ∃ f : C(ℝ, puncturedModel B), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ f ∧
      (fun t => (f t : B)) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → puncturedModel B := fun t =>
    if h : a t = 0 then ⟨a t₀, ha0⟩ else ⟨a t, h⟩
  let V := U ∩ a ⁻¹' ({0}ᶜ : Set B)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU
    isClosed_singleton.isOpen_compl
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) :
      (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hs0 : a s ≠ 0 := hs.2
    simp only [Function.comp_apply, A, dif_neg hs0]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ A V := by
    intro t ht
    have haAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ a t :=
      (ha.contDiffAt (hU.mem_nhds ht.1)).contMDiffAt
    have hvalAt := haAt.congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff (puncturedModel B) A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨f, hf, hfgerm⟩ := exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨f, hf, ?_⟩
  filter_upwards [hfgerm, hval htV] with t ht htval
  exact (congrArg Subtype.val ht).trans htval

variable [FiniteDimensional ℝ B]

/-- In dimension at least two, arbitrary nonzero endpoint germs admit a smooth nonzero join. -/
theorem exists_nonzero_smooth_curve_with_endpoint_germs {a b : ℝ → B} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V)
    (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (ha0 : a 0 ≠ 0) (hb1 : b 1 ≠ 0) (hdim : 2 ≤ Module.finrank ℝ B) :
    ∃ v : ℝ → B, ContDiff ℝ ∞ v ∧ (∀ t, v t ≠ 0) ∧
      (v =ᶠ[𝓝 (0 : ℝ)] a) ∧ (v =ᶠ[𝓝 (1 : ℝ)] b) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_punctured_curve_with_germ ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_smooth_punctured_curve_with_germ hb hV h1V hb1
  have hrank : 1 < Module.rank ℝ B := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ B by omega)
  let : PathConnectedSpace (puncturedModel B) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : B))
  let γ := PathConnectedSpace.somePath (a' 0) (b' 1)
  obtain ⟨f, hf, hfa, hfb⟩ := exists_smooth_curve_with_endpoint_germs a' b' ha' hb' γ
  let v : ℝ → B := fun t => (f t : B)
  have hv : ContDiff ℝ ∞ v :=
    ((contMDiff_subtype_val (I := 𝓘(ℝ, B)) (U := puncturedModel B)).comp hf).contDiff
  refine ⟨v, hv, fun t => (f t).property, ?_, ?_⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num), heqa] with t ht hta
    change t < 1 / 8 at ht
    exact (congrArg Subtype.val (hfa ht.le)).trans hta
  · filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num), heqb] with t ht htb
    change 7 / 8 < t at ht
    exact (congrArg Subtype.val (hfb ht.le)).trans htb

end Wikipedia.SmoothSixDPoincare.DiskFraming
