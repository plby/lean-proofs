import Wikipedia.SmoothSixDPoincare.LocalCurveEndpointGerms

/-!
# Embedded joins of local germs inside an actual open native manifold

Local endpoint curves can be globalized within a prescribed open target,
retaining their ambient germs. An actual path in that open target then
constructs a smooth embedded immersive connecting arc with both endpoint
germs unchanged. The entire connecting curve remains in the open target.
-/

noncomputable section

open Set Function Filter ContinuousMap TopologicalSpace
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

theorem exists_native_open_curve_with_germ (S : Opens N)
    {a : ℝ → N} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ∈ S) :
    ∃ g : C(ℝ, S), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧ (Subtype.val ∘ g) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → S := fun t => if h : a t ∈ S then ⟨a t, h⟩ else ⟨a t₀, ha0⟩
  let V := U ∩ a ⁻¹' (S : Set N)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU S.isOpen
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) : (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hsS : a s ∈ S := hs.2
    simp only [Function.comp_apply, A, dif_pos hsS]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ A V := by
    intro t ht
    have hvalAt := (ha.contMDiffAt (hU.mem_nhds ht.1)).congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff S A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨g, hg, heq⟩ := exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨g, hg, ?_⟩
  filter_upwards [heq, hval htV] with t ht hta
  exact (congrArg Subtype.val ht).trans hta

variable [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N] [T2Space N]

theorem exists_embedded_native_open_arc_with_local_germs (S : Opens N)
    {a b : ℝ → N} {U V : Set ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b V)
    (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (ha0 : a 0 ∈ S) (hb1 : b 1 ∈ S)
    (hia : Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Injective (mfderiv 𝓘(ℝ, ℝ) J b 1))
    (γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S))
    (hxy : a 0 ≠ b 1) (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, S), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
      ((Subtype.val ∘ g) =ᶠ[𝓝 (0 : ℝ)] a) ∧ ((Subtype.val ∘ g) =ᶠ[𝓝 (1 : ℝ)] b) ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  obtain ⟨a', ha', heqa⟩ := exists_native_open_curve_with_germ S ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_native_open_curve_with_germ S hb hV h1V hb1
  have hstart : a' 0 = (⟨a 0, ha0⟩ : S) := Subtype.ext heqa.eq_of_nhds
  have hend : b' 1 = (⟨b 1, hb1⟩ : S) := Subtype.ext heqb.eq_of_nhds
  have hia' : Injective (mfderiv 𝓘(ℝ, ℝ) J a' 0) := by
    have hi : Injective (mfderiv 𝓘(ℝ, ℝ) J (Subtype.val ∘ a') 0) := by
      rw [heqa.mfderiv_eq]
      exact hia
    rw [mfderiv_comp 0 ((contMDiff_subtype_val (I := J) (U := S) (n := ∞)).mdifferentiableAt (by simp))
      (ha'.mdifferentiableAt (by simp))] at hi
    intro x y hxy
    exact hi (congrArg (mfderiv J J (Subtype.val : S → N) (a' 0)) hxy)
  have hib' : Injective (mfderiv 𝓘(ℝ, ℝ) J b' 1) := by
    have hi : Injective (mfderiv 𝓘(ℝ, ℝ) J (Subtype.val ∘ b') 1) := by
      rw [heqb.mfderiv_eq]
      exact hib
    rw [mfderiv_comp 1 ((contMDiff_subtype_val (I := J) (U := S) (n := ∞)).mdifferentiableAt (by simp))
      (hb'.mdifferentiableAt (by simp))] at hi
    intro x y hxy
    exact hi (congrArg (mfderiv J J (Subtype.val : S → N) (b' 1)) hxy)
  have hxy' : a' 0 ≠ b' 1 := by
    intro h
    exact hxy (heqa.eq_of_nhds.symm.trans ((congrArg Subtype.val h).trans heqb.eq_of_nhds))
  obtain ⟨g, hg, hga, hgb, hemb, hi, -⟩ := exists_embedded_arc_with_endpoint_germs
    a' b' ha' hb' hia' hib' (γ.cast hstart hend) hxy' hdim (S := ∅) finite_empty
  refine ⟨g, hg, ?_, ?_, hemb, hi⟩
  · filter_upwards [hga, heqa] with t hta hta'
    exact (congrArg Subtype.val hta).trans hta'
  · filter_upwards [hgb, heqb] with t htb htb'
    exact (congrArg Subtype.val htb).trans htb'

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
