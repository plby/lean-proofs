import Wikipedia.NoExoticSixSphere.RelativeSphereNormalization
import Mathlib.Topology.Separation.Regular

/-!
# Smooth representatives preserving a specified fiber

For a continuous sphere-valued map from a compact smooth manifold, smoothness
near one fiber suffices to smooth the entire map without changing that fiber
or the map on a smaller neighborhood of it. Compactness supplies a positive
separation from the distinguished value outside the protected neighborhood.
-/

open scoped Manifold ContDiff Topology
open Set

namespace NoExoticSixSphere

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

omit [T2Space M] in
theorem sphere_fiber_separation (n : ℕ) (f : C(M, Sphere n)) (a : Sphere n)
    (S : Set M) (hprotect : ∀ x, f x = a → x ∈ interior S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∉ interior S, δ ≤ dist (f x) a := by
  by_cases hne : (interior S)ᶜ.Nonempty
  · have hc : IsCompact (interior S)ᶜ := isOpen_interior.isClosed_compl.isCompact
    obtain ⟨x, hx, hmin⟩ := hc.exists_isMinOn hne (f.continuous.dist continuous_const).continuousOn
    refine ⟨dist (f x) a, dist_pos.mpr (fun h ↦ hx (hprotect x h)), ?_⟩
    exact fun y hy ↦ hmin hy
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

theorem exists_smoothSphereRepresentative_rel_fiber (n : ℕ) (f : C(M, Sphere n))
    (a : Sphere n) {S U : Set M} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hfU : ContMDiffOn I (𝓡 n) ∞ f U)
    (hprotect : ∀ x, f x = a → x ∈ interior S) :
    ∃ g : C(M, Sphere n), ContMDiff I (𝓡 n) ∞ g ∧ f.HomotopicRel g S ∧
      ∀ x, g x = a ↔ f x = a := by
  obtain ⟨δ, hδ, hsep⟩ := sphere_fiber_separation n f a S hprotect
  obtain ⟨g, hg, hrel, hclose⟩ := exists_smoothSphereApproximation_rel (I := I) n f
    hS hU hfU (δ / 2) (by positivity)
  refine ⟨g, hg, hrel, fun x ↦ ?_⟩
  constructor
  · intro hga
    by_cases hx : x ∈ S
    · exact (hrel.fst_eq_snd hx).trans hga
    · have hxi : x ∉ interior S := fun h ↦ hx (interior_subset h)
      have hdist := hsep x hxi
      have hsmall := hclose x
      rw [hga, dist_comm] at hsmall
      linarith
  · intro hfa
    exact (hrel.fst_eq_snd (interior_subset (hprotect x hfa))).symm.trans hfa

theorem exists_smoothSphereRepresentative_preserving_fiber (n : ℕ) (f : C(M, Sphere n))
    (a : Sphere n) {U : Set M} (hU : IsOpen U)
    (hfU : ContMDiffOn I (𝓡 n) ∞ f U) (hfiber : f ⁻¹' {a} ⊆ U) :
    ∃ g : C(M, Sphere n), ContMDiff I (𝓡 n) ∞ g ∧ f.Homotopic g ∧
      (∀ x, g x = a ↔ f x = a) ∧
      ∃ V : Set M, IsOpen V ∧ f ⁻¹' {a} ⊆ V ∧ EqOn g f V := by
  have hK : IsCompact (f ⁻¹' {a}) := (isClosed_singleton.preimage f.continuous).isCompact
  obtain ⟨V, hV, hKV, hVU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hfiber)
  have hprotect : ∀ x, f x = a → x ∈ interior (closure V) := by
    intro x hx
    exact interior_maximal subset_closure hV (hKV hx)
  obtain ⟨g, hg, hrel, heq⟩ := exists_smoothSphereRepresentative_rel_fiber (I := I) n f a
    isClosed_closure (hU.mem_nhdsSet.mpr hVU) hfU hprotect
  exact ⟨g, hg, hrel.homotopic, heq, V, hV, hKV,
    fun _ hx ↦ (hrel.fst_eq_snd (subset_closure hx)).symm⟩

end NoExoticSixSphere
