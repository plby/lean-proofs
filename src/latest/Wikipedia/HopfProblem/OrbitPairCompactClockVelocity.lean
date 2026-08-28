import Wikipedia.HopfProblem.OrbitPairUnitClockVelocity
import Wikipedia.HopfProblem.OrbitPairSupportedFlow
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A complete supported ambient field with the prescribed track velocity

Multiply the unit-clock field by a real bump equal to one on [-2,2].
For a compact ambient target, the resulting field has compact support in
the original cylinder and therefore has the constructed global smooth
flow. The self model on the product is identified with the product of
self models by Mathlib's equality; neither the topology nor the atlas is
replaced. The clock component is the fixed scalar bump at every point.
-/

noncomputable section

open Set Function Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

def clockCutoff : ContDiffBump (0 : ℝ) where
  rIn := 2
  rOut := 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem clockCutoff_one {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) : clockCutoff t = 1 := by
  apply clockCutoff.one_of_mem_closedBall
  change dist t 0 ≤ 2
  rw [dist_zero_right, Real.norm_eq_abs]
  exact abs_le.mpr ht

theorem smooth_field_congr_model {E H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I J : ModelWithCorners ℝ E H}
    [hI : IsManifold I ∞ X] [hJ : IsManifold J ∞ X]
    (h : I = J) (w : X → E)
    (hw : ContMDiff I I.tangent ∞ (fun x => (⟨x, w x⟩ : TangentBundle I X))) :
    ContMDiff J J.tangent ∞ (fun x => (⟨x, w x⟩ : TangentBundle J X)) := by
  subst J
  exact hw

variable {G N : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  [T2Space N] [CompactSpace N]

theorem native_cylinder_isManifold :
    IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) ∞ (ℝ × N) := inferInstance

/-- Expose the literal native product atlas through the untagged model type
required by the existing local-flow API. The atlas data are unchanged. -/
abbrev cylinderChartedSpace : ChartedSpace (ℝ × G) (ℝ × N) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ G) (ℝ × N))

attribute [local instance] cylinderChartedSpace

theorem cylinder_isManifold : IsManifold 𝓘(ℝ, ℝ × G) ∞ (ℝ × N) := by
  simpa +instances only [modelWithCornersSelf_prod, cylinderChartedSpace] using
    (native_cylinder_isManifold (G := G) (N := N))

attribute [local instance] cylinder_isManifold

def clockSupportedField
    (v : (p : ℝ × N) → TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) p)
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)).tangent ∞
      (fun p => (⟨p, v p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) (ℝ × N)))) :
    SupportedFlow.Field (E := ℝ × G) (M := ℝ × N) where
  vector := fun p => clockCutoff p.1 • v p
  support := tsupport clockCutoff ×ˢ univ
  compact_support := clockCutoff.hasCompactSupport.isCompact.prod isCompact_univ
  smooth := by
    have hχ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × N => clockCutoff p.1) := clockCutoff.contDiff.contMDiff.comp contMDiff_fst
    have hs := hχ.smul_section hv
    have hs' := smooth_field_congr_model
      (hJ := by
        rw [modelWithCornersSelf_prod]
        exact native_cylinder_isManifold)
      (modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := G)).symm
      (fun p : ℝ × N => clockCutoff p.1 • v p) hs
    simpa +instances only [cylinderChartedSpace] using hs'
  zero_outside := by
    intro p hp
    have hn : p.1 ∉ tsupport clockCutoff := fun hx => hp ⟨hx, mem_univ _⟩
    rw [image_eq_zero_of_notMem_tsupport hn, zero_smul]
    rfl

theorem clockSupportedField_clock
    {v : (p : ℝ × N) → TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) p}
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)).tangent ∞
      (fun p => (⟨p, v p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) (ℝ × N))))
    (hclock : ∀ p, (v p).1 = 1) (p : ℝ × N) :
    ((clockSupportedField v hv).vector p).1 = clockCutoff p.1 := by
  change clockCutoff p.1 * (v p).1 = clockCutoff p.1
  rw [hclock, mul_one]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]

theorem exists_supported_clock_track_velocity {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) ∞ F)
    (hi : ∀ t, Injective (fun x => F (t, x)))
    (himm : ∀ t x, Injective (mfderiv I 𝓘(ℝ, G) (fun y => F (t, y)) x)) :
    ∃ v : SupportedFlow.Field (E := ℝ × G) (M := ℝ × N),
      (∀ p : ℝ × N, (v.vector p).1 = clockCutoff p.1) ∧
      ∀ q : ℝ × M, q.1 ∈ Icc (-2 : ℝ) 2 →
        v.vector (track F q) = (1, timeVelocity (I := I) (J := 𝓘(ℝ, G)) F q) := by
  obtain ⟨v, hv, hclock, hmatch⟩ := exists_unit_clock_track_velocity hF hi himm
  refine ⟨clockSupportedField v hv, clockSupportedField_clock hv hclock, ?_⟩
  intro q hq
  change clockCutoff q.1 • v (track F q) = _
  rw [clockCutoff_one hq, one_smul, hmatch]

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
