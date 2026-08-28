import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransportChain
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransportSubdivision

/-!
# Local smoothness of finite radial transport in fixed endpoint charts

For an actual finite subordinate chart chain, the same charts remain valid
for nearby radial endpoints. In fixed endpoint coordinates its transport is
locally an explicitly constructed smooth function. The preferred chart index
need not vary continuously: the genuine transition cocycle removes it from
each local formula. No global transport, global frame, or coherence datum is
assumed here.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationTransport
  PeriodTorusLineBundleClassificationConnection

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

/-- In fixed endpoint coordinates, adjoining a segment uses only its actual
chart transport and the actual starting transition. -/
theorem ChartChain.scalar_cons_in_coordinates {γ : ℝ → ComplexPlane₂}
    {a d b : ℝ} {n : ℕ} (k : ι) (had : a ≤ d)
    (hk : MapsTo γ (Icc a d) (A.baseSet k)) (C : ChartChain A γ d b n)
    (i j : ι) (hi : γ a ∈ A.baseSet i) :
    ((A.transition (A.indexAt (γ b)) j (γ b) : ℂ) * C.scalar *
      (A.transition k (A.indexAt (γ d)) (γ d) : ℂ)) *
        connectionTransport A k γ a d * (A.transition i k (γ a) : ℂ) =
      (A.transition (A.indexAt (γ b)) j (γ b) : ℂ) *
        (ChartChain.cons k had hk C).scalar *
          (A.transition i (A.indexAt (γ a)) (γ a) : ℂ) := by
  have ha := transition_mul A i (A.indexAt (γ a)) k (γ a) hi
    (A.mem_baseSet_at _) (hk (left_mem_Icc.mpr had))
  rw [ChartChain.scalar_cons]
  unfold segmentScalar
  rw [← ha]
  ring

variable [A.IsHolomorphic Iℂ]

/-- Evaluation of a radial path at a fixed time is smooth in its endpoint. -/
theorem radialCurve_endpoint_contDiff (a : ℝ) :
    ContDiff ℝ ∞ (fun x : ComplexPlane₂ => radialCurve x a) := by
  change ContDiff ℝ ∞ (fun x : ComplexPlane₂ => a • x)
  have hc : ContDiff ℝ ∞ (fun _ : ComplexPlane₂ => a) := contDiff_const
  have hx : ContDiff ℝ ∞ (fun x : ComplexPlane₂ => x) := contDiff_id
  exact hc.smul hx

/-- An actual transition, evaluated at a fixed radial time, is smooth near
an endpoint whose radial value belongs to the overlap. -/
theorem radial_transition_contDiffAt (i j : ι) (a : ℝ) (x₀ : ComplexPlane₂)
    (hi : radialCurve x₀ a ∈ A.baseSet i)
    (hj : radialCurve x₀ a ∈ A.baseSet j) :
    ContDiffAt ℝ ∞ (fun x => (A.transition i j (radialCurve x a) : ℂ)) x₀ := by
  have ht := (transition_contDiffOn A i j).contDiffAt
    (((A.isOpen_baseSet i).inter (A.isOpen_baseSet j)).mem_nhds ⟨hi, hj⟩)
  exact ht.comp x₀ (radialCurve_endpoint_contDiff a).contDiffAt

/-- A finite subordinate radial chain admits a genuinely smooth local
transport formula in any fixed endpoint charts. The nearby chains are
constructed, have the same length and endpoints, and need no supplied
compatibility or independence property. -/
theorem ChartChain.exists_contDiffAt_radial_scalar {x₀ : ComplexPlane₂}
    {a b : ℝ} {n : ℕ} (C : ChartChain A (radialCurve x₀) a b n)
    (i j : ι) (hi : radialCurve x₀ a ∈ A.baseSet i)
    (hj : radialCurve x₀ b ∈ A.baseSet j) :
    ∃ F : ComplexPlane₂ → ℂ, ContDiffAt ℝ ∞ F x₀ ∧
      ∃ U : Set ComplexPlane₂, IsOpen U ∧ x₀ ∈ U ∧
        ∀ x ∈ U, ∃ D : ChartChain A (radialCurve x) a b n,
          F x = (A.transition (A.indexAt (radialCurve x b)) j (radialCurve x b) : ℂ) *
            D.scalar * (A.transition i (A.indexAt (radialCurve x a)) (radialCurve x a) : ℂ) := by
  induction C generalizing i j with
  | nil a =>
      let U : Set ComplexPlane₂ :=
        {x | radialCurve x a ∈ A.baseSet i ∩ A.baseSet j}
      have hr : Continuous (fun x : ComplexPlane₂ => radialCurve x a) :=
        (radialCurve_endpoint_contDiff a).continuous
      refine ⟨(fun x => (A.transition i j (radialCurve x a) : ℂ)),
        radial_transition_contDiffAt A i j a x₀ hi hj, U,
        ((A.isOpen_baseSet i).inter (A.isOpen_baseSet j)).preimage hr,
        ⟨hi, hj⟩, ?_⟩
      intro x hx
      refine ⟨ChartChain.nil a, ?_⟩
      rw [ChartChain.scalar_nil, mul_one]
      exact (transition_mul A i (A.indexAt (radialCurve x a)) j
        (radialCurve x a) hx.1 (A.mem_baseSet_at _) hx.2).symm
  | @cons a d b n k had hk C ih =>
      have hka := hk (left_mem_Icc.mpr had)
      have hkd := hk (right_mem_Icc.mpr had)
      obtain ⟨F, hF, U, hUo, hxU, hUF⟩ := ih k j hkd hj
      obtain ⟨V, hVo, hxV, hVk⟩ := radial_segment_uniform_nhds A k a d x₀ hk
      let W : Set ComplexPlane₂ := {x | radialCurve x a ∈ A.baseSet i}
      have hWo : IsOpen W := (A.isOpen_baseSet i).preimage
        (radialCurve_endpoint_contDiff a).continuous
      have hT : ContDiffAt ℝ ∞ (radialTransport A k a d) x₀ :=
        radialTransport_contDiffAt A k a d x₀ (by
          rw [uIcc_of_le had]
          exact hk)
      refine ⟨(fun x => F x * radialTransport A k a d x *
        (A.transition i k (radialCurve x a) : ℂ)),
        (hF.mul hT).mul (radial_transition_contDiffAt A i k a x₀ hi hka),
        U ∩ V ∩ W, (hUo.inter hVo).inter hWo, ⟨⟨hxU, hxV⟩, hi⟩, ?_⟩
      intro x hx
      obtain ⟨D, hD⟩ := hUF x hx.1.1
      refine ⟨ChartChain.cons k had (hVk x hx.1.2) D, ?_⟩
      dsimp only
      rw [hD]
      exact ChartChain.scalar_cons_in_coordinates A k had (hVk x hx.1.2) D i j hx.2

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport
