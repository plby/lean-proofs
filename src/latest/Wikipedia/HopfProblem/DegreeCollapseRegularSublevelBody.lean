import Wikipedia.SmoothSixDPoincare.NativeSmoothBoundaryBodies
import Wikipedia.SmoothSixDPoincare.RegularBandDiffeomorph

/-!
# The actual regular sublevel as a body with its native smooth boundary

The body and boundary retain their literal subspace topologies and
inclusion. Across a regular band, the ambient diffeomorphism restricts
to a whole-body homeomorphism and a native boundary diffeomorphism,
with the exact commuting point identity.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularMorseSublevel

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ)
  (ha : ∀ p, f p = a → p ∉ criticalPoints E f)

def body : SmoothBoundaryBody 𝓘(ℝ, RegularLevel.Model E) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf ha
  let _ : CompactSpace {x : M // f x = a} :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ a} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  let i : C({x : M // f x = a}, {x : M // f x ≤ a}) :=
    ⟨fun x ↦ ⟨x.val, x.property.le⟩, continuous_subtype_val.subtype_mk _⟩
  exact SmoothBoundaryBody.ofEmbedding i
    (i.continuous.isClosedEmbedding (fun x y h ↦
      Subtype.ext (congrArg (fun z : {x : M // f x ≤ a} ↦ z.val) h)))

theorem body_inclusion_point (x : (body hf a ha).boundary) :
    ((body hf a ha).inclusion x).val = x.val := rfl

variable {a}

theorem exists_bodyEquiv_of_ambient {b : ℝ}
    (hb : ∀ p, f p = b → p ∉ criticalPoints E f)
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hlevel : D '' {x : M | f x = a} = {x : M | f x = b})
    (hsublevel : D '' {x : M | f x ≤ a} = {x : M | f x ≤ b}) :
    ∃ e : SmoothBoundaryBody.Equiv (body hf a ha) (body hf b hb),
      ∀ x, (e.body x).val = D x.val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨d, hd⟩ := RegularLevel.exists_levelDiffeomorph_of_ambient hf ha hb D hlevel
  have hiff (x : M) : f x ≤ a ↔ f (D x) ≤ b := by
    constructor
    · intro hx
      have h : D x ∈ D '' {y : M | f y ≤ a} := ⟨x, hx, rfl⟩
      rwa [hsublevel] at h
    · intro hx
      have h : D x ∈ D '' {y : M | f y ≤ a} := by rw [hsublevel]; exact hx
      obtain ⟨y, hy, he⟩ := h
      exact D.injective he ▸ hy
  let e := D.toHomeomorph.subtype (p := fun x ↦ f x ≤ a) (q := fun x ↦ f x ≤ b) hiff
  exact ⟨{ body := e, boundary := d, boundary_point := fun x ↦ Subtype.ext (hd x).symm },
    fun _ => rfl⟩

theorem nonempty_regularBandBodyEquiv {b : ℝ}
    (hb : ∀ p, f p = b → p ∉ criticalPoints E f) (hab : a ≤ b)
    (hband : ∀ p, f p ∈ Icc a b → p ∉ criticalPoints E f) :
    Nonempty (SmoothBoundaryBody.Equiv (body hf a ha) (body hf b hb)) := by
  obtain ⟨D, hlevel, hsublevel⟩ := RegularLevel.exists_ambient_regularBand_transport hf hab hband
  obtain ⟨e, _⟩ := exists_bodyEquiv_of_ambient hf ha hb D hlevel hsublevel
  exact ⟨e⟩

variable {ha}

theorem upperSmoothBody_eq {p : M} (d : MorseSurgeryData E f p) :
    d.upperSmoothBody hf = body hf (f p + d.radius ^ 2) d.upper_regular := rfl

theorem lowerSmoothBody_eq {p : M} (d : MorseSurgeryData E f p) :
    d.lowerSmoothBody hf = body hf (f p - d.radius ^ 2) d.lower_regular := rfl

end Wikipedia.HopfProblem.DegreeCollapse.RegularMorseSublevel
