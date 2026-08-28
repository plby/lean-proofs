import Wikipedia.SmoothSixDPoincare.AmbientBumpTranslations
import Wikipedia.SmoothSixDPoincare.FiberwiseDiffeomorph
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Supported fiberwise translations retaining every normal coordinate

A small smooth displacement depending on a vector parameter gives a jointly
smooth isotopy of the product with that parameter space. The parameter is
fixed exactly, and the entire fiber is fixed wherever the displacement is
zero. The inverse is smooth by the triangular native derivative theorem.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E F H M P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)

def normalBumpFamily (β : E → ℝ) (b : P → E) (p : ℝ × (M × P)) : M × P :=
  (bumpFamily Φ β (-(Real.smoothTransition p.1 • b p.2.2), p.2.1), p.2.2)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem normalBumpFamily_normal (β : E → ℝ) (b : P → E) (t : ℝ) (z : M × P) :
    (normalBumpFamily Φ β b (t, z)).2 = z.2 := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem normalBumpFamily_zero (β : E → ℝ) (b : P → E) (z : M × P) :
    normalBumpFamily Φ β b (0, z) = z := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition 0 • b z.2), z.1) = z.1
    rw [Real.smoothTransition.zero, zero_smul, neg_zero, bumpFamily_zero]
  · rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem normalBumpFamily_fixed_fiber (β : E → ℝ) (b : P → E) {u : P} (hu : b u = 0)
    (t : ℝ) (x : M) : normalBumpFamily Φ β b (t, (x, u)) = (x, u) := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition t • b u), x) = x
    rw [hu, smul_zero, neg_zero, bumpFamily_zero]
  · rfl

omit [NormedSpace ℝ P] in
theorem normalBumpFamily_fixed_outside (β : E → ℝ) (b : P → E) (t : ℝ) (z : M × P)
    (hz : z ∉ (Φ '' tsupport β) ×ˢ tsupport b) : normalBumpFamily Φ β b (t, z) = z := by
  by_cases hu : z.2 ∈ tsupport b
  · have hx : z.1 ∉ Φ '' tsupport β := fun hx => hz ⟨hx, hu⟩
    exact Prod.ext (bumpFamily_fixed_outside Φ β _ hx) rfl
  · have hb : b z.2 = 0 := by
      by_contra hb
      exact hu (subset_tsupport b hb)
    exact normalBumpFamily_fixed_fiber Φ β b hb t z.1

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem normalBumpFamily_chart (β : E → ℝ) (b : P → E) {x : E} (hx : x ∈ Φ.source)
    (u : P) : normalBumpFamily Φ β b (1, (Φ x, u)) = (Φ (x - β x • b u), u) := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition 1 • b u), Φ x) = _
    rw [Real.smoothTransition.one, one_smul, bumpFamily_chart Φ β _ hx,
      smul_neg, ← sub_eq_add_neg]
  · rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ P]
  [J.Boundaryless] [IsManifold J ∞ M] [T2Space M]

/-- A small-displacement bound constructs native isotopies preserving the full vector parameter. -/
theorem exists_radius_normalBumpFamily {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b : P → E, ContDiff ℝ ∞ b → HasCompactSupport b →
      (∀ u, ‖b u‖ < ε) →
      ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) (J.prod 𝓘(ℝ, P)) ∞
        (normalBumpFamily Φ β b) ∧
      (∀ t, ∃ D : Diffeomorph (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P))
        (M × P) (M × P) ∞, ∀ z, D z = normalBumpFamily Φ β b (t, z)) ∧
      IsCompact ((Φ '' tsupport β) ×ˢ tsupport b) := by
  obtain ⟨ε, hε, hdiff, hsmooth, -⟩ :=
    exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro b hb hbcompact hbound
  have hsmall (t : ℝ) (u : P) : ‖-(Real.smoothTransition t • b u)‖ < ε := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact (mul_le_of_le_one_left (norm_nonneg (b u))
      (Real.smoothTransition.le_one t)).trans_lt (hbound u)
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hvec : ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) 𝓘(ℝ, E) ∞
      (fun p : ℝ × (M × P) => Real.smoothTransition p.1 • b p.2.2) :=
    (hθ.comp contMDiff_fst).smul (hb.contMDiff.comp (contMDiff_snd.comp contMDiff_snd))
  have hneg : ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) 𝓘(ℝ, E) ∞
      (fun p : ℝ × (M × P) => -(Real.smoothTransition p.1 • b p.2.2)) :=
    (show ContDiff ℝ ∞ (fun x : E => -x) from contDiff_neg).contMDiff.comp hvec
  have hparam : ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P)))
      (𝓘(ℝ, E).prod J) ∞
      (fun p : ℝ × (M × P) => (-(Real.smoothTransition p.1 • b p.2.2), p.2.1)) :=
    hneg.prodMk (contMDiff_fst.comp contMDiff_snd)
  have hfirst : ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) J ∞
      (fun p : ℝ × (M × P) =>
        bumpFamily Φ β (-(Real.smoothTransition p.1 • b p.2.2), p.2.1)) := by
    intro p
    exact (hsmooth _ (hsmall p.1 p.2.2)).comp p hparam.contMDiffAt
  refine ⟨hfirst.prodMk (contMDiff_snd.comp contMDiff_snd), ?_, ?_⟩
  · intro t
    have ht : ContMDiff (J.prod 𝓘(ℝ, P)) J ∞
        (fun z : M × P => bumpFamily Φ β (-(Real.smoothTransition t • b z.2), z.1)) :=
      hfirst.comp (contMDiff_const.prodMk contMDiff_id)
    have hslices : ∀ u : P, ∃ D : Diffeomorph J J M M ∞,
        ∀ x, D x = bumpFamily Φ β (-(Real.smoothTransition t • b u), x) :=
      fun u => hdiff _ (hsmall t u)
    exact ⟨FiberwiseDiffeomorph.diffeomorph ht hslices, fun _ => rfl⟩
  · exact (hcompact.isCompact.image_of_continuousOn
      (Φ.contMDiffOn_toFun.continuousOn.mono hsupport)).prod hbcompact.isCompact

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
