import Wikipedia.HopfProblem.SmoothMorseLemmaBilinear
import Wikipedia.HopfProblem.SmoothMorseLemmaInverse

/-!
# Native quadratic charts from smooth congruence

This is the analytic assembly step of the Morse lemma. A smooth family
of congruences equal to the identity at the center gives the literal map
`x ↦ L (A x) x`. Its derivative is the identity. The proved smooth inverse
theorem therefore constructs a genuine native partial diffeomorphism;
both normal-form identities refer to its actual forward and inverse maps.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A smooth congruence factor yields an actual smooth quadratic chart.
This helper is used with the integral Taylor factor and the congruence
factor constructed by the inverse-function theorem. -/
theorem exists_quadratic_chart_of_smooth_congruence
    (f : E → ℝ) (A : E → SymmetricForm E) (hA : ContDiff ℝ ∞ A)
    (H : SymmetricForm E) (hA0 : A 0 = H)
    (hfactor : ∀ x, f x = f 0 + (1 / 2 : ℝ) * (A x).val x x)
    (V : Set (SymmetricForm E)) (hV : IsOpen V) (hHV : H ∈ V)
    (L : SymmetricForm E → E →L[ℝ] E) (hL : ContDiffOn ℝ ∞ L V)
    (hL0 : L H = ContinuousLinearMap.id ℝ E)
    (hcong : ∀ B ∈ V, congruence H.val (L B) = B.val) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (0 : E) ∈ e.source ∧ e 0 = 0 ∧
      HasFDerivAt e (ContinuousLinearMap.id ℝ E) 0 ∧
      (∀ x ∈ e.source, f x = f 0 + (1 / 2 : ℝ) * H.val (e x) (e x)) ∧
      (∀ y ∈ e.target, f (e.symm y) = f 0 + (1 / 2 : ℝ) * H.val y y) := by
  let U : Set E := A ⁻¹' V
  have hU : IsOpen U := hV.preimage hA.continuous
  have h0 : (0 : E) ∈ U := by
    change A 0 ∈ V
    rw [hA0]
    exact hHV
  have hLA : ContDiffOn ℝ ∞ (fun x => L (A x)) U :=
    hL.comp hA.contDiffOn (fun _ hx => hx)
  let φ : E → E := fun x => L (A x) x
  have hφ : ContDiffOn ℝ ∞ φ U := hLA.clm_apply contDiffOn_id
  have hLA0 : L (A 0) = ContinuousLinearMap.id ℝ E := by rw [hA0, hL0]
  have hd : HasFDerivAt φ (ContinuousLinearMap.id ℝ E) 0 := by
    have h := ((hLA.contDiffAt (hU.mem_nhds h0)).differentiableAt (by simp)).hasFDerivAt
    simpa only [id_eq, hLA0, ContinuousLinearMap.comp_id, map_zero, add_zero] using
      h.clm_apply (hasFDerivAt_id (0 : E))
  obtain ⟨e, he0, heU, he⟩ := exists_partialDiffeomorph_of_contDiffOn
    hU hφ 0 h0 (ContinuousLinearEquiv.refl ℝ E) hd
  have heφ : (e : E → E) = φ := funext he
  have hezero : e 0 = 0 := by
    rw [he]
    exact map_zero (L (A 0))
  have hnormal (x : E) (hx : x ∈ e.source) :
      f x = f 0 + (1 / 2 : ℝ) * H.val (e x) (e x) := by
    have hquad := congrArg (fun B : Bilinear E => B x x) (hcong (A x) (heU hx))
    change H.val (L (A x) x) (L (A x) x) = (A x).val x x at hquad
    rw [he]
    change f x = f 0 + (1 / 2 : ℝ) * H.val (L (A x) x) (L (A x) x)
    rw [hquad]
    exact hfactor x
  refine ⟨e, he0, hezero, ?_, hnormal, ?_⟩
  · rw [heφ]
    exact hd
  · intro y hy
    have hr : e (e.symm y) = y := e.right_inv hy
    simpa only [hr] using hnormal (e.symm y) (e.map_target hy)

end Wikipedia.HopfProblem.SmoothMorseLemma
