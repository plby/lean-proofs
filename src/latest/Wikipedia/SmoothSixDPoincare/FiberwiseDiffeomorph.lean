import Wikipedia.SmoothSixDPoincare.BoundarylessLocalInverse

/-!
# Smooth families of diffeomorphisms with the parameter retained

A jointly smooth family of genuine diffeomorphisms induces a diffeomorphism
of the product. The inverse is proved smooth by the native inverse function
theorem: the full differential is triangular, with the slice differential
and the identity on its diagonal.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FiberwiseDiffeomorph

variable {D H X P : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] {I : ModelWithCorners ℝ D H}
  [TopologicalSpace X] [ChartedSpace H X]

def retainParameter (F : X × P → X) (p : X × P) : X × P := (F p, p.2)

theorem contMDiff_retainParameter {F : X × P → X}
    (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F) :
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞ (retainParameter F) :=
  hF.prodMk contMDiff_snd

omit [TopologicalSpace X] [ChartedSpace H X] [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem bijective_retainParameter {F : X × P → X}
    (hF : ∀ s, Bijective (fun x => F (x, s))) : Bijective (retainParameter F) := by
  constructor
  · rintro ⟨x, s⟩ ⟨y, t⟩ heq
    have hst : s = t := congrArg Prod.snd heq
    subst t
    exact Prod.ext ((hF s).1 (congrArg Prod.fst heq)) rfl
  · rintro ⟨y, s⟩
    obtain ⟨x, hx⟩ := (hF s).2 y
    exact ⟨(x, s), Prod.ext hx rfl⟩

theorem mfderiv_retainParameter_apply {F : X × P → X}
    (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F) (p : X × P) (v : D × P) :
    mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p v =
      (mfderiv I I (fun x => F (x, p.2)) p.1 v.1 +
        mfderiv 𝓘(ℝ, P) I (fun s => F (p.1, s)) p.2 v.2, v.2) := by
  change mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (fun z => (F z, z.2)) p v = _
  rw [mfderiv_prodMk (hF.mdifferentiable (by simp) p) mdifferentiableAt_snd,
    mfderiv_snd]
  change ((mfderiv (I.prod 𝓘(ℝ, P)) I F p) v, v.2) = _
  exact Prod.ext (mfderiv_prod_eq_add_apply (v := v) (hF.mdifferentiable (by simp) p)) rfl

variable [FiniteDimensional ℝ D] [FiniteDimensional ℝ P]

/-- The triangular native differential is invertible, with no assumption about a joint inverse. -/
theorem isInvertible_mfderiv_retainParameter {F : X × P → X}
    (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F)
    (hslice : ∀ s, ∃ d : Diffeomorph I I X X ∞, ∀ x, d x = F (x, s))
    (p : X × P) :
    (mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p).IsInvertible := by
  let A : D →L[ℝ] D := mfderiv I I (fun x => F (x, p.2)) p.1
  let B : P →L[ℝ] D := mfderiv 𝓘(ℝ, P) I (fun s => F (p.1, s)) p.2
  have hA : Bijective A := by
    obtain ⟨d, hd⟩ := hslice p.2
    have heq : (fun x => F (x, p.2)) = d := funext (fun x => (hd x).symm)
    change Bijective (mfderiv I I (fun x => F (x, p.2)) p.1)
    rw [heq]
    exact (d.mfderivToContinuousLinearEquiv (by simp) p.1).bijective
  let L : (D × P) →L[ℝ] (D × P) :=
    mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p
  have hL (v : D × P) : L v = (A v.1 + B v.2, v.2) :=
    mfderiv_retainParameter_apply hF p v
  have hbij : Bijective L := by
    constructor
    · intro u v huv
      have hs : u.2 = v.2 := by simpa only [hL] using congrArg Prod.snd huv
      have hx : A u.1 + B u.2 = A v.1 + B v.2 := by
        simpa only [hL] using congrArg Prod.fst huv
      rw [hs] at hx
      exact Prod.ext (hA.1 (add_right_cancel hx)) hs
    · intro v
      obtain ⟨x, hx⟩ := hA.2 (v.1 - B v.2)
      refine ⟨(x, v.2), ?_⟩
      rw [hL, hx, sub_add_cancel]
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv, rfl⟩

variable [I.Boundaryless] [IsManifold I ∞ X]

/-- Retaining the parameter turns a smooth family of slice diffeomorphisms
into one diffeomorphism. -/
def diffeomorph {F : X × P → X}
    (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F)
    (hslice : ∀ s, ∃ d : Diffeomorph I I X X ∞, ∀ x, d x = F (x, s)) :
    Diffeomorph (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (X × P) (X × P) ∞ := by
  have hlocal : IsLocalDiffeomorph (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞
      (retainParameter F) := by
    intro p
    exact isLocalDiffeomorphAt_boundaryless isOpen_univ (mem_univ p)
      (contMDiff_retainParameter hF).contMDiffOn
      (isInvertible_mfderiv_retainParameter hF hslice p)
  apply hlocal.diffeomorphOfBijective
  apply bijective_retainParameter
  intro s
  obtain ⟨d, hd⟩ := hslice s
  have heq : (fun x => F (x, s)) = d := funext (fun x => (hd x).symm)
  rw [heq]
  exact d.bijective

theorem diffeomorph_apply {F : X × P → X}
    (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F)
    (hslice : ∀ s, ∃ d : Diffeomorph I I X X ∞, ∀ x, d x = F (x, s))
    (p : X × P) : diffeomorph hF hslice p = (F p, p.2) := rfl

end Wikipedia.SmoothSixDPoincare.FiberwiseDiffeomorph
