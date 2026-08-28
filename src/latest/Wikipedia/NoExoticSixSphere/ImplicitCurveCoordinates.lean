import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local curve coordinates retaining the actual free parameter

If the derivative in the first factor is bijective, adjoining the unchanged
second factor makes the actual full derivative bijective. The smooth inverse
function theorem then gives local coordinates exactly `(Φ(p,s),s)`.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace NoExoticSixSphere.ImplicitCurve

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

variable {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ F] [FiniteDimensional ℝ K] in
theorem bijective_prod_snd (A : (P × K) →L[ℝ] F)
    (hA : Bijective (A.comp (ContinuousLinearMap.inl ℝ P K))) :
    Bijective (A.prod (ContinuousLinearMap.snd ℝ P K)) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨p, s⟩ h
    have hs : s = 0 := congrArg Prod.snd h
    subst s
    have hp : (A.comp (ContinuousLinearMap.inl ℝ P K)) p = 0 := congrArg Prod.fst h
    have hp0 : p = 0 := hA.injective (hp.trans (map_zero _).symm)
    simp [hp0]
  · rintro ⟨y, s⟩
    obtain ⟨p, hp⟩ := hA.surjective (y - A (0, s))
    refine ⟨(p, s), Prod.ext ?_ rfl⟩
    change A (p, s) = y
    change A (p, 0) = y - A (0, s) at hp
    have he : (p, s) = (p, 0) + (0, s) := by simp
    rw [he, map_add, hp]
    abel

omit [FiniteDimensional ℝ F] in
theorem exists_parameter_coordinates (Φ : P × K → F) (U : Set (P × K)) (hU : IsOpen U)
    (p : P) (k : K) (hp : (p, k) ∈ U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hb : Bijective (fderiv ℝ (fun q : P ↦ Φ (q, k)) p)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, P × K) 𝓘(ℝ, F × K) (P × K) (F × K) ∞,
      (p, k) ∈ e.source ∧ e.source ⊆ U ∧ ∀ q, e q = (Φ q, q.2) := by
  let g : P × K → F × K := fun q ↦ (Φ q, q.2)
  let A : (P × K) →L[ℝ] F := fderiv ℝ Φ (p, k)
  have hdΦ : HasFDerivAt Φ A (p, k) :=
    ((hΦ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hslice : fderiv ℝ (fun q : P ↦ Φ (q, k)) p =
      A.comp (ContinuousLinearMap.inl ℝ P K) :=
    (hdΦ.comp p (hasFDerivAt_prodMk_left p k)).fderiv
  have hbij : Bijective (A.prod (ContinuousLinearMap.snd ℝ P K)) := by
    apply bijective_prod_snd
    rwa [← hslice]
  have hdg : HasFDerivAt g (A.prod (ContinuousLinearMap.snd ℝ P K)) (p, k) :=
    hdΦ.prodMk hasFDerivAt_snd
  have hinv : (fderiv ℝ g (p, k)).IsInvertible := by
    rw [hdg.fderiv]
    exact ⟨(LinearEquiv.ofBijective
      (A.prod (ContinuousLinearMap.snd ℝ P K)).toLinearMap hbij).toContinuousLinearEquiv, rfl⟩
  obtain ⟨e, hep, heU, heq⟩ := exists_partialDiffeomorph_of_contDiffOn hU hp
    (hΦ.prodMk contDiff_snd.contDiffOn) hinv
  exact ⟨e, hep, heU, fun q ↦ congrFun heq q⟩

omit [FiniteDimensional ℝ F] in
theorem exists_coordinates (Φ : P × ℝ → F) (U : Set (P × ℝ)) (hU : IsOpen U)
    (p : P) (hp : (p, 0) ∈ U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hb : Bijective (fderiv ℝ (fun q : P ↦ Φ (q, 0)) p)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, P × ℝ) 𝓘(ℝ, F × ℝ) (P × ℝ) (F × ℝ) ∞,
      (p, 0) ∈ e.source ∧ e.source ⊆ U ∧ ∀ q, e q = (Φ q, q.2) :=
  exists_parameter_coordinates Φ U hU p 0 hp hΦ hb

end NoExoticSixSphere.ImplicitCurve
