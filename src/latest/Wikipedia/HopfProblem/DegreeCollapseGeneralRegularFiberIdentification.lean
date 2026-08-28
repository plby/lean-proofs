import Wikipedia.NoExoticSixSphere.RegularFiberIdentification

/-!
# Regular-fiber identification with an arbitrary given source model

Retain the source's existing model and atlas, including a product sphere
atlas. Only equality of the real model dimensions is required.
-/

open scoped Manifold ContDiff
open Module

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralRegularFiberIdentification

open NoExoticSixSphere

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  (f : ContinuousMap M N) (hf : ContMDiff I J ∞ f) (b : N)
  (hreg : ∀ x, f x = b → Function.Surjective (mfderiv I J f x))
  (k : ℕ) (hd : finrank ℝ B = finrank ℝ C + k)
  {D H'' P : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace H''] {L : ModelWithCorners ℝ D H''} [L.Boundaryless]
  [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold L ∞ P]
  (hP : finrank ℝ D = finrank ℝ (EuclideanSpace ℝ (Fin k)))

noncomputable def diffeomorphToFiber (e : P → M)
    (he : ContMDiff L I ∞ e) (hei : Function.Injective e)
    (heimm : ∀ x, Function.Injective (mfderiv L I e x))
    (hfiber : ∀ y, f y = b ↔ ∃ x, e x = y) :
    letI := regularFiberAtlas f hf b hreg k hd;
    P ≃ₘ⟮L, 𝓡 k⟯ {x : M // f x = b} := by
  let := regularFiberAtlas f hf b hreg k hd
  let := regularFiber_isManifold f hf b hreg k hd
  let q : P → {x : M // f x = b} := fun x ↦ ⟨e x, (hfiber (e x)).mpr ⟨x, rfl⟩⟩
  have hq : ContMDiff L (𝓡 k) ∞ q :=
    (regularFiber_contMDiff_iff_ambient f hf b hreg k hd q).mpr he
  have hbij : Function.Bijective q := by
    constructor
    · intro x y hxy
      exact hei (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx⟩ := (hfiber y.val).mp y.property
      exact ⟨x, Subtype.ext hx⟩
  apply diffeomorphOfBijectiveImmersion q hq hbij hP
  intro x v w hvw
  have hc : mfderiv L I e x =
      (mfderiv (𝓡 k) I (Subtype.val : {x : M // f x = b} → M) (q x)).comp
        (mfderiv L (𝓡 k) q x) :=
    mfderiv_comp x
      ((regularFiber_contMDiff_subtype_val f hf b hreg k hd).mdifferentiable (by simp) (q x))
      (hq.mdifferentiable (by simp) x)
  apply heimm x
  rw [hc]
  exact congrArg (mfderiv (𝓡 k) I (Subtype.val : {x : M // f x = b} → M) (q x)) hvw

theorem diffeomorphToFiber_val (e : P → M)
    (he : ContMDiff L I ∞ e) (hei : Function.Injective e)
    (heimm : ∀ x, Function.Injective (mfderiv L I e x))
    (hfiber : ∀ y, f y = b ↔ ∃ x, e x = y) (x : P) :
    letI := regularFiberAtlas f hf b hreg k hd;
    (diffeomorphToFiber f hf b hreg k hd hP e he hei heimm hfiber x).val = e x := rfl

end Wikipedia.HopfProblem.DegreeCollapse.GeneralRegularFiberIdentification

