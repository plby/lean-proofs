import Wikipedia.NoExoticSixSphere.RegularFiberManifold
import Wikipedia.NoExoticSixSphere.SphereValueAlignment

/-!
# A target diffeomorphism retains the actual native regular fiber

Postcomposition changes the target value but leaves every fiber point
unchanged. The native regular-fiber atlases on the two sides are genuinely
diffeomorphic. A target diffeomorphism homotopic to the identity therefore
aligns any specified regular value without changing the map's homotopy class.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularSphereFiber.TargetChange

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (D : Sphere n ≃ₘ⟮𝓡 n, 𝓡 n⟯ Sphere n)

def map : C(Sphere m, Sphere n) := (D.toHomeomorph : C(Sphere n, Sphere n)).comp f

include hf in
theorem smooth : ContMDiff (𝓡 m) (𝓡 n) ∞ (map f D) := D.contMDiff.comp hf

include hf hreg in
theorem regular : ∀ x, map f D x = D b →
    Surjective (mfderiv (𝓡 m) (𝓡 n) (map f D) x) := by
  intro x hx
  change Surjective (mfderiv (𝓡 m) (𝓡 n) (D ∘ f) x)
  rw [mfderiv_comp x (D.contMDiff.mdifferentiable (by simp) (f x))
    (hf.mdifferentiable (by simp) x)]
  exact (D.mfderivToContinuousLinearEquiv (by simp) (f x)).surjective.comp
    (hreg x (D.injective hx))

def fiberDiffeomorph (k : ℕ) (hd : m = n + k) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    letI := regularFiberAtlas (map f D) (smooth f hf D) (D b) (regular f hf b hreg D)
      k (by simpa using hd);
    {x : Sphere m // f x = b} ≃ₘ⟮𝓡 k, 𝓡 k⟯ {x : Sphere m // map f D x = D b} := by
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  let := regularFiberAtlas (map f D) (smooth f hf D) (D b) (regular f hf b hreg D)
    k (by simpa using hd)
  let e : {x : Sphere m // f x = b} ≃ {x : Sphere m // map f D x = D b} :=
    { toFun := fun x ↦ ⟨x.val, congrArg D x.property⟩
      invFun := fun x ↦ ⟨x.val, D.injective x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (regularFiber_contMDiff_iff_ambient (map f D) (smooth f hf D) (D b)
      (regular f hf b hreg D) k (by simpa using hd) e).mpr
    exact regularFiber_contMDiff_subtype_val f hf b hreg k (by simpa using hd)
  · apply (regularFiber_contMDiff_iff_ambient f hf b hreg k (by simpa using hd) e.symm).mpr
    exact regularFiber_contMDiff_subtype_val (map f D) (smooth f hf D) (D b)
      (regular f hf b hreg D) k (by simpa using hd)

theorem fiberDiffeomorph_val (k : ℕ) (hd : m = n + k) (x : {x : Sphere m // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    letI := regularFiberAtlas (map f D) (smooth f hf D) (D b) (regular f hf b hreg D)
      k (by simpa using hd);
    (fiberDiffeomorph f hf b hreg D k hd x).val = x.val := rfl

end NoExoticSixSphere.RegularSphereFiber.TargetChange

namespace NoExoticSixSphere.RegularSphereFiber

theorem exists_regular_value_alignment {m n : ℕ}
    (f : C(Sphere m, Sphere n)) (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b c : Sphere n)
    (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
    (hn : 0 < n) (k : ℕ) (hd : m = n + k) :
    ∃ g : C(Sphere m, Sphere n), ∃ hg : ContMDiff (𝓡 m) (𝓡 n) ∞ g,
      ∃ hregg : ∀ x, g x = c → Surjective (mfderiv (𝓡 m) (𝓡 n) g x),
        f.Homotopic g ∧
        letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
        letI := regularFiberAtlas g hg c hregg k (by simpa using hd);
        ∃ E : {x : Sphere m // f x = b} ≃ₘ⟮𝓡 k, 𝓡 k⟯ {x : Sphere m // g x = c},
          ∀ x, (E x).val = x.val := by
  obtain ⟨D, hD, HD⟩ := exists_id_homotopic_sphereDiffeomorph hn b c
  subst c
  refine ⟨TargetChange.map f D, TargetChange.smooth f hf D,
    TargetChange.regular f hf b hreg D, HD.comp (ContinuousMap.Homotopic.refl f), ?_⟩
  exact ⟨TargetChange.fiberDiffeomorph f hf b hreg D k hd,
    TargetChange.fiberDiffeomorph_val f hf b hreg D k hd⟩

end NoExoticSixSphere.RegularSphereFiber
