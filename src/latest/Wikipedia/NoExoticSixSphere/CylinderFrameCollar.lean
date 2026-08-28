import Wikipedia.NoExoticSixSphere.CylinderFiberNormalFrame

/-!
# The actual cylinder normal frame on a constant collar

On an open time collar the ambient cylinder equations are exactly the
endpoint sphere equations with time ignored. Consequently the constructed
full-fiber normal frame is the endpoint normal frame with zero time component.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace NoExoticSixSphere.CylinderFiberNormalFrame

variable {m n : ℕ} (f : C(ℝ × Sphere m, Sphere n)) (f₀ : C(Sphere m, Sphere n))
  (b : Sphere n) (a : Sphere m) {U : Set ℝ}
  (hconstant : ∀ t ∈ U, ∀ x, f (t, x) = f₀ x)

include hconstant in
theorem equations_eq_on_collar
    (p : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1)))) (hp : p.fst ∈ U) :
    equations f b a p = SphereFiberNormalFrame.equations f₀ b a p.snd := by
  apply CylinderLevelEquations.equations_eq_of_timeIndependent (U := U)
  · intro t ht x
    change _ - _ = _ - _
    rw [hconstant t ht x]
  · exact hp

include hconstant in
theorem equations_eventuallyEq_on_collar (hU : IsOpen U) (t : ℝ) (ht : t ∈ U)
    (x : EuclideanSpace ℝ (Fin (m + 1))) :
    equations f b a =ᶠ[𝓝 (WithLp.toLp 2 (t, x))]
      (fun p : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1))) ↦
        SphereFiberNormalFrame.equations f₀ b a p.snd) := by
  have hn : {p : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1))) | p.fst ∈ U} ∈
      𝓝 (WithLp.toLp 2 (t, x)) :=
    (hU.preimage (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin (m + 1)))).continuous).mem_nhds ht
  filter_upwards [hn] with p hp
  exact equations_eq_on_collar f f₀ b a hconstant p hp

theorem normalFrame_ambient_on_collar
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) ∞ f)
    (hf₀ : ContMDiff (𝓡 m) (𝓡 n) ∞ f₀)
    (hreg : ∀ p, f p = b → Function.Surjective
      (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) f p))
    (hreg₀ : ∀ x, f₀ x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f₀ x))
    (k : ℕ) (hd : m = n + k) (hU : IsOpen U) (t : ℝ) (ht : t ∈ U)
    (x : {x : Sphere m // f₀ x = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (dimension_eq hd);
    letI := regularFiberAtlas f₀ hf₀ b hreg₀ k (by simpa using hd);
    (normalFrame f hf b hreg k hd a).ambient
      ⟨(t, x.val), (hconstant t ht x.val).trans x.property⟩ =
        CylinderNormalFrame.liftFrame
          ((SphereFiberNormalFrame.normalFrame f₀ hf₀ b hreg₀ k hd a).ambient x) := by
  let := regularFiberAtlas f hf b hreg (k + 1) (dimension_eq hd)
  let := regularFiberAtlas f₀ hf₀ b hreg₀ k (by simpa using hd)
  rw [normalFrame_ambient, SphereFiberNormalFrame.normalFrame_ambient]
  exact CylinderNormalFrame.orthogonalRightInverse_fderiv_of_eventuallyEq
    ((SphereFiberNormalFrame.contDiffAt_equations f₀ hf₀ b a x.val x.property).differentiableAt
      (by simp))
    (SphereFiberNormalFrame.surjective_fderiv_equations f₀ hf₀ b a x.val x.property
      (hreg₀ x.val x.property))
    (equations_eventuallyEq_on_collar f f₀ b a hconstant hU t ht x.val.val)

end NoExoticSixSphere.CylinderFiberNormalFrame
