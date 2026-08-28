import Wikipedia.NoExoticSixSphere.SphereSuspensionSmoothEquationDerivative

/-!
# The actual normal operator of the smooth suspension

The added height direction is orthogonal to the old ambient space. The
full block derivative therefore has the old orthogonal right inverse
in the tail and the identity in the new height direction. The final
formula concerns the actual smooth representative and its actual radial
defining equations in the genuine cylinder target chart.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

theorem orthogonalRightInverse_eq_of_orthogonal_preimage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : E →L[ℝ] F) (hD : Function.Surjective D) (w : F) (z : E)
    (hz : D z = w) (horth : z ∈ D.kerᗮ) : orthogonalRightInverse D w = z := by
  apply sub_eq_zero.mp
  have hker : orthogonalRightInverse D w - z ∈ D.ker := by
    change D (orthogonalRightInverse D w - z) = 0
    rw [map_sub, apply_orthogonalRightInverse D hD, hz, sub_self]
  have hR : orthogonalRightInverse D w ∈ D.kerᗮ := by
    rw [← range_orthogonalRightInverse D hD]
    exact ⟨w, rfl⟩
  have hzero : orthogonalRightInverse D w - z ∈ (⊥ : Submodule ℝ E) := by
    rw [← D.ker.inf_orthogonal_eq_bot]
    exact ⟨hker, Submodule.sub_mem _ hR horth⟩
  exact hzero

namespace SphereCylinder

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

theorem join_inner (m : ℕ) (p q : ℝ × Vector (m + 1)) :
    inner ℝ (join m p) (join m q) = p.1 * q.1 + inner ℝ p.2 q.2 :=
  EuclideanProduct.coordinates_inner (m + 1) p q

end SphereCylinder

namespace SphereMapSuspension

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

theorem normalOperator_of_equation_block {m n : ℕ}
    (D : Vector (m + 1) →L[ℝ] WithLp 2 (ℝ × Vector n))
    (D' : Vector (m + 2) →L[ℝ] WithLp 2 (ℝ × Vector (n + 1)))
    (hD : Function.Surjective D) (hD' : Function.Surjective D')
    (hblock : ∀ s v, D' (SphereCylinder.join m (s, v)) =
      WithLp.toLp 2 ((D v).fst, EuclideanProduct.coordinates n (s, (D v).snd)))
    (s r : ℝ) (z : Vector n) :
    orthogonalRightInverse D' (WithLp.toLp 2 (r, EuclideanProduct.coordinates n (s, z))) =
      SphereCylinder.join m (s, orthogonalRightInverse D (WithLp.toLp 2 (r, z))) := by
  apply orthogonalRightInverse_eq_of_orthogonal_preimage D' hD'
  · rw [hblock, apply_orthogonalRightInverse D hD]
    rfl
  · rw [Submodule.mem_orthogonal']
    intro y hy
    obtain ⟨⟨t, u⟩, rfl⟩ := (SphereCylinder.join m).surjective y
    have hzero : WithLp.toLp 2 ((D u).fst,
        EuclideanProduct.coordinates n (t, (D u).snd)) = 0 := by
      rw [← hblock]
      exact hy
    have hfirst := congrArg (fun w : WithLp 2 (ℝ × Vector (n + 1)) ↦ w.fst) hzero
    have hsecond := congrArg (fun w : WithLp 2 (ℝ × Vector (n + 1)) ↦ w.snd) hzero
    change (D u).fst = 0 at hfirst
    change EuclideanProduct.coordinates n (t, (D u).snd) = 0 at hsecond
    have hpair : (t, (D u).snd) = (0, 0) := by
      apply (EuclideanProduct.coordinates n).injective
      change EuclideanProduct.coordinates n (t, (D u).snd) =
        EuclideanProduct.coordinates n (0 : ℝ × Vector n)
      rw [map_zero]
      exact hsecond
    have ht : t = 0 := congrArg Prod.fst hpair
    have htail : (D u).snd = 0 := congrArg (fun p : ℝ × Vector n ↦ p.2) hpair
    have hu : D u = 0 := by
      apply WithLp.ofLp_injective
      change ((D u).fst, (D u).snd) = (0, 0)
      exact Prod.ext hfirst htail
    have hR : orthogonalRightInverse D (WithLp.toLp 2 (r, z)) ∈ D.kerᗮ := by
      rw [← range_orthogonalRightInverse D hD]
      exact ⟨_, rfl⟩
    rw [Submodule.mem_orthogonal'] at hR
    rw [SphereCylinder.join_inner, ht, mul_zero, zero_add]
    exact hR u hu

variable {m n : ℕ} (f : C(Sphere m, Sphere n)) (b : Sphere n)
  (c : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞)
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (hb : b ∈ c.source)
  (g : C(Sphere (m + 1), Sphere (n + 1)))
  (hg : ContMDiff (𝓡 (m + 1)) (𝓡 (n + 1)) ∞ g)

include hf hb hg in
theorem normalOperator_smoothSuspension (a : Sphere (m + 1)) (a₀ x : Sphere m)
    (hx : f x = b) (hreg : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
    (hgerm : (g : Sphere (m + 1) → Sphere (n + 1)) =ᶠ[𝓝 (equator m x)] map f)
    (s r : ℝ) (z : Vector n) :
    orthogonalRightInverse (fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart g
      (equator n b) (targetCylinderChart c) a) (equator m x).val)
      (WithLp.toLp 2 (r, EuclideanProduct.coordinates n (s, z))) =
    SphereCylinder.join m (s, orthogonalRightInverse (fderiv ℝ
      (SphereFiberNormalFrame.equationsWithTargetChart f b c a₀) x.val)
        (WithLp.toLp 2 (r, z))) := by
  have hpoint : g (equator m x) = equator n b := by
    rw [hgerm.self_of_nhds, map_equator, hx]
  have hgreg : Function.Surjective
      (mfderiv (𝓡 (m + 1)) (𝓡 (n + 1)) g (equator m x)) := by
    rw [hgerm.mfderiv_eq]
    exact surjective_mfderiv_map_equator f hf x hreg
  exact normalOperator_of_equation_block _ _
    (SphereFiberNormalFrame.surjective_fderiv_equationsWithTargetChart
      f hf b c hb a₀ x hx hreg)
    (SphereFiberNormalFrame.surjective_fderiv_equationsWithTargetChart
      g hg (equator n b) (targetCylinderChart c) (equator_mem_targetCylinderChart c b hb)
        a (equator m x) hpoint hgreg)
    (fderiv_smoothSuspensionEquations f b c hf hb g hg a a₀ x hx hgerm) s r z

end SphereMapSuspension
end NoExoticSixSphere
