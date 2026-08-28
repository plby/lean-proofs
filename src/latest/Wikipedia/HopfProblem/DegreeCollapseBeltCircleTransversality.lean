import Wikipedia.HopfProblem.DegreeCollapseBeltLevelCircle

/-!
# The closed circle retains the actual transverse belt crossing

The short-arc germ factors through the constructed circle. Its derivative
image therefore lies in the circle's derivative image. Surjectivity with
the actual belt tangent image passes to the circle by the chain rule.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem transverse_circle_of_arc_germ
    {D G H N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    {α : ℝ → N} {γ : Circle → N} {ψ : ℝ → Circle}
    (hγ : ContMDiff (𝓡 1) J ∞ γ) (hψ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ψ)
    (hgerm : γ ∘ ψ =ᶠ[𝓝 (0 : ℝ)] α) (B : D →L[ℝ] G)
    (htrans : Surjective ((mfderiv 𝓘(ℝ, ℝ) J α 0 : ℝ →L[ℝ] G).coprod B)) :
    Surjective ((mfderiv (𝓡 1) J γ (ψ 0) : EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod B) := by
  let A : EuclideanSpace ℝ (Fin 1) →L[ℝ] G := mfderiv (𝓡 1) J γ (ψ 0)
  let P : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) ψ 0
  let A₀ : ℝ →L[ℝ] G := mfderiv 𝓘(ℝ, ℝ) J α 0
  have hc := mfderiv_comp 0 (hγ.mdifferentiableAt (by simp)) (hψ.mdifferentiableAt (by simp))
  have heq : A.comp P = A₀ :=
    hc.symm.trans hgerm.mfderiv_eq
  intro y
  obtain ⟨⟨a, b⟩, hab⟩ := htrans y
  refine ⟨(P a, b), ?_⟩
  have ha := congrArg (fun L : ℝ →L[ℝ] G => L a) heq
  change A (P a) + B b = y
  change A (P a) = A₀ a at ha
  rw [ha]
  exact hab

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_transverse_single_belt_circle
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    (hq : nativeMorseIndex E f q = 1)
    (n : ℕ) [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val))
    {d : ℕ} (hlow : ∀ a : criticalPoints E f, f a ≤ S.toSurgeryWindows.upper q →
      nativeMorseIndex E f a ≤ d) (hcut : 1 + d < Module.finrank ℝ E)
    (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ γ : C(Circle, (S.data q).UpperLevel),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧ Injective γ ∧
      (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) ∧
      ∃ z₀ : Circle,
        (∀ z w, γ z = (S.data q).surgery.beltSphere w ↔ z = z₀ ∧ v = w) ∧
        Surjective ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z₀ :
          EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod
            (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  obtain ⟨r, hr, -, γ, hγ, hγi, hγd, hshort, hsingle⟩ :=
    S.exists_single_belt_intersection_circle hf p q hp hq u v hbranches hlow hcut hdim
  let ψ : ℝ → Circle := fun t => Circle.exp (2 * Real.pi / (2 * r + 1) * (t + r))
  have hψ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ψ :=
    contMDiff_circleExp.comp (contDiff_const.mul (contDiff_id.add contDiff_const)).contMDiff
  have heq : γ ∘ ψ =ᶠ[𝓝 (0 : ℝ)] nativeBeltLevelArc S q u v := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hr) hr] with t ht
    exact hshort t ⟨ht.1.le, ht.2.le⟩
  refine ⟨γ, hγ, hγi, hγd, Circle.exp (2 * Real.pi / (2 * r + 1) * r), hsingle, ?_⟩
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v
  have hαtrans : Surjective ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E)
      (nativeBeltLevelArc S q u v) 0 : ℝ →L[ℝ] RegularLevel.Model E).coprod B) :=
    nativeBeltLevelArc_transverse S hf q hq n u v
  have ht : Surjective ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ (ψ 0) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod B) :=
    transverse_circle_of_arc_germ (D := EuclideanSpace ℝ (Fin n))
      (J := 𝓘(ℝ, RegularLevel.Model E)) (α := nativeBeltLevelArc S q u v)
      (γ := γ) (ψ := ψ) hγ hψ heq B hαtrans
  have hp0 : ψ 0 = Circle.exp (2 * Real.pi / (2 * r + 1) * r) := by
    dsimp [ψ]
    rw [zero_add]
  rw [hp0] at ht
  exact ht

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
