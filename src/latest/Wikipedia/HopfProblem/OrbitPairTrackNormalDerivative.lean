import Wikipedia.HopfProblem.OrbitPairNativeFamilyTrack
import Wikipedia.HopfProblem.OrbitPairLinearNormalComplement

/-!
# Normal columns transverse to time-retaining tracks

The spatial derivative is the restriction of the actual family derivative
to the zero-parameter directions. Complementary columns for that spatial
derivative lift to normal columns with exactly zero parameter component.
-/

noncomputable section

open Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {P E G Z : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem surjective_track_normal_coprod (D : P × E →L[ℝ] G) (B : Z →L[ℝ] G)
    (h : Surjective ((D.comp (ContinuousLinearMap.inr ℝ P E)).coprod B)) :
    Surjective (((ContinuousLinearMap.fst ℝ P E).prod D).coprod
      ((0 : Z →L[ℝ] P).prod B)) := by
  intro w
  obtain ⟨⟨u, z⟩, huz⟩ := h (w.2 - D (w.1, 0))
  change D (0, u) + B z = w.2 - D (w.1, 0) at huz
  refine ⟨((w.1, u), z), ?_⟩
  apply Prod.ext
  · change w.1 + 0 = w.1
    exact add_zero _
  · change D (w.1, u) + B z = w.2
    have hd : D (w.1, u) = D (w.1, 0) + D (0, u) := by
      have he : (w.1, u) = (w.1, 0) + (0, u) := by simp
      rw [he, map_add]
    rw [hd]
    calc
      D (w.1, 0) + D (0, u) + B z = D (w.1, 0) + (D (0, u) + B z) := by abel
      _ = D (w.1, 0) + (w.2 - D (w.1, 0)) := by rw [huz]
      _ = w.2 := by abel

variable {H K M N : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

theorem mfderiv_spatial_eq {F : P × M → N} (q : P × M)
    (hF : MDifferentiableAt (𝓘(ℝ, P).prod I) J F q) :
    (mfderiv I J (fun x => F (q.1, x)) q.2 : E →L[ℝ] G) =
      (mfderiv (𝓘(ℝ, P).prod I) J F q : P × E →L[ℝ] G).comp
        (ContinuousLinearMap.inr ℝ P E) := by
  let D : P × E →L[ℝ] G := mfderiv (𝓘(ℝ, P).prod I) J F q
  let S : E →L[ℝ] G := mfderiv I J (fun x => F (q.1, x)) q.2
  let B : E →L[ℝ] P × E :=
    mfderiv I (𝓘(ℝ, P).prod I) (fun x : M => (q.1, x)) q.2
  have hi : HasMFDerivAt I (𝓘(ℝ, P).prod I) (fun x : M => (q.1, x)) q.2
      (ContinuousLinearMap.inr ℝ P E) :=
    (hasMFDerivAt_const q.1 q.2).prodMk (hasMFDerivAt_id q.2)
  have hB : B = ContinuousLinearMap.inr ℝ P E := hi.mfderiv
  have hS : S = D.comp B := mfderiv_comp q.2 hF hi.mdifferentiableAt
  change S = D.comp (ContinuousLinearMap.inr ℝ P E)
  rwa [hB] at hS

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]

theorem exists_track_normal_columns {F : P × M → N} (q : P × M)
    (hF : MDifferentiableAt (𝓘(ℝ, P).prod I) J F q)
    (hi : Injective (mfderiv I J (fun x => F (q.1, x)) q.2))
    (n : ℕ) (hdim : Module.finrank ℝ E + n = Module.finrank ℝ G) :
    ∃ B : EuclideanSpace ℝ (Fin n) →L[ℝ] G,
      Surjective (((ContinuousLinearMap.fst ℝ P E).prod
        (mfderiv (𝓘(ℝ, P).prod I) J F q : P × E →L[ℝ] G)).coprod
          ((0 : EuclideanSpace ℝ (Fin n) →L[ℝ] P).prod B)) := by
  let D : P × E →L[ℝ] G := mfderiv (𝓘(ℝ, P).prod I) J F q
  let S : E →L[ℝ] G := mfderiv I J (fun x => F (q.1, x)) q.2
  obtain ⟨B, hB⟩ := LinearNormal.exists_complement S hi n hdim
  have hS : S = D.comp (ContinuousLinearMap.inr ℝ P E) := mfderiv_spatial_eq q hF
  refine ⟨B, surjective_track_normal_coprod D B ?_⟩
  rw [← hS]
  exact hB.surjective

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
