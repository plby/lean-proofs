import Wikipedia.HopfProblem.OrbitPairNativeFamilyTrack
import Wikipedia.HopfProblem.OrbitPairSynchronizedPairs

/-!
# Synchronized collisions and transverse track branches

The synchronized difference differential is surjective exactly when the two
time-retaining track differentials jointly span the ambient tangent space.
The comparison is an explicit linear identity, with the actual native
derivatives throughout. No change of atlas or generic-position hypothesis
is made here.
-/

noncomputable section

open Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SynchronizedPairs

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def firstLinear : ℝ × (E × E) →L[ℝ] ℝ × E :=
  (ContinuousLinearMap.fst ℝ ℝ (E × E)).prod
    ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E)))

def secondLinear : ℝ × (E × E) →L[ℝ] ℝ × E :=
  (ContinuousLinearMap.fst ℝ ℝ (E × E)).prod
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E)))

theorem surjective_track_coprod_iff (A B : ℝ × E →L[ℝ] G) :
    Surjective (((ContinuousLinearMap.fst ℝ ℝ E).prod A).coprod
      ((ContinuousLinearMap.fst ℝ ℝ E).prod B)) ↔
    Surjective (B.comp secondLinear - A.comp firstLinear) := by
  constructor
  · intro h w
    obtain ⟨⟨a, b⟩, hab⟩ := h (0, w)
    have ht : a.1 + b.1 = 0 := congrArg Prod.fst hab
    have hw : A a + B b = w := congrArg Prod.snd hab
    have hp : (b.1, -a.2) = -a := by
      apply Prod.ext
      · change b.1 = -a.1
        linarith
      · rfl
    refine ⟨(b.1, (-a.2, b.2)), ?_⟩
    change B b - A (b.1, -a.2) = w
    rw [hp, map_neg, sub_neg_eq_add, add_comm]
    exact hw
  · intro h p
    obtain ⟨⟨s, u, v⟩, huv⟩ := h (p.2 - A (p.1, 0))
    change B (s, v) - A (s, u) = p.2 - A (p.1, 0) at huv
    refine ⟨((p.1, 0) - (s, u), (s, v)), ?_⟩
    apply Prod.ext
    · change (p.1 - s) + s = p.1
      exact sub_add_cancel _ _
    · change A ((p.1, 0) - (s, u)) + B (s, v) = p.2
      rw [map_sub]
      calc
        A (p.1, 0) - A (s, u) + B (s, v) =
            A (p.1, 0) + (B (s, v) - A (s, u)) := by abel
        _ = A (p.1, 0) + (p.2 - A (p.1, 0)) := by rw [huv]
        _ = p.2 := by abel

variable {H K M N : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

theorem first_hasMFDerivAt (q : ℝ × (M × M)) :
    HasMFDerivAt (𝓘(ℝ, ℝ).prod (I.prod I)) (𝓘(ℝ, ℝ).prod I)
      first q (firstLinear (E := E)) :=
  (hasMFDerivAt_fst q).prodMk
    ((hasMFDerivAt_fst q.2).comp q (hasMFDerivAt_snd q))

theorem second_hasMFDerivAt (q : ℝ × (M × M)) :
    HasMFDerivAt (𝓘(ℝ, ℝ).prod (I.prod I)) (𝓘(ℝ, ℝ).prod I)
      second q (secondLinear (E := E)) :=
  (hasMFDerivAt_fst q).prodMk
    ((hasMFDerivAt_snd q.2).comp q (hasMFDerivAt_snd q))

/-- Native transversality on the synchronized pair domain is precisely
transversality of the two time-retaining track branches. -/
theorem transverseAt_iff_track_coprod {F : ℝ × M → N} (q : ℝ × (M × M))
    (hF₁ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) J F (first q))
    (hF₂ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) J F (second q)) :
    Coincidence.TransverseAt (I := 𝓘(ℝ, ℝ).prod (I.prod I)) (J := J)
      (F ∘ first) (F ∘ second) q ↔
    Surjective ((mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J)
      (NativeFamily.track F) (first q)).coprod
      (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J)
        (NativeFamily.track F) (second q))) := by
  let A : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (first q)
  let B : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (second q)
  let U : ℝ × (E × E) →L[ℝ] G :=
    mfderiv (𝓘(ℝ, ℝ).prod (I.prod I)) J (F ∘ first) q
  let V : ℝ × (E × E) →L[ℝ] G :=
    mfderiv (𝓘(ℝ, ℝ).prod (I.prod I)) J (F ∘ second) q
  let T₁ : ℝ × E →L[ℝ] ℝ × G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (NativeFamily.track F) (first q)
  let T₂ : ℝ × E →L[ℝ] ℝ × G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (NativeFamily.track F) (second q)
  have hU : U = A.comp firstLinear := by
    have hh := mfderiv_comp q hF₁ (first_hasMFDerivAt (I := I) q).mdifferentiableAt
    rw [(first_hasMFDerivAt (I := I) q).mfderiv] at hh
    exact hh
  have hV : V = B.comp secondLinear := by
    have hh := mfderiv_comp q hF₂ (second_hasMFDerivAt (I := I) q).mdifferentiableAt
    rw [(second_hasMFDerivAt (I := I) q).mfderiv] at hh
    exact hh
  have hT₁ : T₁ = (ContinuousLinearMap.fst ℝ ℝ E).prod A := by
    have hh := mfderiv_prodMk mdifferentiableAt_fst hF₁
    rw [mfderiv_fst] at hh
    exact hh
  have hT₂ : T₂ = (ContinuousLinearMap.fst ℝ ℝ E).prod B := by
    have hh := mfderiv_prodMk mdifferentiableAt_fst hF₂
    rw [mfderiv_fst] at hh
    exact hh
  change Surjective (V - U) ↔ Surjective (T₁.coprod T₂)
  rw [hU, hV, hT₁, hT₂]
  exact (surjective_track_coprod_iff A B).symm

/-- A normalized model-space formula for each native track derivative
can establish transversality without unfolding a concrete family inside
dependent tangent-space instances. -/
theorem transverseAt_of_track_derivative_formulas {F : ℝ × M → N}
    (q : ℝ × (M × M))
    (hF₁ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) J F (first q))
    (hF₂ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) J F (second q))
    (A B : ℝ × E →L[ℝ] ℝ × G)
    (hA : (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J)
      (NativeFamily.track F) (first q) : ℝ × E →L[ℝ] ℝ × G) = A)
    (hB : (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J)
      (NativeFamily.track F) (second q) : ℝ × E →L[ℝ] ℝ × G) = B)
    (ht : Surjective (A.coprod B)) :
    Coincidence.TransverseAt (I := 𝓘(ℝ, ℝ).prod (I.prod I)) (J := J)
      (F ∘ first) (F ∘ second) q := by
  apply (transverseAt_iff_track_coprod q hF₁ hF₂).mpr
  let U : ℝ × E →L[ℝ] ℝ × G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (NativeFamily.track F) (first q)
  let V : ℝ × E →L[ℝ] ℝ × G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (NativeFamily.track F) (second q)
  have hU : U = A := hA
  have hV : V = B := hB
  change Surjective (U.coprod V)
  rw [hU, hV]
  exact ht

end Wikipedia.HopfProblem.OrbitPair.SynchronizedPairs
