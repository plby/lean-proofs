import Wikipedia.HopfProblem.OrbitPairAmbientTrackVelocity

/-!
# Enforcing unit clock speed on the whole ambient cylinder

Keep the spatial component of the constructed ambient track field and
replace its real component by one. The canonical tangent-bundle product
equivalence proves native smoothness. On the track the old clock component
was already one, so the prescribed full velocity is unchanged.
-/

noncomputable section

open Set Function Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {G K N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

def normalizeClockField (v : (p : ℝ × N) → TangentSpace (𝓘(ℝ, ℝ).prod J) p)
    (p : ℝ × N) : TangentSpace (𝓘(ℝ, ℝ).prod J) p := (1, (v p).2)

theorem smooth_normalizeClockField
    {v : (p : ℝ × N) → TangentSpace (𝓘(ℝ, ℝ).prod J) p}
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J).tangent ∞
      (fun p => (⟨p, v p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod J) (ℝ × N)))) :
    ContMDiff (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J).tangent ∞
      (fun p => (⟨p, normalizeClockField v p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod J) (ℝ × N))) := by
  have hR : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).tangent) ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hsplit : ContMDiff (𝓘(ℝ, ℝ).prod J).tangent
      ((𝓘(ℝ, ℝ).tangent).prod J.tangent) ∞ (equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ J N) :=
    contMDiff_equivTangentBundleProd
  have hN : ContMDiff (𝓘(ℝ, ℝ).prod J) J.tangent ∞
      (fun p : ℝ × N => (⟨p.2, (v p).2⟩ : TangentBundle J N)) :=
    contMDiff_snd.comp (hsplit.comp hv)
  have hjoin : ContMDiff ((𝓘(ℝ, ℝ).tangent).prod J.tangent)
      (𝓘(ℝ, ℝ).prod J).tangent ∞ (equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ J N).symm :=
    contMDiff_equivTangentBundleProd_symm
  exact hjoin.comp ((hR.comp contMDiff_fst).prodMk hN)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ G] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [T2Space N] [SigmaCompactSpace N]

theorem exists_unit_clock_track_velocity {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t, Injective (fun x => F (t, x)))
    (himm : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x)) :
    ∃ v : (p : ℝ × N) → TangentSpace (𝓘(ℝ, ℝ).prod J) p,
      ContMDiff (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J).tangent ∞
        (fun p => (⟨p, v p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod J) (ℝ × N))) ∧
      (∀ p : ℝ × N, (v p).1 = 1) ∧
      ∀ q : ℝ × M, v (track F q) = (1, timeVelocity (I := I) (J := J) F q) := by
  obtain ⟨v, hv, hmatch⟩ := exists_ambient_track_velocity hF hi himm
  refine ⟨normalizeClockField v, smooth_normalizeClockField hv, fun _ => rfl, ?_⟩
  intro q
  change (1, (v (track F q)).2) = _
  rw [hmatch]
  rfl

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
