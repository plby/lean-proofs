import Wikipedia.HopfProblem.OrbitPairTrackCrossingDifferential
import Wikipedia.HopfProblem.OrbitPairFamilyDoublePoints

/-!
# Spatial immersion and regular crossings under native track diffeomorphisms

If one family track is an ambient diffeomorphic image of another, with a
native source diffeomorphism accounting for its parametrization, spatial
immersion and synchronized crossing regularity are retained. This is useful
for target-dependent time shears: the track identity supplies these facts
without a projected-separation hypothesis on spatial cutoffs.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open Wikipedia.SmoothSixDPoincare SynchronizedPairs

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

theorem injective_spatial_of_track_immersion {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F) (q : ℝ × M)
    (hi : Injective (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F) q)) :
    Injective (mfderiv I J (fun y => F (q.1, y)) q.2) := by
  let A : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F q
  let T : ℝ × E →L[ℝ] ℝ × G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F) q
  let S : E →L[ℝ] G := mfderiv I J (fun y => F (q.1, y)) q.2
  have hT : T = (ContinuousLinearMap.fst ℝ ℝ E).prod A := by
    have hh := mfderiv_prodMk (x := q) mdifferentiableAt_fst (hF.mdifferentiableAt (by simp))
    rw [mfderiv_fst] at hh
    exact hh
  have hin : HasMFDerivAt I (𝓘(ℝ, ℝ).prod I) (fun y : M => (q.1, y)) q.2
      (ContinuousLinearMap.inr ℝ ℝ E) :=
    (hasMFDerivAt_const q.1 q.2).prodMk (hasMFDerivAt_id q.2)
  have hS : S = A.comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hh := mfderiv_comp q.2 (hF.mdifferentiableAt (by simp)) hin.mdifferentiableAt
    rw [hin.mfderiv] at hh
    exact hh
  change Injective S
  apply (injective_iff_map_eq_zero S).mpr
  intro v hv
  have hzero : T (0, v) = 0 := by
    rw [hT]
    apply Prod.ext
    · rfl
    · change A (0, v) = 0
      rw [hS] at hv
      exact hv
  have hvec : ((0 : ℝ), v) = 0 := (injective_iff_map_eq_zero T).mp hi (0, v) hzero
  exact congrArg Prod.snd hvec

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]

theorem track_derivative_under_diffeomorphs {F F' : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (Φ : Diffeomorph (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J) (ℝ × N) (ℝ × N) ∞)
    (Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞)
    (htrack : track F' = (Φ ∘ track F) ∘ Ψ) (q : ℝ × M) :
    let A : ℝ × E →L[ℝ] ℝ × G :=
      mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F) (Ψ q)
    let B : ℝ × E →L[ℝ] ℝ × E :=
      mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) Ψ q
    let C : ℝ × G →L[ℝ] ℝ × G :=
      mfderiv (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J) Φ (track F (Ψ q))
    (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F') q :
      ℝ × E →L[ℝ] ℝ × G) = C.comp (A.comp B) := by
  dsimp only
  rw [htrack]
  have hT : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) ∞ (track F) :=
    contMDiff_fst.prodMk hF
  have hA := mfderiv_comp (Ψ q) (Φ.contMDiff.mdifferentiableAt (by simp))
    (hT.mdifferentiableAt (by simp))
  have hB := mfderiv_comp q
    ((Φ.contMDiff.comp hT).mdifferentiableAt (by simp))
    (Ψ.contMDiff.mdifferentiableAt (by simp))
  rw [hA] at hB
  exact hB.trans (ContinuousLinearMap.comp_assoc _ _ _)

theorem spatial_immersion_of_track_diffeomorphs {F F' : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hF' : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F')
    (hi : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (Φ : Diffeomorph (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J) (ℝ × N) (ℝ × N) ∞)
    (Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞)
    (htrack : track F' = (Φ ∘ track F) ∘ Ψ) :
    ∀ t x, Injective (mfderiv I J (fun y => F' (t, y)) x) := by
  intro t x
  apply injective_spatial_of_track_immersion hF' (t, x)
  rw [track_derivative_under_diffeomorphs hF Φ Ψ htrack]
  exact (PartialChart.bijective_mfderiv Φ.toPartialDiffeomorph (mem_univ _)).injective.comp
    ((injective_mfderiv_track (Ψ (t, x)) (hF.mdifferentiableAt (by simp))
      (hi _ _)).comp
      (PartialChart.bijective_mfderiv Ψ.toPartialDiffeomorph (mem_univ _)).injective)

theorem regular_of_track_diffeomorphs {F F' : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hF' : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F')
    (hr : RegularOn (I := I) (J := J) F {p | p.2.1 ≠ p.2.2})
    (Φ : Diffeomorph (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J) (ℝ × N) (ℝ × N) ∞)
    (Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞)
    (htrack : track F' = (Φ ∘ track F) ∘ Ψ) :
    RegularOn (I := I) (J := J) F' {p | p.2.1 ≠ p.2.2} := by
  intro p hp hvalue
  have htrackValue : track F' (first p) = track F' (second p) := Prod.ext rfl hvalue
  have heval (q : ℝ × M) : track F' q = Φ (track F (Ψ q)) := congrFun htrack q
  have hold : track F (Ψ (first p)) = track F (Ψ (second p)) :=
    Φ.injective ((heval (first p)).symm.trans (htrackValue.trans (heval (second p))))
  let u := Ψ (first p)
  let v := Ψ (second p)
  have ht : u.1 = v.1 := congrArg (fun z : ℝ × N => z.1) hold
  have hv : F u = F v := congrArg (fun z : ℝ × N => z.2) hold
  let q : ℝ × (M × M) := (u.1, (u.2, v.2))
  have hqu : first q = u := rfl
  have hqv : second q = v := Prod.ext ht rfl
  have hne : u.2 ≠ v.2 := by
    intro h
    have huv : u = v := Prod.ext ht h
    exact hp (congrArg Prod.snd (Ψ.injective huv))
  have hq : q ∈ FamilyDoublePoints.doublePoints F :=
    ⟨hne, hv.trans (congrArg F hqv).symm⟩
  let A : ℝ × E →L[ℝ] ℝ × G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F) u
  let B : ℝ × E →L[ℝ] ℝ × G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F) v
  have hAB : Surjective (A.coprod B) := by
    have hh := (transverseAt_iff_track_coprod q (hF.mdifferentiableAt (by simp))
      (hF.mdifferentiableAt (by simp))).mp (hr q hq.1 hq.2)
    rw [hqu, hqv] at hh
    exact hh
  let S₁ : ℝ × E →L[ℝ] ℝ × E :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) Ψ (first p)
  let S₂ : ℝ × E →L[ℝ] ℝ × E :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) Ψ (second p)
  let C₁ : ℝ × G →L[ℝ] ℝ × G :=
    mfderiv (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J) Φ (track F u)
  let C₂ : ℝ × G →L[ℝ] ℝ × G :=
    mfderiv (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J) Φ (track F v)
  have hC : C₂ = C₁ := by
    dsimp only [C₁, C₂]
    change track F u = track F v at hold
    rw [hold]
  let T₁ : ℝ × E →L[ℝ] ℝ × G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F') (first p)
  let T₂ : ℝ × E →L[ℝ] ℝ × G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F') (second p)
  have hT₁ : T₁ = C₁.comp (A.comp S₁) := track_derivative_under_diffeomorphs hF Φ Ψ htrack _
  have hT₂ : T₂ = C₁.comp (B.comp S₂) := by
    have hh : T₂ = C₂.comp (B.comp S₂) := track_derivative_under_diffeomorphs hF Φ Ψ htrack _
    rwa [hC] at hh
  have hS₁ : Surjective S₁ :=
    (PartialChart.bijective_mfderiv Ψ.toPartialDiffeomorph (mem_univ _)).surjective
  have hS₂ : Surjective S₂ :=
    (PartialChart.bijective_mfderiv Ψ.toPartialDiffeomorph (mem_univ _)).surjective
  have hC₁ : Surjective C₁ :=
    (PartialChart.bijective_mfderiv Φ.toPartialDiffeomorph (mem_univ _)).surjective
  apply (transverseAt_iff_track_coprod p (hF'.mdifferentiableAt (by simp))
    (hF'.mdifferentiableAt (by simp))).mpr
  change Surjective (T₁.coprod T₂)
  intro w
  obtain ⟨z, hz⟩ := hC₁ w
  obtain ⟨⟨a, b⟩, hab⟩ := hAB z
  obtain ⟨a', ha'⟩ := hS₁ a
  obtain ⟨b', hb'⟩ := hS₂ b
  refine ⟨(a', b'), ?_⟩
  change T₁ a' + T₂ b' = w
  rw [hT₁, hT₂, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ha', hb', ← map_add]
  exact (congrArg C₁ hab).trans hz

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
