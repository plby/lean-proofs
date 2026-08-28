import Wikipedia.HopfProblem.OrbitPairCoincidenceDifferential
import Wikipedia.HopfProblem.OrbitPairTrackNormalDerivative

/-!
# Coincidence transversality under a common ambient parameter family

Two coincident maps are postcomposed with the same ambient map at the same
parameter. The parameter derivatives cancel in their difference. Only the
spatial derivative of the ambient family acts on the old difference.
Consequently a family of ambient diffeomorphisms preserves transversality,
without any assumption about joint smoothness of its inverses.
-/

noncomputable section

open Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.Coincidence

variable {P E G H K X N : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace N] [ChartedSpace K N]

def ambientSpatialDifferential (A : P × N → N) (p : P) (y : N) : G →L[ℝ] G :=
  mfderiv J J (fun z => A (p, z)) y

theorem differential_ambient_family {A : P × N → N} {τ : X → P}
    {u v : X → N} {x : X}
    (hA : MDifferentiableAt (𝓘(ℝ, P).prod J) J A (τ x, u x))
    (hτ : MDifferentiableAt I 𝓘(ℝ, P) τ x)
    (hu : MDifferentiableAt I J u x) (hv : MDifferentiableAt I J v x)
    (hxy : v x = u x) :
    differential (I := I) (J := J)
        (fun z => A (τ z, u z)) (fun z => A (τ z, v z)) x =
      (ambientSpatialDifferential (J := J) A (τ x) (u x)).comp
        (differential (I := I) (J := J) u v x) := by
  let U : E →L[ℝ] G := mfderiv I J u x
  let V : E →L[ℝ] G := mfderiv I J v x
  let T : E →L[ℝ] P := mfderiv I 𝓘(ℝ, P) τ x
  let C : P × G →L[ℝ] G := mfderiv (𝓘(ℝ, P).prod J) J A (τ x, u x)
  let B : G →L[ℝ] G := mfderiv J J (fun y => A (τ x, y)) (u x)
  let U' : E →L[ℝ] G := mfderiv I J (fun z => A (τ z, u z)) x
  let V' : E →L[ℝ] G := mfderiv I J (fun z => A (τ z, v z)) x
  have hU : U' = C.comp (T.prod U) := by
    have hd := mfderiv_comp x hA (hτ.prodMk hu)
    rw [mfderiv_prodMk (x := x) hτ hu] at hd
    exact hd
  have hAv : MDifferentiableAt (𝓘(ℝ, P).prod J) J A (τ x, v x) := hxy ▸ hA
  have hV : V' = C.comp (T.prod V) := by
    have hd := mfderiv_comp x hAv (hτ.prodMk hv)
    rw [mfderiv_prodMk (x := x) hτ hv, hxy] at hd
    exact hd
  have hB : B = C.comp (ContinuousLinearMap.inr ℝ P G) :=
    NativeFamily.mfderiv_spatial_eq (τ x, u x) hA
  change V' - U' = B.comp (V - U)
  rw [hU, hV, hB]
  ext w
  change C (T w, V w) - C (T w, U w) = C (0, V w - U w)
  rw [← C.map_sub]
  congr 1
  exact Prod.ext (sub_self _) rfl

theorem transverseAt_ambient_family_iff {A : P × N → N} {τ : X → P}
    {u v : X → N} {x : X}
    (hA : MDifferentiableAt (𝓘(ℝ, P).prod J) J A (τ x, u x))
    (hτ : MDifferentiableAt I 𝓘(ℝ, P) τ x)
    (hu : MDifferentiableAt I J u x) (hv : MDifferentiableAt I J v x)
    (hxy : v x = u x)
    (hB : Bijective (mfderiv J J (fun y => A (τ x, y)) (u x))) :
    TransverseAt (I := I) (J := J)
        (fun z => A (τ z, u z)) (fun z => A (τ z, v z)) x ↔
      TransverseAt (I := I) (J := J) u v x := by
  let B : G →L[ℝ] G := mfderiv J J (fun y => A (τ x, y)) (u x)
  let D : E →L[ℝ] G := differential (I := I) (J := J) u v x
  unfold TransverseAt
  rw [differential_ambient_family hA hτ hu hv hxy]
  change Surjective (B.comp D) ↔ Surjective D
  constructor
  · intro hs w
    obtain ⟨z, hz⟩ := hs (B w)
    exact ⟨z, hB.injective hz⟩
  · exact hB.surjective.comp

end Wikipedia.HopfProblem.OrbitPair.Coincidence
