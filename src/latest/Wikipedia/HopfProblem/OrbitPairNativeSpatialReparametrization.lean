import Wikipedia.HopfProblem.OrbitPairSpatialReparametrization
import Wikipedia.HopfProblem.OrbitPairSpatialSourceDiffeomorph
import Wikipedia.HopfProblem.OrbitPairCoincidencePrecomposition

/-!
# Native regular-family properties under spatial reparametrization

The actual time-preserving source map and its synchronized pair map are
constructed as native diffeomorphisms. The chain rule then retains spatial
immersion, synchronized transversality, and full projected rank at all
transported collision sources. No projected separation assumption is needed
because time itself is unchanged.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization

open Wikipedia.SmoothSixDPoincare

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N]
  (D : ℝ → Diffeomorph I I M M ∞)
  (hD : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => D p.1 p.2))

include hD

theorem changedFamily_smooth {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ (changedFamily F (fun t => (D t).toEquiv)) :=
  hF.comp (contMDiff_fst.prodMk hD)

theorem changedFamily_spatial {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x)) :
    ∀ t x, Injective (mfderiv I J
      (fun y => changedFamily F (fun s => (D s).toEquiv) (t, y)) x) := by
  intro t x
  have hs : ContMDiff I J ∞ (fun y => F (t, y)) :=
    hF.comp (contMDiff_const.prodMk contMDiff_id)
  let A : E →L[ℝ] G := mfderiv I J (fun y => F (t, y)) (D t x)
  let B : E →L[ℝ] E := mfderiv I I (D t) x
  let C : E →L[ℝ] G := mfderiv I J
    (fun y => changedFamily F (fun s => (D s).toEquiv) (t, y)) x
  have he : C = A.comp B := mfderiv_comp x (hs.mdifferentiableAt (by simp))
    ((D t).contMDiff.mdifferentiableAt (by simp))
  change Injective C
  rw [he]
  exact (hi t (D t x)).comp
    (PartialChart.bijective_mfderiv (D t).toPartialDiffeomorph (mem_univ x)).injective

theorem exists_pair_diffeomorph :
    ∃ Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod (I.prod I)) (𝓘(ℝ, ℝ).prod (I.prod I))
        (ℝ × (M × M)) (ℝ × (M × M)) ∞,
      ∀ p, Ψ p = pairEquiv (fun t => (D t).toEquiv) p := by
  have hs : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod I)) (I.prod I) ∞
      (fun p : ℝ × (M × M) => (D p.1 p.2.1, D p.1 p.2.2)) :=
    (hD.comp SynchronizedPairs.first_smooth).prodMk
      (hD.comp SynchronizedPairs.second_smooth)
  exact NativeFamily.exists_spatial_source_diffeomorph hs
    (fun t => ⟨(D t).prodCongr (D t), fun _ => rfl⟩)

theorem changedFamily_regular {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hr : SynchronizedPairs.RegularOn (I := I) (J := J) F {q | q.2.1 ≠ q.2.2}) :
    SynchronizedPairs.RegularOn (I := I) (J := J)
      (changedFamily F (fun t => (D t).toEquiv)) {q | q.2.1 ≠ q.2.2} := by
  obtain ⟨Ψ, hΨ⟩ := exists_pair_diffeomorph D hD
  let e := fun t => (D t).toEquiv
  have hfirst : changedFamily F e ∘ SynchronizedPairs.first =
      (F ∘ SynchronizedPairs.first) ∘ Ψ := by
    funext q
    simp only [comp_apply, hΨ]
    rfl
  have hsecond : changedFamily F e ∘ SynchronizedPairs.second =
      (F ∘ SynchronizedPairs.second) ∘ Ψ := by
    funext q
    simp only [comp_apply, hΨ]
    rfl
  intro q hq heq
  have hold : Ψ q ∈ FamilyDoublePoints.doublePoints F := by
    rw [hΨ]
    exact (mem_doublePoints_iff F e q).mp ⟨hq, heq⟩
  change Coincidence.TransverseAt (I := 𝓘(ℝ, ℝ).prod (I.prod I)) (J := J)
    (changedFamily F e ∘ SynchronizedPairs.first)
    (changedFamily F e ∘ SynchronizedPairs.second) q
  rw [hfirst, hsecond]
  exact (Coincidence.transverseAt_comp_diffeomorph_iff Ψ q
    ((hF.comp SynchronizedPairs.first_smooth).mdifferentiableAt (by simp))
    ((hF.comp SynchronizedPairs.second_smooth).mdifferentiableAt (by simp))).mpr
      (hr (Ψ q) hold.1 hold.2)

theorem changedFamily_full_at_collisionSources {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hfull : ∀ q ∈ FamilyDoublePoints.collisionSources F,
      Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F q)) :
    ∀ q ∈ FamilyDoublePoints.collisionSources (changedFamily F (fun t => (D t).toEquiv)),
      Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J
        (changedFamily F (fun t => (D t).toEquiv)) q) := by
  obtain ⟨Ψ, hΨ⟩ := NativeFamily.exists_spatial_source_diffeomorph hD
    (fun t => ⟨D t, fun _ => rfl⟩)
  let e := fun t => (D t).toEquiv
  have he : changedFamily F e = F ∘ Ψ := by
    funext q
    simp only [comp_apply, hΨ]
    rfl
  intro q hq
  have hp : Ψ q ∈ FamilyDoublePoints.collisionSources F := by
    rw [hΨ]
    exact (mem_collisionSources_iff F e q).mp hq
  change Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J (changedFamily F e) q)
  rw [he, mfderiv_comp q (hF.mdifferentiableAt (by simp))
    (Ψ.contMDiff.mdifferentiableAt (by simp))]
  exact (hfull (Ψ q) hp).comp
    (PartialChart.bijective_mfderiv Ψ.toPartialDiffeomorph (mem_univ q)).injective

end Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization
