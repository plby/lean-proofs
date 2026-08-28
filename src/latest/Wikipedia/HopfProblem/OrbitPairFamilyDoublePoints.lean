import Wikipedia.HopfProblem.OrbitPairFamilyTrackImmersion
import Wikipedia.HopfProblem.OrbitPairChartFamilyExtension

/-!
# Compactness of the actual regular-family double-point locus

Spatial immersion makes the parameter-retaining track locally injective.
Consequently collisions cannot approach the diagonal, and the ordered
double-point locus is closed in the full parameter-pair space. Compactness
of the source and embedded endpoint collars then make that locus compact.
Neither transversality nor finiteness of the double points is asserted.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints

open Wikipedia.SmoothSixDPoincare
open PlaneImmersion (Plane)

variable {E H M G H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

def track (F : ℝ × M → N) (q : ℝ × M) : ℝ × N := (q.1, F q)

def doublePoints (F : ℝ × M → N) : Set (ℝ × (M × M)) :=
  {q | q.2.1 ≠ q.2.2 ∧ F (q.1, q.2.1) = F (q.1, q.2.2)}

theorem exists_open_injOn_track
    (c : PartialDiffeomorph 𝓘(ℝ, Plane) I Plane M ∞) (hsource : c.source = univ)
    (F : ℝ × M → N) (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (q : ℝ × M) (hq : q.2 ∈ c.target)
    (hinj : Injective (mfderiv I J (fun x => F (q.1, x)) q.2)) :
    ∃ W : Set (ℝ × M), IsOpen W ∧ q ∈ W ∧ InjOn (track F) W := by
  let p : ℝ × Plane := ChartFamily.coordinates c ⟨q, hq⟩
  have hp : ChartFamily.cylinderMap c p = q := ChartFamily.cylinderMap_coordinates c ⟨q, hq⟩
  let fD : ℝ × Plane → N := F ∘ ChartFamily.cylinderMap c
  have hfD : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ fD :=
    hF.comp (ChartFamily.cylinderMap_smooth c hsource)
  have hfs : ContMDiff I J ∞ (fun x => F (p.1, x)) :=
    hF.comp (contMDiff_const.prodMk contMDiff_id)
  have hc := ChartFamily.parametrization_smooth c hsource
  have hi : Injective (mfderiv 𝓘(ℝ, Plane) J (fun x => fD (p.1, x)) p.2) := by
    change Injective (mfderiv 𝓘(ℝ, Plane) J ((fun x => F (p.1, x)) ∘ c) p.2)
    rw [mfderiv_comp p.2 (hfs.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
    have hnative : Injective (mfderiv I J (fun x => F (p.1, x)) (c p.2)) := by
      change Injective (mfderiv I J (fun x => F ((ChartFamily.cylinderMap c p).1, x))
        (ChartFamily.cylinderMap c p).2)
      rw [hp]
      exact hinj
    exact hnative.comp (PartialChart.bijective_mfderiv c
      (x := p.2) (hsource.symm ▸ mem_univ p.2)).1
  obtain ⟨V, hV, hpV, hVi⟩ := FamilyTrack.exists_open_injOn_track hfD p hi
  have he : IsOpenEmbedding (ChartFamily.cylinderMap c) :=
    IsOpenEmbedding.id.prodMap (c.toOpenPartialHomeomorph.isOpenEmbedding hsource)
  refine ⟨ChartFamily.cylinderMap c '' V, he.isOpenMap V hV, ⟨p, hpV, hp⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
  exact congrArg (ChartFamily.cylinderMap c) (hVi hu hv huv)

theorem diagonal_not_mem_closure {ι : Type*}
    (c : ι → PartialDiffeomorph 𝓘(ℝ, Plane) I Plane M ∞)
    (hsource : ∀ i, (c i).source = univ) (hcover : ∀ x : M, ∃ i, x ∈ (c i).target)
    (F : ℝ × M → N) (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (t : ℝ) (x : M) (hinj : Injective (mfderiv I J (fun y => F (t, y)) x)) :
    (t, (x, x)) ∉ closure (doublePoints F) := by
  obtain ⟨i, hi⟩ := hcover x
  obtain ⟨V, hV, hxV, hVi⟩ := exists_open_injOn_track (c i) (hsource i) F hF (t, x) hi hinj
  let W : Set (ℝ × (M × M)) := {q | (q.1, q.2.1) ∈ V ∧ (q.1, q.2.2) ∈ V}
  have hW : IsOpen W :=
    (hV.preimage (continuous_fst.prodMk continuous_snd.fst)).inter
      (hV.preimage (continuous_fst.prodMk continuous_snd.snd))
  intro h
  obtain ⟨q, hqW, hq⟩ := (mem_closure_iff.mp h) W hW ⟨hxV, hxV⟩
  apply hq.1
  exact congrArg Prod.snd (hVi hqW.1 hqW.2 (Prod.ext rfl hq.2))

theorem isClosed_doublePoints {ι : Type*}
    (c : ι → PartialDiffeomorph 𝓘(ℝ, Plane) I Plane M ∞)
    (hsource : ∀ i, (c i).source = univ) (hcover : ∀ x : M, ∃ i, x ∈ (c i).target)
    (F : ℝ × M → N) (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hinj : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x)) :
    IsClosed (doublePoints F) := by
  have heq : IsClosed {q : ℝ × (M × M) | F (q.1, q.2.1) = F (q.1, q.2.2)} :=
    isClosed_eq (hF.continuous.comp (continuous_fst.prodMk continuous_snd.fst))
      (hF.continuous.comp (continuous_fst.prodMk continuous_snd.snd))
  apply isClosed_of_closure_subset
  intro q hq
  refine ⟨?_, (closure_minimal (fun _ h => h.2) heq) hq⟩
  intro hdiag
  have he : q = (q.1, (q.2.1, q.2.1)) := Prod.ext rfl (Prod.ext rfl hdiag.symm)
  have hn := diagonal_not_mem_closure c hsource hcover F hF q.1 q.2.1 (hinj q.1 q.2.1)
  apply hn
  rwa [← he]

variable [CompactSpace M]

theorem isCompact_doublePoints {ι : Type*}
    (c : ι → PartialDiffeomorph 𝓘(ℝ, Plane) I Plane M ∞)
    (hsource : ∀ i, (c i).source = univ) (hcover : ∀ x : M, ∃ i, x ∈ (c i).target)
    (F : ℝ × M → N) (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hinj : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (a b : ℝ) (hends : ∀ t, t ≤ a ∨ b ≤ t → Injective (fun x => F (t, x))) :
    IsCompact (doublePoints F) := by
  apply (isCompact_Icc (a := a) (b := b)).prod (isCompact_univ (X := M × M))
    |>.of_isClosed_subset (isClosed_doublePoints c hsource hcover F hF hinj)
  intro q hq
  constructor
  · constructor
    · by_contra ht
      exact hq.1 (hends q.1 (Or.inl (le_of_lt (lt_of_not_ge ht))) hq.2)
    · by_contra ht
      exact hq.1 (hends q.1 (Or.inr (le_of_lt (lt_of_not_ge ht))) hq.2)
  · exact mem_univ _

end Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints
