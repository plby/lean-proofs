import Wikipedia.NoExoticSixSphere.SlabInterior
import Wikipedia.NoExoticSixSphere.ChangedModelAtlas
import Wikipedia.NoExoticSixSphere.ModelAtlasTransport
import Wikipedia.NoExoticSixSphere.RegularFiberManifold

/-!
# Interior slab charts in a common boundary model

The strict-time part inherits the regular fiber's smooth structure. The
checked change of model puts it in the same boundary model as the endpoint
pieces, while every point of this open piece remains an interior point.
-/

open scoped Manifold ContDiff
open Module Topology

namespace NoExoticSixSphere.CylinderFiberSlab

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  (F : C(ℝ × M, N)) (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) J ∞ F) (b : N)
  (hreg : ∀ p, F p = b → Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod I) J F p))
  (l : ℕ) (hd : finrank ℝ (ℝ × B) = finrank ℝ C + l) (s t : ℝ)
  {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace G]
  {R : ModelWithCorners ℝ D G}
  (Φ : PartialDiffeomorph (𝓡 l) R (EuclideanSpace ℝ (Fin l)) G ∞)
  (hsource : Φ.source = Set.univ)

@[instance_reducible]
noncomputable def interiorAtlas : ChartedSpace G (interiorDomain F b s t) :=
  letI := regularFiberAtlas F hF b hreg l hd
  letI := regularFiber_isManifold F hF b hreg l hd
  letI := ChangedModelAtlas.chartedSpace (M := fiberInterior F b s t) Φ hsource
  ModelAtlasTransport.atlas (H := G) (interiorHomeomorph F b s t)

theorem interiorAtlas_isManifold : letI := interiorAtlas F hF b hreg l hd s t Φ hsource;
    IsManifold R ∞ (interiorDomain F b s t) := by
  let := regularFiberAtlas F hF b hreg l hd
  let := regularFiber_isManifold F hF b hreg l hd
  let := ChangedModelAtlas.chartedSpace (M := fiberInterior F b s t) Φ hsource
  let := ChangedModelAtlas.isManifold (M := fiberInterior F b s t) Φ hsource
  exact ModelAtlasTransport.isManifold (interiorHomeomorph F b s t) R

theorem interiorAtlas_contMDiff_ambient :
    letI := interiorAtlas F hF b hreg l hd s t Φ hsource;
    ContMDiff R ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun p : interiorDomain F b s t ↦ p.val.val.val) := by
  let := regularFiberAtlas F hF b hreg l hd
  let := regularFiber_isManifold F hF b hreg l hd
  let := ChangedModelAtlas.chartedSpace (M := fiberInterior F b s t) Φ hsource
  let := interiorAtlas F hF b hreg l hd s t Φ hsource
  have hinc : ContMDiff (𝓡 l) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun p : fiberInterior F b s t ↦ p.val.val) :=
    (regularFiber_contMDiff_subtype_val F hF b hreg l hd).comp contMDiff_subtype_val
  exact hinc.comp
    ((ChangedModelAtlas.contMDiff_toOriginal (M := fiberInterior F b s t) Φ hsource).comp
      (ModelAtlasTransport.contMDiff (interiorHomeomorph F b s t) R))

variable {E H'' P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H''] {L : ModelWithCorners ℝ E H''}
  [TopologicalSpace P] [ChartedSpace H'' P]

theorem interiorAtlas_contMDiff_iff_ambient (g : P → interiorDomain F b s t) :
    letI := interiorAtlas F hF b hreg l hd s t Φ hsource;
    ContMDiff L R ∞ g ↔
      ContMDiff L ((𝓘(ℝ, ℝ)).prod I) ∞ (fun x ↦ (g x).val.val.val) := by
  let := regularFiberAtlas F hF b hreg l hd
  let := regularFiber_isManifold F hF b hreg l hd
  let := ChangedModelAtlas.chartedSpace (M := fiberInterior F b s t) Φ hsource
  let := interiorAtlas F hF b hreg l hd s t Φ hsource
  constructor
  · intro hg
    exact (interiorAtlas_contMDiff_ambient F hF b hreg l hd s t Φ hsource).comp hg
  · intro hg
    let e := interiorHomeomorph F b s t
    let q := e ∘ g
    have hqf : ContMDiff L (𝓡 l) ∞ (fun x ↦ (q x).val) :=
      (regularFiber_contMDiff_iff_ambient F hF b hreg l hd _).mpr hg
    have hqo : ContMDiff L (𝓡 l) ∞ q :=
      (ContMDiff.subtypeVal_comp_iff (fiberInterior F b s t) q).mp hqf
    have hqn : ContMDiff L R ∞ q :=
      (ChangedModelAtlas.contMDiff_fromOriginal (M := fiberInterior F b s t) Φ hsource).comp hqo
    have h := (ModelAtlasTransport.contMDiff_symm e R).comp hqn
    simpa only [q, Function.comp_def, Homeomorph.symm_apply_apply] using h

theorem interiorAtlas_isInteriorPoint
    (hinterior : ∀ y ∈ Φ.target, R y ∈ interior (Set.range R))
    (p : interiorDomain F b s t) :
    letI := interiorAtlas F hF b hreg l hd s t Φ hsource;
    R.IsInteriorPoint p := by
  let := regularFiberAtlas F hF b hreg l hd
  let := regularFiber_isManifold F hF b hreg l hd
  let := ChangedModelAtlas.chartedSpace (M := fiberInterior F b s t) Φ hsource
  let := ChangedModelAtlas.isManifold (M := fiberInterior F b s t) Φ hsource
  let := interiorAtlas F hF b hreg l hd s t Φ hsource
  let := interiorAtlas_isManifold F hF b hreg l hd s t Φ hsource
  let e := interiorHomeomorph F b s t
  have he := (ModelAtlasTransport.diffeomorph e R).isLocalDiffeomorph p
  exact (he.isInteriorPoint_iff (by simp)).mpr
    (ChangedModelAtlas.isInteriorPoint Φ hsource hinterior (e p))

end NoExoticSixSphere.CylinderFiberSlab
