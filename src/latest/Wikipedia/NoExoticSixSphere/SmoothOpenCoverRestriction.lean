import Wikipedia.NoExoticSixSphere.SmoothOpenCoverMaps
import Wikipedia.NoExoticSixSphere.OpenCodomainLocalDiffeomorph

/-!
# Smooth gluing on an inherited open subset of a glued manifold

Restrict each original local atlas to the preimage of an open subset. The
restricted inclusions are local diffeomorphisms into its inherited global
atlas. Compatible smooth local maps therefore glue to a smooth map without
replacing that inherited atlas.
-/

noncomputable section

open Function Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothOpenCover

variable {B H X ι : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace X]
  {U : ι → Opens X} (A : SmoothOpenCover I U)

def restrictedDomain (V : Opens X) (i : ι) : Opens (U i) :=
  ⟨Subtype.val ⁻¹' V, V.isOpen.preimage continuous_subtype_val⟩

def restrictedInclusion (V : Opens X) (i : ι) (p : restrictedDomain (U := U) V i) : V :=
  ⟨p.val.val, p.property⟩

theorem isLocalDiffeomorphAt_restrictedInclusion (V : Opens X) (i : ι)
    (p : restrictedDomain (U := U) V i) :
    letI := A.chartedSpace; letI := A.localAtlas i;
    IsLocalDiffeomorphAt I I ∞ (restrictedInclusion (U := U) V i) p := by
  let := A.chartedSpace
  let := A.localAtlas i
  have h := (isLocalDiffeomorphAt_openSubset_val (I := I) (restrictedDomain V i) p).comp I X
    (A.isLocalDiffeomorphAt_inclusion i p.val)
  exact isLocalDiffeomorphAt_codRestrict V (fun q : restrictedDomain (U := U) V i ↦ q.property) h

variable {C H' Y : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace Y] [ChartedSpace H' Y]

theorem contMDiff_onOpen_iff (V : Opens X) (f : V → Y) : letI := A.chartedSpace;
    ContMDiff I J ∞ f ↔ ∀ i, letI := A.localAtlas i;
      ContMDiff I J ∞ (f ∘ restrictedInclusion (U := U) V i) := by
  let := A.chartedSpace
  constructor
  · intro hf i
    let := A.localAtlas i
    intro p
    exact hf.contMDiffAt.comp p (A.isLocalDiffeomorphAt_restrictedInclusion V i p).contMDiffAt
  · intro hlocal x
    obtain ⟨i, hi⟩ := A.covers x.val
    let := A.localAtlas i
    let p : restrictedDomain (U := U) V i := ⟨⟨x.val, hi⟩, x.property⟩
    exact (contMDiffAt_comp_localDiffeomorph_iff
      (A.isLocalDiffeomorphAt_restrictedInclusion V i p) f).mp (hlocal i p)

def glueOnOpen (V : Opens X) (g : ∀ i, restrictedDomain (U := U) V i → Y) (x : V) : Y :=
  g (A.indexAt x.val).1 ⟨(A.indexAt x.val).2, x.property⟩

omit [TopologicalSpace Y] in
theorem glueOnOpen_on_piece (V : Opens X) (g : ∀ i, restrictedDomain (U := U) V i → Y)
    (he : ∀ i j (p : restrictedDomain (U := U) V i) (q : restrictedDomain (U := U) V j),
      p.val.val = q.val.val → g i p = g j q)
    (i : ι) (p : restrictedDomain (U := U) V i) :
    A.glueOnOpen V g (restrictedInclusion V i p) = g i p :=
  he _ _ _ _ rfl

theorem contMDiff_glueOnOpen (V : Opens X) (g : ∀ i, restrictedDomain (U := U) V i → Y)
    (he : ∀ i j (p : restrictedDomain (U := U) V i) (q : restrictedDomain (U := U) V j),
      p.val.val = q.val.val → g i p = g j q)
    (hg : ∀ i, letI := A.localAtlas i; ContMDiff I J ∞ (g i)) :
    letI := A.chartedSpace; ContMDiff I J ∞ (A.glueOnOpen V g) := by
  let := A.chartedSpace
  apply (A.contMDiff_onOpen_iff V _).mpr
  intro i
  let := A.localAtlas i
  have heq : A.glueOnOpen V g ∘ restrictedInclusion (U := U) V i = g i :=
    funext (A.glueOnOpen_on_piece V g he i)
  rw [heq]
  exact hg i

end NoExoticSixSphere.SmoothOpenCover
