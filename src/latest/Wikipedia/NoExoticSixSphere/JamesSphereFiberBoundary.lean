import Wikipedia.NoExoticSixSphere.JamesSphereInclusionFiberConnectivity

/-!
# The actual James fiber sequence at the unit-word basepoint

The native fiber boundary is originally based at the image of the sphere
pole. Transport along its proved equality with the unit word gives the
boundary used by the James comparison. Its quotient formula and all
three exactness statements retain the original maps and native groups.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.FiberQuotient

def wordBasepointEquiv (n d : ℕ) [NeZero d] :
    π_ d (WordHomology.Words n) (inclusion n (spherePole n)) ≃*
      π_ d (WordHomology.Words n) 1 :=
  NativeHomotopyTargetEquality.equiv d (NativeHopf.inclusion_pole n)

theorem wordBasepointEquiv_inclusion (n d : ℕ) [NeZero d]
    (c : π_ d (Sphere n) (spherePole n)) :
    wordBasepointEquiv n d
      (HigherHomotopy.map (N := Fin d) (inclusion n) (y := spherePole n) rfl c) =
        HigherHomotopy.map (N := Fin d) (inclusion n) (NativeHopf.inclusion_pole n) c :=
  NativeHomotopyTargetEquality.equiv_map d (inclusion n) (NativeHopf.inclusion_pole n) c

theorem quotient_wordBasepointEquiv (n d : ℕ) [NeZero d]
    (c : π_ d (WordHomology.Words n) (inclusion n (spherePole n))) :
    HigherHomotopy.map (N := Fin d) (FirstStageQuotient.quotientMap n) rfl
      (wordBasepointEquiv n d c) =
        HigherHomotopy.map (N := Fin d) (FirstStageQuotient.quotientMap n)
          (quotient_inclusion n (spherePole n)) c :=
  NativeHomotopyTargetEquality.map_equiv d (FirstStageQuotient.quotientMap n)
    (NativeHopf.inclusion_pole n) rfl c

def boundaryHom (n d : ℕ) [NeZero d] :
    π_ (d + 1) (WordHomology.Words n) 1 →* π_ d (Fiber n) (basepoint n) :=
  (HomotopyFiber.boundaryHom d (inclusion n) (spherePole n)).comp
    (wordBasepointEquiv n (d + 1)).symm.toMonoidHom

def projectionHom (n d : ℕ) [NeZero d] :
    π_ d (Fiber n) (basepoint n) →* π_ d (Sphere n) (spherePole n) :=
  HigherHomotopy.mapMonoidHom (N := Fin d)
    (HomotopyFiber.projection (inclusion n) (inclusion n (spherePole n))) rfl

theorem hom_boundaryHom (n d : ℕ) [NeZero d]
    (c : π_ (d + 1) (WordHomology.Words n) 1) :
    hom n d (boundaryHom n d c) =
      HigherHomotopy.map (N := Fin (d + 1)) (FirstStageQuotient.quotientMap n) rfl c := by
  change hom n d (HomotopyFiber.boundaryHom d (inclusion n) (spherePole n)
    ((wordBasepointEquiv n (d + 1)).symm c)) = _
  rw [hom_boundary, ← quotient_wordBasepointEquiv, MulEquiv.apply_symm_apply]

theorem boundaryHom_eq_one_iff (n d : ℕ) [NeZero d]
    (c : π_ (d + 1) (WordHomology.Words n) 1) :
    boundaryHom n d c = 1 ↔ ∃ a : π_ (d + 1) (Sphere n) (spherePole n),
      HigherHomotopy.map (N := Fin (d + 1)) (inclusion n) (NativeHopf.inclusion_pole n) a = c := by
  change HomotopyFiber.boundaryMap d (inclusion n) (spherePole n)
    ((wordBasepointEquiv n (d + 1)).symm c) = Quotient.mk' GenLoop.const ↔ _
  rw [HomotopyFiber.boundary_eq_const_iff_exists_source_class]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← wordBasepointEquiv_inclusion, ha, MulEquiv.apply_symm_apply]
  · rintro ⟨a, ha⟩
    refine ⟨a, (wordBasepointEquiv n (d + 1)).injective ?_⟩
    rw [wordBasepointEquiv_inclusion, MulEquiv.apply_symm_apply]
    exact ha

theorem projectionHom_eq_one_iff (n d : ℕ) [NeZero d]
    (c : π_ d (Fiber n) (basepoint n)) :
    projectionHom n d c = 1 ↔ ∃ a : π_ (d + 1) (WordHomology.Words n) 1,
      boundaryHom n d a = c := by
  have he : projectionHom n d c = 1 ↔
      ∃ a : π_ (d + 1) (WordHomology.Words n) (inclusion n (spherePole n)),
        HomotopyFiber.boundaryHom d (inclusion n) (spherePole n) a = c :=
    HomotopyFiber.projection_eq_const_iff_exists_boundary_class d (inclusion n) (spherePole n) c
  rw [he]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨wordBasepointEquiv n (d + 1) a, ?_⟩
    change HomotopyFiber.boundaryMap d (inclusion n) (spherePole n)
      ((wordBasepointEquiv n (d + 1)).symm (wordBasepointEquiv n (d + 1) a)) = c
    rw [MulEquiv.symm_apply_apply]
    exact ha
  · rintro ⟨a, ha⟩
    exact ⟨(wordBasepointEquiv n (d + 1)).symm a, ha⟩

theorem inclusion_eq_one_iff_projection (n d : ℕ) [NeZero d]
    (c : π_ d (Sphere n) (spherePole n)) :
    HigherHomotopy.map (N := Fin d) (inclusion n) (NativeHopf.inclusion_pole n) c = 1 ↔
      ∃ a : π_ d (Fiber n) (basepoint n), projectionHom n d a = c := by
  have he : HigherHomotopy.map (N := Fin d) (inclusion n) (NativeHopf.inclusion_pole n) c = 1 ↔
      HigherHomotopy.map (N := Fin d) (inclusion n) (y := spherePole n) rfl c = 1 := by
    rw [← wordBasepointEquiv_inclusion]
    exact (wordBasepointEquiv n d).map_eq_one_iff
  rw [he]
  exact HomotopyFiber.map_eq_const_iff_exists_fiber_class (inclusion n) (spherePole n) c

theorem quotient_eq_one_iff_of_hom_injective (n d : ℕ) [NeZero d]
    (hi : Function.Injective (hom n d)) (c : π_ (d + 1) (WordHomology.Words n) 1) :
    HigherHomotopy.map (N := Fin (d + 1)) (FirstStageQuotient.quotientMap n) rfl c = 1 ↔
      ∃ a : π_ (d + 1) (Sphere n) (spherePole n),
        HigherHomotopy.map (N := Fin (d + 1)) (inclusion n)
          (NativeHopf.inclusion_pole n) a = c := by
  rw [← hom_boundaryHom, ← boundaryHom_eq_one_iff]
  constructor
  · intro h
    exact hi (h.trans (map_one (hom n d)).symm)
  · intro h
    exact (congrArg (hom n d) h).trans (map_one (hom n d))

end NoExoticSixSphere.JamesSphere.FiberQuotient
