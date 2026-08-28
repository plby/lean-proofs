import Wikipedia.NoExoticSixSphere.JamesSphereQuotientHopfRange
import Wikipedia.NoExoticSixSphere.JamesSphereFiberBoundary

/-!
# Exact EHP assembly from the actual comparison

All maps here are the original native suspension, coordinate-corrected
James--Hopf map, and genuine fiber boundary and projection. This assembly
retains an explicit input: bijectivity of the actual fiber-to-quotient
homomorphism in the required degree. Inverting that map defines the
connecting homomorphism and gives three consecutive exact terms.
`JamesSphereEHPMetastable` discharges the input in the full required range.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.EHP

open FiberQuotient InclusionRange SuspensionComparison FirstStageQuotient

variable (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n)
  (hF : Function.Bijective (FiberQuotient.hom n d))

def fiberSphereEquiv :
    π_ d (Fiber n) (FiberQuotient.basepoint n) ≃*
      π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)) :=
  (MulEquiv.ofBijective (FiberQuotient.hom n d) hF).trans
    (sphereHopfPiEquiv n (d + 1) hn (by omega))

def connectingHom :
    π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)) →*
      π_ d (Sphere n) (spherePole n) :=
  (projectionHom n d).comp (fiberSphereEquiv n d hn hdn hF).symm.toMonoidHom

theorem fiberSphereEquiv_boundaryHom (c : π_ (d + 1) (WordHomology.Words n) 1) :
    fiberSphereEquiv n d hn hdn hF (boundaryHom n d c) =
      orderedHopfHom n hn (d + 1) (orderedComparison n hn (d + 1) c) := by
  change sphereHopfHom n hn (d + 1) (FiberQuotient.hom n d (boundaryHom n d c)) = _
  rw [hom_boundaryHom]
  exact sphereHopfHom_quotientMap n hn (d + 1) c

theorem connectingHom_fiberSphereEquiv (c : π_ d (Fiber n) (FiberQuotient.basepoint n)) :
    connectingHom n d hn hdn hF (fiberSphereEquiv n d hn hdn hF c) =
      projectionHom n d c := by
  change projectionHom n d
    ((fiberSphereEquiv n d hn hdn hF).symm (fiberSphereEquiv n d hn hdn hF c)) = _
  rw [MulEquiv.symm_apply_apply]

include hdn hF in
theorem hopf_eq_one_iff_of_comparison
    (c : π_ (d + 1 + 1) (Sphere (n + 1)) (spherePole (n + 1))) :
    orderedHopfHom n hn (d + 1) c = 1 ↔
      ∃ a : π_ (d + 1) (Sphere n) (spherePole n),
        CubicalSphereSuspension.hom (d + 1) n a = c := by
  obtain ⟨b, rfl⟩ := (orderedComparison n hn (d + 1)).surjective c
  rw [← fiberSphereEquiv_boundaryHom n d hn hdn hF,
    (fiberSphereEquiv n d hn hdn hF).map_eq_one_iff, boundaryHom_eq_one_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (orderedComparison_inclusion n hn (d + 1) a).symm.trans
      (congrArg (orderedComparison n hn (d + 1)) ha)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (orderedComparison n hn (d + 1)).injective
      ((orderedComparison_inclusion n hn (d + 1) a).trans ha)⟩

theorem connecting_eq_one_iff_of_comparison
    (c : π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1))) :
    connectingHom n d hn hdn hF c = 1 ↔
      ∃ a : π_ (d + 1 + 1) (Sphere (n + 1)) (spherePole (n + 1)),
        orderedHopfHom n hn (d + 1) a = c := by
  obtain ⟨b, rfl⟩ := (fiberSphereEquiv n d hn hdn hF).surjective c
  rw [connectingHom_fiberSphereEquiv, projectionHom_eq_one_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨orderedComparison n hn (d + 1) a, ?_⟩
    rw [← fiberSphereEquiv_boundaryHom n d hn hdn hF, ha]
  · rintro ⟨a, ha⟩
    obtain ⟨a, rfl⟩ := (orderedComparison n hn (d + 1)).surjective a
    refine ⟨a, (fiberSphereEquiv n d hn hdn hF).injective ?_⟩
    rw [fiberSphereEquiv_boundaryHom]
    exact ha

theorem suspension_eq_one_iff_of_comparison (c : π_ d (Sphere n) (spherePole n)) :
    CubicalSphereSuspension.hom d n c = 1 ↔
      ∃ a : π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)),
        connectingHom n d hn hdn hF a = c := by
  rw [← orderedComparison_inclusion n hn d,
    (orderedComparison n hn d).map_eq_one_iff, inclusion_eq_one_iff_projection]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨fiberSphereEquiv n d hn hdn hF a,
      (connectingHom_fiberSphereEquiv n d hn hdn hF a).trans ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨(fiberSphereEquiv n d hn hdn hF).symm a, ha⟩

end NoExoticSixSphere.JamesSphere.EHP
