import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSourceCube
import Wikipedia.NoExoticSixSphere.NativeHomotopyTargetEquality
import Wikipedia.NoExoticSixSphere.BasedHomotopyNativeMap

/-!
# The literal source quotient is the original native sphere

The exact cube fibers construct a based homeomorphism from the standard
sphere to the actual boundary quotient. Combining it with the proved
collapse equivalence gives the source comparison on every positive
native group. The attaching-map formula retains the constructed source
contraction; it does not replace that homotopy by arbitrary axes tracks.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

def sourceSphereMap (n : ℕ) : C(Sphere (2 * n + 1), SourceQuotient n) :=
  SmoothCube.descend (Nat.succ_pos (2 * n)) (sourceCube n)

theorem sourceSphereMap_quotient (n : ℕ) (u : Fin (2 * n + 1) → I) :
    sourceSphereMap n (SmoothCube.quotient (2 * n + 1) u) = cubeSourceMap n u :=
  SmoothCube.descend_quotient (Nat.succ_pos (2 * n)) (sourceCube n) u

theorem sourceSphereMap_pole (n : ℕ) :
    sourceSphereMap n (spherePole (2 * n + 1)) = sourcePoint n :=
  SmoothCube.descend_pole (Nat.succ_pos (2 * n)) (sourceCube n)

theorem sourceSphereMap_bijective (n : ℕ) : Function.Bijective (sourceSphereMap n) := by
  constructor
  · intro x y h
    obtain ⟨u, rfl⟩ := SmoothCube.quotient_surjective (Nat.succ_pos (2 * n)) x
    obtain ⟨v, rfl⟩ := SmoothCube.quotient_surjective (Nat.succ_pos (2 * n)) y
    rw [sourceSphereMap_quotient, sourceSphereMap_quotient] at h
    exact (SmoothCube.quotient_eq_iff (2 * n + 1) u v).mpr ((cubeSourceMap_eq_iff n u v).mp h)
  · intro y
    obtain ⟨u, hu⟩ := cubeSourceMap_surjective n y
    exact ⟨SmoothCube.quotient (2 * n + 1) u, (sourceSphereMap_quotient n u).trans hu⟩

def sourceSphereHomeomorph (n : ℕ) : Sphere (2 * n + 1) ≃ₜ SourceQuotient n :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (sourceSphereMap n) (sourceSphereMap_bijective n))
    (sourceSphereMap n).continuous

theorem sourceSphereHomeomorph_pole (n : ℕ) :
    sourceSphereHomeomorph n (spherePole (2 * n + 1)) = sourcePoint n := sourceSphereMap_pole n

def sourceSpherePiEquiv (n d : ℕ) [NeZero d] :
    π_ d (Sphere (2 * n + 1)) (spherePole (2 * n + 1)) ≃*
      π_ d (SourceQuotient n) (sourcePoint n) :=
  (HigherHomotopyCoordinates.homeomorphMulEquiv (Fin d)
    (sourceSphereHomeomorph n) (spherePole (2 * n + 1))).trans
      (NativeHomotopyTargetEquality.equiv d (sourceSphereHomeomorph_pole n))

theorem sourceSpherePiEquiv_apply (n d : ℕ) [NeZero d]
    (c : π_ d (Sphere (2 * n + 1)) (spherePole (2 * n + 1))) :
    sourceSpherePiEquiv n d c =
      HigherHomotopy.map (N := Fin d) (sourceSphereMap n) (sourceSphereMap_pole n) c :=
  NativeHomotopyTargetEquality.equiv_map d (sourceSphereMap n) (sourceSphereMap_pole n) c

def sourceComparison (n d : ℕ) [NeZero d] :
    π_ d (fullBoundary n) (fullPoint n) ≃*
      π_ d (Sphere (2 * n + 1)) (spherePole (2 * n + 1)) :=
  (sourceCollapseEquiv n d).trans (sourceSpherePiEquiv n d).symm

theorem sourceSpherePiEquiv_comparison (n d : ℕ) [NeZero d]
    (c : π_ d (fullBoundary n) (fullPoint n)) :
    sourceSpherePiEquiv n d (sourceComparison n d c) = sourceCollapseHom n d c :=
  (sourceSpherePiEquiv n d).apply_symm_apply _

def sourceSphereAttaching (n : ℕ) : C(Sphere (2 * n + 1), Sphere (n + 1)) :=
  (sourceQuotientAttaching n).comp (sourceSphereMap n)

theorem sourceSphereAttaching_quotient (n : ℕ) (u : Fin (2 * n + 1) → unitInterval) :
    sourceSphereAttaching n (SmoothCube.quotient (2 * n + 1) u) =
      fullAttaching n (sourceEndpoint n (cubeSourceBoundary n u)) :=
  (congrArg (sourceQuotientAttaching n) (sourceSphereMap_quotient n u)).trans
    (sourceQuotientAttaching_collapse n (cubeSourceBoundary n u))

theorem sourceSphereAttaching_pole (n : ℕ) :
    sourceSphereAttaching n (spherePole (2 * n + 1)) = spherePole (n + 1) :=
  (congrArg (sourceQuotientAttaching n) (sourceSphereMap_pole n)).trans
    (sourceQuotientAttaching_point n)

def sourceSphereAttachingHom (n d : ℕ) [NeZero d] :
    π_ d (Sphere (2 * n + 1)) (spherePole (2 * n + 1)) →*
      π_ d (Sphere (n + 1)) (spherePole (n + 1)) :=
  HigherHomotopy.mapMonoidHom (sourceSphereAttaching n) (sourceSphereAttaching_pole n)

theorem sourceAttaching_comparison (n d : ℕ) [NeZero d]
    (c : π_ d (fullBoundary n) (fullPoint n)) :
    HigherHomotopy.map (N := Fin d) (fullAttaching n) (fullAttaching_point n) c =
      sourceSphereAttachingHom n d (sourceComparison n d c) := by
  have h := HigherHomotopy.map_eq_of_based_homotopy (fullAttaching n)
    ((sourceQuotientAttaching n).comp (sourceCollapse n)) (fullAttaching_point n)
    (sourceQuotientAttaching_point n) (sourceAttachingHomotopy n) c
  calc
    _ = HigherHomotopy.map (sourceQuotientAttaching n) (sourceQuotientAttaching_point n)
        (sourceCollapseHom n d c) := h.trans
      (HigherHomotopy.map_comp (sourceCollapse n)
        (show sourceCollapse n (fullPoint n) = sourcePoint n from rfl)
        (sourceQuotientAttaching n) (sourceQuotientAttaching_point n) c).symm
    _ = HigherHomotopy.map (sourceQuotientAttaching n) (sourceQuotientAttaching_point n)
        (sourceSpherePiEquiv n d (sourceComparison n d c)) :=
      congrArg (HigherHomotopy.map (sourceQuotientAttaching n) (sourceQuotientAttaching_point n))
        (sourceSpherePiEquiv_comparison n d c).symm
    _ = HigherHomotopy.map (sourceQuotientAttaching n) (sourceQuotientAttaching_point n)
        (HigherHomotopy.map (sourceSphereMap n) (sourceSphereMap_pole n)
          (sourceComparison n d c)) :=
      congrArg (HigherHomotopy.map (sourceQuotientAttaching n) (sourceQuotientAttaching_point n))
        (sourceSpherePiEquiv_apply n d _)
    _ = _ := HigherHomotopy.map_comp (sourceSphereMap n) (sourceSphereMap_pole n)
      (sourceQuotientAttaching n) (sourceQuotientAttaching_point n) _

end NoExoticSixSphere.JamesSphere.AttachingSquare
