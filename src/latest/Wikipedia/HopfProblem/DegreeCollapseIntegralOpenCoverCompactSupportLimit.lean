import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenCoverCompactSupports

/-!
# The genuine compact-support limit on the subordinate union family

The directed limit over pairs of compact neighborhood supports maps to
the original compact-support limit by its original component maps.
The proved cofinal representative and equality criteria make this map
an isomorphism. Compatible families therefore descend without choosing
new cohomology groups or assuming independence of representatives.
-/

noncomputable section

open NoExoticSixSphere

open TopologicalSpace
open Wikipedia.HopfProblem

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenCoverCompactSupports

variable {X : Type} [TopologicalSpace X] [T2Space X] (U V : Set X) (p : ℕ)

abbrev UnionComponent (K : Index U V) :=
  IntegralCompactSupportCohomology.Component X p (unionCompact U V K)

def unionTransition (K L : Index U V) (h : K ≤ L) :
    UnionComponent U V p K →ₗ[ℤ] UnionComponent U V p L :=
  IntegralSupportedCohomology.extend (unionCompact_mono U V h) p

instance unionDirectedSystem :
    DirectedSystem (UnionComponent U V p) (unionTransition U V p · · ·) where
  map_self {K} a := LinearMap.congr_fun
    (IntegralSupportedCohomology.extend_refl (unionCompact U V K : Set X) p) a
  map_map {_N _L _K} hKL hLN a := (LinearMap.congr_fun
    (IntegralSupportedCohomology.extend_trans
      (unionCompact_mono U V hKL) (unionCompact_mono U V hLN) p) a).symm

/-- The actual directed limit of the original cohomology groups of subordinate union supports. -/
abbrev UnionCohomology := DirectLimit (UnionComponent U V p) (unionTransition U V p)

def unionOf (K : Index U V) : UnionComponent U V p K →ₗ[ℤ] UnionCohomology U V p :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    (DirectLimit.Module.of ℤ (Index U V) (UnionComponent U V p)
      (unionTransition U V p) K).toAddMonoidHom

/-- Original component insertions induce comparison to ambient compact-support cohomology. -/
def toAmbient : UnionCohomology U V p →ₗ[ℤ] IntegralCompactSupportCohomology.Cohomology X p :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    (DirectLimit.Module.lift ℤ (Index U V) (UnionComponent U V p) (unionTransition U V p)
      (fun K => IntegralCompactSupportCohomology.of X p (unionCompact U V K))
      (fun K L h a => IntegralCompactSupportCohomology.of_transition X p
        (K := unionCompact U V K) (L := unionCompact U V L)
        (unionCompact_mono U V h) a)).toAddMonoidHom

omit [T2Space X] in
theorem toAmbient_unionOf (K : Index U V) (a : UnionComponent U V p K) :
    toAmbient U V p (unionOf U V p K a) =
      IntegralCompactSupportCohomology.of X p (unionCompact U V K) a := rfl

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

include hU hV hcover

theorem toAmbient_surjective : Function.Surjective (toAmbient U V p) := by
  intro a
  obtain ⟨K, b, rfl⟩ := exists_representative U V hU hV hcover p a
  exact ⟨unionOf U V p K b, rfl⟩

theorem toAmbient_injective : Function.Injective (toAmbient U V p) := by
  intro a b
  induction a using DirectLimit.induction with
  | _ K a =>
    induction b using DirectLimit.induction with
    | _ L b =>
      intro hab
      exact Quotient.sound ((of_eq_iff U V hU hV hcover p K L a b).mp hab)

/-- Cofinality is proved on the actual component maps and both original quotient relations. -/
def unionEquiv : UnionCohomology U V p ≃ₗ[ℤ] IntegralCompactSupportCohomology.Cohomology X p :=
  LinearEquiv.ofBijective (toAmbient U V p)
    ⟨toAmbient_injective U V p hU hV hcover, toAmbient_surjective U V p hU hV hcover⟩

theorem unionEquiv_toLinearMap : (unionEquiv U V p hU hV hcover).toLinearMap =
    toAmbient U V p := rfl

variable {P : Type} [AddCommGroup P] [Module ℤ P]
  (f : ∀ K : Index U V, UnionComponent U V p K →ₗ[ℤ] P)
  (hf : ∀ (K L : Index U V) (h : K ≤ L) (a : UnionComponent U V p K),
    f L (unionTransition U V p K L h a) = f K a)

/-- Descend a compatible family from subordinate compact supports to the original ambient limit. -/
def cofinalLift : IntegralCompactSupportCohomology.Cohomology X p →ₗ[ℤ] P :=
  (ConstantSheafSingularComparison.addHomToIntLinearMap
    (DirectLimit.Module.lift ℤ (Index U V) (UnionComponent U V p) (unionTransition U V p)
      f hf).toAddMonoidHom).comp (unionEquiv U V p hU hV hcover).symm.toLinearMap

/-- The descended map retains every original compact-union representative formula. -/
theorem cofinalLift_of (K : Index U V) (a : UnionComponent U V p K) :
    cofinalLift U V p hU hV hcover f hf
        (IntegralCompactSupportCohomology.of X p (unionCompact U V K) a) = f K a := by
  change (ConstantSheafSingularComparison.addHomToIntLinearMap
    (DirectLimit.Module.lift ℤ (Index U V) (UnionComponent U V p) (unionTransition U V p)
      f hf).toAddMonoidHom)
      ((unionEquiv U V p hU hV hcover).symm
        (unionEquiv U V p hU hV hcover (unionOf U V p K a))) = f K a
  rw [LinearEquiv.symm_apply_apply]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenCoverCompactSupports
