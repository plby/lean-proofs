import Wikipedia.NoExoticSixSphere.SixSphereCandidateHopfExclusion
import Wikipedia.NoExoticSixSphere.QuaternionicHopfStableNontriviality
import Wikipedia.HopfProblem.DegreeCollapseSixthStemMapDichotomy

/-!
# There are no exotic smooth six-spheres

The existing whole-stem calculation gives a dichotomy for actual maps
at the S16 to S10 stage. The original Hopf-product collapse is nonnull,
and the candidate-specific Arf argument excludes that alternative for
the candidate's third suspension. Its actual finite nullhomotopy feeds
the original-atlas smooth recognition theorem.

The candidate's topology and smooth atlas are independent inputs. The
conclusion is a genuine smooth diffeomorphism, not a transported atlas
or a merely topological equivalence. No classification hypothesis is used.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SixSphereThirteen

open StableSixSphereMaps SphereMapSuspension

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  (h : M ≃ₜ Sphere 6)

theorem third_suspension_nullhomotopic : (iterate (sphereMap h) 3).Nullhomotopic := by
  let f : StageMap 8 := iterate (sphereMap h) 3
  let g : StageMap 8 := QuaternionicHopf.southPairSmoothCollapseBasedMap.val
  have hg : ¬ g.Nullhomotopic := fun hg ↦
    QuaternionicHopf.southPairCollapse_not_finitely_nullhomotopic ⟨0, hg⟩
  have hstage : liftMap (show 5 ≤ 8 by decide) (sphereMap h) = f :=
    eq_of_heq (liftMap_add_heq 5 3 (sphereMap h))
  have hclass : ofMap f = ofMap (k := 5) (sphereMap h) := by
    rw [← hstage]
    exact ofMap_liftMap (by decide : 5 ≤ 8) (sphereMap h)
  have hfg : ¬ f.Homotopic g := fun H ↦
    sphereMapClass_ne_Hopf h (hclass.symm.trans (ofMap_homotopic H))
  exact Wikipedia.HopfProblem.DegreeCollapse.SixthStemMapDichotomy.nullhomotopic_of_not_homotopic
    8 (by decide) f g hg hfg

theorem stableClass_eq_one : stableClass h = 1 :=
  (stableClass_eq_one_iff h).mpr ⟨3, third_suspension_nullhomotopic h⟩

include h in
theorem nonempty_diffeomorph : Nonempty (M ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6) :=
  nonempty_diffeomorph_of_stableClass_eq_one h (stableClass_eq_one h)

end NoExoticSixSphere.SixSphereThirteen

namespace NoExoticSixSphere

universe u

/-- Every smooth manifold homeomorphic to the standard six-sphere is diffeomorphic to it. -/
theorem noExoticSixSpheres : SixSphereRigidity.{u} := by
  intro M _ _ _ ⟨h⟩
  exact SixSphereThirteen.nonempty_diffeomorph h

/-- No independently supplied smooth six-dimensional atlas defines an exotic six-sphere. -/
theorem not_isExoticSixSphere (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M] :
    ¬ IsExoticSphere 6 M :=
  sixSphereRigidity_iff_no_exotic.mp noExoticSixSpheres M
    inferInstance inferInstance inferInstance

end NoExoticSixSphere
