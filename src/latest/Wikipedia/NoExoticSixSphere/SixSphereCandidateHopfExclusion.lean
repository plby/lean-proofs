import Wikipedia.NoExoticSixSphere.QuaternionicHopfSphereFiberSeparation
import Wikipedia.NoExoticSixSphere.SixSphereStableRecognition

/-!
# A candidate's actual stable collapse class is not the original Hopf-product class

The candidate's actual collapse is S13 to S7. Three suspensions put its
smooth representative in the same S16 to S10 stage as the retained
Hopf-product collapse. The candidate's original native fiber survives
compactification and all three suspensions. Target-value alignment and
the checked original Arf-one obstruction exclude equality of these two
actual stable map classes.

This is the candidate-specific exclusion, not generation of the sixth
stem. The final theorem below states the remaining generation input
explicitly and does not postulate it.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SixSphereThirteen

open StableSixSphereMaps SphereMapSuspension

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  (h : M ≃ₜ Sphere 6)

theorem sphereMapClass_ne_Hopf :
    ofMap (k := 5) (sphereMap h) ≠
      ofMap (k := 8) QuaternionicHopf.southPairSmoothCollapseBasedMap.val := by
  let : CompactSpace M := compactSpace_of_homeomorph h
  let : T2Space M := t2Space_of_homeomorph h
  let : Nonempty M := h.toEquiv.nonempty
  obtain ⟨g, hg, H, hfiber, hregg, _⟩ := (collapseData h).exists_smoothSphereMap_regular
  have hd : (embedding h).ambientDimension = (embedding h).ambientDimension - 6 + 6 := by
    rw [embedding_dimension]
  let := regularFiberAtlas g hg (sphereZero ((embedding h).ambientDimension - 6))
    hregg 6 (by simpa using hd)
  let D := (embedding h).diffeomorphToCompactifiedFiber g hg hregg hd hfiber
  let g₀ : StageMap 5 := g
  have hg₀ : ContMDiff (𝓡 13) (𝓡 7) ∞ g₀ := hg
  have hreg₀ : ∀ x, g₀ x = sphereZero 7 → Surjective (mfderiv (𝓡 13) (𝓡 7) g₀ x) := hregg
  have H₀ : (sphereMap h).Homotopic g₀ := H
  let := regularFiberAtlas g₀ hg₀ (sphereZero 7) hreg₀ 6
    (by simp only [finrank_euclideanSpace_fin])
  have hX₀ : {x : Sphere 13 // g₀ x = sphereZero 7} ≃ₜ Sphere 6 :=
    D.symm.toHomeomorph.trans h
  obtain ⟨G, hG, hregG, HG, E, _⟩ :=
    exists_smooth_iterate_with_fiber g₀ hg₀ (sphereZero 7) hreg₀ 6 (by decide) 3
  let := regularFiberAtlas G hG (equators 7 3 (sphereZero 7)) hregG 6
    (by simp only [finrank_euclideanSpace_fin])
  have hX : {x : Sphere 16 // G x = equators 7 3 (sphereZero 7)} ≃ₜ Sphere 6 :=
    E.symm.toHomeomorph.trans hX₀
  have hstage : liftMap (show 5 ≤ 8 by decide) g₀ = iterate g₀ 3 :=
    eq_of_heq (liftMap_add_heq 5 3 g₀)
  have hclass : ofMap (k := 8) G = ofMap (k := 5) (sphereMap h) := by
    calc
      ofMap G = ofMap (iterate g₀ 3) := (ofMap_homotopic HG).symm
      _ = ofMap g₀ := by
        rw [← hstage]
        exact ofMap_liftMap (by decide : 5 ≤ 8) g₀
      _ = ofMap (sphereMap h) := (ofMap_homotopic H₀).symm
  have hsep := QuaternionicHopf.southPairStableMapClass_ne_regular_sixSphere
    G hG (equators 7 3 (sphereZero 7)) hregG hX
  intro he
  exact hsep (he.symm.trans hclass.symm)

end NoExoticSixSphere.SixSphereThirteen

namespace NoExoticSixSphere

universe u

theorem sixSphereRigidity_of_stableMap_dichotomy
    (hgen : ∀ c : StableSixSphereMaps.Class,
      c = StableSixSphereMaps.nullClass ∨
        c = StableSixSphereMaps.ofMap (k := 8)
          QuaternionicHopf.southPairSmoothCollapseBasedMap.val) : SixSphereRigidity.{u} := by
  intro M t a s ⟨h⟩
  have hz : StableSixSphereMaps.ofMap (k := 5) (SixSphereThirteen.sphereMap h) =
      StableSixSphereMaps.nullClass :=
    (hgen _).resolve_right (SixSphereThirteen.sphereMapClass_ne_Hopf h)
  apply SixSphereThirteen.nonempty_diffeomorph_of_stableClass_eq_one h
  exact (CubicalStableSix.ofNative_sphereClass_eq_one_iff (SixSphereThirteen.basedMap h)).mpr hz

end NoExoticSixSphere
