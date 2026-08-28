import Wikipedia.NoExoticSixSphere.JamesSphereAttachingTrackCoordinates
import Wikipedia.NoExoticSixSphere.JamesSphereAttachingCommutatorHomotopy

/-!
# The actual source correction as a continuous family of based loops

Throughout the source homotopy the clock perimeter starts and ends in
the zero-clock face, whose attaching image stays at the pole. Thus the
entire correction is a continuous native loop family. At its endpoint
the tail boundary is constant. Uncurrying that endpoint cube gives
exactly the previously constructed source-sphere attaching map.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

def perimeterBoundary (n : ℕ) : C(I × Parameter n, fullBoundary n) :=
  ⟨fun p ↦ ⟨((perimeter p.1).val, p.2), Or.inl (perimeter p.1).property⟩,
    (((continuous_subtype_val.comp perimeter.continuous).comp continuous_fst).prodMk
      continuous_snd).subtype_mk _⟩

def loopCorrection (n : ℕ) (s : I) (v : Parameter n) :
    Path (spherePole (n + 1)) (spherePole (n + 1)) where
  toFun t := fullAttaching n (sourceExtension n (s, perimeterBoundary n (t, v)))
  continuous_toFun := (fullAttaching n).continuous.comp
    ((sourceExtension n).continuous.comp (continuous_const.prodMk
      ((perimeterBoundary n).continuous.comp (continuous_id.prodMk continuous_const))))
  source' := by
    apply sourceAttachingTrack_zero_clocks
    change (perimeter 0).val = 0
    rw [perimeter.source]
    exact corner00_val
  target' := by
    apply sourceAttachingTrack_zero_clocks
    change (perimeter 1).val = 0
    rw [perimeter.target]
    exact corner00_val

theorem continuous_loopCorrection (n : ℕ) :
    Continuous (fun p : I × Parameter n ↦ loopCorrection n p.1 p.2) := by
  apply Path.continuous_uncurry_iff.mp
  exact (fullAttaching n).continuous.comp ((sourceExtension n).continuous.comp
    ((continuous_fst.comp continuous_fst).prodMk ((perimeterBoundary n).continuous.comp
      (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))))

def loopCorrectionMap (n : ℕ) :
    C(I × Parameter n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  ⟨fun p ↦ loopCorrection n p.1 p.2, continuous_loopCorrection n⟩

theorem loopCorrection_zero (n : ℕ) (v : Parameter n) : loopCorrection n 0 v = trace n v := by
  apply Path.ext
  funext t
  change fullAttaching n (sourceExtension n (0, perimeterBoundary n (t, v))) = _
  rw [sourceExtension_zero]
  rfl

theorem loopCorrection_respects (n : ℕ) (s : I) (v w : Parameter n)
    (h : sphereParameters n v = sphereParameters n w) :
    loopCorrection n s v = loopCorrection n s w := by
  apply Path.ext
  funext t
  apply sourceAttachingTrack_respects
  · rfl
  · intro i
    exact congrFun h i

theorem loopCorrection_poles (n : ℕ) (s : I) (v : Parameter n) (hv : v ∈ baseParameters n) :
    loopCorrection n s v = Path.refl (spherePole (n + 1)) := by
  apply Path.ext
  funext t
  exact sourceAttachingTrack_poles n s (perimeterBoundary n (t, v)) hv

theorem loopCorrection_one_boundary (n : ℕ) (v : Parameter n)
    (hv : v ∈ tailBoundary n) : loopCorrection n 1 v = Path.refl (spherePole (n + 1)) := by
  apply Path.ext
  funext t
  exact sourceAttaching_constant n (perimeterBoundary n (t, v)) (Or.inr hv)

def correctedCube (n : ℕ) :
    GenLoop (Fin (2 * n)) (Path (spherePole (n + 1)) (spherePole (n + 1)))
      (Path.refl (spherePole (n + 1))) :=
  ⟨(loopCorrectionMap n).comp ⟨fun u ↦ (1, (tailCoordinates n).symm u),
      continuous_const.prodMk (tailCoordinates n).symm.continuous⟩, by
    intro u hu
    apply loopCorrection_one_boundary
    apply (tailCoordinates_boundary n _).mpr
    change tailCoordinates n ((tailCoordinates n).symm u) ∈ Cube.boundary (Fin (2 * n))
    rwa [Homeomorph.apply_symm_apply]⟩

theorem correctedCube_uncurry_apply (n : ℕ) (u : Fin (2 * n + 1) → I) :
    GeneralizedLoopCurrying.uncurry (correctedCube n) u =
      sourceSphereAttaching n (SmoothCube.quotient (2 * n + 1) u) :=
  (sourceSphereAttaching_quotient n u).symm

theorem correctedCube_uncurry (n : ℕ) :
    GeneralizedLoopCurrying.uncurry (correctedCube n) =
      SmoothCube.toGenLoop ⟨sourceSphereAttaching n, sourceSphereAttaching_pole n⟩ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  exact correctedCube_uncurry_apply n

end NoExoticSixSphere.JamesSphere.AttachingSquare
