import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSquare

/-!
# The original attaching map traces the meridian commutator

The four oriented clock edges give the two original ordered meridians,
followed by their reversals. The equality is of actual paths, jointly
continuous in the remaining cube coordinates. No identification of
the source sphere generator is inferred from this perimeter formula.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

def perimeter : Path corner00 corner00 :=
  ((bottom.trans right).trans top.symm).trans left.symm

def atParameter (n : ℕ) (v : Parameter n) : C(ClockBoundary, Sphere (n + 1)) :=
  (attaching n).comp ⟨fun t ↦ (t, v), continuous_id.prodMk continuous_const⟩

theorem atParameter_corner00 (n : ℕ) (v : Parameter n) :
    atParameter n v corner00 = spherePole (n + 1) :=
  (attaching_bottom n v 0).trans (CubicalSphereSuspension.evaluation_zero n _)

theorem atParameter_corner10 (n : ℕ) (v : Parameter n) :
    atParameter n v corner10 = spherePole (n + 1) :=
  (attaching_bottom n v 1).trans (CubicalSphereSuspension.evaluation_one n _)

theorem atParameter_corner11 (n : ℕ) (v : Parameter n) :
    atParameter n v corner11 = spherePole (n + 1) :=
  (attaching_right n v 1).trans (CubicalSphereSuspension.evaluation_one n _)

theorem atParameter_corner01 (n : ℕ) (v : Parameter n) :
    atParameter n v corner01 = spherePole (n + 1) :=
  (attaching_left n v 1).trans (CubicalSphereSuspension.evaluation_one n _)

def orderedMeridian (n : ℕ) (x : Sphere n) :
    Path (spherePole (n + 1)) (spherePole (n + 1)) where
  toFun t := CubicalSphereSuspension.evaluation n (t, x)
  continuous_toFun := (CubicalSphereSuspension.evaluation n).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := CubicalSphereSuspension.evaluation_zero n x
  target' := CubicalSphereSuspension.evaluation_one n x

theorem orderedMeridian_reorder (n : ℕ) (x : Sphere n) (t : I) :
    orderedMeridian n x t = SuspensionCoordinates.reorder n (unitLoop n x t) :=
  CubicalSphereSuspension.evaluation_reorder n (t, x)

theorem continuous_orderedMeridian (n : ℕ) : Continuous (orderedMeridian n) :=
  Path.continuous_uncurry_iff.mp
    ((CubicalSphereSuspension.evaluation n).continuous.comp continuous_swap)

theorem map_bottom (n : ℕ) (v : Parameter n) :
    (bottom.map (atParameter n v).continuous).cast
      (atParameter_corner00 n v).symm (atParameter_corner10 n v).symm =
        orderedMeridian n (SmoothCube.quotient n (v 0)) := by
  apply Path.ext
  funext t
  exact attaching_bottom n v t

theorem map_right (n : ℕ) (v : Parameter n) :
    (right.map (atParameter n v).continuous).cast
      (atParameter_corner10 n v).symm (atParameter_corner11 n v).symm =
        orderedMeridian n (SmoothCube.quotient n (v 1)) := by
  apply Path.ext
  funext t
  exact attaching_right n v t

theorem map_top (n : ℕ) (v : Parameter n) :
    (top.map (atParameter n v).continuous).cast
      (atParameter_corner01 n v).symm (atParameter_corner11 n v).symm =
        orderedMeridian n (SmoothCube.quotient n (v 0)) := by
  apply Path.ext
  funext t
  exact attaching_top n v t

theorem map_left (n : ℕ) (v : Parameter n) :
    (left.map (atParameter n v).continuous).cast
      (atParameter_corner00 n v).symm (atParameter_corner01 n v).symm =
        orderedMeridian n (SmoothCube.quotient n (v 1)) := by
  apply Path.ext
  funext t
  exact attaching_left n v t

def trace (n : ℕ) (v : Parameter n) : Path (spherePole (n + 1)) (spherePole (n + 1)) :=
  (perimeter.map (atParameter n v).continuous).cast
    (atParameter_corner00 n v).symm (atParameter_corner00 n v).symm

theorem trace_apply (n : ℕ) (v : Parameter n) (t : I) :
    trace n v t = CellBoundary.attaching (n + 1) (boundaryMap n (perimeter t, v)) := rfl

theorem trace_commutator (n : ℕ) (v : Parameter n) :
    trace n v =
      (((orderedMeridian n (SmoothCube.quotient n (v 0))).trans
        (orderedMeridian n (SmoothCube.quotient n (v 1)))).trans
          (orderedMeridian n (SmoothCube.quotient n (v 0))).symm).trans
            (orderedMeridian n (SmoothCube.quotient n (v 1))).symm := by
  unfold trace perimeter
  rw [Path.map_trans, Path.map_trans, Path.map_trans]
  rw [Path.cast_trans _ _ _ (atParameter_corner01 n v).symm,
    Path.cast_trans _ _ _ (atParameter_corner11 n v).symm,
    Path.cast_trans _ _ _ (atParameter_corner10 n v).symm]
  rw [← Path.map_symm, ← Path.map_symm, Path.cast_symm, Path.cast_symm,
    map_bottom, map_right, map_top, map_left]

theorem continuous_trace (n : ℕ) : Continuous (trace n) := by
  apply Path.continuous_uncurry_iff.mp
  exact (attaching n).continuous.comp
    ((perimeter.continuous.comp continuous_snd).prodMk continuous_fst)

def traceMap (n : ℕ) : C(Parameter n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  ⟨trace n, continuous_trace n⟩

end NoExoticSixSphere.JamesSphere.AttachingSquare
