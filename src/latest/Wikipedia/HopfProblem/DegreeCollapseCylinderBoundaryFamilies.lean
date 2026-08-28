import Wikipedia.HopfProblem.DegreeCollapseCylinderBoundaryGluing

/-!
# Jointly continuous families on the complete cylinder boundary

Glue into the genuine compact-open mapping space of the outer interval,
then uncurry. This gives a two-parameter boundary family with every value
preserved, not merely a separate continuous map at each outer time.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.CylinderBoundaryFamilies

open DiskCylinder CylinderBall

variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace Y]
  (f g : C(I × Disk (E := V), Y)) (H : C(I × (I × Sphere (E := V)), Y))
  (h0 : ∀ t s, H (t, 0, s) = f (t, boundaryToDisk s))
  (h1 : ∀ t s, H (t, 1, s) = g (t, boundaryToDisk s))

def bottomFamily : C(Disk (E := V), C(I, Y)) := (f.comp ContinuousMap.prodSwap).curry

def topFamily : C(Disk (E := V), C(I, Y)) := (g.comp ContinuousMap.prodSwap).curry

def sideFamily : C(I × Sphere (E := V), C(I, Y)) := (H.comp ContinuousMap.prodSwap).curry

def glued : C(I × boundary (V := V), Y) :=
  (CylinderBoundary.glued (bottomFamily f) (topFamily g) (sideFamily H)
    (fun s => ContinuousMap.ext (fun t => h0 t s))
    (fun s => ContinuousMap.ext (fun t => h1 t s))).uncurry.comp ContinuousMap.prodSwap

theorem glued_bottom (t : I) (z : Disk (E := V)) :
    glued f g H h0 h1 (t, CylinderBoundary.lower (bottomMap z)) = f (t, z) :=
  ContinuousMap.congr_fun (CylinderBoundary.glued_bottom (bottomFamily f) (topFamily g)
    (sideFamily H) (fun s => ContinuousMap.ext (fun t => h0 t s))
    (fun s => ContinuousMap.ext (fun t => h1 t s)) z) t

theorem glued_top (t : I) (z : Disk (E := V)) :
    glued f g H h0 h1 (t, CylinderBoundary.top z) = g (t, z) :=
  ContinuousMap.congr_fun (CylinderBoundary.glued_top (bottomFamily f) (topFamily g)
    (sideFamily H) (fun s => ContinuousMap.ext (fun t => h0 t s))
    (fun s => ContinuousMap.ext (fun t => h1 t s)) z) t

theorem glued_side (t r : I) (s : Sphere (E := V)) :
    glued f g H h0 h1 (t, CylinderBoundary.lower (sideMap (r, s))) = H (t, r, s) :=
  ContinuousMap.congr_fun (CylinderBoundary.glued_side (bottomFamily f) (topFamily g)
    (sideFamily H) (fun s => ContinuousMap.ext (fun t => h0 t s))
    (fun s => ContinuousMap.ext (fun t => h1 t s)) r s) t

end Wikipedia.HopfProblem.DegreeCollapse.CylinderBoundaryFamilies
