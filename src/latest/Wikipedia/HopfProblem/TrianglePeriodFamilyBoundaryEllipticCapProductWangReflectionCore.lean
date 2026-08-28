import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryWangComponents

/-!
# The actual two-arc cover under mapping-torus time reflection

A literal representative formula for a continuous map of mapping tori
determines its maps of the two actual open arcs. Time reflection preserves
each arc but exchanges the two components of their intersection. Moving a
negative representative into the first arc changes its fibre coordinate
by the inverse target monodromy.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open SingularMayerVietoris MappingTorus MappingTorus.HomologyCover

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X ≃ₜ X) (g : Y ≃ₜ Y) (F : C(Torus f, Torus g))
  (G : ℝ → C(X, Y))
  (hF : ∀ (t : ℝ) (x : X), F (mk f (t, x)) = mk g (-t, G t x))

include hF

/-- Reflection, written in the first actual interval chart. -/
theorem reflection_mk_shifted (t : ℝ) (x : X) :
    F (mk f (t, x)) = mk g (1 - t, g.symm (G t x)) := by
  rw [hF]
  calc
    mk g (-t, G t x) = mk g (-t + 1, g.symm (G t x)) := by
      rw [mk_add_one, Homeomorph.apply_symm_apply]
    _ = mk g (1 - t, g.symm (G t x)) :=
      congrArg (fun s : ℝ => mk g (s, g.symm (G t x))) (by ring)

/-- The reflected map carries the actual first open arc into the first open arc. -/
theorem reflection_mapsTo_U : Set.MapsTo F (U f) (U g) := by
  intro q hq
  let p := chartU f ⟨q, hq⟩
  let t : Set.Ioo (0 : ℝ) 1 :=
    ⟨1 - (p.1 : ℝ), by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩
  have he : F q = ((chartU g).symm (t, g.symm (G p.1 p.2)) : Torus g) := by
    rw [chartU_symm_coe]
    exact (congrArg F (chartU_representation f ⟨q, hq⟩)).symm.trans
      (reflection_mk_shifted f g F G hF p.1 p.2)
  rw [he]
  exact ((chartU g).symm (t, g.symm (G p.1 p.2))).property

/-- The reflected map carries the actual second open arc into the second open arc. -/
theorem reflection_mapsTo_V : Set.MapsTo F (V f) (V g) := by
  intro q hq
  let p := chartV f ⟨q, hq⟩
  let t : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨-(p.1 : ℝ), by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩
  have he : F q = ((chartV g).symm (t, G p.1 p.2) : Torus g) := by
    rw [chartV_symm_coe]
    exact (congrArg F (chartV_representation f ⟨q, hq⟩)).symm.trans (hF p.1 p.2)
  rw [he]
  exact ((chartV g).symm (t, G p.1 p.2)).property

/-- The literal restriction to the intersections of the actual two-arc covers. -/
def reflectionIntersectionMap : C((U f ∩ V f : Set (Torus f)),
    (U g ∩ V g : Set (Torus g))) :=
  intersectionRestriction F (U f) (V f) (U g) (V g)
    (reflection_mapsTo_U f g F G hF) (reflection_mapsTo_V f g F G hF)

@[simp] theorem reflectionIntersectionMap_coe (q : (U f ∩ V f : Set (Torus f))) :
    (reflectionIntersectionMap f g F G hF q).val = F q.val := rfl

/-- The lower quarter fibre maps into the upper target component, with the
actual inverse-monodromy change of coordinates. -/
theorem reflectionIntersectionMap_lower :
    (reflectionIntersectionMap f g F G hF).comp (lowerComponentFibre f) =
      (upperComponentFibre g).comp ((g.symm : C(Y, Y)).comp (G (1 / 4))) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change F (lowerComponentFibre f x).val =
    (upperComponentFibre g (g.symm (G (1 / 4) x))).val
  rw [lowerComponentFibre_coe, upperComponentFibre_coe]
  convert reflection_mk_shifted f g F G hF (1 / 4) x using 1; norm_num

/-- The upper quarter fibre maps into the lower target component, with the
same inverse-monodromy change of coordinates. -/
theorem reflectionIntersectionMap_upper :
    (reflectionIntersectionMap f g F G hF).comp (upperComponentFibre f) =
      (lowerComponentFibre g).comp ((g.symm : C(Y, Y)).comp (G (3 / 4))) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change F (upperComponentFibre f x).val =
    (lowerComponentFibre g (g.symm (G (3 / 4) x))).val
  rw [upperComponentFibre_coe, lowerComponentFibre_coe]
  convert reflection_mk_shifted f g F G hF (3 / 4) x using 1; norm_num

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct
