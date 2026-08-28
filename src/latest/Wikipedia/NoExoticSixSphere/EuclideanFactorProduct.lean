import Wikipedia.NoExoticSixSphere.OnePointProductCoordinates
import Wikipedia.NoExoticSixSphere.ProductSphereSuspensionComparison

/-!
# Several genuine Euclidean product factors in the original compactification

The direct product by a Euclidean q-space agrees, after explicit coordinate
homeomorphisms, with successive products by the real line. The identities
retain the original based map on the whole compactification.
-/

noncomputable section

open scoped OnePoint

namespace NoExoticSixSphere.EuclideanFactorProduct

open OnePointProduct

abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)

def productCoordinates (n q : ℕ) : (V n × V q) ≃ₜ V (n + q) :=
  EuclideanSpace.finAddEquivProd.symm.toHomeomorph

def lineCoordinates (n : ℕ) : (V n × ℝ) ≃ₜ V (n + 1) :=
  (Homeomorph.prodComm (V n) ℝ).trans
    (Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates n).toHomeomorph

def compactMap {m n : ℕ} (f : C(OnePoint (V m), OnePoint (V n))) (hf : f ∞ = ∞)
    (q : ℕ) : C(OnePoint (V (m + q)), OnePoint (V (n + q))) :=
  (productCoordinates n q).onePointCongr.toHomotopyEquiv.toFun.comp
    ((addFactor f hf (V q)).comp
      (productCoordinates m q).onePointCongr.symm.toHomotopyEquiv.toFun)

theorem compactMap_infty {m n : ℕ} (f : C(OnePoint (V m), OnePoint (V n)))
    (hf : f ∞ = ∞) (q : ℕ) : compactMap f hf q ∞ = ∞ := by
  change (productCoordinates n q).onePointCongr (addFactor f hf (V q) ∞) = ∞
  exact congrArg (productCoordinates n q).onePointCongr (addFactor_infty f hf)

theorem compactMap_apply {m n : ℕ} (f : C(OnePoint (V m), OnePoint (V n)))
    (hf : f ∞ = ∞) (q : ℕ) (z : OnePoint (V m × V q)) :
    compactMap f hf q ((productCoordinates m q).onePointCongr z) =
      (productCoordinates n q).onePointCongr (addFactor f hf (V q) z) := by
  change (productCoordinates n q).onePointCongr
    (addFactor f hf (V q) ((productCoordinates m q).onePointCongr.symm
      ((productCoordinates m q).onePointCongr z))) = _
  rw [Homeomorph.symm_apply_apply]

theorem compactMap_map {m n : ℕ} (f : C(OnePoint (V m), OnePoint (V n)))
    (hf : f ∞ = ∞) (q : ℕ) (x : OnePoint (V m)) (v : OnePoint (V q)) :
    compactMap f hf q ((productCoordinates m q).onePointCongr (map (x, v))) =
      (productCoordinates n q).onePointCongr (map (f x, v)) := by
  rw [compactMap_apply, addFactor_map]

def zeroCoordinates (m : ℕ) : V (m + 0) ≃ₜ V m :=
  (productCoordinates m 0).symm.trans (Homeomorph.prodUnique (V m) (V 0))

theorem zero_square {m n : ℕ} (f : C(OnePoint (V m), OnePoint (V n)))
    (hf : f ∞ = ∞) (x : OnePoint (V (m + 0))) :
    (zeroCoordinates n).onePointCongr (compactMap f hf 0 x) =
      f ((zeroCoordinates m).onePointCongr x) := by
  obtain ⟨z, rfl⟩ := (productCoordinates m 0).onePointCongr.surjective x
  rw [compactMap_apply, zeroCoordinates, zeroCoordinates,
    onePoint_trans_apply, onePoint_trans_apply]
  change (Homeomorph.prodUnique (V n) (V 0)).onePointCongr
    ((productCoordinates n 0).onePointCongr.symm
      ((productCoordinates n 0).onePointCongr (addFactor f hf (V 0) z))) =
    f ((Homeomorph.prodUnique (V m) (V 0)).onePointCongr
      ((productCoordinates m 0).onePointCongr.symm
        ((productCoordinates m 0).onePointCongr z)))
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
  exact addFactor_unique f hf z

def stepCoordinates (m q : ℕ) : (V (m + q) × ℝ) ≃ₜ V (m + (q + 1)) :=
  ((((productCoordinates m q).symm.prodCongr (Homeomorph.refl ℝ)).trans
    (Homeomorph.prodAssoc (V m) (V q) ℝ)).trans
      ((Homeomorph.refl (V m)).prodCongr (lineCoordinates q))).trans
        (productCoordinates m (q + 1))

theorem stepCoordinates_map (m q : ℕ)
    (x : OnePoint (V m)) (v : OnePoint (V q)) (t : OnePoint ℝ) :
    (stepCoordinates m q).onePointCongr
      (map ((productCoordinates m q).onePointCongr (map (x, v)), t)) =
    (productCoordinates m (q + 1)).onePointCongr
      (map (x, (lineCoordinates q).onePointCongr (map (v, t)))) := by
  simp only [stepCoordinates, onePoint_trans_apply, map_prodCongr, onePoint_refl]
  change (productCoordinates m (q + 1)).onePointCongr
    (((Homeomorph.refl (V m)).prodCongr (lineCoordinates q)).onePointCongr
      ((Homeomorph.prodAssoc (V m) (V q) ℝ).onePointCongr
        (map ((productCoordinates m q).onePointCongr.symm
          ((productCoordinates m q).onePointCongr (map (x, v))), t)))) = _
  rw [Homeomorph.symm_apply_apply, map_assoc, map_prodCongr, onePoint_refl]

theorem step_square {m n : ℕ} (f : C(OnePoint (V m), OnePoint (V n)))
    (hf : f ∞ = ∞) (q : ℕ) (z : OnePoint (V (m + q) × ℝ)) :
    (stepCoordinates n q).onePointCongr
      (addFactor (compactMap f hf q) (compactMap_infty f hf q) ℝ z) =
    compactMap f hf (q + 1) ((stepCoordinates m q).onePointCongr z) := by
  obtain ⟨⟨x, t⟩, rfl⟩ := map_surjective z
  obtain ⟨p, rfl⟩ := (productCoordinates m q).onePointCongr.surjective x
  obtain ⟨⟨u, v⟩, rfl⟩ := map_surjective p
  rw [addFactor_map, compactMap_map, stepCoordinates_map, stepCoordinates_map, compactMap_map]

end NoExoticSixSphere.EuclideanFactorProduct
