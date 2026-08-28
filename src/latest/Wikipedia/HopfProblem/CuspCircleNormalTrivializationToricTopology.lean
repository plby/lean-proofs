import Wikipedia.HopfProblem.CuspCircleNormalTrivializationToricMap

/-!
# The genuine trivial normal neighborhood in the toric space

The union of the two original toric affine charts is identified with
the Riemann sphere times the real four-dimensional normal space.
The forward map is the explicit two-chart map, and its inverse formula
is proved on each unchanged toric inclusion.
-/

noncomputable section

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open ToricCharts ToricFan

/-- The exact original two-chart open neighborhood of the fixed middle curve. -/
def toricNeighborhood : Opens ToricSpace.Space :=
  ⟨range (ToricSpace.inclusion ToricSpace.referenceTriangle) ∪
      range (ToricSpace.inclusion (Triangle.upperNeighbour 1)),
    (ToricSpace.inclusion_openEmbedding _).isOpen_range.union
      (ToricSpace.inclusion_openEmbedding _).isOpen_range⟩

@[simp] theorem toricNeighborhood_coe :
    (toricNeighborhood : Set ToricSpace.Space) =
      range (ToricSpace.inclusion ToricSpace.referenceTriangle) ∪
        range (ToricSpace.inclusion (Triangle.upperNeighbour 1)) := rfl

theorem inclusion_mem_toricNeighborhood (b : Bool) (z : CoordinateSpace 3) :
    ToricSpace.inclusion (chartTriangle b) z ∈ toricNeighborhood := by
  cases b
  · exact Or.inl (mem_range_self z)
  · exact Or.inr (mem_range_self z)

/-- Either original toric inclusion, regarded as landing in that actual open set. -/
def toricInclusion (b : Bool) (z : CoordinateSpace 3) : toricNeighborhood :=
  ⟨ToricSpace.inclusion (chartTriangle b) z, inclusion_mem_toricNeighborhood b z⟩

@[simp] theorem toricInclusion_coe (b : Bool) (z : CoordinateSpace 3) :
    (toricInclusion b z : ToricSpace.Space) = ToricSpace.inclusion (chartTriangle b) z := rfl

/-- Each full normal-coordinate chart is an actual open embedding into the toric space. -/
theorem toricChartMap_isOpenEmbedding (b : Bool) : IsOpenEmbedding (toricChartMap b) :=
  (ToricSpace.inclusion_openEmbedding (chartTriangle b)).comp
    (chartCoordinates b).symm.toHomeomorph.isOpenEmbedding

theorem continuous_fromProduct : Continuous fromProduct := by
  apply continuous_of_comp_baseProductChart
  intro b
  rw [fromProduct_comp_baseProductChart]
  exact (toricChartMap_isOpenEmbedding b).continuous

theorem isOpenMap_fromProduct : IsOpenMap fromProduct := by
  apply isOpenMap_of_comp_baseProductChart
  intro b
  rw [fromProduct_comp_baseProductChart]
  exact (toricChartMap_isOpenEmbedding b).isOpenMap

/-- There are no missing chart points and no extra toric points in the product image. -/
theorem range_fromProduct : range fromProduct = (toricNeighborhood : Set ToricSpace.Space) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨b, q, rfl⟩ := baseProductChart_cover p
    rw [fromProduct_baseProductChart]
    exact inclusion_mem_toricNeighborhood b ((chartCoordinates b).symm q)
  · intro hx
    obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := hx
    · exact ⟨baseProductChart false (chartCoordinates false z),
        fromProduct_chartCoordinates false z⟩
    · exact ⟨baseProductChart true (chartCoordinates true z),
        fromProduct_chartCoordinates true z⟩

theorem fromProduct_mem_toricNeighborhood (p : RiemannSphere × Fibre) :
    fromProduct p ∈ toricNeighborhood := by
  change fromProduct p ∈ (toricNeighborhood : Set ToricSpace.Space)
  rw [← range_fromProduct]
  exact mem_range_self p

/-- The explicit global product map is an open embedding, not a quotient model. -/
theorem fromProduct_isOpenEmbedding : IsOpenEmbedding fromProduct :=
  .of_continuous_injective_isOpenMap continuous_fromProduct fromProduct_injective
    isOpenMap_fromProduct

/-- The genuine product homeomorphism onto the two original toric charts. -/
def toricNeighborhoodHomeomorph : (RiemannSphere × Fibre) ≃ₜ toricNeighborhood :=
  fromProduct_isOpenEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr range_fromProduct)

@[simp] theorem toricNeighborhoodHomeomorph_coe (p : RiemannSphere × Fibre) :
    (toricNeighborhoodHomeomorph p : ToricSpace.Space) = fromProduct p := rfl

/-- The literal forward formula in either affine base chart. -/
@[simp] theorem toricNeighborhoodHomeomorph_baseProductChart (b : Bool) (q : Model) :
    toricNeighborhoodHomeomorph (baseProductChart b q) =
      toricInclusion b ((chartCoordinates b).symm q) := by
  apply Subtype.ext
  exact fromProduct_baseProductChart b q

/-- The actual inverse homeomorphism on each unchanged toric affine inclusion. -/
@[simp] theorem toricNeighborhoodHomeomorph_symm_toricInclusion
    (b : Bool) (z : CoordinateSpace 3) :
    toricNeighborhoodHomeomorph.symm (toricInclusion b z) =
      baseProductChart b (chartCoordinates b z) := by
  apply toricNeighborhoodHomeomorph.injective
  rw [toricNeighborhoodHomeomorph.apply_symm_apply]
  apply Subtype.ext
  exact (fromProduct_chartCoordinates b z).symm

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
