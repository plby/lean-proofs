import Wikipedia.HopfProblem.SheafSingularCupComparisonBicosimplicialAdditive
import Wikipedia.HopfProblem.SheafSingularCupComparisonRingSheaf

/-!
# The actual Godement--singular double complex

The term in bidegree `(p,q)` is the original `(p+1)`st multiplicative
Godement iterate of the actual ring sheaf of singular `q`-cochains.
Horizontal faces are images of the original simplex faces. Vertical
faces are the original insertions of the section-to-germs unit.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf

open SheafCupProduct

variable (X : TopCat.{0})

/-- The genuine low-degree double diagram of ring sheaves. -/
def diagram : Bicosimplicial.Data X where
  R00 := GodementRing.term0 (RingCochains.sheaf X 0)
  R10 := GodementRing.term1 (RingCochains.sheaf X 0)
  R01 := GodementRing.term0 (RingCochains.sheaf X 1)
  R20 := GodementRing.term2 (RingCochains.sheaf X 0)
  R11 := GodementRing.term1 (RingCochains.sheaf X 1)
  R02 := GodementRing.term0 (RingCochains.sheaf X 2)
  R30 := GodementRing.term3 (RingCochains.sheaf X 0)
  R21 := GodementRing.term2 (RingCochains.sheaf X 1)
  R12 := GodementRing.term1 (RingCochains.sheaf X 2)
  R03 := GodementRing.term0 (RingCochains.sheaf X 3)
  v00 := GodementRing.face0 (RingCochains.sheaf X 0)
  h00 i := GodementRing.term0Map (RingCochains.coface X 0 i)
  v10 := GodementRing.face1 (RingCochains.sheaf X 0)
  h10 i := GodementRing.term1Map (RingCochains.coface X 0 i)
  v01 := GodementRing.face0 (RingCochains.sheaf X 1)
  h01 i := GodementRing.term0Map (RingCochains.coface X 1 i)
  v20 := GodementRing.face2 (RingCochains.sheaf X 0)
  h20 i := GodementRing.term2Map (RingCochains.coface X 0 i)
  v11 := GodementRing.face1 (RingCochains.sheaf X 1)
  h11 i := GodementRing.term1Map (RingCochains.coface X 1 i)
  v02 := GodementRing.face0 (RingCochains.sheaf X 2)
  h02 i := GodementRing.term0Map (RingCochains.coface X 2 i)
  cofaceV00 := GodementRing.face01 (RingCochains.sheaf X 0)
  cofaceV10 := GodementRing.face12 (RingCochains.sheaf X 0)
  cofaceV01 := GodementRing.face01 (RingCochains.sheaf X 1)
  cofaceH00 i j hij := GodementRing.map_composition_eq _ _ _ _
    (RingCochains.coface_comp X 0 i j hij)
  cofaceH01 i j hij := GodementRing.map_composition_eq _ _ _ _
    (RingCochains.coface_comp X 1 i j hij)
  cofaceH10 i j hij := GodementRing.map_composition_eq _ _ _ _
    (GodementRing.map_composition_eq _ _ _ _ (RingCochains.coface_comp X 0 i j hij))
  mixed00 i j := (GodementRing.face0_naturality (RingCochains.coface X 0 j) i).symm
  mixed10 i j := (GodementRing.face1_naturality (RingCochains.coface X 0 j) i).symm
  mixed01 i j := (GodementRing.face0_naturality (RingCochains.coface X 1 j) i).symm

/-- The original additive-sheaf double diagram. -/
abbrev categoryData := (diagram X).categoryData

/-- The original global-section ring diagram, with actual mixed faces. -/
abbrev globalData := (diagram X).globalData

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf
