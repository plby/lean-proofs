import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociated

/-!
# Analytic structure on the associated quotient

Both the base and the total space retain their quotient topologies. Their
complex atlases are the covering-quotient atlases; the total quotient map
and the line-bundle projection are holomorphic in these atlases.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle

variable {G A B E : Type*} [Group G] [MulAction G A]
  [TopologicalSpace A] [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E A]
  {q : A → B} (hq : IsQuotientCoveringMap q G) (χ : G →* ℂˣ)

local notation "IA" => modelWithCornersSelf ℂ E
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ (E × ℂ)

local instance associatedProductChartedSpace : ChartedSpace (E × ℂ) (A × ℂ) :=
  inferInstanceAs (ChartedSpace (ModelProd E ℂ) (A × ℂ))

/-- The usual complex quotient atlas of the diagonal covering action. -/
@[instance_reducible] def associatedChartedSpace :
    ChartedSpace (E × ℂ) (AssociatedSpace (A := A) χ) :=
  letI := diagonalAction (A := A) χ
  CoveringQuotient.chartedSpace (E := E × ℂ)
    (associatedMap_isQuotientCoveringMap hq χ)

variable [IsManifold (modelWithCornersSelf ℂ E) ω A]
  (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ E) ω (fun a : A => g • a))

local instance associatedProductManifold : IsManifold I₂ ω (A × ℂ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := IA) (I' := I₁) A ℂ

include hG

theorem diagonalAction_holomorphic (g : G) :
    ContMDiff I₂ I₂ ω (fun p : A × ℂ => (g • p.1, (χ g : ℂ) * p.2)) := by
  rw [modelWithCornersSelf_prod]
  exact ((hG g).comp contMDiff_fst).prodMk
    ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_snd)

theorem associatedSpace_isManifold :
    letI := associatedChartedSpace (E := E) hq χ
    IsManifold I₂ ω (AssociatedSpace (A := A) χ) := by
  letI := diagonalAction (A := A) χ
  exact CoveringQuotient.isManifold
    (associatedMap_isQuotientCoveringMap hq χ) ω (diagonalAction_holomorphic χ hG)

theorem associatedMap_holomorphic :
    letI := associatedChartedSpace (E := E) hq χ
    ContMDiff I₂ I₂ ω (associatedMap (A := A) χ) := by
  letI := diagonalAction (A := A) χ
  exact CoveringQuotient.contMDiff_project
    (associatedMap_isQuotientCoveringMap hq χ) ω (diagonalAction_holomorphic χ hG)

theorem projection_holomorphic :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    letI := associatedChartedSpace (E := E) hq χ
    ContMDiff I₂ IA ω (projection hq χ) := by
  letI := CoveringQuotient.chartedSpace (E := E) hq
  letI := diagonalAction (A := A) χ
  apply CoveringQuotient.contMDiff_of_comp
    (associatedMap_isQuotientCoveringMap hq χ) IA ω
  rw [modelWithCornersSelf_prod]
  exact (CoveringQuotient.contMDiff_project hq ω hG).comp contMDiff_fst

theorem associatedLocalInverse_holomorphic (p : A × ℂ) :
    letI := associatedChartedSpace (E := E) hq χ
    letI := diagonalAction (A := A) χ
    ContMDiffOn I₂ I₂ ω
      (CoveringQuotient.localInverse (associatedMap_isQuotientCoveringMap hq χ) p)
      (CoveringQuotient.localInverse (associatedMap_isQuotientCoveringMap hq χ) p).source := by
  letI := diagonalAction (A := A) χ
  exact CoveringQuotient.localInverse_holomorphic
    (associatedMap_isQuotientCoveringMap hq χ) ω (diagonalAction_holomorphic χ hG) p

end Wikipedia.HopfProblem.HolomorphicCharacterBundle
