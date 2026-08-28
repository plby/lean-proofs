import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorAffine
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCover
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorExtension

/-!
# Constructed local affine μ sections on the actual triangle cover

Regular sheets and the actual cusp horodisc carry the zero seed.  The two
precisely invariant elliptic neighbourhoods carry `(2 - τ) / 3` and
`(1 - τ) / 2`.  Their stabilizer equations follow from the actual τ
covariance and the proved affine free-product cocycle.  Extension to each
whole saturation is then constructed, not included in the input.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

variable {τ : ℍ → ℍ} (hτ : TauCovariant τ)
  (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)

/-- The two explicit affine solutions at the elliptic centres. -/
def ellipticFormula (τ : ℍ → ℍ) : Elliptic.Kind → ℍ → ℂ
  | .three, z => (2 - (τ z : ℂ)) / 3
  | .four, z => (1 - (τ z : ℂ)) / 2

include hτa in
theorem ellipticFormula_holomorphic (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ellipticFormula τ j) := by
  have ht := UpperHalfPlane.contMDiff_coe.comp hτa
  cases j
  · exact (contMDiff_const.sub ht).div₀ contMDiff_const (fun _ => by norm_num)
  · exact (contMDiff_const.sub ht).div₀ contMDiff_const (fun _ => by norm_num)

theorem ellipticFormula_generator (j : Elliptic.Kind) (z : ℍ) :
    ellipticFormula τ j (triangleGeometricRepresentation (Triangle.ellipticGenerator j) z) =
      (cocycle hτ hτa).fibreMap (Triangle.ellipticGenerator j) z (ellipticFormula τ j z) := by
  cases j
  · change (2 - (τ (triangleGeometricRepresentation triangleGenerator₁ z) : ℂ)) / 3 = _
    dsimp only [Triangle.ellipticGenerator]
    rw [triangleGeometricRepresentation_generator₁_apply, hτ.1 z,
      cocycle_fibreMap_generator₁]
    dsimp only [ellipticFormula]
    field_simp [(τ z).ne_zero]
    ring
  · change (1 - (τ (triangleGeometricRepresentation triangleGenerator₂ z) : ℂ)) / 2 = _
    dsimp only [Triangle.ellipticGenerator]
    rw [triangleGeometricRepresentation_generator₂_apply, hτ.2 z,
      cocycle_fibreMap_generator₂]
    dsimp only [ellipticFormula]
    field_simp [(τ z).ne_zero]
    ring

def regularSeed (x : TriangleRegularQuotient) :
    (Cover.regularPatch x).Seed (cocycle hτ hτa) where
  toFun _ := 0
  holomorphic := contMDiffOn_const
  equivariant := by
    intro g z _
    have hg : (g : TriangleGroup) = 1 := Subgroup.mem_bot.mp g.property
    simp only [hg, AffineCocycle.fibreMap_one]

/-- The cusp seed satisfies the whole primitive cusp subgroup, not just
one translation, before extension to all other components. -/
def cuspSeed : Cover.cuspPatch.Seed (cocycle hτ hτa) where
  toFun _ := 0
  holomorphic := contMDiffOn_const
  equivariant := by
    intro g z _
    exact (cocycle hτ hτa).equivariant_of_mem_zpowers (fun _ => 0)
      triangleCuspGenerator (fun w => (cocycle_fibreMap_cusp hτ hτa w 0).symm)
      g.property z

def ellipticSeed (j : Elliptic.Kind) :
    (Cover.ellipticPatch j).Seed (cocycle hτ hτa) where
  toFun := ellipticFormula τ j
  holomorphic := (ellipticFormula_holomorphic hτa j).contMDiffOn
  equivariant := by
    intro g z _
    have hg : (g : TriangleGroup) ∈ Subgroup.zpowers (Triangle.ellipticGenerator j) := by
      rw [← Triangle.ellipticStabilizer_eq_zpowers]
      exact g.property
    exact (cocycle hτ hτa).equivariant_of_mem_zpowers (ellipticFormula τ j)
      (Triangle.ellipticGenerator j) (ellipticFormula_generator hτ hτa j) hg z

/-- A seed has been constructed on every member of the actual cover. -/
def seed : (i : Cover.Index) → (Cover.patch i).Seed (cocycle hτ hτa)
  | none => cuspSeed hτ hτa
  | some (.inl x) => regularSeed hτ hτa x
  | some (.inr j) => ellipticSeed hτ hτa j

/-- The actual full-saturation local section, obtained by affine extension. -/
def localSection (i : Cover.Index) : ℍ → ℂ := (seed hτ hτa i).extend

theorem localSection_holomorphic (i : Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localSection hτ hτa i) (Cover.patch i).saturation :=
  (seed hτ hτa i).extend_holomorphic

theorem localSection_equivariant (i : Cover.Index) :
    (cocycle hτ hτa).EquivariantOn (localSection hτ hτa i) (Cover.patch i).saturation :=
  (seed hτ hτa i).extend_equivariant

theorem localSection_cusp (z : ℍ) (hz : z ∈ Triangle.horodisc Triangle.width) :
    localSection hτ hτa Cover.cuspIndex z = 0 :=
  (cuspSeed hτ hτa).extend_eq z hz

theorem localSection_regular (x : TriangleRegularQuotient) (z : ℍ)
    (hz : z ∈ Cover.regularSheet x) :
    localSection hτ hτa (Cover.regularIndex x) z = 0 :=
  (regularSeed hτ hτa x).extend_eq z hz

theorem localSection_elliptic (j : Elliptic.Kind) (z : ℍ)
    (hz : z ∈ Triangle.ellipticNeighborhood j) :
    localSection hτ hτa (Cover.ellipticIndex j) z = ellipticFormula τ j z :=
  (ellipticSeed hτ hτa j).extend_eq z hz

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
