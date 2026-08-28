import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorData
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCover
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorExtension

/-!
# Constructed beta sections on the actual quotient-cover patches

The returning subgroup of a regular sheet is trivial, so zero is a seed.
The two explicit elliptic primitives satisfy all returning-subgroup laws by
cyclic covariance.  The cusp seed is `-tau`.  Extension from each precisely
invariant sheet constructs an actual holomorphic section on its full triangle
saturation, with the all-word additive law and exact original-sheet formulas.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

open MuTorsor

namespace Data

variable (D : Data)

/-- The actual primitive for the selected elliptic generator. -/
def ellipticPrimitive : Elliptic.Kind → ℍ → ℂ
  | .three => primitiveOne D.tau D.mu
  | .four => primitiveTwo D.tau D.mu

theorem ellipticPrimitive_holomorphic (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.ellipticPrimitive j) := by
  cases j
  · exact primitiveOne_holomorphic D.tau_holomorphic D.mu_holomorphic
  · exact primitiveTwo_holomorphic D.tau_holomorphic D.mu_holomorphic

theorem ellipticPrimitive_generator (j : Elliptic.Kind) (z : ℍ) :
    D.ellipticPrimitive j (triangleGeometricRepresentation (Triangle.ellipticGenerator j) z) =
      D.ellipticPrimitive j z + D.shift (Triangle.ellipticGenerator j) z := by
  cases j
  · change primitiveOne D.tau D.mu (triangleGeometricRepresentation triangleGenerator₁ z) =
      primitiveOne D.tau D.mu z + D.shift triangleGenerator₁ z
    rw [triangleGeometricRepresentation_generator₁_apply, D.shift_generator₁]
    exact sub_eq_iff_eq_add'.mp (primitiveOne_difference D.tau_covariant D.mu_one z)
  · change primitiveTwo D.tau D.mu (triangleGeometricRepresentation triangleGenerator₂ z) =
      primitiveTwo D.tau D.mu z + D.shift triangleGenerator₂ z
    rw [triangleGeometricRepresentation_generator₂_apply, D.shift_generator₂]
    exact sub_eq_iff_eq_add'.mp (primitiveTwo_difference D.tau_covariant D.mu_two z)

/-- The generator identity proves every actual elliptic returning-group law. -/
theorem ellipticPrimitive_additive (j : Elliptic.Kind) {g : TriangleGroup}
    (hg : g ∈ Triangle.ellipticStabilizer j) (z : ℍ) :
    D.ellipticPrimitive j (triangleGeometricRepresentation g z) =
      D.ellipticPrimitive j z + D.shift g z := by
  apply D.covariance_zpowers (D.ellipticPrimitive j) (Triangle.ellipticGenerator j)
    (D.ellipticPrimitive_generator j)
  simpa only [Triangle.ellipticStabilizer_eq_zpowers] using hg

theorem cuspPrimitive_generator (z : ℍ) :
    cuspPrimitive D.tau (triangleGeometricRepresentation triangleCuspGenerator z) =
      cuspPrimitive D.tau z + D.shift triangleCuspGenerator z := by
  rw [D.shift_cusp]
  exact sub_eq_iff_eq_add'.mp (cuspPrimitive_difference D.tau_covariant z)

/-- The cusp primitive satisfies the entire actual cusp returning subgroup. -/
theorem cuspPrimitive_additive {g : TriangleGroup}
    (hg : g ∈ Subgroup.zpowers triangleCuspGenerator) (z : ℍ) :
    cuspPrimitive D.tau (triangleGeometricRepresentation g z) =
      cuspPrimitive D.tau z + D.shift g z :=
  D.covariance_zpowers (cuspPrimitive D.tau) triangleCuspGenerator
    D.cuspPrimitive_generator hg z

/-- On a genuine regular covering sheet, zero is an actual seed. -/
def regularSeed (x : TriangleRegularQuotient) : (Cover.regularPatch x).Seed D.cocycle where
  toFun _ := 0
  holomorphic := contMDiffOn_const
  equivariant := by
    intro g z _
    have hg : (g : TriangleGroup) = 1 := Subgroup.mem_bot.mp g.property
    rw [hg, D.cocycle.fibreMap_one]

/-- The actual finite-average elliptic primitive, with every returning-group
equation proved rather than supplied as seed data. -/
def ellipticSeed (j : Elliptic.Kind) : (Cover.ellipticPatch j).Seed D.cocycle where
  toFun := D.ellipticPrimitive j
  holomorphic := (D.ellipticPrimitive_holomorphic j).contMDiffOn
  equivariant := by
    intro g z _
    rw [D.cocycle_fibreMap]
    exact D.ellipticPrimitive_additive j g.property z

/-- The actual cusp seed `-tau`, with the whole cyclic subgroup verified. -/
def cuspSeed : Cover.cuspPatch.Seed D.cocycle where
  toFun := cuspPrimitive D.tau
  holomorphic := (cuspPrimitive_holomorphic D.tau_holomorphic).contMDiffOn
  equivariant := by
    intro g z _
    rw [D.cocycle_fibreMap]
    exact D.cuspPrimitive_additive g.property z

/-- A constructed seed on every member of the actual common cover. -/
def seed (i : Cover.Index) : (Cover.patch i).Seed D.cocycle :=
  match i with
  | none => D.cuspSeed
  | some (.inl x) => D.regularSeed x
  | some (.inr j) => D.ellipticSeed j

/-- Extend the explicit seed to the literal union of all triangle translates
of its precisely invariant sheet.  Outside this saturation the value is zero. -/
def localSection (i : Cover.Index) : ℍ → ℂ := (D.seed i).extend

theorem localSection_holomorphic (i : Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.localSection i) (Cover.patch i).saturation :=
  (D.seed i).extend_holomorphic

/-- Every local section satisfies the full actual all-word additive law on
its saturation, not merely the equation of one stabilizer generator. -/
theorem localSection_additive (i : Cover.Index) (g : TriangleGroup) (z : ℍ)
    (hz : z ∈ (Cover.patch i).saturation) :
    D.localSection i (triangleGeometricRepresentation g z) =
      D.localSection i z + D.shift g z := by
  have he := (D.seed i).extend_equivariant g z hz
  rwa [D.cocycle_fibreMap] at he

theorem localSection_eq_seed (i : Cover.Index) (z : ℍ) (hz : z ∈ (Cover.patch i).sheet) :
    D.localSection i z = (D.seed i).toFun z :=
  (D.seed i).extend_eq z hz

/-- The formula on a translated sheet uses the actual additive word shift. -/
theorem localSection_translate (i : Cover.Index) (g : TriangleGroup) (z : ℍ)
    (hz : z ∈ (Cover.patch i).sheet) :
    D.localSection i (triangleGeometricRepresentation g z) =
      (D.seed i).toFun z + D.shift g z := by
  have he := (D.seed i).extend_translate g z hz
  rwa [D.cocycle_fibreMap] at he

theorem localSection_regular (x : TriangleRegularQuotient) (z : ℍ)
    (hz : z ∈ Cover.regularSheet x) : D.localSection (Cover.regularIndex x) z = 0 :=
  (D.regularSeed x).extend_eq z hz

theorem localSection_elliptic (j : Elliptic.Kind) (z : ℍ)
    (hz : z ∈ Triangle.ellipticNeighborhood j) :
    D.localSection (Cover.ellipticIndex j) z = D.ellipticPrimitive j z :=
  (D.ellipticSeed j).extend_eq z hz

/-- On the genuine cusp horodisc, the constructed local section is exactly
the explicit primitive `-tau`. -/
theorem localSection_cusp (z : ℍ) (hz : z ∈ Triangle.horodisc Triangle.width) :
    D.localSection Cover.cuspIndex z = -(D.tau z : ℂ) :=
  D.cuspSeed.extend_eq z hz

end Data

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
