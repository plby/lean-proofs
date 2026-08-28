import Wikipedia.HopfProblem.OrbitPairSpherePolygonVariationComparison
import Wikipedia.HopfProblem.OrbitPairSpherePolygonCriticalGeodesic
import Wikipedia.HopfProblem.OrbitPairSphereAntipodalIndex
import Wikipedia.HopfProblem.OrbitPairSphereNormalVertexTangent

/-!
# Independent negative directions for actual antipodal critical polygons

The two normal sine modes along a nonminimal antipodal great circle sample
to a linear family of actual tangent vertex fields. Energy contact transfers
their strictly negative second derivatives to normalized vertex variations.
Negativity itself proves that no nonzero parameter samples to the zero field.
For a polygon on S^n the resulting family has dimension 2*n-2.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace SphereNegativeDirections

variable {n m : ℕ}

def sampleFieldLinear {P : Type*} [AddCommGroup P] [Module ℝ P]
    (v : Space n m) (τ : Fin (m + 2) → ℝ) (F : P →ₗ[ℝ] (ℝ → Vector (n + 1)))
    (hF : ∀ p j, inner ℝ (v j).val (F p (τ j.castSucc.succ)) = 0) : P →ₗ[ℝ] Field v where
  toFun p := sampledField v τ (F p) (hF p)
  map_add' p q := by
    funext j
    apply Subtype.ext
    exact congrFun (F.map_add p q) (τ j.castSucc.succ)
  map_smul' r p := by
    funext j
    apply Subtype.ext
    exact congrFun (F.map_smul r p) (τ j.castSucc.succ)

theorem sampleFieldLinear_apply {P : Type*} [AddCommGroup P] [Module ℝ P]
    (v : Space n m) (τ : Fin (m + 2) → ℝ) (F : P →ₗ[ℝ] (ℝ → Vector (n + 1)))
    (hF : ∀ p j, inner ℝ (v j).val (F p (τ j.castSucc.succ)) = 0) (p : P) :
    sampleFieldLinear v τ F hF p = sampledField v τ (F p) (hF p) := rfl

theorem linear_injective_of_negative_normalVariations (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) {d : ℕ}
    (R : (Fin d → ℝ) →ₗ[ℝ] Field v)
    (hneg : ∀ c, c ≠ 0 →
      deriv (deriv (fun s => energy a b τ (normalVariation v (R c) s))) 0 < 0) :
    Function.Injective R := by
  apply (injective_iff_map_eq_zero R).mpr
  intro c hc
  by_contra hne
  have hn := hneg c hne
  rw [hc] at hn
  simp only [normalVariation_zero_field, deriv_const', deriv_const] at hn
  exact (lt_irrefl 0) hn

theorem exists_negative_vertexFamily (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (y : Vector (n + 1)) (hy : ‖y‖ = 1) (hxy : inner ℝ a.val y = 0)
    (w : ℝ) (hw : 3 * Real.pi ≤ |w|)
    (hmatch : ∀ j : Fin (m + 2),
      SphereGreatCircle.curve a.val y w (τ j) = (vertices a b v j).val)
    (hcontact : energy a b τ v = SpherePathEnergy.energy (SphereGreatCircle.curve a.val y w) 0 1) :
    ∃ (d : ℕ) (R : (Fin d → ℝ) →ₗ[ℝ] Field v),
      d + 2 = 2 * n ∧ Function.Injective R ∧ ∀ c, c ≠ 0 →
        deriv (deriv (fun s => energy a b τ (normalVariation v (R c) s))) 0 < 0 := by
  let e := (Module.finBasis ℝ (Parameters a.val y)).equivFun.symm
  let F := (fieldLinear a.val y).comp e.toLinearMap
  have horth (c : Fin (Module.finrank ℝ (Parameters a.val y)) → ℝ) (t : ℝ) :
      inner ℝ (SphereGreatCircle.curve a.val y w t) (F c t) = 0 :=
    field_orthogonal a.val y (e c) w t
  let R := sampleFieldLinear v τ F
    (fun c => sample_orthogonality a b τ v hmatch (horth c))
  have hRneg (c : Fin (Module.finrank ℝ (Parameters a.val y)) → ℝ) (hc : c ≠ 0) :
      deriv (deriv (fun s => energy a b τ (normalVariation v (R c) s))) 0 < 0 := by
    have hle := secondDerivative_le_of_energy_contact a b τ hτ v hv
      (SphereGreatCircle.contDiff_curve a.val y w) (SphereSineModes.contDiff_field _ _)
      (SphereGreatCircle.norm_curve (ClosedHemisphere.unit_norm a) hy hxy w) (horth c) hmatch
      (by rw [hzero]; exact SphereSineModes.field_zero _ _)
      (by rw [hone]; exact SphereSineModes.field_one _ _)
      (by simpa only [hzero, hone] using hcontact)
    rw [hzero, hone] at hle
    exact lt_of_le_of_lt hle (negative_secondDerivative (ClosedHemisphere.unit_norm a)
      hy hxy w hw (e c) (fun he => hc (e.injective (he.trans e.map_zero.symm))))
  have hd := dimension (ClosedHemisphere.unit_norm a) hy hxy
  exact ⟨Module.finrank ℝ (Parameters a.val y), R, by omega,
    linear_injective_of_negative_normalVariations a b τ v R hRneg, hRneg⟩

theorem endpoints_ne_of_antipodal (a b : Sphere n) (hanti : b.val = -a.val) : a ≠ b := by
  intro he
  have hi := congrArg (fun z => inner ℝ a.val z) hanti
  rw [← he, inner_neg_right, real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm,
    one_pow] at hi
  norm_num at hi

theorem exists_negative_vertexFamily_of_critical (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : b.val = -a.val) (habove : Real.pi ^ 2 < energy a b τ v) :
    ∃ (d : ℕ) (R : (Fin d → ℝ) →ₗ[ℝ] Field v),
      d + 2 = 2 * n ∧ Function.Injective R ∧ ∀ c, c ≠ 0 →
        deriv (deriv (fun s => energy a b τ (normalVariation v (R c) s))) 0 < 0 := by
  have hstat := isStationary_of_mfderiv_eq_zero a b τ v hv hcrit
  obtain ⟨y, w, _, hy, hxy, hw, hsample⟩ :=
    exists_greatCircle_of_stationary a b τ hτ v hv hstat (endpoints_ne_of_antipodal a b hanti)
  have hmatch (j : Fin (m + 2)) :
      SphereGreatCircle.curve a.val y w (τ j) = (vertices a b v j).val := by
    simpa only [hzero, sub_zero] using (hsample j).symm
  have hend : SphereGreatCircle.curve a.val y w 1 = -a.val := by
    have he := hmatch (Fin.last (m + 1))
    simpa only [hone, vertices_last, hanti] using he
  have hcontact : energy a b τ v =
      SpherePathEnergy.energy (SphereGreatCircle.curve a.val y w) 0 1 := by
    rw [energy_eq_speed_sq_mul_of_stationary a b τ hτ v hv hstat,
      hzero, hone, sub_zero, mul_one,
      SphereGreatCircle.energy_curve (ClosedHemisphere.unit_norm a) hy hxy, hw]
  have hwlarge := SphereAntipodalIndex.speed_ge_three_pi_of_nonminimal
    (ClosedHemisphere.unit_norm a) hy hxy hend (by rwa [← hcontact])
  exact exists_negative_vertexFamily a b τ hτ hzero hone v hv y hy hxy w hwlarge hmatch hcontact

theorem exists_negative_tangentFamily_of_critical (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : b.val = -a.val) (habove : Real.pi ^ 2 < energy a b τ v) :
    ∃ (d : ℕ) (R : (Fin d → ℝ) →ₗ[ℝ] Field v), d + 2 = 2 * n ∧
      Function.Injective (fun c =>
        deriv (fun s => atVertices v (normalVariation v (R c) s)) 0) ∧
      ∀ c, c ≠ 0 →
        deriv (deriv (fun s => energy a b τ (normalVariation v (R c) s))) 0 < 0 := by
  obtain ⟨d, R, hd, hR, hneg⟩ :=
    exists_negative_vertexFamily_of_critical a b τ hτ hzero hone v hv hcrit hanti habove
  exact ⟨d, R, hd, independent_normal_chart_tangents v R hR, hneg⟩

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
