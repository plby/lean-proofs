import Wikipedia.NoExoticSixSphere.OrthogonalPolygonVariationComparison
import Wikipedia.NoExoticSixSphere.OrthogonalStationaryPolygon
import Wikipedia.NoExoticSixSphere.OrthogonalAntipodalIndex
import Wikipedia.NoExoticSixSphere.SkewAntipodalMinimum
import Wikipedia.NoExoticSixSphere.OrthogonalVertexTangent

/-!
# Negative directions for the actual finite polygon energy

For a strictly short polygon realizing a nonminimal antipodal exponential,
sampling the rotating sine fields transfers the negative second variations
to a linear family in the finite vertex model. Negativity itself proves
that sampling does not collapse a nonzero member of this family.
-/

open Set
open scoped ContDiff Manifold

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  OrthogonalIndexTestField

variable {n m : ℕ}

noncomputable def sampleFieldLinear (τ : Fin (m + 2) → ℝ) :
    (ℝ → SkewOperators n) →ₗ[ℝ] Model n m :=
  LinearMap.pi (fun j ↦ LinearMap.proj (τ j.castSucc.succ))

theorem sampleFieldLinear_apply (τ : Fin (m + 2) → ℝ) (W : ℝ → SkewOperators n) :
    sampleFieldLinear τ W = sampledField τ W := rfl

theorem vertexVariation_zero_field (v : Space n m) (s : ℝ) : vertexVariation v 0 s = v := by
  funext i
  simp only [vertexVariation, Pi.zero_apply, smul_zero, exp_zero, mul_one]

theorem linear_injective_of_negative_variations (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) {d : ℕ}
    (R : (Fin d → ℝ) →ₗ[ℝ] Model n m)
    (hneg : ∀ c, c ≠ 0 →
      deriv (deriv (fun s ↦ energy a b τ (vertexVariation v (R c) s))) 0 < 0) :
    Function.Injective R := by
  apply (injective_iff_map_eq_zero R).mpr
  intro c hc
  by_contra hne
  have hn := hneg c hne
  rw [hc] at hn
  simp only [vertexVariation_zero_field, deriv_const', deriv_const] at hn
  exact (lt_irrefl 0) hn

theorem exists_negative_vertexFamily (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m) (K : SkewOperators n)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, path a b τ v t = a * exp (t • K))
    (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hnot : SkewSpectralPlane.gram K ≠ Real.pi ^ 2 • (1 : Vector n →L[ℝ] Vector n)) :
    ∃ (d : ℕ) (R : (Fin d → ℝ) →ₗ[ℝ] Model n m),
      d + 2 = n ∧ Function.Injective R ∧ ∀ c, c ≠ 0 →
        deriv (deriv (fun s ↦ energy a b τ (vertexVariation v (R c) s))) 0 < 0 := by
  let γ : ℝ → OrthogonalOperators n := fun t ↦ a * exp (t • K)
  have hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1) :=
    contDiff_const.clm_comp (SkewConjugation.contDiff_exp_smul_operator K)
  have htime (j : Fin (m + 2)) : τ j ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hzero]
      exact hτ.monotone (Fin.zero_le j)
    · rw [← hone]
      exact hτ.monotone (Fin.le_last j)
  have hmatch (j : Fin (m + 2)) : γ (τ j) = vertices a b v j :=
    (hpath _ (htime j)).symm.trans (path_vertex a b τ hτ hv.1 j)
  have hcontact : energy a b τ v = OrthogonalPathEnergy.energy
      (fun t ↦ (γ t).1.1) (τ 0) (τ (Fin.last (m + 1))) := by
    rw [← path_energy_eq a b τ hτ hv.1, hzero, hone]
    apply OrthogonalPathEnergy.energy_congr_Icc zero_le_one
    intro t ht
    exact congrArg (fun q : OrthogonalOperators n ↦ q.1.1) (hpath t ht)
  obtain ⟨d, T, hd, _, hneg⟩ := OrthogonalAntipodalIndex.exists_negativeFamily K hexp hnot
  let R : (Fin d → ℝ) →ₗ[ℝ] Model n m :=
    (sampleFieldLinear τ).comp ((fieldLinear K).comp T)
  have hRneg (c : Fin d → ℝ) (hc : c ≠ 0) :
      deriv (deriv (fun s ↦ energy a b τ (vertexVariation v (R c) s))) 0 < 0 := by
    have hle := secondDerivative_le_of_energy_contact a b τ hτ v hv hγ
      (contDiff_field K (T c)) hmatch
      (by rw [hzero]; exact field_zero K (T c))
      (by rw [hone]; exact field_one K (T c)) hcontact
    rw [hzero, hone] at hle
    exact lt_of_le_of_lt hle (negative_secondDerivative a K (T c) (hneg c hc))
  exact ⟨d, R, hd, linear_injective_of_negative_variations a b τ v R hRneg, hRneg⟩

/-- Nonminimal antipodal critical polygons have at least `n - 2` independent
directions on which the actual second energy derivative is strictly negative. -/
theorem exists_negative_vertexFamily_of_critical (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ (d : ℕ) (R : (Fin d → ℝ) →ₗ[ℝ] Model n m),
      d + 2 = n ∧ Function.Injective R ∧ ∀ c, c ≠ 0 →
        deriv (deriv (fun s ↦ energy a b τ (vertexVariation v (R c) s))) 0 < 0 := by
  obtain ⟨K, hend, hpath⟩ := critical_is_exponential a b τ hτ v hv.1 hcrit
  simp only [hzero, hone, sub_zero, one_smul] at hend hpath
  have hexpeq : exp K = a⁻¹ * b := by rw [← hend, inv_mul_cancel_left]
  have hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n) := by rwa [hexpeq]
  apply exists_negative_vertexFamily a b τ hτ hzero hone v hv K hpath hexp
  intro hgram
  have he := path_energy_eq a b τ hτ hv.1
  rw [hzero, hone] at he
  have hcompare : OrthogonalPathEnergy.energy (fun t ↦ (path a b τ v t).1.1) 0 1 =
      OrthogonalPathEnergy.energy (fun t ↦ (a * exp (t • K)).1.1) 0 1 :=
    OrthogonalPathEnergy.energy_congr_Icc zero_le_one
      (fun t ht ↦ congrArg (fun q : OrthogonalOperators n ↦ q.1.1) (hpath t ht))
  have hs : energy a b τ v = HilbertSchmidt.squareNorm (K : Vector n →L[ℝ] Vector n) := by
    rw [OrthogonalPathEnergy.energy_left_exp] at hcompare
    simpa only [sub_zero, one_mul] using he.symm.trans hcompare
  exact habove.ne' (hs.trans (SkewAntipodalSpectrum.squareNorm_of_gram_scalar K _ hgram))

/-- The negative family has independent actual tangent vectors in the
product Cayley chart, not just independent curve parameters. -/
theorem exists_negative_tangentFamily_of_critical (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ (d : ℕ) (R : (Fin d → ℝ) →ₗ[ℝ] Model n m), d + 2 = n ∧
      Function.Injective (fun c ↦ deriv (fun s ↦ atVertices v (vertexVariation v (R c) s)) 0) ∧
      ∀ c, c ≠ 0 →
        deriv (deriv (fun s ↦ energy a b τ (vertexVariation v (R c) s))) 0 < 0 := by
  obtain ⟨d, R, hd, hR, hneg⟩ :=
    exists_negative_vertexFamily_of_critical a b τ hτ hzero hone v hv hcrit hanti habove
  exact ⟨d, R, hd, independent_chart_tangents v R hR, hneg⟩

end NoExoticSixSphere.OrthogonalPolygon
