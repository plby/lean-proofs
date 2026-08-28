import Wikipedia.HopfProblem.CuspNegationQuotient
import Wikipedia.HopfProblem.CuspPuncturedBasic

/-!
# The full-cap involution is literal fibre negation on the logarithmic cover

On the dense torus the fan involution inverts the first two characters
and fixes the time character. The normalized exponential therefore
identifies it with `(s,w) ↦ (s,-w)`, including the corrected quotient.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspNegation

open ToricCharts ToricFan Triangle ToricSpace CuspQuotient CuspUniformization

def fibreReciprocal (w : CoordinateSpace 3) : CoordinateSpace 3 := ![(w 0)⁻¹, (w 1)⁻¹, w 2]

theorem fibreReciprocal_mem_torus {w : CoordinateSpace 3} (hw : w ∈ torus) :
    fibreReciprocal w ∈ torus := by
  intro i
  fin_cases i
  · exact inv_ne_zero (hw 0)
  · exact inv_ne_zero (hw 1)
  · exact hw 2

theorem permute_mem_torus {w : CoordinateSpace 3} (hw : w ∈ torus) : permute w ∈ torus :=
  fun i => hw i.rev

theorem rays_triangleNeg (s : Triangle) (i j : Fin 3) :
    (triangleNeg s).rays i j =
      if i = 2 then s.rays i j.rev else -s.rays i j.rev := by
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
    simp [Triangle.rays, triangleNeg, hs, Fin.rev] <;> ring

theorem monomial_rays_triangleNeg (s : Triangle) (z : CoordinateSpace 3) :
    monomial (triangleNeg s).rays (permute z) = fibreReciprocal (monomial s.rays z) := by
  have hp (i : Fin 3) :
      (∏ j : Fin 3, z j.rev ^ s.rays i j.rev) = ∏ j : Fin 3, z j ^ s.rays i j :=
    Equiv.prod_comp Fin.revPerm (fun j => z j ^ s.rays i j)
  ext i
  by_cases hi : i = 2
  · subst i
    change (∏ j, z j.rev ^ (triangleNeg s).rays 2 j) = ∏ j, z j ^ s.rays 2 j
    simp only [rays_triangleNeg, if_pos rfl]
    exact hp 2
  · have ht : fibreReciprocal (monomial s.rays z) i = (monomial s.rays z i)⁻¹ := by
      fin_cases i <;> simp_all [fibreReciprocal]
    rw [ht]
    change (∏ j, z j.rev ^ (triangleNeg s).rays i j) = (∏ j, z j ^ s.rays i j)⁻¹
    simp only [rays_triangleNeg, hi, if_false, zpow_neg, Finset.prod_inv_distrib]
    exact congrArg Inv.inv (hp i)

theorem torusCoordinates_toricNegation {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (toricNegation x) = fibreReciprocal (torusCoordinates x) := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [toricNegation_inclusion,
    torusCoordinates_inclusion _ (permute_mem_torus hz),
    torusCoordinates_inclusion _ hz, monomial_rays_triangleNeg]

theorem toricNegation_mem_openTorus {x : Space} (hx : x ∈ openTorus) :
    toricNegation x ∈ openTorus := by
  apply (mem_openTorus_iff _).mpr
  rw [time_toricNegation]
  exact (mem_openTorus_iff _).mp hx

theorem toricNegation_torusPoint {w : CoordinateSpace 3} (hw : w ∈ torus) :
    toricNegation (torusPoint w) = torusPoint (fibreReciprocal w) := by
  apply torusCoordinates_injective
    (toricNegation_mem_openTorus (torusPoint_mem hw))
    (torusPoint_mem (fibreReciprocal_mem_torus hw))
  rw [torusCoordinates_toricNegation (torusPoint_mem hw), torusCoordinates_torusPoint hw,
    torusCoordinates_torusPoint (fibreReciprocal_mem_torus hw)]

theorem exponential_neg (z : ℂ) : exponential (-z) = (exponential z)⁻¹ := by
  simp only [exponential, mul_neg, Complex.exp_neg]

theorem fibreReciprocal_exponentialCoordinates (t : ℂ) (z : ComplexPlane₂) :
    fibreReciprocal (exponentialCoordinates t z) = exponentialCoordinates t (-z) := by
  ext i
  fin_cases i <;> simp [fibreReciprocal, exponentialCoordinates, exponential_neg]

theorem toricNegation_exponentialPoint {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    toricNegation (exponentialPoint t z) = exponentialPoint t (-z) := by
  change toricNegation (torusPoint (exponentialCoordinates t z)) =
    torusPoint (exponentialCoordinates t (-z))
  rw [toricNegation_torusPoint (exponentialCoordinates_mem ht z),
    fibreReciprocal_exponentialCoordinates]

def logCoverNegation (ε : ℝ) (p : LogCover ε) : LogCover ε :=
  ⟨logNeg p, p.2⟩

theorem totalExponentialPoint_logNeg (p : ℂ × ComplexPlane₂) :
    toricNegation (totalExponentialPoint p) = totalExponentialPoint (logNeg p) :=
  toricNegation_exponentialPoint (exponential_ne_zero p.1) p.2

theorem tubeNegation_totalExponentialLift (ε : ℝ) (p : LogCover ε) :
    tubeNegation (disc ε) (totalExponentialLift ε p) =
      totalExponentialLift ε (logCoverNegation ε p) :=
  Subtype.ext (totalExponentialPoint_logNeg p)

theorem quotientNegation_totalCuspCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (p : LogCover ε) :
    quotientNegation C ε (totalCuspCover C ε p) =
      totalCuspCover C ε (logCoverNegation ε p) := by
  change quotientNegation C ε (quotientMap C ε (totalExponentialLift ε p)) = _
  rw [quotientNegation_quotientMap, tubeNegation_totalExponentialLift]
  rfl

theorem quotientNegation_puncturedCuspCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (p : LogCover ε) :
    quotientNegation C ε (puncturedCuspCover C ε p).val =
      (puncturedCuspCover C ε (logCoverNegation ε p)).val :=
  quotientNegation_totalCuspCover C ε p

end Wikipedia.HopfProblem.CuspNegation
