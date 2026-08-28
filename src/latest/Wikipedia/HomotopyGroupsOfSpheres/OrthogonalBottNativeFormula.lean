import Wikipedia.NoExoticSixSphere.OrthogonalBottDegreeShift

/-! # The actual orthogonal Bott map on native cube representatives -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.OrthogonalBottNative

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

variable {n : ℕ}

def antipode (J₀ : OrthogonalComplexStructures.Space n) : OrthogonalOperators n :=
  OrthogonalExponential.exp (Real.pi • J₀.val)

theorem identity_antipodal (J₀ : OrthogonalComplexStructures.Space n) :
    ((1 : OrthogonalOperators n)⁻¹ * antipode J₀).val.val =
      -(1 : Vector n →L[ℝ] Vector n) := by
  simpa only [inv_one, one_mul, antipode] using OrthogonalComplexStructures.exp_pi J₀

def loopMap (J₀ : OrthogonalComplexStructures.Space n) :
    C(OrthogonalComplexStructures.Space n, Path (1 : OrthogonalOperators n) 1) :=
  OrthogonalPolygon.bottLoopMap 1 (antipode J₀) (identity_antipodal J₀) J₀

theorem loopMap_base (J₀ : OrthogonalComplexStructures.Space n) :
    loopMap J₀ J₀ = Path.refl 1 :=
  OrthogonalPolygon.bottLoopMap_base 1 (antipode J₀) (identity_antipodal J₀) J₀

theorem loopMap_apply (J₀ J : OrthogonalComplexStructures.Space n) (t : I) :
    loopMap J₀ J t = OrthogonalExponential.exp (((t : ℝ) * Real.pi) • J.val) *
      (OrthogonalExponential.exp (((t : ℝ) * Real.pi) • J₀.val))⁻¹ := by
  change (1 * OrthogonalExponential.exp ((t : ℝ) • (Real.pi • J.val))) *
    (1 * OrthogonalExponential.exp ((t : ℝ) • (Real.pi • J₀.val)))⁻¹ * 1 = _
  rw [one_mul, one_mul, mul_one, smul_smul, smul_smul]

def degreeShift (d : ℕ) [NeZero d] (J₀ : OrthogonalComplexStructures.Space n)
    (hd : d + 3 < n) :
    π_ d (OrthogonalComplexStructures.Space n) J₀ ≃* π_ (d + 1) (OrthogonalOperators n) 1 :=
  OrthogonalPolygon.bottDegreeShiftMulEquiv d 1 (antipode J₀) (identity_antipodal J₀) J₀ hd

def nativeCube {d : ℕ} (J₀ : OrthogonalComplexStructures.Space n)
    (p : GenLoop (Fin d) (OrthogonalComplexStructures.Space n) J₀) :
    GenLoop (Fin (d + 1)) (OrthogonalOperators n) 1 :=
  GeneralizedLoopCurrying.uncurry (HigherHomotopy.genLoopMap (loopMap J₀) (loopMap_base J₀) p)

theorem nativeCube_apply {d : ℕ} (J₀ : OrthogonalComplexStructures.Space n)
    (p : GenLoop (Fin d) (OrthogonalComplexStructures.Space n) J₀) (t : Fin (d + 1) → I) :
    nativeCube J₀ p t =
      OrthogonalExponential.exp (((t 0 : ℝ) * Real.pi) • (p (Fin.tail t)).val) *
        (OrthogonalExponential.exp (((t 0 : ℝ) * Real.pi) • J₀.val))⁻¹ :=
  loopMap_apply J₀ (p (Fin.tail t)) (t 0)

theorem degreeShift_mk (d : ℕ) [NeZero d] (J₀ : OrthogonalComplexStructures.Space n)
    (hd : d + 3 < n) (p : GenLoop (Fin d) (OrthogonalComplexStructures.Space n) J₀) :
    degreeShift d J₀ hd (⟦p⟧ : π_ d (OrthogonalComplexStructures.Space n) J₀) =
      (⟦nativeCube J₀ p⟧ : π_ (d + 1) (OrthogonalOperators n) 1) := by
  change GeneralizedLoopCurrying.homotopyEquiv d 1
    (HigherHomotopy.map (loopMap J₀) (loopMap_base J₀) (Quotient.mk' p)) = _
  rw [HigherHomotopy.map_mk, GeneralizedLoopCurrying.homotopyEquiv_mk]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.OrthogonalBottNative
