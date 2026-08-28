import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansCore

/-!
# Moving a geometric local meridian to a common base point

A tail in the actual regular covering, followed by a specified local
meridian lift and the translated reverse tail, ends at the same inverse
deck translate of the chosen base point.  Its projection is exactly the
tail, local loop, and reverse tail.  Thus the later explicit local circle
meridians give based meridians, rather than merely arbitrary loops with a
prescribed deck endpoint.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped Matrix MatrixGroups

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open FirstHurewicz SpecialPeriods

/-- Attach a specified upstairs tail to a local inverse-generator lift. -/
def rebaseLift (b c : TriangleRegularPoint) (g : TriangleGroup)
    (α : Path b c) (δ : Path c (g⁻¹ • c)) : Path b (g⁻¹ • b) :=
  α.trans (δ.trans (α.symm.map (continuous_const_smul g⁻¹)))

/-- The based loop obtained from a specified local meridian and tail. -/
def rebaseLoop (b c : TriangleRegularPoint) (g : TriangleGroup)
    (α : Path b c) (δ : Path c (g⁻¹ • c)) :
    Path (triangleRegularProject b) (triangleRegularProject b) :=
  projectLift b g (rebaseLift b c g α δ)

/-- The constructed loop really is the local loop with its outgoing and
returning tail, as a literal parametrized path. -/
theorem rebaseLoop_eq_conjugate (b c : TriangleRegularPoint) (g : TriangleGroup)
    (α : Path b c) (δ : Path c (g⁻¹ • c)) :
    rebaseLoop b c g α δ =
      (α.map triangleRegularProject_covering.continuous).trans
        ((projectLift c g δ).trans
          (α.map triangleRegularProject_covering.continuous).symm) := by
  ext t
  simp only [rebaseLoop, projectLift_apply, rebaseLift, Path.trans_apply, Path.map_coe,
    Function.comp_apply, Path.symm_apply]
  split_ifs <;> simp only [triangleRegularProject_covering.map_smul]

theorem rebaseLoop_monodromy (b c : TriangleRegularPoint) (g : TriangleGroup)
    (α : Path b c) (δ : Path c (g⁻¹ • c)) :
    (triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (rebaseLoop b c g α δ)) ⟨b, rfl⟩ :
        TriangleRegularPoint) = g⁻¹ • b :=
  congrArg Subtype.val (projectLift_monodromy b g (rebaseLift b c g α δ))

/-- Path connectedness chooses only the tail.  The local meridian is
still the supplied, geometrically verified loop, not a chosen deck path. -/
def basedLoop (b c : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path c (g⁻¹ • c)) :
    Path (triangleRegularProject b) (triangleRegularProject b) :=
  rebaseLoop b c g (PathConnectedSpace.somePath b c) δ

theorem basedLoop_eq_conjugate (b c : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path c (g⁻¹ • c)) :
    basedLoop b c g δ =
      ((PathConnectedSpace.somePath b c).map triangleRegularProject_covering.continuous).trans
        ((projectLift c g δ).trans
          ((PathConnectedSpace.somePath b c).map
            triangleRegularProject_covering.continuous).symm) :=
  rebaseLoop_eq_conjugate b c g (PathConnectedSpace.somePath b c) δ

variable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

theorem rebaseLoop_latticeTransport (b c : TriangleRegularPoint) (g : TriangleGroup)
    (α : Path b c) (δ : Path c (g⁻¹ • c)) :
    regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk (rebaseLoop b c g α δ)) = triangleDualRepresentation g :=
  projectLift_latticeTransport P h₁ h₂ b g (rebaseLift b c g α δ)

theorem basedLoop_latticeTransport (b c : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path c (g⁻¹ • c)) :
    regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk (basedLoop b c g δ)) = triangleDualRepresentation g :=
  rebaseLoop_latticeTransport P h₁ h₂ b c g (PathConnectedSpace.somePath b c) δ

/-- The geometric loop with a tail has the prescribed action on the
actual singular homology of the fibre at the common base point. -/
theorem rebaseLoop_singularH1 (b c : TriangleRegularPoint) (g : TriangleGroup)
    (α : Path b c) (δ : Path c (g⁻¹ • c))
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology
        (regularPathTransport P h₁ h₂ (rebaseLoop b c g α δ) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      (triangleDualRepresentation g : LatticeMatrix) *ᵥ
        regularFibreSingularH1Equiv P h₁ h₂ b a :=
  projectLift_singularH1 P h₁ h₂ b g (rebaseLift b c g α δ) a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
