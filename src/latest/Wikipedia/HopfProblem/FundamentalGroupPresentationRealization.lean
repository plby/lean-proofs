import Wikipedia.HopfProblem.FundamentalGroupPresentation

/-!
# Realizing the checked group presentation by actual group elements

The presented-group universal property gives a map into any group once
the five displayed relations hold for its specified elements.  The
generator equations are retained explicitly, so a geometric application
must prove its actual attaching identities before using the algebraic
calculation of the presentation.
-/

namespace Wikipedia.HopfProblem.TwistGroup

variable {G : Type*} [Group G]

/-- The prescribed images of the central, first, and second generators. -/
def realizationImages (c₀ x₀ y₀ : G) : Fin 3 → G := ![c₀, x₀, y₀]

theorem realizationImages_relators (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀)
    (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b) (hy : y₀ ^ 4 = c₀ ^ d) :
    ∀ r ∈ Set.range (twistRelators a b d),
      FreeGroup.lift (realizationImages c₀ x₀ y₀) r = 1 := by
  rintro r ⟨i, rfl⟩
  fin_cases i <;>
    simp [twistRelators, realizationImages, hcx.eq, hcy.eq, hxy, hx, hy]

/-- The homomorphism with the proved actual generator values and relations. -/
def realizationHom (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀)
    (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b) (hy : y₀ ^ 4 = c₀ ^ d) :
    TwistGroup a b d →* G :=
  PresentedGroup.toGroup (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)

@[simp] theorem realizationHom_c (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀)
    (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b) (hy : y₀ ^ 4 = c₀ ^ d) :
    realizationHom a b d c₀ x₀ y₀ hcx hcy hxy hx hy (c a b d) = c₀ :=
  PresentedGroup.toGroup.of (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)

@[simp] theorem realizationHom_x (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀)
    (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b) (hy : y₀ ^ 4 = c₀ ^ d) :
    realizationHom a b d c₀ x₀ y₀ hcx hcy hxy hx hy (x a b d) = x₀ :=
  PresentedGroup.toGroup.of (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)

@[simp] theorem realizationHom_y (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀)
    (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b) (hy : y₀ ^ 4 = c₀ ^ d) :
    realizationHom a b d c₀ x₀ y₀ hcx hcy hxy hx hy (y a b d) = y₀ :=
  PresentedGroup.toGroup.of (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)

/-- The already checked main presentation kills the specified elements
of a target group only after all of their actual relations are supplied. -/
theorem main_realization_generators_eq_one (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀)
    (hxy : x₀ * y₀ = 1) (hx : x₀ ^ 3 = c₀) (hy : y₀ ^ 4 = c₀⁻¹) :
    c₀ = 1 ∧ x₀ = 1 ∧ y₀ = 1 := by
  let f := realizationHom 0 1 (-1) c₀ x₀ y₀ hcx hcy
    (by simpa only [zpow_zero] using hxy)
    (by simpa only [zpow_one] using hx)
    (by simpa only [zpow_neg_one] using hy)
  have hc₀ : f (c 0 1 (-1)) = c₀ := realizationHom_c ..
  have hx₀ : f (x 0 1 (-1)) = x₀ := realizationHom_x ..
  have hy₀ : f (y 0 1 (-1)) = y₀ := realizationHom_y ..
  refine ⟨hc₀.symm.trans ?_, hx₀.symm.trans ?_, hy₀.symm.trans ?_⟩
  · exact (congrArg f (main_group_trivial _)).trans f.map_one
  · exact (congrArg f (main_group_trivial _)).trans f.map_one
  · exact (congrArg f (main_group_trivial _)).trans f.map_one

end Wikipedia.HopfProblem.TwistGroup
