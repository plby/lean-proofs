import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingLattice
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupMarkedCusp
import Wikipedia.HopfProblem.LatticeCuspNormalClosure

/-!
# The surviving lattice in the actual threefold group

The genuine cusp attaching map kills the last two source columns.  Its
normal conjugates under the actual first meridian kill the remaining
kernel of `γ`.  Thus the lattice image is a single central cyclic image.
Together with the proved joint cusp relation, the actual group is
commutative even before the two elliptic power relations are evaluated.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne

/-- The image of the source's invariant first twist in the actual group. -/
def c : GlobalGroup := latticeHom (Multiplicative.ofAdd ε)

theorem latticeHom_eq_one_of_first_two_coordinates_zero (v : Lattice)
    (h₀ : v 0 = 0) (h₁ : v 1 = 0) :
    latticeHom (Multiplicative.ofAdd v) = 1 :=
  latticeHom_eq_one_of_cusp_monodromy_kernel v
    ((M₀_sub_one_kernel v).mpr ⟨h₀, h₁⟩)

/-- The whole actual kernel of the invariant functional dies globally. -/
theorem latticeHom_eq_one_of_gamma_eq_zero (v : Lattice) (hv : γ v = 0) :
    latticeHom (Multiplicative.ofAdd v) = 1 :=
  LatticeCuspNormalClosure.image_eq_one_of_gamma_eq_zero latticeHom (meridian false)
    meridian_first_conjugation latticeHom_eq_one_of_first_two_coordinates_zero v hv

/-- Exact source-column reduction in the native fundamental group. -/
theorem latticeHom_eq_c_zpow (v : Lattice) :
    latticeHom (Multiplicative.ofAdd v) = c ^ γ v :=
  LatticeCuspNormalClosure.image_eq_zpow_gamma latticeHom (meridian false)
    meridian_first_conjugation latticeHom_eq_one_of_first_two_coordinates_zero v

theorem latticeHom_epsilon_prime : latticeHom (Multiplicative.ofAdd ε') = c :=
  LatticeCuspNormalClosure.image_epsilon_prime_eq latticeHom (meridian false)
    meridian_first_conjugation latticeHom_eq_one_of_first_two_coordinates_zero

/-- Centrality is derived from genuine geometric generators and relations. -/
theorem c_mem_center : c ∈ Subgroup.center GlobalGroup := by
  apply LatticeCuspNormalClosure.image_epsilon_mem_center_of_hom_ext
    latticeHom (meridian false) (meridian true) meridian_first_conjugation
    meridian_second_conjugation latticeHom_eq_one_of_first_two_coordinates_zero
  intro f g hL hx hy
  apply hom_ext f g hL
  intro b
  cases b
  · exact hx
  · exact hy

theorem c_commute (g : GlobalGroup) : Commute c g :=
  (Subgroup.mem_center_iff.mp c_mem_center g).symm

private theorem commute_all_of_marked (g : GlobalGroup)
    (hL : ∀ v : Multiplicative Lattice, Commute g (latticeHom v))
    (hM : ∀ b : Bool, Commute g (meridian b)) : ∀ h : GlobalGroup, Commute g h := by
  have heq : (MulAut.conj g).toMonoidHom = MonoidHom.id GlobalGroup := by
    apply hom_ext
    · intro v
      change g * latticeHom v * g⁻¹ = latticeHom v
      rw [(hL v).eq, mul_inv_cancel_right]
    · intro b
      change g * meridian b * g⁻¹ = meridian b
      rw [(hM b).eq, mul_inv_cancel_right]
  intro h
  have hh : g * h * g⁻¹ = h := DFunLike.congr_fun heq h
  exact (mul_inv_eq_iff_eq_mul).mp hh

/-- The first meridian commutes with the whole actual group because the
other meridian is its inverse and the whole lattice image is central. -/
theorem meridian_first_commute (g : GlobalGroup) : Commute (meridian false) g := by
  apply commute_all_of_marked (meridian false)
  · intro v
    change Commute (meridian false) (latticeHom (Multiplicative.ofAdd v.toAdd))
    rw [latticeHom_eq_c_zpow]
    exact (c_commute (meridian false)).symm.zpow_right _
  · intro b
    cases b
    · exact Commute.refl _
    · rw [meridian_second_eq_first_inv]
      exact (Commute.refl (meridian false)).inv_right

/-- The actual threefold fundamental group is already commutative after
the established cusp relations; this does not yet assert it is trivial. -/
theorem all_commute (g h : GlobalGroup) : Commute g h := by
  apply commute_all_of_marked g
  · intro v
    change Commute g (latticeHom (Multiplicative.ofAdd v.toAdd))
    rw [latticeHom_eq_c_zpow]
    exact (c_commute g).symm.zpow_right _
  · intro b
    cases b
    · exact (meridian_first_commute g).symm
    · rw [meridian_second_eq_first_inv]
      exact (meridian_first_commute g).symm.inv_right

theorem conjugate_eq (g h : GlobalGroup) : g * h * g⁻¹ = h := by
  rw [(all_commute g h).eq, mul_inv_cancel_right]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne
