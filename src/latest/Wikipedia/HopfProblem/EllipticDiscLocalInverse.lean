import Wikipedia.HopfProblem.EllipticDiscOrbits
import Wikipedia.HopfProblem.CuspPuncturedCovering
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Analytic inverse charts away from the elliptic branching point

The nonzero derivative of a power map gives actual holomorphic inverse
charts.  Restricting them to the inherited unit-disc atlas proves that
the elliptic base maps are locally biholomorphic away from zero.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

local notation "I₁" => modelWithCornersSelf ℂ ℂ

theorem complexPower_holomorphic (m : ℕ) : ContDiff ℂ ω (fun z : ℂ => z ^ m) :=
  contDiff_id.pow m

theorem complexPower_coefficient_ne_zero (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    (m : ℂ) * z ^ (m - 1) ≠ 0 :=
  mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hz)

/-- An actual analytic inverse chart for the complex power map, restricted
away from zero so its inverse remains analytic on its whole target. -/
def complexPowerChart (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    OpenPartialHomeomorph ℂ ℂ :=
  ((complexPower_holomorphic m).contDiffAt.toOpenPartialHomeomorph (fun w : ℂ => w ^ m)
    ((complexPower_hasDerivAt m z).hasFDerivAt_equiv
      (complexPower_coefficient_ne_zero m hm z hz)) (by simp)).restr {w | w ≠ 0}

@[simp] theorem complexPowerChart_apply (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0)
    (w : ℂ) : complexPowerChart m hm z hz w = w ^ m := rfl

theorem mem_complexPowerChart_source (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    z ∈ (complexPowerChart m hm z hz).source := by
  have ho : IsOpen {w : ℂ | w ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  rw [complexPowerChart, OpenPartialHomeomorph.restr_source' _ _ ho]
  exact ⟨(complexPower_holomorphic m).contDiffAt.mem_toOpenPartialHomeomorph_source
    ((complexPower_hasDerivAt m z).hasFDerivAt_equiv
      (complexPower_coefficient_ne_zero m hm z hz)) (by simp), hz⟩

theorem complexPowerChart_source_ne_zero (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0)
    {w : ℂ} (hw : w ∈ (complexPowerChart m hm z hz).source) : w ≠ 0 := by
  have ho : IsOpen {w : ℂ | w ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  rw [complexPowerChart, OpenPartialHomeomorph.restr_source' _ _ ho] at hw
  exact hw.2

theorem complexPowerChart_holomorphic (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    ContDiffOn ℂ ω (complexPowerChart m hm z hz) (complexPowerChart m hm z hz).source :=
  (complexPower_holomorphic m).contDiffOn

theorem complexPowerChart_symm_holomorphic (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    ContDiffOn ℂ ω (complexPowerChart m hm z hz).symm
      (complexPowerChart m hm z hz).target := by
  intro w hw
  have hne := complexPowerChart_source_ne_zero m hm z hz
    ((complexPowerChart m hm z hz).map_target hw)
  exact ((complexPowerChart m hm z hz).contDiffAt_symm hw
    ((complexPower_hasDerivAt m _).hasFDerivAt_equiv
      (complexPower_coefficient_ne_zero m hm _ hne))
    (complexPower_holomorphic m).contDiffAt).contDiffWithinAt

theorem complexPower_isLocalDiffeomorphAt (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    IsLocalDiffeomorphAt I₁ I₁ ω (fun w : ℂ => w ^ m) z := by
  refine ⟨{
    toPartialEquiv := (complexPowerChart m hm z hz).toPartialEquiv
    open_source := (complexPowerChart m hm z hz).open_source
    open_target := (complexPowerChart m hm z hz).open_target
    contMDiffOn_toFun := (complexPowerChart_holomorphic m hm z hz).contMDiffOn
    contMDiffOn_invFun := (complexPowerChart_symm_holomorphic m hm z hz).contMDiffOn },
    mem_complexPowerChart_source m hm z hz, fun _ _ => rfl⟩

/-- Away from the branching center, the actual disc power map is a local
biholomorphism for the inherited complex charts on both discs. -/
theorem discPower_isLocalDiffeomorphAt (m : ℕ) (hm : 0 < m) (z : Disc)
    (hz : (z : ℂ) ≠ 0) : IsLocalDiffeomorphAt I₁ I₁ ω (discPower m hm) z :=
  isLocalDiffeomorphAt_restrictOpens I₁ I₁
    (complexPower_isLocalDiffeomorphAt m hm z hz) unitDisc unitDisc
    (fun w hw => (pow_mem_unitDisc_iff m hm w).mpr hw) z.property

theorem discPower_isLocalDiffeomorphOn (m : ℕ) (hm : 0 < m) :
    IsLocalDiffeomorphOn I₁ I₁ ω (discPower m hm) {z : Disc | (z : ℂ) ≠ 0} :=
  fun z => discPower_isLocalDiffeomorphAt m hm z z.property

end Wikipedia.HopfProblem.Elliptic
