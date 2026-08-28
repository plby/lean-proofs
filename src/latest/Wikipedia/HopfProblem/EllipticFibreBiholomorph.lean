import Wikipedia.HopfProblem.EllipticFibreManifold
import Wikipedia.HopfProblem.EllipticFibreBiholomorphCore

/-!
# Biholomorphisms with the actual elliptic filling fibres

Both inclusions into the filling are genuine holomorphic immersions. The
proved homeomorphisms with the literal fibres are consequently analytic in
both directions. The target atlas is the single ambient-induced atlas
selected for each base value, independent of which root torus is compared.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ FamilyModel

/-- The actual central quotient surface is biholomorphic to the reduced
central fibre, with the complex atlas induced from its ambient immersion. -/
def centralFibreBiholomorph (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := fillingFibreChartedSpace j v hv Elliptic.discZero
    Diffeomorph I₂ I₂ (Surface j (centralPeriod j) v hv)
      (FillingFibre j v hv Elliptic.discZero) ω := by
  let := fillingFibreChartedSpace j v hv Elliptic.discZero
  exact EmbeddedFibre.biholomorphOfHomeomorph (centralFibreHomeomorph j v hv)
    (centralFibreInclusion_isImmersion j v hv)
    (fillingFibre_inclusion_isImmersionOfComplement j v hv Elliptic.discZero).isImmersion
    (fun _ => rfl)

@[simp] theorem centralFibreBiholomorph_coe (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) :
    letI := fillingFibreChartedSpace j v hv Elliptic.discZero
    (centralFibreBiholomorph j v hv x : Filling j v hv) = centralFibreInclusion j v hv x := rfl

theorem centralFibreHomeomorph_holomorphic (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := fillingFibreChartedSpace j v hv Elliptic.discZero
    ContMDiff I₂ I₂ ω (centralFibreHomeomorph j v hv) := by
  let := fillingFibreChartedSpace j v hv Elliptic.discZero
  exact (centralFibreBiholomorph j v hv).contMDiff

theorem centralFibreHomeomorph_symm_holomorphic (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := fillingFibreChartedSpace j v hv Elliptic.discZero
    ContMDiff I₂ I₂ ω (centralFibreHomeomorph j v hv).symm := by
  let := fillingFibreChartedSpace j v hv Elliptic.discZero
  exact (centralFibreBiholomorph j v hv).symm.contMDiff

/-- Any nonzero root torus is biholomorphic to the same actual filling fibre;
the selected fibre atlas does not depend on this root. -/
def torusFibreBiholomorph (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (hz : (z : ℂ) ≠ 0) :
    letI := fillingFibreChartedSpace j v hv (discPower j.order j.order_pos z)
    Diffeomorph I₂ I₂ ((familyPeriods j).point z).Torus
      (FillingFibre j v hv (discPower j.order j.order_pos z)) ω := by
  let := fillingFibreChartedSpace j v hv (discPower j.order j.order_pos z)
  exact EmbeddedFibre.biholomorphOfHomeomorph (torusFibreHomeomorph j v hv z hz)
    (torusFibreMap_isImmersionOfComplement j v hv z).isImmersion
    (fillingFibre_inclusion_isImmersionOfComplement j v hv
      (discPower j.order j.order_pos z)).isImmersion
    (fun _ => rfl)

@[simp] theorem torusFibreBiholomorph_coe (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (z : Disc) (hz : (z : ℂ) ≠ 0)
    (x : ((familyPeriods j).point z).Torus) :
    letI := fillingFibreChartedSpace j v hv (discPower j.order j.order_pos z)
    (torusFibreBiholomorph j v hv z hz x : Filling j v hv) = torusFibreMap j v hv z x := rfl

theorem torusFibreHomeomorph_holomorphic (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (z : Disc) (hz : (z : ℂ) ≠ 0) :
    letI := fillingFibreChartedSpace j v hv (discPower j.order j.order_pos z)
    ContMDiff I₂ I₂ ω (torusFibreHomeomorph j v hv z hz) := by
  let := fillingFibreChartedSpace j v hv (discPower j.order j.order_pos z)
  exact (torusFibreBiholomorph j v hv z hz).contMDiff

theorem torusFibreHomeomorph_symm_holomorphic (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (z : Disc) (hz : (z : ℂ) ≠ 0) :
    letI := fillingFibreChartedSpace j v hv (discPower j.order j.order_pos z)
    ContMDiff I₂ I₂ ω (torusFibreHomeomorph j v hv z hz).symm := by
  let := fillingFibreChartedSpace j v hv (discPower j.order j.order_pos z)
  exact (torusFibreBiholomorph j v hv z hz).symm.contMDiff

/-- A convenient base-indexed version using the chosen root. -/
def nonzeroFibreBiholomorph (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (b : Disc) (hb : (b : ℂ) ≠ 0) :
    letI := fillingFibreChartedSpace j v hv b
    Diffeomorph I₂ I₂ ((familyPeriods j).point (fillingFibreRoot j b)).Torus
      (FillingFibre j v hv b) ω := by
  let := fillingFibreChartedSpace j v hv b
  exact EmbeddedFibre.biholomorphOfHomeomorph (nonzeroFibreHomeomorph j v hv b hb)
    (torusFibreMap_isImmersionOfComplement j v hv (fillingFibreRoot j b)).isImmersion
    (fillingFibre_inclusion_isImmersionOfComplement j v hv b).isImmersion
    (fun _ => rfl)

@[simp] theorem nonzeroFibreBiholomorph_coe (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) (hb : (b : ℂ) ≠ 0)
    (x : ((familyPeriods j).point (fillingFibreRoot j b)).Torus) :
    letI := fillingFibreChartedSpace j v hv b
    (nonzeroFibreBiholomorph j v hv b hb x : Filling j v hv) =
      torusFibreMap j v hv (fillingFibreRoot j b) x := rfl

theorem nonzero_fibre_biholomorphic_period_torus (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) (hb : (b : ℂ) ≠ 0) :
    letI := fillingFibreChartedSpace j v hv b
    ∃ z : Disc, discPower j.order j.order_pos z = b ∧
      Nonempty (Diffeomorph I₂ I₂ ((familyPeriods j).point z).Torus (FillingFibre j v hv b) ω) := by
  let := fillingFibreChartedSpace j v hv b
  exact ⟨fillingFibreRoot j b, discPower_fillingFibreRoot j b,
    ⟨nonzeroFibreBiholomorph j v hv b hb⟩⟩

/-- For the specified twist, the central fibre identification has no
remaining admissibility or period-existence hypotheses. -/
def mainCentralFibreBiholomorph (j : Kind) :
    letI := fillingFibreChartedSpace j j.twist (mainTwist_admissible j) Elliptic.discZero
    Diffeomorph I₂ I₂ (MainSurface j (centralPeriod j))
      (FillingFibre j j.twist (mainTwist_admissible j) Elliptic.discZero) ω :=
  centralFibreBiholomorph j j.twist (mainTwist_admissible j)

end Wikipedia.HopfProblem.Elliptic
