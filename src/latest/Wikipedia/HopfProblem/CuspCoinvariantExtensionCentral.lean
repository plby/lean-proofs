import Wikipedia.HopfProblem.CuspCoinvariantExtensionCentralDescent
import Wikipedia.HopfProblem.CuspBoundaryTopVanishingPeriods

/-!
# A controlled marked-circle map on the full original closed cusp core

For every sufficiently small actual closed cusp neighborhood and every
chosen positive norm shell, the original equivariant toric deformation
gives a continuous circle map.  It restricts to the marked central
coordinate, kills all norm-one fibre phases, and equals the original
gamma period on every representative of the chosen whole shell.

The working radius is chosen before the shell.  No assertion is made
that one endpoint has the original period coordinate at all radii, or
that the original punctured coordinate extends unchanged to the centre.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

open ToricSpace CuspRetraction CuspControlledRetraction CuspCollapse CuspUniformization
open CuspBoundaryTopVanishing SpecialPeriods.CuspFamily

/-- An actual closed-core circle map with exact central, phase, and whole-shell markings.
The only input is the original holomorphic cusp data; both required small radii
and the equivariant deformation are obtained from their existing existence theorems. -/
theorem exists_closed_core_gamma (D : Data) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < D.radius ∧ η₀ < 1 ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ →
        ∀ (ρ : ℝ), 0 < ρ → ρ ≤ η →
          ∃ Rγ : C(ClosedQuotient D.correction D.radius η, AddCircle (1 : ℝ)),
            Rγ.comp (quotientCentralIntoClosed D.correction D.radius η hη.le) =
              centralGamma D.correction D.radius D.radius_pos D.holomorphic ∧
            (∀ (hηr : η < D.radius) (u : Fin 2 → ℂˣ),
              (∀ i, ‖(u i : ℂ)‖ = 1) → ∀ x : ClosedTube η,
                Rγ (closedQuotientMap D.correction hηr (closedFibreAction η u x)) =
                  Rγ (closedQuotientMap D.correction hηr x)) ∧
            (∀ (hηr : η < D.radius) (s : LogBase D.radius)
              (hsη : ‖exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄),
              ‖exponential (s : ℂ)‖ = ρ →
                Rγ (closedQuotientMap D.correction hηr
                  (periodPointPunctured D η s hsη x).1) = (x 0 : AddCircle (1 : ℝ))) := by
  obtain ⟨a, ha, har, ha1, hret⟩ :=
    exists_closed_tube_controlled_deformation D.correction D.radius_pos
      (fun i j => (D.holomorphic i j).continuousOn)
  obtain ⟨δ, hδ, _hδr, _hδ1, hbase⟩ := exists_period_base_radius D
  let η₀ := min a (δ / 2)
  have hη₀ : 0 < η₀ := lt_min ha (half_pos hδ)
  have hη₀a : η₀ ≤ a := min_le_left _ _
  have hη₀δ : η₀ < δ := (min_le_right a (δ / 2)).trans_lt (half_lt_self hδ)
  refine ⟨η₀, hη₀, hη₀a.trans_lt har, hη₀a.trans_lt ha1, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  have hηa : η ≤ a := hηη₀.trans hη₀a
  have hηr : η < D.radius := hηa.trans_lt har
  obtain ⟨H, _hzero, hfix, hone, hequiv, hfibre, _hmono, hEnd⟩ :=
    hret η hη hηa ρ hρ hρη
  let Rγ := closedCoreGamma D.correction D.radius_pos hηr D.holomorphic H hequiv hone
  refine ⟨Rγ, closedCoreGamma_comp_central D.correction D.radius_pos hηr
    D.holomorphic H hequiv hone hfix hη.le, ?_, ?_⟩
  · intro hηr' u hu x
    exact closedCoreGamma_unit_fibreAction D.correction D.radius_pos hηr D.holomorphic
      H hequiv hone hfibre u hu x
  · intro hηr' s hsη x hsρ
    let p := periodPointPunctured D η s hsη x
    have hp : ‖time (p.1 : Space)‖ = ρ := by
      change ‖time (totalExponentialPoint (periodLogCover D s x))‖ = ρ
      rw [time_totalExponentialPoint]
      exact hsρ
    have hvalue := closedCoreGamma_endpoint D.correction D.radius_pos hηr D.holomorphic
      H hequiv hone hη.le p.1 (straightenedPrescribedCollapse D.correction η p) (hEnd p hp)
    have hsδ : ‖exponential (s : ℂ)‖ < δ := (hsη.trans hηη₀).trans_lt hη₀δ
    have hmarked := congrFun (hbase η s hsδ hsη x) (0 : Fin 2)
    exact hvalue.trans hmarked

end Wikipedia.HopfProblem.CuspCoinvariantExtension
