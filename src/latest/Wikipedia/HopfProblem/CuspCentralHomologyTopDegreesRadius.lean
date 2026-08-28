import Wikipedia.HopfProblem.CuspCentralHomologyFibreRadius

/-!
# The central specialization of the actual fibre radius comparison

This is the level-zero case of the already constructed
representative-preserving homeomorphism of literal fibres. It permits
an admissible smaller radius to be chosen without replacing the central
fibre occurring in a homology statement.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open CuspRetraction

def centralRadiusHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ)
    (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hδ : 0 < δ) : QuotientCentralFibre C δ ≃ₜ QuotientCentralFibre C r :=
  fibreRadiusHomeomorph C r δ 0 hδr hC (by simpa only [norm_zero] using hδ)

end Wikipedia.HopfProblem.CuspCentralHomology
