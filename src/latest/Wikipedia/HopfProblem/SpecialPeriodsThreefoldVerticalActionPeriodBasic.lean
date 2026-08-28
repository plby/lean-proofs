import Wikipedia.HopfProblem.PeriodFamily

/-!
# Vertical translations on the original varying period family

The second complex coordinate is the original constant period column
`δ`.  Translation by `![0, s]` descends through the actual varying
lattice, retaining its fixed real-coordinate quotient topology.
-/

noncomputable section

open Set
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Period

/-- Translation in the original second complex period-vector coordinate. -/
def vector (s : ℂ) : ComplexPlane₂ := ![0, s]

@[simp] theorem vector_zero : vector 0 = 0 := by
  ext i
  fin_cases i <;> rfl

theorem vector_add (s t : ℂ) : vector (s + t) = vector s + vector t := by
  ext i
  fin_cases i <;> simp [vector]

theorem vector_eq_smul (s : ℂ) : vector s = s • (![0, 1] : ComplexPlane₂) := by
  ext i
  fin_cases i <;> simp [vector]

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- The literal translation before taking the period quotient. -/
def vectorFlow (s : ℂ) (x : B × ComplexPlane₂) : B × ComplexPlane₂ :=
  (x.1, x.2 + vector s)

/-- The actual descended translation, written in the family's original
real-coordinate topological trivialization. -/
def flow (s : ℂ) (x : P.TotalSpace) : P.TotalSpace :=
  (x.1, x.2 + standardLattice.mkQ ((P.periodEquiv x.1).symm (vector s)))

@[simp] theorem flow_quotientMap (s : ℂ) (x : B × ComplexPlane₂) :
    flow P s (P.quotientMap x) = P.quotientMap (vectorFlow s x) := by
  simp only [flow, HolomorphicPeriodMap.quotientMap, vectorFlow, map_add]

@[simp] theorem flow_projection (s : ℂ) (x : P.TotalSpace) :
    P.projection (flow P s x) = P.projection x := rfl

@[simp] theorem flow_zero (x : P.TotalSpace) : flow P 0 x = x := by
  simp [flow]

theorem flow_add (s t : ℂ) (x : P.TotalSpace) :
    flow P (s + t) x = flow P s (flow P t x) := by
  simp only [flow, vector_add, map_add]
  congr 1
  abel

/-- The actual last source period column is the constant vector `e₂`. -/
theorem periodEquiv_delta (b : B) :
    P.periodEquiv b (Pi.basisFun ℝ (Fin 4) 3) = (![0, 1] : ComplexPlane₂) := by
  rw [P.periodEquiv_coordinates]
  ext i
  fin_cases i <;> simp

/-- Integral times are actual lattice periods on every fibre. -/
theorem inverse_vector_int_mem (b : B) (n : ℤ) :
    (P.periodEquiv b).symm (vector (n : ℂ)) ∈ standardLattice := by
  have he : P.periodEquiv b (n • Pi.basisFun ℝ (Fin 4) 3) = vector (n : ℂ) := by
    rw [map_zsmul, periodEquiv_delta]
    ext i
    fin_cases i <;> simp [vector]
  rw [← he, LinearEquiv.symm_apply_apply]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨3, rfl⟩

@[simp] theorem flow_int_cast (n : ℤ) (x : P.TotalSpace) : flow P (n : ℂ) x = x := by
  have hz : standardLattice.mkQ ((P.periodEquiv x.1).symm (vector (n : ℂ))) = 0 :=
    (Submodule.Quotient.mk_eq_zero standardLattice).mpr (inverse_vector_int_mem P x.1 n)
  simp [flow, hz]

theorem vector_mem_lattice_iff (s : ℂ) (b : B) :
    vector s ∈ (P.point b).lattice ↔ (P.periodEquiv b).symm (vector s) ∈ standardLattice := by
  rw [← P.periodEquiv_map_lattice]
  constructor
  · rintro ⟨v, hv, he⟩
    change P.periodEquiv b v = vector s at he
    rw [← he, LinearEquiv.symm_apply_apply]
    exact hv
  · intro hv
    exact ⟨(P.periodEquiv b).symm (vector s), hv, (P.periodEquiv b).apply_symm_apply _⟩

/-- A translation fixes a fibre point exactly when its original complex
translation vector belongs to that fibre's actual period lattice. -/
theorem flow_eq_self_iff (s : ℂ) (x : P.TotalSpace) :
    flow P s x = x ↔ vector s ∈ (P.point x.1).lattice := by
  rw [vector_mem_lattice_iff]
  constructor
  · intro h
    apply (Submodule.Quotient.mk_eq_zero standardLattice).mp
    have hh := congrArg Prod.snd h
    change x.2 + standardLattice.mkQ ((P.periodEquiv x.1).symm (vector s)) = x.2 at hh
    exact add_left_cancel (hh.trans (add_zero x.2).symm)
  · intro h
    have hz := (Submodule.Quotient.mk_eq_zero standardLattice).mpr h
    simp [flow, hz]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Period
