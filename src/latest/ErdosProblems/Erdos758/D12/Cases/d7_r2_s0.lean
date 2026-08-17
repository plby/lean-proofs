import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r2_s0_raw
  (include_str "../reduced/d7_r2_s0.cnf")
  (include_str "../reduced/d7_r2_s0.lrat")

def d7_r2_s0_ids : String := include_str "../reduced/d7_r2_s0.ids"

def d7_r2_s0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, false), (18, false), (19, false), (20, false), (21, false)]

private theorem d7_r2_s0_sem_0_402 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 0, 402) := by
  exact d12CaseRangeProof(d7_r2_s0_ids, d7_r2_s0_units, edge, 0, 402)

private theorem d7_r2_s0_sem_402_804 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 402, 804) := by
  exact d12CaseRangeProof(d7_r2_s0_ids, d7_r2_s0_units, edge, 402, 804)

private theorem d7_r2_s0_sem_0_804 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 0, 804) := by
  intro h
  exact h.elim (d7_r2_s0_sem_0_402 edge) (d7_r2_s0_sem_402_804 edge)

private theorem d7_r2_s0_sem_804_1206 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 804, 1206) := by
  exact d12CaseRangeProof(d7_r2_s0_ids, d7_r2_s0_units, edge, 804, 1206)

private theorem d7_r2_s0_sem_1206_1608 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 1206, 1608) := by
  exact d12CaseRangeProof(d7_r2_s0_ids, d7_r2_s0_units, edge, 1206, 1608)

private theorem d7_r2_s0_sem_804_1608 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 804, 1608) := by
  intro h
  exact h.elim (d7_r2_s0_sem_804_1206 edge) (d7_r2_s0_sem_1206_1608 edge)

private theorem d7_r2_s0_sem_0_1608 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 0, 1608) := by
  intro h
  exact h.elim (d7_r2_s0_sem_0_804 edge) (d7_r2_s0_sem_804_1608 edge)

private theorem d7_r2_s0_sem_1608_2010 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 1608, 2010) := by
  exact d12CaseRangeProof(d7_r2_s0_ids, d7_r2_s0_units, edge, 1608, 2010)

private theorem d7_r2_s0_sem_2010_2412 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 2010, 2412) := by
  exact d12CaseRangeProof(d7_r2_s0_ids, d7_r2_s0_units, edge, 2010, 2412)

private theorem d7_r2_s0_sem_1608_2412 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 1608, 2412) := by
  intro h
  exact h.elim (d7_r2_s0_sem_1608_2010 edge) (d7_r2_s0_sem_2010_2412 edge)

private theorem d7_r2_s0_sem_2412_2814 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 2412, 2814) := by
  exact d12CaseRangeProof(d7_r2_s0_ids, d7_r2_s0_units, edge, 2412, 2814)

private theorem d7_r2_s0_sem_2814_3217 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 2814, 3217) := by
  exact d12CaseRangeProof(d7_r2_s0_ids, d7_r2_s0_units, edge, 2814, 3217)

private theorem d7_r2_s0_sem_2412_3217 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 2412, 3217) := by
  intro h
  exact h.elim (d7_r2_s0_sem_2412_2814 edge) (d7_r2_s0_sem_2814_3217 edge)

private theorem d7_r2_s0_sem_1608_3217 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 1608, 3217) := by
  intro h
  exact h.elim (d7_r2_s0_sem_1608_2412 edge) (d7_r2_s0_sem_2412_3217 edge)

private theorem d7_r2_s0_sem_0_3217 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s0_ids, d7_r2_s0_units, edge, 0, 3217) := by
  intro h
  exact h.elim (d7_r2_s0_sem_0_1608 edge) (d7_r2_s0_sem_1608_3217 edge)

theorem d7_r2_s0 (edge : Nat → Prop) : D12Outcome edge d7_r2_s0_units := by
  exact d7_r2_s0_sem_0_3217 edge (d12CaseRaw(d7_r2_s0_raw, edge))

end Erdos758.D12Certificate
