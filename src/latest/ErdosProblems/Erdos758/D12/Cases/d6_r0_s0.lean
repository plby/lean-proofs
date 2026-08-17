import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r0_s0_raw
  (include_str "../reduced/d6_r0_s0.cnf")
  (include_str "../reduced/d6_r0_s0.lrat")

def d6_r0_s0_ids : String := include_str "../reduced/d6_r0_s0.ids"

def d6_r0_s0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, false), (13, false), (14, false), (15, false), (16, false), (17, false), (18, false), (19, false), (20, false), (21, false)]

private theorem d6_r0_s0_sem_0_320 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s0_ids, d6_r0_s0_units, edge, 0, 320) := by
  exact d12CaseRangeProof(d6_r0_s0_ids, d6_r0_s0_units, edge, 0, 320)

private theorem d6_r0_s0_sem_320_640 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s0_ids, d6_r0_s0_units, edge, 320, 640) := by
  exact d12CaseRangeProof(d6_r0_s0_ids, d6_r0_s0_units, edge, 320, 640)

private theorem d6_r0_s0_sem_0_640 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s0_ids, d6_r0_s0_units, edge, 0, 640) := by
  intro h
  exact h.elim (d6_r0_s0_sem_0_320 edge) (d6_r0_s0_sem_320_640 edge)

private theorem d6_r0_s0_sem_640_960 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s0_ids, d6_r0_s0_units, edge, 640, 960) := by
  exact d12CaseRangeProof(d6_r0_s0_ids, d6_r0_s0_units, edge, 640, 960)

private theorem d6_r0_s0_sem_960_1280 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s0_ids, d6_r0_s0_units, edge, 960, 1280) := by
  exact d12CaseRangeProof(d6_r0_s0_ids, d6_r0_s0_units, edge, 960, 1280)

private theorem d6_r0_s0_sem_640_1280 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s0_ids, d6_r0_s0_units, edge, 640, 1280) := by
  intro h
  exact h.elim (d6_r0_s0_sem_640_960 edge) (d6_r0_s0_sem_960_1280 edge)

private theorem d6_r0_s0_sem_0_1280 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s0_ids, d6_r0_s0_units, edge, 0, 1280) := by
  intro h
  exact h.elim (d6_r0_s0_sem_0_640 edge) (d6_r0_s0_sem_640_1280 edge)

theorem d6_r0_s0 (edge : Nat → Prop) : D12Outcome edge d6_r0_s0_units := by
  exact d6_r0_s0_sem_0_1280 edge (d12CaseRaw(d6_r0_s0_raw, edge))

end Erdos758.D12Certificate
