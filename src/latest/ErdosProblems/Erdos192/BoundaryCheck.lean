import ErdosProblems.Erdos192.BoundaryMasks

namespace Erdos192

theorem v_pattern_gives_AS_normal (wa wb we : Fin 4) (r s : Fin 85)
    (h : hasParikhSolution wa wb we r.val s.val = true) :
    vGivesSomeAS wa wb we (parikhSolutionVec wa wb we r.val s.val) = true := by
  have hv := boundaryCheck_verified wa wb we r s
  simp only [hasParikhSolution, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [boundaryCheck, scalarDelta_eq, fastAdj_eq, h.1.1.1,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hv
  exact hv.1

theorem v_pattern_gives_AS_t85 (wa wb we : Fin 4) (r s : Fin 85)
    (h : hasParikhSolution wa wb we r.val s.val = true)
    (ht : (2 * s.val + 85000 - r.val) % 85 = 0) :
    vGivesSomeAS wa wb we (fun c => parikhSolutionVec wa wb we r.val s.val c +
      if c = we then 1 else 0) = true := by
  have hv := boundaryCheck_verified wa wb we r s
  simp only [hasParikhSolution, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [boundaryCheck, scalarDelta_eq, fastAdj_eq, h.1.1.1,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    ht, beq_self_eq_true] at hv
  exact hv.2

end Erdos192
