import StackExchange.Puzzling139335.CentralRotation.CrosscutPaths.PathLoops
import StackExchange.Puzzling139335.JordanCrosscut

/-!
# Compatible boundary paths for a crosscut

All three loops use the same three simple paths: the first outer arc, the
crosscut, and the second outer arc.  In particular the two side boundaries
traverse the crosscut in opposite directions.
-/

open Set unitInterval Schoenflies

namespace Puzzling139335.CentralRotation.CrosscutPaths

/-- Concrete compatible parametrizations of a crosscut and its two outer arcs.
The existence theorem below constructs every field from a Jordan crosscut. -/
structure Data (C Γ M N : Set Plane) (p q : Plane) where
  m : Path p q
  gamma : Path q p
  n : Path q p
  m_injective : Function.Injective m
  gamma_injective : Function.Injective gamma
  n_injective : Function.Injective n
  range_m : range m = M
  range_gamma : range gamma = Γ
  range_n : range n = N
  outer_union : M ∪ N = C
  loopA_isLoop : IsLoop (m.trans gamma).extend
  loopB_isLoop : IsLoop (gamma.symm.trans n).extend
  loopU_isLoop : IsLoop (m.trans n).extend

namespace Data

variable {C Γ M N : Set Plane} {p q : Plane} (d : Data C Γ M N p q)

noncomputable def loopA : Path p p := d.m.trans d.gamma

noncomputable def loopB : Path p p := d.gamma.symm.trans d.n

noncomputable def loopU : Path p p := d.m.trans d.n

theorem range_loopA : range d.loopA = M ∪ Γ := by
  rw [loopA, Path.trans_range, d.range_m, d.range_gamma]

theorem range_loopB : range d.loopB = Γ ∪ N := by
  rw [loopB, Path.trans_range, Path.symm_range, d.range_gamma, d.range_n]

theorem range_loopU : range d.loopU = C := by
  rw [loopU, Path.trans_range, d.range_m, d.range_n, d.outer_union]

theorem loopA_extends_isLoop : IsLoop d.loopA.extend := d.loopA_isLoop

theorem loopB_extends_isLoop : IsLoop d.loopB.extend := d.loopB_isLoop

theorem loopU_extends_isLoop : IsLoop d.loopU.extend := d.loopU_isLoop

end Data

end Puzzling139335.CentralRotation.CrosscutPaths

namespace Puzzling139335.JordanCrosscut

open CentralRotation.CrosscutPaths

/-- An actual Jordan crosscut supplies the compatible three-path data. -/
theorem exists_crosscutPaths {C Γ M N : Set Plane} {p q : Plane}
    (h : JordanCrosscut C Γ p q) (hc : IsCutPair C p q M N) :
    Nonempty (Data C Γ M N p q) := by
  obtain ⟨m, hmi, hmrange⟩ := hc.fst.exists_injective_path
  obtain ⟨gamma, hgi, hgrange⟩ := h.arc.reverse.exists_injective_path
  obtain ⟨n, hni, hnrange⟩ := hc.snd.reverse.exists_injective_path
  refine ⟨{
    m := m
    gamma := gamma
    n := n
    m_injective := hmi
    gamma_injective := hgi
    n_injective := hni
    range_m := hmrange
    range_gamma := hgrange
    range_n := hnrange
    outer_union := hc.union_eq
    loopA_isLoop := ?_
    loopB_isLoop := ?_
    loopU_isLoop := ?_ }⟩
  · apply isLoop_path_trans m gamma hmi hgi
    intro z hzm hzγ
    rw [hmrange] at hzm
    rw [hgrange] at hzγ
    have hz : z ∈ ({p, q} : Set Plane) := h.inter_arc_eq hc ▸ ⟨hzγ, hzm⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using hz
  · apply isLoop_path_trans gamma.symm n (path_symm_injective hgi) hni
    intro z hzγ hzn
    rw [Path.symm_range, hgrange] at hzγ
    rw [hnrange] at hzn
    have hz : z ∈ ({p, q} : Set Plane) := h.inter_arc_eq hc.symm ▸ ⟨hzγ, hzn⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using hz
  · apply isLoop_path_trans m n hmi hni
    intro z hzm hzn
    rw [hmrange] at hzm
    rw [hnrange] at hzn
    have hz : z ∈ ({p, q} : Set Plane) := hc.inter_eq ▸ ⟨hzm, hzn⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using hz

end Puzzling139335.JordanCrosscut
