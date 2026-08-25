import StackExchange.Puzzling139335.Definitions
import Wikipedia.SchoenfliesTheorem.Concatenate
import Mathlib.Topology.Path

/-! # Simple paths and their two-arc loops -/

open Set unitInterval

namespace Schoenflies

/-- An arc with specified endpoints admits a path parametrization injective on
the entire unit interval. -/
theorem IsArcBetween.exists_injective_path {A : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) :
    ∃ m : Path p q, Function.Injective m ∧ range m = A := by
  obtain ⟨f, hf, hfi, hfA, hf0, hf1⟩ := hA
  let m : Path p q :=
    { toFun := fun t => f t
      continuous_toFun := hf.domRestrict
      source' := hf0
      target' := hf1 }
  refine ⟨m, ?_, ?_⟩
  · intro s t hst
    exact Subtype.ext (hfi s.property t.property hst)
  · change range (fun t : I => f t) = A
    rw [← hfA]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩

end Schoenflies

namespace Puzzling139335.CentralRotation.CrosscutPaths

theorem path_injOn_extend {p q : Plane} {m : Path p q}
    (hm : Function.Injective m) : InjOn m.extend I := by
  intro s hs t ht hst
  rw [m.extend_apply hs, m.extend_apply ht] at hst
  exact congrArg Subtype.val (hm hst)

theorem path_symm_injective {p q : Plane} {m : Path p q}
    (hm : Function.Injective m) : Function.Injective m.symm :=
  hm.comp unitInterval.symm_involutive.injective

/-- Mathlib's path concatenation has exactly the same half-speed formula as
the real parametrization used by `Schoenflies.IsLoop.concatenate`. -/
theorem path_trans_extend_eq_concatenate {p q r : Plane} (m : Path p q) (n : Path q r) :
    ⇑(m.trans n).extend = Schoenflies.concatenate m.extend n.extend := by
  funext t
  by_cases ht : t ≤ 1 / 2
  · rw [Path.extend_trans_of_le_half m n ht, Schoenflies.concatenate_of_le ht]
  · rw [Path.extend_trans_of_half_le m n (le_of_lt (lt_of_not_ge ht)),
      Schoenflies.concatenate_of_not_le ht]

/-- Injective paths sharing just their two endpoints form the specified
Jordan loop under `Path.trans`, with no reparametrization choices. -/
theorem isLoop_path_trans {p q : Plane} (m : Path p q) (n : Path q p)
    (hm : Function.Injective m) (hn : Function.Injective n)
    (hmeet : ∀ z ∈ range m, z ∈ range n → z = p ∨ z = q) :
    Schoenflies.IsLoop (m.trans n).extend := by
  rw [path_trans_extend_eq_concatenate]
  refine Schoenflies.IsLoop.concatenate m.continuous_extend.continuousOn
    (path_injOn_extend hm) n.continuous_extend.continuousOn
    (path_injOn_extend hn) (by simp) (by simp) ?_
  intro z hzm hzn
  rw [m.image_extend_of_subset subset_rfl] at hzm
  rw [n.image_extend_of_subset subset_rfl] at hzn
  simpa only [Path.extend_zero, Path.extend_one] using hmeet z hzm hzn

end Puzzling139335.CentralRotation.CrosscutPaths
