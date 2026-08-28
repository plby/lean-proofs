import Wikipedia.NoExoticSixSphere.FiniteLoweringPrefix

/-!
# Relative homotopies with an energy cap

Concatenation preserves the original protected sublevel: on that set the
intermediate map agrees with the original map, so the next homotopy fixes it.
-/

namespace NoExoticSixSphere.FiniteControlledLowering

variable {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y]

def ControlledReachable (energy : Y → ℝ) (admissible : Set Y) (floor cap : ℝ)
    (p q : C(M, Y)) : Prop :=
  ∃ G : ContinuousMap.HomotopyRel p q {x | energy (p x) ≤ floor},
    ∀ t x, G (t, x) ∈ admissible ∧ energy (G (t, x)) ≤ cap

namespace ControlledReachable

variable {energy : Y → ℝ} {admissible : Set Y} {floor cap : ℝ} {p q r : C(M, Y)}

theorem refl (hp : ∀ x, p x ∈ admissible) (hcap : ∀ x, energy (p x) ≤ cap) :
    ControlledReachable energy admissible floor cap p p :=
  ⟨ContinuousMap.HomotopyRel.refl p _, fun _ x ↦ ⟨hp x, hcap x⟩⟩

theorem endpoint_mem (h : ControlledReachable energy admissible floor cap p q) (x : M) :
    q x ∈ admissible := by
  obtain ⟨G, hG⟩ := h
  simpa only [G.apply_one] using (hG 1 x).1

theorem endpoint_fixed (h : ControlledReachable energy admissible floor cap p q)
    {x : M} (hx : energy (p x) ≤ floor) : q x = p x := by
  obtain ⟨G, _⟩ := h
  exact (G.fst_eq_snd hx).symm

theorem trans (h : ControlledReachable energy admissible floor cap p q)
    (h' : ControlledReachable energy admissible floor cap q r) :
    ControlledReachable energy admissible floor cap p r := by
  obtain ⟨G, hG⟩ := h
  obtain ⟨J, hJ⟩ := h'
  let Jfixed : ContinuousMap.HomotopyRel q r {x | energy (p x) ≤ floor} :=
    { toHomotopy := J.toHomotopy
      prop' := fun t x hx ↦ J.eq_fst t (by
        change energy (q x) ≤ floor
        rw [← G.fst_eq_snd hx]
        exact hx) }
  refine ⟨G.trans Jfixed, ?_⟩
  intro t x
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact hG _ x
  · exact hJ _ x

end ControlledReachable

end NoExoticSixSphere.FiniteControlledLowering
