import ErdosProblems.Erdos73.Foundations

/-! Retain any desired initial number of cycles in a canonical integral packing. -/

namespace Erdos73

open SimpleGraph

def cycleUnionTakeCopy (ns : List ℕ) (p : ℕ) :
    (cycleUnionGraph (ns.take p)).Copy (cycleUnionGraph ns) := by
  induction p generalizing ns with
  | zero =>
    exact {
      toHom := {
        toFun := Empty.elim
        map_rel' := by
          intro x
          exact Empty.elim x }
      injective' := by
        intro x
        exact Empty.elim x }
  | succ p ih =>
    cases ns with
    | nil =>
      exact {
        toHom := {
          toFun := Empty.elim
          map_rel' := by
            intro x
            exact Empty.elim x }
        injective' := by
          intro x
          exact Empty.elim x }
    | cons n ns =>
      let f := ih ns
      let ident : cycleGraph n →g cycleGraph n := {
        toFun := id
        map_rel' := fun h => h }
      exact {
        toHom := Hom.sum ident f.toHom
        injective' := Sum.map_injective.mpr ⟨fun _ _ h => h, f.injective⟩ }

theorem HasOddCyclePacking.mono {V : Type*} {G : SimpleGraph V} {p k : ℕ}
    (hpack : HasOddCyclePacking k G) (hpk : p ≤ k) : HasOddCyclePacking p G := by
  obtain ⟨ns, hn, ho, ⟨f⟩⟩ := hpack
  refine ⟨ns.take p, by rw [List.length_take, hn, Nat.min_eq_left hpk],
    (fun n h => ho n (List.mem_of_mem_take h)), ⟨f.comp (cycleUnionTakeCopy ns p)⟩⟩

end Erdos73
