import ErdosProblems.Erdos192.ScalarData

namespace Erdos192

def fastDelta (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  (fastPrefix wb 85 c : Int) - fastPrefix wb s c +
  fastPrefix we ((2 * s + 85000 - r) % 85) c - fastPrefix we 0 c -
  ((fastPrefix wa 85 c : Int) - fastPrefix wa r c) -
  ((fastPrefix wb s c : Int) - fastPrefix wb 0 c)

def fastAdj (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  let d := fastDelta wa wb we r s
  match c with
  | 0 => -701 * d 0 + (-531) * d 1 + 4059 * d 2 + (-2316) * d 3
  | 1 => (-2316) * d 0 + (-701) * d 1 + (-531) * d 2 + 4059 * d 3
  | 2 => 4059 * d 0 + (-2316) * d 1 + (-701) * d 2 + (-531) * d 3
  | 3 => (-531) * d 0 + 4059 * d 1 + (-2316) * d 2 + (-701) * d 3

theorem fastDelta_eq (wa wb we : Fin 4) (r s : Fin 85) (c : Fin 4) :
    fastDelta wa wb we r.val s.val c = boundaryDelta wa wb we r.val s.val c := by
  unfold fastDelta boundaryDelta sliceParikhCount
  simp only [prefixData_correct wa ⟨85, by decide⟩ c,
    prefixData_correct wb ⟨85, by decide⟩ c,
    prefixData_correct wb ⟨s.val, by omega⟩ c,
    prefixData_correct wa ⟨r.val, by omega⟩ c,
    prefixData_correct wb ⟨0, by decide⟩ c,
    prefixData_correct we ⟨0, by decide⟩ c,
    prefixData_correct we ⟨(2 * s.val + 85000 - r.val) % 85, by omega⟩ c]
  ring

theorem fastAdj_eq (wa wb we : Fin 4) (r s : Fin 85) (c : Fin 4) :
    fastAdj wa wb we r.val s.val c = adjMTtimesDelta wa wb we r.val s.val c := by
  fin_cases c <;> simp only [fastAdj, adjMTtimesDelta, fastDelta_eq]

def scalarDelta (wa wb we : Fin 4) (r s : Nat) : Int :=
  scalarPrefix wb 85 - scalarPrefix wa 85 + scalarPrefix wa r +
    scalarPrefix we ((2 * s + 85000 - r) % 85) - 2 * scalarPrefix wb s

theorem scalarDelta_eq (wa wb we : Fin 4) (r s : Fin 85) :
    scalarDelta wa wb we r.val s.val = fastAdj wa wb we r.val s.val 0 := by
  unfold scalarDelta
  rw [scalarData_correct wb ⟨85, by decide⟩, scalarData_correct wa ⟨85, by decide⟩,
    scalarData_correct wa ⟨r.val, by omega⟩,
    scalarData_correct we ⟨(2 * s.val + 85000 - r.val) % 85, by omega⟩,
    scalarData_correct wb ⟨s.val, by omega⟩]
  have hz : ∀ a c : Fin 4, fastPrefix a 0 c = 0 := by decide +kernel
  simp only [fastAdj, fastDelta, hz, Nat.cast_zero, sub_zero]
  ring

def boundaryCheck (wa wb we : Fin 4) (r s : Fin 85) : Bool :=
  let a := fastAdj wa wb we r.val s.val
  if scalarDelta wa wb we r.val s.val % 43435 != 0 then true else
    let v := fun c => a c / 43435
    vGivesSomeAS wa wb we v &&
      (if (2 * s.val + 85000 - r.val) % 85 == 0 then
        vGivesSomeAS wa wb we (fun c => v c + if c = we then 1 else 0)
       else true)

end Erdos192
