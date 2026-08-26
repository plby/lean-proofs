import ErdosProblems.Erdos192.Core

namespace Erdos192

def cumParikhCount (a : Fin 4) (k : Nat) (c : Fin 4) : Nat :=
  ((keranenG a).take k).count c

def sliceParikhCount (a : Fin 4) (lo hi : Nat) (c : Fin 4) : Int :=
  (cumParikhCount a hi c : Int) - (cumParikhCount a lo c : Int)

def boundaryDelta (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  let t := (2 * s + 85 * 1000 - r) % 85
  sliceParikhCount wb s 85 c + sliceParikhCount we 0 t c
  - sliceParikhCount wa r 85 c - sliceParikhCount wb 0 s c

def adjMTtimesDelta (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  let d : Fin 4 → Int := boundaryDelta wa wb we r s
  match c with
  | 0 => -701 * d 0 + (-531) * d 1 + 4059 * d 2 + (-2316) * d 3
  | 1 => (-2316) * d 0 + (-701) * d 1 + (-531) * d 2 + 4059 * d 3
  | 2 => 4059 * d 0 + (-2316) * d 1 + (-701) * d 2 + (-531) * d 3
  | 3 => (-531) * d 0 + 4059 * d 1 + (-2316) * d 2 + (-701) * d 3

def parikhSolutionVec (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  adjMTtimesDelta wa wb we r s c / 43435

/-- Helper: check if solution exists (divisibility) -/
def hasParikhSolution (wa wb we : Fin 4) (r s : Nat) : Bool :=
  adjMTtimesDelta wa wb we r s 0 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 1 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 2 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 3 % 43435 = 0

def vGivesSomeAS (wa wb we : Fin 4) (v : Fin 4 → Int) : Bool :=
  ((List.finRange 4).all fun c => (if c = wa then (1:Int) else 0) - (if c = wb then 1 else 0) + v c == 0) ||
  ((List.finRange 4).all fun c => v c + (if c = wb then (1:Int) else 0) - (if c = we then 1 else 0) == 0) ||
  ((List.finRange 4).all fun c => v c - (if c = wb then (1:Int) else 0) == 0) ||
  ((List.finRange 4).all fun c => v c + (if c = wb then (1:Int) else 0) == 0) ||
  ((List.finRange 4).all fun c => (if c = wa then (1:Int) else 0) - (if c = wb then 1 else 0) - (if c = we then 1 else 0) + v c == 0) ||
  ((List.finRange 4).all fun c => (if c = wa then (1:Int) else 0) + (if c = wb then 1 else 0) + v c - (if c = we then 1 else 0) == 0)

end Erdos192
