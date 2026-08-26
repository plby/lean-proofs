import ErdosProblems.Erdos192.BoundaryMaskData

namespace Erdos192

def residue (a : Fin 4) (r : Nat) : Nat := (scalarPrefix a r % 43435).toNat

def negativeResidue (a : Fin 4) (r : Nat) : Nat := (-scalarPrefix a r % 43435).toNat

def midpointResidue (a : Fin 4) (r : Nat) : Nat := (2 * scalarPrefix a r % 43435).toNat

def candidates (a b e : Fin 4) (s : Nat) : List Nat :=
  (boundaryCandidates[a.val * 16 + b.val * 4 + e.val]!).getD s []

def maskCheck (a b e : Fin 4) (s : Fin 85) : Bool :=
  (positiveMasks[a.val]! &&&
    rotateMask 43435 negativeMasks[e.val]! (midpointResidue b s.val)) ==
      bitset ((candidates a b e s.val).map (residue a))

def candidateCheck (a b e : Fin 4) (s : Fin 85) : Bool :=
  (candidates a b e s.val).all fun r =>
    if h : r < 85 then boundaryCheck a b e ⟨r, h⟩ s else false

def masksCertificate : Bool :=
  (List.finRange 4).all fun a =>
  (List.finRange 4).all fun b =>
  (List.finRange 4).all fun e =>
  (List.finRange 85).all fun s => maskCheck a b e s && candidateCheck a b e s

theorem masksCertificate_true : masksCertificate = true := by decide +kernel

theorem masksContainPrefixes : ∀ a : Fin 4, ∀ r : Fin 85,
    positiveMasks[a.val]!.testBit (residue a r.val) = true ∧
    negativeMasks[a.val]!.testBit (negativeResidue a r.val) = true := by decide +kernel

theorem scalarPrefix_mod85 : ∀ a : Fin 4, ∀ r : Fin 85,
    scalarPrefix a r.val % 85 = (64 * (r.val : Int)) % 85 := by decide +kernel

theorem scalarPrefix_full : ∀ a : Fin 4, scalarPrefix a 85 % 43435 = 0 := by
  decide +kernel

end Erdos192
