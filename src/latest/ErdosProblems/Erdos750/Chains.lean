import ErdosProblems.Erdos750.Basic
import ErdosProblems.Erdos780.External.SignedSphereLength

/-!
# Chains in the signed biclique complex

A face is a list of signed vertices whose opposite shores span a complete
bipartite graph. Repeated vertices are allowed in this intermediate chain
model; the coloring obstruction will normalize them in an exterior algebra.
-/

namespace Erdos750.Chains

open SourceFlags SignedSphere
open scoped BigOperators

noncomputable section

universe u v
variable {V : Type u} {W : Type v}

abbrev Signed (V : Type u) := ZMod 2 × V

def flip (x : Signed V) : Signed V := (x.1 + 1, x.2)

@[simp] lemma flip_flip (x : Signed V) : flip (flip x) = x := by
  ext
  · change x.1 + 1 + 1 = x.1
    have : (1 + 1 : ZMod 2) = 0 := by decide
    rw [add_assoc, this, add_zero]
  · rfl

def Face (G : SimpleGraph V) (l : List (Signed V)) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, a.1 ≠ b.1 → G.Adj a.2 b.2

def Good (G : SimpleGraph V) (k : ℕ) (l : List (Signed V)) : Prop :=
  Face G l ∧ l.length = k

lemma Face.sublist {G : SimpleGraph V} {l q : List (Signed V)}
    (hl : Face G l) (hq : q.Sublist l) : Face G q :=
  fun a ha b hb hab => hl a (hq.subset ha) b (hq.subset hb) hab

lemma Face.map_flip {G : SimpleGraph V} {l : List (Signed V)}
    (hl : Face G l) : Face G (l.map flip) := by
  rintro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
  exact hl x hx y hy (by simpa [flip] using hab)

lemma mapVertices_comp (f : V → W) {U : Type*} (g : W → U) (c : Chain V) :
    mapVertices g (mapVertices f c) = mapVertices (g ∘ f) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp [List.map_map]

def swap : Chain (Signed V) →ₗ[ℤ] Chain (Signed V) := mapVertices flip

@[simp] lemma swap_swap (c : Chain (Signed V)) : swap (swap c) = c := by
  change mapVertices flip (mapVertices flip c) = c
  rw [mapVertices_comp]
  have hf : flip ∘ flip = (id : Signed V → Signed V) := funext flip_flip
  rw [hf]
  exact mapVertices_id_apply c

def op (i : ℕ) : Chain (Signed V) →ₗ[ℤ] Chain (Signed V) :=
  if Odd i then swap - LinearMap.id else swap + LinearMap.id

lemma boundary_op (i : ℕ) (c : Chain (Signed V)) :
    boundary (op i c) = op i (boundary c) := by
  by_cases hi : Odd i <;>
    simp [op, hi, swap, boundary_mapVertices]

lemma op_succ_op (i : ℕ) (c : Chain (Signed V)) : op (i + 1) (op i c) = 0 := by
  rcases Nat.even_or_odd i with hi | hi
  · have hn := Nat.not_odd_iff_even.mpr hi
    simp [op, hn, hi.add_one, map_add]
  · have hn := Nat.not_odd_iff_even.mpr hi.add_one
    simp [op, hi, hn, map_sub]
    abel

lemma supported_op {G : SimpleGraph V} {k : ℕ} {c : Chain (Signed V)}
    (hc : Supported (Good G k) c) (i : ℕ) : Supported (Good G k) (op i c) := by
  have hs : Supported (Good G k) (swap c) :=
    supported_mapVertices flip (fun l hl => ⟨hl.1.map_flip, by simpa using hl.2⟩) hc
  by_cases hi : Odd i
  · simpa only [op, if_pos hi, LinearMap.sub_apply, LinearMap.id_apply] using
      supported_sub hs hc
  · simpa only [op, if_neg hi, LinearMap.add_apply, LinearMap.id_apply] using
      supported_add hs hc

/-- A finite initial segment of the integral periodic resolution in a graph. -/
def HasResolution (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ c : ℕ → Chain (Signed V),
    (∀ i ≤ d, Supported (Good G (i + 1)) (c i)) ∧
    boundary (c 0) = basis [] ∧
    ∀ i < d, boundary (c (i + 1)) = op (i + 1) (c i)

lemma resolution_cycle {d : ℕ}
    {c : ℕ → Chain (Signed V)} (hzero : boundary (c 0) = basis [])
    (hrel : ∀ i < d, boundary (c (i + 1)) = op (i + 1) (c i)) :
    boundary (op (d + 1) (c d)) = 0 := by
  rw [boundary_op]
  cases d with
  | zero => simp [hzero, op, swap]
  | succ i => rw [hrel i (by omega), op_succ_op]

def signedMap (f : V → W) (x : Signed V) : Signed W := (x.1, f x.2)

lemma signedMap_flip (f : V → W) (x : Signed V) :
    signedMap f (flip x) = flip (signedMap f x) := rfl

lemma map_op (f : V → W) (i : ℕ) (c : Chain (Signed V)) :
    mapVertices (signedMap f) (op i c) = op i (mapVertices (signedMap f) c) := by
  have hs : mapVertices (signedMap f) (swap c) =
      swap (mapVertices (signedMap f) c) := by
    simp only [swap, mapVertices_comp]
    rfl
  by_cases hi : Odd i <;> simp [op, hi, hs]

lemma HasResolution.map {G : SimpleGraph V} {H : SimpleGraph W}
    {d : ℕ} (h : HasResolution G d) (f : G →g H) : HasResolution H d := by
  obtain ⟨c, hc, hzero, hrel⟩ := h
  refine ⟨fun i => mapVertices (signedMap f) (c i), ?_, ?_, ?_⟩
  · intro i hi
    refine supported_mapVertices (signedMap f) (P := Good G (i + 1))
      (Q := Good H (i + 1)) ?_ (hc i hi)
    intro l hl
    refine ⟨?_, by simpa using hl.2⟩
    rintro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    exact f.map_adj (hl.1 x hx y hy hab)
  · rw [boundary_mapVertices, hzero, mapVertices_basis]
    rfl
  · intro i hi
    rw [boundary_mapVertices, hrel i hi, map_op]

lemma hasResolution_complete_two : HasResolution (SimpleGraph.completeGraph (Fin 2)) 1 := by
  let a : Signed (Fin 2) := (0, 0)
  let b : Signed (Fin 2) := (0, 1)
  let c : ℕ → Chain (Signed (Fin 2)) := fun i =>
    if i = 0 then basis [a] else basis [a, b] + basis [b, flip a]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · apply supported_basis
      constructor
      · simp [Face]
      · rfl
    · apply supported_add <;> apply supported_basis
      · constructor
        · simp [Face, a, b]
        · rfl
      · constructor
        · simp [Face, a, b, flip, SimpleGraph.completeGraph]
        · rfl
  · simp [c, boundaryBasis]
  · intro i hi
    have : i = 0 := by omega
    subst i
    simp [c, boundaryBasis, op, swap, map_add]

end
end Erdos750.Chains
