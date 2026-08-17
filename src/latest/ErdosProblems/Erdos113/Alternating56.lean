import ErdosProblems.Erdos113.Cycles

open scoped SimpleGraph

namespace Erdos113Alternating56

open Erdos113Cycles

def halfIndex (p : Fin 56) : Fin 28 := ⟨p.val / 2, by omega⟩

def evenIndex (i : Fin 28) : Fin 56 := ⟨2 * i.val, by omega⟩

def oddIndex (i : Fin 28) : Fin 56 := ⟨2 * i.val + 1, by omega⟩

def alternatingTuple {V : Type*} (x y : Fin 28 → V) : Fin 56 → V :=
  fun p ↦ if p.val % 2 = 0 then x (halfIndex p) else y (halfIndex p)

@[simp] lemma halfIndex_evenIndex (i : Fin 28) : halfIndex (evenIndex i) = i := by
  apply Fin.ext
  simp [halfIndex, evenIndex]

@[simp] lemma halfIndex_oddIndex (i : Fin 28) : halfIndex (oddIndex i) = i := by
  apply Fin.ext
  simp only [halfIndex, oddIndex]
  omega

@[simp] lemma alternatingTuple_even {V : Type*} (x y : Fin 28 → V)
    (i : Fin 28) : alternatingTuple x y (evenIndex i) = x i := by
  rw [alternatingTuple, if_pos (by simp [evenIndex]), halfIndex_evenIndex]

@[simp] lemma alternatingTuple_odd {V : Type*} (x y : Fin 28 → V)
    (i : Fin 28) : alternatingTuple x y (oddIndex i) = y i := by
  rw [alternatingTuple, if_neg (by simp [oddIndex]), halfIndex_oddIndex]

lemma evenIndex_halfIndex_of_even (p : Fin 56) (hp : p.val % 2 = 0) :
    evenIndex (halfIndex p) = p := by
  apply Fin.ext
  simp only [evenIndex, halfIndex]
  omega

lemma oddIndex_halfIndex_of_odd (p : Fin 56) (hp : p.val % 2 ≠ 0) :
    oddIndex (halfIndex p) = p := by
  apply Fin.ext
  simp only [oddIndex, halfIndex]
  have hp' : p.val % 2 = 1 := by omega
  omega

lemma evenIndex_add_one (i : Fin 28) : evenIndex i + 1 = oddIndex i := by
  apply Fin.ext
  rw [Fin.val_add_eq_of_add_lt]
  · simp [evenIndex, oddIndex]
  · simp [evenIndex]
    omega

lemma oddIndex_add_one (i : Fin 28) : oddIndex i + 1 = evenIndex (i + 1) := by
  apply Fin.ext
  simp only [oddIndex, evenIndex]
  change (2 * i.val + 1 + 1) % 56 = 2 * ((i.val + 1) % 28)
  omega

lemma alternatingTuple_injective {V : Type*} {x y : Fin 28 → V}
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hdisj : ∀ i j, x i ≠ y j) :
    Function.Injective (alternatingTuple x y) := by
  intro p q hpq
  by_cases hp : p.val % 2 = 0
  · by_cases hq : q.val % 2 = 0
    · have hix : x (halfIndex p) = x (halfIndex q) := by
        simpa [alternatingTuple, hp, hq] using hpq
      rw [← evenIndex_halfIndex_of_even p hp,
        ← evenIndex_halfIndex_of_even q hq, hx hix]
    · exact False.elim (hdisj (halfIndex p) (halfIndex q) (by
        simpa [alternatingTuple, hp, hq] using hpq))
  · by_cases hq : q.val % 2 = 0
    · exact False.elim (hdisj (halfIndex q) (halfIndex p) (by
        simpa [alternatingTuple, hp, hq] using hpq.symm))
    · have hiy : y (halfIndex p) = y (halfIndex q) := by
        simpa [alternatingTuple, hp, hq] using hpq
      rw [← oddIndex_halfIndex_of_odd p hp,
        ← oddIndex_halfIndex_of_odd q hq, hy hiy]

lemma alternatingTuple_hom {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x y : Fin 28 → V)
    (hxy : ∀ i, G.Adj (x i) (y i))
    (hyx : ∀ i, G.Adj (y i) (x (i + 1))) :
    IsHomCycle G (alternatingTuple x y) := by
  intro p
  by_cases hp : p.val % 2 = 0
  · rw [← evenIndex_halfIndex_of_even p hp, evenIndex_add_one]
    simpa using hxy (halfIndex p)
  · rw [← oddIndex_halfIndex_of_odd p hp, oddIndex_add_one]
    simpa using hyx (halfIndex p)

lemma alternatingTuple_genuine {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x y : Fin 28 → V)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hdisj : ∀ i j, x i ≠ y j)
    (hxy : ∀ i, G.Adj (x i) (y i))
    (hyx : ∀ i, G.Adj (y i) (x (i + 1))) :
    IsGenuineCycle G (alternatingTuple x y) :=
  ⟨alternatingTuple_injective hx hy hdisj,
    alternatingTuple_hom G x y hxy hyx⟩

lemma alternatingTuple_pair_injective {V : Type*} :
    Function.Injective (fun p : (Fin 28 → V) × (Fin 28 → V) ↦
      alternatingTuple p.1 p.2) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  apply Prod.ext
  · funext i
    have hi := congrFun h (evenIndex i)
    simpa using hi
  · funext i
    have hi := congrFun h (oddIndex i)
    simpa using hi

end Erdos113Alternating56
