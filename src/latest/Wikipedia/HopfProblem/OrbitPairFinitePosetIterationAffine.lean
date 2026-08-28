import Wikipedia.HopfProblem.OrbitPairFinitePosetIteration

/-!
# Affine coordinates of the actual iterated subdivision homeomorphisms

At each subdivision, a face vertex is sent to the mean of its previous
vertices. The geometric map obtained from the native homeomorphisms agrees
exactly with these recursively defined vertex positions on every simplex.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder
open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open FirstHurewicz RealizationSimplex AffineCoordinates Subdivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineValue_chainDistribution (P : Type u) [PartialOrder P] [Fintype P]
    (v : P → E) (A : NonemptyFiniteChains P) :
    affineValue v (chainDistribution P A) = faceMean v A.finset := by
  classical
  let : Nonempty A.finset := A.nonempty.to_subtype
  change affineValue v (stdSimplex.map (Subtype.val : A.finset → P)
    stdSimplex.barycenter) = _
  rw [affineValue_map]
  change (∑ i : A.finset, (Fintype.card A.finset : ℝ)⁻¹ • v i.val) = _
  rw [← Finset.smul_sum, Fintype.card_coe]
  unfold faceMean
  congr 1
  exact Finset.sum_coe_sort A.finset v

theorem affineValue_subdivisionHomeomorph (P : Type u) [PartialOrder P] [Fintype P]
    [Fintype (NonemptyFiniteChains P)] (v : P → E)
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    affineValue v (coordinates P (subdivisionHomeomorph P z)) =
      affineValue (fun A : NonemptyFiniteChains P ↦ faceMean v A.finset)
        (coordinates (NonemptyFiniteChains P) z) := by
  obtain ⟨k, x, t, rfl⟩ := exists_characteristic (nerve (NonemptyFiniteChains P)) z
  refine (congrArg (affineValue v) (coordinates_subdivisionMap P _)).trans ?_
  refine (congrArg (affineValue v) (subdivisionCoordinates_characteristic P k x t)).trans ?_
  refine (affineValue_weighted v (fun i ↦ chainDistribution P (x.obj i)) t).trans ?_
  have hv : (fun i : Fin (k + 1) ↦ affineValue v (chainDistribution P (x.obj i))) =
      (fun i ↦ faceMean v (x.obj i).finset) :=
    funext (fun i ↦ affineValue_chainDistribution P v (x.obj i))
  refine (congrArg (fun a ↦ affineValue a t) hv).trans ?_
  exact (affineValue_map x.obj (fun A : NonemptyFiniteChains P ↦ faceMean v A.finset) t).symm.trans
    (congrArg (affineValue (fun A : NonemptyFiniteChains P ↦ faceMean v A.finset))
      (coordinates_characteristic (NonemptyFiniteChains P) k x t).symm)

def iteratedVertices (P : PartOrd.{u}) (v : P → E) (r : ℕ) :
    ((iteratedChains r).obj P) → E := by
  induction r with
  | zero => exact v
  | succ r w =>
    exact fun A : NonemptyFiniteChains ((iteratedChains r).obj P) ↦ faceMean w A.finset

theorem iteratedVertices_zero (P : PartOrd.{u}) (v : P → E) (p : P) :
    iteratedVertices P v 0 p = v p := rfl

theorem iteratedVertices_succ (P : PartOrd.{u}) (v : P → E) (r : ℕ)
    (A : NonemptyFiniteChains ((iteratedChains r).obj P)) :
    iteratedVertices P v (r + 1) A = faceMean (iteratedVertices P v r) A.finset := rfl

def iterationAffineMap (P : PartOrd.{u}) [Finite P] (v : P → E) (r : ℕ) :
    C(SSet.toTop.obj (nerve ((iteratedChains r).obj P)), E) := by
  letI : Fintype P := Fintype.ofFinite P
  exact (affineMap v).comp ((coordinates P).comp
    ⟨iterationHomeomorph P r, (iterationHomeomorph P r).continuous⟩)

theorem iterationAffineMap_coordinates (P : PartOrd.{u}) [Finite P] (v : P → E) (r : ℕ)
    (z : SSet.toTop.obj (nerve ((iteratedChains r).obj P))) :
    iterationAffineMap P v r z =
      letI : Fintype ((iteratedChains r).obj P) := Fintype.ofFinite _
      affineValue (iteratedVertices P v r) (coordinates ((iteratedChains r).obj P) z) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    letI : Fintype P := Fintype.ofFinite P
    letI : Fintype ((iteratedChains r).obj P) := Fintype.ofFinite _
    letI : Fintype (NonemptyFiniteChains ((iteratedChains r).obj P)) := Fintype.ofFinite _
    have h := @affineValue_subdivisionHomeomorph E _ _ ((iteratedChains r).obj P) _
      (Fintype.ofFinite _) (Fintype.ofFinite _) (iteratedVertices P v r) z
    change iterationAffineMap P v r (subdivisionHomeomorph ((iteratedChains r).obj P) z) = _
    exact (ih (subdivisionHomeomorph ((iteratedChains r).obj P) z)).trans h

theorem iterationAffineMap_characteristic (P : PartOrd.{u}) [Finite P]
    (v : P → E) (r k : ℕ) (x : (nerve ((iteratedChains r).obj P)) _⦋k⦌)
    (t : Simplex k) :
    iterationAffineMap P v r (characteristic (nerve ((iteratedChains r).obj P)) k x t) =
      affineValue (fun i ↦ iteratedVertices P v r (x.obj i)) t := by
  letI : Fintype ((iteratedChains r).obj P) := Fintype.ofFinite _
  exact (iterationAffineMap_coordinates P v r _).trans
    ((congrArg (affineValue (iteratedVertices P v r))
      (coordinates_characteristic ((iteratedChains r).obj P) k x t)).trans
        (affineValue_map x.obj (iteratedVertices P v r) t))

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
