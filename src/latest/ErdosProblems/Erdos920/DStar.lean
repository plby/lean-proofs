import Mathlib

/-!
# Bradač's `D⋆` digraph

This file formalizes the linear-algebraic part of Lemma 2.11 of Bradač's
construction for off-diagonal Ramsey numbers.  The construction in the paper
uses projective points over a finite field.  Since orthogonality and
nonorthogonality are unchanged when a representative is multiplied by a
nonzero scalar, it is enough for the obstruction argument to work directly
with nonzero vector representatives.

The ambient vector space underlying `Vertex K t` is `K^(t+1)`.  A vertex is an
ordered pair `(x,y)` of nonzero orthogonal vectors.  There is an arc

`(x,y) → (x',y')`

exactly when `x · y' = 0` and `x' · y ≠ 0`.  The main theorem proves
that this digraph contains no injectively embedded transitive tournament on
`t+1` vertices.
-/

open Matrix

namespace Erdos920
namespace DStar

/-- A vector representative for a projective point in `PG(t,K)`. -/
abbrev Vec (K : Type*) (t : ℕ) := Fin (t + 1) → K

/-- A vertex of Bradač's `D⋆`: two nonzero orthogonal vector representatives. -/
structure Vertex (K : Type*) (t : ℕ) [Field K] where
  left : Vec K t
  right : Vec K t
  left_ne_zero : left ≠ 0
  right_ne_zero : right ≠ 0
  orthogonal : left ⬝ᵥ right = 0

/-- The arc relation in Bradač's `D⋆` digraph. -/
def Arc {K : Type*} {t : ℕ} [Field K] (u v : Vertex K t) : Prop :=
  u.left ⬝ᵥ v.right = 0 ∧ v.left ⬝ᵥ u.right ≠ 0

/-- An ordered, injective copy of the transitive tournament `T_r` in `D⋆`. -/
def HasTransitiveTournament (K : Type*) (t r : ℕ) [Field K] : Prop :=
  ∃ v : Fin r → Vertex K t, Function.Injective v ∧
    ∀ ⦃i j : Fin r⦄, i < j → Arc (v i) (v j)

/-- A finite family admitting an upper-triangular system of separating linear
functionals with nonzero diagonal is linearly independent. -/
theorem linearIndependent_of_upperTriangular_pairing
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (v : Fin n → V) (f : Fin n → V →ₗ[K] K)
    (hzero : ∀ ⦃i j : Fin n⦄, i < j → f i (v j) = 0)
    (hdiag : ∀ i : Fin n, f i (v i) ≠ 0) :
    LinearIndependent K v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcoeff : ∀ k (hk : k < n), c ⟨k, hk⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        let i : Fin n := ⟨k, hk⟩
        have hsum : ∑ j : Fin n, c j * f i (v j) = 0 := by
          calc
            ∑ j : Fin n, c j * f i (v j) =
                f i (∑ j : Fin n, c j • v j) := by
                  simp [map_sum, map_smul, smul_eq_mul]
            _ = 0 := by rw [hc]; simp
        have hsingle : c i * f i (v i) = 0 := by
          rw [← hsum]
          symm
          apply Finset.sum_eq_single i
          · intro j _ hji
            rcases lt_or_gt_of_ne hji with hji_lt | hij_lt
            · rw [ih j.val hji_lt j.isLt]
              simp
            · rw [hzero hij_lt]
              simp
          · simp
        exact (mul_eq_zero.mp hsingle).resolve_right (hdiag i)
  intro i
  exact hcoeff i.val i.isLt

/-- Dot product with a fixed vector, regarded as a linear functional. -/
def dotLeft {K : Type*} [Field K] {t : ℕ} (x : Vec K t) : Vec K t →ₗ[K] K where
  toFun y := x ⬝ᵥ y
  map_add' y z := dotProduct_add x y z
  map_smul' a y := by simp [dotProduct_smul]

@[simp]
theorem dotLeft_apply {K : Type*} [Field K] {t : ℕ} (x y : Vec K t) :
    dotLeft x y = x ⬝ᵥ y := rfl

/-- The rank obstruction at the heart of Bradač's construction.  Notice that
finiteness of the field is not needed for this part of the argument. -/
theorem transitiveTournament_impossible
    {K : Type*} [Field K] {t : ℕ}
    (v : Fin (t + 1) → Vertex K t)
    (_hinjective : Function.Injective v)
    (harc : ∀ ⦃i j : Fin (t + 1)⦄, i < j → Arc (v i) (v j)) :
    False := by
  classical
  let x : Fin (t + 1) → Vec K t := fun i ↦ (v i).left
  let y : Fin (t + 1) → Vec K t := fun i ↦ (v i).right

  have hy_last : y (Fin.last t) ≠ 0 := (v (Fin.last t)).right_ne_zero
  have hnot_all : ¬ ∀ w : Vec K t, y (Fin.last t) ⬝ᵥ w = 0 := by
    intro h
    exact hy_last (dotProduct_eq_zero _ h)
  obtain ⟨w, hw⟩ := not_forall.mp hnot_all

  let z : Fin (t + 1) → Vec K t :=
    Fin.lastCases w (fun i : Fin t ↦ x i.succ)
  let f : Fin (t + 1) → Vec K t →ₗ[K] K := fun i ↦ dotLeft (z i)

  have hzero : ∀ ⦃i j : Fin (t + 1)⦄, i < j → f i (y j) = 0 := by
    intro i j hij
    have hi_last : i ≠ Fin.last t := by
      exact ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
    obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hi_last
    have hle : k.succ ≤ j := by
      exact (Fin.castSucc_lt_iff_succ_le.mp hij)
    rcases hle.eq_or_lt with heq | hlt
    · subst j
      simpa [f, z, x, y] using (v k.succ).orthogonal
    · simpa [f, z, x, y] using (harc hlt).1

  have hdiag : ∀ i : Fin (t + 1), f i (y i) ≠ 0 := by
    intro i
    refine Fin.lastCases ?_ (fun k : Fin t ↦ ?_) i
    · simpa [f, z, y, dotProduct_comm] using hw
    · simpa [f, z, x, y] using
        (harc (Fin.castSucc_lt_succ (i := k))).2

  have hy_independent : LinearIndependent K y :=
    linearIndependent_of_upperTriangular_pairing y f hzero hdiag
  have hy_span : Submodule.span K (Set.range y) = ⊤ := by
    apply hy_independent.span_eq_top_of_card_eq_finrank
    simp

  have hx_zero_on_generators : ∀ j : Fin (t + 1), x 0 ⬝ᵥ y j = 0 := by
    intro j
    by_cases hj : j = 0
    · subst j
      exact (v 0).orthogonal
    · exact (harc (Fin.pos_iff_ne_zero.mpr hj)).1

  have hx_zero_on_all : ∀ u : Vec K t, x 0 ⬝ᵥ u = 0 := by
    have hspan_le : Submodule.span K (Set.range y) ≤ (dotLeft (x 0)).ker := by
      rw [Submodule.span_le]
      rintro u ⟨j, rfl⟩
      exact LinearMap.mem_ker.mpr (hx_zero_on_generators j)
    intro u
    have hu : u ∈ Submodule.span K (Set.range y) := by
      rw [hy_span]
      trivial
    exact LinearMap.mem_ker.mp (hspan_le hu)

  have hx0 : x 0 = 0 := dotProduct_eq_zero _ hx_zero_on_all
  exact (v 0).left_ne_zero hx0

/-- Bradač's `D⋆(t,K)` contains no transitive tournament on `t+1` vertices. -/
theorem no_transitiveTournament {K : Type*} [Field K] (t : ℕ) :
    ¬ HasTransitiveTournament K t (t + 1) := by
  rintro ⟨v, hinjective, harc⟩
  exact transitiveTournament_impossible v hinjective harc

end DStar
end Erdos920
