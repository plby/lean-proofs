import Wikipedia.HopfProblem.SingularMayerVietorisFormalChains

/-!
# Linear helpers for formal cross products

The ordered formal chain modules are indexed by the number of vertices.  This
file records transport between equal indices and extensionality for bilinear
maps from two such modules.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

variable {V W M : Type*}

/-- Bilinear maps on ordered formal chains are determined by pairs of simplices. -/
theorem formalChains_bilinear_ext {n m : ℕ} [AddCommGroup M] [Module ℤ M]
    {f g : FormalChains V n →ₗ[ℤ] FormalChains W m →ₗ[ℤ] M}
    (h : ∀ v w, f (formalSimplex v) (formalSimplex w) =
      g (formalSimplex v) (formalSimplex w)) : f = g := by
  apply formalChains_ext
  intro v
  apply formalChains_ext
  exact h v

theorem formalChains_bilinear_ext_iff {n m : ℕ} [AddCommGroup M] [Module ℤ M]
    {f g : FormalChains V n →ₗ[ℤ] FormalChains W m →ₗ[ℤ] M} :
    f = g ↔ ∀ v w, f (formalSimplex v) (formalSimplex w) =
      g (formalSimplex v) (formalSimplex w) := by
  constructor
  · rintro rfl
    intros
    rfl
  · exact formalChains_bilinear_ext

/-- Extend a function on pairs of ordered simplices linearly in each argument. -/
def formalBilinearLift {n m : ℕ} [AddCommGroup M] [Module ℤ M]
    (f : (Fin n → V) → (Fin m → W) → M) :
    FormalChains V n →ₗ[ℤ] FormalChains W m →ₗ[ℤ] M :=
  formalLift fun v => formalLift (f v)

@[simp] theorem formalBilinearLift_simplex {n m : ℕ} [AddCommGroup M] [Module ℤ M]
    (f : (Fin n → V) → (Fin m → W) → M) (v : Fin n → V) (w : Fin m → W) :
    formalBilinearLift f (formalSimplex v) (formalSimplex w) = f v w := by
  simp [formalBilinearLift]

/-- Transport an ordered formal chain along an equality of vertex counts. -/
def formalCast {n m : ℕ} (h : n = m) : FormalChains V n →ₗ[ℤ] FormalChains V m := by
  subst m
  exact LinearMap.id

@[simp] theorem formalCast_rfl {n : ℕ} :
    formalCast (V := V) (rfl : n = n) = LinearMap.id := rfl

@[simp] theorem formalCast_apply_rfl {n : ℕ} (c : FormalChains V n) :
    formalCast rfl c = c := rfl

@[simp] theorem formalCast_comp {n m l : ℕ} (h : n = m) (k : m = l) :
    (formalCast (V := V) k).comp (formalCast h) = formalCast (h.trans k) := by
  subst m
  subst l
  rfl

@[simp] theorem formalCast_trans {n m l : ℕ} (h : n = m) (k : m = l)
    (c : FormalChains V n) :
    formalCast k (formalCast h c) = formalCast (h.trans k) c := by
  subst m
  subst l
  rfl

@[simp] theorem formalCast_simplex {n m : ℕ} (h : n = m) (v : Fin n → V) :
    formalCast h (formalSimplex v) =
      formalSimplex (fun i => v (Fin.cast h.symm i)) := by
  subst m
  rfl

/-- Vertex maps commute with transport of the vertex count. -/
@[simp] theorem formalMap_formalCast (f : V → W) {n m : ℕ} (h : n = m)
    (c : FormalChains V n) :
    formalMap f m (formalCast h c) = formalCast h (formalMap f n c) := by
  subst m
  rfl

/-- The boundary commutes with transport of the vertex count. -/
@[simp] theorem formalBoundary_formalCast {n m : ℕ} (h : n = m)
    (c : FormalChains V (n + 1)) :
    formalBoundary m (formalCast (congrArg Nat.succ h) c) =
      formalCast h (formalBoundary n c) := by
  subst m
  rfl

/-- Coning commutes with transport of the vertex count. -/
@[simp] theorem formalCone_formalCast (a : V) {n m : ℕ} (h : n = m)
    (c : FormalChains V n) :
    formalCone a m (formalCast h c) =
      formalCast (congrArg Nat.succ h) (formalCone a n c) := by
  subst m
  rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
