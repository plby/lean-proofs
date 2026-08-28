import Wikipedia.HopfProblem.PeriodTorusFirstHomologyPeriodDomain
import Wikipedia.HopfProblem.FirstHurewiczTrianglePaths
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Genuine normalized lifts of singular simplices on a period torus

Choose a representative of each torus point, with zero represented by zero.
Every actual singular simplex has a unique lift to the covering vector
space taking its first vertex to the selected representative. Existence
uses the actual quotient covering and the convexity of the standard
simplex. Comparing these lifts is a consequence of covering uniqueness.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCover

open FirstHurewicz

/-- A representative of every actual torus point, normalized at the origin. -/
def vertexLift (p : PeriodDomain) (x : p.Torus) : ComplexPlane₂ := by
  classical
  exact if x = 0 then 0 else (p.lattice.mkQ_surjective x).choose

@[simp] theorem vertexLift_zero (p : PeriodDomain) : vertexLift p 0 = 0 := by
  simp [vertexLift]

/-- The selected representative lies over the given point. -/
@[simp] theorem vertexLift_projection (p : PeriodDomain) (x : p.Torus) :
    p.lattice.mkQ (vertexLift p x) = x := by
  classical
  by_cases hx : x = 0
  · simp [vertexLift, hx]
  · simpa [vertexLift, hx] using (p.lattice.mkQ_surjective x).choose_spec

/-- The standard simplex is locally path connected by its real convexity. -/
theorem simplex_locallyPathConnected (n : ℕ) : LocallyPathConnectedSpace (Simplex n) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).locallyPathConnectedSpace

/-- Actual covering-space lifting of a singular simplex, with any specified
lift of its first vertex. -/
theorem existsUnique_simplexLift (p : PeriodDomain) {n : ℕ}
    (σ : SingularSimplex p.Torus n) (z : ComplexPlane₂)
    (hz : p.lattice.mkQ z = σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1)))) :
    ∃! Γ : C(Simplex n, ComplexPlane₂),
      Γ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))) = z ∧
        p.lattice.mkQ ∘ Γ = σ := by
  let := simplex_simplyConnected n
  let := simplex_locallyPathConnected n
  exact p.quotientCovering.isCoveringMap.existsUnique_continuousMap_lifts σ
    (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))) z hz

/-- The genuine simplex lift normalized at the selected first-vertex representative. -/
def simplexLift (p : PeriodDomain) {n : ℕ} (σ : SingularSimplex p.Torus n) :
    C(Simplex n, ComplexPlane₂) :=
  (existsUnique_simplexLift p σ
    (vertexLift p (σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1)))))
    (vertexLift_projection p _)).choose

@[simp] theorem simplexLift_vertex_zero (p : PeriodDomain) {n : ℕ}
    (σ : SingularSimplex p.Torus n) :
    simplexLift p σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))) =
      vertexLift p (σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1)))) :=
  (existsUnique_simplexLift p σ _ (vertexLift_projection p _)).choose_spec.1.1

/-- Pointwise projection of the actual normalized lift. -/
@[simp] theorem simplexLift_projection (p : PeriodDomain) {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n) :
    p.lattice.mkQ (simplexLift p σ s) = σ s :=
  congr_fun (existsUnique_simplexLift p σ _
    (vertexLift_projection p _)).choose_spec.1.2 s

/-- A normalized continuous lift is the selected lift, by actual covering uniqueness. -/
theorem simplexLift_unique (p : PeriodDomain) {n : ℕ}
    (σ : SingularSimplex p.Torus n) (Γ : C(Simplex n, ComplexPlane₂))
    (hΓ : p.lattice.mkQ ∘ Γ = σ)
    (h0 : Γ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))) =
      vertexLift p (σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))))) :
    Γ = simplexLift p σ :=
  (existsUnique_simplexLift p σ _ (vertexLift_projection p _)).choose_spec.2 Γ ⟨h0, hΓ⟩

/-- Any actual lift differs from the normalized lift by the constant
translation forced by its first vertex. -/
theorem simplexLift_eq_translate (p : PeriodDomain) {n : ℕ}
    (σ : SingularSimplex p.Torus n) (Γ : C(Simplex n, ComplexPlane₂))
    (hΓ : p.lattice.mkQ ∘ Γ = σ) (s : Simplex n) :
    simplexLift p σ s = Γ s +
      vertexLift p (σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1)))) -
        Γ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))) := by
  let Γ' : C(Simplex n, ComplexPlane₂) :=
    ⟨fun t => Γ t +
      vertexLift p (σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1)))) -
        Γ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))),
      (Γ.continuous.add continuous_const).sub continuous_const⟩
  have hproj : p.lattice.mkQ ∘ Γ' = σ := by
    funext t
    change p.lattice.mkQ (Γ t + vertexLift p (σ _) - Γ _) = σ t
    have hl (u : Simplex n) : p.lattice.mkQ (Γ u) = σ u := congr_fun hΓ u
    rw [map_sub, map_add, vertexLift_projection, hl, hl]
    abel
  have hfirst : Γ' (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))) =
      vertexLift p (σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1)))) := by
    dsimp [Γ']
    abel
  exact (congrArg (fun f : C(Simplex n, ComplexPlane₂) => f s)
    (simplexLift_unique p σ Γ' hproj hfirst)).symm

/-- A face lift is the restriction of the simplex lift translated to its
own chosen first-vertex representative. -/
theorem simplexLift_face (p : PeriodDomain) {n : ℕ}
    (σ : SingularSimplex p.Torus (n + 1)) (i : Fin (n + 2)) (s : Simplex n) :
    simplexLift p (σ.comp (simplexFace n i)) s =
      simplexLift p σ (simplexFace n i s) +
        vertexLift p (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (0 : Fin (n + 1))))) -
          simplexLift p σ (stdSimplex.vertex (S := ℝ) (i.succAbove (0 : Fin (n + 1)))) := by
  have hproj : p.lattice.mkQ ∘ ((simplexLift p σ).comp (simplexFace n i)) =
      σ.comp (simplexFace n i) := by
    funext t
    exact simplexLift_projection p σ (simplexFace n i t)
  simpa only [ContinuousMap.comp_apply, simplexFace_vertex] using
    simplexLift_eq_translate p (σ.comp (simplexFace n i))
      ((simplexLift p σ).comp (simplexFace n i)) hproj s

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCover
