import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy
import Wikipedia.NoExoticSixSphere.OnePointProductQuotient

/-!
# Reduced suspension on the actual native cubes

The first cube coordinate runs around the one-point compactified line.
The remaining coordinates run through the original generalized loop.
The actual product-compactification quotient collapses every boundary
face. Concatenating in an old coordinate commutes with this construction
on representatives, before passing to homotopy classes.
-/

noncomputable section

open Set Function Topology
open scoped unitInterval OnePoint

namespace NoExoticSixSphere.CubicalProductSuspension

abbrev Line := EuclideanSpace ℝ (Fin 1)

def clock : C(I, OnePoint Line) :=
  (euclideanOnePointSphere 1).symm.toHomotopyEquiv.toFun.comp
    ((SmoothCube.quotient 1).comp
      ⟨fun t ↦ fun _ : Fin 1 ↦ t, continuous_pi (fun _ ↦ continuous_id)⟩)

theorem clock_zero : clock 0 = ∞ := by
  change (euclideanOnePointSphere 1).symm (SmoothCube.quotient 1 (fun _ ↦ 0)) = ∞
  rw [SmoothCube.quotient_boundary 1 _ ⟨0, Or.inl rfl⟩]
  exact (euclideanOnePointSphere 1).symm_apply_eq.mpr (euclideanOnePointSphere_infty 1).symm

theorem clock_one : clock 1 = ∞ := by
  change (euclideanOnePointSphere 1).symm (SmoothCube.quotient 1 (fun _ ↦ 1)) = ∞
  rw [SmoothCube.quotient_boundary 1 _ ⟨0, Or.inr rfl⟩]
  exact (euclideanOnePointSphere 1).symm_apply_eq.mpr (euclideanOnePointSphere_infty 1).symm

def tail {m : ℕ} (u : Fin (m + 1) → I) : Fin m → I := fun i ↦ u i.succ

theorem continuous_tail (m : ℕ) : Continuous (tail (m := m)) :=
  continuous_pi (fun i ↦ continuous_apply i.succ)

theorem tail_update_succ {m : ℕ} (u : Fin (m + 1) → I) (i : Fin m) (t : I) :
    tail (Function.update u i.succ t) = Function.update (tail u) i t := by
  funext j
  by_cases h : j = i
  · subst j
    simp [tail]
  · simp [tail, h, Fin.succ_inj]

variable {E : Type*} [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E] {m : ℕ}

def loop (p : GenLoop (Fin m) (OnePoint E) ∞) :
    GenLoop (Fin (m + 1)) (OnePoint (Line × E)) ∞ := by
  refine ⟨⟨fun u ↦ OnePointProduct.map (clock (u 0), p (tail u)), ?_⟩, ?_⟩
  · exact OnePointProduct.continuous_map.comp
      ((clock.continuous.comp (continuous_apply 0)).prodMk
        (p.val.continuous.comp (continuous_tail m)))
  · rintro u ⟨i, hi⟩
    change OnePointProduct.map (clock (u 0), p (tail u)) = ∞
    refine Fin.cases ?_ (fun j ↦ ?_) i hi
    · intro h
      rcases h with h | h
      · rw [h, clock_zero, OnePointProduct.map_infty_left]
      · rw [h, clock_one, OnePointProduct.map_infty_left]
    · intro h
      have hp : p (tail u) = ∞ := p.property (tail u) ⟨j, h⟩
      exact (congrArg (fun z ↦ OnePointProduct.map (clock (u 0), z)) hp).trans
        (OnePointProduct.map_infty_right _)

theorem loop_apply (p : GenLoop (Fin m) (OnePoint E) ∞) (u : Fin (m + 1) → I) :
    loop p u = OnePointProduct.map (clock (u 0), p (tail u)) := rfl

theorem loop_const : loop (GenLoop.const : GenLoop (Fin m) (OnePoint E) ∞) = GenLoop.const := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  exact OnePointProduct.map_infty_right _

theorem loop_transAt (p q : GenLoop (Fin m) (OnePoint E) ∞) (i : Fin m) :
    loop (GenLoop.transAt i p q) = GenLoop.transAt i.succ (loop p) (loop q) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  change OnePointProduct.map (clock (u 0),
    if (u i.succ : ℝ) ≤ 1 / 2 then
      p (Function.update (tail u) i (projIcc 0 1 zero_le_one (2 * u i.succ))) else
      q (Function.update (tail u) i (projIcc 0 1 zero_le_one (2 * u i.succ - 1)))) =
    if (u i.succ : ℝ) ≤ 1 / 2 then
      loop p (Function.update u i.succ (projIcc 0 1 zero_le_one (2 * u i.succ))) else
      loop q (Function.update u i.succ (projIcc 0 1 zero_le_one (2 * u i.succ - 1)))
  split_ifs <;>
    simp only [loop_apply, tail_update_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]

theorem loop_homotopic {p q : GenLoop (Fin m) (OnePoint E) ∞} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (loop p) (loop q) := by
  obtain ⟨H⟩ := h
  refine ⟨{
    toFun := fun z ↦ OnePointProduct.map (clock (z.2 0), H (z.1, tail z.2))
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · exact OnePointProduct.continuous_map.comp
      ((clock.continuous.comp ((continuous_apply 0).comp continuous_snd)).prodMk
        (H.continuous.comp (continuous_fst.prodMk ((continuous_tail m).comp continuous_snd))))
  · intro u
    rw [H.apply_zero]
    rfl
  · intro u
    rw [H.apply_one]
    rfl
  · rintro t u ⟨i, hi⟩
    change OnePointProduct.map (clock (u 0), H (t, tail u)) = loop p u
    apply Eq.trans (b := ∞) ?_ ((loop p).property u ⟨i, hi⟩).symm
    refine Fin.cases ?_ (fun j ↦ ?_) i hi
    · intro h
      rcases h with h | h
      · rw [h, clock_zero, OnePointProduct.map_infty_left]
      · rw [h, clock_one, OnePointProduct.map_infty_left]
    · intro h
      rw [H.eq_fst t ⟨j, h⟩, p.property (tail u) ⟨j, h⟩,
        OnePointProduct.map_infty_right]

def map : HomotopyGroup (Fin m) (OnePoint E) ∞ →
    HomotopyGroup (Fin (m + 1)) (OnePoint (Line × E)) ∞ :=
  Quotient.map loop (fun _ _ h ↦ loop_homotopic h)

theorem map_mk (p : GenLoop (Fin m) (OnePoint E) ∞) :
    map (⟦p⟧ : HomotopyGroup (Fin m) (OnePoint E) ∞) = ⟦loop p⟧ := rfl

variable [Nonempty (Fin m)]

theorem map_one : map (1 : HomotopyGroup (Fin m) (OnePoint E) ∞) = 1 := by
  rw [HomotopyGroup.one_def, map_mk, loop_const, HomotopyGroup.one_def]

theorem map_mul (x y : HomotopyGroup (Fin m) (OnePoint E) ∞) :
    map (x * y) = map x * map y := by
  let i : Fin m := Classical.choice inferInstance
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      have hpq := HomotopyGroup.mul_spec (i := i) (p := p) (q := q)
      have hLpLq := HomotopyGroup.mul_spec (i := i.succ) (p := loop p) (q := loop q)
      have hL := congrArg (fun r : GenLoop (Fin (m + 1)) (OnePoint (Line × E)) ∞ ↦
        (⟦r⟧ : HomotopyGroup (Fin (m + 1)) (OnePoint (Line × E)) ∞)) (loop_transAt q p i)
      exact (congrArg map hpq).trans (hL.trans hLpLq.symm)

def hom : HomotopyGroup (Fin m) (OnePoint E) ∞ →*
    HomotopyGroup (Fin (m + 1)) (OnePoint (Line × E)) ∞ where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul

end NoExoticSixSphere.CubicalProductSuspension
