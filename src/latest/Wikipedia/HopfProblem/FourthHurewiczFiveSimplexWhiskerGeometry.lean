import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerTrack

/-!
# The universal continuous cubical whiskering map

The first output coordinate follows the rectangle track. The intermediate
coordinates stay fixed, while the last coordinate is multiplied by the
track's radial coordinate. No target space or basedness assumption enters
this map.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

/-- The actual map underlying whiskering in every dimension. -/
def whiskerMap (n : ℕ) : C((Fin (n + 1) → I) × I, Fin (n + 2) → I) where
  toFun z := Fin.cons (whiskerTrack z.2).1
    (Fin.snoc (Fin.init z.1) ((whiskerTrack z.2).2 * z.1 (Fin.last n)))
  continuous_toFun := by
    apply Continuous.finCons
    · exact (whiskerTrack.continuous.comp continuous_snd).fst
    · apply Continuous.finSnoc
      · apply continuous_pi
        intro i
        exact (continuous_apply i.castSucc).comp continuous_fst
      · apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp
          (whiskerTrack.continuous.comp continuous_snd).snd).mul
          (continuous_subtype_val.comp
            ((continuous_apply (Fin.last n)).comp continuous_fst))

@[simp] theorem whiskerMap_apply (n : ℕ) (u : Fin (n + 1) → I) (s : I) :
    whiskerMap n (u, s) = Fin.cons (whiskerTrack s).1
      (Fin.snoc (Fin.init u) ((whiskerTrack s).2 * u (Fin.last n))) := rfl

@[simp] theorem whiskerMap_first (n : ℕ) (u : Fin (n + 1) → I) (s : I) :
    whiskerMap n (u, s) 0 = (whiskerTrack s).1 := by
  simp

@[simp] theorem whiskerMap_middle (n : ℕ) (u : Fin (n + 1) → I) (s : I)
    (i : Fin n) : whiskerMap n (u, s) i.castSucc.succ = u i.castSucc := by
  simp [Fin.init]

@[simp] theorem whiskerMap_last (n : ℕ) (u : Fin (n + 1) → I) (s : I) :
    whiskerMap n (u, s) (Fin.last n).succ = (whiskerTrack s).2 * u (Fin.last n) := by
  simp

@[simp] theorem whiskerMap_start (n : ℕ) (u : Fin (n + 1) → I) :
    whiskerMap n (u, 0) = Fin.cons 0 (Fin.snoc (Fin.init u) 0) := by
  simp

@[simp] theorem whiskerMap_finish (n : ℕ) (u : Fin (n + 1) → I) :
    whiskerMap n (u, 1) = Fin.cons 1 (Fin.snoc (Fin.init u) 0) := by
  simp

/-- On the upper rectangle edge, the last cube coordinate is unchanged. -/
theorem whiskerMap_radius_one (n : ℕ) (u : Fin (n + 1) → I) (s : I)
    (hs : (whiskerTrack s).2 = 1) :
    whiskerMap n (u, s) = Fin.cons (whiskerTrack s).1 u := by
  simp [hs]

/-- The lower last-coordinate facet remains a lower last-coordinate facet. -/
theorem whiskerMap_last_zero (n : ℕ) (u : Fin (n + 1) → I) (s : I)
    (hu : u (Fin.last n) = 0) : whiskerMap n (u, s) (Fin.last n).succ = 0 := by
  simp [hu]

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
