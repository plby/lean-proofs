import ErdosProblems.Erdos19.VizingStar

/-! # Rotating a fan and coloring its last spoke -/

namespace Erdos19.Vizing.Fan

open Finset

variable {V K : Type*} [Fintype V] {G : SimpleGraph V}
  {C : PartialColoring V K} {x y : V} {n : ℕ}

def rotationValues (F : Fan G C x y n) (a : K) : Fin (n + 1) → Option K :=
  Fin.lastCases (some a) (fun i : Fin n ↦ C s(x, F.vert i.succ))

@[simp] theorem rotationValues_last (F : Fan G C x y n) (a : K) :
    F.rotationValues a (Fin.last n) = some a := Fin.lastCases_last ..

@[simp] theorem rotationValues_castSucc (F : Fan G C x y n) (a : K) (i : Fin n) :
    F.rotationValues a i.castSucc = C s(x, F.vert i.succ) := Fin.lastCases_castSucc ..

theorem rotationValues_isSome (F : Fan G C x y n) (a : K) (i : Fin (n + 1)) :
    (F.rotationValues a i).isSome := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp
  · obtain ⟨b, hb, _⟩ := F.step j
    simp [hb]

theorem rotation_proper (F : Fan G C x y n) (hC : IsProper G C) (a : K)
    (hax : Missing G C x a) (halast : Missing G C (F.vert (Fin.last n)) a) :
    IsProper G (F.recolorWith (F.rotationValues a)) := by
  apply F.recolorWith_proper _ hC
  · intro i j b
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
      refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · intro _ _
      rfl
    · intro hi hj
      simp only [rotationValues_last, Option.some.injEq] at hi
      rw [← hi] at hj
      exact (hax (F.vert j.succ) (F.adj j.succ)
        (by simpa only [rotationValues_castSucc] using hj)).elim
    · intro hi hj
      simp only [rotationValues_last, Option.some.injEq] at hj
      rw [← hj] at hi
      exact (hax (F.vert i.succ) (F.adj i.succ)
        (by simpa only [rotationValues_castSucc] using hi)).elim
    · intro hi hj
      simp only [rotationValues_castSucc] at hi hj
      have hverts := hC (F.adj i.succ) (F.adj j.succ) hi hj
      exact congrArg Fin.castSucc (Fin.succ_inj.mp (F.injective hverts))
  · intro i b
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · intro h
      have hab : a = b := Option.some.inj (by simpa using h)
      exact hab ▸ halast
    · intro h
      obtain ⟨b₀, hb₀, hmissing⟩ := F.step j
      have hb : b₀ = b := Option.some.inj (hb₀.symm.trans
        (by simpa only [rotationValues_castSucc] using h))
      exact hb ▸ hmissing
  · intro i v b hv hxv
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · intro h hcolor
      have hab : a = b := Option.some.inj (by simpa using h)
      exact hax v hxv (hab ▸ hcolor)
    · intro h hcolor
      have hspoke : C s(x, F.vert j.succ) = some b := by
        simpa only [rotationValues_castSucc] using h
      exact hv ⟨j.succ, hC (F.adj j.succ) hxv hspoke hcolor⟩

/-- If every replaced spoke becomes colored and the first was uncolored,
the number of colored graph edges strictly increases. -/
theorem recolorWith_increases (F : Fan G C x y n)
    (values : Fin (n + 1) → Option K) (hvalues : ∀ i, (values i).isSome)
    (hzero : C s(x, y) = none) :
    (coloredEdges G C).card < (coloredEdges G (F.recolorWith values)).card := by
  classical
  have hsub : coloredEdges G C ⊆ coloredEdges G (F.recolorWith values) := by
    intro e he
    obtain ⟨heG, heC⟩ := (mem_coloredEdges G C e).mp he
    apply (mem_coloredEdges G (F.recolorWith values) e).mpr
    refine ⟨heG, ?_⟩
    by_cases hspoke : ∃ i, s(x, F.vert i) = e
    · obtain ⟨i, rfl⟩ := hspoke
      rw [F.recolorWith_spoke]
      exact hvalues i
    · have hsame : F.recolorWith values e = C e := Function.extend_apply' values C e hspoke
      simpa only [hsame] using heC
  have hnew : s(x, F.vert 0) ∈ coloredEdges G (F.recolorWith values) := by
    apply (mem_coloredEdges G (F.recolorWith values) _).mpr
    refine ⟨F.adj 0, ?_⟩
    rw [F.recolorWith_spoke]
    exact hvalues 0
  have hold : s(x, F.vert 0) ∉ coloredEdges G C := by
    simp [mem_coloredEdges, F.first, hzero]
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq ↦ hold (heq.symm ▸ hnew)⟩

theorem exists_rotation_improvement (F : Fan G C x y n) (hC : IsProper G C)
    (hzero : C s(x, y) = none) (a : K) (hax : Missing G C x a)
    (halast : Missing G C (F.vert (Fin.last n)) a) :
    ∃ D : PartialColoring V K, IsProper G D ∧ (coloredEdges G C).card < (coloredEdges G D).card :=
  ⟨F.recolorWith (F.rotationValues a), F.rotation_proper hC a hax halast,
    F.recolorWith_increases _ (F.rotationValues_isSome a) hzero⟩

/-- Every initial segment of a fan is itself a fan. -/
def initialSegment (F : Fan G C x y n) (j : Fin (n + 1)) : Fan G C x y j.val where
  vert i := F.vert (Fin.castLE (Nat.succ_le_of_lt j.isLt) i)
  injective := by
    intro i k hik
    apply Fin.ext
    exact congrArg (fun t : Fin (n + 1) ↦ t.val) (F.injective hik)
  first := by simpa using F.first
  adj i := F.adj _
  step i := F.step ⟨i.val, i.isLt.trans_le (Nat.le_of_lt_succ j.isLt)⟩

@[simp] theorem initialSegment_last (F : Fan G C x y n) (j : Fin (n + 1)) :
    (F.initialSegment j).vert (Fin.last j.val) = F.vert j := by
  apply congrArg F.vert
  exact Fin.ext rfl

#print axioms rotation_proper
#print axioms exists_rotation_improvement
#print axioms initialSegment

end Erdos19.Vizing.Fan
