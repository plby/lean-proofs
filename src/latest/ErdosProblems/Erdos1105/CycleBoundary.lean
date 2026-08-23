import ErdosProblems.Erdos1105.CycleInsertion
import ErdosProblems.Erdos1105.PrivateColors

namespace Erdos1105

open SimpleGraph

/-- The first structural consequence of private colors: all edges from an
external vertex to a rainbow private cycle have one color, provided one of
these edges starts with a color outside the cycle palette. -/
theorem private_cycle_boundary_constant {V C : Type*} {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (v : Fin (n + 3) ↪ V)
    (hb : Function.Injective (fun i : Fin (n + 3) ↦ extendColor c s(v i, v (i + 1))))
    (hprivate : ∀ i, ∃ w, PrivateAt c w
      (c ((completeCopy (cycleGraph (n + 3)) v).mapEdgeSet (cycleEdge n i))))
    (u : V) (hu : u ∉ Set.range v)
    (hzero : ∀ j, extendColor c s(u, v 0) ≠ extendColor c s(v j, v (j + 1))) :
    ∀ i, extendColor c s(u, v i) = extendColor c s(u, v 0) := by
  let a : Fin (n + 3) → Option C := fun i ↦ extendColor c s(u, v i)
  let b : Fin (n + 3) → Option C := fun i ↦ extendColor c s(v i, v (i + 1))
  let e (i : Fin (n + 3)) : (⊤ : SimpleGraph V).edgeSet :=
    (completeCopy (cycleGraph (n + 3)) v).mapEdgeSet (cycleEdge n i)
  have huv (i : Fin (n + 3)) : u ≠ v i := fun h ↦ hu ⟨i, h.symm⟩
  have hue (i : Fin (n + 3)) : u ∉ (e i).val := by
    change u ∉ s(v i, v (i + 1))
    simp only [Sym2.mem_iff, not_or]
    exact ⟨huv i, huv (i + 1)⟩
  have hpriv (i j : Fin (n + 3)) (h : a i = b j) : PrivateAt c (v i) (c (e j)) :=
    privateAt_of_external_color_collision c (e j) (hprivate j) u (v i) (hue j) (huv i) h
  have hincident (i j : Fin (n + 3)) (h : a i = b j) : i = j ∨ i = j + 1 := by
    have hm := hpriv i j h (e j) rfl
    change v i ∈ s(v j, v (j + 1)) at hm
    exact (Sym2.mem_iff.mp hm).imp (fun h ↦ v.injective h) (fun h ↦ v.injective h)
  have hunique (i j : Fin (n + 3)) (hi : a i = b j) :
      ∀ t, i ≠ t → a i ≠ a t := by
    intro t hit heq
    have ht : c ⟨s(u, v t), huv t⟩ = c (e j) := by
      apply Option.some.inj
      rw [← extendColor_edge c ⟨s(u, v t), huv t⟩, ← extendColor_edge c (e j)]
      exact heq.symm.trans hi
    have hm := hpriv i j hi ⟨s(u, v t), huv t⟩ ht
    change v i ∈ s(u, v t) at hm
    rcases Sym2.mem_iff.mp hm with h | h
    · exact huv i h.symm
    · exact hit (v.injective h)
  apply cyclic_boundary_constant a b hb _ _ _ hzero
  · intro i
    let w : Fin (n + 3) ↪ V :=
      { toFun := fun j ↦ v (j + (i + 1))
        inj' := fun j k h ↦ add_right_cancel (v.injective h) }
    have hw (j : Fin (n + 3)) :
        extendColor c s(w j, w (j + 1)) = b (j + (i + 1)) := by
      change extendColor c s(v (j + (i + 1)), v ((j + 1) + (i + 1))) =
        extendColor c s(v (j + (i + 1)), v ((j + (i + 1)) + 1))
      rw [show (j + 1) + (i + 1) = (j + (i + 1)) + 1 by abel]
    have hwb : Function.Injective
        (fun j : Fin (n + 3) ↦ extendColor c s(w j, w (j + 1))) := by
      intro j k h
      simp only [hw] at h
      exact add_right_cancel (hb h)
    have huw : u ∉ Set.range w := by
      rintro ⟨j, hj⟩
      exact hu ⟨j + (i + 1), hj⟩
    have hfirst : w 0 = v (i + 1) := by
      change v (0 + (i + 1)) = v (i + 1)
      rw [zero_add]
    have hlast : w (Fin.last (n + 2)) = v i := by
      change v (Fin.last (n + 2) + (i + 1)) = v i
      congr 1
      have hlast1 : (Fin.last (n + 2) : Fin (n + 3)) + 1 = 0 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_last, Fin.val_one, Fin.val_zero]
        exact Nat.mod_self (n + 3)
      calc
        _ = (Fin.last (n + 2) + 1) + i := by abel
        _ = i := by rw [hlast1, zero_add]
    have hmid (j : Fin (n + 2)) :
        extendColor c s(w j.castSucc, w j.succ) = b (j.castSucc + (i + 1)) := by
      have hs : (j.castSucc : Fin (n + 3)) + 1 = j.succ := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_castSucc, Fin.val_succ, Fin.val_one]
        exact Nat.mod_eq_of_lt (by omega)
      rw [← hs, hw]
    have hidx (j : Fin (n + 2)) : (j.castSucc : Fin (n + 3)) + (i + 1) ≠ i := by
      intro h
      have heq : (j.castSucc : Fin (n + 3)) + 1 = 0 := by
        exact add_right_cancel (show (j.castSucc + 1) + i = 0 + i from calc
          _ = j.castSucc + (i + 1) := by abel
          _ = i := h
          _ = 0 + i := (zero_add i).symm)
      have hv := congrArg Fin.val heq
      simp only [Fin.val_add, Fin.val_castSucc, Fin.val_one, Fin.val_zero] at hv
      rw [Nat.mod_eq_of_lt (by omega)] at hv
      omega
    have hcollision := cycle_cons_collision c hH w hwb u huw
    rw [hfirst, hlast, show s(v i, u) = s(u, v i) from Sym2.eq_swap] at hcollision
    change a (i + 1) = a i ∨ _ ∨ _ at hcollision
    rcases hcollision with h | ⟨j, hj⟩ | ⟨j, hj⟩
    · exact .inl h.symm
    · rw [hmid] at hj
      rcases hincident (i + 1) _ hj with heq | heq
      · exact .inr (.inr (by simpa only [← heq] using hj))
      · exact (hidx j (add_right_cancel heq).symm).elim
    · rw [hmid] at hj
      rcases hincident i _ hj with heq | heq
      · exact (hidx j heq.symm).elim
      · refine .inr (.inl ?_)
        have heq' : j.castSucc + (i + 1) = i - 1 := by
          exact eq_sub_iff_add_eq.mpr heq.symm
        simpa only [heq'] using hj
  · intro i hi
    exact hunique i i hi (i + 1) (by simp)
  · intro i hi
    apply hunique i (i - 1) hi (i - 1)
    intro h
    have h' := congrArg (fun j : Fin (n + 3) ↦ j + 1) h
    simp only [sub_add_cancel] at h'
    simp at h'

/-- For a private representative, an edge from outside a `(k-1)`-cycle
forces all edges to the cycle to have its color, private to the external vertex. -/
theorem private_representative_cycle_boundary {V C : Type*} {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (f : (cycleGraph (n + 3)).Copy R) (u : V) (hu : u ∉ Set.range f)
    (hadj : R.Adj u (f 0)) :
    (∀ i, extendColor c s(u, f i) = extendColor c s(u, f 0)) ∧
      PrivateAt c u (c ⟨s(u, f 0), hadj.ne⟩) := by
  let v : Fin (n + 3) ↪ V := ⟨f, f.injective⟩
  have hcycle : Function.Injective
      (fun i : Fin (n + 3) ↦ extendColor c s(v i, v (i + 1))) := by
    have h := (isRainbow_cycle_iff_pairColors
      ((Copy.ofLE R ⊤ le_top).comp f) c).mp
      (isRainbow_comp_of_color_injOn le_top c hR f)
    exact h
  have hprivate : ∀ i, ∃ w, PrivateAt c w
      (c ((completeCopy (cycleGraph (n + 3)) v).mapEdgeSet (cycleEdge n i))) :=
    fun i ↦ howned (f.mapEdgeSet (cycleEdge n i))
  have huv (i : Fin (n + 3)) : u ≠ f i := fun h ↦ hu ⟨i, h.symm⟩
  have hzero : ∀ j, extendColor c s(u, v 0) ≠ extendColor c s(v j, v (j + 1)) := by
    intro j heq
    have he := hR (show s(u, f 0) ∈ R.edgeSet from hadj)
      (f.mapEdgeSet (cycleEdge n j)).property heq
    have hm : u ∈ (f.mapEdgeSet (cycleEdge n j)).val := by
      rw [← he]
      simp
    change u ∈ s(f j, f (j + 1)) at hm
    exact (Sym2.mem_iff.mp hm).elim (huv j) (huv (j + 1))
  have hconst := private_cycle_boundary_constant c hH v hcycle hprivate u hu hzero
  refine ⟨hconst, ?_⟩
  obtain ⟨w, hw⟩ := howned ⟨s(u, f 0), hadj⟩
  have hmem : w = u ∨ w = f 0 := Sym2.mem_iff.mp (hw ⟨s(u, f 0), hadj.ne⟩ rfl)
  rcases hmem with rfl | rfl
  · exact hw
  · have hraw : c ⟨s(u, f 1), huv 1⟩ = c ⟨s(u, f 0), hadj.ne⟩ := by
      apply Option.some.inj
      rw [← extendColor_edge c ⟨s(u, f 1), huv 1⟩,
        ← extendColor_edge c ⟨s(u, f 0), hadj.ne⟩]
      exact hconst 1
    have hm : f 0 = u ∨ f 0 = f 1 :=
      Sym2.mem_iff.mp (hw ⟨s(u, f 1), huv 1⟩ hraw)
    rcases hm with hm | hm
    · exact (huv 0 hm.symm).elim
    · have hi : (0 : Fin (n + 3)) = 1 := f.injective hm
      exact (zero_ne_one hi).elim

end Erdos1105
