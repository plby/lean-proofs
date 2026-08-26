import ErdosProblems.Erdos73.ProjectiveFaceCorners

/-! The concrete selected corner switches correspond bijectively to the diagonal-tree edges. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv

def projectiveSelectedFirst {n : ℕ} (f : ProjectiveFace n) : ProjectivePort n :=
  (f, if projectiveFaceFlipped f then 1 else 0)

def projectivePortSwitch (n : ℕ) : Perm (ProjectivePort n) :=
  faceSwitchPerm (projectivePortOpposite n) projectivePortSelected
    (projectivePortOpposite_involutive n) projectivePortSelected_opposite

theorem projectivePortSwitch_involutive (n : ℕ) : Function.Involutive (projectivePortSwitch n) :=
  faceSwitch_involutive _ _ (projectivePortOpposite_involutive n) projectivePortSelected_opposite

theorem projectiveSelectedFirst_selected {n : ℕ} (f : ProjectiveFace n) :
    projectivePortSelected (projectiveSelectedFirst f) = true := by
  dsimp only [projectiveSelectedFirst, projectivePortSelected]
  cases projectiveFaceFlipped f <;> simp [quadrangleSelected]

theorem projectivePortSelected_cases {n : ℕ} {d : ProjectivePort n}
    (hd : projectivePortSelected d = true) :
    d = projectiveSelectedFirst d.1 ∨ d = projectivePortOpposite n (projectiveSelectedFirst d.1) := by
  rcases (quadrangleSelected_iff (projectiveFaceFlipped d.1) d.2).mp hd with h | h
  · exact Or.inl (Prod.ext rfl h)
  · exact Or.inr (Prod.ext rfl h)

theorem projectiveSelectedFirst_labels {n : ℕ} (hn : 2 ≤ n) (f : ProjectiveFace n) :
    projectivePortLabel hn (projectiveSelectedFirst f) = (projectiveDiagonalEnds hn f).1 ∧
      projectivePortLabel hn (projectivePortOpposite n (projectiveSelectedFirst f)) =
        (projectiveDiagonalEnds hn f).2 := by
  change projectiveFaceCorner hn f (if projectiveFaceFlipped f then 1 else 0) = _ ∧
    projectiveFaceCorner hn f (quadrangleOpposite (if projectiveFaceFlipped f then 1 else 0)) = _
  rcases f with ⟨r, c⟩ | j
  · have hr := r.isLt
    have hsmall : 1 < n := by omega
    by_cases hrow : r.val + 1 < n
    · by_cases hflip : r.val = 0 ∧ c.val % 2 = 1
      all_goals simp [projectiveFaceFlipped, projectiveFaceCorner, projectiveDiagonalEnds,
        hrow, hflip, hsmall, quadrangleOpposite, swap_apply_def, Fin.ext_iff]
    · have hflip : ¬(r.val = 0 ∧ c.val % 2 = 1) := by omega
      simp [projectiveFaceFlipped, projectiveFaceCorner, projectiveDiagonalEnds,
        hrow, hflip, quadrangleOpposite, swap_apply_def, Fin.ext_iff]
  · simp [projectiveFaceFlipped, projectiveFaceCorner, projectiveDiagonalEnds,
      quadrangleOpposite, swap_apply_def, Fin.ext_iff]

theorem projectivePortSwitch_eq_of_selected {n : ℕ} {d : ProjectivePort n}
    (hd : projectivePortSelected d = true) : projectivePortSwitch n d = projectivePortOpposite n d := by
  change (if projectivePortSelected d then projectivePortOpposite n d else d) = _
  rw [hd]
  rfl

theorem projectivePortSwitch_selected_of_ne {n : ℕ} {d : ProjectivePort n}
    (hd : projectivePortSwitch n d ≠ d) : projectivePortSelected d = true := by
  cases hh : projectivePortSelected d
  · exact False.elim (hd (by
      change (if projectivePortSelected d then projectivePortOpposite n d else d) = d
      rw [hh, if_neg Bool.false_ne_true]))
  · rfl

theorem projectiveSelected_edge {n : ℕ} (hn : 2 ≤ n) {d : ProjectivePort n}
    (hd : projectivePortSelected d = true) :
    s(projectivePortLabel hn d, projectivePortLabel hn (projectivePortOpposite n d)) =
      (projectiveDiagonalEdge hn d.1).val := by
  have hl := projectiveSelectedFirst_labels hn d.1
  rcases projectivePortSelected_cases hd with hh | hh
  · have he₁ := (congrArg (projectivePortLabel hn) hh).trans hl.1
    have he₂ := (congrArg (fun x => projectivePortLabel hn (projectivePortOpposite n x)) hh).trans hl.2
    rw [he₁, he₂]
    rfl
  · have hh' : projectivePortOpposite n d = projectiveSelectedFirst d.1 := by
      have hh' := congrArg (projectivePortOpposite n) hh
      rw [projectivePortOpposite_involutive n (projectiveSelectedFirst d.1)] at hh'
      exact hh'
    have he₁ := (congrArg (projectivePortLabel hn) hh).trans hl.2
    have he₂ := (congrArg (projectivePortLabel hn) hh').trans hl.1
    rw [he₁, he₂]
    exact Sym2.eq_swap

theorem projectivePortSwitch_adj {n : ℕ} (hn : 2 ≤ n) (d : ProjectivePort n)
    (hd : projectivePortSwitch n d ≠ d) :
    (projectiveDiagonalGraph hn).Adj (projectivePortLabel hn d)
      (projectivePortLabel hn (projectivePortSwitch n d)) := by
  have hs := projectivePortSwitch_selected_of_ne hd
  rw [projectivePortSwitch_eq_of_selected hs]
  change s(projectivePortLabel hn d, projectivePortLabel hn (projectivePortOpposite n d)) ∈
    (projectiveDiagonalGraph hn).edgeSet
  rw [projectiveSelected_edge hn hs]
  exact (projectiveDiagonalEdge hn d.1).property

theorem projectivePortSwitch_edge_cover {n : ℕ} (hn : 2 ≤ n) (u v : Fin n × Fin n)
    (huv : (projectiveDiagonalGraph hn).Adj u v) :
    ∃ d, projectivePortLabel hn d = u ∧ projectivePortLabel hn (projectivePortSwitch n d) = v := by
  obtain ⟨f, hf⟩ := projectiveDiagonalEdge_surjective hn ⟨s(u, v), huv⟩
  have he := congrArg Subtype.val hf
  change s((projectiveDiagonalEnds hn f).1, (projectiveDiagonalEnds hn f).2) = s(u, v) at he
  have hl := projectiveSelectedFirst_labels hn f
  have hs := projectiveSelectedFirst_selected f
  have hsw := projectivePortSwitch_eq_of_selected hs
  rcases Sym2.eq_iff.mp he with h | h
  · exact ⟨projectiveSelectedFirst f, hl.1.trans h.1, by rw [hsw, hl.2, h.2]⟩
  · refine ⟨projectivePortSwitch n (projectiveSelectedFirst f), ?_, ?_⟩
    · rw [hsw, hl.2, h.2]
    · rw [projectivePortSwitch_involutive n (projectiveSelectedFirst f), hl.1, h.1]

theorem projectivePortSwitch_port_unique {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (d e : ProjectivePort n) (hd : projectivePortSwitch n d ≠ d)
    (hl : projectivePortLabel hn d = projectivePortLabel hn e)
    (hr : projectivePortLabel hn (projectivePortSwitch n d) =
      projectivePortLabel hn (projectivePortSwitch n e)) : d = e := by
  have hadj := projectivePortSwitch_adj hn d hd
  have he : projectivePortSwitch n e ≠ e := by
    intro heq
    exact hadj.ne (hl.trans ((congrArg (projectivePortLabel hn) heq).symm.trans hr.symm))
  have hsd := projectivePortSwitch_selected_of_ne hd
  have hse := projectivePortSwitch_selected_of_ne he
  have hfaces : d.1 = e.1 := by
    apply (projectiveDiagonalEdge_bijective hn hnEven).injective
    apply Subtype.ext
    rw [← projectiveSelected_edge hn hsd, ← projectiveSelected_edge hn hse]
    rw [← projectivePortSwitch_eq_of_selected hsd, ← projectivePortSwitch_eq_of_selected hse, hl, hr]
  rcases d with ⟨f, i⟩
  rcases e with ⟨g, j⟩
  dsimp only at hfaces
  subst g
  exact Prod.ext rfl (projectiveFaceCorner_injective hn f hl)

end
end Erdos73
