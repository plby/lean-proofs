import ErdosProblems.Erdos73.ProjectivePortRecovery

/-! The explicit map across an alpha-side edge to its beta-side occurrence. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def projectiveAcrossFace {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    ProjectivePort n → ProjectivePort n
  | (Sum.inl (r, c), i) =>
    if hp : (r.val + c.val) % 2 = 0 then
      if i.val < 2 then
        if hr : 0 < r.val then
          (Sum.inl (⟨r.val - 1, by have hh := r.isLt; omega⟩, c), if i = 0 then 3 else 2)
        else
          (Sum.inl (⟨n - 1, by omega⟩, ⟨n - 2 - c.val, by omega⟩), if i = 0 then 2 else 3)
      else
        if hr : r.val + 1 < n then
          (Sum.inl (⟨r.val + 1, hr⟩, c), if i = 2 then 1 else 0)
        else
          (Sum.inl (⟨0, by omega⟩, ⟨n - 2 - c.val, by omega⟩), if i = 2 then 0 else 1)
    else
      if i = 0 ∨ i = 3 then
        if hc : 0 < c.val then
          (Sum.inl (r, ⟨c.val - 1, by have hh := c.isLt; omega⟩), if i = 0 then 1 else 2)
        else
          (Sum.inr ⟨(r.val - 1) / 2, by have hh := r.isLt; omega⟩, if i = 0 then 1 else 2)
      else
        if hc : c.val + 2 < n then
          (Sum.inl (r, ⟨c.val + 1, by omega⟩), if i = 1 then 0 else 3)
        else if hr : r.val + 1 < n then
          (Sum.inr ⟨(n + r.val - 1) / 2, by have hh := c.isLt; omega⟩,
            if i = 1 then 1 else 2)
        else
          (Sum.inr ⟨n - 2, by omega⟩, if i = 1 then 3 else 0)
  | (Sum.inr j, i) =>
    if i.val < 2 then
      if hj : j.val = 0 then
        (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩), if i = 0 then 0 else 3)
      else
        (Sum.inr ⟨j.val - 1, by have hh := j.isLt; omega⟩, if i = 0 then 0 else 3)
    else
      if hj : 2 * j.val + 2 < n then
        (Sum.inl (⟨2 * j.val + 2, hj⟩, ⟨0, by omega⟩), if i = 2 then 0 else 3)
      else
        (Sum.inl (⟨2 * j.val + 2 - n, by have hh := j.isLt; omega⟩, ⟨n - 2, by omega⟩),
          if i = 2 then 1 else 2)

end
end Erdos73
