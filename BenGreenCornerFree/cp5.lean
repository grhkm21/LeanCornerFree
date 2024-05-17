import Mathlib.Tactic

open Filter

example : Tendsto (fun x : ℝ ↦ 1 / x) atTop (nhds 0) := by
  sorry
