/- import Mathlib.Analysis.Asymptotics.Asymptotics -/
/- import Mathlib.Data.Fintype.BigOperators -/
/- import Mathlib.Data.List.ToFinsupp -/
/- import Mathlib.Order.SuccPred.IntervalSucc -/
import Mathlib.Tactic.SlimCheck
import Mathlib.Data.Rat.Defs

/- open Finset BigOperators Filter Asymptotics -/

set_option trace.Meta.synthInstance true
example (a : ℤ) (ha : 0 ≤ a) : 0 ≤ (a : ℚ) := by
  slim_check

example (k : ℕ) :
    (fun n ↦ (∑ i ∈ range n, (i / k : ℤ)) - n ^ 2 / (2 * k)) =O[atTop] (fun n ↦ (n : ℤ)) := by
  sorry
