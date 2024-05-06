import Mathlib.Tactic.SlimCheck
import Mathlib.Data.Rat.Defs

example (a : ℤ) (ha : 0 ≤ a) : 0 ≤ (a : ℚ) := by
  slim_check
