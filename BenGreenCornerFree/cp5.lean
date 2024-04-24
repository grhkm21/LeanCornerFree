import Mathlib.Tactic

example {a b : ℤ} : ((a - b + 1) / b : ℚ) ≤ (a / b : ℤ) := by
  slim_check (config := { numInst := 1000, maxSize := 1000 })
