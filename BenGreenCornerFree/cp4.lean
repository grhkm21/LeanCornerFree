import Mathlib.Tactic
import BenGreenCornerFree.Construction
import BenGreenCornerFree.Bridge
import BenGreenCornerFree.CornerFree

open BenGreen Construction Bridge

set_option trace.slim_check.success true
example {a : ℕ} (ha : Nat.Prime a) (ha' : 2 < a) : a % 2 = 1 := by
  slim_check
