import Mathlib.Tactic

example {P Q R : Prop} (hPQ : P → Q) (hQR : Q → R) :
    P → R := by
  intro p
  have := hPQ p
  exact hQR this
