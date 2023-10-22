import Mathlib.Tactic

def sum_of_squares {R : Type} [Semiring R] : List R → R
  | [] => 0
  | (a :: L) => (a ^ 2) + (sum_of_squares L)

example (a x y : ℚ) : sum_of_squares [a * x, a * y] = a ^ 2 * sum_of_squares [x, y]
  := by simp [sum_of_squares, mul_pow, mul_add]