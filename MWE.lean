import Mathlib
-- import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- def sum_of_squares {R : Type} [Semiring R] : List R → R
--   | [] => 0
--   | (a :: L) => (a ^ 2) + (sum_of_squares L)

-- example (a x y : ℚ) : sum_of_squares [a * x, a * y] = a ^ 2 * sum_of_squares [x, y]
--   := by simp [sum_of_squares, mul_pow, mul_add]

-- example : (π : ℝ) + (π : ℝ) = 2 * π := by ring

#check (π : ℝ)

-- #eval Real.pi + Real.pi
