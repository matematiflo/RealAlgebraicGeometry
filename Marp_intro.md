---
marp: true
# size: 4:3
# class: invert
---

# Real Algebraic Geometry

The goal of this project is to formalise basic results of real algebraic geometry in [Lean4](https://github.com/leanprover/lean4), using resources from the [Mathlib4](https://github.com/leanprover-community/mathlib4) library and apporting to it in return.

---

## Real algebra

1. [Sums of squares](https://github.com/matematiflo/Real_Algebraic_Geometry/blob/main/Sums_of_squares/Sums_of_squares.md)
2. Formally real fields
3. Artin-Schreier theory
4. Real-closed fields
5. The real closure of an ordered field

---

### Sums of squares

Sums of squares are defined inductively, on terms of type `List R` where `R` is a semiring.

```python
def sum_of_squares {R : Type} [Semiring R] : List R → R
| [] => 0
| (a :: L) => (a ^ 2) + (sum_of_squares L)
```

Recall that lists are defined inductively themselves:  

> A list `L` is either the empty list `[]` or of the form `a :: l`, where `l` is an already defined list.

---

## Concatenated lists

The sum of squares of the list `L1 ++ L2` is equal to the sum of squares of `L1` plus the sum of squares of `L2`.

> `sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2`

```python
@[simp]
def sum_of_squares_concat {R : Type} [Semiring R] 
  (L1 L2 : List R) : sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2 
    := by
      induction L1 with 
      | nil => simp [sum_of_squares] 
      | cons a L ih =>
        simp [sum_of_squares]
        rw [ih]
        rw [add_assoc]
      done
```

---

## The real Nullstellensatz

* Real ideals
* Sturm's theorem
* The real-radical of an ideal
* Affine sets over real-closed fields
