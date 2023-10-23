/-
# Sums of squares

Copyright (c) 2023 Matematiflo. All rights reserved.  
Released under Apache 2.0 license as described in the file LICENSE.  
Authors: Florent Schaffhauser
-/

import Mathlib.Data.List.Perm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.BigOperators.Lemmas
-- import Mathlib.GroupTheory.GroupAction.BigOperators
-- import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.ProdSigma

/-!
We introduce sums of squares and prove some of their basic properties.

The basic setup is that of a general semiring `R`. For example, we can consider sums of squares of natural numbers (`R = ℕ`).

For some results, we specialize to rings or fields.

> **Convention.** The notation `ih` in proofs by induction is meant to signify *induction hypothesis*.

## Definition and examples

Sums of squares are defined inductively, on terms of type `List R` where `R` is a semiring (recall that lists are defined inductively themselves: a list `L` is either empty or of the form `a :: l`, where `l` is an already defined list). 
-/

def sum_of_squares {R : Type} [Semiring R] : List R → R
  | [] => 0
  | (a :: L) => (a ^ 2) + (sum_of_squares L)

/-!
Note that the definition is computable. In particular, simple equalities can be proved using `rfl`.
-/

#eval sum_of_squares [1, -2, 3] -- 14
#eval sum_of_squares ([] : List ℕ) -- 0

example : sum_of_squares [1, -2, 3] = 14 := rfl -- the two terms are definitionally equal

#eval sum_of_squares (0 :: [1, -2, 3])
#eval sum_of_squares ([1, -2, 3] ++ [1, -2, 3])

example : sum_of_squares ([1, -2, 3] ++ (0 :: [1, -2, 3])) = 28 := rfl

/-!
## Computations

For greater efficiency in computations, we can also give a tail-recursive definition. 

We start with the definition of an auxiliary function. Note that this is closer to how a human would compute a finite sum (of squares).
-/

def sum_of_squares_aux {R : Type} [Semiring R] (SoFar : R) : List R → R
  | [] => SoFar
  | (a :: l) => sum_of_squares_aux (SoFar + a ^ 2) l

/-!
Alternative syntax for the auxiliary function
-/

def sum_of_squares_aux2 {R : Type} [Semiring R] : R → List R → R
  | SoFar, [] => SoFar
  | SoFar, (a :: l) => sum_of_squares_aux (SoFar + a ^ 2) l

/-!
The tail-recursive version of the `sum_of_squares` function.
-/

def sum_of_squares_TR {R : Type} [Semiring R] : List R → R
  | L => sum_of_squares_aux 0 L

#eval sum_of_squares_TR [1, -2, 3]

/-!
`sum_of_squares L` can also be computed by squaring the members of the list and summing the resulting list.
-/

theorem squaring_and_summing {R : Type} [Semiring R] 
  (L : List R) : (L.map (. ^ 2)).sum = sum_of_squares L
    := by
      induction L with -- we prove the result by induction on the list L (the list type is an inductive type)
      | nil => rfl -- case when L is the empty list, the two terms are definitionally equal
      | cons a l ih => simp [sum_of_squares, ih] -- case when L = (a :: l), the two terms reduce to equal ones after some simplifications
      done

/-!
This is also computable.
-/

#eval (List.map (. ^ 2) [1, -2, 3]).sum

/-!
The next result formalizes a property that one would like to denote by `(c • L).sum = c * L.sum`, meaning that the sum of the list ontained by multiplying each member of `L` by `c` is equal to `c` times the sum of `L`.

**--> DEFINE THE LIST `c • L` SOMEWHERE AND PROVE `mul_sum` USING THIS NOTATION!!!**

*This needs to be done in the following way: if `R` has a `mul`, then `List R` has an `smul`.
-/

theorem mul_sum {R : Type} [Semiring R] (L : List R) (c : R) : List.sum (List.map (c * .) L) = c * List.sum L
  := by
    induction L with -- the proof is by induction on `L`
    | nil => simp -- the case of the empty list reduces to `0 = 0`
    | cons _ _ ih => simp [mul_add, ih] -- the case `L = (a :: l) follows from `c * (a + l.sum) = c * a + c * l.sum` and the induction hypothesis
    done

/-!
Combining `squaring_and_summing` and `mul_sum`, we can prove the following property, which says that `sum_of_squares (c • L) = c ^ 2 * sum_of_squares L`. 

This will be proven again in the section on [Multiplicative properties](#multiplicative-properties). There, we will present a proof by induction, more similar to the proof of `mul_sum` above.

Note that for this result we assume that `R` is a *commutative* semiring (so that we can use [`mul_pow`]()).
-/

theorem mul_sum_sq {R : Type} [CommSemiring R] (L : List R) (c : R) : 
sum_of_squares (L.map (c * .)) = c ^ 2 * sum_of_squares L
  := by
    simp [← squaring_and_summing, ← mul_sum] -- we reduce the statement to an equality between two sums of lists
    have aux : ((fun x => x ^ 2) ∘ fun x => c * x) = ((fun x => c ^ 2 * x) ∘ fun x => x ^ 2) 
      := by simp [Function.funext_iff, mul_pow] -- we prove an auxiliary result that implies that the two lists are in fact equal
    rw [aux] -- by incorporating `aux`, the result is proved: the sums of two equal lists are equal
    done

/-!
## Concatenated lists

The sum of squares of the list `L1 ++ L2` is equal to the sum of squares of `L1` plus the sum of squares of `L2`.

> `sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2`
-/

theorem sum_of_squares_concat {R : Type} [Semiring R] 
  (L1 L2 : List R) : sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2 
    := by
      induction L1 with -- we prove the result by induction on the list L1
      | nil => -- case when L1 is the empty list
        simp [sum_of_squares] -- [] ++ L2 = L2 so everything follows by definition of sum_of_squares
      | cons a L ih => -- case when L1 = (a :: L)
        simp [sum_of_squares] -- (a :: L) ++ L2 = a :: (L ++ L2) and sum_of_squares (a :: (L ++ L2)) = a ^ 2  + sum_of_squares (L ++ L2)
        rw [ih] -- ih : sum_of_squares (L ++ L2) = sum_of_squares L + sum_of_squares L2
        rw [add_assoc] -- the two terms are now equal up to associativity of addition
      done

/-!
## Permuted lists

A sum of squares is invariant under permutations:

> `L1 ~ L2 → sum_of_squares L1 = sum_of_squares L2`.
-/

theorem sum_of_squares_permut {R : Type} [Semiring R] {L1 L2 : List R} 
  (H : L1 ~ L2) : sum_of_squares L1 = sum_of_squares L2 
    := by
      induction H -- we prove the result by induction on ~ (recall that the permutation type is an inductive type: L2 is a permutation of L1 if and only if one of four cases occurs)
      · case nil => -- case when L1 L2 are both empty
        rfl -- equality holds by definition
      · case cons x l1 l2 Hl Sum12 => -- case when L1 = (x :: l1) and L2 = (x :: l2) with l1 ~ l2
        simp [sum_of_squares] -- by definition, sum_of_squares (x :: lj) = x ^ 2  + sum_of_squares lj for j = 1, 2
        rw [Sum12] -- by induction, sum_of_squares l1 = sum_of_squares l2
      · case swap x y L => -- case when L1 = (y :: (x :: L)) and L2 = (x :: (y :: L))
        simp [sum_of_squares] -- by definition, sum_of_squares (y :: (x :: L)) = y ^ 2  + (x ^ 2  + sum_of_squares L)
        rw [← add_assoc, ← add_assoc, add_comm (y ^ 2) (x ^ 2)] -- the two expressions are equal in R
      · case trans l1 L l2 H1 H2 Sum1 Sum2 => -- case when L1 ~ L and L ~ L2
        rw [Sum1, Sum2] -- by induction sum_of_squares L1 = sum_of_squares L and sum_of_squares L = sum_of_squares L2
      done

/-!
## Erasing a member

If a term `a : R` is a member of a list `L : List R`, then we can compute `sum_of_squares L` from `a` and `sum_of_squares (L.erase a)` in the following way.

In order to be able to use the function `List.erase`, we assume that the semiring `R` has decidable equality. Recall that `L.erase a` can be used as notation for `List.erase L a`.
-/

theorem sum_of_squares_erase {R : Type} [Semiring R] [DecidableEq R] 
  (L : List R) (a : R) (h : a ∈ L) : sum_of_squares L = a ^ 2 + sum_of_squares (L.erase a) 
    := by
      change sum_of_squares L = sum_of_squares (a :: (L.erase a)) -- we can replace the goal with a *definitionally equal* one
      have H : L ~ (a :: (L.erase a)) := L.perm_cons_erase h -- this is the Mathlib proof that L ~ (a :: (L.erase a))
      rw [sum_of_squares_permut H] -- since we ha ve a proof that L ~ (a :: (L.erase a)), we can use the sum_of_squares_permut function that we defined earlier to conclude that the two sums of squares are equal
      done

/-!
## Multiplicative properties

The first result says that if you multiply every member of a list `L : List R` by a constant `c : R`, then the sum of squares of the new list is equal to `c ^ 2 * sum_of_squares L`.

In order to be able to apply lemmas such as `mul_pow` in the proof, we assume here that the semiring `R` is commutative.

We take a look at a few examples first.
-/

#eval sum_of_squares [2 * 1, 2 * ( -2), 2 * 3] -- 56 
#eval 4 * sum_of_squares [1, -2, 3] -- 56

example : sum_of_squares [2 * 1, 2 * ( -2), 2 * 3] = 4 * sum_of_squares [1, -2, 3] := rfl

example (a x y : ℚ) : sum_of_squares [a * x, a * y] = a ^ 2 * sum_of_squares [x, y]
  := by simp [sum_of_squares, mul_pow, mul_add]
    
theorem sum_of_squares_of_list_mul {R : Type} [CommSemiring R] 
  (L : List R) (c : R) : sum_of_squares (L.map (c * .)) = c ^ 2 * sum_of_squares L 
    := by
      induction L with -- again an induction on L
      | nil => simp [sum_of_squares] -- the case of the empty list is trivial
      | cons a _ ih => simp [sum_of_squares, ih, mul_add, mul_pow] -- the case of a list of the form (a :: l) follows from simplifications and the use of the induction hypothesis
      done

theorem sum_of_squares_of_list_div {F : Type} [Semifield F] 
  (L : List F) (c : F) : sum_of_squares (L.map (. / c)) = (1 / c ^ 2) * sum_of_squares L 
    := by -- this will be an application of sum_of_squares_of_list_mul, using the fact that . / c = . * c⁻¹
      have aux : (fun x => x / c) = (fun x => c⁻¹ * x) 
        := by field_simp
      simp [aux, sum_of_squares_of_list_mul] -- If we had added `sum_of_squares_of_list_mul` to `simp`, we would not need to include it here (see also the golfed version below)
      done

/-!
## Being a sum of squares (existential)

If `R` is a semiring, we can define what it means for a term `x` of type `R` to be a sum of squares.

The definition means that `x : R` is a sum of squares if we can prove that there exists a list `L : List R` such that the sum of squares of members of that list is equal to `x`.
-/

def is_sum_of_squares {R : Type} [Semiring R] (x : R) : Prop := ∃ L : List R, sum_of_squares L = x

/-!
Let us give basic examples of sums of squares in a semiring `R`.

We first prove that `0` and `1` are sums of squares in `R`. More generally, if `x : R`, then `x ^ 2` is a sum of squares in `R`. The proofs follow directly from the definition of the function `sum_of_squares`.
-/

lemma zero_is_sum_of_squares : is_sum_of_squares 0 
  := by 
    use [0] 
    rfl
    done

lemma one_is_sum_of_squares : is_sum_of_squares 1 
  := by
    use [1]
    rfl
    done

lemma squares_are_sums_of_squares  {R : Type} [Semiring R] (x : R) : is_sum_of_squares (x ^ 2) 
  := by 
    use [x]
    simp [sum_of_squares]
    done

/-!
Next, we prove that if `S1` and `S2` are sums of squares in `R`, then of is `S1 + S2`. And if `R` is commutative, then so is `S1 * S2`.
-/

theorem sum_of_squares_from_sum {R : Type} [Semiring R] {S1 S2 : R} (h1 : is_sum_of_squares S1) (h2 : is_sum_of_squares S2) : is_sum_of_squares (S1 + S2) 
  := by
    rcases h1 with ⟨L1, h1⟩ 
    rcases h2 with ⟨L2, h2⟩ 
    use (L1 ++ L2) 
    simp [sum_of_squares_concat] 
    rw [h1, h2] 
    done

-- TO COMPLETE... 

def boxmul {R : Type} [Semiring R] (L1 L2 : List R) : List R := List.map (fun ((a, b) : R × R) => a * b) (List.product L1 L2)

theorem boxmul_cons {R : Type} [Semiring R] (a : R) (L1 L2 : List R) : 
boxmul (a :: L1) L2 = L2.map (a * .) ++ boxmul L1 L2
  := by
    simp [boxmul, List.product, List.product_cons]
    have aux : (fun x => x.fst * x.snd) ∘ Prod.mk a = (fun x => a * x) := by simp [Function.funext_iff]
    rw [aux] 
    done

theorem boxmul_sum {R : Type} [Semiring R] (L1 L2 : List R) : List.sum (boxmul L1 L2) = (List.sum L1) * (List.sum L2) 
  := by
    induction L1 with
    | nil => simp [List.nil_product] ; have aux : boxmul [] L2 = [] := by {simp [boxmul]} ; rw [aux] ; rfl
    | cons a l ih => simp [boxmul_cons, mul_sum, add_mul, ih] 
    done

-- NOTE THAT `boxmul` BEHAVES DISTRIBUTIVELY 

#eval List.product [1,2] [1, 2, 3]
#eval boxmul [1,2] [1, 2, 3]


-- [MulHomClass F R S] (f : F)

lemma listproduct_map {R S : Type} (L1 L2 : List R) (f : R → S) : (List.product L1 L2).map (fun (x : R × R) => Prod.mk (f x.fst) (f x.snd)) = List.product (L1.map f) (L2.map f) 
  := by
    simp [List.product]
    simp [List.bind]
    simp [List.bind_map]
    sorry
    done


theorem boxmul_map {R S : Type} [Semiring R] [Semiring S] (L1 L2 : List R) (f : R → S) (hf : ∀ a b, f (a * b) = (f a) * (f b)) : (boxmul L1 L2).map f = (boxmul (L1.map f) (L2.map f))
  := by
    induction L1 with
    | nil => simp [boxmul]
    | cons a l ih => 
    simp [boxmul]--, Function.funext_iff, MulHomClass.map_mul]
    have aux : ↑f ∘ (fun (x : R × R) => x.fst * x.snd) = fun (x : R × R) => (f x.fst) * (f x.snd) 
      := by
        -- simp [Function.funext_iff, hf]
        ext x
        apply hf
        -- exact hf x.fst x.snd 
        -- -- simp [Function.funext_iff, MulHomClass.map_mul]
        done
    -- simp [aux]
    rw [← List.map_cons]
    simp [listproduct_map]
    simp [ih]
    simp [List.product]
    simp [List.bind_map]
    simp [boxmul, List.product, List.map_bind, aux] at ih
    simp [List.product, List.map_bind, List.map_comp_map, aux, List.bind, ih]
    sorry
    done


-- boxmul should commute to functions...

theorem sum_of_squares_from_mul {R : Type} [Semiring R] {S1 S2 : R} (h1 : is_sum_of_squares S1) (h2 : is_sum_of_squares S2) : is_sum_of_squares (S1 * S2) 
  := by
    rcases h1 with ⟨L1, h1⟩
    rcases h2 with ⟨L2, h2⟩
    -- have h1' : S1 = (L1.map (. ^ 2)).sum 
    --   := by 
    --     rw [squaring_and_summing, h1]
    --     done
    -- have h2' : S2 = (L2.map (. ^ 2)).sum 
    --   := by 
    --     rw [squaring_and_summing, h2]
    --     done 
    simp [is_sum_of_squares]
    use boxmul L1 L2
    rw [← squaring_and_summing]
    sorry
    done

/-!
## Being a sum of squares (inductive)

Let us write an inductive definition of what it means to be a sum of squares.
-/

inductive ind_sum_of_squares [Semiring R] : R → Prop :=
    | zero : ind_sum_of_squares (0 : R)
    | add (a S : R) (hS : ind_sum_of_squares S) : ind_sum_of_squares (a ^ 2 + S)

lemma ind_zero_is_sum_of_squares : ind_sum_of_squares 0
  := by 
    exact ind_sum_of_squares.zero
    done

lemma ind_one_is_sum_of_squares : ind_sum_of_squares 1 
  := by
    have aux : 1 = (1 ^ 2 + 0) := by rfl
    rw [aux]
    exact ind_sum_of_squares.add 1 0 ind_sum_of_squares.zero
    done

lemma ind_squares_are_sums_of_squares  {R : Type} [Semiring R] (x : R) : ind_sum_of_squares (x ^ 2) 
  := by
    rw [← add_zero (x ^2)]
    exact ind_sum_of_squares.add x 0 ind_sum_of_squares.zero 
    done

theorem ind_sum_of_squares_from_sum {R : Type} [Semiring R] {S1 S2 : R} (h1 : ind_sum_of_squares S1) (h2 : ind_sum_of_squares S2) : ind_sum_of_squares (S1 + S2) 
  := by
    induction h1 with
      | zero => 
        simp
        exact h2
      | add a S hS ih => 
        rw [add_assoc]
        exact ind_sum_of_squares.add a (S + S2) ih 
    done

lemma ind_mul_by_sq_sum_of_squares {R : Type} [CommSemiring R] {S : R} (h : ind_sum_of_squares S) (x : R) : ind_sum_of_squares (x ^2 * S)
  := by
    induction h with
    | zero => 
    rw [mul_zero]
    exact ind_sum_of_squares.zero
    |add a s _ ih => 
    rw [mul_add, ← mul_pow x a 2]
    exact ind_sum_of_squares.add (x * a) (x ^ 2 * s) ih
    done

theorem ind_sum_of_squares_from_mul {R : Type} [CommSemiring R] {S1 S2 : R} (h1 : ind_sum_of_squares S1) (h2 : ind_sum_of_squares S2) : ind_sum_of_squares (S1 * S2) 
  := by
    induction h1 with
    | zero => 
      rw [zero_mul]
      exact ind_sum_of_squares.zero 
    | add a S hS ih => 
      rw [add_mul]
      apply ind_sum_of_squares_from_sum _ _
      · exact ind_mul_by_sq_sum_of_squares h2 _
      · exact ih 
    done

/-!
The inductive definition is very convenient in order to write proofs of certain basic facts (by induction!). For instance, we have proven in this way that the sum `S1 + S2` and the product `S1 * S2` of two sums of squares `S1` and `S2` are again sums of squares.

Now we want to check that the [inductive definition](#being-a-sum-of-squares-inductive) coincides with the [existential definition](#being-a-sum-of-squares-existential).
-/

lemma exist_to_ind {R : Type} [Semiring R] (S : R) (H : is_sum_of_squares S) : ind_sum_of_squares S 
  := by
    rcases H with ⟨L, hL⟩
    induction L generalizing S with
    | nil => 
      simp [sum_of_squares] at hL
      rw [← hL]
      exact ind_sum_of_squares.zero
    | cons a L ih =>
      rw [← hL]
      simp [sum_of_squares]
      specialize ih (sum_of_squares L) (Eq.refl (sum_of_squares L))
      exact ind_sum_of_squares.add a (sum_of_squares L) ih 
    done

lemma ind_to_exist {R : Type} [Semiring R] (S : R) (H : ind_sum_of_squares S) : is_sum_of_squares S 
  := by
    simp [is_sum_of_squares]
    induction H with
    | zero => 
      use [] 
      rfl
    | add a S' _ ih => 
      rcases ih with ⟨L', hL'⟩ 
      rw [← hL']
      use (a :: L')
      rfl 
    done

theorem equiv_defs {R : Type} [Semiring R] (S : R) : is_sum_of_squares S ↔ ind_sum_of_squares S 
  := by
    constructor
    · apply exist_to_ind 
    · apply ind_to_exist 
    done

/-!
## *Golfed versions of the proofs*
-/

theorem squaring_and_summing_golfed {R : Type} [Semiring R] 
  (L : List R) : (L.map (. ^ 2)).sum = sum_of_squares L
    := by induction L with
      | nil => rfl
      | cons a L ih => simp [sum_of_squares, ih]

@[simp]
theorem sum_of_squares_concat_golfed {R : Type} [Semiring R] 
  (L1 L2 : List R) : sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2 
    := by induction L1 with
      | nil => simp [sum_of_squares]
      | cons _ _ ih => simp [sum_of_squares, ih, add_assoc]

@[simp]
theorem sum_of_squares_permut_golfed {R : Type} [Semiring R] {L1 L2 : List R} 
  (H : L1 ~ L2) : sum_of_squares L1 = sum_of_squares L2 
    := by induction H with
      | nil => rfl
      | cons _ _ Sum12 => simp [sum_of_squares, Sum12]
      | swap x y _ => simp [sum_of_squares, ← add_assoc, ← add_assoc, add_comm (y  ^ 2) (x ^ 2)]
      | trans _ _ Sum1 Sum2 => rw [Sum1, Sum2]
  
@[simp]
theorem sum_of_squares_erase_golfed {R : Type} [Semiring R] [DecidableEq R] (L : List R) (a : R) (h : a ∈ L) : 
  sum_of_squares L = a ^ 2 + sum_of_squares (L.erase a) 
    := by rw [sum_of_squares_permut_golfed (L.perm_cons_erase h), sum_of_squares]

@[simp]
theorem sum_of_squares_of_list_mul_golfed {R : Type} [CommSemiring R] 
  (L : List R) (c : R) : sum_of_squares (L.map (c * .)) = c ^ 2 * sum_of_squares L
    := by induction L with
      | nil => simp [sum_of_squares]
      | cons a _ ih => simp [sum_of_squares, ih, mul_add, mul_pow c a 2]

@[simp]
theorem sum_of_squares_of_list_div_golfed {F : Type} [Semifield F] 
  (L : List F) (c : F) : sum_of_squares (L.map (. / c)) = (1 / c ^ 2) * sum_of_squares L 
    := by simp [div_eq_mul_inv, mul_comm _ c⁻¹]

@[simp]
theorem ind_sum_of_squares_from_sum_golfed {R : Type} [Semiring R] {S1 S2 : R} (h1 : ind_sum_of_squares S1) (h2 : ind_sum_of_squares S2) : ind_sum_of_squares (S1 + S2) 
  := by
    induction h1 with
      | zero => simp [zero_add, h2]
      | add a S _ h2 => simp [add_assoc, ind_sum_of_squares.add a (S + S2) h2]
    
@[simp]
theorem ind_mul_by_sq_sum_of_squares_golfed {R : Type} [CommSemiring R] {S : R} (h : ind_sum_of_squares S) (x : R) : ind_sum_of_squares (x ^2 * S)
  := by
    induction h with
    | zero => simp [mul_zero, ind_sum_of_squares.zero]
    | add a s _ h => simp [mul_add, ← mul_pow x a 2, ind_sum_of_squares.add (x * a) (x ^ 2 * s) h]

@[simp]
theorem ind_sum_of_squares_from_mul_golfed {R : Type} [CommSemiring R] {S1 S2 : R} (h1 : ind_sum_of_squares S1) (h2 : ind_sum_of_squares S2) : ind_sum_of_squares (S1 * S2) 
  := by
    induction h1 with
    | zero => simp [zero_mul, ind_sum_of_squares.zero]
    | add a S _ ih => simp [add_mul, ind_sum_of_squares_from_sum (ind_mul_by_sq_sum_of_squares h2 _) ih]

/-!
## Exercises

1. Modify the syntax of the `induction` tactic in [`sum_of_squares_permut`](#permuted-lists) to make it look more similar to that of [`sum_of_squares_concat`](#concatenated-lists) (meaning, in `sum_of_squares_permut`, replace `induction H` by `induction H with` and make the proof syntactically correct after that).

2. Let `R` be a type with decidable equality. Let `a` be a term of type `R` and let `L` be a term of type `List R`. Prove that, if [`a ∈ L`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.Mem), then the list [`a :: L.erase a`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.erase) is a [permutation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Perm.html#List.Perm) of `L` (we have used this standard result [here](#erasing-a-member)). *Indication:* As usual, focus first on the statement, then write the proof.
-/

/-!
We can check the axioms on which results in this file or in Mathlib depend by using the command `#print axioms`.
-/

#print axioms sum_of_squares_erase_golfed -- 'sum_of_squares_erase_golfed' depends on axioms: [propext, Quot.sound]
#print axioms List.perm_cons_erase -- 'List.perm_cons_erase' depends on axioms: [propext, Quot.sound]

/-!
The `#lint` command can help us correct certain errors in the file, e.g. a certain `def` should be a `theorem`, *etc*.
-/

#lint

/-!

ANOTHER FILE:

semireal ring if -1 is not a sum of squares

real ring if sum of squares = 0 implies all terms are 0

for fields, the two are equivalent

the characteristic of a (semi?)real ring is 0

NEXT FILE: 

in **rings**: def of precones, cones, examples, support of a cone , prime cone (compare all of this to positive cone in mathlib, see Leiden pdf again)

NEXT:

real ideals (in rings...)

-/