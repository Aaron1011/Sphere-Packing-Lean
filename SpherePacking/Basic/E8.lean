/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Gareth Ma
-/
import SpherePacking.Basic.PeriodicPacking
import SpherePacking.ForMathlib.Finsupp
import SpherePacking.ForMathlib.Vec

/-!
# Basic properties of the E₈ lattice

We define the E₈ lattice in two ways, as the ℤ-span of a chosen basis (`E8_Matrix`), and as the set
of vectors in ℝ^8 with sum of coordinates an even integer and coordinates either all integers or
half-integers (`E8_Set`). We prove these two definitions are equivalent, and prove various
properties about the E₈ lattice.

## Main theorems

* `E8_Matrix`: a fixed ℤ-basis for the E₈ lattice
* `E8_is_basis`: `E8_Matrix` forms a ℝ-basis of ℝ⁸
* `E8_Set`: the set of vectors in E₈, characterised by relations of their coordinates
* `E8_Set_eq_span`: the ℤ-span of `E8_Matrix` coincides with `E8_Set`
* `E8_norm_eq_sqrt_even`: E₈ is even

## TODO

* Prove E₈ is unimodular
* Prove E₈ is positive-definite
* Documentation and naming

-/

open EuclideanSpace BigOperators SpherePacking Matrix algebraMap Pointwise

/-
* NOTE: *
It will probably be useful, at some point in the future, to subsume this file under a more general
file tackling the classification of crystallographic, irreducible Coxeter groups and their root
systems (or something like that). It might also be useful to add general API that will make it
easier to construct a `SpherePackingCentres` instance for such lattices, which would be useful for
the sphere packing problem in other dimensions.
-/

namespace E8

/-- E₈ is characterised as the set of vectors with (1) coordinates summing to an even integer,
and (2) all its coordinates either an integer or a half-integer. -/
def E8_Set : Set (EuclideanSpace ℝ (Fin 8)) :=
  {v | ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 * v i)) ∧ ∑ i, v i ≡ 0 [PMOD 2]}

theorem mem_E8_Set {v : EuclideanSpace ℝ (Fin 8)} :
    v ∈ E8_Set ↔
      ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 * v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  simp [E8_Set]

theorem mem_E8_Set' {v : EuclideanSpace ℝ (Fin 8)} :
    v ∈ E8_Set ↔
      ((∀ i, ∃ n : ℤ, Even n ∧ n = 2 * v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 * v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  have (k : ℝ) : (∃ n : ℤ, Even n ∧ n = 2 * k) ↔ (∃ n : ℤ, n = k) :=
    ⟨fun ⟨n, ⟨⟨l, hl⟩, hn⟩⟩ ↦ ⟨l, by simp [← two_mul, hl] at hn; exact hn⟩,
     fun ⟨n, hn⟩ ↦ ⟨2 * n, ⟨even_two_mul n, by simp [hn]⟩⟩⟩
  simp_rw [this, mem_E8_Set]

section E8_Over_ℚ

/- Credit for the code proving linear independence goes to Gareth Ma. -/

/- # Choice of Simple Roots
There are many possible choices of simple roots for the E8 root system. Here, we choose the one
mentioned in the Wikipedia article https://en.wikipedia.org/wiki/E8_(mathematics).
-/

/-- E₈ is also characterised as the ℤ-span of the following vectors. -/
def E8' : Matrix (Fin 8) (Fin 8) ℚ := !![
1,-1,0,0,0,0,0,0;
0,1,-1,0,0,0,0,0;
0,0,1,-1,0,0,0,0;
0,0,0,1,-1,0,0,0;
0,0,0,0,1,-1,0,0;
0,0,0,0,0,1,1,0;
-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2;
0,0,0,0,0,1,-1,0
]

/-- F8 is the inverse matrix of E₈, used to assist computation below. -/
def F8' : Matrix (Fin 8) (Fin 8) ℚ := !![
1,1,1,1,1,1/2,0,1/2;
0,1,1,1,1,1/2,0,1/2;
0,0,1,1,1,1/2,0,1/2;
0,0,0,1,1,1/2,0,1/2;
0,0,0,0,1,1/2,0,1/2;
0,0,0,0,0,1/2,0,1/2;
0,0,0,0,0,1/2,0,-1/2;
-1,-2,-3,-4,-5,-7/2,-2,-5/2
]

@[simp]
theorem E8_mul_F8_eq_id_Q : E8' * F8' = !![
    1,0,0,0,0,0,0,0;
    0,1,0,0,0,0,0,0;
    0,0,1,0,0,0,0,0;
    0,0,0,1,0,0,0,0;
    0,0,0,0,1,0,0,0;
    0,0,0,0,0,1,0,0;
    0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,0,1;
    ] := by
  rw [E8', F8']
  norm_num

@[simp]
theorem E8_mul_F8_eq_one_Q : E8' * F8' = 1 := by rw [E8_mul_F8_eq_id_Q]; decide

@[simp]
theorem F8_mul_E8_eq_one_Q : F8' * E8' = 1 := by
  rw [Matrix.mul_eq_one_comm, E8_mul_F8_eq_one_Q]

section E8_unimodular

/- In this section we perform "manual rref" (laughing as I type this). -/

private def c₆ : Fin 8 → ℚ := ![1/2, 1, 3/2, 2, 5/2, 3, 1, 0]
private def c₇ : Fin 8 → ℚ := ![0, 0, 0, 0, 0, -1, 4/5, 1]

private theorem E8'_det_aux_1 : (∑ k : Fin 8, c₆ k • E8' k) = ![0, 0, 0, 0, 0, 0, 5/2, -1/2] := by
  ext i
  trans 1 / 2 * E8' 0 i + E8' 1 i + 3 / 2 * E8' 2 i + 2 * E8' 3 i
    + 5 / 2 * E8' 4 i + 3 * E8' 5 i + E8' 6 i
  · simp [Fin.sum_univ_eight, c₆]
  · fin_cases i <;> simp [E8'] <;> norm_num

private theorem E8'_det_aux_2 (i : Fin 8) :
    E8'.updateRow 6 (∑ k, c₆ k • E8' k) i
      = if i = 6 then ![0, 0, 0, 0, 0, 0, 5/2, -1/2] else E8' i := by
  ext j
  rw [updateRow_apply]
  split_ifs with hi
  · rw [E8'_det_aux_1]
  · rfl

private theorem E8'_det_aux_3 : (∑ k : Fin 8, c₇ k • (E8'.updateRow 6 (∑ k, c₆ k • E8' k)) k)
    = ![0, 0, 0, 0, 0, 0, 0, -2/5] := by
  ext i
  simp_rw [E8'_det_aux_2, Fin.sum_univ_eight]
  simp only [Fin.reduceEq, ↓reduceIte, smul_eq_mul, mul_zero, Pi.add_apply, Pi.smul_apply]
  simp [c₇, E8']
  fin_cases i <;> simp <;> norm_num

theorem E8'_updateRow₆₇ :
    (E8'.updateRow 6 (∑ k : Fin 8, c₆ k • E8' k)).updateRow 7
    (∑ k : Fin 8, c₇ k • E8'.updateRow 6 (∑ k : Fin 8, c₆ k • E8' k) k)
      = !![1,-1,0,0,0,0,0,0;0,1,-1,0,0,0,0,0;0,0,1,-1,0,0,0,0;0,0,0,1,-1,0,0,0;0,0,0,0,1,-1,0,0;
        0,0,0,0,0,1,1,0;0,0,0,0,0,0,5/2,-1/2;0,0,0,0,0,0,0,-2/5] := by
  rw [E8'_det_aux_3, E8'_det_aux_1]
  ext i _
  fin_cases i <;> simp [E8']

theorem E8'_det_aux_4 :
    (!![1,-1,0,0,0,0,0,0;0,1,-1,0,0,0,0,0;0,0,1,-1,0,0,0,0;0,0,0,1,-1,0,0,0;0,0,0,0,1,-1,0,0;
        0,0,0,0,0,1,1,0;0,0,0,0,0,0,5/2,-1/2;0,0,0,0,0,0,0,-2/5] : Matrix (Fin 8) (Fin 8) ℚ).det
      = -1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [Fin.prod_univ_eight];
  · intro i j h
    simp at h
    fin_cases i <;> fin_cases j
    <;> simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceLT] at h <;> norm_num


theorem E8_det_eq_one : E8'.det = 1 := by
  unfold E8'
  repeat rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  dsimp only []
  sorry
  --reduce
  --simp [det_succ_row_zero, Fin.sum_univ_succ]
  --rewrite [Matrix.det_succ_row_zero]

  --simp [det_succ_row_zero, Fin.sum_univ_succ]
  --rw [Matrix.det_succ_row_zero]
  -- conv =>
  --   lhs
  --   arg 2
  --   intro j
  --   lhs
  --   simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, of_apply, cons_val',
  --     cons_val_fin_one, cons_val_zero]

  -- rw [Fin.sum_univ_succ]
  -- norm_num
  -- repeat rw [Matrix.det_succ_row_zero]; rw [Fin.sum_univ_succ]
  -- simp
  --nth_rw 1 [Finset.sum_univ_succ]

  --simp [det_succ_row_zero, Fin.sum_univ_succ]



  --rw [Matrix.det_succ_row_zero]
  --rw [Matrix.det_succ_row_zero]
  --have h₁ := congrArg (fun f ↦ c₇ 7 • f) (det_updateRow_sum E8' 6 c₆)
  --simp only at h₁
  --have h₂ := det_updateRow_sum (E8'.updateRow 6 (∑ k, c₆ k • E8' k)) 7 c₇
  -- TODO: I can't do h₂.trans h₁ (also #15045)
  --sorry

end E8_unimodular

end E8_Over_ℚ

-- noncomputable section E8_Over_ℝ

-- def E8_Matrix : Matrix (Fin 8) (Fin 8) ℝ := (algebraMap ℚ ℝ).mapMatrix E8'

-- def F8_Matrix : Matrix (Fin 8) (Fin 8) ℝ := (algebraMap ℚ ℝ).mapMatrix F8'

-- theorem E8_Matrix_apply {i j : Fin 8} : E8_Matrix i j = E8' i j :=
--   rfl

-- theorem E8_Matrix_apply_row {i : Fin 8} : E8_Matrix i = (fun j ↦ (E8' i j : ℝ)) :=
--   rfl

-- @[simp]
-- theorem E8_mul_F8_eq_one_R : E8_Matrix * F8_Matrix = 1 := by
--   rw [E8_Matrix, F8_Matrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.map_mul,
--     E8_mul_F8_eq_one_Q] --, map_one _ coe_zero coe_one]  -- Doesn't work for some reason
--   simp only [map_zero, _root_.map_one, Matrix.map_one]

-- @[simp]
-- theorem F8_mul_E8_eq_one_R : F8_Matrix * E8_Matrix = 1 := by
--   rw [E8_Matrix, F8_Matrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.map_mul,
--     F8_mul_E8_eq_one_Q] --, map_one _ coe_zero coe_one]
--   simp only [map_zero, _root_.map_one, Matrix.map_one]

-- theorem E8_is_basis :
--     LinearIndependent ℝ E8_Matrix ∧ Submodule.span ℝ (Set.range E8_Matrix) = ⊤ := by
--   -- TODO: un-sorry (kernel error, #15045)
--   -- rw [is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det]
--   -- change IsUnit E8_Matrix.det
--   -- have : E8_Matrix.det * F8_Matrix.det = 1 := by
--   --   rw [← det_mul, E8_mul_F8_eq_one_R, det_one]
--   -- exact isUnit_of_mul_eq_one _ _ this
--   sorry

-- section E8_sum_apply_lemmas

-- variable {α : Type*} [Semiring α] [Module α ℝ] (y : Fin 8 → α)

-- lemma E8_sum_apply_0 :
--     (∑ j : Fin 8, y j • E8_Matrix j) 0 = y 0 • 1 - y 6 • (1 / 2) := by
--   simp [E8', E8_Matrix, Fin.sum_univ_eight, neg_div, ← sub_eq_add_neg]

-- lemma E8_sum_apply_1 :
--     (∑ j : Fin 8, y j • E8_Matrix j) 1 = y 0 • (-1) + y 1 • 1 - y 6 • ((1 : ℝ) / 2) := by
--   simp [E8', E8_Matrix, Fin.sum_univ_eight, neg_div, smul_neg, -one_div, ← sub_eq_add_neg]

-- lemma E8_sum_apply_2 :
--     (∑ j : Fin 8, y j • E8_Matrix j) 2 = y 1 • (-1) + y 2 • 1 - y 6 • ((1 : ℝ) / 2) := by
--   simp [E8', E8_Matrix, Fin.sum_univ_eight, neg_div, mul_neg, ← sub_eq_add_neg]

-- lemma E8_sum_apply_3 :
--     (∑ j : Fin 8, y j • E8_Matrix j) 3 = y 2 • (-1) + y 3 • 1 - y 6 • ((1 : ℝ) / 2) := by
--   simp [E8', E8_Matrix, Fin.sum_univ_eight, neg_div, ← sub_eq_add_neg]

-- lemma E8_sum_apply_4 :
--     (∑ j : Fin 8, y j • E8_Matrix j) 4 = y 3 • (-1) + y 4 • 1 - y 6 • ((1 : ℝ) / 2) := by
--   simp [E8', E8_Matrix, Fin.sum_univ_eight, neg_div, mul_neg, ← sub_eq_add_neg]

-- lemma E8_sum_apply_5 :
--     (∑ j : Fin 8, y j • E8_Matrix j) 5 = y 4 • (-1) + y 5 • 1 - y 6 • ((1 : ℝ) / 2) + y 7 • 1 := by
--   simp [E8', E8_Matrix, Fin.sum_univ_eight, neg_div, mul_neg, ← sub_eq_add_neg]

-- lemma E8_sum_apply_6 :
--     (∑ j : Fin 8, y j • E8_Matrix j) 6 = y 5 • 1 - y 6 • ((1 : ℝ) / 2) - y 7 • 1 := by
--   simp [E8', E8_Matrix, Fin.sum_univ_eight, neg_div, mul_neg, ← sub_eq_add_neg]

-- lemma E8_sum_apply_7 :
--     (∑ j : Fin 8, y j • E8_Matrix j) 7 = y 6 • (-(1 : ℝ) / 2) := by
--   simp [E8', E8_Matrix, Fin.sum_univ_eight]

-- macro "simp_E8_sum_apply" : tactic =>
--   `(tactic |
--     simp only [E8_sum_apply_0, E8_sum_apply_1, E8_sum_apply_2, E8_sum_apply_3, E8_sum_apply_4,
--       E8_sum_apply_5, E8_sum_apply_6, E8_sum_apply_7])

-- end E8_sum_apply_lemmas

-- theorem E8_Set_eq_span : E8_Set = (Submodule.span ℤ (Set.range E8_Matrix) : Set (Fin 8 → ℝ)) := by
--   ext v
--   rw [SetLike.mem_coe, ← Finsupp.range_linearCombination, LinearMap.mem_range]
--   constructor <;> intro hv
--   · obtain ⟨hv₁, hv₂⟩ := mem_E8_Set'.mp hv
--     convert_to (∃ y : Fin 8 →₀ ℤ, (∑ i, y i • E8_Matrix i) = v)
--     · ext y
--       rw [← Finsupp.linearCombination_eq_sum]
--       rfl
--     · cases' hv₁ with hv₁ hv₁
--       -- TODO (the y is just F8_Matrix * v, need to prove it has integer coefficients)
--       <;> sorry
--   · obtain ⟨y, hy⟩ := hv
--     erw [Finsupp.linearCombination_eq_sum] at hy
--     constructor
--     · by_cases hy' : Even (y 6)
--       · left
--         obtain ⟨k, hk⟩ := hy'
--         intro i
--         -- TODO: un-sorry (slow)
--         sorry
--         -- fin_cases i
--         -- <;> [use y 0 - k; use -y 0 + y 1 - k; use -y 1 + y 2 - k; use -y 2 + y 3 - k;
--         --   use -y 3 + y 4 - k; use -y 4 + y 5 - k + y 7; use y 5 - k - y 7; use -k]
--         -- <;> convert congrFun hy _
--         -- all_goals
--         --   simp_rw [Fintype.sum_apply, Pi.smul_apply, Fin.sum_univ_eight, E8_Matrix_apply]
--         --   simp [hk]
--         --   ring_nf
--       · right
--         intro i
--         -- TODO: un-sorry (slow)
--         sorry
--         -- fin_cases i
--         -- <;> [use 2 * y 0 - y 6; use -2 * y 0 + 2 * y 1 - y 6; use -2 * y 1 + 2 * y 2 - y 6;
--         --   use -2 * y 2 + 2 * y 3 - y 6; use -2 * y 3 + 2 * y 4 - y 6;
--         --   use -2 * y 4 + 2 * y 5 - y 6 + 2 * y 7; use 2 * y 5 - y 6 - 2 * y 7; use -y 6]
--         -- <;> simp [Int.even_sub, Int.even_add, hy']
--         -- <;> subst hy
--         -- <;> simp_E8_sum_apply
--         -- <;> try simp only [mul_sub, mul_add, neg_div]
--         -- <;> norm_num
--         -- <;> rw [← mul_assoc, mul_right_comm, mul_one_div_cancel (by norm_num), one_mul]
--     · subst hy
--       simp_rw [Fintype.sum_apply, Pi.smul_apply, E8_Matrix_apply, Fin.sum_univ_eight]
--       -- TODO: un-sorry (slow)
--       sorry
--       -- simp
--       -- use y 6 * 2 - y 5
--       -- ring_nf
--       -- rw [zsmul_eq_mul, Int.cast_sub, sub_mul, Int.cast_mul, mul_assoc]
--       -- norm_num

-- end E8_Over_ℝ

-- noncomputable section E8_isZLattice

-- theorem E8_add_mem {a b : EuclideanSpace ℝ (Fin 8)} (ha : a ∈ E8_Set) (hb : b ∈ E8_Set) :
--     a + b ∈ E8_Set := by
--   rw [E8_Set_eq_span, SetLike.mem_coe] at *
--   exact (Submodule.add_mem_iff_right _ ha).mpr hb

-- theorem E8_neg_mem {a : EuclideanSpace ℝ (Fin 8)} (ha : a ∈ E8_Set) : -a ∈ E8_Set := by
--   rw [E8_Set_eq_span, SetLike.mem_coe] at *
--   exact Submodule.neg_mem _ ha

-- def E8_AddSubgroup : AddSubgroup (EuclideanSpace ℝ (Fin 8)) where
--   carrier := E8_Set
--   zero_mem' := by simp [mem_E8_Set]
--   add_mem' := E8_add_mem
--   neg_mem' := E8_neg_mem

-- def E8_Lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 8)) where
--   carrier := E8_Set
--   zero_mem' := by simp [mem_E8_Set]
--   add_mem' := E8_add_mem
--   smul_mem' := by
--     intros n v hv
--     simp only [mem_E8_Set] at hv ⊢
--     obtain ⟨hv₁, hv₂⟩ := hv
--     -- Need to do cases on whether n is even or odd
--     -- Then do cases on hv₁
--     sorry

-- open Topology TopologicalSpace Filter Function InnerProductSpace RCLike

-- theorem E8_Matrix_inner {i j : Fin 8} :
--     haveI : Inner ℝ (Fin 8 → ℝ) := (inferInstance : Inner ℝ (EuclideanSpace ℝ (Fin 8)))
--     ⟪(E8_Matrix i : EuclideanSpace ℝ (Fin 8)), E8_Matrix j⟫_ℝ = ∑ k, E8' i k * E8' j k := by
--   simp only [inner, inner_apply, conj_trivial, Rat.cast_sum, Rat.cast_mul,
--     E8_Matrix_apply, mul_comm]

-- section E8_norm_bounds

-- set_option maxHeartbeats 2000000 in
-- /-- All vectors in E₈ have norm √(2n) -/
-- theorem E8_norm_eq_sqrt_even (v : E8_Lattice) :
--     ∃ n : ℤ, Even n ∧ ‖v‖ ^ 2 = n := by
--   -- TODO: un-sorry (slow)
--   sorry
--   -- rcases v with ⟨v, hv⟩
--   -- change ∃ n : ℤ, Even n ∧ ‖v‖ ^ 2 = n
--   -- rw [norm_sq_eq_inner (𝕜 := ℝ) v]
--   -- simp_rw [E8_Lattice, AddSubgroup.mem_mk, E8_Set_eq_span, SetLike.mem_coe,← Finsupp.range_total,
--   --   LinearMap.mem_range] at hv
--   -- replace hv : ∃ y : Fin 8 →₀ ℤ, ∑ i, y i • E8_Matrix i = v := by
--   --   convert hv
--   --   rw [← Finsupp.linearCombination_eq_sum E8_Matrix _]
--   --   rfl
--   -- obtain ⟨y, ⟨⟨w, hw⟩, rfl⟩⟩ := hv
--   -- simp_rw [re_to_real, sum_inner, inner_sum, intCast_smul_left, intCast_smul_right, zsmul_eq_mul,
--   --   Fin.sum_univ_eight]
--   -- repeat rw [E8_Matrix_inner]
--   -- repeat rw [Fin.sum_univ_eight]
--   -- -- compute the dot products
--   -- norm_num
--   -- -- normalise the goal to ∃ n, Even n ∧ _ = n
--   -- norm_cast
--   -- rw [exists_eq_right']
--   -- -- now simplify the rest algebraically
--   -- ring_nf
--   -- simp [Int.even_sub, Int.even_add]

-- theorem E8_norm_lower_bound (v : E8_Lattice) : v = 0 ∨ √2 ≤ ‖v‖ := by
--   rw [or_iff_not_imp_left]
--   intro hv
--   obtain ⟨n, ⟨hn, hn'⟩⟩ := E8_norm_eq_sqrt_even v
--   have : 0 ≤ (n : ℝ) := by rw [← hn']; exact sq_nonneg ‖↑v‖
--   have : 0 ≤ n := by norm_cast at this
--   have : n ≠ 0 := by contrapose! hv; simpa [hv] using hn'
--   have : 2 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
--   have : √2 ^ 2 ≤ ‖v‖ ^ 2 := by rw [sq, Real.mul_self_sqrt zero_le_two, hn']; norm_cast
--   rwa [sq_le_sq, abs_norm, abs_eq_self.mpr ?_] at this
--   exact Real.sqrt_nonneg 2

-- end E8_norm_bounds

-- instance instDiscreteE8Lattice : DiscreteTopology E8_Lattice := by
--   rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
--   use 1, by norm_num,
--     fun v h ↦ (E8_norm_lower_bound v).resolve_right ?_
--   have : 1 < √2 := by rw [Real.lt_sqrt zero_le_one, sq, mul_one]; exact one_lt_two
--   linarith [dist_zero_right v ▸ h]

-- instance : DiscreteTopology E8_Set :=
--   (inferInstance : DiscreteTopology E8_Lattice)

-- theorem E8_Set_span_eq_top : Submodule.span ℝ (E8_Set : Set (EuclideanSpace ℝ (Fin 8))) = ⊤ := by
--   simp only [Submodule.span, sInf_eq_top, Set.mem_setOf_eq]
--   intros M hM
--   have := Submodule.span_le.mpr <| Submodule.subset_span.trans (E8_Set_eq_span ▸ hM)
--   rw [E8_is_basis.right] at this
--   exact Submodule.eq_top_iff'.mpr fun _ ↦ this trivial

-- instance instIsZLatticeE8Lattice : IsZLattice ℝ E8_Lattice :=
--   ⟨E8_Set_span_eq_top⟩

-- end E8_isZLattice

-- section Packing

-- open scoped Real

-- -- lattice is inferred!
-- noncomputable def E8Packing : PeriodicSpherePacking 8 where
--   separation := √2
--   lattice := E8_Lattice
--   centers := E8_Lattice
--   centers_dist x y h := (E8_norm_lower_bound (x - y)).resolve_left <| sub_ne_zero_of_ne h
--   lattice_action x y := add_mem

-- -- sanity checks
-- example : E8Packing.separation = √2 := rfl
-- example : E8Packing.lattice = E8_Lattice := rfl

-- -- We need a theorem for when centers = lattice
-- theorem E8Packing_numReps : E8Packing.numReps = 1 := by
--   sorry

-- lemma E8_Matrix_mem (i : Fin 8) : E8_Matrix i ∈ E8_Lattice := by
--   rw [E8_Lattice, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, E8_Set_eq_span,
--       SetLike.mem_coe]
--   exact Set.mem_of_subset_of_mem Submodule.subset_span (Set.mem_range_self i)

-- -- This is ugly but just hide it and pretend it's not there
-- private lemma linearIndependent_subtype_thing
--     {d : ℕ} {ι : Type*} [Fintype ι]
--     {b : ι → EuclideanSpace ℝ (Fin d)} (hb : LinearIndependent ℤ b)
--     {s : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
--     (hs : s = (Submodule.span ℤ (Set.range b)))
--     (h : ∀ i, b i ∈ s) :
--     LinearIndependent ℤ (fun i ↦ (⟨b i, h i⟩ : s)) := by
--   subst hs
--   exact linearIndependent_span hb

-- noncomputable def E8_Basis : Basis (Fin 8) ℤ E8_Lattice := by
--   have af := E8_is_basis.left.restrict_scalars' ℤ
--   have : LinearIndependent ℤ (fun i ↦ (⟨E8_Matrix i, E8_Matrix_mem i⟩ : E8_Lattice)) := by
--     apply linearIndependent_subtype_thing af
--     simp_rw [E8_Lattice, E8_Set_eq_span]
--     rfl
--   apply Basis.mk this
--     -- This is the worst proof ever but I don't want to waste my time on this
--   change (_ : Set E8_Lattice) ⊆ _
--   intro ⟨x, hx⟩ _
--   simp_rw [E8_Lattice, E8_Set_eq_span, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk] at hx
--   rw [SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp] at hx ⊢
--   obtain ⟨c, hc⟩ := hx
--   use c
--   apply Subtype.ext_iff.mpr
--   simp only [Finsupp.sum, ← hc, AddSubgroup.val_finset_sum, AddSubgroupClass.coe_zsmul]
--   exact Submodule.coe_sum E8_Lattice (fun i ↦ c i • ⟨E8_Matrix i, E8_Matrix_mem i⟩) c.support

-- -- sanity check
-- example (i : Fin 8) : ((E8_Basis i : E8_Lattice) : EuclideanSpace ℝ (Fin 8)) = E8_Matrix i := by
--   simp [E8_Basis]

-- lemma E8_Basis_apply_norm (i : Fin 8) : ‖E8_Basis i‖ = √2 := by
--   -- TODO: un-sorry (slow)
--   sorry
--   -- simp_rw [E8_Basis, Basis.coe_mk, AddSubgroup.coe_norm, norm_eq, Real.norm_eq_abs, sq_abs]
--   -- fin_cases i
--   -- <;> simp [Fin.sum_univ_eight, E8_Basis_apply_norm, Fin.sum_univ_eight, E8_Matrix_apply]
--   -- <;> norm_num

-- open MeasureTheory ZSpan in
-- theorem E8_Basis_volume : volume (fundamentalDomain (E8_Basis.ofZLatticeBasis ℝ _)) = 1 := by
--   sorry

-- open MeasureTheory ZSpan in
-- theorem E8Packing_density : E8Packing.density = ENNReal.ofReal π ^ 4 / 384 := by
--   rw [PeriodicSpherePacking.density_eq E8_Basis ?_ (by omega) (L := 8 • √2)]
--   · rw [E8Packing_numReps, Nat.cast_one, one_mul, volume_ball, Fintype.card_fin]
--     simp only [E8Packing]
--     have {x : ℝ} (hx : 0 ≤ x := by positivity) : √x ^ 8 = x ^ 4 := calc
--       √x ^ 8 = (√x ^ 2) ^ 4 := by rw [← pow_mul]
--       _ = x ^ 4 := by rw [Real.sq_sqrt hx]
--     rw [← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, div_pow, this, this, ← mul_div_assoc,
--       div_mul_eq_mul_div, mul_comm, mul_div_assoc, mul_div_assoc]
--     norm_num [Nat.factorial, mul_one_div]
--     convert div_one _
--     · rw [E8_Basis_volume]
--     · rw [← ENNReal.ofReal_pow, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_ofNat] <;> positivity
--     · positivity
--     · positivity
--   · intro x hx
--     trans ∑ i, ‖E8_Basis i‖
--     · rw [← fract_eq_self.mpr hx]
--       convert norm_fract_le (K := ℝ) _ _
--       simp; rfl
--     · apply le_of_eq
--       simp_rw [Fin.sum_univ_eight, E8_Basis_apply_norm]
--       ring_nf

-- end Packing
-- end E8
