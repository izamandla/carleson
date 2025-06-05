import Mathlib
open Function Set Classical MeasureTheory
noncomputable section

/- ## Haar and Rademacher functions -/
namespace Haar

/--
Definition of Haar function `h(x)`.
-/
def haarFunction (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x < 1/2 then 1
  else if 1/2 ≤  x ∧ x < 1 then -1
  else 0

/--
Left half of haar function is equal to one.
-/
@[simp]
theorem haarFunction_left_half (x : ℝ) (h : 0 ≤ x ∧ x < 1 / 2) : haarFunction x = 1 := by
  unfold haarFunction
  exact if_pos h

/--
Right half of haar function is equal to minus one.
-/
@[simp]
theorem haarFunction_right_half (x : ℝ) (h : 1 / 2 ≤ x ∧ x < 1) : haarFunction x = -1 := by
  unfold haarFunction
  split_ifs with h1
  · linarith
  linarith

/--
Haar function is zero outisde `[0,1)`.
-/
@[simp]
theorem haarFunction_outside (x : ℝ) (h : x < 0 ∨ x ≥ 1) : haarFunction x = 0 := by
  unfold haarFunction
  split_ifs with h1 h2
  · have h3 : ¬ (x < 0 ∨ x ≥ 1) := by
      let ⟨hP, hQ⟩ := h1
      push_neg
      constructor
      · apply hP
      · exact lt_trans hQ (by norm_num)
    contradiction
  · have h3 : ¬ (x < 0 ∨ x ≥ 1) := by
      let ⟨hP, hQ⟩ := h2
      push_neg
      constructor
      · exact le_trans (by norm_num) hP
      · apply hQ
    contradiction
  linarith

/--
Square of the Haar function is equal to one.
-/
@[simp]
theorem haar_sqr (x : ℝ): (haarFunction x)^2 = if 0 ≤ x ∧ x < 1 then 1 else 0 := by
  split_ifs with h
  · let ⟨hP, hQ⟩ := h
    by_cases h1 : x< 1/2
    · rw[haarFunction_left_half ]
      · simp only [one_pow]
      constructor
      · apply hP
      · apply h1
    · push_neg at h1
      rw[haarFunction_right_half ]
      · simp only [even_two, Even.neg_pow, one_pow]
      constructor
      · apply h1
      · apply hQ
  rw[not_and_or] at h
  push_neg at h
  rw[sq_eq_zero_iff]
  apply haarFunction_outside
  apply h

/--
The integral of Haar function over `[0,1)` equals 0.
-/

@[simp]
theorem haar_integral : ∫ x in Set.Ico 0 1, haarFunction x = 0 := by
  have hs : MeasurableSet (Set.Ico 0 (1/2 : ℝ )) := by
    simp
  have ht : MeasurableSet (Set.Ico (1/2 : ℝ ) 1) := by
    simp
  have hone : IntegrableOn (fun x : ℝ => (1 : ℝ )) (Set.Ico (0 :ℝ ) (1/2 : ℝ)) volume:=by
    simp
  have hmone : IntegrableOn (fun x : ℝ => (-1 : ℝ )) (Set.Ico (1/2 : ℝ) (1 :ℝ)) volume:=by
    simp
  have h_left : EqOn (haarFunction) 1  (Ico 0 (1/2)):= by
    apply haarFunction_left_half
  have h_right: EqOn (haarFunction) (-1)  (Ico (1/2) 1) := by
    apply haarFunction_right_half
  have h1: MeasureTheory.IntegrableOn haarFunction (Set.Ico 0 (1/2)) := by
    rw[Set.eqOn_comm] at h_left
    apply MeasureTheory.IntegrableOn.congr_fun hone h_left hs
  have h2: MeasureTheory.IntegrableOn haarFunction (Set.Ico (1/2) 1) := by
    rw[Set.eqOn_comm] at h_right
    apply MeasureTheory.IntegrableOn.congr_fun hmone h_right ht
  have h : Disjoint (Set.Ico (0 : ℝ ) (1/2)) (Set.Ico (1/2) 1) := by
    simp
  have h0 : Set.Ico (0 : ℝ ) 1 = Set.Ico 0 (1/2) ∪ Set.Ico (1/2) 1 := by
    refine Eq.symm (Ico_union_Ico_eq_Ico ?h₁ ?h₂)
    simp
    linarith
  rw[h0]
  rw[MeasureTheory.setIntegral_union h ht h1 h2 ]
  rw[MeasureTheory.setIntegral_congr_fun hs h_left ,MeasureTheory.setIntegral_congr_fun ht h_right]
  simp
  norm_num


/--
The integral of squere of Haar function over `[0,1)` equals 1.
-/
theorem haar_integral_sqr : ∫ x in Set.Ico 0 1, (haarFunction x) ^ 2 = 1 := by
  have h : EqOn (fun x ↦ haarFunction x ^ 2) 1  (Ico 0 1):= by
    intro x hx
    simp_all
  have h1 : MeasurableSet (Set.Ico (0 : ℝ ) 1) := by
    simp
  rw [MeasureTheory.setIntegral_congr_fun h1 h]
  simp


/--
Definition of scaled Haar function `h_I(x)` for dyadic interval `I = [2^k n, 2^k (n+1))`.
-/
def haarFunctionScaled (k n : ℤ ) (x : ℝ) : ℝ :=
  2^((-k / 2) : ℝ) * haarFunction (2^(-k) * x - n)


/--
Left half of scaled Haar function is equal to `2^(-k / 2)`.
-/
@[simp]
theorem haarFunctionScaled_left_half (k n : ℤ ) (x : ℝ) (h1 : 0 ≤ 2 ^(-k)  * x - n )(h2: 2 ^ (-k)  * x - n < 1 / 2) :
  haarFunctionScaled k n x = 2 ^ ((-k / 2) : ℝ) := by
  simp only [haarFunctionScaled, zpow_neg]
  rw [haarFunction_left_half]
  · simp
  · rw[← zpow_neg]
    constructor
    · linarith
    · linarith



/--
Right half of the scaled Haar function is equal to `-2^(-k / 2)`.
-/
@[simp]
theorem haarFunctionScaled_right_half (k n : ℤ ) (x : ℝ) (h1 : 1 / 2 ≤ 2^(-k) * x - n )(h2: 2 ^(- k) * x - n < 1) :
  haarFunctionScaled k n x = -2 ^ (-k / 2 : ℝ) := by
  simp only [haarFunctionScaled, zpow_neg]
  rw [haarFunction_right_half]
  · simp
  · rw[← zpow_neg]
    constructor
    · linarith
    · linarith

/--
Scaled Haar function is 0 outside `[2^k n, 2^k (n+1))`.
-/
@[simp]
theorem haarFunctionScaled_outside (k n : ℤ ) (x : ℝ)
  (h : 2 ^(- k) * x - n < 0 ∨ 2 ^ (-k) * x - n ≥ 1) :
  haarFunctionScaled k n x = 0 := by
  unfold haarFunctionScaled
  rw [haarFunction_outside _ h]
  simp


/--
Scaled Haar function of non positive `k` and `n ∈ {0,...,2^(-k) -1}` is 0 outside `[0,1)`.
-/
@[simp]
theorem haarFunctionScaled_outside_zero_one {k n : ℤ } {x : ℝ}
  (h : x < 0 ∨ x≥ 1)(hn1 : n ≥ 0)(hn2: n ≤ (2^(-k : ℤ ) -1 : ℝ ))  : haarFunctionScaled k n x = 0 := by
  apply haarFunctionScaled_outside
  rw[zpow_neg ] at hn2
  simp only [zpow_neg, sub_neg, ge_iff_le]
  obtain h_l|h_r := h
  · left
    have : (2 ^ k)⁻¹* x <0 := by
      rw[mul_comm]
      apply mul_neg_of_neg_of_pos
      · linarith
      · simp only [inv_pos]
        refine zpow_pos ?hb.ha k
        linarith
    apply lt_of_lt_of_le this
    simp
    linarith
  · right
    have h1 :  (2 ^ k)⁻¹ * (x-1) +1 ≤  (2 ^ k)⁻¹ * x - ↑n := by
      rw[mul_sub]
      simp only [mul_one]
      rw[sub_add, sub_le_sub_iff_left (a:=((2 ^ k)⁻¹ * x ))]
      exact hn2
    have h2 : 1 ≤   (2 ^ k)⁻¹ * (x-1) +1 := by
      simp
      ring_nf
      simp only [le_neg_add_iff_add_le, add_zero]
      rw[← mul_one (2 ^ k)⁻¹]
      refine (inv_mul_le_iff₀' ?hc).mpr ?_
      · refine zpow_pos ?hb.ha k
      · simp only [mul_one]
        rw[mul_comm, ← mul_assoc]
        have : (2 ^ k : ℝ )* (2 ^ k)⁻¹  = 1 := by
          refine CommGroupWithZero.mul_inv_cancel (2 ^ k) ?_
          refine zpow_ne_zero k ?_
          simp
        rw[this]
        linarith
    exact Preorder.le_trans 1 ((2 ^ k)⁻¹ * (x - 1) + 1) ((2 ^ k)⁻¹ * x - ↑n) h2 h1

/--
Product of scaled Haar functions of the same `k` and different `n, n'` equals 0.
-/

theorem haarFunctionScaled_mul{k n n' : ℤ } (x :ℝ ) (h_diff : n ≠ n') : haarFunctionScaled k n x  * haarFunctionScaled k n' x = 0 := by
  by_cases h: 2 ^ (-k) * x - n < 0 ∨ 2 ^ (-k) * x - n ≥ 1
  · rw[haarFunctionScaled_outside k n]
    · linarith
    exact h
  · rw[not_or] at h
    push_neg at h
    obtain ⟨h_1, h_2⟩ := h
    simp only [zpow_neg] at h_2
    apply lt_add_of_sub_left_lt at h_2
    rw[haarFunctionScaled_outside k n']
    · simp
    · by_cases h1:  n<  n'
      · left
        rw[← Int.add_one_le_iff]at h1
        simp only [zpow_neg, sub_neg]
        apply lt_of_lt_of_le h_2
        norm_cast
      · push_neg at h1
        rw[le_iff_lt_or_eq] at h1
        obtain h_11|h_12 := h1
        · right
          rw[← Int.add_one_le_iff]at h_11
          simp only [zpow_neg, sub_nonneg] at h_1
          simp only [zpow_neg, ge_iff_le]
          rw[le_sub_iff_add_le, add_comm ]
          norm_cast
          refine le_trans ?_ h_1
          norm_cast
        · left
          exfalso
          rw[eq_comm] at h_12
          exact h_diff h_12

/--
Integral of product of scaled Haar functions of the same `k` and different `n, n'` equals 0.
-/
theorem haarFunctionScaled_orthogonal {k n n' : ℤ } (h_diff : n ≠ n') : ∫ x in Set.Ico 0 1, haarFunctionScaled k n x * haarFunctionScaled k n' x = 0 := by
  simp [haarFunctionScaled_mul _ h_diff]



/--
The square of the scaled Haar function is `2^k` in `[2^k n, 2^k (n+1))` and `0` outside.
-/
@[simp]
theorem haarFunctionScaled_sqr (k n : ℤ ) (x : ℝ) (h1 : 0 ≤ 2 ^ (-k) * x - n) (h2 :2 ^ (-k) * x - n < 1) : (haarFunctionScaled k n x) ^ 2 = 2^(-k):= by
  simp only [haarFunctionScaled, zpow_neg]
  rw[mul_pow, haar_sqr]
  simp only [sub_nonneg, mul_ite, mul_one, mul_zero]
  have h : (2 ^ (-k / 2:ℝ) : ℝ ) ^ 2 = 2^(-k) := by
    rw [← Real.rpow_mul_natCast]
    · simp only [Nat.cast_ofNat, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.div_mul_cancel, zpow_neg]
      rw[ ← zpow_neg]
      norm_cast
    · linarith
  split_ifs with h_1
  · obtain ⟨ h_11, h_12⟩ := h_1
    rw[h]
    simp
  · exfalso
    rw[not_and_or] at h_1
    obtain h_11|h_12 := h_1
    · push_neg at h_11
      rw[← zpow_neg] at h_11
      linarith
    · push_neg at h_12
      rw[← zpow_neg] at h_12
      linarith

/--
Product of scaled Haar functions is 0 outside `[2^k n, 2^k (n+1))`.
-/

theorem haarFunction_product0 (k n : ℤ ) (x y : ℝ) (h:  2 ^ (-k) * x - ↑n < 0 ∨ 1≤  2 ^ (-k) * x - ↑n): haarFunctionScaled k n x  * haarFunctionScaled k n y  = 0 := by
  rw[haarFunctionScaled_outside]
  · simp
  · exact h

theorem haarFunction_product0' (k n : ℤ ) (x y : ℝ) (h:  2 ^ (-k) * y - ↑n < 0 ∨ 1≤  2 ^ (-k) * y - ↑n): haarFunctionScaled k n x  * haarFunctionScaled k n y  = 0 := by
  rw[mul_comm]
  apply haarFunction_product0
  exact h

/--
Product of scaled Haar functions is `2^(-k)` on left half of `[2^k n, 2^k (n+1))`.
-/

theorem haarFunction_product1 (k n : ℤ ) (x y : ℝ) (h1: 0 ≤ 2 ^ (-k) * x - ↑n)(h2: 2 ^ (-k) * x - ↑n<1/2) (h3: 0 ≤ 2 ^ (-k) * y - ↑n )(h4:2 ^ (-k) * y - ↑n<1/2): haarFunctionScaled k n x  * haarFunctionScaled k n y  = 2^(-k) := by
  rw[haarFunctionScaled_left_half ,haarFunctionScaled_left_half]
  · rw[← pow_two]
    rw [← Real.rpow_mul_natCast]
    · simp only [Nat.cast_ofNat, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.div_mul_cancel, zpow_neg]
      rw[ ← zpow_neg]
      norm_cast
    · linarith
  · exact h3
  · exact h4
  · exact h1
  · exact h2

/--
Product of scaled Haar functions is `2^(-k)` on right half of `[2^k n, 2^k (n+1))`.
-/

theorem haarFunction_product2 (k n : ℤ ) (x y : ℝ) (h1: 1/2≤ 2 ^ (-k) * x - ↑n)(h2: 2 ^ (-k) * x - ↑n<1) (h3: 1/2 ≤ 2 ^ (-k) * y - ↑n )(h4:2 ^ (-k) * y - ↑n<1): haarFunctionScaled k n x  * haarFunctionScaled k n y  = 2^(-k) := by
  rw[haarFunctionScaled_right_half ,haarFunctionScaled_right_half]
  · simp only [mul_neg, neg_mul, neg_neg, zpow_neg]
    · rw[← pow_two]
      rw [←Real.rpow_mul_natCast]
      · simp only [Nat.cast_ofNat, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, IsUnit.div_mul_cancel]
        rw[ ← zpow_neg]
        norm_cast
      · linarith
  · exact h3
  · exact h4
  · exact h1
  · exact h2

/--
Product of scaled Haar functions is `-2^(-k)` when one takes values from right half and the second one takes values from left half of `[2^k n, 2^k (n+1))`
-/

theorem haarFunction_product3 (k n : ℤ ) (x y : ℝ) (h1: 1/2≤ 2 ^ (-k) * x - ↑n)(h2: 2 ^ (-k) * x - ↑n<1) (h3: 0 ≤ 2 ^ (-k) * y - ↑n )(h4:2 ^ (-k) * y - ↑n<1/2): haarFunctionScaled k n x  * haarFunctionScaled k n y  = -2^(-k) := by
  rw[haarFunctionScaled_right_half ,haarFunctionScaled_left_half]
  · simp only [neg_mul, zpow_neg, neg_inj]
    · rw[← pow_two]
      rw [←Real.rpow_mul_natCast]
      · simp only [Nat.cast_ofNat, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, IsUnit.div_mul_cancel]
        rw[← zpow_neg]
        norm_cast
      · linarith
  · exact h3
  · exact h4
  · exact h1
  · exact h2



/--
The integral of squere of scaled Haar function over `[2^k n, 2^k (n+1))` equals `1`.
-/
theorem haarFunctionScaled_normalization (k n : ℤ ) : ∫ x in Set.Ico (2^k*n : ℝ) (2^k*(n+1) : ℝ), (haarFunctionScaled k n x)^2 = 1 := by
  have h : EqOn (fun (x) ↦ haarFunctionScaled k n x ^ 2) (2 ^ (-k))  (Set.Ico (2^k*n : ℝ) (2^k*(n+1) : ℝ)):= by
    intro x hx
    simp only [Pi.pow_apply, Pi.ofNat_apply, Nat.cast_ofNat, zpow_neg]
    simp only [mem_Ico] at hx
    obtain ⟨hx1,hx2 ⟩ := hx
    rw[haarFunctionScaled_sqr]
    · simp only [zpow_neg]
    · norm_num
      rw[mul_comm, le_mul_inv_iff₀]
      · linarith
      · apply zpow_pos
        simp
    · norm_num
      rw[sub_lt_iff_lt_add', mul_comm, ← lt_mul_inv_iff₀ ]
      · simp
        linarith
      · simp only [inv_pos]
        apply zpow_pos
        simp only [Nat.ofNat_pos]
  have h1 : MeasurableSet (Set.Ico (2^k*n : ℝ) (2^k*(n+1) : ℝ)) := by
    simp
  rw [MeasureTheory.setIntegral_congr_fun h1 h]
  simp only [Pi.pow_apply, Pi.ofNat_apply, Nat.cast_ofNat, zpow_neg, integral_const,
    MeasurableSet.univ, Measure.restrict_apply, univ_inter, Real.volume_Ico, smul_eq_mul]
  have : ((2 ^ k : ℝ ) * (↑n + 1) - 2 ^ k * ↑n) = 2^k := by
    rw[mul_add]
    simp
  rw[this]
  rw[ENNReal.toReal_ofReal]
  · rw[← zpow_neg, ← zpow_add₀]
    · simp only [add_neg_cancel, zpow_zero]
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  · apply le_of_lt
    apply zpow_pos
    simp only [Nat.ofNat_pos]

theorem helphaarzero1 (n k: ℕ) (x : ℝ ) (hn : n ∈ Finset.range (2^(k+1))\ Finset.range (2^k)) (hx : x ∈ Ico 0 0.5 ) : (2^(k+1)*x - n ) ∉ Ico 0 1 := by
  simp only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hn
  simp only [mem_Ico] at hx
  simp only [mem_Ico, Decidable.not_and_iff_or_not]
  left
  push_neg
  calc
    2 ^ (k + 1) * x - ↑n < 2 ^ (k + 1) * 0.5 - ↑n := by
      simp only [sub_lt_sub_iff_right, Nat.ofNat_pos, pow_pos, mul_lt_mul_left]
      exact hx.2
    _= 2^k - n := by
      simp only [sub_left_inj]
      ring
    _≤ 2^k - 2^k := by
      simp only [sub_self, tsub_le_iff_right, zero_add]
      norm_cast
      exact hn.2
    _= 0 := by simp


theorem helphaarzero2 (n k: ℕ) (x : ℝ ) (hn : n ∈ Finset.range (2^k)) (hx : x ∈ Ico 0.5 1 ) : (2^(k+1)*x - n ) ∉ Ico 0 1 := by
  simp only [Finset.mem_range] at hn
  simp only [mem_Ico] at hx
  simp only [mem_Ico, Decidable.not_and_iff_or_not]
  right
  push_neg
  calc
    2 ^ (k + 1) * x - ↑n ≥  2 ^ (k + 1) * 0.5 - ↑n := by
      simp only [ge_iff_le, tsub_le_iff_right, sub_add_cancel, Nat.ofNat_pos, pow_pos,
        mul_le_mul_left]
      exact hx.1
    _= 2^k - n := by
      simp only [sub_left_inj]
      ring
    _≥  2^k - 2^k +1 := by
      simp only [sub_self, zero_add, ge_iff_le]
      rw[Nat.lt_iff_add_one_le, add_comm ] at hn
      rw[le_sub_iff_add_le]
      norm_cast
    _= 1 := by simp

theorem haarzero1 (n k: ℕ) (x : ℝ ) (hn : n ∈ Finset.range (2^(k+1))\ Finset.range (2^k)) (hx : x ∈ Ico 0 0.5 ) : haarFunctionScaled (-(k+1))  n x = 0 := by
have h : (2^(k+1)*x - n ) < 0 ∨ (2^(k+1)*x - n ) ≥ 1 := by
  by_contra hf
  push_neg at hf
  rw[← mem_Ico] at hf
  apply helphaarzero1
  exact hn
  exact hx
  exact hf
rw[haarFunctionScaled_outside ]
exact h



theorem haarzero2 (n k: ℕ) (x : ℝ ) (hn : n ∈ Finset.range (2^k)) (hx : x ∈ Ico 0.5 1 ) : haarFunctionScaled (-(k+1))  n x = 0 := by
have h : (2^(k+1)*x - n ) < 0 ∨ (2^(k+1)*x - n ) ≥ 1 := by
  by_contra hf
  push_neg at hf
  rw[← mem_Ico] at hf
  apply helphaarzero2
  exact hn
  exact hx
  exact hf
rw[haarFunctionScaled_outside ]
exact h

theorem haarsumzero1 (k : ℕ ) (x : ℝ ) (hx : x ∈ Ico 0 0.5 ) : ∑ n in Finset.range (2^(k+1))\ Finset.range (2^k), haarFunctionScaled (-(k+1)) n x = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  apply haarzero1
  · exact hn
  · exact hx


theorem haarsumzero2 (k : ℕ ) (x : ℝ ) (hx : x ∈ Ico 0.5 1 ) : ∑ n in Finset.range (2^k), haarFunctionScaled (-(k+1)) n x = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  apply haarzero2
  · exact hn
  · exact hx


/--
Definition of the Rademacher function `r_n(x)`.
-/
def rademacherFunction (k : ℕ) (t : ℝ) : ℝ :=
  2^(- k / 2 : ℝ ) * ∑ n in Finset.range (2^k), haarFunctionScaled (-k) n t


def rademacherFunctionzeroleft (t : ℝ) (h1 : 0≤ t ) (h2 : t< 0.5): rademacherFunction 0 t = 1 := by
  simp only [rademacherFunction, CharP.cast_eq_zero, neg_zero, zero_div, Real.rpow_zero, pow_zero,
    Finset.range_one, haarFunctionScaled, Int.cast_zero, zpow_zero, one_mul, Int.cast_natCast,
    Finset.sum_singleton, sub_zero]
  apply haarFunction_left_half
  constructor
  · exact h1
  · ring_nf at h2
    exact h2

  def rademacherFunctionzeroright (t : ℝ) (h1 : 0.5≤ t ) (h2 : t< 1): rademacherFunction 0 t = -1 := by
  simp only [rademacherFunction, CharP.cast_eq_zero, neg_zero, zero_div, Real.rpow_zero, pow_zero,
    Finset.range_one, haarFunctionScaled, Int.cast_zero, zpow_zero, one_mul, Int.cast_natCast,
    Finset.sum_singleton, sub_zero]
  apply haarFunction_right_half
  constructor
  · ring_nf at h1
    exact h1
  · exact h2

/--
Rademacher function is zero outisde `[0,1)`.
-/

@[simp]
theorem rademacherFunction_outside (k : ℕ) (t : ℝ) (h : t < 0 ∨ t ≥ 1) :
  rademacherFunction k t = 0 := by
  unfold rademacherFunction
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro l hl
  have h1 : l ≤ (2^(k : ℕ  ) : ℤ   )-1 := by
    simp only [Finset.range, Finset.mem_mk, Multiset.mem_range] at hl
    refine Int.le_sub_one_of_lt ?H
    exact_mod_cast hl
  have hk : (-k : ℤ ) ≤ 0 := by
    simp
  apply haarFunctionScaled_outside_zero_one h (Int.ofNat_zero_le l)
  simp only [Int.cast_natCast, neg_neg, zpow_natCast]
  exact_mod_cast h1

theorem rademacherassumofhaar (k : ℕ ) ( x : ℝ ) : rademacherFunction (k+1) x = 2^(- (k+1) / 2 : ℝ ) * ∑ n ∈ Finset.range (2^k), haarFunctionScaled (-(k+1)) n x + 2^(- (k+1) / 2 : ℝ ) * ∑ n ∈  Finset.range (2^(k+1))\ Finset.range (2^k), haarFunctionScaled (-(k+1)) n x := by
  unfold rademacherFunction
  push_cast
  rw[← left_distrib]
  simp only [ Int.reduceNeg, mul_eq_mul_left_iff, Nat.ofNat_nonneg]
  left
  have h1 : Disjoint (Finset.range (2^k)) (Finset.range (2^(k+1))\ Finset.range (2^k)) := by
    apply disjoint_sdiff_self_right
  have h2 : Finset.range (2^(k+1)) = Finset.disjUnion (Finset.range (2^k)) (Finset.range (2^(k+1))\ Finset.range (2^k)) h1 := by
    simp only [Finset.disjUnion_eq_union, Finset.union_sdiff_self_eq_union, Finset.right_eq_union,
      Finset.range_subset]
    ring_nf
    simp only [Nat.ofNat_pos, pow_pos, le_mul_iff_one_le_right, Nat.one_le_ofNat]
  rw[h2]
  rw[Finset.sum_disjUnion (α := ℕ) h1 (f := fun n ↦ haarFunctionScaled (-(k + 1)) n x)]
  congr

theorem rademacher2assumofhaar1 (k : ℕ ) ( x : ℝ ) : rademacherFunction k (2*x) =  2^(- (k+1)/ 2 : ℝ ) * ∑ n ∈  Finset.range (2^k), haarFunctionScaled (-(k+1)) n x := by
  unfold rademacherFunction
  unfold haarFunctionScaled
  simp only [Int.cast_neg, Int.cast_natCast, neg_neg, zpow_natCast, Int.reduceNeg,
    Int.cast_add, Int.cast_one]
  rw[Finset.mul_sum, Finset.mul_sum, ← mul_assoc, ← pow_succ]
  apply Finset.sum_congr rfl
  intro n hn
  rw[← mul_assoc, ← mul_assoc]
  congrm ?_ * haarFunction (?_)
  · have h1 : (2 : ℝ) ^ ((k : ℝ ) / 2) ≠ 0 := by
      by_cases hk : k = 0
      · rw[hk]
        simp only [CharP.cast_eq_zero, zero_div, Real.rpow_zero, ne_eq, one_ne_zero,
          not_false_eq_true]
      rw[Real.rpow_ne_zero]
      · simp
      · simp
      · simp only [ne_eq, div_eq_zero_iff, Nat.cast_eq_zero, OfNat.ofNat_ne_zero, or_false]
        exact hk
    have h2 : (2 : ℝ) ^ (((k : ℝ ) +1)/ 2) ≠ 0 := by
      rw[Real.rpow_ne_zero]
      · simp
      · simp
      · simp only [ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
        exact Nat.cast_add_one_ne_zero k
    simp_rw [neg_div, Real.rpow_neg zero_le_two]
    rw [mul_comm, GroupWithZero.mul_inv_cancel _ h1, mul_comm, GroupWithZero.mul_inv_cancel _ h2]
  · norm_cast

theorem rademacher2assumofhaar2 (k : ℕ ) ( x : ℝ ) : rademacherFunction k (2*x -1 ) =  2^(- (k+1)/ 2 : ℝ ) * ∑ n ∈  Finset.range (2^(k+1))\ Finset.range (2^k), haarFunctionScaled (-(k+1)) n x := by
  unfold rademacherFunction
  unfold haarFunctionScaled
  simp only [Int.cast_neg, Int.cast_natCast, neg_neg, zpow_natCast, Int.reduceNeg,
    Int.cast_add, Int.cast_one]
  rw[Finset.mul_sum, Finset.mul_sum]
  have h1 : (2 : ℝ) ^ ((k : ℝ ) * (1/2)) ≠ 0 := by
    by_cases hk : k = 0
    · rw[hk]
      simp only [CharP.cast_eq_zero, one_div, zero_mul, Real.rpow_zero, ne_eq, one_ne_zero,
        not_false_eq_true]
    · rw[Real.rpow_ne_zero]
      · simp
      · simp
      · simp only [one_div, ne_eq, mul_eq_zero, Nat.cast_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
        or_false]
        exact hk
  have h2 : (2 : ℝ) ^ ((1/2) + ((k : ℝ )* (1/2))) ≠ 0 := by
    rw[Real.rpow_ne_zero]
    · simp
    · simp
    · simp only [one_div, ne_eq]
      push_neg
      ring_nf
      rw[ne_iff_lt_or_gt]
      right
      calc
        ((1/2) :ℝ ) + ↑k * (1 / 2) ≥  1/2 := by linarith
        _>0 := by linarith
  let i : ℕ → ℕ  := fun i ↦ i + 2^k
  apply Finset.sum_nbij i
  · intro m
    simp only [Finset.mem_range, Finset.mem_sdiff, not_lt, i,le_add_iff_nonneg_left, zero_le, and_true, pow_succ, mul_comm, two_mul, add_lt_add_iff_right, imp_self]
  · unfold InjOn
    simp only [Finset.coe_range, mem_Iio]
    intro z hz
    intro y hy
    intro h
    simp only [add_left_inj, i] at h
    exact h
  · simp only [Finset.coe_range, Finset.coe_sdiff, Iio_diff_Iio]
    unfold SurjOn
    intro y hy
    simp only [mem_image, mem_Iio,i]
    simp only [mem_Ico] at hy
    use  y - 2^k
    constructor
    · refine Nat.sub_lt_left_of_lt_add ?_ ?_
      · exact hy.1
      · rw[← mul_two, mul_comm, ← Nat.pow_add_one' ]
        exact hy.2
    · refine Nat.sub_add_cancel ?_
      exact hy.1
  · intro a ha
    rw[← mul_assoc]
    simp only [i]
    push_cast
    rw[mul_sub, ← mul_assoc, mul_comm (2^k), mul_one, ← pow_succ']
    ring_nf
    congrm ?_ * haarFunction (?_)
    · simp_rw [neg_div]
      have h0 : -1 * (1 / 2) + -((k:ℝ) * (1 / 2)) = -(1 / 2 + ↑k * (1 / 2)) :=by
        rw[← neg_eq_neg_one_mul, neg_add]
      rw[neg_eq_neg_one_mul, ← mul_assoc, mul_neg_one, neg_eq_neg_one_mul, mul_assoc, neg_one_mul, h0, Real.rpow_neg zero_le_two, Real.rpow_neg zero_le_two]
      rw [mul_comm, GroupWithZero.mul_inv_cancel _ h1, mul_comm, GroupWithZero.mul_inv_cancel _ h2]
    simp only [add_left_inj]
    rw[mul_assoc, ← pow_succ]
    simp only [mul_eq_mul_left_iff]
    left
    norm_cast
    simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, pow_right_inj₀]
    linarith


theorem rademachernext (k : ℕ ) ( x : ℝ ) : rademacherFunction (k+1) x  = rademacherFunction k (2*x) + rademacherFunction k (2*x -1 ) := by
  rw[rademacherassumofhaar, rademacher2assumofhaar1, rademacher2assumofhaar2]

theorem rademachernextfirsthalf (k : ℕ ) ( x : ℝ ) (hx : x ∈ Ico 0 0.5) : rademacherFunction (k+1) x  = rademacherFunction k (2*x) := by
  rw[rademachernext]
  simp only [add_right_eq_self]
  unfold rademacherFunction
  simp only [mul_eq_zero, Nat.ofNat_nonneg]
  right
  unfold haarFunctionScaled
  simp only [Int.cast_neg, Int.cast_natCast, neg_neg, zpow_natCast]
  ring_nf
  rw[mul_assoc, ← pow_succ 2 k]
  simp_rw [neg_sub_left]
  rw[Finset.sum_eq_zero]
  intro i hi
  set j:= 2 ^ k + i with hj
  have hj0 : j ∈ Finset.range (2 ^ (k+1))\Finset.range (2 ^ k) :=by
    rw[hj]
    simp only [Finset.mem_sdiff, Finset.mem_range, add_lt_iff_neg_left, not_lt_zero',
      not_false_eq_true, and_true, pow_add, Nat.pow_one, Nat.mul_two, add_lt_add_iff_left]
    simp only [Finset.mem_range] at hi
    exact hi
  norm_cast
  rw[← hj]
  push_cast
  have h : haarFunctionScaled (-(k + 1)) j x = 0 := by
    apply haarzero1
    · exact hj0
    · exact hx
  unfold haarFunctionScaled at h
  simp only [neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    neg_neg, mul_eq_zero, Nat.ofNat_nonneg] at h
  simp only [one_div, mul_eq_zero, Nat.ofNat_nonneg]
  right
  rw[mul_comm]
  apply Or.resolve_left h
  push_neg
  refine (Real.rpow_ne_zero ?_ ?_).mpr ?_
  · linarith
  · simp only [ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
    linarith
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]


theorem rademachernextsecondhalf (k : ℕ ) ( x : ℝ ) (hx : x ∈ Ico 0.5 1) : rademacherFunction (k+1) x  = rademacherFunction k (2*x - 1) := by
  rw[rademachernext]
  simp only [add_left_eq_self]
  unfold rademacherFunction
  simp only [mul_eq_zero, Nat.ofNat_nonneg]
  right
  unfold haarFunctionScaled
  simp only [Int.cast_neg, Int.cast_natCast, neg_neg, zpow_natCast]
  ring_nf
  rw[mul_assoc, ← pow_succ 2 k]
  rw[Finset.sum_eq_zero]
  intro i hi
  have h : haarFunctionScaled (-(k + 1)) i x = 0 := by
    apply haarzero2
    · exact hi
    · exact hx
  unfold haarFunctionScaled at h
  simp only [neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    neg_neg, mul_eq_zero, Nat.ofNat_nonneg] at h
  simp only [one_div, mul_eq_zero, Nat.ofNat_nonneg]
  right
  rw[mul_comm]
  apply Or.resolve_left h
  push_neg
  refine (Real.rpow_ne_zero ?_ ?_).mpr ?_
  · linarith
  · simp only [ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
    linarith
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

theorem rad_sqr {k : ℕ} {x : ℝ } (hx1: 0≤ x) (hx2 : x < 1) : (rademacherFunction k x )^ 2 = 1 := by
  unfold rademacherFunction
  unfold haarFunctionScaled
  rw[mul_comm, Finset.sum_mul]


  sorry

/- **ToDo** : Prove statements about product of Rademacher functions and its integrals. -/
end Haar
