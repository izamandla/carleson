
import Carleson.ToMathlib.BoundedCompactSupport
import Carleson.Project.modules.DyadicStructures
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


open Function Set MeasureTheory BoundedCompactSupport DyadicStructures--Classical
noncomputable section

/- ## Walsh Functions and Walsh-Fourier Series -/
namespace Walsh


/--
Definition of Walsh function.
-/
def walsh (n : ℕ) : ℝ → ℝ
| x =>
  if x <0 ∨  1 ≤  x then 0
  else if x < 1/2 then
    let m := n / 2
    if n = 0 then 1
    else walsh m (2 * x)
  else
    if n = 0 then 1
    else
      let m := n / 2
      if  n % 2 = 0 then walsh m (2 * x - 1)
      else -walsh m (2 * x - 1)


/--
Walsh function is 0 outisde`[0,1)`.
-/
@[simp]
theorem walsh_not_in {n : ℕ} (x : ℝ) (h : x < 0 ∨ 1 ≤ x) : walsh n x = 0 := by
  unfold walsh
  split_ifs with h1 h2
  · exact if_pos h
  · simp only [h, ↓reduceIte]
  simp only [h, ↓reduceIte]

/--
Walsh function for `n=0` is 1 on `[0,1)`.
-/
@[simp]
theorem walsh_zero {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 1) : walsh 0 x = 1 := by
  simp [walsh, h1,h2]


/--
Walsh function for `n=1` is 1 on the left half of `[0,1)`.
-/
@[simp]
theorem walsh_one_left (x : ℝ) (h1 : 0 ≤ x) (h2 : x < 1 / 2) : walsh 1 x =  1:= by
  simp only [walsh, one_div, one_ne_zero, ↓reduceIte, Nat.reduceDiv, ite_self, Nat.mod_succ,
    sub_neg]
  split_ifs with h_1 h_2 h_3 h_4
  · exfalso
    obtain h_l|h_r := h_1
    · linarith
    · linarith
  · exfalso
    obtain h_l|h_r := h_3
    · linarith
    · linarith
  · rfl
  · exfalso
    obtain h_l|h_r := h_4
    · push_neg at h_2
      simp at h2
      linarith
    · linarith
  · exfalso
    push_neg at h_1 h_4
    linarith

/--
Walsh function for `n=1` is 1 on the right half of `[0,1)`.
-/

@[simp]
theorem walsh_one_right (x : ℝ) (h1 : 1 / 2 ≤ x) (h2 : x < 1) : walsh 1 x = -1:= by
  simp only [walsh, one_div, one_ne_zero, ↓reduceIte, Nat.reduceDiv, ite_self, Nat.mod_succ,
    sub_neg]
  split_ifs with h_1 h_2 h_3 h_4
  · exfalso
    obtain h_l|h_r := h_1
    · linarith
    · linarith
  · exfalso
    obtain h_l|h_r := h_3
    · linarith
    · push_neg at h_1
      simp at h1
      linarith
  · exfalso
    push_neg at h_1 h_3
    linarith
  · exfalso
    obtain h_l|h_r := h_4
    · push_neg at h_2 h_1
      rw[inv_le_iff_one_le_mul₀ (zero_lt_two)] at h_2
      linarith
    · linarith
  · rfl


/--
Walsh function for n being even on the left half of `[0,1)`.
-/
theorem walsh_even_left {n : ℕ} {x : ℝ} (h2 : x < 1 / 2) : walsh (2 * n) x = walsh n (2 * x) := by
  conv_lhs =>
    unfold walsh
  simp only [one_div, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, ne_eq, not_false_eq_true,
    mul_div_cancel_left₀, Nat.mul_mod_right, ↓reduceIte]
  split_ifs with h_1 h_2 h_3 h_4
  · obtain hl|hp := h_1
    · rw[walsh_not_in]
      left
      apply mul_neg_of_pos_of_neg
      · simp only [Nat.ofNat_pos]
      exact hl
    · linarith
  · push_neg at h_1
    rw[h_3]
    rw[walsh_zero]
    · linarith
    · linarith
  · rfl
  · push_neg at h_1 h_2
    rw[h_4]
    rw[walsh_zero]
    · linarith
    · linarith
  · push_neg at h_1 h_2 h_4
    exfalso
    linarith

/--
Walsh function for n being even on the right half of `[0,1)`.
-/
theorem walsh_even_right {n : ℕ} {x : ℝ} (h1 : 1 / 2 ≤ x) : walsh (2 * n) x = walsh n (2 * x - 1) := by
  conv_lhs =>
    unfold walsh
  simp only [one_div, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, ne_eq, not_false_eq_true,
    mul_div_cancel_left₀, Nat.mul_mod_right, ↓reduceIte]
  split_ifs with h_1 h_2 h_3 h_4
  · obtain hl|hp := h_1
    · linarith
    · rw[walsh_not_in]
      right
      linarith
  · push_neg at h_1
    rw[h_3]
    rw[walsh_zero]
    · linarith
    · linarith
  · push_neg at h_1 h_3
    exfalso
    linarith
  · push_neg at h_1 h_2
    rw[h_4]
    rw[walsh_zero]
    · linarith
    · linarith
  · rfl


/--
Walsh function for n being odd on the left half of `[0,1)`.
-/


theorem walsh_odd_left {n : ℕ} {x : ℝ} (h2 : x < 1 / 2) : walsh (2 * n +1) x = walsh n (2 * x) := by
  conv_lhs =>
    unfold walsh
  simp only [one_div, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    one_ne_zero, and_false, ↓reduceIte]
  have h_odd0 : Odd (2 * n + 1) := by
    simp
  have h_oddp : 2*((2 * n + 1  )/2) = 2*n := by
    rw[Nat.odd_iff] at h_odd0
    rw[Nat.two_mul_odd_div_two h_odd0]
    simp
  have h_odd : (2 * n + 1) / 2 = n := by
    rw[← Nat.mul_left_inj (a:=2), mul_comm, h_oddp]
    linarith
    simp
  split_ifs with h_1 h_2 h_3
  · rw[walsh_not_in]
    obtain hl|hp := h_1
    · left
      apply mul_neg_of_pos_of_neg
      · simp only [Nat.ofNat_pos]
      exact hl
    · linarith
  · push_neg at h_1
    rw[h_odd]
  · rw[h_odd]
    push_neg at h_1 h_2
    exfalso
    rw[Nat.odd_iff] at h_odd0
    linarith
  · push_neg at h_1 h_2 h_3
    rw[h_odd]
    linarith

/--
Walsh function for n being odd on the right half of `[0,1)`.
-/


theorem walsh_odd_right {n : ℕ} {x : ℝ} (h1 : 1 / 2 ≤ x) : walsh (2 * n + 1) x =- walsh n (2 * x - 1) := by
  conv_lhs =>
    unfold walsh
  simp only [one_div, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    one_ne_zero, and_false, ↓reduceIte]
  have h_odd0 : Odd (2 * n + 1) := by
    simp
  have h_oddp : 2*((2 * n + 1  )/2) = 2*n := by
    rw[Nat.odd_iff] at h_odd0
    rw[Nat.two_mul_odd_div_two h_odd0]
    simp
  have h_odd : (2 * n + 1) / 2 = n := by
    rw[← Nat.mul_left_inj (a:=2), mul_comm, h_oddp]
    linarith
    simp
  split_ifs with h_1 h_2 h_3
  · obtain hl|hp := h_1
    · linarith
    · rw[walsh_not_in]
      · simp
      · right
        linarith
  · push_neg at h_1
    exfalso
    linarith
  · rw[h_odd]
    push_neg at h_1 h_2
    exfalso
    rw[Nat.odd_iff] at h_odd0
    linarith
  · push_neg at h_1 h_2 h_3
    rw[h_odd]


/--
Relation between Walsh function of `2n` and `2n+1`.
-/
theorem walsh_even_odd_left {n : ℕ} {x : ℝ} (h2 : x < 1 / 2): walsh (2*n) x = walsh (2*n +1) x:= by
  rw[ walsh_even_left h2, walsh_odd_left h2]

theorem walsh_even_odd_right {n : ℕ} {x : ℝ} (h1 : 1 / 2 ≤ x): walsh (2*n) x = - walsh (2*n +1) x:= by
  rw[ walsh_even_right h1, walsh_odd_right h1]
  simp

/--
Walsh functions are nonzero on `[0,1)`.
-/
theorem walsh_in (n : ℕ) : ∀ x : ℝ, 0 ≤ x ∧  x < 1 → walsh n x ≠ 0 := by
  induction' n using Nat.strong_induction_on with n ih
  intro x hx
  set k := n/2 with h_k
  by_cases hzero :n = 0
  · rw[hzero, walsh_zero]
    · linarith
    · let h1:= hx.1
      exact h1
    · let h2:= hx.2
      exact h2
  · by_cases hone : n = 1
    · rw[hone]
      by_cases h : x< 1/2
      · rw[walsh_one_left]
        · linarith
        · linarith
        · exact h
      · push_neg at h
        rw[walsh_one_right]
        · linarith
        · exact h
        · linarith
    · have hk2 : k < n := by
        push_neg at hzero
        rw[h_k]
        exact Nat.bitwise_rec_lemma hzero
      by_cases h0 : Odd n
      · have hk1 : 2*k+1 = n := by
          rw[h_k]
          rw[mul_comm]
          apply Nat.div_two_mul_two_add_one_of_odd
          exact h0
        rw[← hk1]
        by_cases h : x<1/2
        · rw[walsh_odd_left]
          · set y:= 2* x with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · exact h
        · push_neg at h
          rw[walsh_odd_right]
          · set y:= 2* x -1 with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            simp only [ne_eq, neg_eq_zero]
            exact ih k hk2 y hy
          · exact h
      · push_neg at h0
        simp only [Nat.not_odd_iff_even] at h0
        have hk1 : 2*k = n := by
          rw[h_k]
          rw[mul_comm]
          apply Nat.div_two_mul_two_of_even
          exact h0
        rw[← hk1]
        by_cases h : x<1/2
        · rw[walsh_even_left]
          · set y:= 2* x with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · exact h
        · push_neg at h
          rw[walsh_even_right]
          · set y:= 2* x -1 with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · exact h

--ten dowód jest taki sam jak wcześniejszy - to nie ma sensu -> wcześniejsze twierdzenie powinno korzystać z wcześniejszego
theorem walsh_sqr1 (n : ℕ) : ∀ x : ℝ, 0 ≤ x ∧  x < 1 → (walsh n x)*(walsh n x) =1 := by
  induction' n using Nat.strong_induction_on with n ih
  intro x hx
  set k := n/2 with h_k
  by_cases hzero :n = 0
  · rw[hzero, walsh_zero]
    · linarith
    · let h1:= hx.1
      exact h1
    · let h2:= hx.2
      exact h2
  · by_cases hone : n = 1
    · rw[hone]
      by_cases h : x< 1/2
      · rw[walsh_one_left]
        · linarith
        · linarith
        · exact h
      · push_neg at h
        rw[walsh_one_right]
        · linarith
        · exact h
        · linarith
    · have hk2 : k < n := by
        push_neg at hzero
        rw[h_k]
        exact Nat.bitwise_rec_lemma hzero
      by_cases h0 : Odd n
      · have hk1 : 2*k+1 = n := by
          rw[h_k]
          rw[mul_comm]
          apply Nat.div_two_mul_two_add_one_of_odd
          exact h0
        rw[← hk1]
        by_cases h : x<1/2
        · rw[walsh_odd_left]
          · set y:= 2* x with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · exact h
        · push_neg at h
          rw[walsh_odd_right]
          · set y:= 2* x -1 with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            simp only [mul_neg, neg_mul, neg_neg]
            exact ih k hk2 y hy
          · exact h
      · push_neg at h0
        simp only [Nat.not_odd_iff_even] at h0
        have hk1 : 2*k = n := by
          rw[h_k]
          rw[mul_comm]
          apply Nat.div_two_mul_two_of_even
          exact h0
        rw[← hk1]
        by_cases h : x<1/2
        · rw[walsh_even_left]
          · set y:= 2* x with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · exact h
        · push_neg at h
          rw[walsh_even_right]
          · set y:= 2* x -1 with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · exact h


/--
Squere of Wlash functions is 1 on `[0,1).`
-/

theorem sqr_walsh {n : ℕ} (x : ℝ) (h1 : 0 ≤ x) (h2 : x < 1) : (walsh n x)*(walsh n x) = 1 := by
  apply walsh_sqr1
  constructor
  · exact h1
  · exact h2

/--
Walsh function is zero outside the interval `[0, 1)`.
-/
@[simp]
theorem walsh_zero_outside_domain (n : ℕ) (x : ℝ) (h : x < 0 ∨ x ≥ 1) : walsh n x = 0 := by
simp [walsh, h]



theorem walsh_values {n : ℕ} {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 1) : walsh n x = 1 ∨ walsh n x =-1 := by
  rw[← sq_eq_one_iff, pow_two]
  apply sqr_walsh
  · exact h1
  exact h2


/--
Product of Wlash functions of fixed `n` and different arguments is 0 outside `[0, 1)`.
-/
theorem mul_walsh_outside {n : ℕ} (x y : ℝ) (h : x < 0 ∨ 1 ≤ x) : (walsh n x)*(walsh n y ) =  0:= by
  rw[walsh_not_in]
  · simp only [zero_mul]
  exact  h


theorem mul_walsh_outside' {n : ℕ} (x y : ℝ) (h : x < 0 ∨ 1 ≤ x) : (walsh n y )*(walsh n x) =  0:= by
  rw[mul_comm, mul_walsh_outside]
  exact  h





/--
Walsh inner product definition.
-/
def walshInnerProduct (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Set.Ico 0 1, f x * walsh n x



/--
`n`th Walsh inner product of walsh function of `m` is equal to the `m`th Walsh inner product of walsh function of `n`.
-/
theorem walshInnermul {n m : ℕ} : walshInnerProduct (walsh n) m = walshInnerProduct (walsh m) n := by
  simp only [walshInnerProduct]
  have h1 : EqOn ((walsh n)*(walsh m)) ((walsh m)*(walsh n))  (Set.Ico 0 (1:ℝ)):= by
    rw[mul_comm]
    exact fun ⦃x⦄ ↦ congrFun rfl
  have h2 : MeasurableSet (Set.Ico 0 (1:ℝ)) := by
    simp
  change ∫ (x : ℝ) in Ico 0 1, (walsh n * walsh m) x = ∫ (x : ℝ) in Ico 0 1, (walsh m * walsh n) x
  rw[MeasureTheory.setIntegral_congr_fun h2 h1]



/--
Walsh functions have norm 1.
-/
theorem walsh_norm (n : ℕ) :
  walshInnerProduct (walsh n) n = 1 := by
  unfold walshInnerProduct
  have hs : MeasurableSet (Set.Ico 0 (1 : ℝ )) := by
    simp
  have h1 : EqOn ((walsh n)*(walsh n)) 1  (Set.Ico 0 (1:ℝ)):= by
    intro x hx
    rw [Pi.mul_apply, Pi.one_apply, sqr_walsh ]
    · simp_all
    · simp_all
  change ∫ (x : ℝ) in Ico 0 1, (walsh n * walsh n) x = 1
  rw[MeasureTheory.setIntegral_congr_fun hs h1]
  simp

theorem walsh_norm' (n : ℕ) :  ∫ (x : ℝ) in Ico 0 1, walsh n x * walsh n x = 1:= by
  have hs : MeasurableSet (Set.Ico 0 (1 : ℝ )) := by
    simp
  have h1 : EqOn ((walsh n)*(walsh n)) 1  (Set.Ico 0 (1:ℝ)):= by
    intro x hx
    rw [Pi.mul_apply, Pi.one_apply, sqr_walsh ]
    · simp_all
    · simp_all
  change ∫ (x : ℝ) in Ico 0 1, (walsh n * walsh n) x = 1
  rw[MeasureTheory.setIntegral_congr_fun hs h1]
  simp
/--
Walsh functions are orthogonal.
-/
theorem walsh_ort_same {n m : ℕ} (h : m = n) : walshInnerProduct (walsh n) m  = 1 := by
  rw [h]
  apply walsh_norm




theorem walsh_leq_one {n : ℕ} {x : ℝ} : |walsh n x| ≤ 1 := by
  by_cases h : 0 ≤ x ∧ x < 1
  · rw [@abs_le_one_iff_mul_self_le_one, walsh_sqr1]
    exact h
  · rw[Mathlib.Tactic.PushNeg.not_and_or_eq ] at h
    simp only [not_le, not_lt, ← ge_iff_le] at h
    rw[walsh_zero_outside_domain n  x h ]
    simp


/--
Multiplication Walsh inner product by scalar.
-/
theorem walshInnerProduct_smul (c : ℝ) (f : ℝ → ℝ) (n : ℕ) :
  walshInnerProduct (fun x => c * f x) n = c * walshInnerProduct f n := by
  simp only [walshInnerProduct]
  simp_rw[← MeasureTheory.integral_const_mul, mul_assoc]


/--
Multiplication Walsh inner product by function.
-/
theorem mul_walshInnerProduct (f g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
  walshInnerProduct (fun y ↦ g x * f y) n = ∫ y in Set.Ico 0 1, g x * f y * walsh n y := by
  unfold walshInnerProduct
  simp

theorem add_walshInnerProduct (f g : ℝ → ℝ) (n : ℕ) :
  walshInnerProduct (fun y ↦ g y + f y) n = ∫ y in Set.Ico 0 1, (g y + f y) * walsh n y := by
  unfold walshInnerProduct
  simp


/--
Definition of Walsh Fourier partial sum.
-/
def walshFourierPartialSum (f : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
 fun x => ∑ n ∈ Finset.range (N + 1), (walshInnerProduct f n) * walsh n x

/--
Definition of Walsh Fourier Series.
-/
def walshFourierSeries (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => tsum (fun N => walshFourierPartialSum f N x)





theorem relbetweeninteven1 {n : ℕ} : ∫ x in Set.Ico 0 0.5 ,  walsh n (2*x) = ∫ x in Set.Ico 0 0.5, walsh (2*n) x := by
  refine Eq.symm (MeasureTheory.setIntegral_congr_ae₀ ?_ ?_)
  · simp
  · apply Filter.Eventually.of_forall
    intro z hz
    simp at hz
    ring_nf at hz
    rw[walsh_even_left hz.2]


theorem relbetweeninteven2 {n : ℕ} : ∫ x in Set.Ico 0.5 1,  walsh n (2*x-1) = ∫ x in Set.Ico 0.5 1, walsh (2*n) x := by
  refine Eq.symm (MeasureTheory.setIntegral_congr_ae₀ ?_ ?_)
  · simp
  · apply Filter.Eventually.of_forall
    intro z hz
    simp at hz
    ring_nf at hz
    rw[walsh_even_right hz.1]

theorem relbetweenintodd1 {n : ℕ} : ∫ x in Set.Ico 0 0.5 ,  walsh n (2*x) = ∫ x in Set.Ico 0 0.5, walsh (2*n +1) x := by
  refine Eq.symm (MeasureTheory.setIntegral_congr_ae₀ ?_ ?_)
  · simp
  · apply Filter.Eventually.of_forall
    intro z hz
    simp at hz
    ring_nf at hz
    rw[walsh_odd_left hz.2]

theorem relbetweenintodd2 {n : ℕ} : ∫ x in Set.Ico 0.5 1,  walsh n (2*x-1) = - ∫ x in Set.Ico 0.5 1, walsh (2*n+1) x := by
  rw[← MeasureTheory.integral_neg]
  refine Eq.symm (MeasureTheory.setIntegral_congr_ae₀ ?_ ?_)
  · simp
  · apply Filter.Eventually.of_forall
    intro z hz
    simp at hz
    ring_nf at hz
    rw[walsh_odd_right hz.1]
    simp


theorem walsh0asfun : walsh 0 = Set.indicator (Set.Ico 0 1) (fun _ ↦ 1 : ℝ → ℝ ) := by
  ext x
  rw[indicator]
  simp only [mem_Ico]
  split_ifs with h1
  · rw[walsh_zero h1.1 h1.2]
  · rw[Decidable.not_and_iff_or_not] at h1
    push_neg at h1
    rw[← ge_iff_le] at h1
    rw[walsh_zero_outside_domain]
    exact h1

theorem walshevenasfun {n : ℕ} : walsh (2*n)  = Set.indicator (Set.Ico 0 0.5) (fun x ↦ walsh n (2*x) : ℝ → ℝ )  +  Set.indicator (Set.Ico 0.5 1) (fun x ↦ walsh n (2*x -1) : ℝ → ℝ )  := by
  ext x
  simp only [Pi.add_apply]
  rw[indicator, indicator]
  split_ifs with h1 h2 h3
  · exfalso
    simp at h1
    simp at h2
    linarith
  · simp only [add_zero]
    rw[walsh_even_left]
    simp at h1
    ring_nf at h1
    exact h1.2
  · simp only [zero_add]
    rw[walsh_even_right]
    simp at h3
    ring_nf at h3
    exact h3.1
  · simp only [add_zero]
    simp only [mem_Ico, not_and, not_lt] at h3
    simp only [mem_Ico, not_and, not_lt] at h1
    rw[walsh_zero_outside_domain  ]
    by_contra h
    push_neg at h
    obtain ⟨hx₀, hx₁⟩ := h
    have h0_5 : 0.5 ≤ x := h1 hx₀
    have h1' : 1 ≤ x := h3 h0_5
    linarith

theorem walshoddasfun {n : ℕ} : walsh (2*n +1)  = Set.indicator (Set.Ico 0 0.5) (fun x ↦ walsh n (2*x) : ℝ → ℝ )  +  Set.indicator (Set.Ico 0.5 1) (fun x ↦ - walsh n (2*x -1) : ℝ → ℝ )  := by
  ext x
  simp only [Pi.add_apply]
  rw[indicator, indicator]
  split_ifs with h1 h2 h3
  · exfalso
    simp at h1
    simp at h2
    linarith
  · simp only [add_zero]
    rw[walsh_odd_left]
    simp at h1
    ring_nf at h1
    exact h1.2
  · simp only [zero_add]
    rw[walsh_odd_right]
    simp at h3
    ring_nf at h3
    exact h3.1
  · simp only [add_zero]
    simp only [mem_Ico, not_and, not_lt] at h3
    simp only [mem_Ico, not_and, not_lt] at h1
    rw[walsh_zero_outside_domain  ]
    by_contra h
    push_neg at h
    obtain ⟨hx₀, hx₁⟩ := h
    have h0_5 : 0.5 ≤ x := h1 hx₀
    have h1' : 1 ≤ x := h3 h0_5
    linarith

theorem measurability_of_walsh {n : ℕ} : Measurable (walsh n):= by
  induction' n using Nat.evenOddRec with n ih n ih
  · rw[walsh0asfun]
    refine (measurable_indicator_const_iff 1).mpr ?_
    simp
  · rw[walshevenasfun]
    refine (Measurable.add_iff_right ?_).mpr ?_
    · apply Measurable.indicator
      · fun_prop
      · simp
    · apply Measurable.indicator
      · fun_prop
      · simp
  · rw[walshoddasfun]
    refine (Measurable.add_iff_right ?_).mpr ?_
    · apply Measurable.indicator
      · fun_prop
      · simp
    · apply Measurable.indicator
      · fun_prop
      · simp







theorem intergability {n : ℕ} :MeasureTheory.IntegrableOn (walsh n) univ MeasureTheory.volume := by
  induction' n using Nat.evenOddRec with n ih n ih
  · rw[walsh0asfun, MeasureTheory.integrableOn_univ, MeasureTheory.integrable_indicator_iff]
    · simp
    · simp
  · rw[walshevenasfun, MeasureTheory.integrableOn_univ]
    apply MeasureTheory.Integrable.add
    · rw[ MeasureTheory.Integrable.eq_1 ]
      constructor
      · apply Measurable.aestronglyMeasurable
        refine Measurable.indicator ?_ ?_
        · apply Measurable.comp (measurability_of_walsh) (measurable_const_mul 2)
        · simp
      · apply MeasureTheory.HasFiniteIntegral.mono' (g:= (Ico 0 0.5).indicator 1)
        · simp_rw[MeasureTheory.HasFiniteIntegral,enorm_indicator_eq_indicator_enorm]
          simp
        · apply Filter.Eventually.of_forall
          simp only [Real.norm_eq_abs]
          intro x
          simp only [indicator, mem_Ico, Pi.one_apply]
          split_ifs with h
          · apply walsh_leq_one (n := n) (x := (2*x))
          · simp
    · rw[ MeasureTheory.Integrable.eq_1 ]
      constructor
      · apply Measurable.aestronglyMeasurable
        refine Measurable.indicator ?_ ?_
        · apply Measurable.comp (measurability_of_walsh)
          refine Measurable.add_const ?_ (-1)
          exact measurable_const_mul 2
        · simp
      · apply MeasureTheory.HasFiniteIntegral.mono' (g:= (Ico 0.5 1).indicator 1)
        · simp_rw[MeasureTheory.HasFiniteIntegral,enorm_indicator_eq_indicator_enorm]
          simp
        · apply Filter.Eventually.of_forall
          simp only [Real.norm_eq_abs]
          intro x
          simp only [indicator, mem_Ico, Pi.one_apply]
          split_ifs with h
          · apply walsh_leq_one (n := n) (x := (2*x- 1))
          · simp
  · rw[walshoddasfun, MeasureTheory.integrableOn_univ]
    apply MeasureTheory.Integrable.add
    · rw[ MeasureTheory.Integrable.eq_1 ]
      constructor
      · apply Measurable.aestronglyMeasurable
        refine Measurable.indicator ?_ ?_
        · apply Measurable.comp (measurability_of_walsh) (measurable_const_mul 2)
        · simp
      · apply MeasureTheory.HasFiniteIntegral.mono' (g:= (Ico 0 0.5).indicator 1)
        · simp_rw[MeasureTheory.HasFiniteIntegral,enorm_indicator_eq_indicator_enorm]
          simp
        · apply Filter.Eventually.of_forall
          simp only [Real.norm_eq_abs]
          intro x
          simp only [indicator, mem_Ico, Pi.one_apply]
          split_ifs with h
          · apply walsh_leq_one (n := n) (x := (2*x))
          · simp
    · rw[ MeasureTheory.Integrable.eq_1 ]
      constructor
      · apply Measurable.aestronglyMeasurable
        refine Measurable.indicator ?_ ?_
        · simp only [measurable_neg_iff]
          apply Measurable.comp (measurability_of_walsh)
          refine Measurable.add_const ?_ (-1)
          exact measurable_const_mul 2
        · simp
      · apply MeasureTheory.HasFiniteIntegral.mono' (g:= (Ico 0.5 1).indicator 1)
        · simp_rw[MeasureTheory.HasFiniteIntegral,enorm_indicator_eq_indicator_enorm]
          simp
        · apply Filter.Eventually.of_forall
          simp only [Real.norm_eq_abs]
          intro x
          simp only [indicator, mem_Ico, Pi.one_apply]
          split_ifs with h
          · simp only [abs_neg]
            apply walsh_leq_one (n := n) (x := (2*x- 1))
          · simp







theorem changeofint {n : ℕ} : ∫ x in Set.Ico 0 1, walsh n x = ∫ x, walsh n x := by
  rw[← MeasureTheory.integral_indicator ]
  · apply MeasureTheory.integral_congr_ae
    rw[Filter.EventuallyEq ]
    apply Filter.Eventually.of_forall
    simp only [indicator_apply_eq_self]
    intro x hx
    simp_rw[Ico] at hx
    simp only [mem_setOf_eq] at hx
    apply walsh_zero_outside_domain
    simp only [ge_iff_le]
    rw[Decidable.not_and_iff_or_not] at hx
    push_neg at hx
    exact hx
  · exact measurableSet_Ico






theorem changeofint_firsthalf {n : ℕ} : ∫ x in Set.Ico 0 0.5,  walsh n (2*x) = (1/2) *  ∫ x in Set.Ico 0 1, walsh n x := by
  simp_rw [@MeasureTheory.restrict_Ico_eq_restrict_Ioc]
  rw[← intervalIntegral.integral_of_le, ← intervalIntegral.integral_of_le]
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    intervalIntegral.integral_comp_mul_left, mul_zero, smul_eq_mul, one_div, mul_eq_mul_left_iff,
    inv_eq_zero, or_false]
    ring_nf
  · linarith
  · linarith


theorem changeofint_secondhalf {n : ℕ} : ∫ x in Set.Ico 0.5 1,  walsh n (2*x-1) = (1/2) * ∫ x in Set.Ico 0 1, walsh n x := by
  simp_rw [@MeasureTheory.restrict_Ico_eq_restrict_Ioc]
  rw[← intervalIntegral.integral_of_le, ← intervalIntegral.integral_of_le]
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    intervalIntegral.integral_comp_mul_sub, mul_one, smul_eq_mul, one_div, mul_eq_mul_left_iff,
    inv_eq_zero, or_false]
    ring_nf
  · linarith
  · linarith

theorem intsum {n : ℕ} : (∫ x in Set.Ico  0 0.5,  walsh n x) + ∫ x in Set.Ico 0.5 1,  walsh n x = ∫ x in Set.Ico 0 1, walsh n x := by
  have : (Set.Ico 0 (1 :ℝ )) = (Set.Ico 0 0.5) ∪ (Set.Ico 0.5 1) := by
    refine Eq.symm (Ico_union_Ico_eq_Ico ?_ ?_)
    · linarith
    · linarith
  simp_rw[this]
  rw[MeasureTheory.integral_union_ae]
  · refine Disjoint.aedisjoint ?_
    simp
  · simp
  · apply MeasureTheory.IntegrableOn.mono_set (intergability)
    simp
  · apply MeasureTheory.IntegrableOn.mono_set (intergability)
    simp


theorem intofodd {n : ℕ} (h : Odd n) : ∫ x in Set.Ico 0 1,  walsh n x = 0 := by
  rw[← intsum]
  set l :=n/2 with hl
  have hl' : 2*l + 1 = n := by
    exact Nat.two_mul_div_two_add_one_of_odd h
  simp_rw[← hl']
  rw[← relbetweenintodd1, ← sub_neg_eq_add, ← relbetweenintodd2, changeofint_firsthalf, changeofint_secondhalf, sub_self]



theorem intofeven {n k : ℕ} (hk : 2 * k = n): ∫ x in Set.Ico 0 1,  walsh n x =  ∫ x in Set.Ico 0 1,  walsh k x  := by
  rw[← intsum, ← hk]
  rw[← relbetweeninteven1, ← relbetweeninteven2, changeofint_firsthalf, changeofint_secondhalf, ← mul_add]
  rw[Eq.symm (two_mul (∫ (x : ℝ) in Ico 0 1, walsh k x))]
  simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.inv_mul_cancel_left]



theorem bcs_walsh {n : ℕ}: BoundedCompactSupport (walsh n) MeasureTheory.volume := by
  refine { memLp_top := ?_, hasCompactSupport := ?_ }
  · apply MeasureTheory.memLp_top_of_bound (C := 1)
    · apply Measurable.aestronglyMeasurable (measurability_of_walsh)
    · apply Filter.Eventually.of_forall
      simp only [Real.norm_eq_abs]
      apply walsh_leq_one
  · refine exists_compact_iff_hasCompactSupport.mp ?_
    use Icc 0 1
    constructor
    · exact isCompact_Icc
    · intro x hx
      apply walsh_zero_outside_domain
      simp only [mem_Icc, Decidable.not_and_iff_or_not, not_le] at hx
      simp only [ge_iff_le]
      rcases hx with hx | hx
      · left
        exact hx
      · right
        exact hx.le




theorem walshsizing_firsthalf {n : ℕ} {x : ℝ}: 2* walsh n (2* x) = walsh (2*n) x + walsh (2* n + 1) x := by
  by_cases h : x < 1/2
  · rw[walsh_even_odd_left h, walsh_odd_left h, two_mul]
  · push_neg at h
    rw[walsh_even_odd_right h]
    simp only [neg_add_cancel, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    rw[walsh_zero_outside_domain]
    right
    linarith


theorem walshsizing_firsthalf' {n : ℕ} {x : ℝ}: walsh n (2* x) = 1/2 *  (walsh (2*n) x + walsh (2* n + 1) x ):= by
  rw [← @walshsizing_firsthalf]
  simp

theorem walshsizing_secondhalf {n : ℕ} {x : ℝ}: 2* walsh n (2*x -1) = walsh (2*n) x - walsh (2* n + 1) x := by
  by_cases h : 1/2 ≤ x
  · rw[walsh_even_odd_right h, walsh_odd_right h]
    simp only [neg_neg, sub_neg_eq_add]
    linarith
  · push_neg at h
    rw[walsh_even_odd_left h]
    simp only [sub_self, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    rw[walsh_zero_outside_domain]
    left
    linarith

theorem walshsizing_secondhalf' {n : ℕ} {x : ℝ}: walsh n (2*x -1) = 1/2 *(walsh (2*n) x - walsh (2* n + 1) x ):= by
  rw [← @walshsizing_secondhalf]
  simp

theorem walshsizing_zero {M k : ℕ} {x : ℝ} : walsh 0 (2^M* x - k) = (Ico (k * 2 ^ (-M :ℤ )  : ℝ ) ((k+1)* 2 ^ (-M : ℤ )  : ℝ ) ).indicator 1 x := by
  simp only [indicator, zpow_neg, zpow_natCast, mem_Ico, Pi.one_apply]
  split_ifs with h
  · rw[walsh_zero]
    · obtain ⟨ h1, h2⟩ := h
      rw [@sub_nonneg]
      rw[mul_inv_le_iff₀ (pow_pos (zero_lt_two) M)] at h1
      rw[mul_comm]
      exact h1
    · rw [@sub_lt_iff_lt_add']
      obtain ⟨ h1, h2⟩ := h
      rw[mul_comm, lt_inv_mul_iff₀ (pow_pos (zero_lt_two) M)] at h2
      exact h2
  · rw[walsh_zero_outside_domain]
    simp only [Decidable.not_and_iff_or_not, not_le, not_lt ] at h
    rcases h with h | h
    · left
      simp only [sub_neg]
      rw[mul_comm, lt_inv_mul_iff₀ (pow_pos (zero_lt_two) M)] at h
      exact h
    · right
      simp only [ge_iff_le]
      rw [@le_sub_iff_add_le']
      rw[mul_inv_le_iff₀ (pow_pos (zero_lt_two) M)] at h
      linarith


/-theorem walshindicatorhelp {M : ℕ} {x : ℝ} : ∑ k ∈ Finset.range (2 ^ M)\Finset.range (2 ^ (M-1)), walsh k x   = ∑ k ∈ Finset.range (2 ^ (M-1))\Finset.range (2 ^ M), walsh k x   := by

  sorry -/




theorem walshindicator {M k : ℕ} {x : ℝ} (hk : k < 2 ^ M): ∃ (f:ℕ  → ℝ), ∑ j ∈ Finset.range (2^M), (walsh j x  * f j )= (Ico (k * 2 ^ (-M :ℤ )  : ℝ ) ((k+1)* 2 ^ (-M : ℤ )  : ℝ ) ).indicator 1 x := by
  rw[← walshsizing_zero]
  induction' M with M ih generalizing k x
  · simp only [ pow_zero, Nat.lt_one_iff] at hk
    rw[ hk]
    simp only [pow_zero, Finset.range_one, Finset.sum_singleton, one_mul, CharP.cast_eq_zero,
      sub_zero]
    use 1
    simp
  · set s:= {l ∈ Finset.range (2^(M+1)) | Odd l} with hs
    set t := { l ∈ Finset.range (2^(M+1)) |  Even l}  with ht
    have hp : Finset.range (2^(M+1)) = s ∪ t := by
      rw[hs, ht]
      ext k
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_filter]
      rw[← and_or_left]
      simp only [iff_self_and]
      exact fun a ↦ Or.symm (Nat.even_or_odd k)

    have hw (f:ℕ  → ℝ) : ∑ x_1 ∈ Finset.range (2 ^ (M + 1)), f x_1 * walsh x_1 x = ∑ x_1 ∈ s, f x_1 * walsh x_1 x + ∑ x_1 ∈ t, f x_1 * walsh x_1 x := by
      rw[← Finset.sum_union]
      · congr
      · rw[hs, ht]
        refine Finset.disjoint_filter.mpr ?_
        intro k hk
        intro h1
        simp only [Nat.not_even_iff_odd]
        exact h1
    by_cases h : k < 2^M
    · specialize ih (k:=k) (x:=2*x) h
      simp_rw[← mul_assoc, ← pow_succ] at ih
      simp_rw[walshsizing_firsthalf'] at ih
      obtain ⟨g, hg⟩ := ih
      rw[← hg]
      simp_rw[mul_comm, ← mul_assoc, mul_add, Finset.sum_add_distrib]
      simp_rw[hw]
      set f: ℕ → ℝ := (fun x ↦ g (x/2)*(1 / 2)) with hf
      use f
      rw[add_comm]
      refine Eq.symm (Mathlib.Tactic.LinearCombination.add_eq_eq ?_ ?_)
      · rw[ht, eq_comm ]
        let i : ℕ → ℕ  := fun i ↦ i/2
        apply Finset.sum_of_injOn i
        · unfold InjOn
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, and_imp]
          intro n hn hn2 m hm hm2 himp
          simp only [i] at himp
          set k:= n/2
          have hk' : 2*k = n := by
            exact Nat.two_mul_div_two_of_even hn2
          rw[himp] at hk'
          rw[← hk']
          exact Nat.two_mul_div_two_of_even hm2
        · unfold MapsTo
          intro k hk
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, i] at hk
          simp only [Finset.coe_range, mem_Iio, i]
          refine Nat.div_lt_of_lt_mul ?_
          rw [← @Nat.pow_add_one']
          exact hk.1
        · simp only [Finset.mem_range]
          intro l hl
          have : ¬ (l ∉ i '' ↑({l ∈ Finset.range (2 ^ (M + 1)) | Even l})) := by
            simp only [Finset.coe_filter, Finset.mem_range, mem_image, mem_setOf_eq, not_exists,
              not_and, and_imp, not_forall, Classical.not_imp, Decidable.not_not, i]
            simp only [exists_prop, exists_and_left, i]
            use 2*l
            simp only [even_two, Even.mul_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              mul_div_cancel_left₀, and_self, and_true, i]
            rw[pow_add]
            simp only [pow_one, i]
            rw[mul_comm]
            simp only [Nat.ofNat_pos, mul_lt_mul_right, i]
            exact hl
          intro hl1
          exfalso
          exact this hl1
        · simp only [Finset.mem_filter, Finset.mem_range, one_div, and_imp, i]
          rw[hf]
          intro i hi hii
          simp only [one_div, mul_eq_mul_left_iff, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
            or_false, *]
          left
          congr
          exact Eq.symm (Nat.div_two_mul_two_of_even hii)
      · rw[hs, eq_comm ]
        let i : ℕ → ℕ  := fun i ↦ i/2
        apply Finset.sum_of_injOn i
        · unfold InjOn
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, and_imp]
          intro n hn hn2 m hm hm2 himp
          simp only [i] at himp
          set k:= n/2
          have hk' : 2*k +1 = n := by
            exact Nat.two_mul_div_two_add_one_of_odd hn2
          rw[himp] at hk'
          rw[← hk']
          exact Nat.two_mul_div_two_add_one_of_odd hm2
        · unfold MapsTo
          intro k hk
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, i] at hk
          simp only [Finset.coe_range, mem_Iio, i]
          refine Nat.div_lt_of_lt_mul ?_
          rw [← @Nat.pow_add_one']
          exact hk.1
        · simp only [Finset.mem_range]
          intro l hl
          have : ¬ (l ∉ i '' ↑({l ∈ Finset.range (2 ^ (M + 1)) | Odd l})) := by
            simp only [Finset.coe_filter, Finset.mem_range, mem_image, mem_setOf_eq, not_exists,
              not_and, and_imp, not_forall, Classical.not_imp, Decidable.not_not, i]
            use 2 * l + 1
            simp only [even_two, Even.mul_right, Even.add_one, exists_const, exists_prop, i]
            constructor
            · apply Nat.add_one_le_of_lt at hl
              rw[← Nat.mul_le_mul_left_iff (Nat.zero_lt_two)] at hl
              rw[pow_add]
              simp only [pow_one, i]
              rw[mul_comm, add_mul, add_comm, Nat.mul_two (n := 1), add_comm, ← add_assoc ] at hl
              apply Nat.lt_of_add_one_le
              rw[mul_comm, mul_comm (a:= 2^M)]
              exact hl
            · rw [Nat.add_div_of_dvd_right (Exists.intro l rfl)]
              simp
          intro hl1
          exfalso
          exact this hl1
        · simp only [Finset.mem_filter, Finset.mem_range, one_div, and_imp, i]
          rw[hf]
          intro i hi hii
          simp only [one_div, mul_eq_mul_left_iff, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
            or_false, *]
          left
          congr
          exact Eq.symm (Nat.div_two_mul_two_add_one_of_odd hii)
    · push_neg at h
      rw[pow_succ,mul_two] at hk
      apply Nat.sub_lt_left_of_lt_add h  at hk
      specialize ih (k:=k-2^M) (x:=2*x-1) hk
      rw[mul_sub, ← mul_assoc, ← pow_succ   ] at ih
      simp only [mul_one] at ih
      rw[Nat.cast_sub h, sub_sub_eq_add_sub] at ih
      simp_rw[walshsizing_secondhalf'] at ih
      simp only [Nat.cast_pow, Nat.cast_ofNat, sub_add_cancel] at ih
      obtain ⟨g, hg⟩ := ih
      rw[← hg]
      simp_rw[mul_comm, ← mul_assoc, mul_sub, Finset.sum_sub_distrib]
      simp_rw[hw]
      set f: ℕ → ℝ := (fun x ↦ g (x/2)*(1 / 2)*((-1)^x)) with hf
      use f
      conv_rhs => rw[sub_eq_add_neg,← mul_neg_one, Finset.sum_mul]
      rw[← mul_neg_one,add_comm]
      refine Eq.symm (Mathlib.Tactic.LinearCombination.add_eq_eq ?_ ?_)
      · rw[ht, eq_comm ]
        let i : ℕ → ℕ  := fun i ↦ i/2
        apply Finset.sum_of_injOn i
        · unfold InjOn
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, and_imp]
          intro n hn hn2 m hm hm2 himp
          simp only [i] at himp
          set k:= n/2
          have hk' : 2*k = n := by
            exact Nat.two_mul_div_two_of_even hn2
          rw[himp] at hk'
          rw[← hk']
          exact Nat.two_mul_div_two_of_even hm2
        · unfold MapsTo
          intro k hk
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, i] at hk
          simp only [Finset.coe_range, mem_Iio, i]
          refine Nat.div_lt_of_lt_mul ?_
          rw [← @Nat.pow_add_one']
          exact hk.1
        · simp only [Finset.mem_range]
          intro l hl
          have : ¬ (l ∉ i '' ↑({l ∈ Finset.range (2 ^ (M + 1)) | Even l})) := by
            simp only [Finset.coe_filter, Finset.mem_range, mem_image, mem_setOf_eq, not_exists,
              not_and, and_imp, not_forall, Classical.not_imp, Decidable.not_not, i]
            simp only [exists_prop, exists_and_left, i]
            use 2*l
            simp only [even_two, Even.mul_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              mul_div_cancel_left₀, and_self, and_true, i]
            rw[pow_add]
            simp only [pow_one, i]
            rw[mul_comm]
            simp only [Nat.ofNat_pos, mul_lt_mul_right, i]
            exact hl
          intro hl1
          exfalso
          exact this hl1
        · simp only [Finset.mem_filter, Finset.mem_range, one_div, and_imp, i]
          rw[hf]
          intro i hi hii
          simp only [one_div, *, Even.neg_one_pow ,mul_one, mul_eq_mul_left_iff, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
            or_false, *]
          left
          congr
          exact Eq.symm (Nat.div_two_mul_two_of_even hii)
      · rw[hs, eq_comm ]
        let i : ℕ → ℕ  := fun i ↦ i/2
        apply Finset.sum_of_injOn i
        · unfold InjOn
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, and_imp]
          intro n hn hn2 m hm hm2 himp
          simp only [i] at himp
          set k:= n/2
          have hk' : 2*k +1 = n := by
            exact Nat.two_mul_div_two_add_one_of_odd hn2
          rw[himp] at hk'
          rw[← hk']
          exact Nat.two_mul_div_two_add_one_of_odd hm2
        · unfold MapsTo
          intro k hk
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, i] at hk
          simp only [Finset.coe_range, mem_Iio, i]
          refine Nat.div_lt_of_lt_mul ?_
          rw [← @Nat.pow_add_one']
          exact hk.1
        · simp only [Finset.mem_range]
          intro l hl
          have : ¬ (l ∉ i '' ↑({l ∈ Finset.range (2 ^ (M + 1)) | Odd l})) := by
            simp only [Finset.coe_filter, Finset.mem_range, mem_image, mem_setOf_eq, not_exists,
              not_and, and_imp, not_forall, Classical.not_imp, Decidable.not_not, i]
            use 2 * l + 1
            simp only [even_two, Even.mul_right, Even.add_one, exists_const, exists_prop, i]
            constructor
            · apply Nat.add_one_le_of_lt at hl
              rw[← Nat.mul_le_mul_left_iff (Nat.zero_lt_two)] at hl
              rw[pow_add]
              simp only [pow_one, i]
              rw[mul_comm, add_mul, add_comm, Nat.mul_two (n := 1), add_comm, ← add_assoc ] at hl
              apply Nat.lt_of_add_one_le
              rw[mul_comm, mul_comm (a:= 2^M)]
              exact hl
            · rw [Nat.add_div_of_dvd_right (Exists.intro l rfl)]
              simp
          intro hl1
          exfalso
          exact this hl1
        · simp only [Finset.mem_filter, Finset.mem_range, one_div, and_imp, i]
          rw[hf]
          intro i hi hii
          simp_rw[Odd.neg_one_pow hii]
          simp only [one_div, mul_neg, mul_one, neg_mul, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
            inv_eq_zero, OfNat.ofNat_ne_zero, or_false, *]
          left
          congr
          exact Eq.symm (Nat.div_two_mul_two_add_one_of_odd hii)




theorem walshindicator' {M k : ℕ} (hk : k < 2 ^ M): ∃ (f:ℕ  → ℝ), (fun x ↦ ∑ j ∈ Finset.range (2^M), (walsh j x  * f j )) = (fun x ↦ (Ico (k * 2 ^ (-M :ℤ )  : ℝ ) ((k+1)* 2 ^ (-M : ℤ )  : ℝ ) ).indicator 1 x ):= by
  simp_rw[← walshsizing_zero]
  induction' M with M ih generalizing k
  · simp only [ pow_zero, Nat.lt_one_iff] at hk
    rw[ hk]
    simp only [pow_zero, Finset.range_one, Finset.sum_singleton, one_mul, CharP.cast_eq_zero,
      sub_zero]
    use 1
    simp
  · set s:= {l ∈ Finset.range (2^(M+1)) | Odd l} with hs
    set t := { l ∈ Finset.range (2^(M+1)) |  Even l}  with ht
    have hp : Finset.range (2^(M+1)) = s ∪ t := by
      rw[hs, ht]
      ext k
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_filter, ← and_or_left, iff_self_and]
      exact fun a ↦ Or.symm (Nat.even_or_odd k)
    have hw (f:ℕ  → ℝ) (x :ℝ) : ∑ x_1 ∈ Finset.range (2 ^ (M + 1)), f x_1 * walsh x_1 x = ∑ x_1 ∈ s, f x_1 * walsh x_1 x + ∑ x_1 ∈ t, f x_1 * walsh x_1 x := by
      rw[← Finset.sum_union ]
      · congr
      · rw[hs, ht]
        refine Finset.disjoint_filter.mpr ?_
        intro k hk h1
        simp only [Nat.not_even_iff_odd]
        exact h1
    by_cases h : k < 2^M
    · specialize ih (k:=k) h
      obtain ⟨g, hg⟩ := ih
      set f: ℕ → ℝ := (fun x ↦ g (x/2)*(1 / 2)) with hf
      use f
      ext x
      have h_p := congrFun hg (2*x)
      simp_rw[← mul_assoc, ← pow_succ, walshsizing_firsthalf'] at h_p
      rw[← h_p]
      simp_rw[mul_comm, ← mul_assoc, mul_add, Finset.sum_add_distrib]
      simp_rw[hw, hf]
      rw[add_comm]
      refine Eq.symm (Mathlib.Tactic.LinearCombination.add_eq_eq ?_ ?_)
      · rw[ht, eq_comm ]
        let i : ℕ → ℕ  := fun i ↦ i/2
        apply Finset.sum_of_injOn i
        · unfold InjOn
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, and_imp]
          intro n hn hn2 m hm hm2 himp
          simp only [i] at himp
          set k:= n/2
          have hk' : 2*k = n := by
            exact Nat.two_mul_div_two_of_even hn2
          rw[himp] at hk'
          rw[← hk']
          exact Nat.two_mul_div_two_of_even hm2
        · unfold MapsTo
          intro k hk
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, i] at hk
          simp only [Finset.coe_range, mem_Iio, i]
          refine Nat.div_lt_of_lt_mul ?_
          rw [← @Nat.pow_add_one']
          exact hk.1
        · simp only [Finset.mem_range]
          intro l hl
          have : ¬ (l ∉ i '' ↑({l ∈ Finset.range (2 ^ (M + 1)) | Even l})) := by
            simp only [Finset.coe_filter, Finset.mem_range, mem_image, mem_setOf_eq, not_exists,
              not_and, and_imp, not_forall, Classical.not_imp, Decidable.not_not, i]
            simp only [exists_prop, exists_and_left, i]
            use 2*l
            simp only [even_two, Even.mul_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              mul_div_cancel_left₀, and_self, and_true, i]
            rw[pow_add]
            simp only [pow_one, i]
            rw[mul_comm]
            simp only [Nat.ofNat_pos, mul_lt_mul_right, i]
            exact hl
          intro hl1
          exfalso
          exact this hl1
        · simp only [Finset.mem_filter, Finset.mem_range, one_div, and_imp, i]
          intro i hi hii
          simp only [one_div, mul_eq_mul_left_iff, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
            or_false, *]
          left
          congr
          exact Eq.symm (Nat.div_two_mul_two_of_even hii)
      · rw[hs, eq_comm ]
        let i : ℕ → ℕ  := fun i ↦ i/2
        apply Finset.sum_of_injOn i
        · unfold InjOn
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, and_imp]
          intro n hn hn2 m hm hm2 himp
          simp only [i] at himp
          set k:= n/2
          have hk' : 2*k +1 = n := by
            exact Nat.two_mul_div_two_add_one_of_odd hn2
          rw[himp] at hk'
          rw[← hk']
          exact Nat.two_mul_div_two_add_one_of_odd hm2
        · unfold MapsTo
          intro k hk
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, i] at hk
          simp only [Finset.coe_range, mem_Iio, i]
          refine Nat.div_lt_of_lt_mul ?_
          rw [← @Nat.pow_add_one']
          exact hk.1
        · simp only [Finset.mem_range]
          intro l hl
          have : ¬ (l ∉ i '' ↑({l ∈ Finset.range (2 ^ (M + 1)) | Odd l})) := by
            simp only [Finset.coe_filter, Finset.mem_range, mem_image, mem_setOf_eq, not_exists,
              not_and, and_imp, not_forall, Classical.not_imp, Decidable.not_not, i]
            use 2 * l + 1
            simp only [even_two, Even.mul_right, Even.add_one, exists_const, exists_prop, i]
            constructor
            · apply Nat.add_one_le_of_lt at hl
              rw[← Nat.mul_le_mul_left_iff (Nat.zero_lt_two)] at hl
              rw[pow_add]
              simp only [pow_one, i]
              rw[mul_comm, add_mul, add_comm, Nat.mul_two (n := 1), add_comm, ← add_assoc ] at hl
              apply Nat.lt_of_add_one_le
              rw[mul_comm, mul_comm (a:= 2^M)]
              exact hl
            · rw [Nat.add_div_of_dvd_right (Exists.intro l rfl)]
              simp
          intro hl1
          exfalso
          exact this hl1
        · simp only [Finset.mem_filter, Finset.mem_range, one_div, and_imp, i]
          intro i hi hii
          simp only [one_div, mul_eq_mul_left_iff, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
            or_false, *]
          left
          congr
          exact Eq.symm (Nat.div_two_mul_two_add_one_of_odd hii)
    · push_neg at h
      rw[pow_succ,mul_two] at hk
      apply Nat.sub_lt_left_of_lt_add h  at hk
      specialize ih (k:=k-2^M) hk
      obtain ⟨g, hg⟩ := ih
      set f: ℕ → ℝ := (fun x ↦ g (x/2)*(1 / 2)*((-1)^x)) with hf
      use f
      ext x
      have h_p := congrFun hg (2*x-1)
      rw[mul_sub, ← mul_assoc, ← pow_succ, mul_one, Nat.cast_sub h, sub_sub_eq_add_sub] at h_p
      simp_rw[walshsizing_secondhalf'] at h_p
      simp only [Nat.cast_pow, Nat.cast_ofNat, sub_add_cancel] at h_p
      rw[← h_p]
      simp_rw[mul_comm, ← mul_assoc, mul_sub, Finset.sum_sub_distrib]
      simp_rw[hw]
      conv_rhs => rw[sub_eq_add_neg,← mul_neg_one, Finset.sum_mul]
      rw[← mul_neg_one,add_comm]
      refine Eq.symm (Mathlib.Tactic.LinearCombination.add_eq_eq ?_ ?_)
      · rw[ht, eq_comm ]
        let i : ℕ → ℕ  := fun i ↦ i/2
        apply Finset.sum_of_injOn i
        · unfold InjOn
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, and_imp]
          intro n hn hn2 m hm hm2 himp
          simp only [i] at himp
          set k:= n/2
          have hk' : 2*k = n := by
            exact Nat.two_mul_div_two_of_even hn2
          rw[himp] at hk'
          rw[← hk']
          exact Nat.two_mul_div_two_of_even hm2
        · unfold MapsTo
          intro k hk
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, i] at hk
          simp only [Finset.coe_range, mem_Iio, i]
          refine Nat.div_lt_of_lt_mul ?_
          rw [← @Nat.pow_add_one']
          exact hk.1
        · simp only [Finset.mem_range]
          intro l hl
          have : ¬ (l ∉ i '' ↑({l ∈ Finset.range (2 ^ (M + 1)) | Even l})) := by
            simp only [Finset.coe_filter, Finset.mem_range, mem_image, mem_setOf_eq, not_exists,
              not_and, and_imp, not_forall, Classical.not_imp, Decidable.not_not, i]
            simp only [exists_prop, exists_and_left, i]
            use 2*l
            simp only [even_two, Even.mul_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              mul_div_cancel_left₀, and_self, and_true, i]
            rw[pow_add]
            simp only [pow_one, i]
            rw[mul_comm]
            simp only [Nat.ofNat_pos, mul_lt_mul_right, i]
            exact hl
          intro hl1
          exfalso
          exact this hl1
        · simp only [Finset.mem_filter, Finset.mem_range, one_div, and_imp, i]
          rw[hf]
          intro i hi hii
          simp only [one_div, *, Even.neg_one_pow ,mul_one, mul_eq_mul_left_iff, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
            or_false, *]
          left
          congr
          exact Eq.symm (Nat.div_two_mul_two_of_even hii)
      · rw[hs, eq_comm ]
        let i : ℕ → ℕ  := fun i ↦ i/2
        apply Finset.sum_of_injOn i
        · unfold InjOn
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, and_imp]
          intro n hn hn2 m hm hm2 himp
          simp only [i] at himp
          set k:= n/2
          have hk' : 2*k +1 = n := by
            exact Nat.two_mul_div_two_add_one_of_odd hn2
          rw[himp] at hk'
          rw[← hk']
          exact Nat.two_mul_div_two_add_one_of_odd hm2
        · unfold MapsTo
          intro k hk
          simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq, i] at hk
          simp only [Finset.coe_range, mem_Iio, i]
          refine Nat.div_lt_of_lt_mul ?_
          rw [← @Nat.pow_add_one']
          exact hk.1
        · simp only [Finset.mem_range]
          intro l hl
          have : ¬ (l ∉ i '' ↑({l ∈ Finset.range (2 ^ (M + 1)) | Odd l})) := by
            simp only [Finset.coe_filter, Finset.mem_range, mem_image, mem_setOf_eq, not_exists,
              not_and, and_imp, not_forall, Classical.not_imp, Decidable.not_not, i]
            use 2 * l + 1
            simp only [even_two, Even.mul_right, Even.add_one, exists_const, exists_prop, i]
            constructor
            · apply Nat.add_one_le_of_lt at hl
              rw[← Nat.mul_le_mul_left_iff (Nat.zero_lt_two)] at hl
              rw[pow_add]
              simp only [pow_one, i]
              rw[mul_comm, add_mul, add_comm, Nat.mul_two (n := 1), add_comm, ← add_assoc ] at hl
              apply Nat.lt_of_add_one_le
              rw[mul_comm, mul_comm (a:= 2^M)]
              exact hl
            · rw [Nat.add_div_of_dvd_right (Exists.intro l rfl)]
              simp
          intro hl1
          exfalso
          exact this hl1
        · simp only [Finset.mem_filter, Finset.mem_range, one_div, and_imp, i]
          rw[hf]
          intro i hi hii
          simp_rw[Odd.neg_one_pow hii]
          simp only [one_div, mul_neg, mul_one, neg_mul, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
            inv_eq_zero, OfNat.ofNat_ne_zero, or_false, *]
          left
          congr
          exact Eq.symm (Nat.div_two_mul_two_add_one_of_odd hii)






theorem domain {n : ℕ} {x : ℝ} (h : ¬walsh n x = 0) : 0≤ x ∧ x <1 := by
  by_contra hc
  simp only [Decidable.not_and_iff_or_not ] at hc
  simp only [not_le, not_lt] at hc
  have : walsh n x = 0 := by
    apply walsh_not_in x hc
  exact h this



theorem ago1 {M k : ℕ} {x : ℝ} (hx1 : 2 ^ (-M : ℤ) * k ≤ x) : 0 ≤ x := by
  apply le_trans ?_ hx1
  simp


theorem ago2 {M k : ℕ} {x : ℝ} (hk : k < 2 ^ M) (hx1 : x < 2 ^ (-M : ℤ) * (k + 1)) : x<1 := by
  apply lt_of_lt_of_le hx1
  rw[Nat.lt_iff_add_one_le] at hk
  simp only [zpow_neg, zpow_natCast]
  rw[inv_mul_le_one₀]
  · norm_cast
  · simp

theorem ago {M k : ℕ} {x : ℝ} (hk : k < 2 ^ M) (hx : x ∈ dyadicInterval (-M : ℤ) k) : 0 ≤ x ∧ x<1 := by
  simp only [dyadicInterval, zpow_neg, zpow_natCast, Int.cast_natCast, mem_setOf_eq] at hx
  obtain ⟨ hx1 , hx2 ⟩ := hx
  constructor
  · apply ago1 (M := M) (k := k)
    simp only [zpow_neg, zpow_natCast]
    exact hx1
  · apply ago2 (M := M) (k := k) hk
    simp only [zpow_neg, zpow_natCast]
    exact hx2






theorem walshonint {M n k : ℕ} (hn : n < 2 ^ M) (hk : k < 2 ^ M) : ∃ c :ℝ , ∀ x ∈  dyadicInterval (-M : ℤ) k, walsh n x = c := by
  induction' M with M ih generalizing k n
  · simp only [pow_zero, Nat.lt_one_iff] at hn
    simp only [pow_zero, Nat.lt_one_iff] at hk
    simp only [CharP.cast_eq_zero, neg_zero, hk, dyadicInterval_of_n_zero, zpow_zero, mem_Ico, hn]
    use 1
    intro x hx
    rw[walsh_zero hx.1 hx.2]
  · have hM : dyadicInterval (-(M + 1)) (k :ℤ)  ⊆ dyadicInterval (-(↑M + 1) + 1)  (k/2) := by
      apply dyadicin (k := -(M + 1)) (n := k)
    simp only [neg_add_rev, Int.reduceNeg, neg_add_cancel_comm] at hM
    have hk' : k/2 < 2 ^ M := Nat.nat_repr_len_aux k 2 M (two_pos) hk
    set l := n/2 with hl
    by_cases hn' : Odd n
    · have hl' : n = 2*l + 1 := Eq.symm (Nat.two_mul_div_two_add_one_of_odd hn')
      rw[hl', @walshoddasfun]
      simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg, Pi.add_apply]
      have hl0 : l < 2^M := by
        rw[hl', pow_add] at hn
        simp at hn
        linarith
      by_cases hk' :  k < 2^ M
      · obtain ⟨ p, hp⟩ := ih hl0 hk'
        use p
        intro x hx
        have h0 : x ∈ Ico 0 0.5 := by
          set N := M + 1 with hN
          have hN' : N - 1 = M := rfl
          rw[← hN'] at hk'
          rw[← infirsthalf (Ne.symm (Nat.zero_ne_add_one M))] at hk'
          simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg] at hk'
          exact hk' hx
        have h01 : x ∉ Ico 0.5 1 := by
          simp only [mem_Ico] at h0
          refine notMem_Ico_of_lt h0.2
        simp only [h0, indicator_of_mem, h01, not_false_eq_true, indicator_of_notMem, add_zero]
        simp_rw[← neg_add] at hx
        norm_cast at hx
        apply xinfirsthalf' at hx
        simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg,
          neg_add_cancel_right] at hx
        exact hp (2 * x) hx
      · have hk1 : (k - 2^M) < 2^M := by
          apply Nat.sub_lt_left_of_lt_add
          · simp only [not_lt] at hk'
            exact hk'
          · rw [← Nat.two_pow_succ]
            exact hk
        obtain ⟨ p, hp⟩ := ih hl0 hk1
        use -p
        intro x hx
        have h01 : x ∈ Ico 0.5 1 := by
          set N := M + 1 with hN
          have hN' : N - 1 = M := rfl
          rw[← hN'] at hk'
          simp only [not_lt] at hk'
          rw[← insecondhalf hk (Ne.symm (Nat.zero_ne_add_one M)) ] at hk'
          simp only [hN, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg] at hk'
          exact hk' hx
        have h0 : x ∉ Ico 0 0.5 := by
          simp only [mem_Ico] at h01
          refine notMem_Ico_of_ge h01.1
        simp only [h0, not_false_eq_true, indicator_of_notMem, h01, indicator_of_mem, zero_add, neg_inj]
        simp_rw[← neg_add] at hx
        norm_cast at hx
        have : 1 + M ≠ 0 := Ne.symm (NeZero.ne' (1 + M))
        apply xinsecondhalf' at hx
        simp only [ne_eq, Nat.add_eq_zero, one_ne_zero, false_and, not_false_eq_true, Nat.cast_add,
          Nat.cast_one, neg_add_rev, Int.reduceNeg, neg_add_cancel_right, add_tsub_cancel_left,
          forall_const] at hx
        rw[hp (2 * x - 1) ]
        have : dyadicInterval (-↑M) ↑(k - 2 ^ M) = dyadicInterval (-↑M) (↑k - 2 ^ M) := by
          sorry
        rw[this]
        exact hx
    · simp only [Nat.not_odd_iff_even] at hn'
      have hl' : n = 2*l  := Eq.symm (Nat.two_mul_div_two_of_even hn')
      rw[hl', @walshevenasfun]
      have hl0 : l < 2^M := by
        rw[hl', pow_add, mul_comm, pow_one, mul_lt_mul_iff_of_pos_right (two_pos)] at hn
        exact hn
      by_cases hk' :  k < 2^ M
      · obtain ⟨ p, hp⟩ := ih hl0 hk'
        use p
        intro x hx
        have h0 : x ∈ Ico 0 0.5 := by
          set N := M + 1 with hN
          have hN' : N - 1 = M := rfl
          rw[← hN'] at hk'
          rw[← infirsthalf (Ne.symm (Nat.zero_ne_add_one M))] at hk'
          simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg] at hk'
          simp only [hN, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg] at hx
          exact hk' hx
        have h01 : x ∉ Ico 0.5 1 := by
          simp only [mem_Ico] at h0
          refine notMem_Ico_of_lt h0.2
        simp only [Pi.add_apply, h0, indicator_of_mem, h01, not_false_eq_true, indicator_of_notMem,
          add_zero]
        apply xinfirsthalf' at hx
        simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg,
          neg_add_cancel_comm] at hx
        exact hp (2 * x) hx
      · have hk1 : (k - 2^M) < 2^M := by
          apply Nat.sub_lt_left_of_lt_add
          · simp only [not_lt] at hk'
            exact hk'
          · rw [← Nat.two_pow_succ]
            exact hk
        obtain ⟨ p, hp⟩ := ih hl0 hk1
        use p
        intro x hx
        have h01 : x ∈ Ico 0.5 1 := by
          set N := M + 1 with hN
          have hN' : N - 1 = M := rfl
          rw[← hN'] at hk'
          simp only [not_lt] at hk'
          rw[← insecondhalf hk (Ne.symm (Nat.zero_ne_add_one M)) ] at hk'
          simp only [hN, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg] at hk'
          simp only [hN, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg] at hx
          exact hk' hx
        have h0 : x ∉ Ico 0 0.5 := by
          simp only [mem_Ico] at h01
          refine notMem_Ico_of_ge h01.1
        simp only [Pi.add_apply, h0, not_false_eq_true, indicator_of_notMem, h01, indicator_of_mem,
          zero_add]
        have : 1 + M ≠ 0 := Ne.symm (NeZero.ne' (1 + M))
        apply xinsecondhalf' at hx
        simp only [ne_eq, Nat.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, Nat.cast_add,
          Nat.cast_one, neg_add_rev, Int.reduceNeg, neg_add_cancel_comm, add_tsub_cancel_right,
          forall_const] at hx
        rw[hp (2 * x - 1) ]
        have : dyadicInterval (-↑M) ↑(k - 2 ^ M) = dyadicInterval (-↑M) (↑k - 2 ^ M) := by sorry
        rw[this]
        exact hx


theorem walshonintnext {M n k : ℕ} (hn : n < 2 ^ M) (hk : k < 2 ^ M) : ∀ x ∈  dyadicInterval (-M : ℤ) k, ∀ y ∈  dyadicInterval (-M : ℤ) k , walsh n x = walsh n y := by
  intro x hx y hy
  obtain ⟨c, hc⟩ := walshonint hn hk
  apply hc at hy
  apply hc at hx
  rw[hx, hy]

theorem walshonintval {M n k : ℕ} {x : ℝ} (hn : n < 2 ^ M) (hk : k < 2 ^ M): (dyadicInterval (-M : ℤ) k).indicator (1) = (dyadicInterval (-M : ℤ) k).indicator (walsh n)  ∨ (dyadicInterval (-M : ℤ) k).indicator (- 1 ) = (dyadicInterval (-M : ℤ) k).indicator (walsh n) := by


  sorry


def val (M n k : ℕ) (hn : n < 2 ^ M) (hk : k < 2 ^ M): ℝ  :=
  (walshonint (M := M) (n := n ) (k := k) hn hk ).choose



end Walsh

/-
theorem valexplicit (M n k : ℕ) (hn : n < 2 ^ M) (hk : k < 2 ^ M): val M n k hn hk = 1 ∨ val M n k hn hk = -1 := by
  obtain hp  := (walshonint (M := M) (n := n ) (k := k) hn hk ).choose_spec


  sorry  --/


---measurability
--#min_imports
