import Mathlib
open Function Set Classical
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
    #check walsh.induct

/--
Walsh function is 0 outisde`[0,1)`.
-/
@[simp]
theorem walsh_not_in {n : ℕ} (x : ℝ) (h : x < 0 ∨  1 ≤ x ) : walsh n x = 0 := by
  unfold walsh
  split_ifs with h1 h2
  · exact if_pos h
  · simp only [h, ↓reduceIte]
  simp only [h, ↓reduceIte]

/--
Walsh function for `n=0` is 1 on `[0,1)`.
-/
@[simp]
theorem walsh_zero {x : ℝ} (h1 :0 ≤ x) (h2: x <1 ) : walsh 0 x = 1 := by
  simp [walsh, h1,h2]


/--
Walsh function for `n=1` is 1 on the left half of `[0,1)`.
-/
@[simp]
theorem walsh_one_left (x : ℝ) (h1 :0 ≤ x) (h2: x < 1/2 ) : walsh 1 x =  1:= by
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
      simp_all
      linarith
    · linarith
  · exfalso
    push_neg at h_1 h_4
    linarith

/--
Walsh function for `n=1` is 1 on the right half of `[0,1)`.
-/

@[simp]
theorem walsh_one_right (x : ℝ) (h1 :1/2 ≤ x) (h2: x < 1 ) : walsh 1 x = -1:= by
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
      simp_all
      linarith
  · exfalso
    push_neg at h_1 h_3
    linarith
  · exfalso
    obtain h_l|h_r := h_4
    · push_neg at h_2 h_1
      simp_all
      rw[inv_le_iff_one_le_mul₀ (zero_lt_two)] at h_2
      linarith
    · linarith
  · rfl


/--
Walsh function for n being even on the left half of `[0,1)`.
-/
theorem walsh_even_left {n : ℕ}{x : ℝ}(h2: x < 1/2 ) : walsh (2*n) x = walsh n (2 * x) := by
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
    simp_all
    linarith

/--
Walsh function for n being even on the right half of `[0,1)`.
-/
theorem walsh_even_right {n : ℕ}{x : ℝ}  (h1 :1/2 ≤ x) : walsh (2*n) x = walsh n (2 * x - 1) := by
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
    simp_all
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


theorem walsh_odd_left {n : ℕ}{x : ℝ}(h2: x < 1/2 ) : walsh (2*n +1) x = walsh n (2 * x) := by
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
    simp_all
    linarith

/--
Walsh function for n being odd on the right half of `[0,1)`.
-/


theorem walsh_odd_right {n : ℕ}{x : ℝ} (h1 :1/2 ≤ x)  : walsh (2*n+ 1) x =- walsh n (2 * x - 1) := by
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
    simp_all
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
theorem walsh_even_odd_left {n : ℕ}{x : ℝ} (h2: x < 1/2 ): walsh (2*n) x = walsh (2*n +1) x:= by
  rw[ walsh_even_left h2, walsh_odd_left h2]

theorem walsh_even_odd_right {n : ℕ}{x : ℝ} (h1 :1/2 ≤ x)  :walsh (2*n) x = - walsh (2*n +1) x:= by
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
        apply Nat.div2Induction.proof_2
        apply Nat.pos_of_ne_zero hzero
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
        apply Nat.div2Induction.proof_2
        apply Nat.pos_of_ne_zero hzero
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

theorem sqr_walsh {n : ℕ} (x : ℝ) (h1 : 0 ≤ x)(h2: x < 1) : (walsh n x)*(walsh n x) = 1 := by
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







theorem walsh_values {n : ℕ} {x : ℝ} (h1 : 0 ≤ x)(h2: x < 1) : walsh n x = 1 ∨ walsh n x =-1 := by
  rw[← sq_eq_one_iff, pow_two]
  apply sqr_walsh
  · exact h1
  exact h2


/--
Product of Wlash functions of fixed `n` and different arguments is 0 outside `[0, 1)`.
-/
theorem mul_walsh_outside {n : ℕ} (x y : ℝ ) (h : x <0 ∨  1 ≤  x) : (walsh n x)*(walsh n y ) =  0:= by
  rw[walsh_not_in]
  · simp only [zero_mul]
  exact  h


theorem mul_walsh_outside' {n : ℕ} (x y : ℝ ) (h : x <0 ∨  1 ≤  x) : (walsh n y )*(walsh n x) =  0:= by
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
theorem walshInnermul {n m : ℕ}  : walshInnerProduct (walsh n) m = walshInnerProduct (walsh m) n := by
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

/-- Walsh functions are orthogonal.-/
theorem walsh_ort_same {n m : ℕ} (h: m = n) : walshInnerProduct (walsh n) m  = 1 := by
  rw [h]
  apply walsh_norm




/--
Multiplication Walsh inner product by scalar.
-/
theorem walshInnerProduct_smul (c : ℝ) (f : ℝ → ℝ) (n : ℕ) :
  walshInnerProduct (λ x => c * f x) n = c * walshInnerProduct f n := by
  simp only [walshInnerProduct]
  simp_rw[← MeasureTheory.integral_mul_left, mul_assoc]


/--
Multiplication Walsh inner product by function.
-/
theorem mul_walshInnerProduct (f g : ℝ → ℝ) (n : ℕ) (x : ℝ ) :
  walshInnerProduct (λ y ↦ g x * f y) n = ∫ y in Set.Ico 0 1, g x * f y * walsh n y := by
  unfold walshInnerProduct
  simp

theorem add_walshInnerProduct (f g : ℝ → ℝ) (n : ℕ) :
  walshInnerProduct (λ y ↦ g y + f y) n = ∫ y in Set.Ico 0 1, (g y + f y) * walsh n y := by
  unfold walshInnerProduct
  simp


/--
Definition of Walsh Fourier partial sum.
-/
def walshFourierPartialSum (f : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
 λ x => ∑ n in Finset.range N, (walshInnerProduct f n) * walsh n x

/--
Definition of Walsh Fourier Series.
-/
def walshFourierSeries (f : ℝ → ℝ) : ℝ → ℝ :=
  λ x => tsum (λ N => walshFourierPartialSum f N x)





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


theorem intergability {n : ℕ } :MeasureTheory.IntegrableOn (walsh n) univ MeasureTheory.volume := by
  --simp only [MeasureTheory.integrableOn_univ]
  induction' n using Nat.strong_induction_on with n ih
  have h : univ = Ico 0 1 ∪ (univ\Ico 0 1) := by simp
  --simp_rw[h] at ih --czemu to nie dziala?
  --simp_rw[h , MeasureTheory.IntegrableOn.union ]
  set l := n/2 with hl
  by_cases hn : Odd n
  · have hl' : 2*l + 1 = n := by sorry
    rw[← hl']
    sorry
  · sorry





theorem changeofint {n : ℕ} : ∫ x in Set.Ico 0 1, walsh n x = ∫ x, walsh n x := by
  rw[← MeasureTheory.integral_indicator ]
  apply MeasureTheory.integral_congr_ae --?
  · rw[Filter.EventuallyEq ]
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
  --nwm jak zamienic granice calkowania

  sorry

theorem changeofint_secondhalf {n : ℕ} : ∫ x in Set.Ico 0.5 1,  walsh n (2*x-1) = (1/2) * ∫ x in Set.Ico 0 1, walsh n x := by sorry

theorem intsum {n :ℕ} : (∫ x in Set.Ico  0 0.5,  walsh n x) + ∫ x in Set.Ico 0.5 1,  walsh n x = ∫ x in Set.Ico 0 1, walsh n x := by
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


theorem intofodd {n : ℕ} (h: Odd n) : ∫ x in Set.Ico 0 1,  walsh n x = 0 := by
  rw[← intsum]
  set l :=n/2 with hl
  have hl' : 2*l + 1 = n := by
    exact Nat.two_mul_div_two_add_one_of_odd h
  simp_rw[← hl']
  rw[← relbetweenintodd1, ← sub_neg_eq_add, ← relbetweenintodd2, changeofint_firsthalf, changeofint_secondhalf, sub_self]



theorem intofeven {n k : ℕ}  (hk: 2*k = n): ∫ x in Set.Ico 0 1,  walsh n x =  ∫ x in Set.Ico 0 1,  walsh k x  := by
  rw[← intsum, ← hk]
  rw[← relbetweeninteven1, ← relbetweeninteven2, changeofint_firsthalf, changeofint_secondhalf, ← mul_add]
  rw[Eq.symm (two_mul (∫ (x : ℝ) in Ico 0 1, walsh k x))]
  simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.inv_mul_cancel_left]

end Walsh


---measurability
