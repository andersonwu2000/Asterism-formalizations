import ACS12.PureAdjacentIntegralTail

/-! The signed quadratic cumulative bound for the pure power primitive. -/
namespace ACS12.GammaMeasure

open Set CenteredCircle.AllN MeasureTheory

private theorem weighted_power_integral_lower {x q a : ℝ} (hx : 0 < x) (hq : 0 < q)
    (hbL : 13 / 25 ≤ 1 - 2 * a) (hbU : 1 - 2 * a ≤ 43 / 75) :
    (1 / 2 - a) * (x + 7 / 30) ^ (-q) ≤
      ∫ s in (0 : ℝ)..1, (1 - a - s) * (x + s) ^ (-q) := by
  let c : ℝ := 7 / 30
  let b := 1 - 2 * a
  let F (s : ℝ) := (x + s) ^ (-q)
  let D (s : ℝ) := -q * (x + s) ^ (-q - 1)
  let H (s : ℝ) := q * (q + 1) * (x + s) ^ (-q - 2)
  let I (s : ℝ) := (1 - a) * s ^ 2 / 2 - s ^ 3 / 6
  let J (s : ℝ) := (1 - a) * s - s ^ 2 / 2
  let I₁ (s : ℝ) := I s - b / 2 * (s - c)
  let J₁ (s : ℝ) := J s - b / 2
  have hc₀ : 0 ≤ c := by norm_num [c]
  have hc₁ : c ≤ 1 := by norm_num [c]
  have hB₀ : 0 ≤ b := by dsimp only [b]; linarith only [hbL]
  have hI {s : ℝ} (hs : s ∈ Icc (0 : ℝ) c) : 0 ≤ I s := by
    have hK : 0 ≤ (1 - a) / 2 - s / 6 := by
      have hsU := hs.2
      norm_num [c] at hsU
      linarith only [hbL,hsU]
    have hE : I s = s ^ 2 * ((1 - a) / 2 - s / 6) := by unfold I; ring
    rw [hE]
    positivity
  have hI₁ {s : ℝ} (hs : s ∈ Icc c 1) : 0 ≤ I₁ s := by
    have hK : 0 ≤ (3 * (1 - a) - s - 2 * b) / 6 := by
      dsimp only [b]
      linarith only [hbU,hs.2]
    have hM : 0 ≤ c - b / 2 + b ^ 2 / 6 := by
      have h := mul_nonneg (show 0 ≤ 43 / 75 - b by exact sub_nonneg.mpr hbU)
        (show 0 ≤ 1 / 2 - ((43 / 75 : ℝ) + b) / 6 by linarith only [hbU])
      unfold c
      nlinarith only [h]
    have hE : I₁ s = b / 2 * (c - b / 2 + b ^ 2 / 6) +
        (s - b) ^ 2 * ((3 * (1 - a) - s - 2 * b) / 6) := by
      unfold I₁ I b
      ring
    rw [hE]
    exact add_nonneg (mul_nonneg (by positivity) hM) (mul_nonneg (sq_nonneg _) hK)
  have hF (s : ℝ) (hs : 0 ≤ s) : HasDerivAt F (D s) s := by
    simpa only [F,D,id_eq,mul_one,one_mul] using
      ((hasDerivAt_id s).const_add x).rpow_const (p := -q) (Or.inl (add_pos_of_pos_of_nonneg hx hs).ne')
  have hD (s : ℝ) (hs : 0 ≤ s) : HasDerivAt D (H s) s := by
    convert ((((hasDerivAt_id s).const_add x).rpow_const (p := -q - 1)
      (Or.inl (add_pos_of_pos_of_nonneg hx hs).ne')).const_mul (-q)) using 1
    simp only [H,id_eq,mul_one,show -q - 1 - 1 = -q - 2 by ring]
    ring
  have hH (s : ℝ) (hs : 0 ≤ s) : ContinuousAt H s := by
    exact ((((hasDerivAt_id s).const_add x).rpow_const (p := -q - 2)
      (Or.inl (add_pos_of_pos_of_nonneg hx hs).ne')).const_mul (q * (q + 1))).continuousAt
  have hID (s : ℝ) : HasDerivAt I (J s) s := by
    convert (((hasDerivAt_id s).pow 2).const_mul (1 - a) |>.div_const 2).sub
      (((hasDerivAt_id s).pow 3).div_const 6) using 1
    simp only [J,id_eq,mul_one,Nat.cast_ofNat,pow_one,show (3 : ℕ) - 1 = 2 by decide,
      show (2 : ℕ) - 1 = 1 by decide,pow_one]
    ring
  have hJD (s : ℝ) : HasDerivAt J (1 - a - s) s := by
    convert ((hasDerivAt_id s).const_mul (1 - a)).sub (((hasDerivAt_id s).pow 2).div_const 2) using 1
    simp only [id_eq,mul_one,Nat.cast_ofNat,show (2 : ℕ) - 1 = 1 by decide,pow_one]
    ring
  have hI₁D (s : ℝ) : HasDerivAt I₁ (J₁ s) s := by
    simpa only [I₁,J₁,mul_one] using
      (hID s).sub (((hasDerivAt_id s).sub_const c).const_mul (b / 2))
  have hJ₁D (s : ℝ) : HasDerivAt J₁ (1 - a - s) s := (hJD s).sub_const (b / 2)
  have hIntegral {l r : ℝ} (hl : 0 ≤ l) (hlr : l ≤ r) {A B : ℝ → ℝ}
      (hAB : ∀ s : ℝ, HasDerivAt A (B s) s)
      (hB : ∀ s : ℝ, HasDerivAt B (1 - a - s) s)
      (hA₀ : ∀ s ∈ Icc l r, 0 ≤ A s) :
      B r * F r - A r * D r - (B l * F l - A l * D l) ≤
        ∫ s in l..r, (1 - a - s) * F s := by
    have hDer (s : ℝ) (hs : 0 ≤ s) :
        HasDerivAt (fun y => B y * F y - A y * D y) ((1 - a - s) * F s - A s * H s) s := by
      convert ((hB s).mul (hF s hs)).sub ((hAB s).mul (hD s hs)) using 1
      ring
    have hFC : ContinuousOn (fun s => (1 - a - s) * F s) (Icc l r) :=
      (by fun_prop : ContinuousOn (fun s : ℝ => 1 - a - s) (Icc l r)).mul
        (fun s hs => (hF s (hl.trans hs.1)).continuousAt.continuousWithinAt)
    have hAC : ContinuousOn (fun s => A s * H s) (Icc l r) :=
      fun s hs => ((hAB s).continuousAt.mul (hH s (hl.trans hs.1))).continuousWithinAt
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := l) (b := r)
      (fun s hs => hDer s (hl.trans (by simpa only [min_eq_left hlr] using hs.1)))
      ((hFC.sub hAC).intervalIntegrable_of_Icc hlr)
    rw [intervalIntegral.integral_sub (hFC.intervalIntegrable_of_Icc hlr)
      (hAC.intervalIntegrable_of_Icc hlr)] at hFTC
    have hPos : 0 ≤ ∫ s in l..r, A s * H s := by
      apply intervalIntegral.integral_nonneg hlr
      intro s hs
      have hxs : 0 ≤ x + s := add_nonneg hx.le (hl.trans hs.1)
      exact mul_nonneg (hA₀ s hs) (by unfold H; positivity)
    linarith only [hFTC,hPos]
  have hL := hIntegral (l := 0) (r := c) le_rfl hc₀ hID hJD (fun _ hs => hI hs)
  have hR := hIntegral hc₀ hc₁ hI₁D hJ₁D (fun _ hs => hI₁ hs)
  have hFC (l r : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) :
      IntervalIntegrable (fun s => (1 - a - s) * F s) MeasureTheory.volume l r :=
    ((by fun_prop : ContinuousOn (fun s : ℝ => 1 - a - s) (Icc l r)).mul
      (fun s hs => (hF s (hl.trans hs.1)).continuousAt.continuousWithinAt)).intervalIntegrable_of_Icc hlr
  have hSum := add_le_add hL hR
  rw [intervalIntegral.integral_add_adjacent_intervals (hFC 0 c le_rfl hc₀) (hFC c 1 hc₀ hc₁)] at hSum
  have hJ0 : J 0 = 0 := by simp [J]
  have hI0 : I 0 = 0 := by simp [I]
  have hI1c : I₁ c = I c := by simp [I₁]
  have hJ11 : J₁ 1 = 0 := by unfold J₁ J b; ring
  have hI11 : 0 ≤ I₁ 1 := hI₁ ⟨hc₁,le_rfl⟩
  have hD1 : D 1 ≤ 0 := by unfold D; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) (by positivity)
  rw [hJ0,hI0,hI1c,hJ11] at hSum
  have hCoef : 1 / 2 - a = b / 2 := by unfold b; ring
  change (1 / 2 - a) * F c ≤ _
  rw [hCoef]
  have hSign := mul_nonpos_of_nonneg_of_nonpos hI11 hD1
  dsimp only [J₁] at hSum
  nlinarith only [hSum,hSign]

private theorem pureRightPrimitive_weighted_eq {p u x : ℝ} (hp : 1 < p) (hx : 0 < x) :
    pureRightPrimitive p u x = -(1 - u) * x ^ (-p) +
      p * ∫ s in (0 : ℝ)..1, (1 - middleA u - s) * (x + s) ^ (-p - 1) := by
  let a := middleA u
  let k (s : ℝ) := (x + s) ^ (-p)
  let A (s : ℝ) := (x + s) ^ (1 - p) / (1 - p)
  let Q (s : ℝ) := (1 - a - s) * k s + A s
  have hDer (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt Q (-p * ((1 - a - s) * (x + s) ^ (-p - 1))) s := by
    have hXs := add_pos_of_pos_of_nonneg hx hs
    have hi := hasDerivAt_id s
    have hK : HasDerivAt k (-p * (x + s) ^ (-p - 1)) s := by
      simpa only [k,id_eq,mul_one,one_mul] using
        (hi.const_add x).rpow_const (p := -p) (Or.inl hXs.ne')
    have hA : HasDerivAt A (k s) s := by
      convert ((hi.const_add x).rpow_const (p := 1 - p) (Or.inl hXs.ne')).div_const (1 - p) using 1
      simp only [k,id_eq,mul_one,show 1 - p - 1 = -p by ring]
      field_simp [(show 1 - p ≠ 0 by linarith only [hp])]
    convert (((hi.const_sub (1 - a)).mul hK).add hA) using 1
    simp only [id_eq,neg_mul,one_mul]
    ring
  have hC : ContinuousOn (fun s : ℝ => (1 - a - s) * (x + s) ^ (-p - 1)) (Icc 0 1) := by
    apply ContinuousOn.mul (by fun_prop)
    intro s hs
    exact (((hasDerivAt_id s).const_add x).rpow_const (p := -p - 1)
      (Or.inl (add_pos_of_pos_of_nonneg hx hs.1).ne')).continuousAt.continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun s hs => hDer s (by norm_num at hs; exact hs.1)) ((hC.intervalIntegrable_of_Icc zero_le_one).const_mul (-p))
  change (∫ s in (0 : ℝ)..1, -p * ((1 - a - s) * (x + s) ^ (-p - 1))) = _ at h
  rw [intervalIntegral.integral_const_mul] at h
  unfold Q A k at h
  simp only [add_zero] at h
  unfold pureRightPrimitive middleZ
  change (u - a) * x ^ (-p) + a * (x + 1) ^ (-p) +
    ((x + 1) ^ (1 - p) - x ^ (1 - p)) / (p - 1) = _
  have hE : ((x + 1) ^ (1 - p) - x ^ (1 - p)) / (p - 1) =
      x ^ (1 - p) / (1 - p) - (x + 1) ^ (1 - p) / (1 - p) := by
    rw [show p - 1 = -(1 - p) by ring,div_neg,sub_div,neg_sub]
  rw [hE]
  linear_combination h

private theorem endpoint_power_shift_le {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (15 / 26)) :
    (1 - (7 / 30) * y) ^ (-(9 / 5 : ℝ)) ≤ 1 + (13 / 25) * y := by
  have hx : 1 - (7 / 30) * y = (1 - (26 / 15) * y) • (1 : ℝ) +
      ((26 / 15) * y) • (45 / 52 : ℝ) := by simp only [smul_eq_mul]; ring
  have hA : 0 ≤ (26 / 15) * y := by have := hy.1; positivity
  have hB : 0 ≤ 1 - (26 / 15) * y := by linarith only [hy.2]
  have h := (negativePower_convex (s := (9 / 5 : ℝ)) (by norm_num)).2
    (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show (45 / 52 : ℝ) ∈ Ioi 0 by norm_num)
    hB hA (by ring)
  rw [← hx] at h
  simp only [smul_eq_mul,Real.one_rpow,mul_one] at h
  have hE : (45 / 52 : ℝ) ^ (-(9 / 5 : ℝ)) < 13 / 10 := by
    apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _) (by norm_num)
      (z := (5 : ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 45 / 52)]
    norm_num
  exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_left hE.le hA])

private theorem endpoint_shifted_minimum {δ y : ℝ} (hδ : 0 < δ) (hy : 0 < y) :
    -(10 / 9) * δ ^ (14 / 5 : ℝ) < -δ * y ^ (9 / 5 : ℝ) + (257 / 750) * y ^ (14 / 5 : ℝ) := by
  let k : ℝ := 257 / 750
  let c : ℝ := (9 / 14) / k
  let z := c * δ
  let f (t : ℝ) := -δ * t ^ (9 / 5 : ℝ) + k * t ^ (14 / 5 : ℝ)
  have hk : 0 < k := by norm_num [k]
  have hc : 0 < c := by norm_num [c,k]
  have hz := mul_pos hc hδ
  have hDer (t : ℝ) (ht : 0 < t) :
      HasDerivAt f (t ^ (4 / 5 : ℝ) * ((14 / 5) * k * (t - z))) t := by
    have h1 := (Real.hasDerivAt_rpow_const (x := t) (p := (9 / 5 : ℝ)) (Or.inl ht.ne')).const_mul (-δ)
    have h2 := (Real.hasDerivAt_rpow_const (x := t) (p := (14 / 5 : ℝ)) (Or.inl ht.ne')).const_mul k
    convert h1.add h2 using 1
    rw [show (9 / 5 : ℝ) - 1 = 4 / 5 by norm_num,
      show (14 / 5 : ℝ) - 1 = 4 / 5 + 1 by norm_num,Real.rpow_add_one ht.ne']
    unfold z c
    field_simp [hk.ne']
    <;> ring
  have hMin : f z ≤ f y := by
    rcases le_total y z with h | h
    · have hAnti : AntitoneOn f (Icc y z) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        · exact fun t ht => (hDer t (hy.trans_le ht.1)).continuousAt.continuousWithinAt
        · exact fun t ht => (hDer t (hy.trans_le (interior_subset ht).1)).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht' : t ∈ Icc y z := interior_subset ht
          rw [(hDer t (hy.trans_le ht'.1)).deriv]
          exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hy.trans_le ht'.1).le _)
            (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr ht'.2))
      exact hAnti ⟨le_rfl,h⟩ ⟨h,le_rfl⟩ h
    · have hMono : MonotoneOn f (Icc z y) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        · exact fun t ht => (hDer t (hz.trans_le ht.1)).continuousAt.continuousWithinAt
        · exact fun t ht => (hDer t (hz.trans_le (interior_subset ht).1)).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht' : t ∈ Icc z y := interior_subset ht
          rw [(hDer t (hz.trans_le ht'.1)).deriv]
          exact mul_nonneg (Real.rpow_nonneg (hz.trans_le ht'.1).le _)
            (mul_nonneg (by positivity) (sub_nonneg.mpr ht'.1))
      exact hMono ⟨le_rfl,h⟩ ⟨h,le_rfl⟩ h
  have hVal : f z = -((5 / 14) * c ^ (9 / 5 : ℝ)) * δ ^ (14 / 5 : ℝ) := by
    unfold f
    rw [show (14 / 5 : ℝ) = 9 / 5 + 1 by norm_num,Real.rpow_add_one hz.ne']
    unfold z
    rw [Real.mul_rpow hc.le hδ.le,Real.rpow_add_one hδ.ne']
    unfold c
    field_simp [hk.ne']
    <;> ring
  have hConst : (5 / 14) * c ^ (9 / 5 : ℝ) < 10 / 9 := by
    apply (Real.rpow_lt_rpow_iff (by positivity) (by norm_num) (z := (5 : ℝ)) (by norm_num)).mp
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5 / 14) (by positivity),← Real.rpow_mul hc.le]
    norm_num [c,k]
  calc
    _ < f z := by rw [hVal]; nlinarith only [mul_lt_mul_of_pos_right hConst (Real.rpow_pos_of_pos hδ (14 / 5))]
    _ ≤ f y := hMin

theorem pureRightPrimitive_endpoint_floor {u x : ℝ} (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8))
    (hx : 3 / 2 ≤ x) :
    -(10 / 9) * (1 - u) ^ (14 / 5 : ℝ) < pureRightPrimitive (9 / 5) u x := by
  let a := middleA u
  let δ := 1 - u
  let c : ℝ := 7 / 30
  let y := (x + c)⁻¹
  have hx₀ : 0 < x := (by norm_num : (0 : ℝ) < 3 / 2).trans_le hx
  have hδ : 0 < δ := by unfold δ; linarith only [hu.2]
  have hy : 0 < y := by unfold y c; positivity
  have hyU : y ≤ 15 / 26 := by
    rw [show y = 1 / (x + c) by simp [y,one_div]]
    apply (div_le_iff₀ (by unfold c; positivity : 0 < x + c)).mpr
    unfold c
    linarith only [hx]
  have ha : a = (6 / 25) * (1 - δ ^ 2) := by unfold a δ middleA; ring
  have hdL : 1 / 8 ≤ δ := by unfold δ; linarith only [hu.2]
  have hdU : δ ≤ 1 / 3 := by unfold δ; linarith only [hu.1]
  have hdSq := pow_le_pow_left₀ hδ.le hdU 2
  have hbL : 13 / 25 ≤ 1 - 2 * a := by rw [ha]; nlinarith only [sq_nonneg δ]
  have hbU : 1 - 2 * a ≤ 43 / 75 := by rw [ha]; nlinarith only [hdSq]
  have hWeight := weighted_power_integral_lower hx₀ (q := (14 / 5 : ℝ)) (a := a) (by norm_num) hbL hbU
  have hPrim := pureRightPrimitive_weighted_eq (u := u) (p := (9 / 5 : ℝ)) (by norm_num) hx₀
  rw [show -(9 / 5 : ℝ) - 1 = -(14 / 5) by norm_num] at hPrim
  change pureRightPrimitive (9 / 5) u x = -δ * x ^ (-(9 / 5 : ℝ)) + _ at hPrim
  have hY : x = (x + c) * (1 - c * y) := by
    unfold y
    field_simp [(by unfold c; positivity : 0 < x + c).ne']
    ring
  have hR : 0 ≤ 1 - c * y := by unfold c; linarith only [hyU]
  have hPow : x ^ (-(9 / 5 : ℝ)) = y ^ (9 / 5 : ℝ) * (1 - c * y) ^ (-(9 / 5 : ℝ)) := by
    conv_lhs => rw [hY,Real.mul_rpow (by unfold c; positivity) hR]
    rw [show y ^ (9 / 5 : ℝ) = (x + c) ^ (-(9 / 5 : ℝ)) by
      unfold y
      rw [Real.inv_rpow (by unfold c; positivity),Real.rpow_neg (by unfold c; positivity)]]
  have hShift := endpoint_power_shift_le ⟨hy.le,hyU⟩
  change (1 - c * y) ^ (-(9 / 5 : ℝ)) ≤ _ at hShift
  have hExp : y ^ (14 / 5 : ℝ) = y ^ (9 / 5 : ℝ) * y := by
    rw [show (14 / 5 : ℝ) = 9 / 5 + 1 by norm_num,Real.rpow_add_one hy.ne']
  have hW : (x + c) ^ (-(14 / 5 : ℝ)) = y ^ (14 / 5 : ℝ) := by
    unfold y
    rw [Real.inv_rpow (by unfold c; positivity),Real.rpow_neg (by unfold c; positivity)]
  change (1 / 2 - a) * (x + c) ^ (-(14 / 5 : ℝ)) ≤ _ at hWeight
  rw [hW] at hWeight
  have hPrimL : -δ * y ^ (9 / 5 : ℝ) + ((9 / 5) * (1 / 2 - a) - (13 / 25) * δ) *
      y ^ (14 / 5 : ℝ) ≤ pureRightPrimitive (9 / 5) u x := by
    rw [hPrim,hPow]
    have hS := mul_le_mul_of_nonpos_left hShift (show -δ * y ^ (9 / 5 : ℝ) ≤ 0 from
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) (Real.rpow_nonneg hy.le _))
    have hT := mul_le_mul_of_nonneg_left hWeight (by norm_num : (0 : ℝ) ≤ 9 / 5)
    rw [hExp] at hT ⊢
    linarith only [hS,hT]
  have hK : (257 / 750 : ℝ) ≤ (9 / 5) * (1 / 2 - a) - (13 / 25) * δ := by
    rw [ha]
    nlinarith only [hdU,sq_nonneg (δ - 1 / 3)]
  exact (endpoint_shifted_minimum hδ hy).trans_le
    ((add_le_add_right (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hy.le (14 / 5))) _).trans hPrimL)

theorem pureRight_clipped_tail_le {L u t X : ℝ} (hL : 0 < L)
    (hu : u ∈ Icc (2 / 3 : ℝ) (7 / 8)) (ht : 3 / 2 ≤ t) (htX : t ≤ X)
    (hX : pureRight (9 / 5) u X ≤ 0) :
    (∫ x in Ioi t, lawRightClip (9 / 5) L 0 u x) ≤
      pureRightPrimitive (9 / 5) u t + (10 / 9) * (1 - u) ^ (14 / 5 : ℝ) := by
  let p : ℝ := 9 / 5
  let f := lawRightClip p L 0 u
  let g := pureRight p u
  let A := Icc t X ∩ g ⁻¹' Iic 0
  let b := sInf A
  have hp : 1 < p := by norm_num [p]
  have hp₂ : p ≤ 2 := by norm_num [p]
  have hθ : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have ht₀ : 0 < t := (by norm_num : (0 : ℝ) < 3 / 2).trans_le ht
  have hXC : X ∈ A := ⟨⟨htX,le_rfl⟩,hX⟩
  have hBdd : BddBelow A := ⟨t,fun _ hx => hx.1.1⟩
  have hGC : ContinuousOn g (Icc t X) := by
    intro x hx
    have hx₀ := ht₀.trans_le hx.1
    unfold g pureRight
    have h (q : ℝ) : ContinuousAt (fun z : ℝ => z ^ q) x :=
      (Real.hasDerivAt_rpow_const (p := q) (Or.inl hx₀.ne')).continuousAt
    have h' (q : ℝ) : ContinuousAt (fun z : ℝ => (z + 1) ^ q) x :=
      (((hasDerivAt_id x).add_const 1).rpow_const (p := q) (Or.inl (by positivity : 0 < x + 1).ne')).continuousAt
    exact ((((h _).const_mul _).add ((h' _).const_mul _)).sub (h _)).add (h' _) |>.continuousWithinAt
  have hClosed : IsClosed A := by
    obtain ⟨S,hS,hEq⟩ := continuousOn_iff_isClosed.mp hGC (Iic 0) isClosed_Iic
    unfold A
    rw [inter_comm,hEq]
    exact hS.inter isClosed_Icc
  have hb : b ∈ A := hClosed.csInf_mem ⟨X,hXC⟩ hBdd
  have hb₀ : 0 < b := ht₀.trans_le hb.1.1
  have hf (x : ℝ) (hx : 0 < x) : f x = max 0 (g x) := by
    unfold f g lawRightClip
    rw [lawRightTest_zero hp.le hp₂ hL hx]
  have hfZero : f b = 0 := by rw [hf b hb₀,max_eq_left hb.2]
  have hTail (x : ℝ) (hx : x ∈ Ioi b) : f x = 0 := by
    apply le_antisymm _ (le_max_left _ _)
    exact (lawRightClip_antitone hp.le hp₂ hL hθ hb₀ (hb₀.trans hx) hx.le).trans_eq hfZero
  have hHead (x : ℝ) (hx : x ∈ Ioo t b) : f x = g x := by
    rw [hf x (ht₀.trans hx.1)]
    apply max_eq_right
    by_contra! hn
    have h : x ∈ A := ⟨⟨hx.1.le,hx.2.le.trans hb.1.2⟩,hn.le⟩
    exact hx.2.not_ge (csInf_le hBdd h)
  have hEQ : (∫ x in Ioc t b, f x) = ∫ x in Ioc t b, g x := by
    apply integral_congr_ae
    have hNE : ∀ᵐ x ∂(volume.restrict (Ioc t b)), x ≠ b := by
      exact (volume.restrict (Ioc t b)).ae_ne b
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hNE] with x hx hne
    exact hHead x ⟨hx.1,lt_of_le_of_ne hx.2 hne⟩
  have hUnion : Ioc t b ∪ Ioi b = Ioi t := by
    ext x
    change (t < x ∧ x ≤ b) ∨ b < x ↔ t < x
    exact ⟨fun h => h.elim And.left (fun h' => hb.1.1.trans_lt h'),fun h =>
      (le_or_gt x b).elim (fun h' => Or.inl ⟨h,h'⟩) Or.inr⟩
  have hDisj : Disjoint (Ioc t b) (Ioi b) := Set.disjoint_left.mpr fun _ hx hy => hy.not_ge hx.2
  have hI : IntegrableOn f (Ioi t) := by
    apply (pureRight_tail_integral (u := u) hp ht₀).1.pos_part.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change max (g x) 0 = f x
    rw [hf x (ht₀.trans hx),max_comm]
  have hT : (∫ x in Ioi b, f x) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hTail]
    simp
  change (∫ x in Ioi t, f x) ≤ _
  rw [← hUnion, setIntegral_union hDisj measurableSet_Ioi
    (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hb.1.1)),hT,add_zero,hEQ]
  change (∫ x in Ioc t b, pureRight p u x) ≤ _
  rw [← intervalIntegral.integral_of_le hb.1.1,
    ← intervalIntegral.integral_Ioi_sub_Ioi (pureRight_tail_integral hp ht₀).1 hb.1.1,
    (pureRight_tail_integral hp ht₀).2,(pureRight_tail_integral hp hb₀).2]
  have hFloor := pureRightPrimitive_endpoint_floor hu (ht.trans hb.1.1)
  change -(10 / 9) * (1 - u) ^ (14 / 5 : ℝ) < pureRightPrimitive p u b at hFloor
  change pureRightPrimitive p u t - pureRightPrimitive p u b ≤
    pureRightPrimitive p u t + (10 / 9) * (1 - u) ^ (14 / 5 : ℝ)
  linarith only [hFloor]

end ACS12.GammaMeasure
