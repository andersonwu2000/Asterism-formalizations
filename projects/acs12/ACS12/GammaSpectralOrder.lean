import ACS12.GammaSublinear

/-! Strict order of the normalized Gamma ratio at every exponent above two. -/
namespace ACS12.GammaMeasure

open Set Filter
open scoped Topology

theorem gammaSpectralRatio_strictMono {q : ℝ} (hq : 1 < q) :
    StrictMonoOn (gammaSpectralRatio q) (Ici 0) := by
  intro x hx y hy hxy
  have hx₀ : 0 ≤ x := hx
  have hy₀ : 0 ≤ y := hy
  let a := gammaEulerSite 1
  let b := gammaEulerSite q
  let F (z : ℝ) (i : ℕ) := (1 + z / a i) / (1 + z / b i)
  have ha (i : ℕ) : 0 < a i := by unfold a gammaEulerSite; positivity
  have hab (i : ℕ) : a i < b i := by
    unfold a b gammaEulerSite
    exact (sq_lt_sq₀ (by positivity) (by positivity)).mpr (by linarith only [hq])
  have hb (i : ℕ) := (ha i).trans (hab i)
  have hF (i : ℕ) (z : ℝ) (hz : 0 ≤ z) : 0 < F z i := by
    unfold F
    exact div_pos (add_pos_of_pos_of_nonneg one_pos (div_nonneg hz (ha i).le))
      (add_pos_of_pos_of_nonneg one_pos (div_nonneg hz (hb i).le))
  have hGt (i : ℕ) : F x i < F y i := by
    have hEq (z : ℝ) (hz : 0 ≤ z) :
        F z i = 1 + (b i / a i - 1) * (z / (z + b i)) := by
      unfold F
      have hQ : 0 < z + b i := add_pos_of_nonneg_of_pos hz (hb i)
      have hN (v : ℝ) (hv : 0 < v) : 1 + z / v = (z + v) / v := by
        rw [add_div,div_self hv.ne',add_comm]
      rw [hN _ (ha i),hN _ (hb i)]
      field_simp [(ha i).ne',(hb i).ne',hQ.ne']
      ring
    rw [hEq x hx₀,hEq y hy₀]
    have hS : x / (x + b i) < y / (y + b i) := by
      apply (div_lt_div_iff₀ (add_pos_of_nonneg_of_pos hx₀ (hb i))
        (add_pos_of_nonneg_of_pos hy₀ (hb i))).mpr
      nlinarith only [mul_pos (sub_pos.mpr hxy) (hb i)]
    have hT := mul_lt_mul_of_pos_left hS (sub_pos.mpr ((one_lt_div (ha i)).mpr (hab i)))
    linarith only [hT]
  let c := F y 0 / F x 0
  have hc : 1 < c := (one_lt_div (hF 0 x hx₀)).mpr (hGt 0)
  have hP (N : ℕ) (hN : 1 ≤ N) :
      c * interlacingProduct a b N x ≤ interlacingProduct a b N y := by
    unfold interlacingProduct
    change c * (∏ i ∈ Finset.range N, F x i) ≤ ∏ i ∈ Finset.range N, F y i
    have hMem : 0 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    rw [← Finset.mul_prod_erase (Finset.range N) (F x) hMem,
      ← Finset.mul_prod_erase (Finset.range N) (F y) hMem,← mul_assoc]
    have hEq : c * F x 0 = F y 0 := div_mul_cancel₀ _ (hF 0 x hx₀).ne'
    rw [hEq]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod
      (fun i _ => (hF i x hx₀).le) (fun i _ => (hGt i).le)) (hF 0 y hy₀).le
  have hL := le_of_tendsto_of_tendsto ((gammaSpectralRatio_euler (zero_lt_one.trans hq) hx₀).const_mul c)
    (gammaSpectralRatio_euler (zero_lt_one.trans hq) hy₀)
    ((eventually_ge_atTop (1 : ℕ)).mono fun N hN => hP N hN)
  exact (by simpa only [one_mul] using mul_lt_mul_of_pos_right hc (gammaSpectralRatio_pos (zero_lt_one.trans hq) x) :
    gammaSpectralRatio q x < c * gammaSpectralRatio q x).trans_le hL


theorem imageDensity_div_strictMono {p L : ℝ} (hp : 2 < p) (hL : 0 < L) :
    StrictMonoOn (fun s => imageDensity p L s / s) (Ioi 0) := by
  let q := p / 2
  let t (s : ℝ) := L * s / (2 * Real.pi)
  let C := (Real.pi / L) ^ (p - 1) * (2 : ℝ) ^ (p - 1) /
        (Real.Gamma p * (Real.pi / L) * 2)
  let A := (‖Complex.Gamma (gammaArgument q 0)‖ / ‖Complex.Gamma (gammaArgument 1 0)‖) ^ 2
  have hq : 1 < q := by unfold q; linarith only [hp]
  have hp₀ : 0 < p := by linarith only [hp]
  have hC : 0 < C := by unfold C; positivity
  have hA : 0 < A := sq_pos_of_ne_zero (div_ne_zero (norm_gamma_argument_ne (zero_lt_one.trans hq) 0)
    (norm_gamma_argument_ne zero_lt_one 0))
  have hEq (s : ℝ) (hs : 0 < s) :
      imageDensity p L s / s = (C * A) * gammaSpectralRatio q ((t s) ^ 2) := by
    rw [imageDensity_div_eq_ratio hp₀ hL hs]
    have hT : 0 ≤ t s := by unfold t; positivity
    unfold gammaSpectralRatio
    rw [Real.sqrt_sq hT]
    unfold gammaNormalizedRatio A
    change C * (‖Complex.Gamma (gammaArgument q (t s))‖ / ‖Complex.Gamma (gammaArgument 1 (t s))‖) ^ 2 = _
    rw [div_pow,div_pow,div_pow,div_pow]
    field_simp [norm_gamma_argument_ne (zero_lt_one.trans hq) 0,norm_gamma_argument_ne zero_lt_one 0,
      norm_gamma_argument_ne zero_lt_one (t s)]
  intro x hx y hy hxy
  have hx₀ : 0 < x := hx
  have hy₀ : 0 < y := hy
  have hT : t x < t y := div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hxy hL) (by positivity)
  have hS : (t x) ^ 2 < (t y) ^ 2 := (sq_lt_sq₀ (by unfold t; positivity) (by unfold t; positivity)).mpr hT
  change imageDensity p L x / x < imageDensity p L y / y
  rw [hEq x hx₀,hEq y hy₀]
  exact mul_lt_mul_of_pos_left (gammaSpectralRatio_strictMono hq (mem_Ici.mpr (sq_nonneg _)) (mem_Ici.mpr (sq_nonneg _)) hS) (mul_pos hC hA)

end ACS12.GammaMeasure

